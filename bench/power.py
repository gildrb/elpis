# Copyright (c) 2026 inference contributors.
"""Bounded board-power observations and gap-aware, clipped trapezoidal integration."""

from __future__ import annotations

import math
import subprocess
import threading
import time
from dataclasses import dataclass
from itertools import pairwise
from typing import Self, final

NANOSECONDS = 1_000_000_000


@dataclass(frozen=True)
class PowerSample:
    """One host observation; query midpoint timestamps are not device timestamps."""

    monotonic_ns: int
    unix_time_ns: int
    query_started_ns: int
    query_finished_ns: int
    watts: float | None
    error: str | None = None

    def __post_init__(self) -> None:
        """Reject invalid numeric observations rather than integrating them."""
        if not self.query_started_ns <= self.monotonic_ns <= self.query_finished_ns:
            raise ValueError("Sample timestamp must lie within its query interval")
        if self.watts is not None and (not math.isfinite(self.watts) or self.watts < 0):
            raise ValueError("Observed watts must be finite and nonnegative")
        if self.watts is not None and self.error is not None:
            raise ValueError("Failed samples cannot also provide power")


def clock_anchor() -> dict[str, int]:
    """Pair the host Unix and monotonic clocks, with read uncertainty in ns."""
    before = time.monotonic_ns()
    unix_time = time.time_ns()
    after = time.monotonic_ns()
    return {
        "monotonic_ns": (before + after) // 2,
        "unix_time_ns": unix_time,
        "uncertainty_ns": (after - before + 1) // 2,
    }


def integrate_power(
    samples: list[PowerSample], start_ns: int, end_ns: int, max_gap_ns: int
) -> dict[str, object]:
    """Integrate only adjacent valid observations, clipped to [start, end].

    No extrapolation, bridging failed reads, or filling long gaps. Full-interval
    joules are null unless every nanosecond is covered. Zero observed power is
    valid, but no observation is never represented as zero energy.
    """
    if end_ns < start_ns or max_gap_ns <= 0:
        raise ValueError("Invalid integration interval or maximum gap")
    if any(b.monotonic_ns <= a.monotonic_ns for a, b in pairwise(samples)):
        raise ValueError("Power samples must be strictly monotonic")
    covered_ns = 0
    joules = 0.0
    cursor = start_ns
    gaps: list[dict[str, object]] = []
    for left, right in pairwise(samples):
        lo = max(start_ns, left.monotonic_ns)
        hi = min(end_ns, right.monotonic_ns)
        if hi <= lo:
            continue
        if lo > cursor:
            gaps.append({"start_ns": cursor, "end_ns": lo, "reason": "unobserved_boundary"})
        span = right.monotonic_ns - left.monotonic_ns
        if left.watts is None or right.watts is None:
            reason = "failed_sample"
        elif span > max_gap_ns:
            reason = "sampling_gap"
        else:
            reason = None
        if reason is not None:
            gaps.append({"start_ns": lo, "end_ns": hi, "reason": reason})
        else:
            # Both endpoints were checked above; no nominal/average fill value.
            assert left.watts is not None and right.watts is not None
            slope = (right.watts - left.watts) / span
            low_watts = left.watts + slope * (lo - left.monotonic_ns)
            high_watts = left.watts + slope * (hi - left.monotonic_ns)
            joules += (low_watts + high_watts) * 0.5 * (hi - lo) / NANOSECONDS
            covered_ns += hi - lo
        cursor = hi
    if cursor < end_ns:
        gaps.append({"start_ns": cursor, "end_ns": end_ns, "reason": "unobserved_boundary"})
    elapsed_ns = end_ns - start_ns
    complete = elapsed_ns > 0 and covered_ns == elapsed_ns
    return {
        "start_monotonic_ns": start_ns,
        "end_monotonic_ns": end_ns,
        "wall_seconds": elapsed_ns / NANOSECONDS,
        "observed_joules": joules if covered_ns else None,
        "joules": joules if complete else None,
        "covered_seconds": covered_ns / NANOSECONDS,
        "uncovered_seconds": (elapsed_ns - covered_ns) / NANOSECONDS,
        "coverage_fraction": covered_ns / elapsed_ns if elapsed_ns else None,
        "complete": complete,
        "gaps": gaps,
    }


@final
class PowerSampler:
    """Sample one selected board on absolute monotonic deadlines, within bounds."""

    def __init__(
        self,
        gpu: str = "0",
        interval_seconds: float = 0.5,
        max_seconds: float = 86400.0,
        max_samples: int = 200_000,
    ) -> None:
        """Validate collection bounds; this never changes device power policy."""
        if not 0.1 <= interval_seconds <= 60 or not 1 <= max_seconds <= 604800:
            raise ValueError("Power interval must be 0.1..60 s and duration 1..604800 s")
        if not 2 <= max_samples <= 1_000_000:
            raise ValueError("Power sample limit must be 2..1000000")
        if not gpu or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-:." for c in gpu):
            raise ValueError("Use a single GPU index, UUID, or PCI bus ID")
        self.gpu = gpu
        self.interval_ns = int(interval_seconds * NANOSECONDS)
        self.max_gap_ns = self.interval_ns * 3
        self.max_ns = int(max_seconds * NANOSECONDS)
        self.max_samples = max_samples
        self.samples: list[PowerSample] = []
        self.limit_reached: str | None = None
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._loop, daemon=False)
        self._deadline_ns = 0
        self.started: dict[str, int] = {}
        self.ended: dict[str, int] = {}

    def _sample(self) -> None:
        if len(self.samples) >= self.max_samples:
            self.limit_reached = "sample_limit"
            return
        if time.monotonic_ns() >= self._deadline_ns:
            self.limit_reached = "duration_limit"
            return
        before = clock_anchor()
        watts = None
        error = None
        try:
            result = subprocess.run(
                [
                    "nvidia-smi",
                    f"--id={self.gpu}",
                    "--query-gpu=power.draw",
                    "--format=csv,noheader,nounits",
                ],
                capture_output=True,
                text=True,
                check=False,
                timeout=2,
            )
            if result.returncode:
                error = f"nvidia_smi_exit_{result.returncode}"
            else:
                value = float(result.stdout.strip())
                if math.isfinite(value) and value >= 0:
                    watts = value
                else:
                    error = "invalid_power_value"
        except FileNotFoundError:
            error = "nvidia_smi_not_found"
        except subprocess.TimeoutExpired:
            error = "nvidia_smi_timeout"
        except (ValueError, UnicodeError):
            error = "invalid_power_output"
        except OSError:
            error = "nvidia_smi_os_error"
        after = clock_anchor()
        self.samples.append(PowerSample(
            monotonic_ns=(before["monotonic_ns"] + after["monotonic_ns"]) // 2,
            unix_time_ns=(before["unix_time_ns"] + after["unix_time_ns"]) // 2,
            query_started_ns=before["monotonic_ns"],
            query_finished_ns=after["monotonic_ns"],
            watts=watts,
            error=error,
        ))

    def _loop(self) -> None:
        deadline = time.monotonic_ns() + self.interval_ns
        while not self._stop.wait(max(0, deadline - time.monotonic_ns()) / NANOSECONDS):
            self._sample()
            if self.limit_reached:
                return
            deadline += self.interval_ns
            # Missed deadlines are visible as gaps; never issue catch-up bursts.
            now = time.monotonic_ns()
            if deadline <= now:
                deadline += ((now - deadline) // self.interval_ns + 1) * self.interval_ns

    def __enter__(self) -> Self:
        """Bracket the measured interval with a first observation."""
        self._deadline_ns = time.monotonic_ns() + self.max_ns
        self._sample()
        self.started = clock_anchor()
        self._thread.start()
        return self

    def __exit__(self, *_args: object) -> None:
        """Stop and join collection, including on exceptions; bracket the end."""
        self.ended = clock_anchor()
        self._stop.set()
        self._thread.join()
        self._sample()

    def summary(self, start_ns: int | None = None, end_ns: int | None = None) -> dict[str, object]:
        """Return evidence only after cleanup, never a fabricated zero sample."""
        if not self.ended:
            raise RuntimeError("Power summary requires a closed sampler")
        interval = integrate_power(
            self.samples,
            self.started["monotonic_ns"] if start_ns is None else start_ns,
            self.ended["monotonic_ns"] if end_ns is None else end_ns,
            self.max_gap_ns,
        )
        values = sorted(sample.watts for sample in self.samples if sample.watts is not None)
        errors: dict[str, int] = {}
        for sample in self.samples:
            if sample.error is not None:
                errors[sample.error] = errors.get(sample.error, 0) + 1
        return {
            "schema_version": 1,
            "scope": "selected_gpu_board_not_system_or_decode_only",
            "integration": "piecewise_linear_trapezoids_no_extrapolation",
            "timestamp_basis": "host_query_midpoint_not_device_timestamp",
            "units": {"power": "W", "energy": "J", "duration": "s", "timestamps": "ns"},
            "gpu": self.gpu,
            "sampling_interval_seconds": self.interval_ns / NANOSECONDS,
            "max_gap_seconds": self.max_gap_ns / NANOSECONDS,
            "sample_count": len(self.samples),
            "valid_sample_count": len(values),
            "sample_failures": errors,
            "limit_reached": self.limit_reached,
            "watts_min": values[0] if values else None,
            "watts_p50": values[len(values) // 2] if values else None,
            "watts_p90": values[min(len(values) - 1, len(values) * 9 // 10)] if values else None,
            "watts_max": values[-1] if values else None,
            "interval": interval,
        }

    def records(self) -> list[dict[str, int | float | str | None]]:
        """Return timestamped raw observations without subprocess output or secrets."""
        return [{
            "monotonic_ns": sample.monotonic_ns,
            "unix_time_ns": sample.unix_time_ns,
            "query_started_ns": sample.query_started_ns,
            "query_finished_ns": sample.query_finished_ns,
            "watts": sample.watts,
            "error": sample.error,
        } for sample in self.samples]
