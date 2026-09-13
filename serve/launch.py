#!/usr/bin/env python3
"""Run the single guarded deployment in the foreground; never install models."""

import argparse
import fcntl
import hashlib
import os
import signal
import stat
import subprocess
import sys
import time
from contextlib import ExitStack
from pathlib import Path
from types import FrameType

DEFAULT_PORT = 18020
MAX_PORT = 65535
GPU_IDLE_MIB = 1000
GPU_IDLE_ATTEMPTS = 60


class CleanupIncomplete(RuntimeError):
    """Owned process-group cleanup failed; require explicit operator recovery."""


class StopRequested(Exception):
    """A foreground operator requested cleanup and exit."""


def stop_requested(_signum: int, _frame: FrameType | None) -> None:
    """Raise the stop request handled by the foreground lifecycle.

    Raises:
        StopRequested: The operator requested stop.

    """
    raise StopRequested


def private_directory(path: Path) -> None:
    """Require a canonical, private directory owned by the caller.

    Raises:
        ValueError: A required configuration or input check failed.

    """
    if not path.is_absolute() or path.resolve() != path or not path.is_dir():
        message = "state paths must be existing canonical absolute directories"
        raise ValueError(message)
    metadata = path.stat()
    if metadata.st_uid != os.getuid() or (stat.S_IMODE(metadata.st_mode) & 0o077) != 0:
        message = "state paths must be owned by the caller and private (0700)"
        raise ValueError(message)


def _terminate_group(owned: subprocess.Popen[str], signum: int) -> bool:
    deadline = time.monotonic() + 10
    try:
        os.killpg(owned.pid, signum)
    except ProcessLookupError:
        # A vanished group still needs bounded leader/pipe collection.
        print(
            "Command group already exited; collecting owned pipes and leader.",
            file=sys.stderr,
        )
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return False
        drained = False
        try:
            owned.communicate(timeout=min(0.2, remaining))
            drained = True
        except subprocess.TimeoutExpired:
            # Continue within this phase's deadline, not an unlimited wait.
            drained = False
        try:
            os.killpg(owned.pid, 0)
            group_gone = False
        except ProcessLookupError:
            group_gone = True
        if drained and group_gone:
            return True
        time.sleep(min(0.05, max(0, deadline - time.monotonic())))


def execute(
    command: list[str],
    *,
    env: dict[str, str] | None = None,
    check: bool = True,
    capture_output: bool = False,
    text: bool = True,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
    """Collect an owned command with bounded process-group cleanup on failure.

    Returns:
        The command result after collection.

    Raises:
        CleanupIncomplete: Owned process-group cleanup did not finish.
        StopRequested: The operator requested stop.

    """
    output = subprocess.PIPE if capture_output else None
    process: subprocess.Popen[str] | None = None
    pending_signal: int | None = None
    cleanup_incomplete = False

    def defer_stop(signum: int, _frame: FrameType | None) -> None:
        nonlocal pending_signal
        pending_signal = signum

    previous_int = signal.signal(signal.SIGINT, defer_stop)
    previous_term = signal.signal(signal.SIGTERM, defer_stop)
    try:
        # Python handlers defer parent interruption without a blocked signal
        # mask that an exec child would inherit. Own the handle before replay.
        process = subprocess.Popen(
            command,
            env=env,
            stdout=output,
            stderr=output,
            text=text,
            start_new_session=True,
        )
        signal.signal(signal.SIGINT, previous_int)
        signal.signal(signal.SIGTERM, previous_term)
        if pending_signal is not None:
            signum = pending_signal
            pending_signal = None
            handler = previous_int if signum == signal.SIGINT else previous_term
            if callable(handler):
                handler(signum, None)
            elif handler != signal.SIG_IGN:
                raise StopRequested
        stdout, stderr = process.communicate(timeout=timeout)
        result = subprocess.CompletedProcess(
            command, process.returncode, stdout, stderr
        )
        if check:
            result.check_returncode()
        return result
    except BaseException:
        # No context manager: its implicit wait would remove these bounds.
        # Repeated stop requests are replayed only after bounded group cleanup.
        signal.signal(signal.SIGINT, defer_stop)
        signal.signal(signal.SIGTERM, defer_stop)
        if process is not None:
            cleanup_incomplete = True
            if not _terminate_group(process, signal.SIGTERM) and not _terminate_group(
                process, signal.SIGKILL
            ):
                message = (
                    "Command group cleanup incomplete after bounded TERM/KILL; "
                    "operator cleanup required"
                )
                raise CleanupIncomplete(message)
            cleanup_incomplete = False
        raise
    finally:
        # These are our pipes only. Closing them cannot wait for child exit.
        if process is not None:
            if process.stdout is not None:
                process.stdout.close()
            if process.stderr is not None:
                process.stderr.close()
        signal.signal(signal.SIGINT, previous_int)
        signal.signal(signal.SIGTERM, previous_term)
        if pending_signal is not None and not cleanup_incomplete:
            handler = previous_int if pending_signal == signal.SIGINT else previous_term
            if callable(handler):
                handler(pending_signal, None)
            elif handler != signal.SIG_IGN:
                raise StopRequested


def cleanup(compose: list[str], environment: dict[str, str]) -> tuple[bool, bool]:
    """Stop Compose while deferring operator signals until cleanup finishes.

    Returns:
        Cleanup success and whether an operator requested stop.

    """
    requested = False

    def defer_stop(_signum: int, _frame: FrameType | None) -> None:
        nonlocal requested
        requested = True

    previous_int = signal.signal(signal.SIGINT, defer_stop)
    previous_term = signal.signal(signal.SIGTERM, defer_stop)
    try:
        execute([*compose, "down"], env=environment, check=True, timeout=90)
        return True, requested
    except (subprocess.SubprocessError, OSError) as failure:
        print(
            "Deployment cleanup failed ("
            + type(failure).__name__
            + "); keeping the launch lock until retry or explicit failed stop.",
            file=sys.stderr,
        )
        return False, requested
    finally:
        signal.signal(signal.SIGINT, previous_int)
        signal.signal(signal.SIGTERM, previous_term)


def _wait_for_idle_gpu() -> None:
    """Bound the existing host-driver memory checks before starting inference.

    Raises:
        ValueError: A required configuration or input check failed.

    """
    # Use the installed host driver to inspect the selected GPU.
    for attempt in range(GPU_IDLE_ATTEMPTS):
        gpu = execute(
            [
                "nvidia-smi",
                "--query-gpu=memory.used",
                "--format=csv,noheader,nounits",
            ],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
        rows = gpu.stdout.splitlines()
        if len(rows) == 0 or not rows[0].strip().isdecimal():
            message = "invalid GPU memory response"
            raise ValueError(message)
        if int(rows[0].strip()) < GPU_IDLE_MIB:
            break
        if attempt == GPU_IDLE_ATTEMPTS - 1:
            message = "GPU memory did not become free"
            raise ValueError(message)
        time.sleep(2)


def main() -> int:
    """Run the guarded foreground deployment.

    Returns:
        The process exit status.

    Raises:
        ValueError: A required configuration or input check failed.

    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state-root", required=True, type=Path)
    parser.add_argument(
        "--systemd",
        action="store_true",
        help="report readiness to the owning systemd service",
    )
    parser.add_argument("--port", type=int, default=DEFAULT_PORT)
    args = parser.parse_args()
    if not args.systemd and args.port != DEFAULT_PORT:
        message = "foreground deployment uses fixed port 18020"
        raise ValueError(message)
    if not 1 <= args.port <= MAX_PORT:
        message = "port must be in 1..65535"
        raise ValueError(message)
    state = args.state_root
    if any(character in str(state) for character in (":", "\n", "\r")):
        message = "state root contains unsupported Compose path characters"
        raise ValueError(message)
    for directory in (state, state / "models", state / "cache"):
        private_directory(directory)
    credential = state / "api-key"
    if credential.resolve() != credential or not credential.is_file():
        message = "api-key must be an existing regular file, not a symlink"
        raise ValueError(message)
    metadata = credential.stat()
    if metadata.st_uid != os.getuid() or (stat.S_IMODE(metadata.st_mode) & 0o077) != 0:
        message = "api-key must be owned by the caller and private (0600)"
        raise ValueError(message)
    runtime_text = os.environ.get("XDG_RUNTIME_DIR")
    if runtime_text is None:
        message = "a rootless user runtime directory is required"
        raise ValueError(message)
    runtime = Path(runtime_text)
    private_directory(runtime)
    docker_socket = runtime / "docker.sock"
    if not docker_socket.is_socket():
        message = "rootless Docker socket is missing"
        raise ValueError(message)
    # Global to this user's rootless daemon for supported Nix controllers;
    # the state lock also coordinates Docker delivery using the same state.
    lock_paths = (
        runtime / "qwen-inference-controller.lock",
        state / "qwen-inference-launch.lock",
    )
    with ExitStack() as locks:
        for lock_path in lock_paths:
            descriptor = os.open(
                lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600
            )
            lock = locks.enter_context(os.fdopen(descriptor, "r+"))
            lock_metadata = os.fstat(lock.fileno())
            if (
                not stat.S_ISREG(lock_metadata.st_mode)
                or lock_metadata.st_uid != os.getuid()
                or (stat.S_IMODE(lock_metadata.st_mode) & 0o077) != 0
            ):
                message = "lock must be a private caller-owned regular file"
                raise ValueError(message)
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        environment = dict(os.environ)
        environment["DOCKER_HOST"] = "unix://" + str(docker_socket)
        environment["QWEN_STATE_ROOT"] = str(state)
        project = "qwen-inference-" + hashlib.sha256(os.fsencode(state)).hexdigest()
        compose = [
            "docker-compose",
            "--project-name",
            project,
            "-f",
            os.environ["QWEN_COMPOSE"],
        ]
        supervisor = [
            sys.executable,
            os.environ["QWEN_SUPERVISOR"],
            str(args.port),
            str(credential),
            "qwen3.8-27b",
        ]
        if not args.systemd:
            supervisor.append("--standalone")
        signal.signal(signal.SIGINT, stop_requested)
        signal.signal(signal.SIGTERM, stop_requested)
        stopped = False
        while True:
            # Cleanup is the gate: retain the lifetime lock and do not prepare
            # another attempt until Docker confirms the old deployment is down.
            clean, requested = cleanup(compose, environment)
            stopped = stopped or requested
            if stopped:
                if clean:
                    print("Serving stopped and deployment cleaned up.", flush=True)
                    return 0
                print(
                    "Stop requested but cleanup failed; operator cleanup is required.",
                    file=sys.stderr,
                )
                return 1
            if not clean:
                try:
                    time.sleep(20)
                except StopRequested:
                    stopped = True
                continue
            failed = False
            try:
                execute(
                    [*compose, "run", "--rm", "prepare"],
                    env=environment,
                    check=True,
                    timeout=2700,
                )
                _wait_for_idle_gpu()
                execute(
                    [*compose, "up", "-d", "--remove-orphans", "inference"],
                    env=environment,
                    check=True,
                    timeout=2700,
                )
                execute(supervisor, env=environment, check=True)
                message = "supervisor exited unexpectedly"
                raise ValueError(message)
            except StopRequested:
                stopped = True
            except (subprocess.SubprocessError, OSError, ValueError) as failure:
                failed = True
                print(
                    "Guarded serving attempt failed ("
                    + type(failure).__name__
                    + "); cleaning up before retry.",
                    flush=True,
                )
            # Always complete a bounded cleanup, even after repeated signals.
            while True:
                clean, requested = cleanup(compose, environment)
                stopped = stopped or requested
                if clean:
                    break
                if stopped:
                    print(
                        "Stop requested but cleanup failed; "
                        "operator cleanup is required.",
                        file=sys.stderr,
                    )
                    return 1
                try:
                    time.sleep(20)
                except StopRequested:
                    stopped = True
            if stopped:
                print("Serving stopped and deployment cleaned up.", flush=True)
                return 0
            if args.systemd and failed:
                # Let systemd reset readiness on its next guarded invocation.
                return 1
            try:
                time.sleep(20)
            except StopRequested:
                stopped = True


if __name__ == "__main__":
    try:
        sys.exit(main())
    except CleanupIncomplete:
        print(
            "Command group cleanup incomplete; "
            "operator verification is required before restart.",
            file=sys.stderr,
        )
        sys.exit(78)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(
            "Serving launcher failed: "
            + type(error).__name__
            + ". Check prerequisites and stop competing deployments.",
            file=sys.stderr,
        )
        sys.exit(1)
