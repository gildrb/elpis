#!/usr/bin/env python3
"""Notify systemd only after bounded scheduler-health and authenticated API probes.

Failure exits deliberately: ExecStopPost removes the container and systemd
retries the complete original-source/model/replacement guarded startup.
"""

import http.client
import json
import os
import signal
import socket
import sys
import time
from pathlib import Path
from types import FrameType

MAX_PORT = 65535
MAX_KEY_BYTES = 4096
MIN_KEY_CHARACTER = 33
MAX_KEY_CHARACTER = 126
SYSTEMD_ARG_COUNT = 4
STANDALONE_ARG_COUNT = 5
HTTP_OK = 200


# SGLang /health generates one token when idle and accepts any scheduler
# response while busy. The server allows 300s without progress so the qualified
# ~75s full-context prefill does not trip a short HTTP watchdog. Three failures
# tolerate transient stalls; this is not a guarantee for unbounded workloads.
PROBE_SECONDS = 310
STARTUP_SECONDS = 20 * 60
INTERVAL_SECONDS = 30
FAILURE_LIMIT = 3
MAX_BODY_BYTES = 65536


def deadline_expired(_signum: int, _frame: FrameType | None) -> None:
    """Interrupt the current probe when its whole-exchange budget expires.

    Raises:
        TimeoutError: The API exchange exceeded its deadline.

    """
    message = "API probe deadline exceeded"
    raise TimeoutError(message)


def notify(message: str) -> None:
    """Send a readiness message to the configured systemd socket.

    Raises:
        ValueError: A required configuration or input check failed.

    """
    address = os.environ.get("NOTIFY_SOCKET")
    if address is None or len(address) == 0:
        message = "systemd notification socket is required"
        raise ValueError(message)
    if address.startswith("@"):
        address = "\0" + address[1:]
    elif not address.startswith("/"):
        message = "invalid systemd notification socket"
        raise ValueError(message)
    with socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM) as channel:
        channel.settimeout(10)
        channel.connect(address)
        channel.sendall(message.encode("utf-8"))


def _check_models(response: http.client.HTTPResponse, model: str) -> str | None:
    """Validate every inventory entry without exposing response content.

    Returns:
        A private failure description, or None on success.

    """
    body = response.read(MAX_BODY_BYTES + 1)
    if len(body) > MAX_BODY_BYTES:
        return "models: invalid or oversized JSON schema"
    payload: object = json.loads(body)
    if not isinstance(payload, dict):
        return "models: invalid or oversized JSON schema"
    models: object = payload.get("data")
    if not isinstance(models, list):
        return "models: invalid or oversized JSON schema"
    found = False
    for item in models:
        if not isinstance(item, dict):
            return "models: invalid or oversized JSON schema"
        identifier: object = item.get("id")
        if not isinstance(identifier, str):
            return "models: invalid or oversized JSON schema"
        if identifier == model:
            found = True
    return None if found else "models: expected model missing"


def _probe_endpoints(port: int, key: str, model: str, budget: float) -> str | None:
    """Close each connection before reporting its health or inventory failure.

    Returns:
        A private failure description, or None on success.

    """
    for path in ("/health", "/v1/models"):
        connection = http.client.HTTPConnection("127.0.0.1", port, timeout=budget)
        try:
            connection.request("GET", path, headers={"Authorization": "Bearer " + key})
            response = connection.getresponse()
            if response.status != HTTP_OK:
                return f"{path}: HTTP {response.status}"
            if path == "/v1/models":
                failure = _check_models(response, model)
                if failure is not None:
                    return failure
        finally:
            connection.close()
    return None


def probe(port: int, key: str, model: str, budget: float) -> str | None:
    """Check scheduler health and the authenticated model inventory.

    Returns:
        A private failure description, or None on success.

    """
    # SIGALRM bounds the entire exchange, including slowly arriving bodies.
    signal.setitimer(signal.ITIMER_REAL, budget)
    try:
        failure = _probe_endpoints(port, key, model, budget)
    except TimeoutError:
        return "API probe timeout"
    except OSError:
        return "API connection failure"
    except http.client.HTTPException:
        return "API HTTP protocol failure"
    except ValueError:
        return "models: invalid JSON"
    # Never expose response bodies, headers or exception text containing keys.
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    return failure


def _configuration() -> tuple[int, str, str, bool]:
    """Read and validate the CLI identity and bounded private credential.

    Returns:
        The port, key, model and standalone flag.

    Raises:
        ValueError: The identity or credential is invalid.

    """
    standalone = len(sys.argv) == STANDALONE_ARG_COUNT and sys.argv[4] == "--standalone"
    if len(sys.argv) != SYSTEMD_ARG_COUNT and not standalone:
        message = "expected port, credential path and model"
        raise ValueError(message)
    port_text, key_path, model = sys.argv[1:4]
    if not port_text.isascii() or not port_text.isdecimal():
        message = "invalid port"
        raise ValueError(message)
    port = int(port_text)
    if not 1 <= port <= MAX_PORT or model != "qwen3.8-27b":
        message = "invalid service identity"
        raise ValueError(message)
    with Path(key_path).open("rb") as credential:
        raw_key = credential.read(MAX_KEY_BYTES + 1)
    if len(raw_key) > MAX_KEY_BYTES:
        message = "credential is too large"
        raise ValueError(message)
    # Match the entrypoint's newline removal, but reject header injection.
    key = raw_key.decode("ascii").replace("\n", "")
    if len(key) == 0 or not all(
        MIN_KEY_CHARACTER <= ord(char) <= MAX_KEY_CHARACTER for char in key
    ):
        message = "invalid credential format"
        raise ValueError(message)
    return port, key, model, standalone


def main() -> int:
    """Monitor authenticated readiness and request restart after repeated failure.

    Returns:
        The process exit status.

    """
    port, key, model, standalone = _configuration()
    signal.signal(signal.SIGALRM, deadline_expired)
    deadline = time.monotonic() + STARTUP_SECONDS
    ready = False
    failures = 0
    while True:
        budget = float(PROBE_SECONDS)
        if not ready:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                print("Qwen readiness deadline exceeded.", flush=True)
                return 1
            budget = min(budget, remaining)
        failure = probe(port, key, model, budget)
        if failure is not None:
            print(f"Qwen probe failed: {failure}.", flush=True)
        if failure is None:
            failures = 0
            if not ready:
                if time.monotonic() >= deadline:
                    print("Qwen readiness deadline exceeded.", flush=True)
                    return 1
                if standalone:
                    print("Authenticated model API is ready.", flush=True)
                else:
                    notify("READY=1\nSTATUS=Authenticated model API is ready")
                ready = True
        elif ready:
            failures += 1
            if failures >= FAILURE_LIMIT:
                print(
                    "Qwen API failed three probes; requesting guarded restart.",
                    flush=True,
                )
                return 1
        if not ready and time.monotonic() >= deadline:
            print("Qwen readiness deadline exceeded.", flush=True)
            return 1
        time.sleep(
            INTERVAL_SECONDS if ready else min(5, max(0, deadline - time.monotonic()))
        )


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError):
        print("Qwen supervisor configuration or notification failed.", file=sys.stderr)
        sys.exit(1)
