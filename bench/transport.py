"""Bounded OpenAI chat transport and private benchmark artifact primitives."""

from __future__ import annotations

import hashlib
import json
import os
import re
import time
import traceback
from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal, Self
from urllib.parse import urlsplit

import httpx
from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    JsonValue,
    TypeAdapter,
    model_validator,
)

if TYPE_CHECKING:
    from pathlib import Path

MAX_PORT = 65535
MAX_MESSAGES = 1000
MAX_KEY_LENGTH = 16384

JSON = TypeAdapter(JsonValue)


class RequestSettings(BaseModel):
    """Strict chat endpoint and generation settings."""

    model_config = ConfigDict(extra="forbid", strict=True, frozen=True)
    endpoint: str
    model: str = Field(min_length=1, max_length=1024)
    thinking: Literal["enabled", "disabled"] = "enabled"
    max_tokens: int = Field(default=8192, ge=1, le=65536)
    timeout: int = Field(default=600, ge=1, le=3600)

    @model_validator(mode="after")
    def validate_endpoint(self) -> Self:
        """Validate endpoint security constraints and model identity syntax.

        Returns:
            This settings instance after validation.

        Raises:
            ValueError: If validation or request preconditions fail.

        """
        endpoint = urlsplit(self.endpoint)
        port = endpoint.port
        if port is not None and not 1 <= port <= MAX_PORT:
            message = "Invalid endpoint port"
            raise ValueError(message)
        invalid_suffix = (
            len(endpoint.query) > 0
            or len(endpoint.fragment) > 0
            or endpoint.path.rstrip("/") != "/v1"
        )
        if (
            endpoint.scheme not in {"http", "https"}
            or endpoint.hostname is None
            or endpoint.username is not None
            or endpoint.password is not None
            or invalid_suffix
        ):
            message = "Endpoint must be HTTP(S) /v1 without credentials/query/fragment"
            raise ValueError(message)
        if endpoint.scheme == "http" and endpoint.hostname not in {
            "127.0.0.1",
            "localhost",
            "::1",
        }:
            message = "Non-loopback endpoints require HTTPS"
            raise ValueError(message)
        if len(self.model.strip()) == 0:
            message = "Model must not be blank"
            raise ValueError(message)
        return self


class ChatMessage(BaseModel):
    """One bounded chat message accepted by the request transport."""

    model_config = ConfigDict(extra="forbid", strict=True, frozen=True)
    role: Literal["system", "user", "assistant"]
    content: str = Field(min_length=1, max_length=2_000_000)


class ApiFailure(BaseModel):
    """Sanitized request failure identity and elapsed time."""

    model_config = ConfigDict(extra="forbid", strict=True, frozen=True)
    error_type: str
    elapsed_seconds: float = Field(ge=0, allow_inf_nan=False)


class TokenDetails(BaseModel):
    """Optional cached and reasoning token counts."""

    model_config = ConfigDict(extra="ignore", strict=True)
    cached_tokens: int | None = Field(default=None, ge=0)
    reasoning_tokens: int | None = Field(default=None, ge=0)


class Usage(BaseModel):
    """Validated prompt and completion token usage."""

    model_config = ConfigDict(extra="ignore", strict=True)
    prompt_tokens: int = Field(ge=0)
    completion_tokens: int = Field(ge=0)
    prompt_tokens_details: TokenDetails | None = None
    completion_tokens_details: TokenDetails | None = None


class Message(BaseModel):
    """One assistant response with optional reasoning content."""

    model_config = ConfigDict(extra="ignore", strict=True)
    role: Literal["assistant"]
    content: str | None
    reasoning_content: str | None = None


class Choice(BaseModel):
    """The sole response choice and its finish reason."""

    model_config = ConfigDict(extra="ignore", strict=True)
    index: Literal[0]
    message: Message
    finish_reason: str


class Completion(BaseModel):
    """Validated single-choice chat completion."""

    model_config = ConfigDict(extra="ignore", strict=True)
    model: str = Field(min_length=1)
    usage: Usage | None = None
    choices: list[Choice] = Field(min_length=1, max_length=1)


class CompletedRequest(BaseModel):
    """Validated completion and measured elapsed time."""

    model_config = ConfigDict(extra="forbid", strict=True, frozen=True)
    completion: Completion
    elapsed_seconds: float = Field(ge=0, allow_inf_nan=False)


def unique_object(pairs: list[tuple[str, JsonValue]]) -> dict[str, JsonValue]:
    """Build a JSON object without duplicate keys.

    Returns:
        The object with unique keys and original JSON values.

    Raises:
        ValueError: If validation or request preconditions fail.

    """
    result: dict[str, JsonValue] = {}
    for key, value in pairs:
        if key in result:
            message = "Duplicate JSON key"
            raise ValueError(message)
        result[key] = value
    return result


def invalid_constant(value: str) -> None:
    """Reject non-finite JSON constants.

    Raises:
        ValueError: If validation or request preconditions fail.

    """
    message = "Non-finite JSON constant: " + value
    raise ValueError(message)


def read_bounded(path: Path, limit: int = 8 * 1024 * 1024) -> str:
    """Read a bounded UTF-8 file.

    Returns:
        The file content decoded as UTF-8.

    Raises:
        ValueError: If validation or request preconditions fail.

    """
    with path.open("rb") as stream:
        content = stream.read(limit + 1)
    if len(content) > limit:
        message = "Input file exceeds byte limit"
        raise ValueError(message)
    return content.decode("utf-8")


def decode(text: str) -> JsonValue:
    """Decode strict JSON while rejecting duplicate keys and constants.

    Returns:
        The validated JSON value.

    """
    value: object = json.loads(
        text, object_pairs_hook=unique_object, parse_constant=invalid_constant
    )
    return JSON.validate_python(value, strict=True)


def canonical(value: object) -> bytes:
    """Encode deterministic UTF-8 JSON bytes.

    Returns:
        The canonical JSON encoding.

    """
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode()


def digest(value: object) -> str:
    """Return the SHA-256 digest of canonical JSON bytes.

    Returns:
        The hexadecimal SHA-256 digest.

    """
    return hashlib.sha256(canonical(value)).hexdigest()


def write_private(path: Path, value: object) -> None:
    # Exclusive creation: a failed initialization cannot overwrite another run.
    """Exclusively create and sync a private canonical JSON artifact."""
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(canonical(value) + b"\n")
        stream.flush()
        os.fsync(stream.fileno())


def _read_response(response: httpx.Response, output: Path, stem: str) -> list[bytes]:
    chunks: list[bytes] = []
    size = 0
    for chunk in response.iter_bytes(chunk_size=65536):
        size += len(chunk)
        if size > 16 * 1024 * 1024:
            write_private(
                output / f"{stem}-raw.json",
                {
                    "http_status": response.status_code,
                    "oversized": True,
                    "body_prefix": b"".join(chunks).decode("utf-8", errors="replace"),
                },
            )
            message = "API response exceeds 16 MiB"
            raise ValueError(message)
        chunks.append(chunk)
    return chunks


def _record_response(
    response: httpx.Response, chunks: list[bytes], output: Path, stem: str
) -> str:
    body = b"".join(chunks).decode("utf-8")
    write_private(
        output / f"{stem}-raw.json",
        {"http_status": response.status_code, "body": body},
    )
    response.raise_for_status()
    return body


def _validate_completion(body: str, settings: RequestSettings) -> Completion:
    completion = Completion.model_validate(decode(body))
    usage = completion.usage
    if usage is not None:
        if usage.completion_tokens > settings.max_tokens:
            message = "Completion usage exceeds requested output cap"
            raise ValueError(message)
        if usage.prompt_tokens_details is not None:
            cached = usage.prompt_tokens_details.cached_tokens
            if cached is not None and cached > usage.prompt_tokens:
                message = "Cached usage exceeds prompt usage"
                raise ValueError(message)
        if usage.completion_tokens_details is not None:
            reasoning = usage.completion_tokens_details.reasoning_tokens
            if reasoning is not None and reasoning > usage.completion_tokens:
                message = "Reasoning usage exceeds completion usage"
                raise ValueError(message)
    if completion.model != settings.model:
        message = "Response model does not match requested served model"
        raise ValueError(message)
    return completion


@dataclass(frozen=True)
class ArtifactTarget:
    """Caller-owned private directory and request artifact stem."""

    output: Path
    stem: str


def request_completion(
    client: httpx.Client,
    settings: RequestSettings,
    key: str,
    messages: tuple[ChatMessage, ...],
    target: ArtifactTarget,
) -> CompletedRequest | ApiFailure:
    """Send one bounded chat request and retain its private artifacts.

    The caller owns a private output directory and a trust_env=False C1 client.
    The artifact stem is validated before the request starts.

    Returns:
        A validated completion or a recorded API failure.

    Raises:
        RuntimeError: If the completed request has no measured elapsed time.
        ValueError: If validation or request preconditions fail.

    """
    output, stem = target.output, target.stem
    if re.fullmatch(r"[a-z0-9-]{1,100}", stem) is None:
        message = "Invalid artifact stem"
        raise ValueError(message)
    if (
        not 1 <= len(messages) <= MAX_MESSAGES
        or len(canonical([message.model_dump() for message in messages]))
        > 2 * 1024 * 1024
    ):
        message = "Request messages exceed bounds"
        raise ValueError(message)
    if len(key) == 0 or len(key) > MAX_KEY_LENGTH or re.search(r"\s", key) is not None:
        message = "Invalid API key"
        raise ValueError(message)
    if client.follow_redirects:
        message = "Benchmark client must disable redirects"
        raise ValueError(message)
    payload = {
        "model": settings.model,
        "messages": [message.model_dump() for message in messages],
        "temperature": 0,
        "max_tokens": settings.max_tokens,
        "stream": False,
        "chat_template_kwargs": {"enable_thinking": settings.thinking == "enabled"},
    }
    start = time.monotonic()
    elapsed: float | None = None
    try:
        with client.stream(
            "POST",
            settings.endpoint.rstrip("/") + "/chat/completions",
            headers={"Authorization": "Bearer " + key},
            json=payload,
        ) as response:
            chunks = _read_response(response, output, stem)
            elapsed = time.monotonic() - start
            body = _record_response(response, chunks, output, stem)
        completion = _validate_completion(body, settings)
    except (httpx.HTTPError, ValueError) as error:
        write_private(
            output / f"{stem}-api-error.json",
            {"type": type(error).__name__, "traceback": traceback.format_exc()},
        )
        return ApiFailure(
            error_type=type(error).__name__,
            elapsed_seconds=time.monotonic() - start if elapsed is None else elapsed,
        )
    if elapsed is None:
        message = "Completed HTTP request has no elapsed time"
        raise RuntimeError(message)
    return CompletedRequest(completion=completion, elapsed_seconds=elapsed)
