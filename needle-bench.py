#!/usr/bin/env python3
"""Bounded retrieval fixture for the current compact SGLang profile.

The 12,000 estimated-token ceiling is fixture policy, not the model's 24,576
context limit. Actual prompt token usage is reported by the API. Set
QWEN_API_KEY_FILE to the host key path when running outside the container.
"""
import json
import math
import os
import sys
import time
import urllib.request

key_path = os.environ.get("QWEN_API_KEY_FILE", "/app/api_key.txt")
api = os.environ.get("QWEN_API", "http://127.0.0.1:18020/v1")
if len(sys.argv) > 3:
    raise SystemExit("Usage: needle-bench.py [estimated_tokens: 1..12000] [depth: 0..1]")
try:
    target_tokens = int(sys.argv[1]) if len(sys.argv) > 1 else 12_000
    depth = float(sys.argv[2]) if len(sys.argv) > 2 else 0.9
except ValueError as error:
    raise SystemExit(f"Invalid retrieval fixture argument: {error}") from error
if not 1 <= target_tokens <= 12_000:
    raise SystemExit("Estimated tokens must be 1..12000 for this bounded fixture.")
if not math.isfinite(depth) or not 0 <= depth <= 1:
    raise SystemExit("Depth must be finite and between 0 and 1.")
needle = "ZXCVBNM12345"
unit = "All work and no play makes Jack a dull boy. "
filler = unit * int(target_tokens / 11)
offset = int(len(filler) * depth)
prompt = (
    filler[:offset]
    + f"\n\nThe secret passcode is {needle}. Remember it exactly.\n\n"
    + filler[offset:]
    + "\n\nWhat is the secret passcode? Reply with the passcode only."
)
payload = {
    "model": "qwen3.8-27b",
    "messages": [{"role": "user", "content": prompt}],
    "max_tokens": 64,
    "temperature": 0,
    "chat_template_kwargs": {"enable_thinking": False},
}
request = urllib.request.Request(
    api + "/chat/completions",
    data=json.dumps(payload).encode(),
    headers={
        "Authorization": "Bearer " + open(key_path).read().strip(),
        "Content-Type": "application/json",
    },
)
started = time.perf_counter()
with urllib.request.urlopen(request, timeout=1800) as response:
    result = json.load(response)
elapsed = time.perf_counter() - started
choice = result["choices"][0]
answer = choice["message"].get("content") or ""
usage = result.get("usage", {})
print(json.dumps({
    "target_tokens": target_tokens,
    "prompt_tokens": usage.get("prompt_tokens"),
    "completion_tokens": usage.get("completion_tokens"),
    "depth": depth,
    "elapsed_seconds": round(elapsed, 3),
    "finish_reason": choice.get("finish_reason"),
    "answer": answer,
    "retrieved": needle in answer,
}, sort_keys=True))
raise SystemExit(0 if needle in answer else 1)
