#!/usr/bin/env python3
import concurrent.futures
import json
import os
import re
import sys
import time
import urllib.request

fixture = sys.argv[1] if len(sys.argv) > 1 else "gsm8k-200.json"
key_path = os.environ.get("QWEN_API_KEY_FILE", "/mnt/ssd/storage/ai/qwen3.8-27b/api-key")
api = os.environ.get("QWEN_API", "http://127.0.0.1:18020/v1")
workers = int(os.environ.get("GSM8K_WORKERS", "1"))
if workers < 1:
    raise SystemExit("GSM8K_WORKERS must be a positive integer.")
rows = json.load(open(fixture))
key = open(key_path).read().strip()


def extract_number(text):
    matches = re.findall(r"-?\d[\d,]*\.?\d*", text.replace("$", ""))
    return matches[-1].replace(",", "") if matches else None


def score(item):
    index, row = item
    gold = row["answer"].split("####")[-1].strip().replace(",", "")
    payload = {
        "model": "qwen3.8-27b",
        "messages": [{
            "role": "user",
            "content": row["question"] + "\n\nSolve step by step, then give the final answer as 'Final answer: <number>'.",
        }],
        "max_tokens": 768,
        "temperature": 0,
        "chat_template_kwargs": {"enable_thinking": False},
    }
    request = urllib.request.Request(
        api + "/chat/completions",
        data=json.dumps(payload).encode(),
        headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(request, timeout=1200) as response:
        result = json.load(response)
    text = result["choices"][0]["message"].get("content") or ""
    match = re.search(r"Final answer:\s*\**\s*\$?(-?[\d,]*\.?\d+)", text)
    predicted = match.group(1).replace(",", "") if match else extract_number(text)
    try:
        passed = abs(float(predicted) - float(gold)) < 1e-6
    except (TypeError, ValueError):
        passed = False
    return {
        "index": index,
        "expected": gold,
        "predicted": predicted,
        "passed": passed,
        "completion_tokens": result["usage"]["completion_tokens"],
    }


started = time.perf_counter()
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
    results = list(executor.map(score, enumerate(rows)))
elapsed = time.perf_counter() - started
passed = sum(item["passed"] for item in results)
summary = {
    "model": "qwen3.8-27b",
    "count": len(results),
    "passed": passed,
    "accuracy": passed / len(results),
    "mean_completion_tokens": sum(item["completion_tokens"] for item in results) / len(results),
    "elapsed_seconds": elapsed,
    "workers": workers,
    "failures": [item for item in results if not item["passed"]],
}
print(json.dumps(summary, indent=2, sort_keys=True))
raise SystemExit(0 if summary["accuracy"] >= 0.95 else 1)
