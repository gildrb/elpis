#!/usr/bin/env python3
import json
import os
import urllib.request

key_path = os.environ.get("QWEN_API_KEY_FILE", "/app/api_key.txt")
payload = {
    "model": "qwen3.8-27b",
    "messages": [{"role": "user", "content": "Call health_check with status ok."}],
    "tools": [{
        "type": "function",
        "function": {
            "name": "health_check",
            "description": "Report inference health.",
            "parameters": {
                "type": "object",
                "properties": {"status": {"type": "string"}},
                "required": ["status"],
            },
        },
    }],
    "tool_choice": {"type": "function", "function": {"name": "health_check"}},
    "temperature": 0,
    "max_tokens": 64,
    "chat_template_kwargs": {"enable_thinking": False},
}
request = urllib.request.Request(
    "http://127.0.0.1:18020/v1/chat/completions",
    data=json.dumps(payload).encode(),
    headers={
        "Authorization": "Bearer " + open(key_path).read().strip(),
        "Content-Type": "application/json",
    },
)
with urllib.request.urlopen(request, timeout=180) as response:
    result = json.load(response)
call = result["choices"][0]["message"]["tool_calls"][0]
arguments = json.loads(call["function"]["arguments"])
print(json.dumps({"function": call["function"]["name"], "arguments": arguments}, sort_keys=True))
raise SystemExit(0 if call["function"]["name"] == "health_check" and arguments.get("status") == "ok" else 1)
