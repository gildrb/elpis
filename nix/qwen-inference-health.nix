{
  lib,
  pkgs,
  port,
  stateRoot,
  readinessBudgetSeconds ? 120,
  retryDelaySeconds ? 5,
}:

pkgs.writeShellApplication {
  name = "qwen-inference-health";
  runtimeInputs = [
    pkgs.coreutils
    pkgs.curl
    pkgs.jq
  ];
  text = ''
    key_file=${lib.escapeShellArg "${stateRoot}/api-key"}
    [[ -s "$key_file" ]] || {
      echo "Qwen API key is missing." >&2
      exit 1
    }

    # Normal model loading is about 81 seconds. Two minutes covers a 90-second
    # cold start plus polling and request jitter without hiding a stuck load.
    readiness_deadline=$((SECONDS + ${toString readinessBudgetSeconds}))
    ready=false
    while (( SECONDS < readiness_deadline )); do
      if curl -fsS --max-time 5 -o /dev/null \
        http://127.0.0.1:${toString port}/health; then
        ready=true
        break
      fi
      remaining=$((readiness_deadline - SECONDS))
      (( remaining > 0 )) || break
      sleep_seconds=${toString retryDelaySeconds}
      if (( sleep_seconds > remaining )); then
        sleep_seconds=$remaining
      fi
      sleep "$sleep_seconds"
    done
    if [[ "$ready" != true ]]; then
      echo "Qwen API did not become ready within ${toString readinessBudgetSeconds} seconds." >&2
      exit 1
    fi

    response="$(mktemp)"
    trap 'rm -f "$response"' EXIT
    for attempt in 1 2; do
      if curl -fsS --max-time 120 \
        -H "Authorization: Bearer $(cat "$key_file")" \
        -H 'Content-Type: application/json' \
        -o "$response" \
        -d '{
          "model": "qwen3.8-27b",
          "messages": [{"role": "user", "content": "Call health_check with status ok."}],
          "tools": [{
            "type": "function",
            "function": {
              "name": "health_check",
              "description": "Report inference health.",
              "parameters": {
                "type": "object",
                "properties": {"status": {"type": "string", "enum": ["ok"]}},
                "required": ["status"],
                "additionalProperties": false
              }
            }
          }],
          "tool_choice": {"type": "function", "function": {"name": "health_check"}},
          "temperature": 0,
          "max_tokens": 64,
          "chat_template_kwargs": {"enable_thinking": false}
        }' \
        http://127.0.0.1:${toString port}/v1/chat/completions &&
        jq -e '
          .choices[0].message.tool_calls[0].function
          | .name == "health_check"
            and ((.arguments | fromjson) == {"status": "ok"})
        ' "$response" >/dev/null; then
        exit 0
      fi
      (( attempt < 2 )) && sleep ${toString retryDelaySeconds}
    done
    jq -r '.error.message // "Qwen completion/tool health check failed."' \
      "$response" >&2 2>/dev/null || true
    exit 1
  '';
}
