{
  config,
  lib,
  pkgs,
  ...
}:

let
  qwen = config.workstation.qwenInference;
  prometheusDatasource = {
    type = "prometheus";
    uid = "prometheus";
  };
  qwenDashboardDirectory = pkgs.writeTextDir "qwen-inference.json" (
    builtins.toJSON {
      id = null;
      uid = "qwen-inference";
      title = "Qwen inference";
      tags = [
        "ai"
        "qwen"
        "sglang"
      ];
      timezone = "browser";
      schemaVersion = 39;
      version = 1;
      refresh = "10s";
      time = {
        from = "now-1h";
        to = "now";
      };
      panels = [
        {
          id = 1;
          type = "stat";
          title = "SGLang metrics";
          datasource = prometheusDatasource;
          gridPos = {
            h = 8;
            w = 6;
            x = 0;
            y = 0;
          };
          fieldConfig = {
            defaults = {
              mappings = [
                {
                  options = {
                    "0" = {
                      color = "red";
                      text = "down";
                    };
                    "1" = {
                      color = "green";
                      text = "up";
                    };
                  };
                  type = "value";
                }
              ];
              thresholds = {
                mode = "absolute";
                steps = [
                  {
                    color = "red";
                    value = null;
                  }
                  {
                    color = "green";
                    value = 1;
                  }
                ];
              };
            };
            overrides = [ ];
          };
          options = {
            colorMode = "value";
            graphMode = "none";
            justifyMode = "center";
            orientation = "auto";
            reduceOptions = {
              calcs = [ "lastNotNull" ];
              fields = "";
              values = false;
            };
          };
          targets = [
            {
              expr = ''up{job="qwen-inference"}'';
              refId = "A";
            }
          ];
        }
        {
          id = 2;
          type = "timeseries";
          title = "Requests";
          datasource = prometheusDatasource;
          gridPos = {
            h = 8;
            w = 18;
            x = 6;
            y = 0;
          };
          fieldConfig = {
            defaults.unit = "short";
            overrides = [ ];
          };
          options.legend = {
            displayMode = "list";
            placement = "bottom";
          };
          targets = [
            {
              expr = ''sum(sglang:num_running_reqs{job="qwen-inference"})'';
              legendFormat = "running";
              refId = "A";
            }
            {
              expr = ''sum(sglang:num_queue_reqs{job="qwen-inference"})'';
              legendFormat = "waiting";
              refId = "B";
            }
          ];
        }
        {
          id = 3;
          type = "timeseries";
          title = "Token throughput";
          datasource = prometheusDatasource;
          gridPos = {
            h = 8;
            w = 12;
            x = 0;
            y = 8;
          };
          fieldConfig = {
            defaults.unit = "tps";
            overrides = [ ];
          };
          options.legend = {
            displayMode = "list";
            placement = "bottom";
          };
          targets = [
            {
              expr = ''sum(rate(sglang:prompt_tokens_total{job="qwen-inference"}[$__rate_interval]))'';
              legendFormat = "prompt";
              refId = "A";
            }
            {
              expr = ''sum(rate(sglang:generation_tokens_total{job="qwen-inference"}[$__rate_interval]))'';
              legendFormat = "generation";
              refId = "B";
            }
          ];
        }
        {
          id = 4;
          type = "timeseries";
          title = "Cache usage";
          datasource = prometheusDatasource;
          gridPos = {
            h = 8;
            w = 12;
            x = 12;
            y = 8;
          };
          fieldConfig = {
            defaults = {
              max = 100;
              min = 0;
              unit = "percent";
            };
            overrides = [ ];
          };
          options.legend = {
            displayMode = "list";
            placement = "bottom";
          };
          targets = [
            {
              expr = ''100 * max(sglang:token_usage{job="qwen-inference"})'';
              legendFormat = "token usage";
              refId = "A";
            }
            {
              expr = ''100 * max(sglang:cache_hit_rate{job="qwen-inference"})'';
              legendFormat = "cache hit rate";
              refId = "B";
            }
          ];
        }
        {
          id = 5;
          type = "timeseries";
          title = "Request latency p95";
          datasource = prometheusDatasource;
          gridPos = {
            h = 8;
            w = 12;
            x = 0;
            y = 16;
          };
          fieldConfig = {
            defaults.unit = "s";
            overrides = [ ];
          };
          options.legend = {
            displayMode = "list";
            placement = "bottom";
          };
          targets = [
            {
              expr = ''histogram_quantile(0.95, sum by (le) (rate(sglang:time_to_first_token_seconds_bucket{job="qwen-inference"}[$__rate_interval])))'';
              legendFormat = "time to first token";
              refId = "A";
            }
            {
              expr = ''histogram_quantile(0.95, sum by (le) (rate(sglang:e2e_request_latency_seconds_bucket{job="qwen-inference"}[$__rate_interval])))'';
              legendFormat = "end to end";
              refId = "B";
            }
          ];
        }
        {
          id = 6;
          type = "timeseries";
          title = "Generate throughput";
          datasource = prometheusDatasource;
          gridPos = {
            h = 8;
            w = 12;
            x = 12;
            y = 16;
          };
          fieldConfig = {
            defaults.unit = "tps";
            overrides = [ ];
          };
          options.legend = {
            displayMode = "list";
            placement = "bottom";
          };
          targets = [
            {
              expr = ''sum(sglang:gen_throughput{job="qwen-inference"})'';
              legendFormat = "generate";
              refId = "A";
            }
          ];
        }
      ];
    }
  );
in
{
  config = lib.mkIf (qwen.enable && config.workstation.observability.enable) {
    services.prometheus.scrapeConfigs = lib.mkAfter [
      {
        job_name = "qwen-inference";
        metrics_path = "/metrics";
        scrape_interval = "15s";
        scrape_timeout = "5s";
        static_configs = [
          {
            targets = [ "127.0.0.1:${toString qwen.port}" ];
          }
        ];
      }
    ];

    services.grafana.provision.dashboards.settings.providers = lib.mkAfter [
      {
        name = "qwen-inference";
        options.path = qwenDashboardDirectory;
      }
    ];
  };
}
