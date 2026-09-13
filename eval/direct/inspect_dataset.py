#!/usr/bin/env python3
# Copyright (c) 2026 inference contributors
"""Inspect native upstream configs and datasets without constructing a client."""

import argparse
import json
import sys
from pathlib import Path

import verifiers as vf
from verifiers.utils.eval_utils import load_toml_config

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("config", type=Path)
arguments = parser.parse_args()
configs = load_toml_config(arguments.config)
for config in configs:
    env = vf.load_environment(config["env_id"], **config.get("env_args", {}))
    dataset = env.get_eval_dataset(n=config["num_examples"])
    if len(dataset) == 0:
        message = f"No native examples matched {config['name']}"
        raise ValueError(message)
    message_counts = [len(row["prompt"]) for row in dataset]
    prompt_characters = [
        sum(len(message["content"]) for message in row["prompt"]) for row in dataset
    ]
    json.dump(
        {
            "environment": config["env_id"],
            "name": config["name"],
            "environment_type": type(env).__name__,
            "examples": len(dataset),
            "rollouts_per_example": config["rollouts_per_example"],
            "max_concurrent": config["max_concurrent"],
            "independent_scoring": config["independent_scoring"],
            "prompt_message_counts": sorted(set(message_counts)),
            "prompt_characters_min": min(prompt_characters, default=None),
            "prompt_characters_max": max(prompt_characters, default=None),
            "character_counts_are_not_model_tokens": True,
            "sampling": config["sampling_args"],
            "requests_sent": 0,
        },
        sys.stdout,
        sort_keys=True,
    )
    sys.stdout.write("\n")
