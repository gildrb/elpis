#!/usr/bin/env python3
"""Create a stopped, guardian-gated candidate container.

usage: mkcand.py run|serve NAME IMAGE WINDOW [--cmd JSON_LIST] [--mount SRC:DST[:ro]]...
  run   : one-shot payload (parity/bench/profile) from the parity compose template, no ports
  serve : the OpenAI server on 127.0.0.1:18020 from the autoresearch compose template
"""
import argparse, copy, json, subprocess, sys
from pathlib import Path

S = Path('/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2')
ap = argparse.ArgumentParser()
ap.add_argument('mode', choices=('run', 'serve'))
ap.add_argument('name'); ap.add_argument('image'); ap.add_argument('window')
ap.add_argument('--cmd', default=None)
ap.add_argument('--mount', action='append', default=[])
ap.add_argument('--env', action='append', default=[])
a = ap.parse_args()
if not (a.image.startswith('sha256:') and len(a.image) == 71):
    sys.exit('full image id required')
if (S / a.window).exists():
    sys.exit('window directory already exists: must be fresh')
if a.mode == 'run':
    tmpl = json.loads((S / 'evidence/parity-1/compose.json').read_text())
    svc = copy.deepcopy(tmpl['services']['b'])
    svc['volumes'] = [v for v in svc['volumes'] if v['target'] not in ('/parity.py', '/out')]
    if a.cmd is None:
        sys.exit('run mode needs --cmd')
    cmd = json.loads(a.cmd)
    nets = None
else:
    tmpl = json.loads((S / 'ar/compose-g3.json').read_text())
    svc = copy.deepcopy(tmpl['services']['g3'])
    cmd = ['bash', '/opt/qwen/serve/entrypoint.sh']
    nets = tmpl['networks']
for m in a.mount:
    parts = m.split(':')
    v = {'type': 'bind', 'source': parts[0], 'target': parts[1]}
    if len(parts) > 2 and parts[2] == 'ro':
        v['read_only'] = True
    svc['volumes'].append(v)
for e in a.env:
    k, sep, val = e.partition('=')
    if not sep or not k:
        sys.exit(f'bad --env {e!r}: need KEY=VALUE')
    envs = svc.setdefault('environment', {})
    if isinstance(envs, list):
        envs.append(f'{k}={val}')
    else:
        envs[k] = val
svc['container_name'] = a.name
svc['image'] = a.image
svc['entrypoint'] = ['python3', '/maintenance-control/launch-gate.py', '--window', a.window,
                     '--candidate-name', a.name, '--candidate-image', a.image, '--'] + cmd
doc = {'name': 'elpis-' + a.name, 'services': {'c': svc}}
if nets:
    doc['networks'] = nets
out = Path('/tmp/cand') / f'{a.name}.json'
out.parent.mkdir(exist_ok=True)
out.write_text(json.dumps(doc, indent=1))
env = dict(__import__('os').environ, DOCKER_HOST='unix:///run/user/1000/docker.sock')
subprocess.run(['docker', 'rm', '-f', a.name], env=env, capture_output=True)
subprocess.run(['docker', 'compose', '-f', str(out), 'create', '--no-build', '--pull', 'never'],
               env=env, check=True, capture_output=True)
cid = subprocess.run(['docker', 'inspect', '-f', '{{.Id}} {{.State.Status}}', a.name], env=env,
                     check=True, capture_output=True, text=True).stdout.strip()
print(cid)
