#!/usr/bin/env python3
"""Compile the real probe, enumerate the declared fault model, and check outcomes."""
import argparse
import csv
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--portable', action='store_true')
parser.add_argument('--sanitize', action='store_true')
args = parser.parse_args()
variant = 'sanitize' if args.sanitize else 'portable' if args.portable else 'native'
build = ROOT / 'build' / 'observability'
build.mkdir(parents=True, exist_ok=True)
cc = os.environ.get('CC', 'cc')
flags = ['-std=c11', '-Wall', '-Wextra', '-Wpedantic', '-Werror', '-O2']
if args.portable:
    flags += ['-DBX_PORTABLE']
if args.sanitize:
    flags += ['-O1', '-g', '-fsanitize=address,undefined', '-fno-omit-frame-pointer']
binary = build / variant
command = [cc, *flags, '-I.', 'experiments/observability.c', 'bitoxin_core.c', '-o', str(binary)]
subprocess.run(command, cwd=ROOT, check=True)
raw = subprocess.run([str(binary)], cwd=ROOT, check=True, capture_output=True).stdout
rows = list(csv.DictReader(io.StringIO(raw.decode())))
assert len(rows) == 61560, len(rows)
groups = defaultdict(list)
controls = 0
for row in rows:
    for key in ('seed', 'direction', 'boundary', 'bit', 'current_detected', 'following_detected', 'attempts', 'reported_bit'):
        row[key] = int(row[key])
    if row['bit'] == -1:
        assert row['current_detected'] == row['following_detected'] == 0
        controls += 1
    else:
        groups[(row['experiment'], row['policy'], row['seed'], row['direction'], row['boundary'])].append(row)
assert controls == 120
summary_groups = defaultdict(list)
for (experiment, policy, seed, direction, boundary), group in groups.items():
    assert len(group) == 512 and {r['bit'] for r in group} == set(range(512))
    expected = (512 - 8 * boundary if experiment == 'scan_boundary' else
                512 if policy == 'retain_scan' else
                512 - boundary if policy == 'walk_only' else 0)
    assert sum(r['current_detected'] for r in group) == expected
    if experiment == 'scan_boundary':
        assert sum(r['following_detected'] for r in group) == 512
    for r in group:
        if r['phase'] == 'walk':
            assert r['reported_bit'] == r['bit']
        elif r['phase'] == 'verify':
            assert r['reported_bit'] == r['bit'] // 8 * 8
        else:
            assert not r['following_detected']
    summary_groups[(experiment, policy, boundary)] += group
summary = []
for (experiment, policy, boundary), group in sorted(summary_groups.items()):
    detected = [r['attempts'] for r in group if r['following_detected']]
    summary.append(dict(experiment=experiment, policy=policy, boundary=boundary,
                        trials=len(group), current_detected=sum(r['current_detected'] for r in group),
                        following_detected=sum(r['following_detected'] for r in group),
                        max_detection_attempts=max(detected, default=0)))
out = ROOT / 'paper' / 'data'
out.mkdir(parents=True, exist_ok=True)
report = dict(variant=variant, injected_trials=61440, clean_controls=controls,
              raw_sha256=hashlib.sha256(raw).hexdigest(), compiler=subprocess.check_output([cc, '--version'], text=True).splitlines()[0],
              command=command[:-1] + ['build/observability/' + variant], groups=summary)
(out / (variant + '-summary.json')).write_text(json.dumps(report, indent=2) + '\n')
if variant == 'native':
    with open(out / 'trials.csv.gz', 'wb') as f:
        f.write(gzip.compress(raw, mtime=0))
    with (out / 'summary.csv').open('w') as f:
        writer = csv.DictWriter(f, fieldnames=summary[0].keys())
        writer.writeheader(); writer.writerows(summary)
else:
    reference = json.loads((out / 'native-summary.json').read_text())
    assert report['raw_sha256'] == reference['raw_sha256'], 'backend outcome divergence'
print(f'{variant}: {report["injected_trials"]} injected trials, {controls} clean controls; model checks PASS; raw sha256 {report["raw_sha256"]}')
