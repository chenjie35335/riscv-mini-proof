#!/usr/bin/env python3
"""Lower existing resolved FIRRTL using the project's cached Mill classpath."""
import argparse
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('input', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
target = args.output.resolve()
if target.exists():
    parser.error('Output already exists; select a fresh path to preserve proof baselines.')
metadata = root / 'out/chiselModule/runClasspath/meta.json'
classpath = ':'.join(item.split(':', 2)[2] for item in json.loads(metadata.read_text())['value'])
target.parent.mkdir(parents=True, exist_ok=True)
subprocess.run([
    'java', '-cp', classpath, 'firrtl.stage.FirrtlMain',
    '-i', str(args.input.resolve()), '-o', target.name, '-X', 'low',
    '--inline', 'CoreSoc', '--target-dir', str(target.parent),
], check=True, cwd=root)
text = target.read_text()
assert len(re.findall(r'^  module ', text, re.M)) == 1
assert not re.search(r'^\s+inst ', text, re.M)
print(f'Flattened low FIRRTL: {target}')
