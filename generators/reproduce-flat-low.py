#!/usr/bin/env python3
"""Reproduce flattened FIRRTL and Coq in a new temporary directory; never publish models."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
WORK = Path(tempfile.mkdtemp(prefix='riscv-flat-low-reproduction-'))
TRANSLATOR = ROOT / 'firrtl2coq'
SOURCE = ROOT / 'formal/CoreSoc.hi.fir'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-C', str(TRANSLATOR), *args], text=True).strip()

baseline_paths = [ROOT / 'formal/CoreSoc.v', ROOT / 'formal/flat-low/CoreSoc.v',
                  ROOT / 'formal/flat-low/CoreSoc.lo.fir', ROOT / 'formal/flat-low/CoreSocModel.v']
before = {str(p.relative_to(ROOT)): sha(p) for p in baseline_paths}
metadata = ROOT / 'out/chiselModule/runClasspath/meta.json'
if not metadata.exists():
    raise SystemExit('Missing cached classpath: first run mill chiselModule.runClasspath')
classpath = [item.split(':', 2)[2] for item in json.loads(metadata.read_text())['value']]
report = {'directory': str(WORK), 'input': str(SOURCE.relative_to(ROOT)),
          'input_sha256': sha(SOURCE), 'translator_commit': git('rev-parse', 'HEAD'),
          'translator_dirty_status': git('status', '--short'),
          'translator_diff_sha256': hashlib.sha256(git('diff', 'HEAD').encode()).hexdigest(),
          'firrtl_jars': [p for p in classpath if '/firrtl_' in p], 'baseline_sha256': before}
commands = [
    (ROOT, ['python3', str(ROOT / 'formal/generators/lower-flat-firrtl.py'), str(SOURCE), str(WORK / 'CoreSoc.lo.fir')]),
    (TRANSLATOR / 'src/ocaml', ['dune', 'exec', './bin/main.exe', '--', str(WORK / 'CoreSoc.lo.fir'), str(WORK / 'CoreSoc.v')]),
]
report['commands'] = [{'cwd': str(cwd), 'argv': cmd} for cwd, cmd in commands]
print(str(WORK), flush=True)
try:
    for index, (cwd, cmd) in enumerate(commands):
        with (WORK / f'step-{index}.log').open('w') as log:
            subprocess.run(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT, check=True)
    fir = (WORK / 'CoreSoc.lo.fir').read_text()
    counts = {'modules': len(re.findall(r'^  module ', fir, re.M)),
              'instances': len(re.findall(r'^\s+inst ', fir, re.M)),
              'assertions': len(re.findall(r'^\s+assert\(', fir, re.M)),
              'assumptions': len(re.findall(r'^\s+assume\(', fir, re.M))}
    report['counts'] = counts
    assert counts == {'modules': 1, 'instances': 0, 'assertions': 45, 'assumptions': 1}, counts
    report['outputs_sha256'] = {name: sha(WORK / name) for name in ['CoreSoc.lo.fir', 'CoreSoc.v']}
    report['matches_checked_models'] = all(sha(WORK / name) == sha(ROOT / 'formal/flat-low' / name) for name in ['CoreSoc.lo.fir', 'CoreSoc.v'])
    if not report['matches_checked_models']:
        raise RuntimeError('Reproduction differs; temporary outputs retained, baseline untouched.')
    report['status'] = 'passed'
finally:
    report['baselines_unchanged'] = all(sha(ROOT / name) == digest for name, digest in before.items())
    (WORK / 'reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
