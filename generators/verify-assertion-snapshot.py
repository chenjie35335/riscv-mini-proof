#!/usr/bin/env python3
"""Rebuild assertion dependencies in an isolated, source-hashed snapshot."""
import argparse, hashlib, json, shutil, subprocess, tempfile, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
p = argparse.ArgumentParser()
p.add_argument('--assertions', nargs='+', type=int, required=True)
p.add_argument('--jobs', type=int, default=2)
p.add_argument('--audit-all', action='store_true', help='Build and audit the combined 45-assertion theorem after dependency validation.')
p.add_argument('--resume', type=Path, help='Resume a terminal snapshot; preserve verified compiled dependencies.')
a = p.parse_args()
snapshot = a.resume.resolve() if a.resume else Path(tempfile.mkdtemp(prefix='riscv-coq-proof-check-', dir='/tmp'))
if a.resume:
    prior = json.loads((snapshot / 'verification.json').read_text())
    if prior['status'] == 'running':
        raise SystemExit('Refusing to modify a running snapshot')
    shutil.copy2(snapshot / 'verification.json', snapshot / f'verification-before-{time.time_ns()}.json')
hashes = {}
for directory in ['formal/flat-low', 'firrtl2coq']:
    for source in (ROOT / directory).rglob('*'):
        if not source.is_file() or source.suffix not in {'.v', '.vo'}:
            continue
        relative = source.relative_to(ROOT)
        destination = snapshot / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not a.resume or not destination.exists():
            shutil.copy2(source, destination)
        elif source.suffix == '.v' and source.read_bytes() != destination.read_bytes():
            shutil.copy2(source, destination)
            # A changed source must invalidate prior snapshot compilation.
            destination.touch()
        if source.suffix == '.v':
            hashes[str(relative)] = hashlib.sha256(destination.read_bytes()).hexdigest()
makefile = Path('formal/flat-low/Makefile.proofs')
shutil.copy2(ROOT / makefile, snapshot / makefile)
targets = [f'formal/flat-low/staged-integration/GeneratedAssertion{n}.vo' for n in a.assertions]
if a.audit_all:
    if sorted(set(a.assertions)) != list(range(45)):
        raise SystemExit('--audit-all requires all 45 original assertion numbers')
    targets.append('formal/flat-low/staged-integration/AllOriginalAssertions.vo')
command = ['make', '-j', str(a.jobs), '-f', str(makefile), *targets]
report = {'snapshot': str(snapshot), 'assertions': a.assertions, 'source_sha256': hashes,
          'command': command, 'started': time.time(), 'status': 'running',
          'scope': 'Dependency rebuild only; assumption audit is separate.'}
report_path = snapshot / 'verification.json'
report_path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'snapshot': str(snapshot), 'report': str(report_path), 'source_count': len(hashes)}), flush=True)
with (snapshot / 'build.log').open('w') as log:
    result = subprocess.run(command, cwd=snapshot, stdout=log, stderr=subprocess.STDOUT)
if result.returncode == 0 and a.audit_all:
    audit_source = snapshot / 'formal/flat-low/staged-integration/AllOriginalAssertionsAudit.v'
    audit_source.write_text('Require Import AllOriginalAssertions.\nPrint Assumptions all_original_assertions.\n')
    audit_command = ['/home/stormy/.opam/firrtl2coq/bin/coqc', '-Q', 'firrtl2coq/lib/simplssrlib', 'simplssrlib', '-Q', 'firrtl2coq/lib/nbits', 'nbits', '-R', 'firrtl2coq/src', 'firrtl', '-Q', 'formal/flat-low', '', '-Q', 'formal/flat-low/staged-integration', '', str(audit_source.relative_to(snapshot))]
    report['assumptions_audit'] = {'command': audit_command, 'source_sha256': hashlib.sha256(audit_source.read_bytes()).hexdigest(), 'log': 'all-assertions-assumptions.log', 'status': 'running'}
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    with (snapshot / 'all-assertions-assumptions.log').open('w') as log:
        result = subprocess.run(audit_command, cwd=snapshot, stdout=log, stderr=subprocess.STDOUT)
    report['assumptions_audit'].update(status='passed' if result.returncode == 0 else 'failed', exit_code=result.returncode)
report.update(status='passed' if result.returncode == 0 else 'failed',
              exit_code=result.returncode, finished=time.time())
report['changed_workspace_sources'] = [name for name, digest in hashes.items()
    if not (ROOT / name).exists() or hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest]
report_path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ['snapshot', 'status', 'exit_code', 'changed_workspace_sources']}), flush=True)
raise SystemExit(result.returncode)
