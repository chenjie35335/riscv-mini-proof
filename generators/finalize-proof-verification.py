#!/usr/bin/env python3
"""Accept completion only from a successful, current 45-assertion snapshot audit."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'formal/flat-low'
parser = argparse.ArgumentParser()
parser.add_argument('snapshot', type=Path)
args = parser.parse_args()
snapshot = args.snapshot.resolve()

def require(condition, message):
    if not condition:
        raise SystemExit('NOT VERIFIED: ' + message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

report = json.loads((snapshot / 'verification.json').read_text())
# Incremental snapshots that import workspace artifacts cannot certify source provenance.
require(report.get('build_provenance') == 'source-only-local-dependency-rebuild',
        'a source-only rebuild of all local dependencies is required')
require(report.get('status') == 'passed' and report.get('exit_code') == 0,
        'snapshot build is not successfully complete')
require(sorted(set(report.get('assertions', []))) == list(range(45)), 'snapshot does not cover all 45 assertions')
audit = report.get('assumptions_audit', {})
require(audit.get('status') == 'passed' and audit.get('exit_code') == 0, 'combined theorem assumptions audit is incomplete')
require(not report.get('changed_workspace_sources'), 'sources changed during verification')
require(report.get('workspace_sources_unchanged') is True and report.get('snapshot_sources_unchanged') is True,
        'verified source inventories were not stable')
require(bool(report.get('tools')), 'missing compiler and checker identities')
for tool in report['tools'].values():
    require(Path(tool['path']).is_file() and sha(Path(tool['path'])) == tool['sha256'],
            'verification tool changed: ' + tool['path'])
kernel = report.get('kernel_audit', {})
require(kernel.get('status') == 'passed' and kernel.get('exit_code') == 0,
        'recursive kernel audit is incomplete')
require(kernel.get('command', [])[-1:] == ['AllOriginalAssertions']
        and not any(flag in kernel.get('command', []) for flag in ['-norec', '-admit']),
        'kernel audit does not recursively check the aggregate')
require(kernel.get('log') in report.get('log_sha256', {})
        and audit.get('log') in report.get('log_sha256', {}),
        'audit logs are not bound to verification')
for field in ['artifact_sha256', 'log_sha256', 'generated_files_sha256']:
    require(bool(report.get(field)), 'missing ' + field)
    for name, digest in report[field].items():
        require((snapshot / name).is_file() and sha(snapshot / name) == digest,
                'verified artifact or log changed: ' + name)
closure = report.get('closure_sources', [])
require(bool(closure), 'missing local dependency closure')
for name in closure:
    require(name in report['source_sha256'], 'dependency source not recorded: ' + name)
    source_text = (snapshot / name).read_text()
    require(not re.search(r'\b(?:native_cast_no_check|vm_cast_no_check)\b', source_text),
            'unchecked cast in dependency: ' + name)
    require(str(Path(name).with_suffix('.vo')) in report['artifact_sha256'],
            'dependency artifact not bound to audit: ' + name)
aggregate = (BASE / 'staged-integration/AllOriginalAssertions.v').read_text()
expected_statement = ('Theorem all_original_assertions memory inputs k states : '
    'generated_observe memory inputs k=Some states ->generated_legal_trace memory inputs k -> '
    + ' /\\ '.join(f'generated_assert_m0_{n}_all states' for n in range(45)) + '.')
actual_statement = aggregate[aggregate.index('Theorem all_original_assertions'):aggregate.index('Proof.')]
require(re.sub(r'\s+', '', actual_statement) == re.sub(r'\s+', '', expected_statement),
        'aggregate does not state exactly all 45 original assertions')

for name, digest in report['source_sha256'].items():
    require((ROOT / name).is_file() and sha(ROOT / name) == digest, 'workspace source changed: ' + name)
    require((snapshot / name).is_file() and sha(snapshot / name) == digest, 'snapshot source changed: ' + name)
require((snapshot / 'formal/flat-low/staged-integration/AllOriginalAssertions.vo').is_file(), 'combined artifact missing')
current = subprocess.run(['make', '-q', '-f', 'Makefile.clean',
                          'formal/flat-low/staged-integration/AllOriginalAssertions.vo'], cwd=snapshot)
require(current.returncode == 0, 'combined theorem dependencies are not current')
log_path = snapshot / audit['log']
log = log_path.read_text()
require('Error:' not in log, 'assumptions audit contains an error')
require(log.count('Axioms:') == 1 or 'Closed under the global context' in log, 'missing or ambiguous assumptions output')
assumptions = re.findall(r'^([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)\s*:',
                        log.rsplit('Axioms:', 1)[-1], re.M) if 'Axioms:' in log else []
allowed = {'HiEnv_with_implicit_widths.ftype_eqn_eq', 'HiEnv_with_implicit_widths.ffield_eqn_eq'}
require(set(assumptions) <= allowed, 'unexpected assumptions: ' + repr(assumptions))
require('Axioms:' not in log or bool(assumptions), 'could not parse declared axioms')
audit_source = snapshot / 'formal/flat-low/staged-integration/AllOriginalAssertionsAudit.v'
require(audit_source.read_text() == 'Require Import AllOriginalAssertions.\nPrint Assumptions all_original_assertions.\n',
        'audit did not inspect the expected combined theorem')
require(sha(audit_source) == audit['source_sha256'], 'audit source changed')
pattern = r'(?:Lemma|Theorem)\s+generated_assert_(\d+)\s*:\s*(.*?)\.\s*(?:Proof\.|Admitted\.)'
original = dict(re.findall(pattern, (BASE / 'CoreSoc.v').read_text(), re.S))
require(set(original) == {str(i) for i in range(45)}, 'original assertion inventory changed')
normalize = lambda text: re.sub(r'\s+', '', text)
entries = []
for number in range(45):
    relative = f'formal/flat-low/staged-integration/GeneratedAssertion{number}.v'
    source = ROOT / relative
    require(relative in report['source_sha256'], 'endpoint absent from snapshot inventory')
    text = source.read_text()
    declarations = dict(re.findall(pattern, text, re.S))
    require(str(number) in declarations and normalize(declarations[str(number)]) == normalize(original[str(number)]),
            f'assertion {number} differs from original')
    require(not re.search(r'\b(?:Admitted|admit|Axiom|Parameter|native_cast_no_check|vm_cast_no_check)\b', text),
            f'unchecked command in endpoint {number}')
    artifact = (snapshot / relative).with_suffix('.vo')
    require(artifact.is_file(), f'compiled endpoint {number} missing')
    entries.append({'assertion': number, 'status': 'compiled_exact_original_statement',
                    'statement_matches_original': True, 'source_sha256': sha(source),
                    'snapshot_artifact_sha256': sha(artifact)})
for baseline in ['CoreSoc.before-proof.sha256', 'legacy-CoreSoc.sha256']:
    result = subprocess.run(['sha256sum', '-c', str(BASE / baseline)], cwd=ROOT, capture_output=True, text=True)
    require(result.returncode == 0, 'model preservation check failed: ' + result.stdout + result.stderr)
model = (BASE / 'CoreSoc.v').read_text()
require((BASE / 'CoreSocModel.v').read_text() == model[:model.index('Lemma generated_assert_0')],
        'proof model is not the exact generated definition prefix')
firrtl = (BASE / 'CoreSoc.lo.fir').read_text()
counts = {name: len(re.findall(pattern, firrtl, re.M)) for name, pattern in {
    'modules': r'^\s*(?:extmodule|module)\s', 'instances': r'^\s*inst\s',
    'asserts': r'^\s*assert\(', 'assumes': r'^\s*assume\('}.items()}
require(counts == {'modules': 1, 'instances': 0, 'asserts': 45, 'assumes': 1}, 'flattened FIRRTL inventory changed')
reproduction = json.loads((BASE / 'flat-low-reproduction.json').read_text())
require(reproduction.get('status') == 'passed' and reproduction.get('matches_checked_models') is True
        and reproduction.get('baselines_unchanged') is True, 'conversion reproduction did not pass')
for name, digest in reproduction['baseline_sha256'].items():
    require(sha(ROOT / name) == digest, 'conversion reproduction baseline changed: ' + name)
result = {'scope': 'All 45 original statements; current source-bound dependency rebuild and combined Coq assumptions audit',
          'original_assertion_count': 45, 'compiled_exact_original_count': 45,
          'reported_assumptions': assumptions, 'snapshot': str(snapshot), 'firrtl_inventory': counts,
          'flat_core_sha256': sha(BASE / 'CoreSoc.v'), 'entries': entries}
(BASE / 'all-original-assertions-assumptions.log').write_text(log)
(BASE / 'final-snapshot-verification.json').write_text(json.dumps(report, indent=2) + '\n')
(BASE / 'original-assertion-proof-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'verified_original_assertions': 45, 'model_unchanged': True, 'assumptions': assumptions}))
