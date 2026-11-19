#!/usr/bin/env python3
"""Certify all original assertions using a completed, fully covered modular kernel audit.
Does not alter the clean snapshot or either verifier's report. Output is a new sidecar.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'formal/flat-low'


def require(condition, message):
    if not condition:
        raise SystemExit('NOT VERIFIED: ' + message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_inventory(base):
    return {str(p.relative_to(base)): sha(p) for directory in ['formal/flat-low', 'firrtl2coq']
            for p in (base / directory).rglob('*.v') if p.is_file()
            and p.name != 'AllOriginalAssertionsAudit.v'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parallel_report', type=Path)
    parser.add_argument('--output', type=Path, help='New sidecar JSON (must not already exist)')
    args = parser.parse_args()
    parallel_path = args.parallel_report.resolve()
    parallel_digest = sha(parallel_path)
    parallel = json.loads(parallel_path.read_text())
    require(parallel.get('format') == 'covered-parallel-kernel-v1' and parallel.get('status') == 'passed',
            'parallel kernel audit is not fully passed')
    snapshot = Path(parallel['snapshot']).resolve()
    clean_path = snapshot / 'verification.json'
    clean_digest = sha(clean_path)
    report = json.loads(clean_path.read_text())
    output = args.output.resolve() if args.output else parallel_path.parent / 'final-parallel-verification.json'
    require(not output.is_relative_to(snapshot), 'output must be outside the immutable snapshot')
    require(not output.exists(), 'refusing to replace an existing certification')
    require(report.get('build_provenance') == 'source-only-local-dependency-rebuild'
            and report.get('status') in {'running', 'passed'}, 'clean source rebuild provenance is absent')
    require(report.get('kernel_audit', {}).get('status') in {'running', 'passed'},
            'clean build did not successfully reach kernel checking')
    require(sorted(set(report.get('assertions', []))) == list(range(45)), 'original assertion inventory is incomplete')
    require(sha(ROOT / 'formal/generators/verify-clean-assertions.py') == report['script_sha256'],
            'clean verifier implementation differs from the recorded build')
    parallel_script = ROOT / 'formal/generators/verify-parallel-kernel.py'
    require(sha(parallel_script) == parallel['script_sha256'], 'parallel verifier implementation changed')
    spec = importlib.util.spec_from_file_location('parallel_checker_definitions', parallel_script)
    definitions = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(definitions)
    require(parallel['source_sha256'] == report['source_sha256'], 'verifiers used different source inventories')
    require(source_inventory(ROOT) == report['source_sha256'], 'current workspace source inventory differs')
    require(source_inventory(snapshot) == report['source_sha256'], 'snapshot source inventory differs')
    for tool in report['tools'].values():
        require(sha(Path(tool['path'])) == tool['sha256'], 'tool binary changed: ' + tool['path'])
    require(parallel['checker'] == report['tools']['coqchk'], 'different kernel checker identity')
    checker = Path(parallel['checker']['path'])
    coqlib = checker.parent.parent / 'lib/coq'
    closure = set(report['closure_sources'])
    graph = report['dependency_graph']
    target = 'formal/flat-low/staged-integration/AllOriginalAssertions.vo'
    reachable, todo = set(), [target]
    while todo:
        item = todo.pop()
        if item in reachable:
            continue
        require(item in graph, 'incomplete local dependency graph: ' + item)
        reachable.add(item)
        todo.extend(graph[item])
    require(reachable == {str(Path(name).with_suffix('.vo')) for name in closure}, 'closure is not the full aggregate graph')
    require('formal/flat-low/CoreSoc.v' not in closure, 'original admitted CoreSoc entered proof dependencies')
    for name in closure:
        require(name in report['source_sha256'], 'unrecorded proof dependency: ' + name)
        require(not re.search(r'\b(?:native_cast_no_check|vm_cast_no_check)\b|Unset\s+(?:Guard|Positivity|Universe)\s+Checking',
                              (snapshot / name).read_text()), 'unchecked dependency: ' + name)
    # Running clean reports have not executed their final artifact-hash step.
    # Require evidence of an actual full source compilation, not a copied-cache
    # incremental build, and disclose this distinction in the certification.
    logs = report.get('log_sha256', report.get('logs', {}))
    for name in ['build.log', 'dependencies.log', 'build-plan.log', 'assumptions.log']:
        require(name in logs and sha(snapshot / name) == logs[name], 'unbound/changed clean log: ' + name)
    build_text = (snapshot / 'build.log').read_text()
    compiled_sources = set(re.findall(r'^COQC (\S+\.v)\s*$', build_text, re.M))
    clean_artifacts = report.get('artifact_sha256', {})
    if not clean_artifacts:
        require(closure <= compiled_sources, 'running clean report lacks full-source compilation evidence')
    expected_make = ['make', '-j']
    build_commands = [command for command in report['commands'] if command[:2] == expected_make and command[-1:] == [target]]
    require(len(build_commands) == 1 and build_commands[0][3:] ==
            ['-f', 'Makefile.clean', 'COQBIN=' + str(checker.parent) + '/', target], 'unexpected source build invocation')
    require((snapshot / 'clean-proof.project').read_text().splitlines() == sorted(closure), 'build project changed')
    # Independently reconstruct dependencies from the coqdep log bound by the builder.
    dependency_lines = (snapshot / 'dependencies.log').read_text().replace('\\\n', ' ').splitlines()
    import shlex
    recorded_graph = {}
    for line in dependency_lines:
        if ':' not in line or line.startswith('Warning:'):
            continue
        left, right = line.split(':', 1)
        for name in shlex.split(left):
            if name.endswith('.vo'):
                recorded_graph[name] = [dep for dep in shlex.split(right) if dep.endswith('.vo')]
    require(all(recorded_graph.get(name) == graph[name] for name in reachable), 'dependency graph differs from coqdep evidence')
    prefix_path = parallel_path.parent / 'intern-prefix.log'
    require(sha(prefix_path) == parallel['intern_prefix_sha256'], 'recursive dependency discovery prefix changed')
    prefix = prefix_path.read_text()
    serial_prefix = (snapshot / 'coqchk.log').read_text().split('Checking library:', 1)[0]
    require(prefix == serial_prefix, 'dependency inventory is not the original completed recursive intern phase')
    all_paths = definitions.interned(prefix)
    local_paths = {(snapshot / name).resolve() for name in reachable}
    require({path for path in all_paths if path.is_relative_to(snapshot)} == local_paths, 'recursive local closure mismatch')
    require(set(parallel['artifact_sha256']) == {str(path) for path in all_paths}, 'artifact hash inventory mismatch')
    names = {path: definitions.logical(path, snapshot, coqlib) for path in all_paths}
    require(len(set(names.values())) == len(names), 'logical module collision')
    require(parallel['logical_names'] == {str(path): name for path, name in names.items()}, 'logical-name mapping differs')
    for path in all_paths:
        require(sha(path) == parallel['artifact_sha256'][str(path)], 'checked artifact changed: ' + str(path))
        if path in local_paths and clean_artifacts:
            require(clean_artifacts.get(str(path.relative_to(snapshot))) == parallel['artifact_sha256'][str(path)],
                    'kernel artifact differs from clean-build artifact: ' + str(path))
    local_names = {names[path] for path in local_paths}
    external_names = set(names.values()) - local_names
    require(parallel['local_count'] == len(local_names) and parallel['external_count'] == len(external_names), 'module counts differ')
    local_targets, external_targets, checked_union, intern_union = [], [], set(), set()
    tasks = parallel['tasks']
    require(len({task['id'] for task in tasks}) == len(tasks), 'duplicate task identifier')
    require(set(parallel['results']) == {task['id'] for task in tasks}, 'missing or extra worker results')
    worker_logs = {}
    for task in tasks:
        result = parallel['results'][task['id']]
        require(result.get('status') == 'passed' and result.get('exit_code') == 0, 'worker not successful: ' + task['id'])
        targets = task['targets']
        require(targets and len(set(targets)) == len(targets), 'empty/duplicate worker targets')
        if task['mode'] == 'explicit-norec':
            require(set(targets) <= local_names, 'nonlocal -norec target')
            local_targets.extend(targets)
            options = [value for name in targets for value in ['-norec', name]]
        else:
            require(task['mode'] == 'recursive' and set(targets) <= external_names, 'invalid recursive task')
            external_targets.extend(targets)
            options = targets
        vm = parallel.get('bytecode_compiler')
        require(vm in {'yes', 'no'}, 'unspecified VM conversion mode')
        expected_command = [str(checker), '-bytecode-compiler', vm, *definitions.FLAGS, *options]
        require(task['command'] == expected_command, 'worker flags differ from complete-check policy')
        logfile = (parallel_path.parent / result['log']).resolve()
        require(logfile.parent == parallel_path.parent, 'worker log outside report directory')
        require(sha(logfile) == result['log_sha256'], 'worker log hash differs')
        trace = logfile.read_text()
        require('Modules were successfully checked' in trace and 'Error:' not in trace, 'missing full worker success trace')
        checked = set(re.findall(r'^Checking library:\s*(\S+)\s*$', trace, re.M))
        imported = definitions.interned(trace)
        require(set(targets) <= checked <= set(names.values()), 'worker skipped target or checked unbound module')
        require(imported <= all_paths, 'worker imported an unbound artifact')
        require(checked == set(result['checked']) and {str(path) for path in imported} == set(result['interned']),
                'worker summary disagrees with raw trace')
        checked_union |= checked
        intern_union |= imported
        worker_logs[str(logfile)] = sha(logfile)
    require(len(local_targets) == len(local_names) and set(local_targets) == local_names, 'local explicit targets are not a partition')
    require(len(external_targets) == len(external_names) and set(external_targets) == external_names, 'external recursive targets do not cover dependencies')
    require(checked_union == set(names.values()) and intern_union == all_paths, 'global checked/interned coverage is incomplete')
    audit = report['assumptions_audit']
    require(audit.get('command') == [report['tools']['coqc']['path'], *definitions.FLAGS,
            'formal/flat-low/staged-integration/AllOriginalAssertionsAudit.v'], 'unexpected assumptions audit invocation')
    require(report['kernel_audit'].get('command') == [str(checker), *definitions.FLAGS, 'AllOriginalAssertions'],
            'recursive discovery did not target the complete aggregate')
    require(audit.get('status') == 'passed' and audit.get('exit_code') == 0, 'combined assumptions audit is incomplete')
    audit_source = snapshot / 'formal/flat-low/staged-integration/AllOriginalAssertionsAudit.v'
    require(audit_source.read_text() == 'Require Import AllOriginalAssertions.\nPrint Assumptions all_original_assertions.\n'
            and sha(audit_source) == audit['source_sha256'], 'assumptions audit source differs')
    log = (snapshot / audit['log']).read_text()
    require(audit['log'] in logs and sha(snapshot / audit['log']) == logs[audit['log']], 'unbound assumption log')
    if log.count('Axioms:') == 1:
        assumptions = re.findall(r'^([^\s:]+)\s*:', log.split('Axioms:', 1)[1], re.M)
        require(bool(assumptions), 'unparsed assumptions')
    else:
        require('Axioms:' not in log and 'Closed under the global context' in log, 'ambiguous assumptions output')
        assumptions = []
    require(set(assumptions) <= {'HiEnv_with_implicit_widths.ftype_eqn_eq', 'HiEnv_with_implicit_widths.ffield_eqn_eq'},
            'unexpected assumptions: ' + repr(assumptions))
    aggregate = (BASE / 'staged-integration/AllOriginalAssertions.v').read_text()
    expected = ('Theorem all_original_assertions memory inputs k states : '
        'generated_observe memory inputs k=Some states ->generated_legal_trace memory inputs k -> '
        + ' /\\ '.join(f'generated_assert_m0_{n}_all states' for n in range(45)) + '.')
    normalize = lambda text: re.sub(r'\s+', '', text)
    require(normalize(aggregate[aggregate.index('Theorem all_original_assertions'):aggregate.index('Proof.')]) == normalize(expected),
            'aggregate does not state exactly all original assertions')
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
    # The serial checker may finish while this independent audit runs. Preserve
    # its latest report verbatim; never rewrite a running report into a success.
    latest_clean = json.loads(clean_path.read_text())
    for field in ['build_provenance', 'source_sha256', 'tools', 'closure_sources', 'dependency_graph', 'assumptions_audit']:
        require(latest_clean.get(field) == report.get(field), 'clean immutable evidence changed: ' + field)
    require(sha(parallel_path) == parallel_digest, 'parallel report changed during finalization')
    require(all(sha(Path(name)) == value for name, value in parallel['artifact_sha256'].items()),
            'artifact changed during finalization')
    require(source_inventory(ROOT) == report['source_sha256'] and source_inventory(snapshot) == report['source_sha256'],
            'source changed during finalization')
    result = {
        'format': 'original-assertions-modular-kernel-certification-v1', 'status': 'passed', 'finished': time.time(),
        'scope': 'All 45 exact original assertions: source-only local rebuild, combined assumptions audit, '
                 'and exhaustive modular kernel checking with separately recursively checked external dependencies',
        'kernel_method': 'explicit-norec local partition plus recursive external coverage; not a single recursive checker run',
        'original_assertion_count': 45, 'compiled_exact_original_count': 45,
        'reported_assumptions': assumptions, 'snapshot': str(snapshot), 'firrtl_inventory': counts,
        'flat_core_sha256': sha(BASE / 'CoreSoc.v'), 'entries': entries,
        'local_checked_count': len(local_names), 'external_checked_count': len(external_names),
        'checked_modules': sorted(checked_union), 'artifact_sha256': parallel['artifact_sha256'],
        'source_sha256': report['source_sha256'], 'worker_log_sha256': worker_logs,
        'bytecode_compiler': parallel['bytecode_compiler'], 'tools': report['tools'],
        'clean_build_artifact_evidence': 'recorded clean terminal artifact hashes cross-matched' if clean_artifacts else
            'full source-only COQC build log bound by clean report, identical sources, and parallel start/end artifact hashes; '
            'no historical build-completion artifact hash was recorded while serial verification remained running',
        'build_log_sha256': logs['build.log'], 'assumptions_log_sha256': logs[audit['log']],
        'parallel_report': str(parallel_path), 'parallel_report_sha256': parallel_digest,
        'clean_report_initial_sha256': clean_digest, 'clean_report_copy': latest_clean,
        'finalizer_sha256': sha(Path(__file__)),
    }
    with output.open('x') as stream:
        stream.write(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'certification': str(output), 'verified_original_assertions': 45,
                      'local_checked': len(local_names), 'external_checked': len(external_names),
                      'assumptions': assumptions}))


if __name__ == '__main__':
    main()
