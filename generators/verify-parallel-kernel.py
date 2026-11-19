#!/usr/bin/env python3
"""Plan (default) or run covered, modular coqchk workers without modifying a snapshot.

Local modules are explicit -norec targets. Their dependencies are NOT globally
trusted: every local module must appear in a successful worker's Checking library
trace; every external module is checked by a separate recursive worker. All
interned artifacts must belong to the hash-bound, completely covered inventory.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time

FLAGS = ['-Q', 'firrtl2coq/lib/simplssrlib', 'simplssrlib', '-Q', 'firrtl2coq/lib/nbits', 'nbits',
         '-R', 'firrtl2coq/src', 'firrtl', '-Q', 'formal/flat-low', '',
         '-Q', 'formal/flat-low/staged-integration', '']
BINDINGS = [('formal/flat-low/staged-integration', ''), ('formal/flat-low', ''),
            ('firrtl2coq/lib/simplssrlib', 'simplssrlib'), ('firrtl2coq/lib/nbits', 'nbits'),
            ('firrtl2coq/src', 'firrtl')]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def logical(path, snapshot, coqlib):
    for relative, prefix in BINDINGS:
        base = snapshot / relative
        if path.is_relative_to(base):
            return '.'.join(([prefix] if prefix else []) + list(path.relative_to(base).with_suffix('').parts))
    for directory, prefix in [('theories', 'Coq'), ('user-contrib', '')]:
        base = coqlib / directory
        if path.is_relative_to(base):
            return '.'.join(([prefix] if prefix else []) + list(path.relative_to(base).with_suffix('').parts))
    raise RuntimeError('Unmapped library path: ' + str(path))


def interned(text):
    return {Path(name).resolve() for name in re.findall(r'^\[intern (.*?) \.\.\.$', text, re.M)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('snapshot', type=Path)
    parser.add_argument('--jobs', type=int, default=3)
    parser.add_argument('--bytecode-compiler', choices=['yes', 'no'], default='no')
    parser.add_argument('--intern-log', type=Path, help='Existing full recursive coqchk log; only completed intern phase is read')
    parser.add_argument('--run', action='store_true', help='Explicitly start workers; otherwise only produce a plan')
    args = parser.parse_args()
    if not 1 <= args.jobs <= 8:
        parser.error('--jobs must be between 1 and 8')
    snapshot = args.snapshot.resolve()
    original = json.loads((snapshot / 'verification.json').read_text())
    if original.get('build_provenance') != 'source-only-local-dependency-rebuild':
        raise RuntimeError('Requires a source-only rebuild snapshot')
    if original.get('kernel_audit', {}).get('status') not in {'running', 'passed'}:
        raise RuntimeError('Source build must have completed and reached recursive kernel audit')
    checker = Path(original['tools']['coqchk']['path'])
    if sha(checker) != original['tools']['coqchk']['sha256']:
        raise RuntimeError('Kernel checker binary changed')
    coqlib = checker.parent.parent / 'lib/coq'
    log_path = args.intern_log or snapshot / 'coqchk.log'
    # A complete recursive interning phase finishes before the first check. The
    # serial process can keep appending its check trace; only this stable prefix is bound.
    log = log_path.read_text()
    if 'Checking library:' not in log:
        raise RuntimeError('No completed recursive intern phase available')
    prefix, _ = log.split('Checking library:', 1)
    all_paths = interned(prefix)
    local_paths = {(snapshot / name).with_suffix('.vo').resolve() for name in original['closure_sources']}
    if {path for path in all_paths if path.is_relative_to(snapshot)} != local_paths:
        raise RuntimeError('Recursive intern inventory differs from the entire local dependency closure')
    if snapshot / 'formal/flat-low/staged-integration/AllOriginalAssertions.vo' not in local_paths:
        raise RuntimeError('Combined original assertion module missing')
    for name, expected in original['source_sha256'].items():
        if sha(snapshot / name) != expected:
            raise RuntimeError('Snapshot source changed: ' + name)
    artifacts = {str(path): sha(path) for path in sorted(all_paths)}
    names = {path: logical(path, snapshot, coqlib) for path in all_paths}
    if len(set(names.values())) != len(names):
        raise RuntimeError('Duplicate logical library names')
    external_paths = all_paths - local_paths
    output = Path(tempfile.mkdtemp(prefix='riscv-parallel-kernel-', dir='/tmp'))
    # Size is only a work estimate; no proof dependency or correctness decision
    # relies on it. Large modules are spread first to reduce worker imbalance.
    shards, weights = [[] for _ in range(args.jobs)], [0] * args.jobs
    for path in sorted(local_paths, key=lambda p: p.stat().st_size, reverse=True):
        index = min(range(args.jobs), key=lambda i: weights[i])
        shards[index].append(path)
        weights[index] += path.stat().st_size
    tasks = []
    if external_paths:
        tasks.append({'id': 'external-recursive', 'mode': 'recursive',
                      'targets': sorted(names[path] for path in external_paths)})
    for index, shard in enumerate(shards):
        if shard:
            tasks.append({'id': 'local-%d' % index, 'mode': 'explicit-norec',
                          'targets': sorted(names[path] for path in shard), 'estimated_bytes': weights[index]})
    for task in tasks:
        options = task['targets'] if task['mode'] == 'recursive' else [value for name in task['targets'] for value in ['-norec', name]]
        task['command'] = [str(checker), '-bytecode-compiler', args.bytecode_compiler, *FLAGS, *options]
    report = {'format': 'covered-parallel-kernel-v1', 'snapshot': str(snapshot), 'output': str(output),
              'status': 'planned', 'workers': args.jobs, 'started': time.time(),
              'bytecode_compiler': args.bytecode_compiler,
              'script_sha256': sha(Path(__file__)), 'checker': original['tools']['coqchk'],
              'source_sha256': original['source_sha256'], 'artifact_sha256': artifacts,
              'logical_names': {str(path): name for path, name in names.items()},
              'local_count': len(local_paths), 'external_count': len(external_paths),
              'intern_prefix_sha256': hashlib.sha256(prefix.encode()).hexdigest(),
              'tasks': tasks, 'results': {}}
    (output / 'intern-prefix.log').write_text(prefix)
    report_path = output / 'parallel-kernel.json'
    write(report_path, report)
    print(json.dumps({'report': str(report_path), 'local_count': len(local_paths), 'external_count': len(external_paths),
                      'local_shards': [len(s) for s in shards], 'run': args.run}), flush=True)
    if not args.run:
        return 0

    def worker(task):
        path = output / (task['id'] + '.log')
        started = time.time()
        with path.open('w') as stream:
            result = subprocess.run(task['command'], cwd=snapshot, stdout=stream, stderr=subprocess.STDOUT)
        trace = path.read_text()
        checked = set(re.findall(r'^Checking library:\s*(\S+)\s*$', trace, re.M))
        imported = interned(trace)
        # The checker may load admitted dependencies, but a target skipped by
        # coqchk's option handling MUST NOT be counted as checked.
        missing = set(task['targets']) - checked
        unknown = imported - all_paths
        success_marker = 'Modules were successfully checked' in trace
        passed = result.returncode == 0 and success_marker and not missing and not unknown
        return {'status': 'passed' if passed else 'failed', 'exit_code': result.returncode,
                'success_marker': success_marker, 'checked': sorted(checked), 'interned': sorted(map(str, imported)),
                'missing_explicit_targets': sorted(missing), 'unknown_artifacts': sorted(map(str, unknown)),
                'log': path.name, 'log_sha256': sha(path), 'seconds': time.time() - started}

    report['status'] = 'running'
    write(report_path, report)
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            pending = {pool.submit(worker, task): task for task in tasks}
            for future in as_completed(pending):
                task = pending[future]
                report['results'][task['id']] = future.result()
                write(report_path, report)
        checked = set().union(*(set(result['checked']) for result in report['results'].values()))
        imported = set().union(*(set(result['interned']) for result in report['results'].values()))
        report['uncovered_modules'] = sorted(set(names.values()) - checked)
        report['unseen_artifacts'] = sorted(set(artifacts) - imported)
        report['changed_artifacts'] = [name for name, expected in artifacts.items() if sha(Path(name)) != expected]
        report['changed_sources'] = [name for name, expected in original['source_sha256'].items() if sha(snapshot / name) != expected]
        report['checker_unchanged'] = sha(checker) == report['checker']['sha256']
        report['coverage_complete'] = not report['uncovered_modules'] and not report['unseen_artifacts']
        report['status'] = 'passed' if (all(result['status'] == 'passed' for result in report['results'].values())
            and report['coverage_complete'] and not report['changed_artifacts'] and not report['changed_sources']
            and report['checker_unchanged']) else 'failed'
    except Exception as error:
        report['status'] = 'failed'
        report['error'] = str(error)
    report['finished'] = time.time()
    write(report_path, report)
    print(json.dumps({'report': str(report_path), 'status': report['status']}), flush=True)
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
