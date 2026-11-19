#!/usr/bin/env python3
"""Freeze completed serial module evidence; plan/run only the unchecked mini-proof remainder.
A serial module is reusable only once the next Checking library line has appeared.
The final announced module is never credited, even if the serial run later finishes.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
MINI = ROOT / 'mini-proof'
spec = importlib.util.spec_from_file_location('kernel_definitions', ROOT / 'formal/generators/verify-parallel-kernel.py')
kernel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernel)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources(base):
    return {str(p.relative_to(base)): sha(p) for directory in ['formal/flat-low', 'firrtl2coq']
            for p in (base / directory).rglob('*.v') if p.name != 'AllOriginalAssertionsAudit.v'}


def checked(text):
    return re.findall(r'^Checking library:\s*(\S+)[ \t]*$', text, re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', type=Path, default=Path('/tmp/riscv-mini-proof-check-zn1djw_z'))
    parser.add_argument('--parallel-report', type=Path, default=Path('/tmp/riscv-parallel-kernel-hz666o4h/parallel-kernel.json'))
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    require(1 <= args.jobs <= 16, 'jobs must be between 1 and 16')
    snapshot = args.snapshot.resolve()
    parallel_path = args.parallel_report.resolve()
    clean_bytes = (snapshot / 'verification.json').read_bytes()
    clean = json.loads(clean_bytes)
    parallel_bytes = parallel_path.read_bytes()
    parallel = json.loads(parallel_bytes)
    require(Path(parallel['snapshot']).resolve() == snapshot, 'different snapshots')
    require(clean['build_provenance'] == 'source-only-local-dependency-rebuild', 'not a clean source build')
    require(clean['assumptions_audit']['status'] == 'passed', 'assumptions audit incomplete')
    require(clean['source_sha256'] == parallel['source_sha256'] == sources(snapshot) == sources(MINI),
            'mini-proof, snapshot, or verifier sources differ')
    for tool in clean['tools'].values():
        require(sha(Path(tool['path'])) == tool['sha256'], 'tool binary changed')
    require(parallel['checker'] == clean['tools']['coqchk'], 'different checkers')
    checker = Path(parallel['checker']['path'])
    serial_command = [str(checker), '-bytecode-compiler', 'yes', *kernel.FLAGS, 'AllOriginalAssertions']
    require(clean['kernel_audit']['command'] == serial_command, 'unexpected serial checking command')
    serial_bytes = (snapshot / 'coqchk.log').read_bytes()
    serial = serial_bytes.decode()
    require('Checking library:' in serial, 'serial intern phase has not finished')
    require('Error:' not in serial and 'Anomaly:' not in serial, 'serial trace contains a checking error')
    prefix = serial.split('Checking library:', 1)[0]
    paths = kernel.interned(prefix)
    require(paths == {Path(name) for name in parallel['artifact_sha256']}, 'artifact inventories differ')
    artifact_hashes = {str(path): sha(path) for path in sorted(paths)}
    require(artifact_hashes == parallel['artifact_sha256'], 'artifacts changed since prior parallel launch')
    coqlib = checker.parent.parent / 'lib/coq'
    names = {path: kernel.logical(path, snapshot, coqlib) for path in paths}
    require(parallel['logical_names'] == {str(path): name for path, name in names.items()}, 'library mapping differs')
    local_paths = {(snapshot / name).with_suffix('.vo') for name in clean['closure_sources']}
    require(local_paths == {path for path in paths if path.is_relative_to(snapshot)}, 'local closure incomplete')
    local_names = {names[path] for path in local_paths}
    external_names = set(names.values()) - local_names
    announcements = checked(serial)
    require(announcements and set(announcements) <= set(names.values()), 'unknown serial module')
    # Conservative exclusion of the last announcement even if it appeared earlier.
    serial_completed = set(announcements[:-1]) - {announcements[-1]}
    external_task = [task for task in parallel['tasks'] if task['mode'] == 'recursive']
    require(len(external_task) == 1, 'expected one external recursive worker')
    external_task = external_task[0]
    external_result = parallel['results'].get(external_task['id'], {})
    require(external_result.get('status') == 'passed' and external_result.get('exit_code') == 0,
            'external recursive worker has not passed')
    require(set(external_task['targets']) == external_names, 'external targets incomplete')
    require(external_task['command'] == [str(checker), '-bytecode-compiler', parallel['bytecode_compiler'],
            *kernel.FLAGS, *external_task['targets']], 'external worker has nonrecursive/unknown options')
    external_path = parallel_path.parent / external_result['log']
    external_bytes = external_path.read_bytes()
    require(hashlib.sha256(external_bytes).hexdigest() == external_result['log_sha256'], 'external log changed')
    external_trace = external_bytes.decode()
    require('Modules were successfully checked' in external_trace and 'Error:' not in external_trace,
            'external worker lacks terminal success')
    external_checked = set(checked(external_trace))
    require(external_names <= external_checked <= set(names.values()), 'external checked coverage mismatch')
    require(external_checked == set(external_result['checked']) and kernel.interned(external_trace) <= paths,
            'external evidence mismatch')
    reused = serial_completed | external_checked
    remaining = local_names - reused
    reverse_names = {name: path for path, name in names.items()}
    shards, weights = [[] for _ in range(args.jobs)], [0] * args.jobs
    for name in sorted(remaining, key=lambda n: reverse_names[n].stat().st_size, reverse=True):
        index = min(range(args.jobs), key=lambda i: weights[i])
        shards[index].append(name)
        weights[index] += reverse_names[name].stat().st_size
    output = Path(tempfile.mkdtemp(prefix='riscv-mini-remainder-', dir='/tmp'))
    evidence = {'serial-frozen.log': serial_bytes, 'external-frozen.log': external_bytes,
                'clean-source-report.json': clean_bytes, 'parallel-source-report.json': parallel_bytes}
    for filename, data in evidence.items():
        (output / filename).write_bytes(data)
    tasks = [{'id': 'remainder-%d' % index, 'targets': sorted(shard),
              'command': [str(checker), '-bytecode-compiler', 'yes', *kernel.FLAGS,
                          *[value for name in sorted(shard) for value in ['-norec', name]]]}
             for index, shard in enumerate(shards) if shard]
    report = {'format': 'mini-proof-serial-remainder-v1', 'status': 'planned', 'snapshot': str(snapshot),
              'output': str(output), 'started': time.time(), 'script_sha256': sha(Path(__file__)),
              'evidence_sha256': {name: sha(output / name) for name in evidence},
              'source_sha256': clean['source_sha256'], 'artifact_sha256': artifact_hashes, 'tools': clean['tools'],
              'logical_names': {str(path): name for path, name in names.items()},
              'serial_evidence_kind': 'nonterminal per-module completion inferred from next-library announcement; not a terminal pass',
              'serial_completed': sorted(serial_completed), 'serial_last_excluded': announcements[-1],
              'external_checked': sorted(external_checked), 'reused_coverage': sorted(reused),
              'remaining_targets': sorted(remaining), 'tasks': tasks, 'results': {},
              'local_count': len(local_names), 'external_count': len(external_names), 'jobs': args.jobs}
    report_path = output / 'remainder-verification.json'
    kernel.write(report_path, report)
    print(json.dumps({'report': str(report_path), 'serial_completed': len(serial_completed),
                      'serial_last_excluded': announcements[-1], 'external_checked': len(external_checked),
                      'remaining_local': len(remaining), 'shards': [len(shard) for shard in shards], 'run': args.run}), flush=True)
    if not args.run:
        return 0

    def worker(task):
        log_path = output / (task['id'] + '.log')
        with log_path.open('w') as stream:
            result = subprocess.run(task['command'], cwd=snapshot, stdout=stream, stderr=subprocess.STDOUT)
        text = log_path.read_text()
        done, imported = set(checked(text)), kernel.interned(text)
        good = result.returncode == 0 and 'Modules were successfully checked' in text and set(task['targets']) <= done <= set(names.values()) and imported <= paths
        return {'status': 'passed' if good else 'failed', 'exit_code': result.returncode,
                'checked': sorted(done), 'interned': sorted(map(str, imported)), 'log': log_path.name,
                'log_sha256': sha(log_path), 'success_marker': 'Modules were successfully checked' in text}

    report['status'] = 'running'
    kernel.write(report_path, report)
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            pending = {pool.submit(worker, task): task for task in tasks}
            for future in as_completed(pending):
                report['results'][pending[future]['id']] = future.result()
                kernel.write(report_path, report)
        union = reused | set().union(*(set(result['checked']) for result in report['results'].values()))
        report['coverage_complete'] = union == set(names.values())
        report['checked_union'] = sorted(union)
        report['uncovered'] = sorted(set(names.values()) - union)
        report['unchanged_artifacts'] = all(sha(Path(name)) == value for name, value in artifact_hashes.items())
        report['unchanged_sources'] = sources(MINI) == sources(snapshot) == clean['source_sha256']
        report['unchanged_tools'] = all(sha(Path(tool['path'])) == tool['sha256'] for tool in clean['tools'].values())
        report['unchanged_evidence'] = all(sha(output / name) == value for name, value in report['evidence_sha256'].items())
        report['status'] = 'passed' if (all(result['status'] == 'passed' for result in report['results'].values())
            and all(report[key] for key in ['coverage_complete', 'unchanged_artifacts', 'unchanged_sources', 'unchanged_tools', 'unchanged_evidence'])) else 'failed'
    except Exception as error:
        report['status'], report['error'] = 'failed', str(error)
    report['finished'] = time.time()
    kernel.write(report_path, report)
    print(json.dumps({'report': str(report_path), 'status': report['status']}), flush=True)
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
