#!/usr/bin/env python3
"""Source-only Coq verification. --plan-only prepares/checks dependencies, without compiling."""
import argparse
import hashlib
import json
import re
import shlex
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOOLBIN = Path('/home/stormy/.opam/firrtl2coq/bin')
FLAGS = ['-Q', 'firrtl2coq/lib/simplssrlib', 'simplssrlib', '-Q', 'firrtl2coq/lib/nbits', 'nbits',
         '-R', 'firrtl2coq/src', 'firrtl', '-Q', 'formal/flat-low', '',
         '-Q', 'formal/flat-low/staged-integration', '']
TARGET = 'formal/flat-low/staged-integration/AllOriginalAssertions.vo'
AUDIT = 'formal/flat-low/staged-integration/AllOriginalAssertionsAudit.v'
AUDIT_TEXT = 'Require Import AllOriginalAssertions.\nPrint Assumptions all_original_assertions.\n'
FORMAT = 'clean-coq-verification-v1'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(base, suffix):
    return {str(p.relative_to(base)): digest(p) for directory in ['formal/flat-low', 'firrtl2coq']
            for p in (base / directory).rglob('*' + suffix) if p.is_file()}


def save(path, data):
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--resume', type=Path)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--plan-only', action='store_true')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    snapshot = args.resume.resolve() if args.resume else Path(tempfile.mkdtemp(prefix='riscv-clean-coq-', dir='/tmp'))
    report_path = snapshot / 'verification.json'
    prior = {}
    if args.resume:
        prior = json.loads(report_path.read_text())
        if prior.get('format') != FORMAT or prior.get('status') == 'running':
            raise RuntimeError('Resume requires a terminal snapshot created by this script')
        # Authenticate all cached .vo, including failed runs; never import workspace .vo.
        if inventory(snapshot, '.vo') != prior.get('artifact_sha256', {}):
            raise RuntimeError('Snapshot compiled artifacts changed outside the verifier')
        save(snapshot / ('clean-verification-before-%d.json' % time.time_ns()), prior)
    report = {'format': FORMAT, 'snapshot': str(snapshot), 'status': 'running', 'started': time.time(),
              'script_sha256': digest(Path(__file__)), 'commands': [], 'logs': {},
              'build_provenance': 'source-only-local-dependency-rebuild', 'assertions': list(range(45))}
    save(report_path, report)
    print(json.dumps({'snapshot': str(snapshot), 'report': str(report_path)}), flush=True)

    def run(command, log):
        report['commands'].append(command)
        save(report_path, report)
        with (snapshot / log).open('w') as stream:
            result = subprocess.run(command, cwd=snapshot, stdout=stream, stderr=subprocess.STDOUT)
        report['logs'][log] = digest(snapshot / log)
        report['last_command_exit_code'] = result.returncode
        if result.returncode:
            raise RuntimeError('%s failed (%s); see %s' % (command[0], result.returncode, snapshot / log))
        return (snapshot / log).read_text()

    try:
        # Byte copies deliberately omit metadata and every compiled product.
        sources = inventory(ROOT, '.v')
        sources.pop(AUDIT, None)
        changed = {name for name, value in sources.items() if prior.get('source_sha256', {}).get(name) != value}
        deleted = set(prior.get('source_sha256', {})) - set(sources)
        for name in deleted:
            (snapshot / name).unlink(missing_ok=True)
        for name in sources:
            destination = snapshot / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            if not destination.exists() or digest(destination) != sources[name]:
                destination.write_bytes((ROOT / name).read_bytes())
                changed.add(name)
        report['source_sha256'] = sources
        report['tools'] = {}
        for name in ['coqc', 'coqdep', 'coq_makefile', 'coqchk']:
            binary = TOOLBIN / name
            report['tools'][name] = {'path': str(binary), 'sha256': digest(binary)}
        report['coq_version'] = run([str(TOOLBIN / 'coqc'), '--version'], 'tool-version.log').strip()
        for tool in report['tools'].values():
            tool['coq_suite_version'] = report['coq_version']
        report['coq_configuration'] = run([str(TOOLBIN / 'coqc'), '-config'], 'tool-configuration.log').strip()
        # coqdep resolves every local Require, recursively including the FIRRTL/bitvector libraries.
        project = snapshot / 'clean-all.project'
        project.write_text('\n'.join(shlex.quote(n) for n in sorted(sources)
                                     if n != 'formal/flat-low/CoreSoc.v') + '\n')
        dependencies = run([str(TOOLBIN / 'coqdep'), *FLAGS, '-f', project.name], 'dependencies.log')
        if re.search(r'not found|cannot find|not been found', dependencies, re.I):
            raise RuntimeError('coqdep reported an unresolved dependency')
        graph = {}
        for line in dependencies.replace('\\\n', ' ').splitlines():
            if ':' not in line or line.startswith('Warning:'):
                continue
            lhs, rhs = line.split(':', 1)
            targets = shlex.split(lhs)
            deps = [d for d in shlex.split(rhs) if d.endswith('.vo')]
            for target in targets:
                if target.endswith('.vo'):
                    graph[target] = deps
        closure, todo = set(), [TARGET]
        while todo:
            target = todo.pop()
            if target in closure:
                continue
            if target not in graph or str(Path(target).with_suffix('.v')) not in sources:
                raise RuntimeError('No local source/dependency rule for ' + target)
            if target == 'formal/flat-low/CoreSoc.vo':
                raise RuntimeError('Original admitted CoreSoc must not enter the proof closure')
            closure.add(target)
            todo.extend(graph[target])
        report['dependency_graph'] = {name: graph[name] for name in sorted(closure)}
        report['closure_sources'] = sorted(str(Path(name).with_suffix('.v')) for name in closure)
        # Ban unchecked casts throughout the actual proof closure, not merely endpoints.
        for name in report['closure_sources']:
            text = (snapshot / name).read_text()
            if re.search(r'\b(?:native_cast_no_check|vm_cast_no_check)\b|Unset\s+(?:Guard|Positivity|Universe)\s+Checking', text):
                raise RuntimeError('Unchecked proof command in ' + name)
        # Delete affected cache entries using content changes and both dependency graphs.
        affected = {str(Path(name).with_suffix('.vo')) for name in changed | deleted}
        merged = dict(prior.get('dependency_graph', {}))
        for name, deps in graph.items():
            merged[name] = list(set(merged.get(name, [])) | set(deps))
        while True:
            expanded = affected | {name for name, deps in merged.items() if set(deps) & affected}
            if expanded == affected:
                break
            affected = expanded
        for name in affected:
            (snapshot / name).unlink(missing_ok=True)
        # A different compiler/configuration invalidates every previous compiled object.
        if prior and (prior.get('tools') != report['tools'] or prior.get('coq_configuration') != report['coq_configuration']):
            for name in inventory(snapshot, '.vo'):
                (snapshot / name).unlink()
        report['invalidated_artifacts'] = sorted(affected & closure)
        proof_project = snapshot / 'clean-proof.project'
        # Coq project files do not use POSIX single-quote escaping. Pass empty
        # logical namespaces as real argv elements, never shell-quoted project text.
        proof_project.write_text('\n'.join(report['closure_sources']) + '\n')
        run([str(TOOLBIN / 'coq_makefile'), *FLAGS, '-f', proof_project.name, '-o', 'Makefile.clean'], 'makefile.log')
        # Never retain a dependency file generated under an older load-path configuration.
        (snapshot / '.Makefile.clean.d').unlink(missing_ok=True)
        plan = run(['make', '-n', '-f', 'Makefile.clean', 'COQBIN=' + str(TOOLBIN) + '/', TARGET], 'build-plan.log')
        if re.search(r'not found|cannot find|not been found', plan, re.I):
            raise RuntimeError('Generated make dependency plan contains unresolved imports')
        generated_deps = (snapshot / '.Makefile.clean.d').read_text()
        target_line = next((line for line in generated_deps.splitlines() if line.startswith(TARGET + ' ')), '')
        if not target_line or any(name not in target_line.split(':', 1)[1].split() for name in graph[TARGET]):
            raise RuntimeError('Generated makefile lost aggregate dependencies')
        print(json.dumps({'closure_sources': len(closure), 'library_sources': sum(n.startswith('firrtl2coq/') for n in closure),
                          'plan_only': args.plan_only}), flush=True)
        if args.plan_only:
            report['status'] = 'planned'
        else:
            run(['make', '-j', str(args.jobs), '-f', 'Makefile.clean', 'COQBIN=' + str(TOOLBIN) + '/', TARGET], 'build.log')
            (snapshot / AUDIT).write_text(AUDIT_TEXT)
            report['audit_source_sha256'] = digest(snapshot / AUDIT)
            audit_command = [str(TOOLBIN / 'coqc'), *FLAGS, AUDIT]
            report['assumptions_audit'] = {'status': 'running', 'command': audit_command,
                'source_sha256': report['audit_source_sha256'], 'log': 'assumptions.log'}
            log = run(audit_command, 'assumptions.log')
            report['assumptions_audit'].update(status='passed', exit_code=0)
            allowed = {'HiEnv_with_implicit_widths.ftype_eqn_eq', 'HiEnv_with_implicit_widths.ffield_eqn_eq'}
            if log.count('Axioms:') == 1:
                names = re.findall(r"^([^\s:]+)\s*:", log.split('Axioms:', 1)[1], re.M)
                if not names or not set(names) <= allowed:
                    raise RuntimeError('Unexpected assumptions: ' + repr(names))
            elif 'Axioms:' not in log and 'Closed under the global context' in log:
                names = []
            else:
                raise RuntimeError('Missing or ambiguous assumptions output')
            report['assumptions'] = names
            kernel_command = [str(TOOLBIN / 'coqchk'), *FLAGS, 'AllOriginalAssertions']
            report['kernel_audit'] = {'status': 'running', 'command': kernel_command, 'log': 'coqchk.log'}
            run(kernel_command, 'coqchk.log')
            report['kernel_audit'].update(status='passed', exit_code=0)
            report['status'] = 'passed'
    except Exception as error:
        report['status'] = 'failed'
        report['error'] = str(error)
    finally:
        for field in ['assumptions_audit', 'kernel_audit']:
            if report.get(field, {}).get('status') == 'running':
                report[field].update(status='failed', exit_code=report.get('last_command_exit_code', 1))
        report['artifact_sha256'] = inventory(snapshot, '.vo')
        report['finished'] = time.time()
        current = inventory(ROOT, '.v')
        current.pop(AUDIT, None)
        report['workspace_sources_unchanged'] = current == report.get('source_sha256')
        snapshot_sources = inventory(snapshot, '.v')
        snapshot_sources.pop(AUDIT, None)
        report['snapshot_sources_unchanged'] = snapshot_sources == report.get('source_sha256')
        if report['status'] == 'passed' and not (report['workspace_sources_unchanged'] and report['snapshot_sources_unchanged']):
            report['status'] = 'failed'
            report['error'] = 'Workspace source inventory changed during verification'
        report['exit_code'] = 0 if report['status'] in {'passed', 'planned'} else 1
        report['changed_workspace_sources'] = sorted(name for name in set(current) | set(report.get('source_sha256', {}))
            if current.get(name) != report.get('source_sha256', {}).get(name))
        report['log_sha256'] = report['logs']
        report['generated_files_sha256'] = {name: digest(snapshot / name) for name in
            ['clean-all.project', 'clean-proof.project', 'Makefile.clean', 'Makefile.clean.conf'] if (snapshot / name).exists()}
        save(report_path, report)
        print(json.dumps({name: report[name] for name in ['snapshot', 'status', 'workspace_sources_unchanged']}
                         | {'error': report.get('error')}), flush=True)
    return 0 if report['status'] in {'passed', 'planned'} else 1


if __name__ == '__main__':
    raise SystemExit(main())
