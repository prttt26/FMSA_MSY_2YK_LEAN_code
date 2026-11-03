#!/usr/bin/env python3
"""Compile and audit the MSAConvergence library of this package.

No Lake command is invoked: Lake would start parallel compilers, and Lean here runs one process at a
time under the monitored 30 GiB cap of scripts/lean_memory_limited.py. The other libraries are read
only. Outputs are MSAConvergence artifacts in .lake/build and results/convergence_lean. Package
source/config hashes are audited against release-manifest.json before and after.

A module is recompiled unless the last PASS record shows the same source hash, the same exact
compiler command and the same artifact hash on disk, with every local dependency itself reused,
under an unchanged compiler, foundation manifest and import pins. Pass --fresh to rebuild all.
Pass -j N to compile up to N independent modules at once.
"""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait

import hashlib
from certificates.check_m2_tangency_generation import TARGETS as REPLAY_TARGETS, INPUTS as REPLAY_INPUTS, OUT as REPLAY_OUTPUT

ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT
RESULTS = ROOT / 'results/convergence_lean'
DIRECT_IMPORTS = ROOT / 'scripts/convergence_direct_imports.json'
BUILD = ROOT / '.lake/build/lib/lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
JOBS = int(sys.argv[sys.argv.index('-j') + 1]) if '-j' in sys.argv else 1
SCOPE = ('Compilation, exact per-theorem axiom-footprint guards and input pins only. The '
         'statement-level scope of each module is in README.md and proof_notes/.')

if not __debug__:
    raise RuntimeError('Assertions must remain enabled; do not use python -O.')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify():
    """Audit the package source/config hashes against its own release manifest; never builds."""
    release_path = CORE / 'release-manifest.json'
    release = json.loads(release_path.read_text())
    config = tomllib.loads((CORE / 'lakefile.toml').read_text())
    assert config['name'] == release['project'] and config['version'] == release['version']
    assert (CORE / 'lean-toolchain').read_text().strip() == release['toolchain']
    manifest = json.loads((CORE / 'lake-manifest.json').read_text())
    assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == release['mathlib_revision']
    paths = [p for p in CORE.rglob('*.lean') if '.lake' not in p.parts]
    paths += [CORE / n for n in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]
    actual = {str(p.relative_to(CORE)): digest(p) for p in sorted(paths)}
    assert actual == release['source_and_config_sha256'], 'Package source/config differ from the release manifest.'
    return {'status': 'PASS', 'version': release['version'], 'manifest_sha256': digest(release_path),
            'source_config_hash_count': len(actual), 'source_and_config_sha256': actual}


def inspect(path):
    text = path.read_text()
    namespace = re.search(r'^namespace (\S+)', text, re.M).group(1)
    names = [namespace + '.' + n for n in re.findall(r'^theorem ([^\s(:]+)', text, re.M)]
    assert names, ('No guarded theorem module', path)
    assert re.findall(r'^#print axioms (\S+)', text, re.M) == names, ('Footprint order/coverage', path)
    assert text.count('#guard_msgs') == len(names), ('Missing exact compiler guards', path)
    messages = list(re.finditer(
        r"/-- info: '([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms) -/", text))
    reports = [(m.group(1), m.group(2) or '') for m in messages]
    assert [n for n, _ in reports] == names, ('Footprint message coverage', path)
    assert all(set(a.strip() for a in axioms.split(',') if a.strip()) <= STANDARD for _, axioms in reports)
    assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|unsafe|admit)\b', text, re.M), path
    return {'source': str(path.relative_to(ROOT)), 'source_sha256': digest(path),
            'theorems': names, 'guard_count': len(names),
            'axiom_footprints': {n: [a.strip() for a in fp.split(',') if a.strip()] for n, fp in reports}}


def imports(path):
    return [word for line in re.findall(r'^\s*import\s+([^\n]*)', path.read_text(), re.M)
            for word in line.split('--', 1)[0].split()]


def compiler():
    pin = (ROOT / 'lean-toolchain').read_text().strip()
    installed = Path.home() / '.elan/toolchains' / pin.replace('/', '--').replace(':', '---') / 'bin/lean'
    assert installed.is_file(), 'The pinned compiler is not installed.'
    binary = Path(os.environ.get('LEAN_BIN', str(ROOT / 'scripts/lean_memory_limited.py'))).resolve()
    assert binary.is_file(), 'LEAN_BIN does not exist.'
    version = subprocess.check_output([str(binary), '--version'], cwd=ROOT, text=True).strip()
    assert re.search(r'\bversion ' + re.escape(pin.split(':v')[1]) + r'\b', version), version
    return binary, version



def audited_lean_code_imports(sources, foundation):
    """Verify separately locked direct LeanCode sources and existing artifacts."""
    lock = json.loads(DIRECT_IMPORTS.read_text())
    assert lock['toolchain'] == (ROOT / 'lean-toolchain').read_text().strip()
    direct = {m for p in sources for m in imports(p) if m.startswith('LeanCode.')}
    assert direct == set(lock['imports']), ('Additional direct foundation import coverage', direct)
    for name, pin in lock['imports'].items():
        source = name.replace('.', '/') + '.lean'
        artifact = CORE / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
        assert foundation['source_and_config_sha256'][source] == pin['source_sha256']
        assert digest(CORE / source) == pin['source_sha256'], ('Locked foundation source changed', name)
        assert digest(artifact) == pin['artifact_sha256'], ('Locked foundation artifact changed', name)
    return lock['imports']


def audited_expression_replay():
    """Bind optional expression generation to already checked source bytes.

    The receipt is a provenance record, not an analytic/root premise. This
    checker needs only the standard library; SymPy/Flint are used separately
    by the explicit replay command before this full Lean validation.
    """
    evidence = json.loads(REPLAY_OUTPUT.read_text())
    assert evidence['status'] == 'PASS_BODY_REPLAY'
    assert evidence['generated_count'] == len(REPLAY_TARGETS) == 9
    assert len(REPLAY_INPUTS) == 37
    assert not evidence['analytic_enclosure_assumed'] and not evidence['numerical_root_assumed']
    assert set(evidence['inputs_sha256']) == set(REPLAY_INPUTS)
    for relative, expected in evidence['inputs_sha256'].items():
        assert digest(ROOT / relative) == expected, ('Expression input changed', relative)
    rows = evidence['generated']
    assert [r['module'] for r in rows] == ['MSAConvergence.' + name for name, _, _ in REPLAY_TARGETS]
    for row, (name, generator, args) in zip(rows, REPLAY_TARGETS):
        source = ROOT / 'MSAConvergence' / (name + '.lean')
        assert row['source'] == str(source.relative_to(ROOT))
        assert row['command'][1:] == ['scripts/certificates/' + generator, *args]
        assert row['source_sha256'] == digest(source)
        prefix = source.read_bytes().split(b'/-- info:')[0].rstrip(b'\n') + b'\n'
        import hashlib
        actual = hashlib.sha256(prefix).hexdigest()
        assert actual == row['source_prefix_sha256'] == row['canonical_generated_sha256'], name
    return {'receipt': str(REPLAY_OUTPUT.relative_to(ROOT)),
            'receipt_sha256': digest(REPLAY_OUTPUT), 'evidence': evidence}


def slim(rec):
    """The part of a PASS record that artifact reuse depends on."""
    if 'pins' in rec:
        return rec
    return {'status': rec['status'], 'validated_at_utc': rec['validated_at_utc'], 'compiler': rec['compiler'],
            'foundation_manifest_sha256': rec['foundation_before']['manifest_sha256'],
            'pins': [rec['validated_import_artifact_sha256'], rec['direct_lean_code_import_pins'],
                     rec['direct_mathlib_import_artifact_sha256']],
            'commands': rec['commands'],
            'modules': [{k: m[k] for k in ('source', 'source_sha256', 'artifact_sha256', 'status')}
                        for m in rec['modules']]}


def reuse_base(argv):
    """The last PASS record (slimmed), or None. A FAIL/RUNNING record keeps the one it started from."""
    if '--fresh' in argv:
        return None
    try:
        last = json.loads((RESULTS / 'validation.json').read_text())
    except (OSError, ValueError):
        return None
    if last.get('status') != 'PASS':
        last = last.get('reuse_base')
    return slim(last) if last and last.get('status') == 'PASS' else None


def reusable_artifacts(base, version, foundation, *pins):
    """Prior module rows by source path, or {} if the compiler, foundation or a shared import pin changed."""
    if not base or base['compiler'] != version or base['foundation_manifest_sha256'] != foundation['manifest_sha256']:
        return {}
    if any(old[k] != new[k] for old, new in zip(base['pins'], pins) for k in old.keys() & new.keys()):
        return {}
    commands = {c[-1]: c for c in base['commands']}
    return {m['source']: dict(m, command=commands.get(m['source'])) for m in base['modules'] if m['status'] == 'PASS'}


def main():
    RESULTS.mkdir(parents=True, exist_ok=True)
    base = reuse_base(sys.argv[1:])
    record = {'status': 'RUNNING', 'started_at_utc': datetime.now(timezone.utc).isoformat(),
              'integration_status': 'FOUNDATION_LIBRARY',
              'policy': 'Library of this package, outside the default Lake target; built only by this checker.',
              'reuse_base': base}
    output = RESULTS / 'validation.json'
    output.write_text(json.dumps(record, indent=2) + '\n')
    try:
        before = verify()
        record.update(foundation_before=before, shared_dependency_builds_invoked=False)
        config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
        assert 'MSAConvergence' in {lib['name'] for lib in config['lean_lib']}
        assert 'MSAConvergence' not in config['defaultTargets'], 'Lake would compile this library in parallel.'
        sources = sorted((ROOT / 'MSAConvergence').rglob('*.lean'))
        assert sources
        modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in sources}
        root = ROOT / 'MSAConvergence.lean'
        assert set(imports(root)) == set(modules), 'The root must import all and only research modules.'
        records = {name: inspect(path) for name, path in modules.items()}
        graph = {name: [m for m in imports(path) if m.startswith('MSAConvergence.')] for name, path in modules.items()}
        assert all(m in modules for edges in graph.values() for m in edges), 'Missing local import.'
        order, visiting, visited = [], set(), set()

        def visit(name):
            assert name not in visiting, ('Local import cycle', name)
            if name in visited:
                return
            visiting.add(name)
            for dependency in graph[name]:
                visit(dependency)
            visiting.remove(name)
            visited.add(name)
            order.append(name)

        for name in sorted(modules):
            visit(name)
        expression_replay = audited_expression_replay()
        record['expression_generation_replay'] = expression_replay
        cached = json.loads((CORE / 'formalization/results/validation.json').read_text())
        assert cached['status'] == 'PASS' and cached['foundation_manifest_sha256'] == before['manifest_sha256']
        by_source = {m['source']: m for m in cached['modules']}
        direct = sorted({m for p in sources for m in imports(p) if m.startswith('FMSAPaper.')})
        artifact_pins = {}
        for name in direct:
            module = by_source[name.replace('.', '/') + '.lean']
            artifact = CORE / module['artifact']
            assert digest(artifact) == module['artifact_sha256'], ('Validated import artifact changed', name)
            artifact_pins[name] = module['artifact_sha256']
        lean_code_pins = audited_lean_code_imports(sources, before)
        binary, version = compiler()
        shared = (ROOT / config['packagesDir']).resolve()
        direct_mathlib = sorted({m for p in sources for m in imports(p) if m.startswith('Mathlib.')})
        mathlib_artifact_pins = {
            name: digest(shared / 'mathlib/.lake/build/lib/lean' / (name.replace('.', '/') + '.olean'))
            for name in direct_mathlib}
        libraries = [BUILD, *sorted(shared.glob('*/.lake/build/lib/lean'))]
        env = os.environ.copy()
        env['LEAN_PATH'] = ':'.join(str(p.resolve()) for p in libraries)
        def flatten_options(data, prefix=''):
            for key, value in data.items():
                name = prefix + '.' + key if prefix else key
                if isinstance(value, dict):
                    yield from flatten_options(value, name)
                else:
                    yield name, value

        flags = []
        for key, value in flatten_options(config.get('leanOptions', {})):
            flags.append('-D' + key + '=' + (str(value).lower() if isinstance(value, bool) else str(value)))
        reusable = reusable_artifacts(base, version, before, artifact_pins, lean_code_pins, mathlib_artifact_pins)
        names = [*order, 'MSAConvergence']
        deps = {name: graph[name] if name in graph else list(order) for name in names}
        commands, reused, outputs, done = {}, set(), {}, set()

        def build(name):
            source = modules.get(name, root)
            artifact = BUILD / (name.replace('.', '/') + '.olean')
            artifact.parent.mkdir(parents=True, exist_ok=True)
            command = [str(binary), *flags, '-o', str(artifact), str(source.relative_to(ROOT))]
            commands[name] = command
            prior = reusable.get(command[-1])
            if (name in records and prior and prior['source_sha256'] == records[name]['source_sha256']
                    and prior['command'] == command and artifact.is_file()
                    and digest(artifact) == prior['artifact_sha256'] and all(d in reused for d in deps[name])):
                reused.add(name)
                return f'REUSED {name} {prior["artifact_sha256"]}\n'.encode()
            process = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            outputs[name] = process.stdout
            assert process.returncode == 0, ('Lean failed', name, 'results/lean/build.log')
            return process.stdout

        # Independent modules compile concurrently (-j N); a module starts once all its local
        # dependencies are finished, so the reuse rule sees their final status.
        try:
            with ThreadPoolExecutor(max_workers=JOBS) as pool:
                pending, running = list(names), {}
                while pending or running:
                    for name in [n for n in pending if all(d in done for d in deps[n])]:
                        pending.remove(name)
                        running[pool.submit(build, name)] = name
                    finished, _ = wait(running, return_when=FIRST_COMPLETED)
                    for future in finished:
                        name = running.pop(future)
                        outputs[name] = future.result()
                        done.add(name)
        finally:
            with (RESULTS / 'build.log').open('wb') as log:
                for name in names:
                    log.write(outputs.get(name, b''))
        commands = [commands[name] for name in names]
        for name in order:
            artifact = BUILD / (name.replace('.', '/') + '.olean')
            records[name].update(status='PASS', artifact=str(artifact.relative_to(ROOT)),
                                 artifact_sha256=digest(artifact), reused=name in reused)
        after = verify()
        assert expression_replay == audited_expression_replay(), 'Expression replay inputs changed during validation.'
        assert before == after, 'Package sources changed during the build.'
        assert lean_code_pins == audited_lean_code_imports(sources, after), 'Additional frozen imports changed.'
        for name, expected in artifact_pins.items():
            assert digest(CORE / by_source[name.replace('.', '/') + '.lean']['artifact']) == expected
        for name, expected in mathlib_artifact_pins.items():
            assert digest(shared / 'mathlib/.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')) == expected, (
                'Direct mathlib import artifact changed', name)
        inputs = [*sources, root, *(ROOT / n for n in
                  ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'scripts/check_convergence.py',
                   'scripts/lean_memory_limited.py', 'scripts/convergence_direct_imports.json')),
                  REPLAY_OUTPUT, *(ROOT / relative for relative in REPLAY_INPUTS)]
        record.update(status='PASS', validated_at_utc=datetime.now(timezone.utc).isoformat(),
                      compiler=version, toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                      package_version=config['version'], foundation_before=before, foundation_after=after,
                      validated_import_artifact_sha256=artifact_pins, foundation_unchanged=True,
                      direct_mathlib_import_artifact_sha256=mathlib_artifact_pins,
                      direct_lean_code_import_pins=lean_code_pins,
                      shared_dependency_builds_invoked=False, modules=list(records.values()),
                      theorem_count=sum(m['guard_count'] for m in records.values()), standard_axioms_only=True,
                      root_artifact_sha256=digest(BUILD / 'MSAConvergence.olean'),
                      inputs_sha256={str(p.relative_to(ROOT)): digest(p) for p in inputs},
                      commands=commands, build_log_sha256=digest(RESULTS / 'build.log'),
                      reused_modules=sorted(reused),
                      reuse_base_validated_at_utc=base['validated_at_utc'] if base else None,
                      scope=SCOPE)
        record.pop('reuse_base')
    except Exception as error:
        record.update(status='FAIL', error=str(error))
        if 'before' in locals():
            try:
                record['foundation_after'] = verify()
                record['foundation_unchanged'] = before == record['foundation_after']
            except Exception as post_error:
                record['foundation_post_audit_error'] = str(post_error)
        output.write_text(json.dumps(record, indent=2) + '\n')
        raise
    output.write_text(json.dumps(record, indent=2) + '\n')
    print(f"PASS: {record['theorem_count']} exact theorem guards, {len(records)} MSAConvergence modules; package {after['version']} sources unchanged during the build.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
