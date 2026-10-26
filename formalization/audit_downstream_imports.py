#!/usr/bin/env python3
"""Audit active downstream imports after a leaf FMSAPaper-only change.

This checks source impact; it does not run downstream proof builds. Run in
an authors' four-project workspace, with --output pointing to the evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tomllib

CORE = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
report = {}
for name in ('Other_Closures', 'SCOZA', 'FMSA_HSGMSA'):
    project = CORE.parent / name
    config = tomllib.loads((project / 'lakefile.toml').read_text())
    libraries = config['lean_lib']
    sources = set()
    for lib in libraries:
        # These projects use Lake's default root/submodule globs. Fail rather
        # than silently auditing an incomplete set if that configuration changes.
        assert 'globs' not in lib and 'srcDir' not in lib and 'srcDir' not in config, name
        for root in lib.get('roots', [lib['name']]):
            stem = project / root.replace('.', '/')
            if stem.with_suffix('.lean').is_file():
                sources.add(stem.with_suffix('.lean'))
            if stem.is_dir():
                sources.update(stem.rglob('*.lean'))
    assert sources, name
    forbidden = {}
    for source in sorted(sources):
        # Conservative source scan: example import lines can only add a false
        # positive. Scan all modules on an import line, not just its first one.
        imports = re.findall(r'^\s*import\s+([^\n]*)', source.read_text(), re.M)
        hits = sorted({token for line in imports for token in line.split('--', 1)[0].split()
                       if token == 'MSA_and_1st_Truncation' or token == 'FMSAPaper'
                       or token.startswith('FMSAPaper.')})
        if hits:
            forbidden[str(source.relative_to(project))] = hits
    report[name] = {
        'status': 'PASS_IMPORT_IMPACT_CHECK' if not forbidden else 'FAIL',
        'scope': 'Only declared active lean_lib sources, excluding archived handoff/results snapshots. '
                 'Independent downstream proof build NOT_RERUN; foundation change is leaf paper '
                 'modules and the aggregate root, with all existing foundation proof sources unchanged.',
        'library_names': [lib['name'] for lib in libraries],
        'active_source_count': len(sources),
        'imports_of_changed_foundation_root_or_paper': forbidden,
        'source_sha256': {str(p.relative_to(project)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(sources)},
    }
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + '\n')
for name, entry in report.items():
    print(f"{name}: {entry['status']} ({entry['active_source_count']} active sources)")
assert all(not entry['imports_of_changed_foundation_root_or_paper'] for entry in report.values())
