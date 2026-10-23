"""Verify the frozen foundation from inside the package (standalone clone)."""
from pathlib import Path
import hashlib
import json
import tomllib

CORE = Path(__file__).resolve().parents[1]
release = json.loads((CORE / 'release-manifest.json').read_text())
config = tomllib.loads((CORE / 'lakefile.toml').read_text())
assert config['name'] == release['project'] == 'MSA_and_1st_Truncation'
assert config['version'] == release['version']
assert (CORE / 'lean-toolchain').read_text().strip() == release['toolchain']
manifest = json.loads((CORE / 'lake-manifest.json').read_text())
assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == release['mathlib_revision']
paths = [p for p in CORE.rglob('*.lean') if '.lake' not in p.parts]
paths += [CORE / name for name in ('lakefile.toml','lake-manifest.json','lean-toolchain')]
actual = {str(p.relative_to(CORE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
assert actual == release['source_and_config_sha256'], 'Frozen foundation changed.'
print(f"PASS: foundation {release['version']}, {len(actual)} source/config hashes.")
