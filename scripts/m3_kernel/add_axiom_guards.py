"""Append exact `#guard_msgs` axiom-footprint guards to a research module, as check_project.py requires.

The module is compiled once with `#print axioms` for every public `theorem`. The actual compiler
messages are then written back verbatim as guards. No message is invented: a theorem whose
message is missing makes the script fail.

Usage: python3 scripts/m3_kernel/add_axiom_guards.py MSAConvergence/Foo.lean [more.lean ...]
"""
import os, re, subprocess, sys, tempfile, tomllib
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT

config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
def flatten(d, p=''):
    for k, v in d.items():
        n = p + '.' + k if p else k
        if isinstance(v, dict): yield from flatten(v, n)
        else: yield n, v
FLAGS = ['-D' + k + '=' + (str(v).lower() if isinstance(v, bool) else str(v)) for k, v in flatten(config.get('leanOptions', {}))]
shared = (ROOT / config['packagesDir']).resolve()
LIBS = [ROOT / '.lake/build/lib/lean', CORE / '.lake/build/lib/lean', *sorted(shared.glob('*/.lake/build/lib/lean'))]
LEAN = Path.home() / '.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean'


def guard(path):
    text = path.read_text()
    # refresh: drop existing guard blocks, they are regenerated from the compiler below
    text = re.sub(r"/-- info: '[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms) -/\n#guard_msgs in\n#print axioms \S+\n",
                  '', text)
    assert '#guard_msgs' not in text, ('unrecognised guard left', path)
    ns = re.search(r'^namespace (\S+)', text, re.M).group(1)
    names = [ns + '.' + n for n in re.findall(r'^theorem ([^\s(:]+)', text, re.M)]
    assert names, path
    end = f'end {ns}'
    assert text.rstrip().endswith(end), (path, 'must end with', end)
    body = text.rstrip()[:-len(end)]
    probe = body + ''.join(f'#print axioms {n}\n' for n in names) + end + '\n'
    env = os.environ.copy(); env['LEAN_PATH'] = ':'.join(str(p.resolve()) for p in LIBS)
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / path.name
        f.write_text(probe)
        out = subprocess.run([str(LEAN), *FLAGS, str(f)], cwd=ROOT, env=env, capture_output=True, text=True)
    assert out.returncode == 0, out.stdout[-3000:]
    # `#print axioms` output is printed bare: a line starting with the quoted name, possibly
    # continued on lines that start with a space.
    info, cur = {}, None
    for line in out.stdout.splitlines():
        if line.startswith("'") and ("depends on axioms" in line or "does not depend on any axioms" in line):
            cur = re.match(r"'([^']+)'", line).group(1)
            info[cur] = line
        elif cur is not None and line.startswith(' '):
            info[cur] += '\n' + line
        else:
            cur = None
    blocks = []
    for n in names:
        assert n in info, ('no axiom message for', n)
        blocks.append(f'/-- info: {info[n]} -/\n#guard_msgs in\n#print axioms {n}\n')
    path.write_text(body + ''.join(blocks) + end + '\n')
    print(path, len(names), 'guards')


if __name__ == '__main__':
    for p in sys.argv[1:]:
        guard(ROOT / p)
