#!/usr/bin/env python3
"""Replay the rational certificate checks of the convergence library from a temporary tree.

The scripts in scripts/certificates and the receipts in results/two_tail were written in the research
package MSA_Convergence. They name inputs as `MSA_Convergence/...` and, in some receipts, by the absolute
paths of both packages at the time. Those strings are pinned by hashes, so all these files stay
byte-identical. This tool copies them into `<tmp>/MSA_Convergence`, links `<tmp>/MSA_and_1st_Truncation` to
this package, and maps the old absolute prefixes to the tree when a script resolves a recorded path.
Nothing else changes. It writes nothing inside this package.

Usage: replay_convergence_certificates.py [log-file]. check_py_seeded_chain_rational needs python-flint
on PYTHONPATH. The analytic enclosures remain EXTERNAL; these checks are not Lean proofs.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

CORE = Path(__file__).resolve().parents[1]
OLD_WORKSPACE = '/home/rpan/YK_tail_FMSA/Lean_code'
CHECKS = ('check_endpoint_witness_rational', 'check_m1_fold_witness_rational',
          'check_m1_parameter_monotonicity_rational', 'check_m2_jacobian_rational',
          'check_m2_second_root_witness_rational', 'check_m3_arb_witness_rational',
          'check_py_seeded_chain_rational')
DRIVER = '''
import pathlib, runpy, sys
old, new, script = sys.argv[1:4]
original = pathlib.Path.resolve
def resolve(self, strict=False):
    text = str(self)
    for name in ('MSA_Convergence', 'MSA_and_1st_Truncation'):
        if text.startswith(old + '/' + name + '/'):
            return pathlib.Path(new + text[len(old):])
    return original(self, strict)
pathlib.Path.resolve = resolve
sys.argv = [script]
sys.path.insert(0, str(pathlib.Path(script).parent))
runpy.run_path(script, run_name='__main__')
'''


def main():
    log = open(sys.argv[1], 'w') if len(sys.argv) > 1 else sys.stdout
    failed = []
    with tempfile.TemporaryDirectory(prefix='convergence_replay_') as tmp:
        research = Path(tmp).resolve() / 'MSA_Convergence'
        research.mkdir()
        for name in ('MSAConvergence', 'scripts/certificates', 'scripts/two_tail', 'scripts/m3_kernel',
                     'results/certificates', 'results/two_tail'):
            shutil.copytree(CORE / name, research / name, ignore=shutil.ignore_patterns('__pycache__'))
        (Path(tmp).resolve() / 'MSA_and_1st_Truncation').symlink_to(CORE)
        for check in CHECKS:
            script = str(research / 'scripts/certificates' / (check + '.py'))
            run = subprocess.run([sys.executable, '-c', DRIVER, OLD_WORKSPACE, str(research.parent), script],
                                 cwd=research, text=True, capture_output=True)
            print(f'{check}: exit {run.returncode}', file=log)
            print(run.stdout + run.stderr, file=log, flush=True)
            if run.returncode:
                failed.append(check)
    print(f'{len(CHECKS) - len(failed)} of {len(CHECKS)} replays passed; failed: {failed}')
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
