#!/usr/bin/env python3
"""Replay expression generators and bind every source/input by SHA256.

This is a provenance check only. The generated expressions and all analytic
bounds must independently pass the ordinary Lean kernel in check_project.py.
"""
from datetime import datetime,timezone
from hashlib import sha256
import json,os,subprocess,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/certificates/codex_m2_tangency_generation.json'
TARGETS=[
 ('M2ZeroMode','generate_m2_zero_mode.py',[]),
 ('M2TangencyPolynomials','generate_m2_tangency_polynomials.py',[]),
 ('M2TangencyJacobian','generate_m2_tangency_jacobian.py',[]),
 ('M2TangencyData','generate_m2_tangency_certificate.py',['data']),
 ('M2TangencyJacobianBounds','generate_m2_tangency_certificate.py',['jacobian_bounds']),
 ('M2TangencyDefect','generate_m2_tangency_certificate.py',['defect']),
 ('M2TangencyCenter','generate_m2_tangency_certificate.py',['center']),
 ('M2CurvatureCertificate','generate_m2_curvature_certificate.py',[]),
 ('M2WeightCertificate','generate_m2_weight_certificate.py',[]),
]
MODULES=['M2ZeroMode','M2TangencySystem','PolynomialNewtonMap','M2TangencyPolynomials',
 'M2TangencyJacobian','M2TangencyData','M2TangencyJacobianBounds','M2TangencyDefect',
 'M2TangencyCenter','M2TangencyExistence','PreconditionedLinearError',
 'M2BranchSecondDerivative','M2CurvatureCertificate','M2Curvature',
 'M2WeightBranch','M2WeightCertificate','M2WeightTransversality',
 'M2JointBranch','ImplicitZeroContour','M2JointZeroContour',
 'ImplicitContourCurvature','M2ContourCurvature','LocalMinimumLevels','M2LocalBifurcation']
INPUTS=[*('MSAConvergence/'+m+'.lean' for m in MODULES),
 *('scripts/certificates/'+n for n in ['check_m2_tangency_generation.py',
 'generate_m2_zero_mode.py','m2_tangency_symbolics.py','generate_m2_tangency_polynomials.py',
 'generate_m2_tangency_jacobian.py','generate_m2_tangency_certificate.py',
 'generate_m2_kernel_certificate.py','codex_m2_jacobian_arb.py',
 'generate_m2_curvature_certificate.py','generate_m2_weight_certificate.py']),
 'results/certificates/codex_m2_tangency_kernel_inputs.json',
 'results/certificates/codex_m2_jacobian_arb.json',
 '../MSA_and_1st_Truncation/results/coupling_singularities/codex_m2_zero_mode_firstness.json']

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def main():
 if not __debug__:raise RuntimeError('Assertions must remain enabled.')
 before={p:digest(ROOT/p) for p in INPUTS}
 choices=json.loads((ROOT/'results/certificates/codex_m2_tangency_kernel_inputs.json').read_text())
 assert all(digest(ROOT/p)==h for p,h in choices['source_sha256'].items())
 versions=json.loads(subprocess.check_output([sys.executable,'-c',
  "import json,sympy;from importlib.metadata import version;print(json.dumps({'sympy':sympy.__version__,'python_flint':version('python-flint')}))"],text=True))
 records=[]
 for module,script,args in TARGETS:
  command=[sys.executable,'scripts/certificates/'+script,*args]
  generated=subprocess.check_output(command,cwd=ROOT)
  source=ROOT/'MSAConvergence'/(module+'.lean')
  prefix=source.read_bytes().split(b'/-- info:')[0]
  assert b'#guard_msgs' in source.read_bytes(),module
  assert generated.rstrip(b'\n')==prefix.rstrip(b'\n'),module
  records.append(dict(module='MSAConvergence.'+module,source=str(source.relative_to(ROOT)),
   command=command,source_sha256=digest(source),stdout_sha256=sha256(generated).hexdigest(),
   source_prefix_sha256=sha256(prefix.rstrip(b'\n')+b'\n').hexdigest(),
   canonical_generated_sha256=sha256(generated.rstrip(b'\n')+b'\n').hexdigest()))
 assert before=={p:digest(ROOT/p) for p in INPUTS},'Input changed during generator replay'
 receipt=dict(status='PASS_BODY_REPLAY',label='EXPRESSION PROVENANCE ONLY; NO MATHEMATICAL PREMISE',
  created_at_utc=datetime.now(timezone.utc).isoformat(),python=sys.version,dependencies=versions,
  inputs_sha256=before,generated=records,generated_count=len(records),
  analytic_enclosure_assumed=False,numerical_root_assumed=False,
  scope='Nine byte-identical generated source prefixes; all37 source/input fingerprints. Ordinary Lean proofs and guarded full validation remain separate.')
 OUT.write_text(json.dumps(receipt,indent=2)+'\n')
 print(f'PASS: {len(records)} exact generated prefixes; {len(before)} source/input pins; mathematical verification remains the Lean kernel.')
if __name__=='__main__':main()
