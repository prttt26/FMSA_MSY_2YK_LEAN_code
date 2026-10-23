"""Reconstruct actual MSAEXACT.6 division checkpoints; emit kernel-checkable tests.

Loads only the algebraic prefix of the old benchmark script, so its hard-coded
temporary output directory and old proof emission are never executed. RHS
products are deliberately retained: emitting expanded identical sides would
only test reflexivity, not the normalization that needs a certificate.
"""
import ast
import hashlib
import json
from pathlib import Path
import time
import sympy as sp

ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parents[1]/'results/exact_msa_feasibility'
GEN=Path(__file__).resolve().parents[1]/'LeanCode/YukawaOZ/ExactMSASparseCheckpoints.lean'


def balanced(op,args):
    if len(args)==1:return args[0]
    n=len(args)//2
    return f'(.{op} {balanced(op,args[:n])} {balanced(op,args[n:])})'


def encode(e,indices):
    if isinstance(e,sp.Integer):return f'(.const ({e}))'
    if e.is_Symbol:return f'(.var {indices[e]})'
    if e.is_Add:return balanced('add',[encode(a,indices) for a in e.args])
    if e.is_Mul:return balanced('mul',[encode(a,indices) for a in e.args])
    if e.is_Pow and e.exp.is_Integer and e.exp>=0:return f'(.pow {encode(e.base,indices)} {e.exp})'
    raise ValueError(f'Noninteger-polynomial node: {e}')


def emit_reassembly(q1,r0,r1,idx):
    code='''import LeanCode.YukawaOZ.ExactMSASparseDt1
import LeanCode.YukawaOZ.ExactMSASparseDt2
namespace FMSA.ExactMSA.SparseCheckpoints
open FMSA.ExactMSA.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
    for name,value in [('quotientCoefficient',q1),('residualConstant',r0),('residualLinear',r1)]:
        code+=f'def {name} : Expr := {encode(value,idx)}\n'
    code+='''theorem dt1_coefficient (v : Nat → ℝ) :
    eval dt1Left v = eval quotientCoefficient v * eval residualConstant v := by
  have h := dt1_identity v
  change eval dt1Left v = ((0 : Int) : ℝ) * eval residualLinear v +
    eval quotientCoefficient v * eval residualConstant v at h
  simpa only [Int.cast_zero, zero_mul, zero_add] using h

theorem dt2_coefficient (v : Nat → ℝ) :
    eval dt2Left v = eval quotientCoefficient v * eval residualLinear v :=
  dt2_identity v

/-- No large polynomial normalization is needed at reassembly. -/
theorem full_division_reassembled (v : Nat → ℝ) (Dt : ℝ) :
    eval dt1Left v * Dt + eval dt2Left v * Dt ^ 2 =
      Dt * eval quotientCoefficient v *
        (eval residualConstant v + Dt * eval residualLinear v) := by
  rw [dt1_coefficient, dt2_coefficient]
  ring

theorem full_division_zero_of_residual (v : Nat → ℝ) (Dt : ℝ)
    (hroot : eval residualConstant v + Dt * eval residualLinear v = 0) :
    eval dt1Left v * Dt + eval dt2Left v * Dt ^ 2 = 0 := by
  rw [full_division_reassembled, hroot, mul_zero]

#print axioms full_division_reassembled
#print axioms full_division_zero_of_residual
end FMSA.ExactMSA.SparseCheckpoints
'''
    GEN.with_name('ExactMSASparseReassembly.lean').write_text(code)


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    source=ROOT/'msaexact6_scaletest.py'
    tree=ast.parse(source.read_text())
    prefix=[]
    for node in tree.body:
        if isinstance(node,ast.FunctionDef) and node.name=='lean':break
        prefix.append(node)
    env={}
    start=time.monotonic()
    exec(compile(ast.Module(body=prefix,type_ignores=[]),str(source),'exec'),env)
    print('Reconstructed original rational residual and G-division',flush=True)
    xi,z,k,G,C,S,Ez,p=[env[n] for n in ['xi','z','k','G','C','S','Ez','p']]
    variables=[xi,z,k,G,C,S,Ez,p]
    idx={x:i for i,x in enumerate(variables)}
    n1,n2,q0,q1,r0,r1=[env[n] for n in ['n1','n2','q0','q1','r0','r1']]
    assert q0==0 and env['cf'](env['numD'],0)==0
    assert env['numD'].degree()==2 and env['qD'].degree()==1 and env['rD'].degree()==1
    PN=sp.Poly(n2,C,S,Ez)
    best=max(PN.terms(),key=lambda mc:len(sp.Poly(mc[1],xi,z,k,G,p).terms()))
    mono,lhs=best
    # Extract the same coefficient from each factor BEFORE multiplying them.
    rhs=sp.Integer(0)
    Q=sp.Poly(q1,C,S,Ez); R=sp.Poly(r1,C,S,Ez)
    for qm,qc in Q.terms():
        rem=tuple(a-b for a,b in zip(mono,qm))
        if min(rem)>=0:
            rc=R.coeff_monomial(C**rem[0]*S**rem[1]*Ez**rem[2])
            if rc!=0:rhs=sp.Add(rhs,sp.Mul(qc,rc,evaluate=False),evaluate=False)
    cases=[('small323',lhs,rhs),('dt1',n1,sp.Add(sp.Mul(q0,r1,evaluate=False),sp.Mul(q1,r0,evaluate=False),evaluate=False)),
           ('dt2',n2,sp.Mul(q1,r1,evaluate=False))]
    header=['import LeanCode.YukawaOZ.SparsePolynomialCertificate',
           'namespace FMSA.ExactMSA.SparseCheckpoints',
           'open FMSA.ExactMSA.SparseCertificate',
           'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    metadata=[]
    modules=['ExactMSASparseSmall','ExactMSASparseDt1','ExactMSASparseDt2']
    for (name,left,right),module in zip(cases,modules):
        assert sp.expand(left-right)==0
        coefficients=sp.Poly(left,*variables).coeffs()+sp.Poly(sp.expand(right),*variables).coeffs()
        assert all(c.is_Integer for c in coefficients)
        ll=encode(left,idx); rr=encode(right,idx)
        lines=header+[f'def {name}Left : Expr := {ll}',f'def {name}Right : Expr := {rr}',
                      f'def {name}Diff : Expr := .add {name}Left (.neg {name}Right)',
                      f'theorem {name}_checked : compile {name}Diff = [] := by decide +kernel',
                      f'theorem {name}_identity (v : Nat → ℝ) : eval {name}Left v = eval {name}Right v := by',
                      f'  have h := expression_zero {name}Diff {name}_checked v',
                      f'  simpa only [{name}Diff, eval, ← sub_eq_add_neg, sub_eq_zero] using h',
                      f'#print axioms {name}_identity',
                      'end FMSA.ExactMSA.SparseCheckpoints']
        GEN.with_name(module+'.lean').write_text('\n'.join(lines)+'\n')
        metadata.append(dict(name=name,monomials=len(sp.Poly(left,*variables).terms()),
                             total_degree=sp.Poly(left,*variables).total_degree(),
                             lhs_expr_chars=len(ll),rhs_expr_chars=len(rr),
                             old_expanded_sides_identical=sp.sstr(sp.expand(left))==sp.sstr(sp.expand(right))))
        print(name,metadata[-1],flush=True)
    emit_reassembly(q1,r0,r1,idx)
    aggregate=''.join('import LeanCode.YukawaOZ.'+m+'\n'
                      for m in modules+['ExactMSASparseReassembly'])
    aggregate+='\n-- Fail the build if a physical axiom or an admitted proof enters these certificates.\n'
    for theorem in ['small323_identity','dt1_identity','dt2_identity',
                    'full_division_reassembled','full_division_zero_of_residual']:
        fullname='FMSA.ExactMSA.SparseCheckpoints.'+theorem
        aggregate+=(f"/-- info: '{fullname}' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n"
                    '#guard_msgs (whitespace := lax) in\n'
                    f'#print axioms {fullname}\n\n')
    GEN.write_text(aggregate)
    report=dict(generator_seconds=time.monotonic()-start,source=str(source),
                source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                variables=list(map(str,variables)),
                graded_small_coefficient=list(map(int,mono)),cases=metadata,
                scope='Kernel-checkable actual division checkpoints; complete original Fourier/residual bridge pending')
    (OUT/'checkpoint_metadata.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Emitted',GEN,flush=True)


if __name__=='__main__':main()
