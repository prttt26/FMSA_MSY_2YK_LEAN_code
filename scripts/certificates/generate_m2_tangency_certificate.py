#!/usr/bin/env python3
"""Emit ordinary Lean-kernel ten-dimensional Newton certificates.

All rational/analytic bounds and exact expression identities are proved in
Lean. The JSON is only untrusted rational choices, never a truth premise.
"""
from pathlib import Path
from fractions import Fraction as Q
from contextlib import redirect_stdout
import argparse,io,json,importlib.util
import sympy as sp
from m2_tangency_symbolics import symbolic_system
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('interval_generator',Path(__file__).with_name('generate_m2_kernel_certificate.py'))
g=importlib.util.module_from_spec(spec)
with redirect_stdout(io.StringIO()):spec.loader.exec_module(g)
choice=json.loads((ROOT/'results/certificates/codex_m2_tangency_kernel_inputs.json').read_text())
variables,S,J=symbolic_system()
box=[tuple(map(Q,b)) for b in choice['box']]
C=[[Q(c) for c in row] for row in choice['C']]
center=list(map(Q,choice['center']))
g.amp=variables;g.box=box;g.C=C
lit=g.lit
# Keep every interval soundness rule exactly the earlier proved rule. Only
# supply the correct ten-dimensional variable leaf and its exact box premise.
original_emit=g.emit
def emit(e):
    if e in g.cache:return g.cache[e]
    if e in variables:
        i=variables.index(e)
        out=g.declare(f'x {i}',box[i],lambda n:f'by simpa [lower,upper,{n},Matrix.cons_val,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] using hx {i}')
        g.cache[e]=out;return out
    return original_emit(e)
g.emit=emit

def header(namespace,imports):
    print('\n'.join('import MSAConvergence.'+m for m in imports))
    print('''
/-! Ordinary-kernel certificate for the full ten-dimensional M2 contact
system. Every bound and exact identity is a proof obligation, not an external
interval/PASS premise. Scope is local stationary zero-mode contact only. -/
noncomputable section
open Set
open scoped BigOperators
namespace FMSA.Convergence.'''+namespace+'''
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2TangencyData
open FMSA.Convergence.M2TangencyJacobian FMSA.Convergence.RealIntervalCertificates
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
''')
    if namespace in ['M2TangencyDefect','M2TangencyCenter']:
        print("private theorem sum_ten (f : Fin 10 → ℝ) : (∑ i, f i) =\n  f 0+(f 1+(f 2+(f 3+(f 4+(f 5+(f 6+(f 7+(f 8+f 9)))))))) := by\n  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]\n  rfl\n")
def matrix(rows):return '!!['+';\n    '.join(','.join(lit(c) for c in row) for row in rows)+']'

def data():
    print('''import MSAConvergence.M2TangencySystem

/-! Explicit rational choices and exact box geometry. No root or analytic
bound is assumed. First four intervals are the earlier actual regular box. -/
noncomputable section
open Set
namespace FMSA.Convergence.M2TangencyData
open FMSA.Convergence.M2TangencySystem
''')
    print('def lower : Fin 10 → ℝ := !['+','.join(lit(b[0]) for b in box)+']')
    print('def upper : Fin 10 → ℝ := !['+','.join(lit(b[1]) for b in box)+']')
    print('def center : Fin 10 → ℝ := !['+','.join(map(lit,center))+']')
    print('def preconditioner : Matrix (Fin 10) (Fin 10) ℝ :=\n  '+matrix(C)+'\n')
    print('''/-- The new exact box preserves the already proved original regularity domain. -/
theorem amplitude_box (x : Fin 10 → ℝ) (hx : x ∈ Icc lower upper) :
    ∀ i, M2KernelCertificate.lower i ≤ amplitudes x i ∧
      amplitudes x i ≤ M2KernelCertificate.upper i := by
  intro i
  fin_cases i
  · exact ⟨hx.1 0,hx.2 0⟩
  · exact ⟨hx.1 1,hx.2 1⟩
  · exact ⟨hx.1 2,hx.2 2⟩
  · exact ⟨hx.1 3,hx.2 3⟩

/-- Every center-to-face margin is at least 10^-10. -/
theorem center_margin : ∀ i, lower i+(1 : ℝ)/10000000000 ≤ center i ∧
    center i+(1 : ℝ)/10000000000 ≤ upper i := by
  intro i
  fin_cases i <;> norm_num [lower,upper,center,Matrix.cons_val,Matrix.cons_val_succ]

/-- The exact box is contained in the uniform radius-2*10^-9 center ball. -/
theorem center_radius : ∀ i, center i-lower i ≤ (1 : ℝ)/500000000 ∧
    upper i-center i ≤ (1 : ℝ)/500000000 := by
  intro i
  fin_cases i <;> norm_num [lower,upper,center,Matrix.cons_val,Matrix.cons_val_succ]

/-- The coupling is strictly positive and the second tail strength negative. -/
theorem parameter_signs (x : Fin 10 → ℝ) (hx : x ∈ Icc lower upper) : 0 < x 4 ∧ x 5 < 0 := by
  have h4 := hx.1 4
  have h5 := hx.2 5
  simp only [lower,upper,Matrix.cons_val] at h4 h5
  norm_num at h4 h5
  constructor <;> linarith

end FMSA.Convergence.M2TangencyData''')

Jbounds={}
def jproof(i,j):
    g.reset();buf=io.StringIO()
    with redirect_stdout(buf):root=g.emit(J[i,j])
    return buf.getvalue(),root,list(g.defs)
for i in range(10):
 for j in range(10):
    _,(_,_,bounds),_=jproof(i,j);Jbounds[i,j]=bounds

def jacobian_bounds():
    header('M2TangencyJacobianBounds',['M2TangencyJacobian','M2TangencyData','M2PhysicalBounds','RealIntervalCertificates'])
    print('def jacobianLower : Matrix (Fin 10) (Fin 10) ℝ :=\n  '+matrix([[Jbounds[i,j][0] for j in range(10)] for i in range(10)]))
    print('def jacobianUpper : Matrix (Fin 10) (Fin 10) ℝ :=\n  '+matrix([[Jbounds[i,j][1] for j in range(10)] for i in range(10)]))
    for i in range(10):
     for j in range(10):
        proof,(n,h,bounds),defs=jproof(i,j)
        print(f'private theorem j_bound_{i}_{j} (x : Fin 10 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) :')
        print(f'    {lit(bounds[0])} ≤ formula x {i} {j} ∧ formula x {i} {j} ≤ {lit(bounds[1])} := by')
        print(proof,end='')
        print(f'  have he : formula x {i} {j} = {n} := by')
        print('    simp only [formula,Matrix.of_apply,Matrix.cons_val]')
        print('    norm_num [formula,Matrix.of_apply,Matrix.cons_val,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,'+','.join(defs)+'] <;> ring')
        print(f'  rw [he]\n  exact {h}\n')
    print('''/-- ALL full Jacobian entry enclosures, checked with genuine pi/exp bounds. -/
theorem entry_bounds (x : Fin 10 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) (i j : Fin 10) :
    jacobianLower i j ≤ formula x i j ∧ formula x i j ≤ jacobianUpper i j := by
  fin_cases i <;> fin_cases j''')
    for i in range(10):
     for j in range(10):print(f'  · exact j_bound_{i}_{j} x hx')
    print('\nend FMSA.Convergence.M2TangencyJacobianBounds')

radii={}
def eproof(i,j):
    g.reset();buf=io.StringIO()
    with redirect_stdout(buf):
        js=[g.declare(f'formula x {k} {j}',Jbounds[k,j],lambda n,k=k:f'M2TangencyJacobianBounds.entry_bounds x hx {k} {j}') for k in range(10)]
        parts=[g.binary('*',g.emit(sp.Rational(C[i][k].numerator,C[i][k].denominator)),js[k]) for k in range(10)]
        total=parts[0]
        for part in parts[1:]:total=g.binary('+',total,part)
        out=g.binary('+',g.emit(sp.Integer(i==j)),g.negate(total))
    return buf.getvalue(),out,list(g.defs)
for i in range(10):
 for j in range(10):
    _,(_,_,bounds),_=eproof(i,j);radii[i,j]=max(map(abs,bounds))
assert max(sum((radii[i,j] for j in range(10)),Q(0)) for i in range(10))<Q(1,10**6)

def defect():
    header('M2TangencyDefect',['M2TangencyJacobianBounds'])
    print('def radius : Matrix (Fin 10) (Fin 10) ℝ :=\n  '+matrix([[radii[i,j] for j in range(10)] for i in range(10)]))
    for i in range(10):
     for j in range(10):
        proof,(n,h,bounds),defs=eproof(i,j)
        print(f'private theorem e_bound_{i}_{j} (x : Fin 10 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) :')
        print(f'    |(1-preconditioner*formula x) {i} {j}| ≤ {lit(radii[i,j])} := by')
        print(proof,end='')
        print(f'  have he : (1-preconditioner*formula x) {i} {j} = {n} := by')
        print('    simp only [Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,Matrix.vecMul,dotProduct,sum_ten,preconditioner,Matrix.of_apply,Matrix.cons_val]')
        print('    norm_num ['+','.join(defs)+'] <;> simp only [Matrix.vecMul,dotProduct,sum_ten,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff] <;> norm_num <;> ring')
        print(f'  rw [he]\n  exact abs_bound {h} (by norm_num) (by norm_num)\n')
    print('''/-- Every preconditioned defect entry is bounded by proved rational data. -/
theorem entry_defect_bound (x : Fin 10 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) (i j : Fin 10) :
    |(1-preconditioner*formula x) i j| ≤ radius i j := by
  fin_cases i <;> fin_cases j''')
    for i in range(10):
     for j in range(10):print(f'  · exact e_bound_{i}_{j} x hx')
    print('''
/-- The true full Jacobian has a uniform row defect <1e-6 on the ten-dimensional box. -/
theorem row_defect_bound (x : Fin 10 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) :
    ∀ i, ∑ j, |(1-preconditioner*formula x) i j| < (1 : ℝ)/1000000 := by
  intro i
  calc
    _ ≤ ∑ j, radius i j := Finset.sum_le_sum (fun j _ => entry_defect_bound x hx i j)
    _ < _ := by
      fin_cases i <;> simp only [radius,sum_ten,Matrix.of_apply,Matrix.cons_val,Matrix.cons_val_succ',Matrix.cons_val_zero'] <;> norm_num

end FMSA.Convergence.M2TangencyDefect''')

subs={v:sp.Rational(c.numerator,c.denominator) for v,c in zip(variables,center)}
rc=[sp.expand(e.subs(subs)) for e in S]
cr=[sp.expand(sum(sp.Rational(C[i][j].numerator,C[i][j].denominator)*rc[j] for j in range(10))) for i in range(10)]

def center_certificate():
    header('M2TangencyCenter',['M2TangencyJacobianBounds'])
    print('open FMSA.Convergence.NewtonBoxExistence\n')
    for i,e in enumerate(rc):
        assert not e.free_symbols
        g.reset();buf=io.StringIO()
        with redirect_stdout(buf):n,h,bounds=g.emit(e)
        assert max(map(abs,bounds))<Q(1,10**13),(i,bounds)
        print(f'private theorem center_bound_{i} :')
        print(f'    |system center {i}| ≤ (1 : ℝ)/10000000000000 := by')
        print(buf.getvalue(),end='')
        print(f'  have he : system center {i} = {n} := by')
        print('    rw [M2TangencyPolynomials.system_eq_polynomialMap]')
        print(f'    change MvPolynomial.eval M2TangencyData.center M2TangencyPolynomials.equation_{i} = {n}')
        print(f'    simp only [M2TangencyPolynomials.equation_{i},map_add,map_mul,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X,M2TangencyData.center,Matrix.cons_val]')
        print('    norm_num ['+','.join(g.defs)+'] <;> ring')
        print(f'  rw [he]\n  exact abs_bound {h} (by norm_num) (by norm_num)\n')
    print('''private theorem preconditioner_norm_bound : ‖matrixCLM preconditioner‖ ≤ (50 : ℝ) := by
  apply matrixCLM_norm_le _ _ (by norm_num)
  intro i
  fin_cases i <;> simp only [preconditioner,sum_ten,Matrix.of_apply,Matrix.cons_val,
    Matrix.cons_val_succ',Matrix.cons_val_zero'] <;> norm_num

/-- The full center estimate follows from RAW residuals <=1e-13 and a
PROVED exact Pi-space operator norm <=50. No cancellation enclosure is used. -/
theorem center_residual_bound : ‖matrixCLM preconditioner (system center)‖ ≤ (1 : ℝ)/200000000000 := by
  have hr : ‖system center‖ ≤ (1 : ℝ)/10000000000000 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/10000000000000)).mpr
    intro i
    fin_cases i''')
    for i in range(10):print(f'    · exact center_bound_{i}')
    print('''  calc
    _ ≤ ‖matrixCLM preconditioner‖*‖system center‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 50*((1 : ℝ)/10000000000000) := mul_le_mul preconditioner_norm_bound hr
      (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

end FMSA.Convergence.M2TangencyCenter''')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('part',choices=['data','jacobian_bounds','defect','center'])
    part=parser.parse_args().part
    {'data':data,'jacobian_bounds':jacobian_bounds,'defect':defect,'center':center_certificate}[part]()
if __name__=='__main__':main()
