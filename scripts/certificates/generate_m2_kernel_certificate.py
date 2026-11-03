#!/usr/bin/env python3
"""Emit an ordinary Lean-kernel interval certificate for the actual M2 box.

Python/SymPy choose expressions and outward-rounded rational endpoints only.
Every operation has a soundness lemma and eight proved corner inequalities;
Lean also checks each expression against the proved literal Jacobian formula.
No Arb value, native_decide or external PASS flag is used as a proof premise.
Output is an unguarded body on stdout; guards require actual compiler queries.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import sympy as sp
from codex_m2_jacobian_arb import symbolic_residual

ROOT=Path(__file__).resolve().parents[2]
r=json.loads((ROOT/'results/certificates/codex_m2_jacobian_arb.json').read_text())
amp,_,_,J=symbolic_residual()
box=[tuple(map(Q,b)) for b in r['exact_widened_box_rational'][:4]]
C=[[Q(v) for v in row] for row in r['C_rational']]
seed=Q(548811636094026432628,10**21),Q(548811636094026432629,10**21)
pi=Q(314159265358979323846,10**20),Q(314159265358979323847,10**20)
SCALE=10**24

def lit(x):
    x=Q(x);return f'(({x.numerator} : ℝ) / {x.denominator})'
def roundout(lo,hi):return Q((lo*SCALE).__floor__(),SCALE),Q((hi*SCALE).__ceil__(),SCALE)
def vmatrix(rows):return '!!['+';\n    '.join(', '.join(lit(x) for x in row) for row in rows)+']'

print('''import MSAConvergence.M2JacobianFormula
import MSAConvergence.M2PhysicalBounds
import MSAConvergence.RealIntervalCertificates

/-! Ordinary-kernel M2 interval certificate. Every generated arithmetic step
and every rectangle-corner inequality is proved. External output is not a
premise. This proves actual-partial regularity on a NONEMPTY positive-density
amplitude box, not root existence, canonicity, first loss or a Taylor radius. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2KernelCertificate
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.Convergence.RegularEndpointContinuation
open FMSA.Convergence.RealIntervalCertificates
open FMSA.Convergence.M2JacobianFormula
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
''')
print('def lower : Fin 4 → ℝ := !['+', '.join(lit(b[0]) for b in box)+']')
print('def upper : Fin 4 → ℝ := !['+', '.join(lit(b[1]) for b in box)+']')
print('def preconditioner : Matrix (Fin 4) (Fin 4) ℝ :=\n  '+vmatrix(C)+'\n')
print('''/-- The certified physical amplitude box is nonempty, verified by exact arithmetic. -/
theorem box_nonempty : ∃ x : Fin 4 → ℝ, ∀ i, lower i ≤ x i ∧ x i ≤ upper i := by
  refine ⟨fun i => (lower i+upper i)/2,?_⟩
  intro i
  fin_cases i <;> norm_num [lower,upper]

''')

cache={};defs=[];counter=0

def declare(expr,bounds,proof):
    global counter
    name=f'v{counter}';h=f'h{counter}';counter+=1
    print(f'  let {name} : ℝ := {expr}')
    print(f'  have {h} : {lit(bounds[0])} ≤ {name} ∧ {name} ≤ {lit(bounds[1])} := {proof(name)}')
    defs.append(name)
    return name,h,bounds

def leaf(expr,bounds,rule):
    return declare(expr,bounds,lambda n:f'by\n    dsimp only [{n}]\n    constructor <;> linarith [{rule}.1,{rule}.2]')
def binary(op,a,b):
    na,ha,(la,ua)=a;nb,hb,(lb,ub)=b
    key=op,na,nb
    if key in cache:return cache[key]
    if op=='+':
        bounds=roundout(la+lb,ua+ub)
        proof=lambda n:f'add_interval {ha} {hb} (by norm_num) (by norm_num)'
    else:
        corners=[la*lb,la*ub,ua*lb,ua*ub];bounds=roundout(min(corners),max(corners))
        proof=lambda n:f'mul_interval {ha} {hb} (by norm_num) (by norm_num)'
    out=declare(f'{na}{op}{nb}',bounds,proof);cache[key]=out;return out

def negate(a):
    n,h,(lo,hi)=a;key='neg',n
    if key not in cache:cache[key]=declare('-'+n,(-hi,-lo),lambda v:f'neg_interval {h} (by norm_num) (by norm_num)')
    return cache[key]

def emit(e):
    if e in cache:return cache[e]
    if e in amp:
        i=amp.index(e)
        out=declare(f'x {i}',box[i],lambda n:f'by simpa [lower,upper,{n},Matrix.cons_val_two,Matrix.cons_val_three] using hx {i}')
    elif e==sp.pi:
        out=leaf('Real.pi',pi,'M2PhysicalBounds.pi_interval')
    elif e==sp.pi**-1:
        out=leaf('Real.pi⁻¹',(1/pi[1],1/pi[0]),'M2PhysicalBounds.inverse_pi_interval')
    elif e.func==sp.exp:
        n=e.args[0]/(-sp.Rational(3,5));assert n.is_Integer and int(n) in [3,6,20,23,40];n=int(n)
        bounds=Q((seed[0]**n*10**21).__floor__(),10**21),Q((seed[1]**n*10**21).__ceil__(),10**21)
        out=leaf('Real.exp '+lit(-Q(3*n,5)),bounds,f'M2PhysicalBounds.exp_multiple_{n}')
    elif e.is_Rational:
        q=Q(int(e.p),int(e.q));out=declare(lit(q),(q,q),lambda n:f'by constructor <;> norm_num [{n}]')
    elif e.func in (sp.Add,sp.Mul):
        op='+' if e.func==sp.Add else '*';out=emit(e.args[0])
        for a in e.args[1:]:out=binary(op,out,emit(a))
    elif e.func==sp.Pow and e.exp.is_Integer and e.exp>=0:
        out=emit(sp.Integer(1))
        for _ in range(int(e.exp)):out=binary('*',out,emit(e.base))
    else:raise ValueError(e)
    cache[e]=out;return out


import io
from contextlib import redirect_stdout

def reset():
    global cache,defs,counter
    cache={};defs=[];counter=0

Jbounds={}
for i in range(4):
    for j in range(4):
        reset();buf=io.StringIO()
        with redirect_stdout(buf): root=emit(J[i][j])
        n,h,bounds=root;Jbounds[i,j]=bounds
        print(f'private theorem j_bounds_{i}_{j} (x : Fin 4 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) :')
        print(f'    {lit(bounds[0])} ≤ formula x {i} {j} ∧ formula x {i} {j} ≤ {lit(bounds[1])} := by')
        print(buf.getvalue(),end='')
        print(f'  have he : formula x {i} {j} = {n} := by')
        print('    norm_num [formula,Matrix.of_apply,Matrix.cons_val_two,Matrix.cons_val_three,'+','.join(defs)+'] <;> ring')
        print(f'  rw [he]\n  exact {h}\n')

radii={}
for i in range(4):
    for j in range(4):
        reset();buf=io.StringIO()
        with redirect_stdout(buf):
            js=[declare(f'formula x {k} {j}',Jbounds[k,j],lambda n,k=k:f'j_bounds_{k}_{j} x hx') for k in range(4)]
            parts=[binary('*',emit(sp.Rational(C[i][k].numerator,C[i][k].denominator)),js[k]) for k in range(4)]
            total=parts[0]
            for part in parts[1:]:total=binary('+',total,part)
            out=binary('+',emit(sp.Integer(i==j)),negate(total))
        n,h,(lo,hi)=out;rad=max(abs(lo),abs(hi));radii[i,j]=rad
        assert rad<Q(1,10**6)
        print(f'private theorem e_bound_{i}_{j} (x : Fin 4 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) :')
        print(f'    |(1-preconditioner*formula x) {i} {j}| ≤ {lit(rad)} := by')
        print(buf.getvalue(),end='')
        print(f'  have he : (1-preconditioner*formula x) {i} {j} = {n} := by')
        print('    norm_num [Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_four,preconditioner,Matrix.of_apply,Matrix.cons_val_two,Matrix.cons_val_three,'+','.join(defs)+'] <;> ring')
        print(f'  rw [he]\n  exact abs_bound {h} (by norm_num) (by norm_num)\n')

assert max(sum((radii[i,j] for j in range(4)),Q(0)) for i in range(4))<Q(1,10**6)
print("""/-- All transcendental inputs and rounded rational arithmetic are kernel
checked in small reusable lemmas. No external analytic enclosure is assumed. -/
theorem row_defect_bound (x : Fin 4 → ℝ) (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) :
    ∀ i, ∑ j, |(1-preconditioner*formula x) i j| < (1 : ℝ)/1000000 := by""")
for i in range(4):
    for j in range(4):print(f'  have b{i}{j} := e_bound_{i}_{j} x hx')
print('  intro i\n  fin_cases i')
for i in range(4):
    print('  · rw [Fin.sum_univ_four]')
    print('    change '+' + '.join(f'|(1-preconditioner*formula x) {i} {j}|' for j in range(4))+' < (1 : ℝ)/1000000')
    print('    linarith only ['+','.join(f'b{i}{j}' for j in range(4))+']')
print('''
/-- Exact four-coordinate multiplication of the ORIGINAL amplitude partial. -/
theorem ordered_partial_coordinates
    (a h : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)
    (K : TailMatrix (Fin 2) 1) (b : ℝ) (i : Fin 4) :
    ∑ j, formula (fun k => amplitudeValues a (index k)) i j*amplitudeValues h (index j) =
      amplitudeValues (actualPartial z rho sigma K b a h) (index i) := by
  simp_rw [← jacobian_formula_actual a K b]
  exact (index.sum_comp (fun j => jacobian z rho sigma K b a (index i) j*amplitudeValues h j)).trans
    (actual_partial_coordinates z rho sigma K b a h (index i)).symm

/-- A true kernel certificate for actual M2 amplitude regularity on the
explicit NONEMPTY box. Coupling and ALL strengths remain arbitrary. This
asserts no root existence, PY matching, canonical stability or Taylor bound. -/
theorem actual_regular_on_box (a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)
    (K : TailMatrix (Fin 2) 1) (b : ℝ)
    (ha : ∀ i, lower i ≤ amplitudeValues a (index i) ∧ amplitudeValues a (index i) ≤ upper i) :
    EndpointRegular z rho sigma K b a := by
  classical
  have hj := matrix_injective_of_row_defect (formula (fun i => amplitudeValues a (index i))) preconditioner
    (fun i => (row_defect_bound _ ha i).trans (by norm_num))
  have hl : Function.Injective (actualPartial z rho sigma K b a) := by
    intro h1 h2 he
    apply amplitude_values_injective
    have hc : (fun i => amplitudeValues h1 (index i)) = (fun i => amplitudeValues h2 (index i)) := by
      apply hj
      funext i
      change (∑ j, formula (fun k => amplitudeValues a (index k)) i j*amplitudeValues h1 (index j)) =
        (∑ j, formula (fun k => amplitudeValues a (index k)) i j*amplitudeValues h2 (index j))
      rw [ordered_partial_coordinates a h1 K b,ordered_partial_coordinates a h2 K b,he]
    funext k
    obtain ⟨i,rfl⟩ := index.surjective k
    exact congrFun hc i
  let L := actualPartial z rho sigma K b a
  have hk : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hl
  have hs : L.range = ⊤ := LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hl)
  exact ⟨ContinuousLinearEquiv.ofBijective L hk hs,ContinuousLinearEquiv.coe_ofBijective L hk hs⟩

end FMSA.Convergence.M2KernelCertificate''')
