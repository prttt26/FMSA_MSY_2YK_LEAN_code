#!/usr/bin/env python3
"""Emit candidate M2 residual formulas and ordinary-kernel equality proofs.

The four original residual coordinates, arbitrary coupling and strengths are
retained. SymPy is an expression generator only; Lean proves all identities.
Output is an unguarded body on stdout; guards require real compiler queries.
"""
import sympy as sp
from codex_m2_jacobian_arb import symbolic_residual

amp,(tau,weight),R,_=symbolic_residual()
beta,k0,k1=sp.symbols('beta k0 k1')
R=[sp.expand(R[0].subs(tau,0)-10*sp.pi*beta*k0/9),
   sp.expand(R[1].subs(tau,0)-sp.pi*beta*k1/6),R[2],R[3]]
assert all(not e.atoms(sp.Float) and e.free_symbols <= set(amp)|{beta,k0,k1} for e in R)

def lean(e):
    if e in amp:return f'x {amp.index(e)}'
    if e==beta:return 'b'
    if e==k0:return 'K 0 0 0'
    if e==k1:return 'K 1 0 0'
    if e==sp.pi:return 'Real.pi'
    if e.is_Integer:return f'({int(e)} : ℝ)'
    if e.is_Rational:return f'(({int(e.p)} : ℝ) / {int(e.q)})'
    if e.func==sp.exp:return '(Real.exp '+lean(e.args[0])+')'
    if e.func==sp.Add:return '('+' + '.join(lean(a) for a in e.args)+')'
    if e.func==sp.Mul:return '('+' * '.join(lean(a) for a in e.args)+')'
    if e.func==sp.Pow and e.exp.is_Integer:
        n=int(e.exp);return '('+lean(e.base)+f' ^ {abs(n)})'+('⁻¹' if n<0 else '')
    raise ValueError(e)

print('''import MSAConvergence.M2JacobianFormula

/-! Exact four-coordinate formulas of the ORIGINAL M2 residual, with arbitrary
coupling and strengths. Symbolic candidates are checked against actual literal
BH polynomial evaluation; no numerical or root assumption is used. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2ResidualFormula
open FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.M2JacobianFormula
open FMSA.ExactMSA.Breakpoint MSAMixture
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

private lemma hv : vacMix rho sigma = 9/10 := by
  norm_num [vacMix,etaMix,rho,sigma,Fin.sum_univ_one]
private lemma hqp : Q0phys rho sigma 0 0 = 70*Real.pi/27 := by
  simp [Q0phys,hv,xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring
private lemma hqpp : Qppphys rho sigma 0 0 = 80*Real.pi/27 := by
  simp [Qppphys,hv,xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring
private lemma h18 : Real.exp (-(18/5 : ℝ)) = Real.exp (-(9/5 : ℝ))^2 := by
  rw [← Real.exp_nat_mul]
  norm_num
private lemma h69 : Real.exp (-(69/5 : ℝ)) = Real.exp (-(9/5 : ℝ))*Real.exp (-12) := by
  rw [← Real.exp_add]
  norm_num
private lemma h24 : Real.exp (-24) = Real.exp (-12)^2 := by
  rw [← Real.exp_nat_mul]
  norm_num

/-- The original residual scaling, not a rescaled root-only surrogate. -/
def residualFormula (K : TailMatrix (Fin 2) 1) (b : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
''')
print('  !['+',\n    '.join(lean(e) for e in R)+']\n')
coords=['(false,0,0,0)','(false,1,0,0)','(true,0,0,0)','(true,1,0,0)']
for i in range(4):
    print(f'''private theorem entry_{i} (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,point x)) {coords[i]} =
      {lean(R[i])} := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring
''')
print('''/-- Exact original residual evaluation, at EVERY amplitude and parameter point. -/
theorem actual_formula (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) (i : Fin 4) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,point x)) (index i) =
      residualFormula K b x i := by
  fin_cases i''')
for i in range(4):print(f'  · exact entry_{i} x K b')
print('''
/-- Vanishing of all four formulas is equivalent to the actual BH root. -/
theorem actual_root_iff_formula_zero (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    IsRoot z rho sigma (b • K) (point x).1 (point x).2 ↔ residualFormula K b x = 0 := by
  rw [← residual_eq_zero_iff z rho sigma K (point x).1 (point x).2 b]
  constructor
  · intro h
    funext i
    rw [← actual_formula]
    simp only [h,amplitudeValues]
    cases (index i).1 <;> rfl
  · intro h
    apply (amplitude_values_zero_iff _).mp
    intro j
    obtain ⟨i,rfl⟩ := index.surjective j
    rw [actual_formula]
    exact congrFun h i

end FMSA.Convergence.M2ResidualFormula''')
