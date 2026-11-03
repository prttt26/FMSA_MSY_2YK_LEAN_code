#!/usr/bin/env python3
"""Emit a Lean proof body identifying ALL 16 original M2 Jacobian entries.

SymPy supplies only candidate expressions. Lean proves each from the literal
actual polynomial definitions. No numerical enclosure is trusted. Output is
stdout; redirect to an explicit research/scratch path. Requires SymPy/flint
via the existing read-only dependency directory. Exact axiom guards are added
only after querying the compiled declarations, never inferred here.
"""
import sympy as sp
from codex_m2_jacobian_arb import symbolic_residual

amp, _, residual, J = symbolic_residual()

def lean(e):
    if e in amp: return f'x {amp.index(e)}'
    if e == sp.pi: return 'Real.pi'
    if e.is_Integer: return f'({int(e)} : ℝ)'
    if e.is_Rational: return f'(({int(e.p)} : ℝ) / {int(e.q)})'
    if e.func == sp.exp: return '(Real.exp '+lean(e.args[0])+')'
    if e.func == sp.Add: return '('+' + '.join(lean(a) for a in e.args)+')'
    if e.func == sp.Mul: return '('+' * '.join(lean(a) for a in e.args)+')'
    if e.func == sp.Pow and e.exp.is_Integer:
        n=int(e.exp)
        return '('+lean(e.base)+f' ^ {abs(n)})'+('⁻¹' if n < 0 else '')
    raise ValueError(e)

prefix='''import MSAConvergence.BHPolynomialJacobian

/-! Literal M2 four-coordinate Jacobian formulas, PROVED from the original
polynomial residual. A symbolic generator supplies candidate expressions only.
No numeric interval, root existence, canonicity or Taylor radius is assumed. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2JacobianFormula
open FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.ExactMSA.Breakpoint MSAMixture
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def z : Fin 2 → ℝ := ![9/5,12]
def rho : Fin 1 → ℝ := fun _ => (3/5)/Real.pi
def sigma : Fin 1 → ℝ := fun _ => 1

/-- Ordered ORIGINAL coordinates: Dt1, Dt2, G1, G2. -/
def index : Fin 4 ≃ AmpIndex (Fin 2) 1 :=
  Equiv.ofBijective (fun i => ![(false,0,0,0),(false,1,0,0),(true,0,0,0),(true,1,0,0)] i)
    (by decide)

def point (x : Fin 4 → ℝ) : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1 :=
  (fun u _ _ => ![x 0,x 1] u, fun u _ _ => ![x 2,x 3] u)

/-- Exact forward four-coordinate encoding, with no float convention. -/
theorem point_coordinates (x : Fin 4 → ℝ) (i : Fin 4) :
    amplitudeValues (point x) (index i) = x i := by
  fin_cases i <;> rfl

/-- The ordered encoding recovers ALL original amplitudes, not just a root. -/
theorem point_coordinates_inverse (a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1) :
    point (fun i => amplitudeValues a (index i)) = a := by
  apply Prod.ext
  · funext u i j
    fin_cases u <;> fin_cases i <;> fin_cases j <;> rfl
  · funext u i j
    fin_cases u <;> fin_cases i <;> fin_cases j <;> rfl

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

/-- Exact expanded expressions in the original four coordinates. -/
def formula (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
'''
print(prefix+'  !!['+';\n      '.join(', '.join(lean(e) for e in row) for row in J)+']\n')
coords=['(false,0,0,0)','(false,1,0,0)','(true,0,0,0)','(true,1,0,0)']
for i in range(4):
    for j in range(4):
        print(f"""private theorem entry_{i}_{j} (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) {coords[i]} {coords[j]} = {lean(J[i][j])} := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring
""")
print("""/-- ALL 16 symbolic candidates are proved against the literal original
BH polynomial Jacobian. K and coupling are arbitrary; no root or physical
box premise is supplied to this identity. -/
theorem jacobian_formula (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ)
    (i j : Fin 4) :
    jacobian z rho sigma K b (point x) (index i) (index j) = formula x i j := by
  fin_cases i <;> fin_cases j""")
for i in range(4):
    for j in range(4):
        print(f'  · exact entry_{i}_{j} x K b')
print("""
/-- The same formula for EVERY original amplitude point via a proved exact
coordinate inverse. -/
theorem jacobian_formula_actual (a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)
    (K : TailMatrix (Fin 2) 1) (b : ℝ) (i j : Fin 4) :
    jacobian z rho sigma K b a (index i) (index j) =
      formula (fun k => amplitudeValues a (index k)) i j := by
  simpa only [point_coordinates_inverse] using
    jacobian_formula (fun k => amplitudeValues a (index k)) K b i j

end FMSA.Convergence.M2JacobianFormula""")
