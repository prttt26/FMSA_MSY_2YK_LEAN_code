#!/usr/bin/env python3
"""Emit candidate M2 zero-mode coefficients; Lean proves the actual dictionary.

Coefficients match the frozen TwoTail observable at eta=1/10,z=(9/5,12).
No numerical witness or analytic enclosure is a proof premise.
"""
import sympy as s
eta=s.Rational(1,10);rho=6*eta/s.pi;v=1-eta
zs=[s.Rational(9,5),s.Integer(12)]
a=[s.expand(rho*(6*eta+(4*eta-1)*z+(eta-1)*z*z)/(v*v*z*z)) for z in zs]
b=[s.expand(12*eta*rho/(v*v*z**3)*(-(1+2*eta)*z*(1-(1+z)*s.exp(-z))+6*eta*(1-(1+z+z*z/2)*s.exp(-z)))) for z in zs]
def lean(e):
 if e==s.pi:return 'Real.pi'
 if e.is_Integer:return f'({int(e)} : ℝ)'
 if e.is_Rational:return f'(({int(e.p)} : ℝ)/{int(e.q)})'
 if e.func==s.exp:return '(Real.exp '+lean(e.args[0])+')'
 if e.func==s.Add:return '('+'+'.join(lean(x) for x in e.args)+')'
 if e.func==s.Mul:return '('+'*'.join(lean(x) for x in e.args)+')'
 if e.func==s.Pow and e.exp.is_Integer:return '('+lean(e.base)+f'^{abs(int(e.exp))})'+('⁻¹' if e.exp<0 else '')
 raise ValueError(e)
print('''import MSAConvergence.M2ResidualDerivative

/-! Honest zero-frequency M2 factor and its genuine amplitude derivative.
The observable is proved from the actual zeroth integral moment, never by
substituting zero into a quotient formula valid only off the origin. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.M2ZeroMode
open FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.M2JacobianFormula
open FMSA.Convergence.CanonicalKernelEstimates FMSA.Convergence.CanonicalFirstLoss
open FMSA.Convergence.CanonicalNeighborhood FMSA.Paper.BaxterZeroMode
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
''')
print('def alpha : Fin 2 → ℝ := !['+','.join(map(lean,a))+']')
print('def beta : Fin 2 → ℝ := !['+','.join(map(lean,b))+']')
print('''
def zeroMode (x : Fin 4 → ℝ) : ℝ :=
  40/27+x 0*(alpha 0+beta 0*x 2)+x 1*(alpha 1+beta 1*x 3)
def gradient (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![alpha 0+beta 0*x 2,alpha 1+beta 1*x 3,beta 0*x 0,beta 1*x 1]
def gradientCLM (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ i, gradient x i • (ContinuousLinearMap.proj i : (Fin 4 → ℝ) →L[ℝ] ℝ)

private theorem rates_pos : ∀ u, 0 < z u := by intro u; fin_cases u <;> norm_num [z]
private theorem vacancy : vacMix rho sigma = 9/10 := by
  norm_num [vacMix,etaMix,rho,sigma,Fin.sum_univ_one]
private theorem hqpp : Qppphys rho sigma 0 0 = 80*Real.pi/27 := by
  simp [Qppphys,vacancy,xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

/-- Exact agreement with the ORIGINAL amplitude A, at every amplitude. -/
theorem actual_amplitude_formula (x : Fin 4 → ℝ) :
    amplitudeA z rho sigma (point x).1 (point x).2 0/(2*Real.pi) = zeroMode x := by
  norm_num [amplitudeA,mixDA,mixM,mixN,Wt,Ct,gam,hqpp,vacancy,
    z,rho,sigma,point,Fin.sum_univ_two,Fin.sum_univ_one,alpha,beta,zeroMode]
  norm_num [xi2,rho,sigma,sigMix,Fin.sum_univ_one]
  field_simp [Real.pi_ne_zero]
  ring

/-- The true zeroth integral moment, with its density, gives this observable. -/
theorem actual_moment_formula (x : Fin 4 → ℝ) :
    1-rho 0*nonlinearQMoment0 z rho sigma (point x).1 (point x).2 0 0 = zeroMode x := by
  rw [← actual_amplitude_formula]
  exact scalar_zeroMoment_balance z (fun u => (rates_pos u).ne') rho sigma _ _
    (by rw [vacancy]; norm_num)

/-- The HONEST Laplace integral factor at s=0, not a quotient junk value. -/
theorem actual_laplace_at_zero (x : Fin 4 → ℝ) :
    1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma (point x).1 (point x).2) 0 0 0 =
      (zeroMode x : ℂ) := by
  rw [kernel_laplace_at_zero z rates_pos rho sigma (by intro i; norm_num [sigma]) (point x)]
  exact_mod_cast actual_moment_formula x

/-- The actual whole renewal determinant, at the genuine frequency origin. -/
theorem actual_renewalDet_at_zero (x : Fin 4 → ℝ) :
    renewalDet z rho sigma (point x) 0 = (zeroMode x : ℂ) := by
  rw [renewalDet,Matrix.det_fin_one]
  simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true] using actual_laplace_at_zero x

/-- The physical density-weighted Fourier factor, including k=0. -/
theorem actual_fourier_at_zero (x : Fin 4 → ℝ) :
    fourierFactor z rho sigma (amplitudeA z rho sigma (point x).1 (point x).2)
      (amplitudeQp z rho sigma (point x).1 (point x).2)
      (W z rho (point x).1 (point x).2) (C z rho sigma (point x).1 (point x).2) 0 0 0 =
      (zeroMode x : ℂ) := by
  rw [scalar_fourierFactor_zero z rates_pos rho sigma _ _ (by dsimp [rho]; positivity)
    (by norm_num [sigma]) (by rw [vacancy]; norm_num),actual_amplitude_formula]

/-- A zero is a true failure of full canonicity; no first-loss claim is made. -/
theorem not_canonical_of_zero (x : Fin 4 → ℝ) (h : zeroMode x = 0) :
    point x ∉ canonicalAmplitudes z rho sigma := by
  intro hc
  have hu := hc 0 (by simp)
  have hn := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  apply hn
  change renewalDet z rho sigma (point x) 0 = 0
  rw [actual_renewalDet_at_zero,h,Complex.ofReal_zero]

/-- Exact gradient action in the same four ORIGINAL coordinates. -/
theorem gradientCLM_apply (x h : Fin 4 → ℝ) :
    gradientCLM x h = ∑ i, gradient x i*h i := by
  simp [gradientCLM]

/-- The displayed polynomial gradient is the genuine Frechet derivative. -/
theorem hasFDerivAt_zeroMode (x : Fin 4 → ℝ) :
    HasFDerivAt zeroMode (gradientCLM x) x := by
  let p (i : Fin 4) := (ContinuousLinearMap.proj i : (Fin 4 → ℝ) →L[ℝ] ℝ)
  have hp (i : Fin 4) : HasFDerivAt (p i) (p i) x := (p i).hasFDerivAt
  have h := (((hp 0).mul (((hp 2).const_mul (beta 0)).const_add (alpha 0))).add
    ((hp 1).mul (((hp 3).const_mul (beta 1)).const_add (alpha 1)))).const_add (40/27)
  convert! h using 1 <;> ext v <;>
    simp [zeroMode,p,gradientCLM,gradient,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

/-- Differentiating along ANY actual coordinate curve gives grad(F0)*v. -/
theorem hasDerivAt_along (p : ℝ → Fin 4 → ℝ) (v : Fin 4 → ℝ) (t : ℝ)
    (hp : HasDerivAt p v t) :
    HasDerivAt (fun s => zeroMode (p s)) (∑ i, gradient (p t) i*v i) t := by
  simpa only [gradientCLM_apply,Function.comp_def] using (hasFDerivAt_zeroMode (p t)).comp_hasDerivAt t hp

/-- This is also the true derivative of the HONEST complex Laplace factor. -/
theorem honest_factor_hasDerivAt (p : ℝ → Fin 4 → ℝ) (v : Fin 4 → ℝ) (t : ℝ)
    (hp : HasDerivAt p v t) :
    HasDerivAt (fun s => 1-rdfMatrixLaplace
      (nonlinearCausalKernel z rho sigma (point (p s)).1 (point (p s)).2) 0 0 0)
      ((∑ i, gradient (p t) i*v i : ℝ) : ℂ) t := by
  simp_rw [actual_laplace_at_zero]
  exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_along p v t hp)

/-- Concrete counterexample to substituting s=0 into the quotient transform:
even at fixed positive physical density, it misses the true moment. -/
theorem quotient_zero_is_not_actual_moment :
    1-rho 0*dressedQhat z rho sigma (point 0).1 (point 0).2 0 0 0 ≠ zeroMode 0 := by
  norm_num [dressedQhat,Qhat,amplitudeA,amplitudeQp,W,C,Wt,Ct,gam,point,zeroMode,
    z,sigma,rho,Fin.sum_univ_two]

end FMSA.Convergence.M2ZeroMode''')
