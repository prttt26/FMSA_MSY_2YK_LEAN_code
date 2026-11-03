import MSAConvergence.M2JacobianFormula

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

  ![((((7441 : ℝ) / 6561) * x 0) + (((-35699 : ℝ) / 177147) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((5150 : ℝ) / 6561) * x 0 * (Real.exp ((-9 : ℝ) / 5))) + (((-54289 : ℝ) / 531441) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-24353 : ℝ) / 78732) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-10 : ℝ) / 9) * Real.pi * b * K 0 0 0) + (((2809 : ℝ) / 354294) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-9 : ℝ) / 5))) + (((-88507 : ℝ) / 18108360) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((-2809 : ℝ) / 531441) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((12655 : ℝ) / 452709) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24698 : ℝ) / 531441) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 905418) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ)))),
    ((((2053 : ℝ) / 1944) * x 1) + (((-23077 : ℝ) / 466560) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((23 : ℝ) / 1944) * x 1 * (Real.exp (-12 : ℝ))) + (((-12769 : ℝ) / 4665600) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((-8849 : ℝ) / 524880) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-1 : ℝ) / 6) * Real.pi * b * K 1 0 0) + (((10201 : ℝ) / 466560) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-12 : ℝ))) + (((-25853 : ℝ) / 905418) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹) + (((-10201 : ℝ) / 4665600) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-24 : ℝ))) + (((11413 : ℝ) / 2332800) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 12072240) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 18108360) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 39366) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))),
    ((((-12655 : ℝ) / 150903) * x 1) + (((-5150 : ℝ) / 2187) * Real.pi) + (((-2809 : ℝ) / 118098) * x 0) + (((-108578 : ℝ) / 531441) * x 0 * (x 2 ^ 2)) + (((-24698 : ℝ) / 177147) * x 0 * x 2) + (((-24353 : ℝ) / 39366) * x 1 * x 2) + (((143 : ℝ) / 13122) * x 1 * x 3) + (((14882 : ℝ) / 6561) * Real.pi * x 2) + (((-88507 : ℝ) / 9054180) * x 1 * x 2 * x 3) + (((-5618 : ℝ) / 531441) * x 0 * (x 2 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((2531 : ℝ) / 301806) * x 1 * x 3 * (Real.exp (-12 : ℝ))) + (((5618 : ℝ) / 177147) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((10300 : ℝ) / 6561) * Real.pi * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((25310 : ℝ) / 452709) * x 1 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((49396 : ℝ) / 531441) * x 0 * (x 2 ^ 2) * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 452709) * x 1 * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 1 * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 1 * x 2 * x 3 * (Real.exp (-12 : ℝ)))),
    ((((-72499 : ℝ) / 603612) * x 0) + (((-10201 : ℝ) / 23328) * x 1) + (((-115 : ℝ) / 486) * Real.pi) + (((-12769 : ℝ) / 2332800) * x 1 * (x 3 ^ 2)) + (((-11413 : ℝ) / 116640) * x 1 * x 3) + (((-8849 : ℝ) / 262440) * x 0 * x 3) + (((410 : ℝ) / 19683) * x 0 * x 2) + (((2053 : ℝ) / 972) * Real.pi * x 3) + (((-25853 : ℝ) / 452709) * x 0 * x 2 * x 3) + (((-10201 : ℝ) / 2332800) * x 1 * (x 3 ^ 2) * (Real.exp (-24 : ℝ))) + (((23 : ℝ) / 972) * Real.pi * x 3 * (Real.exp (-12 : ℝ))) + (((10201 : ℝ) / 116640) * x 1 * x 3 * (Real.exp (-12 : ℝ))) + (((11413 : ℝ) / 1166400) * x 1 * (x 3 ^ 2) * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 905418) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((72499 : ℝ) / 6036120) * x 0 * x 3 * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 9054180) * x 0 * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 19683) * x 0 * x 2 * x 3 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 0 * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5))))]

private theorem entry_0 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,point x)) (false,0,0,0) =
      ((((7441 : ℝ) / 6561) * x 0) + (((-35699 : ℝ) / 177147) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((5150 : ℝ) / 6561) * x 0 * (Real.exp ((-9 : ℝ) / 5))) + (((-54289 : ℝ) / 531441) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-24353 : ℝ) / 78732) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-10 : ℝ) / 9) * Real.pi * b * K 0 0 0) + (((2809 : ℝ) / 354294) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-9 : ℝ) / 5))) + (((-88507 : ℝ) / 18108360) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((-2809 : ℝ) / 531441) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((12655 : ℝ) / 452709) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24698 : ℝ) / 531441) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 905418) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_1 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,point x)) (false,1,0,0) =
      ((((2053 : ℝ) / 1944) * x 1) + (((-23077 : ℝ) / 466560) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((23 : ℝ) / 1944) * x 1 * (Real.exp (-12 : ℝ))) + (((-12769 : ℝ) / 4665600) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((-8849 : ℝ) / 524880) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-1 : ℝ) / 6) * Real.pi * b * K 1 0 0) + (((10201 : ℝ) / 466560) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-12 : ℝ))) + (((-25853 : ℝ) / 905418) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹) + (((-10201 : ℝ) / 4665600) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-24 : ℝ))) + (((11413 : ℝ) / 2332800) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 12072240) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 18108360) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 39366) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_2 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,point x)) (true,0,0,0) =
      ((((-12655 : ℝ) / 150903) * x 1) + (((-5150 : ℝ) / 2187) * Real.pi) + (((-2809 : ℝ) / 118098) * x 0) + (((-108578 : ℝ) / 531441) * x 0 * (x 2 ^ 2)) + (((-24698 : ℝ) / 177147) * x 0 * x 2) + (((-24353 : ℝ) / 39366) * x 1 * x 2) + (((143 : ℝ) / 13122) * x 1 * x 3) + (((14882 : ℝ) / 6561) * Real.pi * x 2) + (((-88507 : ℝ) / 9054180) * x 1 * x 2 * x 3) + (((-5618 : ℝ) / 531441) * x 0 * (x 2 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((2531 : ℝ) / 301806) * x 1 * x 3 * (Real.exp (-12 : ℝ))) + (((5618 : ℝ) / 177147) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((10300 : ℝ) / 6561) * Real.pi * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((25310 : ℝ) / 452709) * x 1 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((49396 : ℝ) / 531441) * x 0 * (x 2 ^ 2) * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 452709) * x 1 * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 1 * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 1 * x 2 * x 3 * (Real.exp (-12 : ℝ)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_3 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,point x)) (true,1,0,0) =
      ((((-72499 : ℝ) / 603612) * x 0) + (((-10201 : ℝ) / 23328) * x 1) + (((-115 : ℝ) / 486) * Real.pi) + (((-12769 : ℝ) / 2332800) * x 1 * (x 3 ^ 2)) + (((-11413 : ℝ) / 116640) * x 1 * x 3) + (((-8849 : ℝ) / 262440) * x 0 * x 3) + (((410 : ℝ) / 19683) * x 0 * x 2) + (((2053 : ℝ) / 972) * Real.pi * x 3) + (((-25853 : ℝ) / 452709) * x 0 * x 2 * x 3) + (((-10201 : ℝ) / 2332800) * x 1 * (x 3 ^ 2) * (Real.exp (-24 : ℝ))) + (((23 : ℝ) / 972) * Real.pi * x 3 * (Real.exp (-12 : ℝ))) + (((10201 : ℝ) / 116640) * x 1 * x 3 * (Real.exp (-12 : ℝ))) + (((11413 : ℝ) / 1166400) * x 1 * (x 3 ^ 2) * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 905418) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((72499 : ℝ) / 6036120) * x 0 * x 3 * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 9054180) * x 0 * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 19683) * x 0 * x 2 * x 3 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 0 * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

/-- Exact original residual evaluation, at EVERY amplitude and parameter point. -/
theorem actual_formula (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) (i : Fin 4) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,point x)) (index i) =
      residualFormula K b x i := by
  fin_cases i
  · exact entry_0 x K b
  · exact entry_1 x K b
  · exact entry_2 x K b
  · exact entry_3 x K b

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

end FMSA.Convergence.M2ResidualFormula

/-- info: 'FMSA.Convergence.M2ResidualFormula.actual_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ResidualFormula.actual_formula

/-- info: 'FMSA.Convergence.M2ResidualFormula.actual_root_iff_formula_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ResidualFormula.actual_root_iff_formula_zero

