import MSAConvergence.ActualComplexBH
import MSAConvergence.BHPolynomialJacobian
import MSAConvergence.M3PhysicalBounds
import MSAConvergence.ComplexPolynomialSystem

/-! Literal original M3 data and exact four-coordinate encoding. No root,
canonicity, interval enclosure or Taylor-radius assertion is assumed. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M3ResidualModel
open FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.ExactMSA.Breakpoint MSAMixture

def z : Fin 2 → ℝ := ![7,14]
def rho : Fin 1 → ℝ := fun _ => 147/(50*Real.pi)
def sigma : Fin 1 → ℝ := fun _ => 1
def strengths : TailMatrix (Fin 2) 1 := fun u _ _ => ![1,-419/384] u

/-- The literal original order is Dt1,Dt2,G1,G2. -/
def index : Fin 4 ≃ AmpIndex (Fin 2) 1 :=
  Equiv.ofBijective (fun i => ![(false,0,0,0),(false,1,0,0),(true,0,0,0),(true,1,0,0)] i)
    (by decide)

def point (x : Fin 4 → ℝ) : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1 :=
  (fun u _ _ => ![x 0,x 1] u, fun u _ _ => ![x 2,x 3] u)

/-- Exact original forward coordinate order at every amplitude. -/
theorem point_coordinates (x : Fin 4 → ℝ) (i : Fin 4) :
    amplitudeValues (point x) (index i) = x i := by
  fin_cases i <;> rfl

/-- The four-coordinate representation recovers every original amplitude. -/
theorem point_coordinates_inverse (a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1) :
    point (fun i => amplitudeValues a (index i)) = a := by
  apply Prod.ext
  · funext u i j
    fin_cases u <;> fin_cases i <;> fin_cases j <;> rfl
  · funext u i j
    fin_cases u <;> fin_cases i <;> fin_cases j <;> rfl

/-- The fixed density is EXACTLY the original eta49/100 physical state. -/
theorem eta_eq : etaMix rho sigma = 49/100 := by
  norm_num [etaMix,rho,sigma,Fin.sum_univ_one]
  field_simp [Real.pi_ne_zero]
  ring

/-- Positive vacancy is proved from the original mixture definition. -/
theorem vacancy_eq : vacMix rho sigma = 51/100 := by
  rw [vacMix,eta_eq]
  norm_num

/-- Positive rates/diameters, nonnegative density and original strength
symmetry are all discharged from the exact state data. -/
theorem physical_data : (∀ u, 0 < z u) ∧ (∀ i, 0 < sigma i) ∧
    (∀ i, 0 ≤ rho i) ∧ (∀ u i j, strengths u i j = strengths u j i) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u
    fin_cases u <;> norm_num [z]
  · intro i
    norm_num [sigma]
  · intro i
    dsimp [rho]
    positivity
  · intro u i j
    fin_cases i
    fin_cases j
    rfl

/-- Exact ORIGINAL compact HS coefficients, with all pi factors retained. -/
theorem hs_coefficients : Q0phys rho sigma 0 0 = 8300*Real.pi/867 ∧
    Qppphys rho sigma 0 0 = 4400*Real.pi/289 := by
  constructor
  · simp [Q0phys,vacancy_eq,xi2,rho,sigma]
    field_simp [Real.pi_ne_zero]
    ring
  · simp [Qppphys,vacancy_eq,xi2,rho,sigma]
    field_simp [Real.pi_ne_zero]
    ring

/-- This actual state lies strictly below the proposed eta0.8 cap. -/
theorem eta_lt_four_fifths : etaMix rho sigma < 4/5 := by
  rw [eta_eq]
  norm_num

set_option maxRecDepth 10000

private lemma hv : vacMix rho sigma = 51/100 := vacancy_eq
private lemma hqp : Q0phys rho sigma 0 0 = 8300*Real.pi/867 := hs_coefficients.1
private lemma hqpp : Qppphys rho sigma 0 0 = 4400*Real.pi/289 := hs_coefficients.2
private lemma h14 : Real.exp (-14) = Real.exp (-7)^2 := by
  rw [← Real.exp_nat_mul]
  norm_num
private lemma h21 : Real.exp (-21) = Real.exp (-7)*Real.exp (-14) := by
  rw [← Real.exp_add]
  norm_num
private lemma h28 : Real.exp (-28) = Real.exp (-14)^2 := by
  rw [← Real.exp_nat_mul]
  norm_num

/-- Literal original M3 four-coordinate residual with exact fixed strengths.
Candidate expressions only; every equality is proved below at ALL amplitudes. -/
def formula (b : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![((((4111 : ℝ)/2023) * x 0) + (((-2751 : ℝ)/14450) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-2 : ℝ)/7) * Real.pi * b) + (((1426 : ℝ)/2023) * x 0 * (Real.exp (-7 : ℝ))) + (((-321489 : ℝ)/722500) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-3303 : ℝ)/7225) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((21 : ℝ)/28900) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp (-7 : ℝ))) + (((-24906 : ℝ)/180625) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((-11907 : ℝ)/361250) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp (-7 : ℝ))) + (((-919 : ℝ)/14450) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ))) + (((-441 : ℝ)/722500) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp (-14 : ℝ))) + (((-39879 : ℝ)/722500) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ))) + (((19299 : ℝ)/722500) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-21 : ℝ))) + (((69363 : ℝ)/361250) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ)))),
    ((((5989 : ℝ)/4046) * x 1) + (((-1302 : ℝ)/7225) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((419 : ℝ)/2688) * Real.pi * b) + (((647 : ℝ)/4046) * x 1 * (Real.exp (-14 : ℝ))) + (((-233289 : ℝ)/2890000) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((-354 : ℝ)/7225) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((1701 : ℝ)/57800) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-14 : ℝ))) + (((-174237 : ℝ)/722500) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹) + (((-35721 : ℝ)/2890000) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-28 : ℝ))) + (((73 : ℝ)/2890) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ))) + (((91287 : ℝ)/1445000) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-14 : ℝ))) + (((-31563 : ℝ)/722500) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ))) + (((-1533 : ℝ)/72250) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-21 : ℝ))) + (((7434 : ℝ)/180625) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ)))),
    ((((-71300 : ℝ)/42483) * Real.pi) + (((-1 : ℝ)/578) * x 0) + (((919 : ℝ)/6069) * x 1) + (((-321489 : ℝ)/361250) * x 0 * (x 2 ^ 2)) + (((-6606 : ℝ)/7225) * x 1 * x 2) + (((567 : ℝ)/7225) * x 0 * x 2) + (((1899 : ℝ)/14450) * x 1 * x 3) + (((8222 : ℝ)/2023) * Real.pi * x 2) + (((-49812 : ℝ)/180625) * x 1 * x 2 * x 3) + (((-11907 : ℝ)/180625) * x 0 * (x 2 ^ 2) * (Real.exp (-7 : ℝ))) + (((-919 : ℝ)/7225) * x 1 * x 2 * (Real.exp (-7 : ℝ))) + (((-919 : ℝ)/14450) * x 1 * x 3 * (Real.exp (-14 : ℝ))) + (((-441 : ℝ)/361250) * x 0 * (x 2 ^ 2) * (Real.exp (-14 : ℝ))) + (((21 : ℝ)/7225) * x 0 * x 2 * (Real.exp (-7 : ℝ))) + (((2852 : ℝ)/2023) * Real.pi * x 2 * (Real.exp (-7 : ℝ))) + (((-39879 : ℝ)/361250) * x 1 * x 2 * x 3 * (Real.exp (-7 : ℝ))) + (((19299 : ℝ)/361250) * x 1 * x 2 * x 3 * (Real.exp (-21 : ℝ))) + (((69363 : ℝ)/180625) * x 1 * x 2 * x 3 * (Real.exp (-14 : ℝ)))),
    ((((-32350 : ℝ)/42483) * Real.pi) + (((-730 : ℝ)/6069) * x 0) + (((-81 : ℝ)/578) * x 1) + (((-233289 : ℝ)/1445000) * x 1 * (x 3 ^ 2)) + (((-4347 : ℝ)/14450) * x 1 * x 3) + (((-708 : ℝ)/7225) * x 0 * x 3) + (((1503 : ℝ)/7225) * x 0 * x 2) + (((5989 : ℝ)/2023) * Real.pi * x 3) + (((-174237 : ℝ)/361250) * x 0 * x 2 * x 3) + (((-35721 : ℝ)/1445000) * x 1 * (x 3 ^ 2) * (Real.exp (-28 : ℝ))) + (((73 : ℝ)/1445) * x 0 * x 3 * (Real.exp (-14 : ℝ))) + (((146 : ℝ)/1445) * x 0 * x 2 * (Real.exp (-7 : ℝ))) + (((647 : ℝ)/2023) * Real.pi * x 3 * (Real.exp (-14 : ℝ))) + (((1701 : ℝ)/14450) * x 1 * x 3 * (Real.exp (-14 : ℝ))) + (((91287 : ℝ)/722500) * x 1 * (x 3 ^ 2) * (Real.exp (-14 : ℝ))) + (((-31563 : ℝ)/361250) * x 0 * x 2 * x 3 * (Real.exp (-14 : ℝ))) + (((-1533 : ℝ)/36125) * x 0 * x 2 * x 3 * (Real.exp (-21 : ℝ))) + (((14868 : ℝ)/180625) * x 0 * x 2 * x 3 * (Real.exp (-7 : ℝ))))]

set_option maxHeartbeats 10000000 in
-- Literal original residual expansion and exact ring normalization need this budget.
private theorem entry_0 (x : Fin 4 → ℝ) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma strengths (b,point x)) (false,0,0,0) =
      ((((4111 : ℝ)/2023) * x 0) + (((-2751 : ℝ)/14450) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-2 : ℝ)/7) * Real.pi * b) + (((1426 : ℝ)/2023) * x 0 * (Real.exp (-7 : ℝ))) + (((-321489 : ℝ)/722500) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-3303 : ℝ)/7225) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((21 : ℝ)/28900) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp (-7 : ℝ))) + (((-24906 : ℝ)/180625) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((-11907 : ℝ)/361250) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp (-7 : ℝ))) + (((-919 : ℝ)/14450) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ))) + (((-441 : ℝ)/722500) * x 2 * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp (-14 : ℝ))) + (((-39879 : ℝ)/722500) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ))) + (((19299 : ℝ)/722500) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-21 : ℝ))) + (((69363 : ℝ)/361250) * x 0 * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,strengths,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp [xi2,rho,sigma]
  simp only [h14,h21]
  field_simp [Real.pi_ne_zero]
  ring

set_option maxHeartbeats 10000000 in
-- Literal original residual expansion and exact ring normalization need this budget.
private theorem entry_1 (x : Fin 4 → ℝ) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma strengths (b,point x)) (false,1,0,0) =
      ((((5989 : ℝ)/4046) * x 1) + (((-1302 : ℝ)/7225) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((419 : ℝ)/2688) * Real.pi * b) + (((647 : ℝ)/4046) * x 1 * (Real.exp (-14 : ℝ))) + (((-233289 : ℝ)/2890000) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((-354 : ℝ)/7225) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((1701 : ℝ)/57800) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-14 : ℝ))) + (((-174237 : ℝ)/722500) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹) + (((-35721 : ℝ)/2890000) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-28 : ℝ))) + (((73 : ℝ)/2890) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ))) + (((91287 : ℝ)/1445000) * x 3 * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-14 : ℝ))) + (((-31563 : ℝ)/722500) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ))) + (((-1533 : ℝ)/72250) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-21 : ℝ))) + (((7434 : ℝ)/180625) * x 0 * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,strengths,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp [xi2,rho,sigma]
  simp only [h14,h21,h28]
  field_simp [Real.pi_ne_zero]
  ring

set_option maxHeartbeats 10000000 in
-- Literal original residual expansion and exact ring normalization need this budget.
private theorem entry_2 (x : Fin 4 → ℝ) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma strengths (b,point x)) (true,0,0,0) =
      ((((-71300 : ℝ)/42483) * Real.pi) + (((-1 : ℝ)/578) * x 0) + (((919 : ℝ)/6069) * x 1) + (((-321489 : ℝ)/361250) * x 0 * (x 2 ^ 2)) + (((-6606 : ℝ)/7225) * x 1 * x 2) + (((567 : ℝ)/7225) * x 0 * x 2) + (((1899 : ℝ)/14450) * x 1 * x 3) + (((8222 : ℝ)/2023) * Real.pi * x 2) + (((-49812 : ℝ)/180625) * x 1 * x 2 * x 3) + (((-11907 : ℝ)/180625) * x 0 * (x 2 ^ 2) * (Real.exp (-7 : ℝ))) + (((-919 : ℝ)/7225) * x 1 * x 2 * (Real.exp (-7 : ℝ))) + (((-919 : ℝ)/14450) * x 1 * x 3 * (Real.exp (-14 : ℝ))) + (((-441 : ℝ)/361250) * x 0 * (x 2 ^ 2) * (Real.exp (-14 : ℝ))) + (((21 : ℝ)/7225) * x 0 * x 2 * (Real.exp (-7 : ℝ))) + (((2852 : ℝ)/2023) * Real.pi * x 2 * (Real.exp (-7 : ℝ))) + (((-39879 : ℝ)/361250) * x 1 * x 2 * x 3 * (Real.exp (-7 : ℝ))) + (((19299 : ℝ)/361250) * x 1 * x 2 * x 3 * (Real.exp (-21 : ℝ))) + (((69363 : ℝ)/180625) * x 1 * x 2 * x 3 * (Real.exp (-14 : ℝ)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,strengths,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp [xi2,rho,sigma]
  simp only [h14,h21]
  field_simp [Real.pi_ne_zero]
  ring

set_option maxHeartbeats 10000000 in
-- Literal original residual expansion and exact ring normalization need this budget.
private theorem entry_3 (x : Fin 4 → ℝ) (b : ℝ) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma strengths (b,point x)) (true,1,0,0) =
      ((((-32350 : ℝ)/42483) * Real.pi) + (((-730 : ℝ)/6069) * x 0) + (((-81 : ℝ)/578) * x 1) + (((-233289 : ℝ)/1445000) * x 1 * (x 3 ^ 2)) + (((-4347 : ℝ)/14450) * x 1 * x 3) + (((-708 : ℝ)/7225) * x 0 * x 3) + (((1503 : ℝ)/7225) * x 0 * x 2) + (((5989 : ℝ)/2023) * Real.pi * x 3) + (((-174237 : ℝ)/361250) * x 0 * x 2 * x 3) + (((-35721 : ℝ)/1445000) * x 1 * (x 3 ^ 2) * (Real.exp (-28 : ℝ))) + (((73 : ℝ)/1445) * x 0 * x 3 * (Real.exp (-14 : ℝ))) + (((146 : ℝ)/1445) * x 0 * x 2 * (Real.exp (-7 : ℝ))) + (((647 : ℝ)/2023) * Real.pi * x 3 * (Real.exp (-14 : ℝ))) + (((1701 : ℝ)/14450) * x 1 * x 3 * (Real.exp (-14 : ℝ))) + (((91287 : ℝ)/722500) * x 1 * (x 3 ^ 2) * (Real.exp (-14 : ℝ))) + (((-31563 : ℝ)/361250) * x 0 * x 2 * x 3 * (Real.exp (-14 : ℝ))) + (((-1533 : ℝ)/36125) * x 0 * x 2 * x 3 * (Real.exp (-21 : ℝ))) + (((14868 : ℝ)/180625) * x 0 * x 2 * x 3 * (Real.exp (-7 : ℝ)))) := by
  rw [← eval_endpointPoly]
  norm_num [endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,strengths,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one]
  simp [xi2,rho,sigma]
  simp only [h14,h21,h28]
  field_simp [Real.pi_ne_zero]
  ring

/-- Exact ORIGINAL residual values at EVERY amplitude and real coupling. -/
theorem actual_formula (x : Fin 4 → ℝ) (b : ℝ) (i : Fin 4) :
    amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma strengths (b,point x)) (index i) =
      formula b x i := by
  fin_cases i
  · exact entry_0 x b
  · exact entry_1 x b
  · exact entry_2 x b
  · exact entry_3 x b

/-- All four formula zeros are equivalent to the original M3 BH root;
there is no rescaling or root-only surrogate. -/
theorem actual_root_iff_formula_zero (x : Fin 4 → ℝ) (b : ℝ) :
    IsRoot z rho sigma (b • strengths) (point x).1 (point x).2 ↔ formula b x = 0 := by
  rw [← residual_eq_zero_iff z rho sigma strengths (point x).1 (point x).2 b]
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

open FMSA.Convergence.ComplexPolynomialSystem

/-- The exact joint polynomial system retains coupling and ALL amplitudes,
with the original physical real pi/exp coefficients. -/
def polynomial : Fin 4 → MvPolynomial (Option (Fin 4)) ℝ :=
  ![((MvPolynomial.C ((((-321489 : ℝ)/722500) * (Real.pi ^ 1)⁻¹) + (((-11907 : ℝ)/361250) * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ))) + (((-441 : ℝ)/722500) * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 2 * (MvPolynomial.X (some (2 : Fin 4))) ^ 1) + (MvPolynomial.C ((((-2751 : ℝ)/14450) * (Real.pi ^ 1)⁻¹) + (((21 : ℝ)/28900) * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 2) + (MvPolynomial.C ((((-24906 : ℝ)/180625) * (Real.pi ^ 1)⁻¹) + (((-39879 : ℝ)/722500) * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ))) + (((19299 : ℝ)/722500) * (Real.pi ^ 1)⁻¹ * (Real.exp (-21 : ℝ))) + (((69363 : ℝ)/361250) * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (1 : Fin 4))) ^ 1 * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C ((((-3303 : ℝ)/7225) * (Real.pi ^ 1)⁻¹) + (((-919 : ℝ)/14450) * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (1 : Fin 4))) ^ 1) + (MvPolynomial.C (((4111 : ℝ)/2023) + (((1426 : ℝ)/2023) * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1) + (MvPolynomial.C (((-2 : ℝ)/7) * Real.pi) * (MvPolynomial.X none) ^ 1)),
    ((MvPolynomial.C ((((-174237 : ℝ)/722500) * (Real.pi ^ 1)⁻¹) + (((-31563 : ℝ)/722500) * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ))) + (((-1533 : ℝ)/72250) * (Real.pi ^ 1)⁻¹ * (Real.exp (-21 : ℝ))) + (((7434 : ℝ)/180625) * (Real.pi ^ 1)⁻¹ * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (1 : Fin 4))) ^ 1 * (MvPolynomial.X (some (2 : Fin 4))) ^ 1) + (MvPolynomial.C ((((-354 : ℝ)/7225) * (Real.pi ^ 1)⁻¹) + (((73 : ℝ)/2890) * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (1 : Fin 4))) ^ 1) + (MvPolynomial.C ((((-233289 : ℝ)/2890000) * (Real.pi ^ 1)⁻¹) + (((-35721 : ℝ)/2890000) * (Real.pi ^ 1)⁻¹ * (Real.exp (-28 : ℝ))) + (((91287 : ℝ)/1445000) * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 2 * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C ((((-1302 : ℝ)/7225) * (Real.pi ^ 1)⁻¹) + (((1701 : ℝ)/57800) * (Real.pi ^ 1)⁻¹ * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 2) + (MvPolynomial.C (((5989 : ℝ)/4046) + (((647 : ℝ)/4046) * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1) + (MvPolynomial.C (((419 : ℝ)/2688) * Real.pi) * (MvPolynomial.X none) ^ 1)),
    ((MvPolynomial.C (((-321489 : ℝ)/361250) + (((-11907 : ℝ)/180625) * (Real.exp (-7 : ℝ))) + (((-441 : ℝ)/361250) * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (2 : Fin 4))) ^ 2) + (MvPolynomial.C (((567 : ℝ)/7225) + (((21 : ℝ)/7225) * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (2 : Fin 4))) ^ 1) + (MvPolynomial.C ((-1 : ℝ)/578) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1) + (MvPolynomial.C (((-49812 : ℝ)/180625) + (((-39879 : ℝ)/361250) * (Real.exp (-7 : ℝ))) + (((19299 : ℝ)/361250) * (Real.exp (-21 : ℝ))) + (((69363 : ℝ)/180625) * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1 * (MvPolynomial.X (some (2 : Fin 4))) ^ 1 * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C (((-6606 : ℝ)/7225) + (((-919 : ℝ)/7225) * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1 * (MvPolynomial.X (some (2 : Fin 4))) ^ 1) + (MvPolynomial.C (((1899 : ℝ)/14450) + (((-919 : ℝ)/14450) * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1 * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C ((919 : ℝ)/6069) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1) + (MvPolynomial.C ((((8222 : ℝ)/2023) * Real.pi) + (((2852 : ℝ)/2023) * Real.pi * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (2 : Fin 4))) ^ 1) + (MvPolynomial.C (((-71300 : ℝ)/42483) * Real.pi))),
    ((MvPolynomial.C (((-174237 : ℝ)/361250) + (((-31563 : ℝ)/361250) * (Real.exp (-14 : ℝ))) + (((-1533 : ℝ)/36125) * (Real.exp (-21 : ℝ))) + (((14868 : ℝ)/180625) * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (2 : Fin 4))) ^ 1 * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C (((1503 : ℝ)/7225) + (((146 : ℝ)/1445) * (Real.exp (-7 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (2 : Fin 4))) ^ 1) + (MvPolynomial.C (((-708 : ℝ)/7225) + (((73 : ℝ)/1445) * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1 * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C ((-730 : ℝ)/6069) * (MvPolynomial.X (some (0 : Fin 4))) ^ 1) + (MvPolynomial.C (((-233289 : ℝ)/1445000) + (((-35721 : ℝ)/1445000) * (Real.exp (-28 : ℝ))) + (((91287 : ℝ)/722500) * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1 * (MvPolynomial.X (some (3 : Fin 4))) ^ 2) + (MvPolynomial.C (((-4347 : ℝ)/14450) + (((1701 : ℝ)/14450) * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1 * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C ((-81 : ℝ)/578) * (MvPolynomial.X (some (1 : Fin 4))) ^ 1) + (MvPolynomial.C ((((5989 : ℝ)/2023) * Real.pi) + (((647 : ℝ)/2023) * Real.pi * (Real.exp (-14 : ℝ)))) * (MvPolynomial.X (some (3 : Fin 4))) ^ 1) + (MvPolynomial.C (((-32350 : ℝ)/42483) * Real.pi)))]

set_option maxHeartbeats 10000000 in
-- Exact finite polynomial evaluation expands the generated real coefficients.
/-- Polynomial evaluation is exactly the independently verified real formula. -/
theorem polynomial_eval (b : ℝ) (x : Fin 4 → ℝ) (i : Fin 4) :
    MvPolynomial.eval (realPoint b x) (polynomial i) = formula b x i := by
  fin_cases i <;> simp [polynomial,formula,realPoint] <;> ring

/-- The candidate polynomial is IDENTICAL to the original BH polynomial,
after the proved ordered coordinate renaming; no numerical/root premise. -/
theorem polynomial_actual_identity (i : Fin 4) :
    MvPolynomial.rename (Option.map index) (polynomial i) =
      residualPoly z rho sigma strengths (index i) := by
  apply MvPolynomial.funext
  intro v
  let b := v none
  let x : Fin 4 → ℝ := fun j => v (some (index j))
  have hvpoint : pointValues (b,point x)=v := by
    funext j
    cases j with
    | none => rfl
    | some j =>
      obtain ⟨i,rfl⟩ := index.surjective j
      exact point_coordinates x i
  have hm : v ∘ Option.map index = realPoint b x := by
    funext j
    cases j <;> rfl
  rw [MvPolynomial.eval_rename,hm,polynomial_eval]
  rw [← hvpoint,eval_residualPoly,actual_formula]


/-- The complex representation retains ALL original amplitude coordinates. -/
def complexAmplitudes (a : Fin 4 → ℂ) : AmpIndex (Fin 2) 1 → ℂ :=
  fun j => a (index.symm j)

/-- The complex ordered representation is exactly the embedded ORIGINAL
real amplitude pair, not a new root/observable convention. -/
theorem complex_amplitudes_ofReal (x : Fin 4 → ℝ) :
    complexAmplitudes (fun i => (x i : ℂ)) =
      amplitudeEmbedding (amplitudeValues (point x)) := by
  funext j
  obtain ⟨i,rfl⟩ := index.surjective j
  change (x (index.symm (index i)) : ℂ) = (amplitudeValues (point x) (index i) : ℂ)
  rw [index.symm_apply_apply,point_coordinates]

private lemma complex_point_rename (t : ℂ) (a : Fin 4 → ℂ) :
    FMSA.Convergence.ComplexPolynomialSystem.point (t,complexAmplitudes a) ∘ Option.map index =
      FMSA.Convergence.ComplexPolynomialSystem.point (t,a) := by
  funext j
  cases j with
  | none => rfl
  | some j =>
    change a (index.symm (index j)) = a j
    rw [index.symm_apply_apply]

/-- EXACT ORIGINAL complex BH residual at every complex coupling/amplitude. -/
theorem complex_residual_dictionary (t : ℂ) (a : Fin 4 → ℂ) (i : Fin 4) :
    FMSA.Convergence.ActualComplexBH.complexBHResidual z rho sigma strengths
      (t,complexAmplitudes a) (index i) = complexResidual polynomial (t,a) i := by
  change MvPolynomial.eval₂Hom Complex.ofRealHom
    (FMSA.Convergence.ComplexPolynomialSystem.point (t,complexAmplitudes a))
      (residualPoly z rho sigma strengths (index i)) =
    MvPolynomial.eval₂Hom Complex.ofRealHom
      (FMSA.Convergence.ComplexPolynomialSystem.point (t,a)) (polynomial i)
  rw [← polynomial_actual_identity,MvPolynomial.eval₂Hom_rename,complex_point_rename]

/-- Complex zeros are equivalent to literal ORIGINAL complex BH roots;
no complex germ, real-slice restriction or numerical premise is supplied. -/
theorem complex_root_iff (t : ℂ) (a : Fin 4 → ℂ) :
    FMSA.Convergence.ActualComplexBH.complexBHResidual z rho sigma strengths
      (t,complexAmplitudes a) = 0 ↔ complexResidual polynomial (t,a) = 0 := by
  constructor
  · intro h
    funext i
    change complexResidual polynomial (t,a) i = 0
    rw [← complex_residual_dictionary]
    exact congrFun h (index i)
  · intro h
    funext j
    obtain ⟨i,rfl⟩ := index.surjective j
    change FMSA.Convergence.ActualComplexBH.complexBHResidual z rho sigma strengths
      (t,complexAmplitudes a) (index i) = 0
    rw [complex_residual_dictionary]
    exact congrFun h i

/-- The ORIGINAL true complex Jacobian is the literal model Jacobian,
with the exact proved row/column ordering at ALL complex points. -/
theorem complex_jacobian_dictionary (t : ℂ) (a : Fin 4 → ℂ) (i j : Fin 4) :
    complexJacobian (residualPoly z rho sigma strengths) (t,complexAmplitudes a)
      (index i) (index j) = complexJacobian polynomial (t,a) i j := by
  change MvPolynomial.eval₂Hom Complex.ofRealHom
    (FMSA.Convergence.ComplexPolynomialSystem.point (t,complexAmplitudes a))
      (MvPolynomial.pderiv (some (index j)) (residualPoly z rho sigma strengths (index i))) =
    MvPolynomial.eval₂Hom Complex.ofRealHom
      (FMSA.Convergence.ComplexPolynomialSystem.point (t,a))
      (MvPolynomial.pderiv (some j) (polynomial i))
  rw [← polynomial_actual_identity]
  have hf : Function.Injective (Option.map index) := (Equiv.optionCongr index).injective
  have hd : MvPolynomial.pderiv (some (index j))
      (MvPolynomial.rename (Option.map index) (polynomial i)) =
      MvPolynomial.rename (Option.map index) (MvPolynomial.pderiv (some j) (polynomial i)) := by
    simpa only [Option.map_some] using MvPolynomial.pderiv_rename hf (some j) (polynomial i)
  rw [hd,MvPolynomial.eval₂Hom_rename,complex_point_rename]

/-- Original and model complex determinants are IDENTICAL; no scaling,
conjugation, nonzero-factor premise or regularity is inserted. -/
theorem complex_jacobian_det_dictionary (t : ℂ) (a : Fin 4 → ℂ) :
    (complexJacobian (residualPoly z rho sigma strengths) (t,complexAmplitudes a)).det =
      (complexJacobian polynomial (t,a)).det := by
  classical
  have hm : (complexJacobian (residualPoly z rho sigma strengths)
      (t,complexAmplitudes a)).submatrix index index = complexJacobian polynomial (t,a) := by
    ext i j
    exact complex_jacobian_dictionary t a i j
  rw [← hm,Matrix.det_submatrix_equiv_self]

/-- info: 'FMSA.Convergence.M3ResidualModel.point_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.point_coordinates
/-- info: 'FMSA.Convergence.M3ResidualModel.point_coordinates_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.point_coordinates_inverse
/-- info: 'FMSA.Convergence.M3ResidualModel.eta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.eta_eq
/-- info: 'FMSA.Convergence.M3ResidualModel.vacancy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.vacancy_eq
/-- info: 'FMSA.Convergence.M3ResidualModel.physical_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.physical_data
/-- info: 'FMSA.Convergence.M3ResidualModel.hs_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.hs_coefficients
/-- info: 'FMSA.Convergence.M3ResidualModel.eta_lt_four_fifths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.eta_lt_four_fifths
/-- info: 'FMSA.Convergence.M3ResidualModel.actual_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.actual_formula
/-- info: 'FMSA.Convergence.M3ResidualModel.actual_root_iff_formula_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.actual_root_iff_formula_zero
/-- info: 'FMSA.Convergence.M3ResidualModel.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.polynomial_eval
/-- info: 'FMSA.Convergence.M3ResidualModel.polynomial_actual_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.polynomial_actual_identity
/-- info: 'FMSA.Convergence.M3ResidualModel.complex_amplitudes_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.complex_amplitudes_ofReal
/-- info: 'FMSA.Convergence.M3ResidualModel.complex_residual_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.complex_residual_dictionary
/-- info: 'FMSA.Convergence.M3ResidualModel.complex_root_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.complex_root_iff
/-- info: 'FMSA.Convergence.M3ResidualModel.complex_jacobian_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.complex_jacobian_dictionary
/-- info: 'FMSA.Convergence.M3ResidualModel.complex_jacobian_det_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3ResidualModel.complex_jacobian_det_dictionary
end FMSA.Convergence.M3ResidualModel
