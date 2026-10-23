import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearRadialOZ

/-! Both finite nonlinear admissibility certificates hold automatically at the
actual unequal-diameter PY hard-sphere starting point, at arbitrary density.
This proves a starting point, not persistence along a nonzero-coupling branch. -/
noncomputable section
open Real Polynomial FMSA.MatrixQ0 MSAMixture FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def hsAdmissibilityJ {R : Type*} [CommRing R] (a c x y s : R) : R :=
  2*a*(1+c*y)+a*(y+x*(1+c*y))*s
def hsAdmissibilityL {R : Type*} [CommRing R] (a c x y s : R) : R :=
  2*a*(1+c*y)+a*(y-x*(1+c*y))*s-a*x*y*s^2

theorem hsAdmissibility_cross_products {R : Type*} [CommRing R] (a c x y t s : R) :
    (hsAdmissibilityJ a c t x s*hsAdmissibilityL a c t y s-
      hsAdmissibilityL a c t x s*hsAdmissibilityJ a c t y s = a^2*s^3*t^2*(x-y)) ∧
    (hsAdmissibilityJ a c x t (-s)*hsAdmissibilityJ a c y t s-
      hsAdmissibilityL a c x t s*hsAdmissibilityL a c y t (-s) =
        -a^2*s^3*t^2*(s*x*y+x-y)) ∧
    (hsAdmissibilityJ a c x t s*hsAdmissibilityL a c y t (-s)-
      hsAdmissibilityL a c x t (-s)*hsAdmissibilityJ a c y t s = a^2*s^3*t^2*(x-y)) := by
  unfold hsAdmissibilityJ hsAdmissibilityL
  constructor
  · ring
  constructor <;> ring

theorem hsAdmissibility_linear_products {R : Type*} [CommRing R] (a c x y s : R) :
    hsAdmissibilityJ a c x y s-hsAdmissibilityJ a c y x s = -2*a*c*(x-y) ∧
    -hsAdmissibilityL a c x y s+hsAdmissibilityL a c y x (-s) =
      2*a*c*(s*x*y+x-y) := by
  unfold hsAdmissibilityJ hsAdmissibilityL
  constructor <;> ring

omit [DecidableEq ι] in
theorem nonlinearHS_lower_value (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G : TailMatrix ι N) (i j : Fin N) :
    nonlinearLowerQValue z ρ σ 0 G i j = -(π/vacMix ρ σ)*σ i*σ j := by
  simp [nonlinearLowerQValue, W, C, Wt, Ct, Q0phys, Qppphys]
  ring

theorem nonlinearHS_numerator_dictionary (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G : TailMatrix ι N) (i j : Fin N) :
    nonlinearJNumerator z ρ σ 0 G i j =
      hsAdmissibilityJ (Polynomial.C (π/vacMix ρ σ))
        (Polynomial.C (π*xi2 ρ σ/(2*vacMix ρ σ)))
        (Polynomial.C (σ i)) (Polynomial.C (σ j)) X*nonlinearRatePolynomial z ∧
    nonlinearLNumerator z ρ σ 0 G i j =
      hsAdmissibilityL (Polynomial.C (π/vacMix ρ σ))
        (Polynomial.C (π*xi2 ρ σ/(2*vacMix ρ σ)))
        (Polynomial.C (σ i)) (Polynomial.C (σ j)) X*nonlinearRatePolynomial z := by
  simp only [nonlinearJNumerator, nonlinearLNumerator, amplitudeA_zero, amplitudeQp_zero,
    nonlinearHS_lower_value]
  have hw : ∀ u i j, W z ρ 0 G u i j=0 := by intros; simp [W, Wt]
  have hc : ∀ u i j, C z ρ σ 0 G u i j=0 := by intros; simp [C, Ct]
  simp only [hw, hc, mul_zero, Polynomial.C_0, zero_mul, Finset.sum_const_zero,
    add_zero, sub_zero]
  have ha : Qppphys ρ σ j j =
      2*(π/vacMix ρ σ)*(1+(π*xi2 ρ σ/(2*vacMix ρ σ))*σ j) := by
    unfold Qppphys; ring
  have hq : Q0phys ρ σ i j = (π/vacMix ρ σ)*
      (σ j+σ i*(1+(π*xi2 ρ σ/(2*vacMix ρ σ))*σ j)) := by
    unfold Q0phys; ring
  rw [ha, hq]
  simp only [hsAdmissibilityJ, hsAdmissibilityL, map_mul, map_add, map_sub, map_neg,
    Polynomial.C_ofNat, Polynomial.C_1]
  constructor <;> first | trivial | ring

theorem hsAdmissibility_moment_relation (ρ σ : Fin N → ℝ) :
    Polynomial.C (π/vacMix ρ σ)*(∑ m, Polynomial.C (ρ m)*(Polynomial.C (σ m))^2) =
      2*Polynomial.C (π*xi2 ρ σ/(2*vacMix ρ σ)) := by
  have hm : (∑ m, Polynomial.C (ρ m)*(Polynomial.C (σ m))^2)=
      Polynomial.C (xi2 ρ σ) := by simp [xi2, map_sum, map_mul, map_pow]
  rw [hm, ← map_mul]
  rw [show (2 : Polynomial ℝ)=Polynomial.C (2 : ℝ) by rfl, ← map_mul]
  congr 1
  ring

theorem hsAdmissibility_finite_residuals {R : Type*} [CommRing R]
    (a c s : R) (d x : Fin N → R)
    (h : a*(∑ m, d m*(x m)^2)=2*c) (i j : Fin N) :
    ((hsAdmissibilityJ a c (x i) (x j) s-hsAdmissibilityJ a c (x j) (x i) s)*s^3+
      ∑ m, d m*(hsAdmissibilityJ a c (x m) (x i) s*hsAdmissibilityL a c (x m) (x j) s-
        hsAdmissibilityL a c (x m) (x i) s*hsAdmissibilityJ a c (x m) (x j) s)=0) ∧
    ((-hsAdmissibilityL a c (x i) (x j) s+hsAdmissibilityL a c (x j) (x i) (-s))*s^3+
      ∑ m, d m*(hsAdmissibilityJ a c (x i) (x m) (-s)*hsAdmissibilityJ a c (x j) (x m) s-
        hsAdmissibilityL a c (x i) (x m) s*hsAdmissibilityL a c (x j) (x m) (-s))=0) ∧
    ((hsAdmissibilityJ a c (x i) (x j) s-hsAdmissibilityJ a c (x j) (x i) s)*s^3+
      ∑ m, d m*(hsAdmissibilityJ a c (x i) (x m) s*hsAdmissibilityL a c (x j) (x m) (-s)-
        hsAdmissibilityL a c (x i) (x m) (-s)*hsAdmissibilityJ a c (x j) (x m) s)=0) := by
  have hr (m : Fin N) := hsAdmissibility_cross_products a c (x i) (x j) (x m) s
  have hl := hsAdmissibility_linear_products a c (x i) (x j) s
  simp only [hl.1, hl.2, (hr _).1, (hr _).2.1, (hr _).2.2]
  have sumR : (∑ m, d m*(a^2*s^3*(x m)^2*(x i-x j))) =
      a^2*s^3*(x i-x j)*(∑ m, d m*(x m)^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
  have sumU : (∑ m, d m*(-a^2*s^3*(x m)^2*(s*x i*x j+x i-x j))) =
      -a^2*s^3*(s*x i*x j+x i-x j)*(∑ m, d m*(x m)^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
  rw [sumR, sumU]
  constructor
  · linear_combination a*s^3*(x i-x j)*h
  constructor
  · linear_combination -a*s^3*(s*x i*x j+x i-x j)*h
  · linear_combination a*s^3*(x i-x j)*h

theorem nonlinearHS_admissibility_polynomials_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G : TailMatrix ι N) (i j : Fin N) :
    nonlinearReciprocityPolynomial z ρ σ 0 G i j=0 ∧
    nonlinearWronskianUPolynomial z ρ σ 0 G i j=0 ∧
    nonlinearWronskianVPolynomial z ρ σ 0 G i j=0 := by
  let a := Polynomial.C (π/vacMix ρ σ)
  let c := Polynomial.C (π*xi2 ρ σ/(2*vacMix ρ σ))
  let x : Fin N → Polynomial ℝ := fun i => Polynomial.C (σ i)
  let d : Fin N → Polynomial ℝ := fun i => Polynomial.C (ρ i)
  let J := fun i j s => hsAdmissibilityJ a c (x i) (x j) s
  let L := fun i j s => hsAdmissibilityL a c (x i) (x j) s
  let P := nonlinearRatePolynomial z
  let M := P.comp (-X)
  have hd := nonlinearHS_numerator_dictionary z ρ σ G
  have hj (i j : Fin N) : nonlinearJNumerator z ρ σ 0 G i j=J i j X*P := (hd i j).1
  have hl (i j : Fin N) : nonlinearLNumerator z ρ σ 0 G i j=L i j X*P := (hd i j).2
  have hjm (i j : Fin N) : (nonlinearJNumerator z ρ σ 0 G i j).comp (-X)=J i j (-X)*M := by
    rw [hj]; simp [J, a, c, x, hsAdmissibilityJ, M, Polynomial.mul_comp, Polynomial.add_comp]
  have hlm (i j : Fin N) : (nonlinearLNumerator z ρ σ 0 G i j).comp (-X)=L i j (-X)*M := by
    rw [hl]; simp [L, a, c, x, hsAdmissibilityL, M, Polynomial.mul_comp, Polynomial.add_comp,
      Polynomial.sub_comp, Polynomial.pow_comp]
  have hD : (nonlinearRationalDenominator z).comp (-X)=X^2*M := by
    simp [nonlinearRationalDenominator, M, P, Polynomial.mul_comp, Polynomial.pow_comp]
  have hr := hsAdmissibility_finite_residuals a c X d x (hsAdmissibility_moment_relation ρ σ) i j
  change ((J i j X-J j i X)*X^3+∑ m, d m*(J m i X*L m j X-L m i X*J m j X)=0) ∧
    ((-L i j X+L j i (-X))*X^3+∑ m, d m*(J i m (-X)*J j m X-L i m X*L j m (-X))=0) ∧
    ((J i j X-J j i X)*X^3+∑ m, d m*(J i m X*L j m (-X)-L i m (-X)*J j m X)=0) at hr
  simp only [nonlinearReciprocityPolynomial, nonlinearWronskianUPolynomial,
    nonlinearWronskianVPolynomial]
  simp only [hjm, hlm, hD]
  simp only [hj, hl, nonlinearRationalDenominator]
  change ((J i j X*P-J j i X*P)*X*(X^2*P)+
      ∑ m, d m*(J m i X*P*(L m j X*P)-L m i X*P*(J m j X*P))=0) ∧
    (-(L i j X*P)*X*(X^2*M)+L j i (-X)*M*X*(X^2*P)+
      ∑ m, d m*(J i m (-X)*M*(J j m X*P)-L i m X*P*(L j m (-X)*M))=0) ∧
    ((J i j X*P-J j i X*P)*X*(X^2*M)+
      ∑ m, d m*(J i m X*P*(L j m (-X)*M)-L i m (-X)*M*(J j m X*P))=0)
  have sr : (∑ m, d m*(J m i X*P*(L m j X*P)-L m i X*P*(J m j X*P)))=
      (∑ m, d m*(J m i X*L m j X-L m i X*J m j X))*P^2 := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; ring
  have su : (∑ m, d m*(J i m (-X)*M*(J j m X*P)-L i m X*P*(L j m (-X)*M)))=
      (∑ m, d m*(J i m (-X)*J j m X-L i m X*L j m (-X)))*(P*M) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; ring
  have sv : (∑ m, d m*(J i m X*P*(L j m (-X)*M)-L i m (-X)*M*(J j m X*P)))=
      (∑ m, d m*(J i m X*L j m (-X)-L i m (-X)*J j m X))*(P*M) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; ring
  rw [sr, su, sv]
  constructor
  · linear_combination P^2*hr.1
  constructor
  · linear_combination P*M*hr.2.1
  · linear_combination P*M*hr.2.2

theorem nonlinearHS_automatic_finite_certificates (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G : TailMatrix ι N) :
    NonlinearFiniteReciprocityCertificate z ρ σ 0 G ∧
    NonlinearFiniteWronskianCertificate z ρ σ 0 G := by
  have h := nonlinearHS_admissibility_polynomials_zero z ρ σ G
  constructor
  · intro i j n _; rw [(h i j).1, Polynomial.coeff_zero]
  constructor
  · intro i j n _; rw [(h i j).2.1, Polynomial.coeff_zero]
  · intro i j n _; rw [(h i j).2.2, Polynomial.coeff_zero]

omit [DecidableEq ι] in
theorem nonlinear_zero_coupling_Dt_eq_zero_of_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ 0 Dt G) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδz : ∀ u, δ < z u) (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) : Dt=0 := by
  funext u i j
  have hu := nonlinear_firstBlock_isUnit_of_weighted_budget z ρ σ Dt G hz hσ δ hδ hδz hb u
  have he : Matrix.of (Dt u)*Matrix.of (firstBlock z ρ σ Dt G u)=0 := by
    ext a b
    simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply, firstBlock,
      firstLHS, Pi.zero_apply, mul_zero, zero_div] using hroot.1 u a b
  have hd : Matrix.of (Dt u)=0 := hu.mul_left_injective (by simpa using he)
  exact congrFun (congrFun hd i) j

/-- Every zero-coupling root in the actual budget domain passes both checks;
the seed need not have been selected externally. This is not a nonzero-tau
branch theorem. -/
theorem nonlinear_zero_coupling_root_automatic_finite_certificates
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ 0 Dt G) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδz : ∀ u, δ < z u) (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) :
    NonlinearFiniteReciprocityCertificate z ρ σ Dt G ∧
    NonlinearFiniteWronskianCertificate z ρ σ Dt G := by
  rw [nonlinear_zero_coupling_Dt_eq_zero_of_budget z ρ σ Dt G hz hσ hroot δ hδ hδz hb]
  exact nonlinearHS_automatic_finite_certificates z ρ σ G

omit [DecidableEq ι] in
theorem nonlinearHS_base_actual_root (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    IsRoot z ρ σ 0 0 (baseSeed z ρ σ) := by
  have hr := (residual_eq_zero_iff z ρ σ 0 0 (baseSeed z ρ σ) 0).mp
    (residual_base z ρ σ 0 (baseSecond_isUnit_det z ρ σ hz hv hρ hσ))
  simpa using hr

/-- Actual positive-density unequal-diameter HS instance of the nonlinear
joint certificate. The root and both finite checks are discharged internally;
only the explicit sufficient integral decay budget remains. -/
theorem nonlinearHS_actual_joint_certificate (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ 0 (baseSeed z ρ σ) δ < 1) :
    (∀ i j r, r < edgeHi σ i j → nonlinearG z ρ σ 0 (baseSeed z ρ σ) i j r=0) ∧
    (∀ i j, MeasureTheory.Integrable (fun r => r*nonlinearH z ρ σ 0 (baseSeed z ρ σ) i j r)) ∧
    (∀ u i j, (∫ r in Set.Ioi (0 : ℝ), exp (-z u*r)*(r*nonlinearG z ρ σ 0 (baseSeed z ρ σ) i j r))=
      exp (-z u*edgeHi σ i j)*baseSeed z ρ σ u i j) ∧
    (∀ i j r, 0 < r → nonlinearG z ρ σ 0 (baseSeed z ρ σ) i j r=
      nonlinearG z ρ σ 0 (baseSeed z ρ σ) j i r) ∧
    (∀ i j, nonlinearH z ρ σ 0 (baseSeed z ρ σ) i j =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] fun r =>
      orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j r+
        radialMixtureConv (orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ))
          (nonlinearH z ρ σ 0 (baseSeed z ρ σ)) ρ i j r) := by
  have hc := nonlinearHS_automatic_finite_certificates z ρ σ (baseSeed z ρ σ)
  exact nonlinearMixtureRDF_finite_admissibility_certificate z ρ σ 0 0 (baseSeed z ρ σ)
    hz hσ hv.ne' (nonlinearHS_base_actual_root z ρ σ hz hv hρ hσ)
    (by intros; rfl) δ hδ hδz hb hc.1 hc.2

end FMSA.ExactMSA.MultiTailMixture
