import MSAConvergence.MixtureFrequencyGridCoverage

/-! Quantitative perturbation of an actual mixture Fourier sample across
a coupling slab. A single center inverse and one uniform matrix-change
bound control every root candidate in the slab. -/
noncomputable section
open Real MeasureTheory
namespace FMSA.Convergence.MixtureCouplingSlabCertificate
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.MixtureAxisFrequencyGrid
open FMSA.Convergence.MixtureMomentCoefficientBudget
open FMSA.Convergence.MixtureFrequencyGridCoverage
open FMSA.Convergence.MixtureSampleInverseCertificate
open FMSA.Convergence.MixtureAxisHighFrequency
open FMSA.Convergence.MixtureCoefficientBudget
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper FMSA.MatrixQ0 FMSA.Paper.StableIntervalRadius
open MSAMixture
variable {N : ℕ} {T : Type*} [Fintype T]

/-- A base finite-matrix inverse and a half-size perturbation certify both
invertibility and an explicit inverse entry-norm bound at the new matrix. -/
theorem inverse_bound_of_half_perturbation
    (Q P : Matrix (Fin N) (Fin N) ℂ) (C D : ℝ)
    (hbase : IsUnit (1-Q))
    (hC : complexNormSum ((1-Q)⁻¹) ≤ C)
    (hD : complexNormSum (P-Q) ≤ D)
    (hhalf : C*D ≤ 1/2) :
    IsUnit (1-P) ∧ complexNormSum ((1-P)⁻¹) ≤ 2*(N : ℝ)*C := by
  let E := (1-Q)⁻¹*(P-Q)
  have hE : complexNormSum E ≤ 1/2 := by
    calc
      complexNormSum E ≤ complexNormSum ((1-Q)⁻¹)*complexNormSum (P-Q) :=
        complexNormSum_mul_le _ _
      _ ≤ C*D := mul_le_mul hC hD (complexNormSum_nonneg _) (by
        exact (complexNormSum_nonneg _).trans hC)
      _ ≤ 1/2 := hhalf
  obtain ⟨huE,hInvE⟩ := one_sub_inverse_normSum_bound E hE
  have hprod : (1-Q)*(1-E) = 1-P := by
    dsimp [E]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hbase),
      Matrix.one_mul]
    noncomm_ring
  have hunit : IsUnit (1-P) := by
    rw [← hprod]
    exact hbase.mul huE
  have hinv : (1-P)⁻¹ = (1-E)⁻¹*(1-Q)⁻¹ := by
    rw [← hprod,Matrix.mul_inv_rev]
  refine ⟨hunit,?_⟩
  rw [hinv]
  calc
    complexNormSum ((1-E)⁻¹*(1-Q)⁻¹) ≤
        complexNormSum ((1-E)⁻¹)*complexNormSum ((1-Q)⁻¹) :=
      complexNormSum_mul_le _ _
    _ ≤ (2*(N : ℝ))*C :=
      mul_le_mul hInvE hC (complexNormSum_nonneg _) (by positivity)

/-- A center actual Fourier factor controls every factor whose density-
weighted Fourier matrix lies in a certified complex matrix-norm slab. -/
theorem actual_factor_sample_slab_inverse_bound
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (A0 A : Fin N → ℝ) (qp0 qp : Fin N → Fin N → ℝ)
    (W0 C0 W C : TailMatrix T N) (a : ℝ) (Cbase D : ℝ)
    (hbase : (fourierFactor z rho sigma A0 qp0 W0 C0 a).det ≠ 0)
    (hC : complexNormSum ((fourierFactor z rho sigma A0 qp0 W0 C0 a)⁻¹) ≤ Cbase)
    (hD : complexNormSum
      (weightedFourierQ z rho sigma A qp W C a -
        weightedFourierQ z rho sigma A0 qp0 W0 C0 a) ≤ D)
    (hhalf : Cbase*D ≤ 1/2) :
    (fourierFactor z rho sigma A qp W C a).det ≠ 0 ∧
      complexNormSum ((fourierFactor z rho sigma A qp W C a)⁻¹) ≤
        2*(N : ℝ)*Cbase := by
  let Q := weightedFourierQ z rho sigma A0 qp0 W0 C0 a
  let P := weightedFourierQ z rho sigma A qp W C a
  have hbaseUnit : IsUnit (1-Q) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hbase)
  obtain ⟨hunit,hinv⟩ := inverse_bound_of_half_perturbation Q P Cbase D
    hbaseUnit hC hD hhalf
  exact ⟨isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit),hinv⟩

/-- The actual full-line Baxter kernel is exactly linear in its four BH
coefficient families at fixed rates and diameters. -/
theorem actual_q_sub_eq_q_of_coefficient_differences
    (z : T → ℝ) (sigma A₁ A₀ : Fin N → ℝ)
    (qp₁ qp₀ : Fin N → Fin N → ℝ)
    (W₁ C₁ W₀ C₀ : TailMatrix T N) (i j : Fin N) (r : ℝ) :
    q z sigma A₁ qp₁ W₁ C₁ i j r - q z sigma A₀ qp₀ W₀ C₀ i j r =
      q z sigma (fun j => A₁ j-A₀ j) (fun i j => qp₁ i j-qp₀ i j)
        (fun u i j => W₁ u i j-W₀ u i j)
        (fun u i j => C₁ u i j-C₀ u i j) i j r := by
  unfold q
  by_cases hlo : r < edgeLo sigma i j
  · simp [hlo]
  · simp only [if_neg hlo]
    by_cases hhi : r ≤ edgeHi sigma i j
    · simp only [if_pos hhi]
      have hsum :
          (∑ u, (W₁ u i j * exp (-z u*(r-edgeLo sigma i j)) + C₁ u i j)) -
          (∑ u, (W₀ u i j * exp (-z u*(r-edgeLo sigma i j)) + C₀ u i j)) =
          ∑ u, ((W₁ u i j-W₀ u i j)*exp (-z u*(r-edgeLo sigma i j)) +
            (C₁ u i j-C₀ u i j)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring
      rw [← hsum]
      ring
    · simp only [if_neg hhi]
      have hsum :
          (∑ u, (W₁ u i j * exp (-z u*(r-edgeLo sigma i j)) +
            C₁ u i j * exp (-z u*(r-edgeHi sigma i j)))) -
          (∑ u, (W₀ u i j * exp (-z u*(r-edgeLo sigma i j)) +
            C₀ u i j * exp (-z u*(r-edgeHi sigma i j)))) =
          ∑ u, ((W₁ u i j-W₀ u i j)*exp (-z u*(r-edgeLo sigma i j)) +
            (C₁ u i j-C₀ u i j)*exp (-z u*(r-edgeHi sigma i j))) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring
      exact hsum

def referenceMass (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (i j : Fin N) : ℝ :=
  ∫ r : ℝ, |referenceQ z sigma Abar Qbar Wbar Cbar i j r|

def transformMassUpper (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (δ : ℝ) (i j : Fin N) : ℝ :=
  exp (-δ*edgeLo sigma i j) *
    Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j

theorem referenceMass_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (i j : Fin N) :
    Integrable (fun r : ℝ => |referenceQ z sigma Abar Qbar Wbar Cbar i j r|) := by
  have hh := actual_q_rate_integrable z sigma Abar (fun i j => -Qbar i j)
    Wbar Cbar hσ 0 (fun u => by simpa using hz u) i j
  have hq : Integrable (fun r : ℝ =>
      (referenceQ z sigma Abar Qbar Wbar Cbar i j r : ℂ)) := by
    simpa only [referenceQ,zero_mul,neg_zero,Complex.exp_zero,mul_one] using hh
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hq.norm

/-- The fixed reference L1 mass is bounded by a finite real transform
evaluation at any strictly admissible negative Laplace parameter. -/
theorem referenceMass_le_transformMassUpper
    (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (hσ : ∀ i, 0 ≤ sigma i)
    (hA : ∀ j, 0 ≤ Abar j) (hQ : ∀ i j, 0 ≤ Qbar i j)
    (hW : ∀ u i j, 0 ≤ Wbar u i j)
    (hC : ∀ u i j, 0 ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (i j : Fin N) :
    referenceMass z sigma Abar Qbar Wbar Cbar i j ≤
      transformMassUpper z sigma Abar Qbar Wbar Cbar δ i j := by
  let qref : ℝ → ℝ := referenceQ z sigma Abar Qbar Wbar Cbar i j
  have hqpos (r : ℝ) : 0 ≤ qref r :=
    referenceQ_nonneg z sigma Abar Qbar Wbar Cbar hA hQ hW hC i j r
  have hqzero (r : ℝ) (hr : r < edgeLo sigma i j) : qref r = 0 := by
    simp [qref,referenceQ,q,hr]
  have hraw : Integrable (fun r : ℝ => |qref r|) :=
    referenceMass_integrable z (fun u => lt_trans hδ (hrate u))
      sigma Abar Qbar Wbar Cbar hσ i j
  have hweightComplex : Integrable (fun r : ℝ => (qref r : ℂ) *
      Complex.exp (((δ : ℝ) : ℂ) * r)) := by
    simpa only [qref,referenceQ,neg_neg] using
      actual_q_rate_integrable z sigma Abar (fun i j => -Qbar i j)
        Wbar Cbar hσ (-δ : ℂ)
        (fun u => by simp only [Complex.neg_re,Complex.ofReal_re]; linarith [hrate u]) i j
  have hweightReal : Integrable (fun r : ℝ => qref r * exp (δ*r)) := by
    have hcast : Integrable (fun r : ℝ => ((qref r * exp (δ*r) : ℝ) : ℂ)) := by
      convert hweightComplex using 1
      funext r
      simp [Complex.ofReal_exp]
    simpa [Complex.exp_re,Complex.mul_re] using hcast.re
  have hdom : Integrable (fun r : ℝ => exp (-δ*edgeLo sigma i j) *
      (qref r*exp (δ*r))) := hweightReal.const_mul _
  have hpoint (r : ℝ) : |qref r| ≤
      exp (-δ*edgeLo sigma i j) * (qref r*exp (δ*r)) := by
    by_cases hr : r < edgeLo sigma i j
    · simp [hqzero r hr]
    · have ht : 0 ≤ r-edgeLo sigma i j := by linarith
      have hbase : 1 ≤ exp (δ*(r-edgeLo sigma i j)) := by
        linarith [Real.add_one_le_exp (δ*(r-edgeLo sigma i j)),mul_nonneg hδ.le ht]
      have he : exp (δ*(r-edgeLo sigma i j)) =
          exp (-δ*edgeLo sigma i j)*exp (δ*r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [abs_of_nonneg (hqpos r)]
      have hh := mul_le_mul_of_nonneg_right hbase (hqpos r)
      calc
        qref r ≤ exp (δ*(r-edgeLo sigma i j))*qref r := by
          simpa only [one_mul] using hh
        _ = exp (-δ*edgeLo sigma i j) * (qref r*exp (δ*r)) := by
          rw [he]
          ring
  have hint : (∫ r : ℝ, |qref r|) ≤
      ∫ r : ℝ, exp (-δ*edgeLo sigma i j) * (qref r*exp (δ*r)) :=
    integral_mono hraw hdom hpoint
  have htransform : (∫ r : ℝ, qref r*exp (δ*r)) =
      Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j := by
    have hcomplex := FMSA.Convergence.CanonicalKernelEstimates.full_q_integral_rate_domain
      z sigma Abar (fun i j => -Qbar i j) Wbar Cbar hσ (-δ : ℂ)
      (by simp [ne_of_gt hδ])
      (fun u => by simp only [Complex.neg_re,Complex.ofReal_re]; linarith [hrate u]) i j
    have hqeq : QhatComplex z sigma Abar (fun i j => -Qbar i j)
        Wbar Cbar (-δ : ℂ) i j =
        (Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j : ℂ) := by
      simpa only [Complex.ofReal_neg] using
        (QhatComplex_ofReal z sigma Abar (fun i j => -Qbar i j)
          Wbar Cbar (-δ) i j)
    rw [hqeq] at hcomplex
    have hcast : ((∫ r : ℝ, qref r*exp (δ*r) : ℝ) : ℂ) =
        (Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j : ℂ) := by
      rw [← integral_complex_ofReal]
      calc
        (∫ r : ℝ, ((qref r*exp (δ*r) : ℝ) : ℂ)) =
            ∫ r : ℝ, (q z sigma Abar (fun i j => -Qbar i j) Wbar Cbar i j r : ℂ) *
              Complex.exp (-(-δ : ℂ)*r) := by
          apply integral_congr_ae
          filter_upwards [] with r
          simp [qref,referenceQ,Complex.ofReal_exp]
        _ = _ := hcomplex
    exact Complex.ofReal_injective hcast
  unfold referenceMass transformMassUpper
  change (∫ r : ℝ, |qref r|) ≤ _
  simpa only [integral_const_mul,htransform] using hint

/-- Entrywise Fourier change at a fixed sample is bounded by the fixed
reference L1 mass of four coefficient-difference caps. -/
theorem fourierQ_difference_le_referenceMass
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A₁ A₀ : Fin N → ℝ)
    (qp₁ qp₀ : Fin N → Fin N → ℝ)
    (W₁ C₁ W₀ C₀ : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, |A₁ j-A₀ j| ≤ Abar j)
    (hQ : ∀ i j, |qp₁ i j-qp₀ i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W₁ u i j-W₀ u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C₁ u i j-C₀ u i j| ≤ Cbar u i j)
    (a : ℝ) (i j : Fin N) :
    ‖fourierQ z sigma A₁ qp₁ W₁ C₁ a i j -
      fourierQ z sigma A₀ qp₀ W₀ C₀ a i j‖ ≤
      referenceMass z sigma Abar Qbar Wbar Cbar i j := by
  let f₁ : ℝ → ℂ := fun r => (q z sigma A₁ qp₁ W₁ C₁ i j r : ℂ) *
    Complex.exp (-(Complex.I*(a : ℂ))*r)
  let f₀ : ℝ → ℂ := fun r => (q z sigma A₀ qp₀ W₀ C₀ i j r : ℂ) *
    Complex.exp (-(Complex.I*(a : ℂ))*r)
  have h₁ : Integrable f₁ := by
    simpa only [f₁] using q_complex_weighted_integrable z hz sigma A₁ qp₁ W₁ C₁
      hσ (Complex.I*(a : ℂ)) (by simp) i j
  have h₀ : Integrable f₀ := by
    simpa only [f₀] using q_complex_weighted_integrable z hz sigma A₀ qp₀ W₀ C₀
      hσ (Complex.I*(a : ℂ)) (by simp) i j
  have href := referenceMass_integrable z hz sigma Abar Qbar Wbar Cbar hσ i j
  have hpoint (r : ℝ) : ‖f₁ r-f₀ r‖ ≤
      |referenceQ z sigma Abar Qbar Wbar Cbar i j r| := by
    have hlin := actual_q_sub_eq_q_of_coefficient_differences z sigma
      A₁ A₀ qp₁ qp₀ W₁ C₁ W₀ C₀ i j r
    have hcap := actual_q_abs_le_reference_q z sigma
      (fun j => A₁ j-A₀ j) (fun i j => qp₁ i j-qp₀ i j)
      (fun u i j => W₁ u i j-W₀ u i j)
      (fun u i j => C₁ u i j-C₀ u i j)
      Abar Qbar Wbar Cbar hA hQ hW hC i j r
    change ‖(q z sigma A₁ qp₁ W₁ C₁ i j r : ℂ) *
        Complex.exp (-(Complex.I*(a : ℂ))*r) -
        (q z sigma A₀ qp₀ W₀ C₀ i j r : ℂ) *
        Complex.exp (-(Complex.I*(a : ℂ))*r)‖ ≤ _
    rw [← sub_mul,norm_mul]
    have he : ‖Complex.exp (-(Complex.I*(a : ℂ))*r)‖ = 1 := by
      simp [Complex.norm_exp,Complex.mul_re]
    rw [he,mul_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,hlin]
    exact hcap.trans (le_abs_self _)
  unfold fourierQ
  change ‖(∫ r, f₁ r)-(∫ r, f₀ r)‖ ≤ _
  rw [← integral_sub h₁ h₀]
  calc
    ‖∫ r, f₁ r-f₀ r‖ ≤ ∫ r, ‖f₁ r-f₀ r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r, |referenceQ z sigma Abar Qbar Wbar Cbar i j r| :=
      integral_mono (h₁.sub h₀).norm href hpoint
    _ = referenceMass z sigma Abar Qbar Wbar Cbar i j := rfl

def referenceMatrixMassBudget (z : T → ℝ) (rho sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N) : ℝ :=
  ∑ i, ∑ j, |sqrt (rho i)| * |sqrt (rho j)| *
    referenceMass z sigma Abar Qbar Wbar Cbar i j

def transformMatrixMassBudget (z : T → ℝ) (rho sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (δ : ℝ) : ℝ :=
  ∑ i, ∑ j, |sqrt (rho i)| * |sqrt (rho j)| *
    transformMassUpper z sigma Abar Qbar Wbar Cbar δ i j

/-- The actual fixed L1 matrix budget is bounded by an explicit finite
real rational-exponential expression in coefficient-difference caps. -/
theorem referenceMatrixMassBudget_le_transformMatrixMassBudget
    (z : T → ℝ) (rho sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (hσ : ∀ i, 0 ≤ sigma i)
    (hA : ∀ j, 0 ≤ Abar j) (hQ : ∀ i j, 0 ≤ Qbar i j)
    (hW : ∀ u i j, 0 ≤ Wbar u i j)
    (hC : ∀ u i j, 0 ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u) :
    referenceMatrixMassBudget z rho sigma Abar Qbar Wbar Cbar ≤
      transformMatrixMassBudget z rho sigma Abar Qbar Wbar Cbar δ := by
  unfold referenceMatrixMassBudget transformMatrixMassBudget
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (referenceMass_le_transformMassUpper z sigma Abar Qbar Wbar Cbar
      hσ hA hQ hW hC δ hδ hrate i j)
    (by positivity)

/-- Four coefficient-difference boxes bound the actual density-weighted
Fourier matrix change at every fixed real sample frequency. -/
theorem weightedFourierQ_difference_le_referenceMassBudget
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A₁ A₀ : Fin N → ℝ)
    (qp₁ qp₀ : Fin N → Fin N → ℝ)
    (W₁ C₁ W₀ C₀ : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, |A₁ j-A₀ j| ≤ Abar j)
    (hQ : ∀ i j, |qp₁ i j-qp₀ i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W₁ u i j-W₀ u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C₁ u i j-C₀ u i j| ≤ Cbar u i j)
    (a : ℝ) :
    complexNormSum (weightedFourierQ z rho sigma A₁ qp₁ W₁ C₁ a -
      weightedFourierQ z rho sigma A₀ qp₀ W₀ C₀ a) ≤
      referenceMatrixMassBudget z rho sigma Abar Qbar Wbar Cbar := by
  unfold complexNormSum referenceMatrixMassBudget
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.sub_apply,weightedFourierQ,Matrix.of_apply]
  rw [← mul_sub,norm_mul,norm_mul]
  have hq := fourierQ_difference_le_referenceMass z hz sigma
    A₁ A₀ qp₁ qp₀ W₁ C₁ W₀ C₀ hσ Abar Qbar Wbar Cbar
    hA hQ hW hC a i j
  calc
    ‖(sqrt (rho i) : ℂ)‖ * ‖(sqrt (rho j) : ℂ)‖ *
        ‖fourierQ z sigma A₁ qp₁ W₁ C₁ a i j -
          fourierQ z sigma A₀ qp₀ W₀ C₀ a i j‖ ≤
      ‖(sqrt (rho i) : ℂ)‖ * ‖(sqrt (rho j) : ℂ)‖ *
        referenceMass z sigma Abar Qbar Wbar Cbar i j :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = |sqrt (rho i)| * |sqrt (rho j)| *
        referenceMass z sigma Abar Qbar Wbar Cbar i j := by
      simp only [Complex.norm_real,Real.norm_eq_abs]

/-- A single exactly checked actual Fourier center plus coefficient boxes
certifies determinant nonvanishing and inverse control throughout the box. -/
theorem actual_factor_sample_slab_of_coefficient_boxes
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A₁ A₀ : Fin N → ℝ)
    (qp₁ qp₀ : Fin N → Fin N → ℝ)
    (W₁ C₁ W₀ C₀ : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, |A₁ j-A₀ j| ≤ Abar j)
    (hQ : ∀ i j, |qp₁ i j-qp₀ i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W₁ u i j-W₀ u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C₁ u i j-C₀ u i j| ≤ Cbar u i j)
    (a Cbase : ℝ)
    (hbase : (fourierFactor z rho sigma A₀ qp₀ W₀ C₀ a).det ≠ 0)
    (hCbase : complexNormSum ((fourierFactor z rho sigma A₀ qp₀ W₀ C₀ a)⁻¹) ≤ Cbase)
    (hhalf : Cbase * referenceMatrixMassBudget z rho sigma
      Abar Qbar Wbar Cbar ≤ 1/2) :
    (fourierFactor z rho sigma A₁ qp₁ W₁ C₁ a).det ≠ 0 ∧
      complexNormSum ((fourierFactor z rho sigma A₁ qp₁ W₁ C₁ a)⁻¹) ≤
        2*(N : ℝ)*Cbase := by
  exact actual_factor_sample_slab_inverse_bound z rho sigma
    A₀ A₁ qp₀ qp₁ W₀ C₀ W₁ C₁ a Cbase
    (referenceMatrixMassBudget z rho sigma Abar Qbar Wbar Cbar)
    hbase hCbase
    (weightedFourierQ_difference_le_referenceMassBudget z hz rho sigma
      A₁ A₀ qp₁ qp₀ W₁ C₁ W₀ C₀ hσ Abar Qbar Wbar Cbar
      hA hQ hW hC a) hhalf

/-- The coupling-slab sample certificate has no unevaluated integral:
the change budget is the actual `Qhat(-δ)` finite transform expression. -/
theorem actual_factor_sample_slab_of_transform_boxes
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A₁ A₀ : Fin N → ℝ)
    (qp₁ qp₀ : Fin N → Fin N → ℝ)
    (W₁ C₁ W₀ C₀ : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA0 : ∀ j, 0 ≤ Abar j) (hQ0 : ∀ i j, 0 ≤ Qbar i j)
    (hW0 : ∀ u i j, 0 ≤ Wbar u i j)
    (hC0 : ∀ u i j, 0 ≤ Cbar u i j)
    (hA : ∀ j, |A₁ j-A₀ j| ≤ Abar j)
    (hQ : ∀ i j, |qp₁ i j-qp₀ i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W₁ u i j-W₀ u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C₁ u i j-C₀ u i j| ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (a Cbase : ℝ)
    (hbase : (fourierFactor z rho sigma A₀ qp₀ W₀ C₀ a).det ≠ 0)
    (hCbase : complexNormSum ((fourierFactor z rho sigma A₀ qp₀ W₀ C₀ a)⁻¹) ≤ Cbase)
    (hhalf : Cbase * transformMatrixMassBudget z rho sigma
      Abar Qbar Wbar Cbar δ ≤ 1/2) :
    (fourierFactor z rho sigma A₁ qp₁ W₁ C₁ a).det ≠ 0 ∧
      complexNormSum ((fourierFactor z rho sigma A₁ qp₁ W₁ C₁ a)⁻¹) ≤
        2*(N : ℝ)*Cbase := by
  have hCbase0 : 0 ≤ Cbase := (complexNormSum_nonneg _).trans hCbase
  have hmass := referenceMatrixMassBudget_le_transformMatrixMassBudget z rho
    sigma Abar Qbar Wbar Cbar hσ hA0 hQ0 hW0 hC0 δ hδ hrate
  have hhalf' : Cbase * referenceMatrixMassBudget z rho sigma
      Abar Qbar Wbar Cbar ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hmass hCbase0).trans hhalf
  exact actual_factor_sample_slab_of_coefficient_boxes z hz rho sigma
    A₁ A₀ qp₁ qp₀ W₁ C₁ W₀ C₀ hσ Abar Qbar Wbar Cbar
    hA hQ hW hC a Cbase hbase hCbase hhalf'

def CoefficientBoxContains (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p center : TailMatrix T N × TailMatrix T N)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N) : Prop :=
  (∀ j, |amplitudeA z rho sigma p.1 p.2 j -
    amplitudeA z rho sigma center.1 center.2 j| ≤ Abar j) ∧
  (∀ i j, |amplitudeQp z rho sigma p.1 p.2 i j -
    amplitudeQp z rho sigma center.1 center.2 i j| ≤ Qbar i j) ∧
  (∀ u i j, |W z rho p.1 p.2 u i j -
    W z rho center.1 center.2 u i j| ≤ Wbar u i j) ∧
  (∀ u i j, |C z rho sigma p.1 p.2 u i j -
    C z rho sigma center.1 center.2 u i j| ≤ Cbar u i j)

/-- A local coefficient box and an absolute center cap imply a global cap. -/
theorem abs_le_of_center_box (x y d M : ℝ)
    (hxy : |x-y| ≤ d) (hcenter : |y|+d ≤ M) : |x| ≤ M := by
  calc
    |x| = |(x-y)+y| := by rw [sub_add_cancel]
    _ ≤ |x-y|+|y| := abs_add_le _ _
    _ ≤ d+|y| := by linarith
    _ = |y|+d := add_comm _ _
    _ ≤ M := hcenter

/-- A finite family of actual-amplitude center boxes certifies all
specified Fourier samples over a whole coupling set. Center factors are
checked only finitely often; each path value must belong to one box. -/
theorem path_samples_of_finite_coefficient_boxes
    {J : Type*} [Fintype J]
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (S : Set ℝ)
    (center : J → TailMatrix T N × TailMatrix T N)
    (Abar : J → Fin N → ℝ) (Qbar : J → Fin N → Fin N → ℝ)
    (Wbar Cbar : J → TailMatrix T N)
    (hA0 : ∀ c j, 0 ≤ Abar c j)
    (hQ0 : ∀ c i j, 0 ≤ Qbar c i j)
    (hW0 : ∀ c u i j, 0 ≤ Wbar c u i j)
    (hC0 : ∀ c u i j, 0 ≤ Cbar c u i j)
    (hcover : ∀ t ∈ S, ∃ c : J,
      CoefficientBoxContains z rho sigma (p t) (center c)
        (Abar c) (Qbar c) (Wbar c) (Cbar c))
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (samples : Finset ℝ) (Cbase : J → ℝ → ℝ) (Rbar : ℝ)
    (hbase : ∀ c, ∀ a ∈ samples,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (center c).1 (center c).2)
        (amplitudeQp z rho sigma (center c).1 (center c).2)
        (W z rho (center c).1 (center c).2)
        (C z rho sigma (center c).1 (center c).2) a).det ≠ 0)
    (hCbase : ∀ c, ∀ a ∈ samples,
      complexNormSum ((fourierFactor z rho sigma
        (amplitudeA z rho sigma (center c).1 (center c).2)
        (amplitudeQp z rho sigma (center c).1 (center c).2)
        (W z rho (center c).1 (center c).2)
        (C z rho sigma (center c).1 (center c).2) a)⁻¹) ≤ Cbase c a)
    (hhalf : ∀ c, ∀ a ∈ samples,
      Cbase c a * transformMatrixMassBudget z rho sigma
        (Abar c) (Qbar c) (Wbar c) (Cbar c) δ ≤ 1/2)
    (hRbar : ∀ c, ∀ a ∈ samples, 2*(N : ℝ)*Cbase c a ≤ Rbar) :
    ∀ t ∈ S, ∀ a ∈ samples,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) a).det ≠ 0 ∧
      complexNormSum ((fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) a)⁻¹) ≤ Rbar := by
  intro t ht a ha
  obtain ⟨c,hbox⟩ := hcover t ht
  obtain ⟨hA,hQ,hW,hC⟩ := hbox
  obtain ⟨hdet,hinv⟩ := actual_factor_sample_slab_of_transform_boxes
    z hz rho sigma
    (amplitudeA z rho sigma (p t).1 (p t).2)
    (amplitudeA z rho sigma (center c).1 (center c).2)
    (amplitudeQp z rho sigma (p t).1 (p t).2)
    (amplitudeQp z rho sigma (center c).1 (center c).2)
    (W z rho (p t).1 (p t).2)
    (C z rho sigma (p t).1 (p t).2)
    (W z rho (center c).1 (center c).2)
    (C z rho sigma (center c).1 (center c).2)
    hσ (Abar c) (Qbar c) (Wbar c) (Cbar c)
    (hA0 c) (hQ0 c) (hW0 c) (hC0 c)
    hA hQ hW hC δ hδ hrate a (Cbase c a)
    (hbase c a ha) (hCbase c a ha) (hhalf c a ha)
  exact ⟨hdet,hinv.trans (hRbar c a ha)⟩

/-- An end-to-end conditional certificate: finite center caps and local
coefficient boxes give global BH caps and sample inverses. The arithmetic
frequency mesh then excludes original mixture amplitude escape. -/
theorem hs_finite_center_mesh_amplitude_bound
    {J : Type*} [Fintype J]
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Set.Ico 0 b))
    (hroot : ∀ t ∈ Set.Ico 0 b,
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (Ag : Fin N → ℝ) (Qg : Fin N → Fin N → ℝ)
    (Wg Cg : TailMatrix T N)
    (hAg0 : ∀ j, 0 ≤ Ag j) (hQg0 : ∀ i j, 0 ≤ Qg i j)
    (hWg0 : ∀ u i j, 0 ≤ Wg u i j)
    (hCg0 : ∀ u i j, 0 ≤ Cg u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hspan : 2*explicitWindow z rho sigma Ag Qg Wg Cg ≤ (n : ℝ)*h)
    (Rbar : ℝ) (hR0 : 0 ≤ Rbar)
    (hstep : Rbar * (h * momentBudget rho
      (transformMomentUpper z sigma Ag Qg Wg Cg δ)) < 1)
    (center : J → TailMatrix T N × TailMatrix T N)
    (Al : J → Fin N → ℝ) (Ql : J → Fin N → Fin N → ℝ)
    (Wl Cl : J → TailMatrix T N)
    (hAl0 : ∀ c j, 0 ≤ Al c j)
    (hQl0 : ∀ c i j, 0 ≤ Ql c i j)
    (hWl0 : ∀ c u i j, 0 ≤ Wl c u i j)
    (hCl0 : ∀ c u i j, 0 ≤ Cl c u i j)
    (hcover : ∀ t ∈ Set.Ico 0 b, ∃ c : J,
      CoefficientBoxContains z rho sigma (p t) (center c)
        (Al c) (Ql c) (Wl c) (Cl c))
    (hAgCenter : ∀ c j,
      |amplitudeA z rho sigma (center c).1 (center c).2 j| + Al c j ≤ Ag j)
    (hQgCenter : ∀ c i j,
      |amplitudeQp z rho sigma (center c).1 (center c).2 i j| + Ql c i j ≤ Qg i j)
    (hWgCenter : ∀ c u i j,
      |W z rho (center c).1 (center c).2 u i j| + Wl c u i j ≤ Wg u i j)
    (hCgCenter : ∀ c u i j,
      |C z rho sigma (center c).1 (center c).2 u i j| + Cl c u i j ≤ Cg u i j)
    (Cbase : J → ℝ → ℝ)
    (hbase : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (center c).1 (center c).2)
        (amplitudeQp z rho sigma (center c).1 (center c).2)
        (W z rho (center c).1 (center c).2)
        (C z rho sigma (center c).1 (center c).2) a).det ≠ 0)
    (hCbase : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      complexNormSum ((fourierFactor z rho sigma
        (amplitudeA z rho sigma (center c).1 (center c).2)
        (amplitudeQp z rho sigma (center c).1 (center c).2)
        (W z rho (center c).1 (center c).2)
        (C z rho sigma (center c).1 (center c).2) a)⁻¹) ≤ Cbase c a)
    (hhalf : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      Cbase c a * transformMatrixMassBudget z rho sigma
        (Al c) (Ql c) (Wl c) (Cl c) δ ≤ 1/2)
    (hRbar : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      2*(N : ℝ)*Cbase c a ≤ Rbar) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico 0 b, ‖p t‖ ≤ B := by
  have hAg : ∀ t ∈ Set.Ico 0 b, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Ag j := by
    intro t ht j
    obtain ⟨c,hbox⟩ := hcover t ht
    exact abs_le_of_center_box _ _ _ _ (hbox.1 j) (hAgCenter c j)
  have hQg : ∀ t ∈ Set.Ico 0 b, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qg i j := by
    intro t ht i j
    obtain ⟨c,hbox⟩ := hcover t ht
    exact abs_le_of_center_box _ _ _ _ (hbox.2.1 i j) (hQgCenter c i j)
  have hWg : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wg u i j := by
    intro t ht u i j
    obtain ⟨c,hbox⟩ := hcover t ht
    exact abs_le_of_center_box _ _ _ _ (hbox.2.2.1 u i j) (hWgCenter c u i j)
  have hCg : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |C z rho sigma (p t).1 (p t).2 u i j| ≤ Cg u i j := by
    intro t ht u i j
    obtain ⟨c,hbox⟩ := hcover t ht
    exact abs_le_of_center_box _ _ _ _ (hbox.2.2.2 u i j) (hCgCenter c u i j)
  have hsamples := path_samples_of_finite_coefficient_boxes z hz rho sigma
    (fun i => (hσ i).le) p (Set.Ico 0 b) center Al Ql Wl Cl
    hAl0 hQl0 hWl0 hCl0 hcover δ hδ hrate
    (uniformSamples (explicitWindow z rho sigma Ag Qg Wg Cg) h n)
    Cbase Rbar hbase hCbase hhalf hRbar
  apply hs_uniform_mesh_amplitude_bound z hz rho sigma hρ hσ hη
    K hK p b hb hp0 hp hroot Ag Qg Wg Cg
    hAg0 hQg0 hWg0 hCg0 hAg hQg hWg hCg δ hδ hrate
    h hh n hspan Rbar hR0
  · intro t ht a ha
    exact (hsamples t ht a ha).1
  · intro t ht a ha
    exact (hsamples t ht a ha).2
  · exact hstep

/-- The finite-center mixture certificate can use determinant margins and
adjugate bounds at every center sample instead of matrix inverse entries. -/
theorem hs_finite_center_mesh_adjugate_amplitude_bound
    {J : Type*} [Fintype J]
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Set.Ico 0 b))
    (hroot : ∀ t ∈ Set.Ico 0 b,
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (Ag : Fin N → ℝ) (Qg : Fin N → Fin N → ℝ)
    (Wg Cg : TailMatrix T N)
    (hAg0 : ∀ j, 0 ≤ Ag j) (hQg0 : ∀ i j, 0 ≤ Qg i j)
    (hWg0 : ∀ u i j, 0 ≤ Wg u i j)
    (hCg0 : ∀ u i j, 0 ≤ Cg u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hspan : 2*explicitWindow z rho sigma Ag Qg Wg Cg ≤ (n : ℝ)*h)
    (Rbar : ℝ) (hR0 : 0 ≤ Rbar)
    (hstep : Rbar * (h * momentBudget rho
      (transformMomentUpper z sigma Ag Qg Wg Cg δ)) < 1)
    (center : J → TailMatrix T N × TailMatrix T N)
    (Al : J → Fin N → ℝ) (Ql : J → Fin N → Fin N → ℝ)
    (Wl Cl : J → TailMatrix T N)
    (hAl0 : ∀ c j, 0 ≤ Al c j)
    (hQl0 : ∀ c i j, 0 ≤ Ql c i j)
    (hWl0 : ∀ c u i j, 0 ≤ Wl c u i j)
    (hCl0 : ∀ c u i j, 0 ≤ Cl c u i j)
    (hcover : ∀ t ∈ Set.Ico 0 b, ∃ c : J,
      CoefficientBoxContains z rho sigma (p t) (center c)
        (Al c) (Ql c) (Wl c) (Cl c))
    (hAgCenter : ∀ c j,
      |amplitudeA z rho sigma (center c).1 (center c).2 j| + Al c j ≤ Ag j)
    (hQgCenter : ∀ c i j,
      |amplitudeQp z rho sigma (center c).1 (center c).2 i j| + Ql c i j ≤ Qg i j)
    (hWgCenter : ∀ c u i j,
      |W z rho (center c).1 (center c).2 u i j| + Wl c u i j ≤ Wg u i j)
    (hCgCenter : ∀ c u i j,
      |C z rho sigma (center c).1 (center c).2 u i j| + Cl c u i j ≤ Cg u i j)
    (m Badj : J → ℝ → ℝ)
    (hm : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n, 0 < m c a)
    (hdet : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      m c a ≤ ‖(fourierFactor z rho sigma
        (amplitudeA z rho sigma (center c).1 (center c).2)
        (amplitudeQp z rho sigma (center c).1 (center c).2)
        (W z rho (center c).1 (center c).2)
        (C z rho sigma (center c).1 (center c).2) a).det‖)
    (hadj : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      complexNormSum (fourierFactor z rho sigma
        (amplitudeA z rho sigma (center c).1 (center c).2)
        (amplitudeQp z rho sigma (center c).1 (center c).2)
        (W z rho (center c).1 (center c).2)
        (C z rho sigma (center c).1 (center c).2) a).adjugate ≤ Badj c a)
    (hhalf : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      (Badj c a / m c a) * transformMatrixMassBudget z rho sigma
        (Al c) (Ql c) (Wl c) (Cl c) δ ≤ 1/2)
    (hRbar : ∀ c, ∀ a ∈ uniformSamples
      (explicitWindow z rho sigma Ag Qg Wg Cg) h n,
      2*(N : ℝ)*(Badj c a / m c a) ≤ Rbar) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico 0 b, ‖p t‖ ≤ B := by
  apply hs_finite_center_mesh_amplitude_bound z hz rho sigma hρ hσ hη
    K hK p b hb hp0 hp hroot Ag Qg Wg Cg
    hAg0 hQg0 hWg0 hCg0 δ hδ hrate h hh n hspan
    Rbar hR0 hstep center Al Ql Wl Cl
    hAl0 hQl0 hWl0 hCl0 hcover
    hAgCenter hQgCenter hWgCenter hCgCenter
    (fun c a => Badj c a / m c a)
  · intro c a ha heq
    have hpos := lt_of_lt_of_le (hm c a ha) (hdet c a ha)
    simp [heq] at hpos
  · intro c a ha
    exact inverse_normSum_le_adjugate_over_margin _ (m c a) (Badj c a)
      (hm c a ha) (hdet c a ha) (hadj c a ha)
  · exact hhalf
  · exact hRbar

end FMSA.Convergence.MixtureCouplingSlabCertificate
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.inverse_bound_of_half_perturbation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.inverse_bound_of_half_perturbation
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.actual_factor_sample_slab_inverse_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.actual_factor_sample_slab_inverse_bound
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.actual_q_sub_eq_q_of_coefficient_differences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.actual_q_sub_eq_q_of_coefficient_differences
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.referenceMass_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.referenceMass_integrable
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.referenceMass_le_transformMassUpper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.referenceMass_le_transformMassUpper
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.fourierQ_difference_le_referenceMass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.fourierQ_difference_le_referenceMass
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.referenceMatrixMassBudget_le_transformMatrixMassBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.referenceMatrixMassBudget_le_transformMatrixMassBudget
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.weightedFourierQ_difference_le_referenceMassBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.weightedFourierQ_difference_le_referenceMassBudget
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.actual_factor_sample_slab_of_coefficient_boxes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.actual_factor_sample_slab_of_coefficient_boxes
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.actual_factor_sample_slab_of_transform_boxes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.actual_factor_sample_slab_of_transform_boxes
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.abs_le_of_center_box' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.abs_le_of_center_box
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.path_samples_of_finite_coefficient_boxes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.path_samples_of_finite_coefficient_boxes
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.hs_finite_center_mesh_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.hs_finite_center_mesh_amplitude_bound
/-- info: 'FMSA.Convergence.MixtureCouplingSlabCertificate.hs_finite_center_mesh_adjugate_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCouplingSlabCertificate.hs_finite_center_mesh_adjugate_amplitude_bound
