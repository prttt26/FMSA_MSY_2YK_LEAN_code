import MSAConvergence.MixtureMomentCoefficientBudget

/-! A finite adjugate certificate for the inverse entry-norm budget at
actual mixture Fourier samples. -/
noncomputable section
open Real
open scoped BigOperators
namespace FMSA.Convergence.MixtureSampleInverseCertificate
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.MixtureAxisFrequencyGrid
open FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

/-- The entry-norm sum of a finite complex matrix inverse is controlled by
its determinant margin and adjugate entry-norm sum. -/
theorem inverse_normSum_le_adjugate_over_margin
    (A : Matrix (Fin N) (Fin N) ℂ) (m B : ℝ)
    (hm : 0 < m) (hdet : m ≤ ‖A.det‖)
    (hB : complexNormSum A.adjugate ≤ B) :
    complexNormSum A⁻¹ ≤ B/m := by
  have hdetpos : 0 < ‖A.det‖ := lt_of_lt_of_le hm hdet
  have hdetne : A.det ≠ 0 := by
    intro h
    simp [h] at hdetpos
  have heq : complexNormSum A⁻¹ =
      ‖A.det⁻¹‖ * complexNormSum A.adjugate := by
    rw [Matrix.inv_def]
    unfold complexNormSum
    simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, norm_mul,
      Finset.mul_sum]
  rw [heq, norm_inv]
  have hnorm : 0 ≤ complexNormSum A.adjugate := complexNormSum_nonneg _
  have hB0 : 0 ≤ B := hnorm.trans hB
  have hinv : (‖A.det‖)⁻¹ ≤ m⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hm hdet
  calc
    (‖A.det‖)⁻¹ * complexNormSum A.adjugate ≤
        m⁻¹ * complexNormSum A.adjugate :=
      mul_le_mul_of_nonneg_right hinv hnorm
    _ ≤ m⁻¹ * B := mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hm.le)
    _ = B/m := by ring

/-- A positive determinant margin and a finite adjugate bound certify an
actual physical Fourier factor on a whole frequency slab. -/
theorem factor_det_ne_zero_on_slab_of_adjugate
    {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (a k m B : ℝ) (M : Fin N → Fin N → ℝ)
    (hM : ∀ i j, (∫ r : ℝ,
      |r| * |q z sigma A qp W C i j r|) ≤ M i j)
    (hm : 0 < m)
    (hdet : m ≤ ‖(fourierFactor z rho sigma A qp W C a).det‖)
    (hB : complexNormSum (fourierFactor z rho sigma A qp W C a).adjugate ≤ B)
    (hstep : (B/m) * (|k-a| * momentBudget rho M) < 1) :
    (fourierFactor z rho sigma A qp W C k).det ≠ 0 := by
  have hbase : (fourierFactor z rho sigma A qp W C a).det ≠ 0 := by
    intro h
    have hh := lt_of_lt_of_le hm hdet
    simp [h] at hh
  exact factor_det_ne_zero_on_sample_slab z hz rho sigma A qp W C hσ
    a k (B/m) M hM hbase
    (inverse_normSum_le_adjugate_over_margin _ m B hm hdet hB) hstep

end FMSA.Convergence.MixtureSampleInverseCertificate

/-- info: 'FMSA.Convergence.MixtureSampleInverseCertificate.inverse_normSum_le_adjugate_over_margin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureSampleInverseCertificate.inverse_normSum_le_adjugate_over_margin
/-- info: 'FMSA.Convergence.MixtureSampleInverseCertificate.factor_det_ne_zero_on_slab_of_adjugate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureSampleInverseCertificate.factor_det_ne_zero_on_slab_of_adjugate
