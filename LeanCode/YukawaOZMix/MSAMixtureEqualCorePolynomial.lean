import LeanCode.YukawaOZMix.MSAMixtureEqualCoreOriginAlgebra

/-! The three polynomial coefficients of the old equal-diameter core
are exact reductions of the checked unequal-diameter coefficients. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

theorem legacyC1_kernel (z sig : ℝ) (hz : z ≠ 0) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (hσ : ∀ i, σ i = sig) (i j : Fin N) :
    MSAMixtureCoreUneq.cC1o z ρ σ A qp Wt Ct i j =
      -A j+2*π*∑ l, ρ l*c1pair z (A l) (qp i l) (qp j l) (Wt i l) (Wt j l)
        (Ct i l) (Ct j l) sig := by
  simp only [MSAMixtureCoreUneq.cC1o, hσ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  unfold c1pair
  field_simp [hz, pi_ne_zero]
  <;> ring

theorem legacyC2_kernel (z sig : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (hσ : ∀ i, σ i = sig) (i j : Fin N) :
    MSAMixtureCoreUneq.cC2o z ρ σ A qp Wt Ct i j =
      (1/2 : ℝ)*∑ l, ρ l*(qp i l*qp j l-A l*(Ct i l+Ct j l)) := by
  simp only [MSAMixtureCoreUneq.cC2o, hσ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem legacyC3_zero (z sig : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (hσ : ∀ i, σ i = sig)
    (hqp : ∀ a b m, qp a m=qp b m) (i j : Fin N) :
    MSAMixtureCoreUneq.cC3o z ρ σ A qp Wt Ct i j=0 := by
  simp only [MSAMixtureCoreUneq.cC3o, hσ]
  apply Finset.sum_eq_zero
  intro l _
  rw [hqp j i l]
  ring

theorem legacyEqual_poly_coefficients (z sig : ℝ) (hz : z ≠ 0) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig) (i j : Fin N) :
    MSAMixtureCoreUneq.cC1o z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j -
      MSAMixtureCoreUneq.cC1o z ρ σ (A0Vec ρ σ) (qp0Mat ρ σ) 0 0 i j =
      2*π*coreC1 z ρ σ Gt Dt K i j ∧
    MSAMixtureCoreUneq.cC2o z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j -
      MSAMixtureCoreUneq.cC2o z ρ σ (A0Vec ρ σ) (qp0Mat ρ σ) 0 0 i j =
      2*π*coreC2 z ρ σ Gt Dt K i j ∧
    MSAMixtureCoreUneq.cC4o z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j -
      MSAMixtureCoreUneq.cC4o z ρ σ (A0Vec ρ σ) (qp0Mat ρ σ) 0 0 i j =
      2*π*coreC3 z ρ σ Gt Dt K i j ∧
    MSAMixtureCoreUneq.cC3o z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j=0 := by
  have hsij : sigMix σ i j=sig := by unfold sigMix; rw [hσ i,hσ j]; ring
  refine ⟨?_,?_,?_,legacyC3_zero z sig ρ σ _ _ _ _ hσ
    (qpMat_equalDiam_rows z sig ρ σ Gt Dt hσ) i j⟩
  · rw [legacyC1_kernel z sig hz ρ σ _ _ _ _ hσ,
      legacyC1_kernel z sig hz ρ σ _ _ _ _ hσ, coreC1]
    simp only [hsij, AVec, AMSA, qpMat, A0Vec, qp0Mat, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib]
    field_simp [pi_ne_zero]
    <;> ring
  · rw [legacyC2_kernel z sig ρ σ _ _ _ _ hσ,
      legacyC2_kernel z sig ρ σ _ _ _ _ hσ, coreC2]
    simp only [AVec, qpMat, A0Vec, qp0Mat, Pi.zero_apply, mul_zero, add_zero,
      sub_zero, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    field_simp [pi_ne_zero]
    <;> ring
  · simp only [MSAMixtureCoreUneq.cC4o, coreC3, AVec, A0Vec,
      Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    simp only [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    field_simp [pi_ne_zero]
    <;> ring

end FMSA.ExactMSA.MultiTailMixture
