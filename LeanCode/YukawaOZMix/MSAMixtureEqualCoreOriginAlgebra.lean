import LeanCode.YukawaOZMix.MSAMixtureEqualCoreOrigin
import LeanCode.YukawaOZMix.MSAMixtureSingleTailOriginPolynomial

/-! The removable equal-diameter origin term vanishes at every actual
symmetric-contact BH root; this is an algebraic and analytic kernel proof. -/
noncomputable section
open Real MeasureTheory Set Filter Topology MSAMixture FMSA.MatrixQ0 Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

theorem legacyOuterNumerator_origin_sum (z sig : ℝ) (hz : z ≠ 0)
    (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (hσ : ∀ i, σ i = sig) (hqp : ∀ a b m, qp a m = qp b m) (i j : Fin N) :
    legacyOuterNumerator z ρ σ A qp Wt Ct i j 0 +
      legacyOuterNumerator z ρ σ A qp Wt Ct j i 0 +
      (qp i j-sig*A j-z*Wt i j)+(qp j i-sig*A i-z*Wt j i)+
      ∑ m, ρ m*(-sig*qp i m+A m*sig^2/2+Wt i m+Ct i m)*
        (-sig*qp j m+A m*sig^2/2+Wt j m+Ct j m) = 0 := by
  have hem : exp (-z*(sig+sig)/2)=exp (-z*sig) := by congr 1; ring
  have hez : exp (sig*z)=1/exp (-z*sig) := by
    apply (eq_div_iff (exp_ne_zero _)).mpr
    rw [← exp_add, show sig*z + -z*sig = 0 by ring, exp_zero]
  simp only [legacyOuterNumerator, MSAMixtureCoreUneq.gForm, mul_zero, zero_pow two_ne_zero, zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    add_zero, neg_zero, exp_zero, mul_one, MSAMixtureCoreUneq.cC0o,
    MSAMixtureCoreUneq.cEmo, MSAMixtureCoreUneq.cEpo, hσ, sub_self, mul_zero,
    zero_div, neg_zero, exp_zero, hem]
  simp_rw [hqp j i]
  ring_nf
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro m _
  rw [hez]
  field_simp [hz, exp_ne_zero]
  <;> ring


theorem qpMat_equalDiam_rows (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig) (a b m : Fin N) :
    qpMat z ρ σ Gt Dt a m = qpMat z ρ σ Gt Dt b m := by
  rw [← amplitudeQp_single z ρ σ Gt Dt]
  rw [amplitudeQp_nonlinear_rank_two, amplitudeQp_nonlinear_rank_two, hσ a, hσ b]

theorem legacyEqual_core_origin_zero (z : ℝ) (hz : 0 < z)
    (ρ σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (sig : ℝ)
    (hs : 0 < sig) (hσ : ∀ i, σ i = sig) (hv : vacMix ρ σ ≠ 0)
    (hr : MixBHRootUneq z ρ σ Gt Dt K) (hK : ∀ i j, K i j = K j i) (i j : Fin N) :
    MSAMixtureCoreUneq.cC0o z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j =
      -MSAMixtureCoreUneq.cEmo z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j -
      MSAMixtureCoreUneq.cEpo z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j := by
  have hc := nonlinearRoot_automatic_finite_wronskian (fun _ : Unit => z) ρ σ (fun _ => K)
    (fun _ => Dt) (fun _ => Gt) (fun _ => hz) hv
    ((isRoot_single_iff z hz.ne' ρ σ Gt Dt K).mpr hr) (fun _ => hK)
  have hu := finite_polynomial_zero_of_coefficients _ (hc.1 i j)
  have h6 := congrArg (fun p : Polynomial ℝ => p.coeff 6) hu
  rw [legacySingle_U_coeff6, Polynomial.coeff_zero] at h6
  simp only [nonlinearLowerQValue, amplitudeA_single, amplitudeQp_single, W_single, C_single,
    Finset.univ_unique, Finset.sum_singleton, hσ] at h6
  simp only [← add_assoc] at h6
  have hs0 := legacyOuterNumerator_origin_sum z sig hz.ne' ρ σ (AVec z ρ σ Gt Dt)
    (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) hσ
    (qpMat_equalDiam_rows z sig ρ σ Gt Dt hσ) i j
  have hrec := legacyOuterNumerator_equalDiam_reciprocal_zero z hz ρ σ Gt Dt K sig hs hσ hv hr hK i j
  have he : legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j 0 = 0 := by
    have hsm : legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j 0 +
        legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
          (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) j i 0 = 0 := by
      linear_combination (norm := ring_nf) hs0 - h6 <;> simp only [sub_self]
    linarith
  simp only [legacyOuterNumerator, MSAMixtureCoreUneq.gForm, mul_zero, zero_pow two_ne_zero, zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    add_zero, neg_zero, exp_zero, mul_one] at he
  linarith

end FMSA.ExactMSA.MultiTailMixture
