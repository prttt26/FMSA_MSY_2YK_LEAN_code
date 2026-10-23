import LeanCode.YukawaOZMix.MSAMixtureEqualRootBridge
import LeanCode.YukawaOZMix.MSAMixtureLegacySingleTail

/-! Species contractions of both BH equations identify the equal-diameter
exponential core coefficients, for arbitrary finite species count. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def legacyS (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j =>
  (AVec z ρ σ Gt Dt j+z*qpMat z ρ σ Gt Dt i j+z^2*Ct z ρ σ Gt Dt i j/2)/z^2

def legacyQ (z sig : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j =>
  qhatMixR z sig (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
    (AVec z ρ σ Gt Dt) z i j

def legacyW (z : ℝ) (ρ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := Wt z ρ Gt Dt

def legacyC (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := Ct z ρ σ Gt Dt

theorem legacyS_entry (z : ℝ) (hz : z ≠ 0) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    legacyS z ρ σ Gt Dt i j = AVec z ρ σ Gt Dt j/z^2+qpMat z ρ σ Gt Dt i j/z+
      Ct z ρ σ Gt Dt i j/2 := by
  unfold legacyS
  field_simp [hz]
  <;> ring

theorem Wt_matrix_dictionary (z : ℝ) (ρ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    legacyW z ρ Gt Dt=(2*π/z) • (Gt*Matrix.diagonal ρ*Dt) := by
  ext i j
  simp only [legacyW, Wt, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply (M := Gt*Matrix.diagonal ρ),
    Matrix.mul_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem legacyRoot_first_matrix (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hr : MixBHRoot z sig ρ σ Gt Dt K) :
    Dt*(1-Matrix.diagonal ρ*(legacyQ z sig ρ σ Gt Dt).transpose)=(2*π/z) • K := by
  ext i j
  simpa only [Matrix.mul_apply (M := Dt), Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, legacyQ, div_mul_eq_mul_div,
    mul_assoc] using hr.1 i j

theorem legacyRoot_second_matrix (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hr : MixBHRoot z sig ρ σ Gt Dt K) :
    legacyS z ρ σ Gt Dt=(2*π) • (Gt*(1-Matrix.diagonal ρ*legacyQ z sig ρ σ Gt Dt)) := by
  ext i j
  simpa only [Matrix.mul_apply (M := Gt), Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul, legacyQ, legacyS] using (hr.2 i j).symm

theorem legacyD_S_contraction (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hr : MixBHRoot z sig ρ σ Gt Dt K) :
    Dt*Matrix.diagonal ρ*(legacyS z ρ σ Gt Dt).transpose =
      (4*π^2/z) • (K*Matrix.diagonal ρ*Gt.transpose) := by
  rw [legacyRoot_second_matrix z sig ρ σ Gt Dt K hr,
    Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_one]
  have hm : Dt*Matrix.diagonal ρ*((1-(legacyQ z sig ρ σ Gt Dt).transpose*Matrix.diagonal ρ)*Gt.transpose)=
      (Dt*(1-Matrix.diagonal ρ*(legacyQ z sig ρ σ Gt Dt).transpose))*Matrix.diagonal ρ*Gt.transpose := by
    noncomm_ring
  rw [Matrix.mul_smul, hm, legacyRoot_first_matrix z sig ρ σ Gt Dt K hr]
  simp only [Matrix.smul_mul, smul_smul]
  congr 1
  ring

theorem legacyW_S_contraction (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hr : MixBHRoot z sig ρ σ Gt Dt K) :
    legacyW z ρ Gt Dt*Matrix.diagonal ρ*(legacyS z ρ σ Gt Dt).transpose =
      (8*π^3/z^2) • (Gt*Matrix.diagonal ρ*K*Matrix.diagonal ρ*Gt.transpose) := by
  rw [Wt_matrix_dictionary]
  simp only [Matrix.smul_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Dt, legacyD_S_contraction z sig ρ σ Gt Dt K hr]
  simp only [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  congr 1
  ring

theorem legacyW_root_contraction (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hr : MixBHRoot z sig ρ σ Gt Dt K) :
    z • (legacyW z ρ Gt Dt*(1-Matrix.diagonal ρ*(legacyQ z sig ρ σ Gt Dt).transpose)) =
      (4*π^2/z) • (Gt*Matrix.diagonal ρ*K) := by
  rw [Wt_matrix_dictionary, Matrix.smul_mul, Matrix.mul_assoc,
    legacyRoot_first_matrix z sig ρ σ Gt Dt K hr]
  simp only [Matrix.mul_smul, smul_smul]
  congr 1
  by_cases hz : z=0
  · simp [hz]
  · field_simp [hz]
    <;> ring


theorem legacyCt_equalDiam (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig) :
    legacyC z ρ σ Gt Dt=Dt-exp (-z*sig) • legacyW z ρ Gt Dt := by
  have hex : exp (-z*sig)*exp (z*sig)=1 := by
    rw [← exp_add]; simp
  simp only [neg_mul] at hex
  ext i j
  have h := W_add_C_exp (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) () i j
  simp only [W, C, edgeLo, edgeHi, hσ, sub_self, zero_div, mul_zero, exp_zero, mul_one] at h
  have he : (sig+sig)/2=sig := by ring
  rw [he] at h
  simp only [legacyC, legacyW, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hc : Ct z ρ σ Gt Dt i j = (Dt i j*exp (z*sig)-Wt z ρ Gt Dt i j)/exp (z*sig) := by
    apply (eq_div_iff (exp_ne_zero _)).mpr
    linarith [h]
  have hi : (exp (z*sig))⁻¹=exp (-z*sig) := by rw [← exp_neg]; congr 1; ring
  rw [hc, sub_div]
  simp only [mul_div_cancel_right₀ _ (exp_ne_zero _), div_eq_mul_inv, hi]
  ring


theorem legacyEm_kernel (z sig : ℝ) (hz : z ≠ 0) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (hσ : ∀ i, σ i = sig) (i j : Fin N) :
    MSAMixtureCoreUneq.cEmo z ρ σ A qp Wt Ct i j =
      z*Wt i j+∑ l, ρ l*(Ct i l*(A l/z^2+qp j l/z+Ct j l/2)-
        z*Wt i l*qhatMixR z sig qp Wt Ct A z j l) := by
  have hem : exp (-z*(sig+sig)/2)=exp (-z*sig) := by congr 1; ring
  have hez : exp (sig*z)=1/exp (-z*sig) := by
    apply (eq_div_iff (exp_ne_zero _)).mpr
    rw [← exp_add, show sig*z + -z*sig = 0 by ring, exp_zero]
  simp only [MSAMixtureCoreUneq.cEmo, hσ, sub_self, mul_zero, neg_zero, zero_div,
    exp_zero, mul_one, hem]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [hez]
  unfold qhatMixR
  field_simp [hz, exp_ne_zero]
  <;> ring

theorem legacyEp_kernel (z sig : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (hσ : ∀ i, σ i = sig) (i j : Fin N) :
    MSAMixtureCoreUneq.cEpo z ρ σ A qp Wt Ct i j =
      -exp (-z*sig)*∑ l, ρ l*Wt j l*(A l/z^2+qp i l/z+Ct i l/2) := by
  have hem : exp (-z*(sig+sig)/2)=exp (-z*sig) := by congr 1; ring
  simp only [MSAMixtureCoreUneq.cEpo, hσ, hem, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem legacyWeighted_transpose_entry (ρ : Fin N → ℝ)
    (A B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (A*Matrix.diagonal ρ*B.transpose) i j=∑ l, ρ l*A i l*B j l := by
  simp only [Matrix.mul_apply (M := A*Matrix.diagonal ρ), Matrix.mul_diagonal,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem legacyEm_matrix (z sig : ℝ) (hz : z ≠ 0) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig) (i j : Fin N) :
    MSAMixtureCoreUneq.cEmo z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j =
      (z • (legacyW z ρ Gt Dt*(1-Matrix.diagonal ρ*(legacyQ z sig ρ σ Gt Dt).transpose))+
        legacyC z ρ σ Gt Dt*Matrix.diagonal ρ*(legacyS z ρ σ Gt Dt).transpose) i j := by
  rw [legacyEm_kernel z sig hz ρ σ _ _ _ _ hσ]
  have hm : legacyW z ρ Gt Dt*(1-Matrix.diagonal ρ*(legacyQ z sig ρ σ Gt Dt).transpose)=
      legacyW z ρ Gt Dt-legacyW z ρ Gt Dt*Matrix.diagonal ρ*(legacyQ z sig ρ σ Gt Dt).transpose := by
    noncomm_ring
  rw [hm]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    legacyWeighted_transpose_entry, legacyC, legacyW, legacyQ, legacyS_entry z hz]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have he : (∑ l, ρ l*(z*Wt z ρ Gt Dt i l*qhatMixR z sig (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z j l)) =
      ∑ l, z*(ρ l*Wt z ρ Gt Dt i l*qhatMixR z sig (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z j l) := by
    apply Finset.sum_congr rfl; intro l _; ring
  rw [he]
  apply sub_eq_zero.mp
  ring_nf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro l _
  ring

theorem legacyEp_matrix (z sig : ℝ) (hz : z ≠ 0) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig) (i j : Fin N) :
    MSAMixtureCoreUneq.cEpo z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j =
      (-exp (-z*sig) • (legacyW z ρ Gt Dt*Matrix.diagonal ρ*(legacyS z ρ σ Gt Dt).transpose)) j i := by
  rw [legacyEp_kernel z sig ρ σ _ _ _ _ hσ]
  simp only [Matrix.smul_apply, smul_eq_mul, legacyWeighted_transpose_entry,
    legacyW, legacyS_entry z hz]


theorem legacyZ_entry (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) :
    ((8*π^3/z^2) • (Gt*Matrix.diagonal ρ*K*Matrix.diagonal ρ*Gt.transpose)) i j =
      -π*coreC5 z ρ σ Gt Dt K i j := by
  have he : (Gt*Matrix.diagonal ρ*K*Matrix.diagonal ρ*Gt.transpose) i j =
      ∑ l, ∑ m, ρ l*ρ m*Gt i l*K l m*Gt j m := by
    rw [legacyWeighted_transpose_entry]
    simp only [Matrix.mul_apply (M := Gt*Matrix.diagonal ρ), Matrix.mul_diagonal,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [Matrix.smul_apply, smul_eq_mul, he, coreC5]
  ring

theorem coreC5_swap (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (hK : ∀ i j, K i j = K j i) (i j : Fin N) :
    coreC5 z ρ σ Gt Dt K i j = coreC5 z ρ σ Gt Dt K j i := by
  unfold coreC5
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [hK m l]
  ring

theorem legacyLinear_entry (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (hK : ∀ i j, K i j = K j i) (i j : Fin N) :
    ((4*π^2/z) • (Gt*Matrix.diagonal ρ*K+K*Matrix.diagonal ρ*Gt.transpose)) i j =
      -2*π*coreC4 z ρ σ Gt Dt K i j := by
  have hg : (Gt*Matrix.diagonal ρ*K) i j=∑ l, ρ l*Gt i l*K j l := by
    simp only [Matrix.mul_apply (M := Gt*Matrix.diagonal ρ), Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro l _
    rw [hK l j]
    ring
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, hg,
    legacyWeighted_transpose_entry, coreC4, mul_add, Finset.sum_add_distrib]
  ring

theorem legacyEqual_exp_coefficients (z sig : ℝ) (hz : z ≠ 0) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig)
    (hr : MixBHRoot z sig ρ σ Gt Dt K) (hK : ∀ i j, K i j = K j i) (i j : Fin N) :
    MSAMixtureCoreUneq.cEmo z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j =
        -2*π*coreC4 z ρ σ Gt Dt K i j+π*exp (-z*sig)*coreC5 z ρ σ Gt Dt K i j ∧
    MSAMixtureCoreUneq.cEpo z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j =
        π*exp (-z*sig)*coreC5 z ρ σ Gt Dt K i j := by
  have hc : z • (legacyW z ρ Gt Dt*(1-Matrix.diagonal ρ*(legacyQ z sig ρ σ Gt Dt).transpose))+
      legacyC z ρ σ Gt Dt*Matrix.diagonal ρ*(legacyS z ρ σ Gt Dt).transpose =
      (4*π^2/z) • (Gt*Matrix.diagonal ρ*K+K*Matrix.diagonal ρ*Gt.transpose)-
        exp (-z*sig) • ((8*π^3/z^2) • (Gt*Matrix.diagonal ρ*K*Matrix.diagonal ρ*Gt.transpose)) := by
    rw [legacyCt_equalDiam z sig ρ σ Gt Dt hσ]
    simp only [Matrix.sub_mul, Matrix.smul_mul]
    rw [legacyW_root_contraction z sig ρ σ Gt Dt K hr,
      legacyD_S_contraction z sig ρ σ Gt Dt K hr,
      legacyW_S_contraction z sig ρ σ Gt Dt K hr]
    module
  constructor
  · rw [legacyEm_matrix z sig hz ρ σ Gt Dt hσ, hc]
    rw [Matrix.sub_apply, legacyLinear_entry z ρ σ Gt Dt K hK i j]
    change -2*π*coreC4 z ρ σ Gt Dt K i j-exp (-z*sig)*
      (((8*π^3/z^2) • (Gt*Matrix.diagonal ρ*K*Matrix.diagonal ρ*Gt.transpose)) i j) = _
    rw [legacyZ_entry]
    ring
  · rw [legacyEp_matrix z sig hz ρ σ Gt Dt hσ,
      legacyW_S_contraction z sig ρ σ Gt Dt K hr]
    change -exp (-z*sig)*
      (((8*π^3/z^2) • (Gt*Matrix.diagonal ρ*K*Matrix.diagonal ρ*Gt.transpose)) j i) = _
    rw [legacyZ_entry, coreC5_swap z ρ σ Gt Dt K hK j i]
    ring

end FMSA.ExactMSA.MultiTailMixture
