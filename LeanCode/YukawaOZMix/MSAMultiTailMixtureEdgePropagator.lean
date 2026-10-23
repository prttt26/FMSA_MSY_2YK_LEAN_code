import LeanCode.YukawaOZMix.MSAMultiTailMixtureSeedReciprocity
import LeanCode.YukawaOZMix.MSAMultiTailMixtureLinearized

/-! Actual first-order lower-edge amplitudes and the two-sided PY propagator.
These are Q-boundary identities; full DP DCF matching remains separate. -/
noncomputable section
open Real Filter Topology FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def edgeMomentA (s x : ℝ) : ℝ := 2/s^2+x/s

def edgeMomentM (s x : ℝ) : ℝ := (2-s*x-(2+s*x)*exp (-s*x))/s^2

/-- The j-dependent polynomial moment combination loses its j dependence. -/
theorem mix_edge_combination (s : ℝ) (hs : s ≠ 0) (ρ σ : Fin N → ℝ)
    (G D : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) :
    σ j*mixM s ρ σ G D j+2*mixN s ρ σ G D j =
      ∑ l, ρ l*(edgeMomentA s (σ l)*D l j + edgeMomentM s (σ l)*Wt s ρ G D l j) := by
  unfold mixM mixN
  rw [show σ j * (-(1/s) * ∑ l, ρ l * (Wt s ρ G D l j + (1+s*σ l)*Ct s ρ σ G D l j)) =
    (-σ j/s) * ∑ l, ρ l * (Wt s ρ G D l j + (1+s*σ l)*Ct s ρ σ G D l j) by ring]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  have hc := cancellation_star s ρ σ G D l j
  rw [show Ct s ρ σ G D l j = D l j-exp (-s*σ l)*Wt s ρ G D l j by linarith [hc]]
  unfold edgeMomentA edgeMomentM
  field_simp
  <;> ring

/-- Single-tail contribution to the actual lower-edge Q increment. -/
def edgeIncrement (s : ℝ) (ρ σ : Fin N → ℝ) (G D : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  -σ i*mixDqp s ρ σ G D i j + σ i^2/2*mixDA s ρ σ G D j +
    Wt s ρ G D i j + Ct s ρ σ G D i j

theorem edgeIncrement_eq_moments (s : ℝ) (hs : s ≠ 0) (ρ σ : Fin N → ℝ)
    (hv : vacMix ρ σ ≠ 0) (G D : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    edgeIncrement s ρ σ G D i j = D i j+(1-exp (-s*σ i))*Wt s ρ G D i j -
      (π*σ i/vacMix ρ σ) *
        ∑ l, ρ l*(edgeMomentA s (σ l)*D l j + edgeMomentM s (σ l)*Wt s ρ G D l j) := by
  rw [← mix_edge_combination s hs ρ σ G D j]
  have hc := cancellation_star s ρ σ G D i j
  unfold edgeIncrement mixDqp mixDA Q0phys Qppphys
  rw [show Ct s ρ σ G D i j = D i j-exp (-s*σ i)*Wt s ρ G D i j by linarith [hc]]
  field_simp
  <;> ring

/-- Left propagator written using the actual HS moment seed. -/
def edgeSeedLeft (s : ℝ) (ρ σ : Fin N → ℝ) (G : Matrix (Fin N) (Fin N) ℝ)
    (i k : Fin N) : ℝ :=
  (if i=k then 1 else 0) - π*σ i/vacMix ρ σ*ρ k*edgeMomentA s (σ k) +
    (2*π/s)*ρ k*((1-exp (-s*σ i))*G i k -
      π*σ i/vacMix ρ σ*∑ l, ρ l*edgeMomentM s (σ l)*G l k)

theorem edgeIncrement_eq_left_mul (s : ℝ) (hs : s ≠ 0) (ρ σ : Fin N → ℝ)
    (hv : vacMix ρ σ ≠ 0) (G D : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    edgeIncrement s ρ σ G D i j = ∑ k, edgeSeedLeft s ρ σ G i k*D k j := by
  rw [edgeIncrement_eq_moments s hs ρ σ hv G D i j]
  have hw : (1-exp (-s*σ i))*Wt s ρ G D i j =
      ∑ k, (2*π/s)*ρ k*(1-exp (-s*σ i))*G i k*D k j := by
    unfold Wt
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hm : (∑ l, ρ l*edgeMomentM s (σ l)*Wt s ρ G D l j) =
      ∑ k, (2*π/s)*ρ k*(∑ l, ρ l*edgeMomentM s (σ l)*G l k)*D k j := by
    unfold Wt
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have he : ∀ k, edgeSeedLeft s ρ σ G i k*D k j =
      (if i=k then D k j else 0) - (π*σ i/vacMix ρ σ)*(ρ k*edgeMomentA s (σ k)*D k j) +
      (2*π/s)*ρ k*(1-exp (-s*σ i))*G i k*D k j -
      (π*σ i/vacMix ρ σ)*((2*π/s)*ρ k*(∑ l, ρ l*edgeMomentM s (σ l)*G l k)*D k j) := by
    intro k
    unfold edgeSeedLeft
    split_ifs <;> ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have ha : (∑ l, ρ l*(edgeMomentA s (σ l)*D l j + edgeMomentM s (σ l)*Wt s ρ G D l j)) =
      (∑ l, ρ l*edgeMomentA s (σ l)*D l j) + ∑ l, ρ l*edgeMomentM s (σ l)*Wt s ρ G D l j := by
    simp only [mul_add, Finset.sum_add_distrib, mul_assoc]
  rw [hw, ha, hm]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem hsMoment_edge_cancellation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (l k : Fin N) :
    edgeMomentA (z u) (σ l)*hsMoment ρ σ (z u) l k -
      edgeMomentM (z u) (σ l)/(z u)*baseSource z ρ σ u l k =
      -π/vacMix ρ σ/(z u)^2 * σ l^2 * σ k := by
  unfold edgeMomentA edgeMomentM hsMoment baseSource Q0phys Qppphys
  field_simp
  <;> ring

theorem hsMoment_edge_identity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (i k : Fin N) :
    hsMoment ρ σ (z u) i k =
      -π*σ i/vacMix ρ σ*edgeMomentA (z u) (σ k) +
      (1-exp (-z u*σ i))/(z u)*baseSource z ρ σ u i k +
      π*σ i/vacMix ρ σ * ∑ l, ρ l *
        (edgeMomentA (z u) (σ l)*hsMoment ρ σ (z u) l k -
          edgeMomentM (z u) (σ l)/(z u)*baseSource z ρ σ u l k) := by
  simp_rw [hsMoment_edge_cancellation z ρ σ u hz hv]
  have he : (∑ l, ρ l*(-π/vacMix ρ σ/(z u)^2*σ l^2*σ k)) =
      -π/vacMix ρ σ/(z u)^2*xi2 ρ σ*σ k := by
    unfold xi2
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  unfold edgeMomentA hsMoment baseSource Q0phys Qppphys
  field_simp
  <;> ring

def edgeL (s : ℝ) (ρ σ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i k => π*σ i/vacMix ρ σ*edgeMomentA s (σ k))

def edgeV (s : ℝ) (ρ σ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i k => (if i=k then 1-exp (-s*σ i) else 0) -
    π*σ i/vacMix ρ σ*ρ k*edgeMomentM s (σ k))

theorem hsMoment_edge_matrix_identity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    Matrix.of (hsMoment ρ σ (z u)) = -edgeL (z u) ρ σ +
      edgeL (z u) ρ σ*Matrix.diagonal ρ*Matrix.of (hsMoment ρ σ (z u)) +
      (1/(z u)) • (edgeV (z u) ρ σ*Matrix.of (baseSource z ρ σ u)) := by
  ext i k
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply (M := edgeL (z u) ρ σ*Matrix.diagonal ρ) (N := Matrix.of (hsMoment ρ σ (z u))) (i := i) (k := k),
    Matrix.mul_apply (M := edgeV (z u) ρ σ) (N := Matrix.of (baseSource z ρ σ u)) (i := i) (k := k)]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, edgeL, edgeV,
    Matrix.of_apply, smul_eq_mul, sub_mul, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hsMoment_edge_identity z ρ σ u hz hv i k]
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

theorem edgeSeedLeft_matrix (s : ℝ) (ρ σ : Fin N → ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.of (edgeSeedLeft s ρ σ G) =
      1-edgeL s ρ σ*Matrix.diagonal ρ +
      (2*π/s) • (edgeV s ρ σ*G*Matrix.diagonal ρ) := by
  ext i k
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal]
  simp only [edgeSeedLeft, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, Matrix.mul_diagonal,
    Matrix.mul_apply, edgeL, edgeV, Matrix.of_apply, smul_eq_mul,
    sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  ring

theorem baseSecond_matrix_moment (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    Matrix.of (baseSecond z ρ σ u) = 1-Matrix.diagonal ρ*Matrix.of (hsMoment ρ σ (z u)) := by
  ext i j
  simp [baseSecond_entry, Matrix.diagonal_mul, Matrix.one_apply]

theorem baseFirst_transpose_matrix_moment (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    (Matrix.of (baseFirst z ρ σ u)).transpose =
      1-Matrix.of (hsMoment ρ σ (z u))*Matrix.diagonal ρ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, baseFirst, firstBlock,
    dressedQhat_zero, hsTransform, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_diagonal,
    Matrix.of_apply, hsMoment]
  have he : exp (z u*edgeLo σ i j)*exp (-z u*edgeLo σ i j) = 1 := by
    rw [← exp_add]
    simp
  have heρ : ρ j*exp (z u*edgeLo σ i j)*exp (-z u*edgeLo σ i j) = ρ j := by
    rw [mul_assoc, he, mul_one]
  simp only [← mul_assoc]
  rw [heρ]
  rw [show (if j=i then (1:ℝ) else 0) = (if i=j then 1 else 0) by simp [eq_comm]]
  ring

theorem dual_resolvent_right_inverse (H R : Matrix (Fin N) (Fin N) ℝ)
    (h : IsUnit (1-R*H).det) :
    (1+H*(1-R*H)⁻¹*R)*(1-H*R) = 1 := by
  have he : R*(1-H*R) = (1-R*H)*R := by noncomm_ring
  calc
    _ = (1-H*R)+H*(1-R*H)⁻¹*(R*(1-H*R)) := by noncomm_ring
    _ = (1-H*R)+H*(1-R*H)⁻¹*((1-R*H)*R) := by rw [he]
    _ = (1-H*R)+H*R := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right (1-R*H) H h]
    _ = 1 := by noncomm_ring

/-- The actual left seed coefficient is the transposed inverse of the first
HS block; the determinant and seed equation are supplied internally. -/
theorem edgeSeedLeft_eq_inverse_transpose (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    Matrix.of (edgeSeedLeft (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))) =
      ((Matrix.of (baseFirst z ρ σ u))⁻¹).transpose := by
  let H := Matrix.of (hsMoment ρ σ (z u))
  let R := Matrix.diagonal ρ
  let B := Matrix.of (baseSecond z ρ σ u)
  let J := Matrix.of (baseSource z ρ σ u)
  let L := edgeL (z u) ρ σ
  let V := edgeV (z u) ρ σ
  have hB : B = 1-R*H := baseSecond_matrix_moment z ρ σ u
  have hdet : IsUnit B.det := baseSecond_isUnit_det z ρ σ hz hv hρ hσ u
  have hH : H = -L+L*R*H+(1/(z u)) • (V*J) :=
    hsMoment_edge_matrix_identity z ρ σ u (hz u).ne' hv.ne'
  have he : H = -L*B+(1/(z u)) • (V*J) := by
    rw [hH, hB]
    noncomm_ring
  have hc : (2*π/(z u))*(2*π)⁻¹ = 1/(z u) := by field_simp
  have hT : Matrix.of (edgeSeedLeft (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))) =
      1+H*B⁻¹*R := by
    rw [edgeSeedLeft_matrix, baseSeed_matrix]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul, hc]
    change 1-L*R+(1/(z u)) • (V*(J*B⁻¹)*R) = 1+H*B⁻¹*R
    rw [he]
    rw [add_mul, add_mul]
    rw [Matrix.mul_nonsing_inv_cancel_right B (-L) hdet]
    simp only [smul_mul_assoc, Matrix.mul_assoc, neg_mul]
    module
  have hright : Matrix.of (edgeSeedLeft (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))) *
      (Matrix.of (baseFirst z ρ σ u)).transpose = 1 := by
    rw [hT, baseFirst_transpose_matrix_moment]
    rw [hB] at hdet ⊢
    exact dual_resolvent_right_inverse H R hdet
  have hdF : IsUnit ((Matrix.of (baseFirst z ρ σ u)).transpose).det := by
    rw [Matrix.det_transpose]
    convert! baseFirst_isUnit_det z ρ σ hz hv hρ hσ u using 1
  have hinv := congrArg (fun M => M*((Matrix.of (baseFirst z ρ σ u)).transpose)⁻¹) hright
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hdF, Matrix.one_mul,
    ← Matrix.transpose_nonsing_inv] at hinv
  exact hinv

theorem firstOrderDt_matrix (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (u : ι) :
    Matrix.of (firstOrderDt z ρ σ K u) = (2*π/(z u)) •
      (Matrix.of (K u)*(Matrix.of (baseFirst z ρ σ u))⁻¹) := by
  unfold firstOrderDt
  rw [rightBlock_matrix]
  change Matrix.of (firstOrderSource z K u)*(Matrix.of (baseFirst z ρ σ u))⁻¹ = _
  have he : Matrix.of (firstOrderSource z K u) = (2*π/(z u)) • Matrix.of (K u) := by
    ext i j
    simp only [Matrix.of_apply, firstOrderSource, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he, smul_mul_assoc]

/-- The actual lower-edge Q increment is a two-sided actual HS-block
amplitude. Full independent DP DCF identification remains separate. -/
theorem edgeIncrement_firstOrderDt_matrix (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    Matrix.of (fun i j => edgeIncrement (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) i j) =
      (2*π/(z u)) • (((Matrix.of (baseFirst z ρ σ u))⁻¹).transpose *
        Matrix.of (K u)*(Matrix.of (baseFirst z ρ σ u))⁻¹) := by
  have he : Matrix.of (fun i j => edgeIncrement (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) i j) =
      Matrix.of (edgeSeedLeft (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))) *
        Matrix.of (firstOrderDt z ρ σ K u) := by
    ext i j
    exact edgeIncrement_eq_left_mul (z u) (hz u).ne' ρ σ hv.ne' _ _ i j
  rw [he, edgeSeedLeft_eq_inverse_transpose z ρ σ hz hv hρ hσ u,
    firstOrderDt_matrix, mul_smul_comm, Matrix.mul_assoc]

theorem edgeIncrement_firstOrderDt_symmetric (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (u : ι) (i j : Fin N) :
    edgeIncrement (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) i j =
    edgeIncrement (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) j i := by
  have hKM : (Matrix.of (K u)).transpose = Matrix.of (K u) := by
    ext a b
    exact hK u b a
  have hm := edgeIncrement_firstOrderDt_matrix z ρ σ K hz hv hρ hσ u
  have he : (Matrix.of (fun a b => edgeIncrement (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) a b)).transpose =
      Matrix.of (fun a b => edgeIncrement (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
        (Matrix.of (firstOrderDt z ρ σ K u)) a b) := by
    rw [hm, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hKM, Matrix.mul_assoc]
  exact congrFun (congrFun he j) i

theorem q_lower_edge (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j : Fin N) (hσ : 0 ≤ σ i) :
    q z σ A qp W C i j (edgeLo σ i j) =
      -σ i*qp i j+σ i^2/2*A j+∑ u, (W u i j+C u i j) := by
  have he : edgeLo σ i j-edgeHi σ i j = -σ i := by unfold edgeLo edgeHi; ring
  have hlo : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith
  simp only [q, lt_self_iff_false, if_false, hlo, if_true, sub_self, mul_zero,
    neg_zero, exp_zero, mul_one, he]
  ring

theorem q_lower_edge_increment (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (i j : Fin N) (hσ : 0 ≤ σ i) :
    q z σ (amplitudeA z ρ σ D G) (amplitudeQp z ρ σ D G)
      (W z ρ D G) (C z ρ σ D G) i j (edgeLo σ i j) -
    q z σ (amplitudeA z ρ σ 0 G) (amplitudeQp z ρ σ 0 G)
      (W z ρ 0 G) (C z ρ σ 0 G) i j (edgeLo σ i j) =
      ∑ u, edgeIncrement (z u) ρ σ (Matrix.of (G u)) (Matrix.of (D u)) i j := by
  rw [q_lower_edge z σ _ _ _ _ i j hσ, q_lower_edge z σ _ _ _ _ i j hσ]
  simp only [amplitudeA_zero, amplitudeQp_zero, W, C, Pi.zero_apply, Wt_zero_of_Dt_zero, Ct_zero_of_Dt_zero,
    add_zero, Finset.sum_const_zero]
  unfold amplitudeA amplitudeQp edgeIncrement
  have hGM : ∀ u, Matrix.of (G u) = G u := fun u => rfl
  have hDM : ∀ u, Matrix.of (D u) = D u := fun u => rfl
  simp_rw [hGM, hDM]
  simp only [Wt, Ct, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.sum_const_zero, sub_zero]

/-- Actual Q-value derivative at its lower support edge, with the G direction
eliminated internally by the zero Dt seed. -/
theorem q_lower_edge_hasDerivAt_seed (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G0 : TailMatrix ι N) (ψ : ℝ → TailMatrix ι N × TailMatrix ι N)
    (d : TailMatrix ι N × TailMatrix ι N) (h0 : ψ 0 = (0, G0))
    (hd : HasDerivAt ψ d 0) (i j : Fin N) (hσ : 0 ≤ σ i) :
    HasDerivAt (fun τ => q z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) i j (edgeLo σ i j))
      (∑ u, edgeIncrement (z u) ρ σ (Matrix.of (G0 u)) (Matrix.of (d.1 u)) i j) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
    (bhCoefficient_hasDerivAt_seed z ρ σ G0 ψ d h0 hd i j b).mul_const
      (basisQ z σ b i j (edgeLo σ i j)))
  have he : (∑ b, coefficientSlope z ρ σ d.1 G0 i j b * basisQ z σ b i j (edgeLo σ i j)) =
      ∑ u, edgeIncrement (z u) ρ σ (Matrix.of (G0 u)) (Matrix.of (d.1 u)) i j := by
    rw [← q_lower_edge_increment z ρ σ d.1 G0 i j hσ,
      q_eq_basis, q_eq_basis]
    simp only [coefficientSlope, bhCoefficient, sub_mul, Finset.sum_sub_distrib]
  rw [he] at h
  simp_rw [q_eq_basis]
  exact h

def dressedEdgeSlope (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (u : ι) : Matrix (Fin N) (Fin N) ℝ :=
  (2*π/(z u)) • (((Matrix.of (baseFirst z ρ σ u))⁻¹).transpose *
    Matrix.of (K u)*(Matrix.of (baseFirst z ρ σ u))⁻¹)

/-- Along any differentiable actual local root germ through the PY seed,
the lower-edge derivative is the explicit sum of two-sided HS amplitudes. -/
theorem q_lower_edge_hasDerivAt_of_family (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, baseSeed z ρ σ))
    (hr : ∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2)
    (hd : HasDerivAt ψ d 0) (i j : Fin N) :
    HasDerivAt (fun τ => q z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) i j (edgeLo σ i j))
      (∑ u, dressedEdgeSlope z ρ σ K u i j) 0 := by
  have h := q_lower_edge_hasDerivAt_seed z ρ σ (baseSeed z ρ σ) ψ d h0 hd i j (hσ i).le
  rw [firstOrderDt_eq_of_family z ρ σ K hz hv hρ hσ ψ d h0 hr hd] at h
  have he : (∑ u, edgeIncrement (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) i j) = ∑ u, dressedEdgeSlope z ρ σ K u i j := by
    apply Finset.sum_congr rfl
    intro u _
    exact congrFun (congrFun (edgeIncrement_firstOrderDt_matrix z ρ σ K hz hv hρ hσ u) i) j
  rw [he] at h
  exact h

/-- Existence of the actual local root family and of its explicit lower-edge
derivatives, with no root-family or derivative-existence premise. -/
theorem exists_contDiffAt_root_with_lower_edge_slope (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      ∀ i j, HasDerivAt (fun τ => q z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
        (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
        (C z ρ σ (ψ τ).1 (ψ τ).2) i j (edgeLo σ i j))
        (∑ u, dressedEdgeSlope z ρ σ K u i j) 0 := by
  obtain ⟨ψ, h0, hr, hc⟩ := exists_contDiffAt_root z ρ σ K hz hv hρ hσ
  have hd := (hc.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
  exact ⟨ψ, h0, hr, hc, fun i j =>
    q_lower_edge_hasDerivAt_of_family z ρ σ K hz hv hρ hσ ψ _ h0 hr hd i j⟩

theorem dressedEdgeSlope_symmetric (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j = K u j i) (u : ι) (i j : Fin N) :
    dressedEdgeSlope z ρ σ K u i j = dressedEdgeSlope z ρ σ K u j i := by
  have hk : (Matrix.of (K u)).transpose = Matrix.of (K u) := by ext a b; exact hK u b a
  have hm : (dressedEdgeSlope z ρ σ K u).transpose = dressedEdgeSlope z ρ σ K u := by
    unfold dressedEdgeSlope
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hk, Matrix.mul_assoc]
  exact congrFun (congrFun hm j) i

/-- Pair skew of the actual lower-edge Q values has zero first derivative
on the canonical local branch when every tail strength matrix is symmetric. -/
theorem q_lower_edge_skew_hasDerivAt_of_family (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, baseSeed z ρ σ))
    (hr : ∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2)
    (hd : HasDerivAt ψ d 0) (i j : Fin N) :
    HasDerivAt (fun τ =>
      q z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
        (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j (edgeLo σ i j) -
      q z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
        (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) j i (edgeLo σ j i)) 0 0 := by
  have hi := q_lower_edge_hasDerivAt_of_family z ρ σ K hz hv hρ hσ ψ d h0 hr hd i j
  have hj := q_lower_edge_hasDerivAt_of_family z ρ σ K hz hv hρ hσ ψ d h0 hr hd j i
  have he : (∑ u, dressedEdgeSlope z ρ σ K u i j) = ∑ u, dressedEdgeSlope z ρ σ K u j i :=
    Finset.sum_congr rfl (fun u _ => dressedEdgeSlope_symmetric z ρ σ K hK u i j)
  have h := hi.sub hj
  rw [he, sub_self] at h
  convert! h using 1

end FMSA.ExactMSA.MultiTailMixture
