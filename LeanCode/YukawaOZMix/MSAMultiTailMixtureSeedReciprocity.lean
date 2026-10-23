import LeanCode.YukawaOZMix.MSAMultiTailMixtureFirstOrder

/-! Reciprocity of the actual PY seed for arbitrary finite species.
This is a finite algebraic identity, not reciprocity of general BH roots. -/
noncomputable section
open Real FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def hsMoment (ρ σ : Fin N → ℝ) (s : ℝ) (i j : Fin N) : ℝ :=
  (1-s*σ i-exp (-s*σ i))/s^2 * Q0phys ρ σ i j +
  (1-s*σ i+(s*σ i)^2/2-exp (-s*σ i))/s^3 * Qppphys ρ σ j j

theorem baseSecond_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) (i j : Fin N) :
    baseSecond z ρ σ u i j = (if i=j then 1 else 0) - ρ i*hsMoment ρ σ (z u) i j := by
  simp only [baseSecond, secondBlock, dressedQhat_zero, hsTransform, hsMoment]
  have he : exp (z u*edgeLo σ i j)*exp (-z u*edgeLo σ i j) = 1 := by
    rw [← exp_add]
    simp
  have heρ : ρ i*exp (z u*edgeLo σ i j)*exp (-z u*edgeLo σ i j) = ρ i := by
    rw [mul_assoc, he, mul_one]
  simp only [← mul_assoc]
  rw [heρ]

theorem hsMoment_source_skew (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (l i j : Fin N) :
    hsMoment ρ σ (z u) l i * baseSource z ρ σ u l j -
      baseSource z ρ σ u l i * hsMoment ρ σ (z u) l j =
      -π^2/(vacMix ρ σ)^2/(z u)^2 * σ l^2 * (σ i-σ j) := by
  unfold hsMoment baseSource Q0phys Qppphys
  field_simp
  <;> ring

theorem baseSource_skew (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι)
    (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (i j : Fin N) :
    baseSource z ρ σ u i j - baseSource z ρ σ u j i =
      -π^2/(vacMix ρ σ)^2/(z u)^2 * xi2 ρ σ * (σ i-σ j) := by
  unfold baseSource Q0phys Qppphys
  field_simp
  <;> ring

/-- The recentered HS block is self-adjoint relative to its source. -/
theorem baseSecond_source_compatibility (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    (Matrix.of (baseSecond z ρ σ u)).transpose * Matrix.of (baseSource z ρ σ u) =
      (Matrix.of (baseSource z ρ σ u)).transpose * Matrix.of (baseSecond z ρ σ u) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, baseSecond_entry]
  have he : ∀ l : Fin N,
      ((if l=i then 1 else 0)-ρ l*hsMoment ρ σ (z u) l i)*baseSource z ρ σ u l j -
      baseSource z ρ σ u l i*((if l=j then 1 else 0)-ρ l*hsMoment ρ σ (z u) l j) =
      (if l=i then baseSource z ρ σ u l j else 0) -
      (if l=j then baseSource z ρ σ u l i else 0) -
      ρ l*(hsMoment ρ σ (z u) l i*baseSource z ρ σ u l j -
        baseSource z ρ σ u l i*hsMoment ρ σ (z u) l j) := by
    intro l
    split_ifs <;> ring
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simp_rw [he, hsMoment_source_skew z ρ σ u hz hv]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [baseSource_skew z ρ σ u hz hv]
  have hs : (∑ l, ρ l * (-π^2/(vacMix ρ σ)^2/(z u)^2 * σ l^2 * (σ i-σ j))) =
      -π^2/(vacMix ρ σ)^2/(z u)^2 * xi2 ρ σ * (σ i-σ j) := by
    unfold xi2
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hs, sub_self]

theorem source_inverse_symmetric (B J : Matrix (Fin N) (Fin N) ℝ)
    (hB : IsUnit B.det) (hcompat : B.transpose*J = J.transpose*B) :
    (J*B⁻¹).transpose = J*B⁻¹ := by
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  have hBT : IsUnit B.transpose.det := by simpa only [Matrix.det_transpose] using hB
  calc
    B.transpose⁻¹*J.transpose = (B.transpose⁻¹*J.transpose)*B*B⁻¹ :=
      (Matrix.mul_nonsing_inv_cancel_right B _ hB).symm
    _ = B.transpose⁻¹*(J.transpose*B)*B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = B.transpose⁻¹*(B.transpose*J)*B⁻¹ := by rw [← hcompat]
    _ = J*B⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left B.transpose J hBT]

theorem baseSeed_matrix (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    Matrix.of (baseSeed z ρ σ u) = (2*π)⁻¹ •
      (Matrix.of (baseSource z ρ σ u)*(Matrix.of (baseSecond z ρ σ u))⁻¹) := by
  ext i j
  simp only [Matrix.of_apply, baseSeed, Pi.smul_apply, smul_eq_mul, rightBlock_apply,
    inverseBlocks, Matrix.smul_apply, Matrix.mul_apply]

/-- The actual internally constructed PY seed is pair-symmetric for every
finite species count, positive rate and physical PY state. -/
theorem baseSeed_symmetric (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (i j : Fin N) :
    baseSeed z ρ σ u i j = baseSeed z ρ σ u j i := by
  have hm : (Matrix.of (baseSeed z ρ σ u)).transpose = Matrix.of (baseSeed z ρ σ u) := by
    rw [baseSeed_matrix, Matrix.transpose_smul]
    rw [source_inverse_symmetric (Matrix.of (baseSecond z ρ σ u)) (Matrix.of (baseSource z ρ σ u))
      (baseSecond_isUnit_det z ρ σ hz hvac hρ hσ u)
      (baseSecond_source_compatibility z ρ σ u (hz u).ne' hvac.ne')]
  exact congrFun (congrFun hm j) i

end FMSA.ExactMSA.MultiTailMixture
