import LeanCode.HSMixture.MixtureDetGeneralN

/-!
# Closed-form inverse of the physical Baxter factor `Q̂₀` (Tang & Lu Appendix, Woodbury form)

Tang & Lu (Mol. Phys. 84, 89 (1995)) note the "one disadvantage" of their mixture OZ solution is the
inverse of the factor correlation matrix `[Q̂₀]⁻¹` (eq 15's `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹`), since "formalism
for the inverse of an arbitrary n×n matrix is not available".  But `Q̂₀ = I − U·V` is a **rank-2**
perturbation of the identity (`Q0_mat_phys_eq_one_sub_mul`), so the Sherman–Morrison–Woodbury identity
gives the closed form `[Q̂₀]⁻¹ = I + U·(I − V·U)⁻¹·V`, where `I − V·U` is a `2×2` matrix with
`det = det Q̂₀ ≥ 1 > 0` (`Q0_mat_phys_det_ge_one_N` + `Q0_mat_phys_det_eq_two_by_two`).  This is exactly
Tang & Lu's Appendix (A2–A7) result, obtained here for free from the existing rank-2 factorization.
-/

open Matrix
namespace FMSA.MatrixQ0

/-- **`Q̂₀ · (I + U·(I−V·U)⁻¹·V) = I`** — the Sherman–Morrison–Woodbury right inverse of the rank-2
`Q̂₀ = I − U·V`.  `I − V·U` is invertible since `det(I − V·U) = det Q̂₀ ≥ 1 > 0`. -/
theorem Q0_mat_phys_inv_closed_form {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    (Q0_mat_phys z sigma rho) *
      (1 + Umat z sigma rho * (1 - Vmat z sigma rho * Umat z sigma rho)⁻¹ * Vmat z sigma rho) = 1 := by
  have hge : 1 ≤ (Q0_mat_phys z sigma rho).det :=
    FMSA.MixtureGenN.Q0_mat_phys_det_ge_one_N hz hvac hrho hsigma
  have heq : (Q0_mat_phys z sigma rho).det = (1 - Vmat z sigma rho * Umat z sigma rho).det :=
    Q0_mat_phys_det_eq_two_by_two hz.ne' hvac.ne' hrho
  have hdet : IsUnit (1 - Vmat z sigma rho * Umat z sigma rho).det :=
    isUnit_iff_ne_zero.mpr (by rw [← heq]; linarith)
  rw [Q0_mat_phys_eq_one_sub_mul hz.ne' hvac.ne' hrho]
  set U := Umat z sigma rho
  set V := Vmat z sigma rho
  set W := (1 - V * U)⁻¹ with hWdef
  have hVU : (1 - V * U) * W = 1 := Matrix.mul_nonsing_inv _ hdet
  have expand : (1 - U * V) * (1 + U * W * V)
      = 1 - U * V + U * ((1 - V * U) * W) * V := by
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
  rw [expand, hVU, Matrix.mul_one]
  abel

/-- **Closed-form inverse `[Q̂₀]⁻¹ = I + U·(I − V·U)⁻¹·V`** (Tang & Lu Appendix, Woodbury form). -/
theorem Q0_mat_phys_inv_eq {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    (Q0_mat_phys z sigma rho)⁻¹
      = 1 + Umat z sigma rho * (1 - Vmat z sigma rho * Umat z sigma rho)⁻¹ * Vmat z sigma rho :=
  Matrix.inv_eq_right_inv (Q0_mat_phys_inv_closed_form hz hvac hrho hsigma)

/-! ### Tang & Lu eq (15) — solving the transformed first-order OZ equation for `Ĥ₁` -/

/-- **Tang & Lu eq (15), the algebraic assembly.**  From the transformed first-order OZ equation
`Q̂₀ᵀ·Ĥ₁·Q̂₀ = B₁` (eq 14) and the invertibility of `Q̂₀` (`det ≠ 0`), the first-order RDF is
`Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` — solved by inverting `Q̂₀ᵀ` on the left and `Q̂₀` on the right
(`nonsing_inv_mul` / `mul_nonsing_inv`). -/
theorem H1_eq_of_transformed {N : ℕ} (Q0 H1 B1 : Matrix (Fin N) (Fin N) ℝ)
    (hdet : IsUnit Q0.det) (heq : Q0ᵀ * H1 * Q0 = B1) :
    H1 = (Q0ᵀ)⁻¹ * B1 * Q0⁻¹ := by
  have hdetT : IsUnit (Q0ᵀ).det := (Matrix.det_transpose Q0) ▸ hdet
  have hL : (Q0ᵀ)⁻¹ * Q0ᵀ = 1 := Matrix.nonsing_inv_mul _ hdetT
  have hR : Q0 * Q0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  rw [← heq]
  simp only [Matrix.mul_assoc]
  rw [hR, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]

/-- **Tang & Lu eq (15) for the physical Baxter factor.**  With `Q̂₀ = Q0_mat_phys` (real `z > 0`,
`det ≥ 1 > 0`), the first-order OZ transform `Q̂₀ᵀ·Ĥ₁·Q̂₀ = B₁` yields `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`, and
with the closed-form inverse `[Q̂₀]⁻¹ = I + U(I−VU)⁻¹V` (`Q0_mat_phys_inv_eq`) this `Ĥ₁` is fully explicit
— the whole point of the Tang & Lu first-order mixture RDF. -/
theorem H1_eq_phys {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i)
    (H1 B1 : Matrix (Fin N) (Fin N) ℝ)
    (heq : (Q0_mat_phys z sigma rho)ᵀ * H1 * (Q0_mat_phys z sigma rho) = B1) :
    H1 = ((Q0_mat_phys z sigma rho)ᵀ)⁻¹ * B1 * (Q0_mat_phys z sigma rho)⁻¹ := by
  have hdet : IsUnit (Q0_mat_phys z sigma rho).det :=
    isUnit_iff_ne_zero.mpr
      (by linarith [FMSA.MixtureGenN.Q0_mat_phys_det_ge_one_N hz hvac hrho hsigma])
  exact H1_eq_of_transformed _ H1 B1 hdet heq

end FMSA.MatrixQ0
