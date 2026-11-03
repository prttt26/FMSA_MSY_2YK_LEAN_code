import MSAConvergence.TracerBathFactorBound
/-! A finite-dimensional weighted Cauchy–Schwarz inequality obtained from
the genuine positive structure matrix and its induced inner product. -/
open scoped ComplexOrder
open Matrix
noncomputable section
namespace FMSA.Convergence.TracerEnergyCauchy
variable {N : ℕ}

/-- Positive covariance controls the pairing with an inverse-covariance
trial vector, without inverting any species density. -/
theorem weighted_matrix_cauchy_schwarz (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef) (x y : Fin N → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤
      Real.sqrt ((star x ⬝ᵥ (A*ᵥ x)).re) *
      Real.sqrt ((y ⬝ᵥ star (A⁻¹*ᵥ y)).re) := by
  letI : SeminormedAddCommGroup (Fin N → ℂ) := A.toSeminormedAddCommGroup hA.posSemidef
  letI : InnerProductSpace ℂ (Fin N → ℂ) := A.toInnerProductSpace hA.posSemidef
  have h := norm_inner_le_norm (𝕜 := ℂ) x (A⁻¹ *ᵥ y)
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) x, norm_eq_sqrt_re_inner (𝕜 := ℂ) (A⁻¹ *ᵥ y)] at h
  change ‖(A*ᵥ (A⁻¹*ᵥ y)) ⬝ᵥ star x‖ ≤
    Real.sqrt (((A*ᵥ x) ⬝ᵥ star x).re) *
    Real.sqrt (((A*ᵥ (A⁻¹*ᵥ y)) ⬝ᵥ star (A⁻¹*ᵥ y)).re) at h
  have hu : IsUnit A := hA.isUnit
  have hinv : A*ᵥ (A⁻¹*ᵥ y) = y := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hu), Matrix.one_mulVec]
  rw [hinv] at h
  simpa only [dotProduct_comm] using h

/-- Real forcing terms obey the same weighted energy estimate. -/
theorem weighted_matrix_pair_re_le (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.PosDef) (x y : Fin N → ℂ) :
    (star x ⬝ᵥ y).re ≤
      Real.sqrt ((star x ⬝ᵥ (A*ᵥ x)).re) *
      Real.sqrt ((y ⬝ᵥ star (A⁻¹*ᵥ y)).re) :=
  (Complex.re_le_norm _).trans (weighted_matrix_cauchy_schwarz A hA x y)

/-- A right-multiplied matrix row has nonnegative energy against its source
row when the right factor is positive definite. The transpose is essential:
row multiplication acts on column vectors through the transpose. -/
theorem positive_row_energy (C H S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.PosDef) (hrow : H = C * S) (i : Fin N) :
    0 ≤ (∑ j : Fin N, star (C i j)*H i j).re := by
  let x : Fin N → ℂ := fun j => C i j
  have he : (fun j => H i j) = S.transpose *ᵥ x := by
    funext j
    rw [hrow]
    simp only [Matrix.mul_apply,Matrix.mulVec,Matrix.transpose_apply,x]
    change (∑ l : Fin N, C i l*S l j) = (∑ l : Fin N, S l j*C i l)
    exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
  have hp := hS.transpose.posSemidef.re_dotProduct_nonneg x
  change 0 ≤ (star x ⬝ᵥ (fun j => H i j)).re
  rw [he]
  exact hp

/-- Invert a positive right factor in the row transfer equation. -/
theorem positive_row_source_eq_response_mul_inverse
    (C H S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.PosDef) (hrow : H = C * S) :
    C = H * S⁻¹ := by
  rw [hrow, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit),
    Matrix.mul_one]

/-- Cauchy–Schwarz for two vectors in the same actual positive covariance
metric; used for the exterior-tail cross forcing term. -/
theorem positive_matrix_cross_norm_le_energy
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (x y : Fin N → ℂ) :
    ‖star x ⬝ᵥ (A*ᵥ y)‖ ≤
      Real.sqrt ((star x ⬝ᵥ (A*ᵥ x)).re) *
      Real.sqrt ((star y ⬝ᵥ (A*ᵥ y)).re) := by
  letI : SeminormedAddCommGroup (Fin N → ℂ) := A.toSeminormedAddCommGroup hA.posSemidef
  letI : InnerProductSpace ℂ (Fin N → ℂ) := A.toInnerProductSpace hA.posSemidef
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) x,
    norm_eq_sqrt_re_inner (𝕜 := ℂ) y] at h
  change ‖(A*ᵥ y) ⬝ᵥ star x‖ ≤
    Real.sqrt (((A*ᵥ x) ⬝ᵥ star x).re) *
    Real.sqrt (((A*ᵥ y) ⬝ᵥ star y).re) at h
  simpa only [dotProduct_comm] using h

/-- For a real spectral trial vector, transposing the covariance matrix
does not change its quadratic energy. -/
theorem real_vector_quadratic_transpose_eq
    (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℝ) :
    (∑ a : Fin N, ∑ b : Fin N,
      star ((v a : ℝ) : ℂ)*A.transpose a b*(v b : ℂ)) =
    (∑ a : Fin N, ∑ b : Fin N,
      star ((v a : ℝ) : ℂ)*A a b*(v b : ℂ)) := by
  simp only [Complex.star_def,Complex.conj_ofReal,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end FMSA.Convergence.TracerEnergyCauchy
/-- info: 'FMSA.Convergence.TracerEnergyCauchy.weighted_matrix_cauchy_schwarz' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyCauchy.weighted_matrix_cauchy_schwarz
/-- info: 'FMSA.Convergence.TracerEnergyCauchy.weighted_matrix_pair_re_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyCauchy.weighted_matrix_pair_re_le
/-- info: 'FMSA.Convergence.TracerEnergyCauchy.positive_row_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyCauchy.positive_row_energy
/-- info: 'FMSA.Convergence.TracerEnergyCauchy.positive_row_source_eq_response_mul_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyCauchy.positive_row_source_eq_response_mul_inverse
/-- info: 'FMSA.Convergence.TracerEnergyCauchy.positive_matrix_cross_norm_le_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyCauchy.positive_matrix_cross_norm_le_energy
/-- info: 'FMSA.Convergence.TracerEnergyCauchy.real_vector_quadratic_transpose_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyCauchy.real_vector_quadratic_transpose_eq
