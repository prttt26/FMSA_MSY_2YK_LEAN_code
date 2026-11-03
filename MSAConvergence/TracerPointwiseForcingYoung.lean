import MSAConvergence.TracerIntegratedEnergyIdentity

/-! Pointwise positive-matrix Young estimates for the two physical tracer-row
forcing terms. -/
noncomputable section
open Matrix
open scoped ComplexOrder BigOperators
open FMSA.Convergence.TracerEnergyCauchy
open FMSA.Convergence.TracerEnergyYoung
namespace FMSA.Convergence.TracerPointwiseForcingYoung
variable {N : ℕ}

/-- The inverse covariance quadratic is nonnegative in the real order. -/
theorem inverse_quadratic_re_nonneg (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.PosDef) (v : Fin N → ℂ) :
    0 ≤ (v ⬝ᵥ star (A⁻¹*ᵥ v)).re := by
  have h := hA.inv.posSemidef.re_dotProduct_nonneg v
  rw [Matrix.dotProduct_star, dotProduct_comm]
  simpa only [Complex.star_def, Complex.conj_re, RCLike.re_to_complex] using h

/-- A hard-core test vector can spend at most one quarter of the row energy,
plus its actual inverse-covariance quadratic. -/
theorem core_forcing_le_quarter_energy_add_inverse
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (x v : Fin N → ℂ) :
    (star x ⬝ᵥ v).re ≤
      (star x ⬝ᵥ (A*ᵥ x)).re/4 +
      (v ⬝ᵥ star (A⁻¹*ᵥ v)).re := by
  have hE := hA.posSemidef.re_dotProduct_nonneg x
  have hQ := inverse_quadratic_re_nonneg A hA v
  calc
    _ ≤ Real.sqrt ((star x ⬝ᵥ (A*ᵥ x)).re) *
      Real.sqrt ((v ⬝ᵥ star (A⁻¹*ᵥ v)).re) :=
      weighted_matrix_pair_re_le A hA x v
    _ ≤ _ := sqrt_mul_le_quarter_energy_add _ _ hE hQ

/-- The actual covariance quadratic similarly controls the exterior-tail
forcing term, with the same quarter-energy cost. -/
theorem tail_forcing_le_quarter_energy_add_covariance
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (x t : Fin N → ℂ) :
    (star t ⬝ᵥ (A*ᵥ x)).re ≤
      (star x ⬝ᵥ (A*ᵥ x)).re/4 +
      (star t ⬝ᵥ (A*ᵥ t)).re := by
  have hE := hA.posSemidef.re_dotProduct_nonneg x
  have hQ := hA.posSemidef.re_dotProduct_nonneg t
  calc
    _ ≤ ‖star t ⬝ᵥ (A*ᵥ x)‖ := Complex.re_le_norm _
    _ ≤ Real.sqrt ((star t ⬝ᵥ (A*ᵥ t)).re) *
      Real.sqrt ((star x ⬝ᵥ (A*ᵥ x)).re) :=
      positive_matrix_cross_norm_le_energy A hA t x
    _ = Real.sqrt ((star x ⬝ᵥ (A*ᵥ x)).re) *
      Real.sqrt ((star t ⬝ᵥ (A*ᵥ t)).re) := mul_comm _ _
    _ ≤ _ := sqrt_mul_le_quarter_energy_add _ _ hE hQ

end FMSA.Convergence.TracerPointwiseForcingYoung
/-- info: 'FMSA.Convergence.TracerPointwiseForcingYoung.inverse_quadratic_re_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerPointwiseForcingYoung.inverse_quadratic_re_nonneg
/-- info: 'FMSA.Convergence.TracerPointwiseForcingYoung.core_forcing_le_quarter_energy_add_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerPointwiseForcingYoung.core_forcing_le_quarter_energy_add_inverse
/-- info: 'FMSA.Convergence.TracerPointwiseForcingYoung.tail_forcing_le_quarter_energy_add_covariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerPointwiseForcingYoung.tail_forcing_le_quarter_energy_add_covariance
