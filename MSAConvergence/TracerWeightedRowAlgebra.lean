import MSAConvergence.TracerPointwiseForcingYoung

/-! Exact real-to-complex algebra for density-weighted row spectra. -/
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open FMSA.Convergence.TracerPointwiseForcingYoung
open FMSA.Convergence.TracerEnergyCauchy
namespace FMSA.Convergence.TracerWeightedRowAlgebra
variable {N : ℕ}

def weightedRealRow (rho : Fin N → ℝ) (f : Fin N → ℝ) (j : Fin N) : ℂ :=
  (Real.sqrt (rho j) : ℂ) * (f j : ℂ)

/-- The complex inner product of real weighted spectral rows is exactly
the physical density-weighted real sum. -/
theorem weighted_real_row_pair (rho : Fin N → ℝ) (hρ : ∀ j, 0 ≤ rho j)
    (f g : Fin N → ℝ) :
    (star (weightedRealRow rho f) ⬝ᵥ weightedRealRow rho g).re =
      ∑ j : Fin N, rho j * f j * g j := by
  simp only [dotProduct,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [weightedRealRow,Pi.star_apply,Complex.star_def,
    Complex.conj_ofReal,← Complex.ofReal_mul,Complex.ofReal_re]
  calc
    _ = (Real.sqrt (rho j))^2 * f j * g j := by ring
    _ = _ := by rw [Real.sq_sqrt (hρ j)]


/-- Both pointwise forcing terms for an arbitrary real right-multiplied
OZ row obey quarter-energy bounds in the exact transposed covariance metric. -/
theorem weighted_real_row_forcing_bounds
    (rho : Fin N → ℝ) (hρ : ∀ j, 0 ≤ rho j)
    (S : Matrix (Fin N) (Fin N) ℂ) (hS : S.PosDef)
    (c h c0 t : Fin N → ℝ)
    (hrow : weightedRealRow rho h = S.transpose *ᵥ weightedRealRow rho c) :
    (∑ j : Fin N, rho j*c j*c0 j) ≤
      (∑ j : Fin N, rho j*c j*h j)/4 +
      (weightedRealRow rho c0 ⬝ᵥ
        star ((S.transpose)⁻¹ *ᵥ weightedRealRow rho c0)).re ∧
    (∑ j : Fin N, rho j*t j*h j) ≤
      (∑ j : Fin N, rho j*c j*h j)/4 +
      (star (weightedRealRow rho t) ⬝ᵥ
        (S.transpose *ᵥ weightedRealRow rho t)).re := by
  have hcore := core_forcing_le_quarter_energy_add_inverse
    S.transpose hS.transpose (weightedRealRow rho c) (weightedRealRow rho c0)
  have htail := tail_forcing_le_quarter_energy_add_covariance
    S.transpose hS.transpose (weightedRealRow rho c) (weightedRealRow rho t)
  rw [← hrow] at hcore htail
  rw [weighted_real_row_pair rho hρ c c0,
    weighted_real_row_pair rho hρ c h] at hcore
  rw [weighted_real_row_pair rho hρ t h,
    weighted_real_row_pair rho hρ c h] at htail
  exact ⟨hcore,htail⟩


/-- Transposing a matrix does not alter a quadratic trial built from a
real density-weighted spectral row. -/
theorem weighted_real_row_quadratic_transpose
    (A : Matrix (Fin N) (Fin N) ℂ) (rho f : Fin N → ℝ) :
    star (weightedRealRow rho f) ⬝ᵥ (A.transpose *ᵥ weightedRealRow rho f) =
      star (weightedRealRow rho f) ⬝ᵥ (A *ᵥ weightedRealRow rho f) := by
  let v : Fin N → ℝ := fun j => Real.sqrt (rho j)*f j
  have hv (j : Fin N) : weightedRealRow rho f j = (v j : ℂ) := by
    simp [weightedRealRow,v]
  have hvfun : weightedRealRow rho f = (fun j => (v j : ℂ)) := funext hv
  rw [hvfun]
  simpa only [dotProduct,mulVec,Matrix.transpose_apply,Finset.mul_sum,mul_assoc,Pi.star_apply] using
    real_vector_quadratic_transpose_eq A v


/-- For a real trial row, the inverse of the transposed right-covariance
has exactly the same real quadratic as the untransposed inverse. -/
theorem weighted_real_row_inverse_transpose_re
    (A : Matrix (Fin N) (Fin N) ℂ) (rho f : Fin N → ℝ) :
    (weightedRealRow rho f ⬝ᵥ
      star ((A.transpose)⁻¹ *ᵥ weightedRealRow rho f)).re =
    (star (weightedRealRow rho f) ⬝ᵥ
      (A⁻¹ *ᵥ weightedRealRow rho f)).re := by
  let v := weightedRealRow rho f
  have hstar : (v ⬝ᵥ star ((A.transpose)⁻¹ *ᵥ v)).re =
      (star v ⬝ᵥ ((A.transpose)⁻¹ *ᵥ v)).re := by
    rw [Matrix.dotProduct_star,dotProduct_comm]
    simp only [Complex.star_def,Complex.conj_re]
  rw [hstar]
  rw [← Matrix.transpose_nonsing_inv A]
  exact congrArg Complex.re (weighted_real_row_quadratic_transpose (A⁻¹) rho f)

end FMSA.Convergence.TracerWeightedRowAlgebra
/-- info: 'FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_pair
/-- info: 'FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_forcing_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_forcing_bounds
/-- info: 'FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_quadratic_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_quadratic_transpose
/-- info: 'FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_inverse_transpose_re' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerWeightedRowAlgebra.weighted_real_row_inverse_transpose_re
