import MSAConvergence.TracerEnergyCauchy
/-! Actual nonnegative tracer-row spectral energy at every nonzero real
frequency, derived from the physical c/h OZ identity and covariance. -/
open Matrix
open scoped ComplexOrder BigOperators
open FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerBaseCField FMSA.Convergence.TracerEnergyCauchy
open FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
noncomputable section
namespace FMSA.Convergence.TracerActualRowEnergy
variable {N : ℕ} {T : Type*} [Fintype T]
/-- The actual ordered MSA c/h radial Fourier row has nonnegative
density-weighted energy even when the row species has zero density. -/
theorem actual_tracer_row_energy_nonneg (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hs : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (k : ℝ) (hk : k ≠ 0) (i : Fin N) :
    0 ≤ ∑ j : Fin N, rho j *
      FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k *
      FMSA.HardSphere.radial_fourier (nonlinearH z rho sigma D G i j) k := by
  let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun a b =>
    (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z rho sigma K D G a b) k : ℂ))
  let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun a b =>
    (FMSA.HardSphere.radial_fourier (nonlinearH z rho sigma D G a b) k : ℂ))
  let Q : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun a => (Real.sqrt (rho a) : ℂ))
  let S := MatrixOZPairing.structureMatrix z rho sigma K D G k
  have hrow : H*Q=(C*Q)*S :=
    actual_row_OZ_structure z hz rho sigma hρ hs hv K D G hK hroot hcanon k hk
  have hF : IsUnit (physicalFactor z rho sigma D G k) :=
    FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
      z rho sigma hρ (D,G) k (hcanon _ (by simp))
  have hpos : S.PosDef :=
    MatrixOZPairing.actual_structure_matrix_posDef z hz rho sigma K D G
      hρ hs hv hroot hK k hF
  have hp := positive_row_energy (C*Q) (H*Q) S hpos hrow i
  have he (j : Fin N) : star ((C*Q) i j) * (H*Q) i j =
      ((rho j * FMSA.HardSphere.radial_fourier
        (orderedRadialCorrelation z rho sigma K D G i j) k *
        FMSA.HardSphere.radial_fourier (nonlinearH z rho sigma D G i j) k : ℝ) : ℂ) := by
    simp only [Matrix.mul_diagonal, C,H,Q,Matrix.of_apply]
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    apply congrArg (fun x : ℝ => (x : ℂ))
    calc
      _ = (Real.sqrt (rho j))^2 *
        FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k *
        FMSA.HardSphere.radial_fourier (nonlinearH z rho sigma D G i j) k := by ring
      _ = _ := by rw [Real.sq_sqrt (hρ j)]
  simp_rw [he] at hp
  simpa only [Complex.re_sum, Complex.ofReal_re] using hp

/-- Recover the density-weighted actual c row from the actual h row using
the uniformly controlled physical Gram denominator. No density is divided. -/
theorem actual_tracer_row_source_eq_response_denominator (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hs : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (k : ℝ) (hk : k ≠ 0) :
    let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun a b =>
      (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z rho sigma K D G a b) k : ℂ))
    let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun a b =>
      (FMSA.HardSphere.radial_fourier (nonlinearH z rho sigma D G a b) k : ℂ))
    let Q : Matrix (Fin N) (Fin N) ℂ :=
      Matrix.diagonal (fun a => (Real.sqrt (rho a) : ℂ))
    C * Q = (H * Q) * MatrixOZPairing.radialDenominator z rho sigma K D G k := by
  dsimp only
  have hrow := actual_row_OZ_structure z hz rho sigma hρ hs hv K D G hK hroot hcanon k hk
  have hF : IsUnit (physicalFactor z rho sigma D G k) :=
    FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
      z rho sigma hρ (D,G) k (hcanon _ (by simp))
  have hpos := MatrixOZPairing.actual_structure_matrix_posDef z hz rho sigma K D G
    hρ hs hv hroot hK k hF
  have h := positive_row_source_eq_response_mul_inverse _ _ _ hpos hrow
  rw [FMSA.Convergence.TracerBathFactorBound.actual_structure_inverse_eq_denominator
    z hz rho sigma hρ hs hv K D G hK hroot hcanon k] at h
  exact h
end FMSA.Convergence.TracerActualRowEnergy
/-- info: 'FMSA.Convergence.TracerActualRowEnergy.actual_tracer_row_energy_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActualRowEnergy.actual_tracer_row_energy_nonneg
/-- info: 'FMSA.Convergence.TracerActualRowEnergy.actual_tracer_row_source_eq_response_denominator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActualRowEnergy.actual_tracer_row_source_eq_response_denominator
