import MSAConvergence.TracerWeightedRowAlgebra
import MSAConvergence.TracerActualRowEnergy

/-! Identify the genuine physical right-multiplied OZ row with the
transposed positive covariance action used by the forcing estimates. -/
noncomputable section
open Matrix FMSA.HardSphere FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerBaseCField FMSA.Convergence.TracerWeightedRowAlgebra
open FMSA.Convergence.TracerIntegratedEnergyIdentity
open FMSA.Convergence.TracerCoreTrialField FMSA.Convergence.TracerTailSpectralBound
open FMSA.Convergence.TracerCoreForcingBound FMSA.Convergence.TracerTailForcingBound
open FMSA.Convergence.TracerBathFactorBound
open FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerActualPointwiseForcing
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The ACTUAL c/h row at nonzero real frequency is a covariance response
on its density-weighted column vector, including zero-density tracer rows. -/
theorem actual_weighted_row_OZ (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hs : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) (w : ℝ) (hw : w ≠ 0) :
    let c : Fin N → ℝ := fun j => w*radial_fourier
      (orderedRadialCorrelation z rho sigma K D G i j) (2*Real.pi*w)
    let h : Fin N → ℝ := fun j => w*radial_fourier
      (nonlinearH z rho sigma D G i j) (2*Real.pi*w)
    weightedRealRow rho h =
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)).transpose *ᵥ
        weightedRealRow rho c := by
  dsimp only
  let k : ℝ := 2*Real.pi*w
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
  have hrow := actual_row_OZ_structure z hz rho sigma hρ hs hv K D G
    hK hroot hcanon k hk
  dsimp only at hrow
  have hj (j : Fin N) := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hrow
  funext j
  simp only [weightedRealRow,Matrix.mulVec,Matrix.transpose_apply]
  simp [Matrix.mul_apply,Matrix.diagonal_apply] at hj
  dsimp only [k] at hj
  calc
    (Real.sqrt (rho j) : ℂ) *
      ((w * radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w) : ℝ) : ℂ) =
      (w : ℂ) * ((Real.sqrt (rho j) : ℂ) *
        (radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w) : ℂ)) := by
      push_cast; ring
    _ = (w : ℂ) * (∑ l : Fin N,
      ((Real.sqrt (rho l) : ℂ) *
        (radial_fourier (orderedRadialCorrelation z rho sigma K D G i l)
          (2*Real.pi*w) : ℂ)) *
        (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)) l j) := by
      rw [mul_comm (Real.sqrt (rho j) : ℂ)
        (radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w) : ℂ), hj j]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ l : Fin N,
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)) l j *
        ((Real.sqrt (rho l) : ℂ) *
          ((w * radial_fourier (orderedRadialCorrelation z rho sigma K D G i l)
            (2*Real.pi*w) : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      push_cast
      ring


/-- The ACTUAL MSA hard-core and exterior-tail row forcing terms obey the
quarter-energy estimates at each nonzero frequency. The two remaining
quadratics are the exact transposed inverse- and direct-covariance trials. -/
theorem actual_row_forcing_pointwise_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hs : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) (w : ℝ) (hw : w ≠ 0) :
    let S := MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
    let c0 : Fin N → ℝ := fun j => w*radial_fourier
      (coreValue (edgeHi sigma i j)) (2*Real.pi*w)
    let t : Fin N → ℝ := fun j => w*radial_fourier
      (tailField z (edgeHi sigma i j) (fun u => K u i j)) (2*Real.pi*w)
    rowCoreForcing z rho sigma K D G i w ≤
      rowEnergy z rho sigma K D G i w/4 +
      (weightedRealRow rho c0 ⬝ᵥ star ((S.transpose)⁻¹ *ᵥ weightedRealRow rho c0)).re ∧
    rowTailForcing z rho sigma K D G i w ≤
      rowEnergy z rho sigma K D G i w/4 +
      (star (weightedRealRow rho t) ⬝ᵥ (S.transpose *ᵥ weightedRealRow rho t)).re := by
  let c : Fin N → ℝ := fun j => w*radial_fourier
    (orderedRadialCorrelation z rho sigma K D G i j) (2*Real.pi*w)
  let h : Fin N → ℝ := fun j => w*radial_fourier
    (nonlinearH z rho sigma D G i j) (2*Real.pi*w)
  let c0 : Fin N → ℝ := fun j => w*radial_fourier
    (coreValue (edgeHi sigma i j)) (2*Real.pi*w)
  let t : Fin N → ℝ := fun j => w*radial_fourier
    (tailField z (edgeHi sigma i j) (fun u => K u i j)) (2*Real.pi*w)
  let S := MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
  have hF : IsUnit (physicalFactor z rho sigma D G (2*Real.pi*w)) :=
    FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
      z rho sigma hρ (D,G) (2*Real.pi*w) (hcanon _ (by simp))
  have hpos : S.PosDef :=
    MatrixOZPairing.actual_structure_matrix_posDef z hz rho sigma K D G
      hρ hs hv hroot hK (2*Real.pi*w) hF
  have hrow : weightedRealRow rho h = S.transpose *ᵥ weightedRealRow rho c :=
    actual_weighted_row_OZ z hz rho sigma hρ hs hv K D G hK hroot hcanon i w hw
  have hb := weighted_real_row_forcing_bounds rho hρ S hpos c h c0 t hrow
  have hE : (∑ j : Fin N, rho j*c j*h j) =
      rowEnergy z rho sigma K D G i w := by
    simp only [rowEnergy,c,h]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hC : (∑ j : Fin N, rho j*c j*c0 j) =
      rowCoreForcing z rho sigma K D G i w := by
    simp only [rowCoreForcing,c,c0]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hT : (∑ j : Fin N, rho j*t j*h j) =
      rowTailForcing z rho sigma K D G i w := by
    simp only [rowTailForcing,t,h]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hE,hC,hT] at hb
  exact hb


/-- The actual pointwise MSA forcing inequalities expressed directly in
the physical Gram denominator and structure matrix used by the uniform
integral budgets. No density is divided, so tracer rows remain included. -/
theorem actual_row_forcing_physical_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hs : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) (w : ℝ) (hw : w ≠ 0) :
    let v : Fin N → ℂ := fun a => coreTrialVector rho sigma i a w
    let t : Fin N → ℂ := fun a => tailTrialVector z rho sigma K i a w
    let Den := MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w)
    let S := MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
    rowCoreForcing z rho sigma K D G i w ≤
      rowEnergy z rho sigma K D G i w/4 + (star v ⬝ᵥ (Den *ᵥ v)).re ∧
    rowTailForcing z rho sigma K D G i w ≤
      rowEnergy z rho sigma K D G i w/4 + (star t ⬝ᵥ (S *ᵥ t)).re := by
  let c0 : Fin N → ℝ := fun j => w*radial_fourier
    (coreValue (edgeHi sigma i j)) (2*Real.pi*w)
  let t0 : Fin N → ℝ := fun j => w*radial_fourier
    (tailField z (edgeHi sigma i j) (fun u => K u i j)) (2*Real.pi*w)
  let S := MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
  let Den := MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w)
  let v : Fin N → ℂ := fun a => coreTrialVector rho sigma i a w
  let t : Fin N → ℂ := fun a => tailTrialVector z rho sigma K i a w
  have hvtrial : weightedRealRow rho c0 = v := rfl
  have ht : weightedRealRow rho t0 = t := rfl
  have hqcore := weighted_real_row_inverse_transpose_re S rho c0
  have hqtail := weighted_real_row_quadratic_transpose S rho t0
  have hinv : S⁻¹ = Den := actual_structure_inverse_eq_denominator
    z hz rho sigma hρ hs hv K D G hK hroot hcanon (2*Real.pi*w)
  have hb := actual_row_forcing_pointwise_bounds z hz rho sigma hρ hs hv
    K D G hK hroot hcanon i w hw
  dsimp only at hb
  rw [hqcore, congrArg Complex.re hqtail, hvtrial, ht, hinv] at hb
  exact hb

end FMSA.Convergence.TracerActualPointwiseForcing
/-- info: 'FMSA.Convergence.TracerActualPointwiseForcing.actual_weighted_row_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActualPointwiseForcing.actual_weighted_row_OZ
/-- info: 'FMSA.Convergence.TracerActualPointwiseForcing.actual_row_forcing_pointwise_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActualPointwiseForcing.actual_row_forcing_pointwise_bounds
/-- info: 'FMSA.Convergence.TracerActualPointwiseForcing.actual_row_forcing_physical_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActualPointwiseForcing.actual_row_forcing_physical_bounds
