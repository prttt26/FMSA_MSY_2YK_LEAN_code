import MSAConvergence.TracerTailForcingBound
/-! Real-frequency continuity of the actual physical structure matrix
from the continuous Gram denominator and canonical invertibility. -/
open MeasureTheory Set Real FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.TracerBathFactorBound
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped ComplexOrder
noncomputable section
namespace FMSA.Convergence.TracerStructureContinuity
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The true structure matrix is continuous at all real frequencies,
including the physical zero mode, for canonical reciprocal BH roots. -/
theorem actual_structure_matrix_continuous (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hs : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hroot : IsRoot z rho sigma K D G)
    (hK : ∀ u i j, K u i j = K u j i)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) :
    Continuous (fun k : ℝ => MatrixOZPairing.structureMatrix z rho sigma K D G k) := by
  let F : ℝ → Matrix (Fin N) (Fin N) ℂ := fun k =>
    MatrixOZPairing.radialDenominator z rho sigma K D G k
  have hFc : Continuous F := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact actual_denominator_entry_continuous z hz rho sigma hs K D G hroot i j
  have hunit (k : ℝ) : IsUnit (F k) := by
    have hphys : IsUnit (physicalFactor z rho sigma D G k) :=
      FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
        z rho sigma hρ (D,G) k (hcanon _ (by simp))
    exact (MatrixOZPairing.actual_radial_denominator_posDef z hz rho sigma K D G
      hρ hs hv hroot hK k hphys).isUnit
  have hIc : Continuous (fun k : ℝ => (F k)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro k
    have hd : (F k).det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hunit k))
    have hi : ContinuousAt Ring.inverse (F k).det := by
      change ContinuousAt (fun c : ℂ => Ring.inverse c) (F k).det
      simpa only [Ring.inverse_eq_inv] using (continuousAt_inv₀ hd)
    exact (continuousAt_matrix_inv (F k) hi).comp hFc.continuousAt
  exact hIc

end FMSA.Convergence.TracerStructureContinuity
/-- info: 'FMSA.Convergence.TracerStructureContinuity.actual_structure_matrix_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerStructureContinuity.actual_structure_matrix_continuous
