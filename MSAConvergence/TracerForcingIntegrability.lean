import MSAConvergence.TracerSpectralL2
/-! Finite matrix pairings of genuine weighted spectral L2 fields with
measurable bounded multipliers, for the actual tracer core forcing. -/
open MeasureTheory FMSA.Convergence.TracerSpectralL2
open FMSA.Convergence.TracerBathFactorBound FMSA.Convergence.TracerCoreTrialField
open FMSA.Convergence.TracerTailSpectralBound FMSA.HardSphere
open FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Paper
open FMSA.Convergence.CanonicalInverseCovariance
noncomputable section
namespace FMSA.Convergence.TracerForcingIntegrability

/-- An L2 pair remains L1 after insertion of a bounded measurable scalar. -/
theorem l2_bounded_multiplier_integrable (f g m : ℝ → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hm : AEStronglyMeasurable m volume) (B : ℝ)
    (hbound : ∀ w, ‖m w‖ ≤ B) :
    Integrable (fun w : ℝ => star (f w)*m w*g w) := by
  have hfg : Integrable (fun w : ℝ => star (f w)*g w) := hf.star.integrable_mul hg
  have h := hfg.mul_bdd hm (ae_of_all _ hbound)
  have he : (fun w : ℝ => star (f w)*m w*g w) =
      (fun w : ℝ => (star (f w)*g w)*m w) := by
    funext w; ring
  rw [he]
  exact h

variable {N : ℕ}
/-- The same integrability holds for a finite matrix pairing. -/
theorem l2_matrix_pair_integrable (f g : Fin N → ℝ → ℂ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hf : ∀ i, MemLp (f i) 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hM : ∀ i j, AEStronglyMeasurable (fun w => M w i j) volume)
    (B : ℝ) (hbound : ∀ w i j, ‖M w i j‖ ≤ B) :
    Integrable (fun w : ℝ => ∑ i : Fin N, ∑ j : Fin N,
      star (f i w)*M w i j*g j w) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  exact l2_bounded_multiplier_integrable (f i) (g j) (fun w => M w i j)
    (hf i) (hg j) (hM i j) B (fun w => hbound w i j)

variable {T : Type*} [Fintype T]

/-- The physical inverse-bath hard-core trial quadratic is genuinely L1 for
each canonical root over a bounded coupling set. Its uniform integral bound
is a separate quantitative step. -/
theorem actual_core_inverse_trial_integrable (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hρ : ∀ a, 0 ≤ rho a) (hs : ∀ a, 0 < sigma a)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) (B : ℝ)
    (K D G : TailMatrix T N) (hB : ‖K‖ ≤ B)
    (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) :
    let f : Fin N → ℝ → ℂ := fun a w =>
      (Real.sqrt (rho a) : ℂ) *
      ((w*radial_fourier (coreValue (edgeHi sigma i a)) (2*Real.pi*w) : ℝ) : ℂ)
    Integrable (fun w : ℝ => ∑ a : Fin N, ∑ b : Fin N,
      star (f a w) *
      (MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w)) a b *
      f b w) := by
  dsimp only
  let f : Fin N → ℝ → ℂ := fun a w =>
    (Real.sqrt (rho a) : ℂ) *
    ((w*radial_fourier (coreValue (edgeHi sigma i a)) (2*Real.pi*w) : ℝ) : ℂ)
  obtain ⟨M,hM,hbound⟩ := actual_denominator_entries_uniformly_bounded
    z hz rho sigma hρ hs hv B
  have hf (a : Fin N) : MemLp (f a) 2 volume := by
    have hR : 0 < edgeHi sigma i a := by
      dsimp [edgeHi]; linarith [hs i,hs a]
    have hreal := core_weighted_spectral_memLp_two (edgeHi sigma i a) hR
    have hc : MemLp (fun w : ℝ =>
        ((w*radial_fourier (coreValue (edgeHi sigma i a)) (2*Real.pi*w) : ℝ) : ℂ))
        2 volume := hreal.ofReal
    exact hc.const_mul (Real.sqrt (rho a) : ℂ)
  have hm (a b : Fin N) : AEStronglyMeasurable
      (fun w : ℝ => (MatrixOZPairing.radialDenominator z rho sigma K D G
        (2*Real.pi*w)) a b) volume := by
    have hc := actual_denominator_entry_continuous z hz rho sigma hs K D G hroot a b
    exact (hc.comp (show Continuous (fun w : ℝ => 2*Real.pi*w) by fun_prop)).aestronglyMeasurable
  exact l2_matrix_pair_integrable f f
    (fun w => MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w))
    hf hf hm M (fun w a b => hbound K D G hB hK hroot hcanon (2*Real.pi*w) a b)

end FMSA.Convergence.TracerForcingIntegrability
/-- info: 'FMSA.Convergence.TracerForcingIntegrability.l2_bounded_multiplier_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerForcingIntegrability.l2_bounded_multiplier_integrable
/-- info: 'FMSA.Convergence.TracerForcingIntegrability.l2_matrix_pair_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerForcingIntegrability.l2_matrix_pair_integrable
/-- info: 'FMSA.Convergence.TracerForcingIntegrability.actual_core_inverse_trial_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerForcingIntegrability.actual_core_inverse_trial_integrable
