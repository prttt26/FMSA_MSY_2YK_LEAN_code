import MSAConvergence.TracerForcingIntegrability
/-! Quantitative uniform integrals for bounded physical Gram multipliers
and fixed L2 tracer trial fields. -/
open MeasureTheory FMSA.Convergence.TracerForcingIntegrability
open FMSA.Convergence.TracerSpectralL2 FMSA.Convergence.TracerBathFactorBound
open FMSA.Convergence.TracerCoreTrialField FMSA.Convergence.TracerTailSpectralBound
open FMSA.Convergence.CanonicalInverseCovariance
open FMSA.ExactMSA.MultiTailMixture MSAMixture FMSA.HardSphere
open FMSA.Paper
noncomputable section
namespace FMSA.Convergence.TracerCoreForcingBound

/-- Scalar bounded-multiplier L2–L2 Hölder estimate. -/
theorem bounded_l2_pair_integral_le (f g m : ℝ → ℂ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hm : AEStronglyMeasurable m volume) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ w, ‖m w‖ ≤ B) :
    ‖∫ w : ℝ, star (f w)*m w*g w‖ ≤
      B * ((∫ w : ℝ, ‖f w‖^2)^(1/(2:ℝ)) *
        (∫ w : ℝ, ‖g w‖^2)^(1/(2:ℝ))) := by
  have hi := FMSA.Convergence.TracerForcingIntegrability.l2_bounded_multiplier_integrable
    f g m hf hg hm B hbound
  have hfg : Integrable (fun w : ℝ => ‖f w‖*‖g w‖) := by
    simpa only [Pi.mul_apply, Pi.star_apply, norm_mul, norm_star] using
      (hf.star.integrable_mul hg).norm
  have hpoint (w : ℝ) : ‖star (f w)*m w*g w‖ ≤ B*(‖f w‖*‖g w‖) := by
    simp only [norm_mul,norm_star]
    have h1 := hbound w
    nlinarith [mul_nonneg (norm_nonneg (f w)) (norm_nonneg (g w))]
  have h22 : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hf' : MemLp f (ENNReal.ofReal (2:ℝ)) volume := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2:ℝ)) volume := by simpa using hg
  have hh := integral_mul_norm_le_Lp_mul_Lq h22 hf' hg'
  calc
    _ ≤ ∫ w : ℝ, ‖star (f w)*m w*g w‖ := norm_integral_le_integral_norm _
    _ ≤ B*(∫ w : ℝ, ‖f w‖*‖g w‖) := by
      rw [← integral_const_mul]
      exact integral_mono hi.norm (hfg.const_mul B) hpoint
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa using hh

variable {N : ℕ}
/-- Finite matrix version of the same uniform integral estimate. -/
theorem bounded_l2_matrix_integral_le
    (f g : Fin N → ℝ → ℂ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hf : ∀ i, MemLp (f i) 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hM : ∀ i j, AEStronglyMeasurable (fun w => M w i j) volume)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w i j, ‖M w i j‖ ≤ B) :
    ‖∫ w : ℝ, ∑ i : Fin N, ∑ j : Fin N,
      star (f i w)*M w i j*g j w‖ ≤
    ∑ i : Fin N, ∑ j : Fin N,
      B * ((∫ w : ℝ, ‖f i w‖^2)^(1/(2:ℝ)) *
        (∫ w : ℝ, ‖g j w‖^2)^(1/(2:ℝ))) := by
  have hij (i j : Fin N) : Integrable
      (fun w : ℝ => star (f i w)*M w i j*g j w) :=
    l2_bounded_multiplier_integrable (f i) (g j) (fun w => M w i j)
      (hf i) (hg j) (hM i j) B (fun w => hbound w i j)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hij _ j)]
  calc
    ‖∑ i : Fin N, ∑ j : Fin N,
       ∫ w : ℝ, star (f i w)*M w i j*g j w‖ ≤
      ∑ i : Fin N, ‖∑ j : Fin N,
       ∫ w : ℝ, star (f i w)*M w i j*g j w‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N,
      ‖∫ w : ℝ, star (f i w)*M w i j*g j w‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact bounded_l2_pair_integral_le (f i) (g j) (fun w => M w i j)
        (hf i) (hg j) (hM i j) B hB (fun w => hbound w i j)

/-- Fixed density-weighted hard-core trial spectral vector for row i. -/
def coreTrialVector {N : ℕ} (rho sigma : Fin N → ℝ) (i a : Fin N)
    (w : ℝ) : ℂ :=
  (Real.sqrt (rho a) : ℂ) *
    ((w*radial_fourier (coreValue (edgeHi sigma i a)) (2*Real.pi*w) : ℝ) : ℂ)

variable {T : Type*} [Fintype T]

/-- Uniform integral bound on the actual hard-core inverse-bath quadratic.
The constant depends on fixed mixture data and the bounded-coupling radius,
not on the BH amplitudes, root, or real frequency. -/
theorem actual_core_inverse_trial_integral_uniform (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hρ : ∀ a, 0 ≤ rho a) (hs : ∀ a, 0 < sigma a)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) (B : ℝ) (i : Fin N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u a b, K u a b = K u b a) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ‖∫ w : ℝ, ∑ a : Fin N, ∑ b : Fin N,
        star (coreTrialVector rho sigma i a w) *
        (MatrixOZPairing.radialDenominator z rho sigma K D G
          (2*Real.pi*w)) a b * coreTrialVector rho sigma i b w‖ ≤ M := by
  let f : Fin N → ℝ → ℂ := fun a w => coreTrialVector rho sigma i a w
  obtain ⟨L,hL,hbound⟩ := actual_denominator_entries_uniformly_bounded
    z hz rho sigma hρ hs hv B
  let M : ℝ := ∑ a : Fin N, ∑ b : Fin N,
    L * ((∫ w : ℝ, ‖f a w‖^2)^(1/(2:ℝ)) *
      (∫ w : ℝ, ‖f b w‖^2)^(1/(2:ℝ)))
  have hM : 0 ≤ M := by
    dsimp only [M]
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    have ha : 0 ≤ (∫ w : ℝ, ‖f a w‖^2)^(1/(2:ℝ)) := by positivity
    have hb : 0 ≤ (∫ w : ℝ, ‖f b w‖^2)^(1/(2:ℝ)) := by positivity
    exact mul_nonneg hL (mul_nonneg ha hb)
  refine ⟨M,hM,?_⟩
  intro K D G hB hK hroot hcanon
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
  exact bounded_l2_matrix_integral_le f f
    (fun w => MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w))
    hf hf hm L hL (fun w a b => hbound K D G hB hK hroot hcanon (2*Real.pi*w) a b)

end FMSA.Convergence.TracerCoreForcingBound
/-- info: 'FMSA.Convergence.TracerCoreForcingBound.bounded_l2_pair_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreForcingBound.bounded_l2_pair_integral_le
/-- info: 'FMSA.Convergence.TracerCoreForcingBound.bounded_l2_matrix_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreForcingBound.bounded_l2_matrix_integral_le
/-- info: 'FMSA.Convergence.TracerCoreForcingBound.actual_core_inverse_trial_integral_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreForcingBound.actual_core_inverse_trial_integral_uniform
