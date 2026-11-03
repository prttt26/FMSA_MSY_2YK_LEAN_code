import MSAConvergence.TracerQuadraticIntegrability

/-! Uniform integrated positive energy for each physical MSA row,
including rows belonging to zero-density retained tracers. -/
noncomputable section
open Matrix MeasureTheory FMSA.HardSphere FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerIntegratedEnergyIdentity
open FMSA.Convergence.TracerActualPointwiseForcing
open FMSA.Convergence.TracerQuadraticIntegrability
open FMSA.Convergence.TracerEnergyYoung
open FMSA.Convergence.TracerCoreForcingBound FMSA.Convergence.TracerTailCovarianceBudget
open FMSA.Convergence.TracerCoreTrialField FMSA.Convergence.TracerTailSpectralBound
open FMSA.Convergence.TracerTailForcingBound
open FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerUniformRowEnergy
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The real integral of an integrable complex field is bounded above by
the norm of its complex integral. -/
theorem integral_real_part_le_norm_integral (f : ℝ → ℂ) (hf : Integrable f) :
    (∫ w : ℝ, (f w).re) ≤ ‖∫ w : ℝ, f w‖ := by
  rw [show (∫ w : ℝ, (f w).re) = (∫ w : ℝ, f w).re by
    simpa only [RCLike.re_to_complex] using (integral_re hf)]
  exact Complex.re_le_norm _

/-- Actual physical MSA row energy is controlled by the two true forcing
integrals, with no assumption of positive density for the row species. -/
theorem actual_row_energy_le_two_quadratic_integrals
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hs : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B : ℝ) (K D G : TailMatrix T N) (hB : ‖K‖ ≤ B)
    (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) :
    (∫ w : ℝ, rowEnergy z rho sigma K D G i w) ≤
      2*(‖∫ w : ℝ, coreQuadratic z rho sigma K D G i w‖ +
        ‖∫ w : ℝ, tailQuadratic z rho sigma K D G i w‖) := by
  obtain ⟨hEi,hCi,hTi,hsplit⟩ := actual_row_energy_integral_split
    z hz rho sigma hs hv K D G hK hroot hcanon i
  have hqiC := actual_core_quadratic_integrable z hz rho sigma hρ hs hv B
    K D G hB hK hroot hcanon i
  have hqiT := actual_tail_quadratic_integrable z hz rho sigma hρ hs hv
    R hR hRσ B K D G hB hK hroot hcanon i
  have hqCr : Integrable (fun w : ℝ => (coreQuadratic z rho sigma K D G i w).re) := by
    simpa only [RCLike.re_to_complex] using hqiC.re
  have hqTr : Integrable (fun w : ℝ => (tailQuadratic z rho sigma K D G i w).re) := by
    simpa only [RCLike.re_to_complex] using hqiT.re
  have hFp (w : ℝ) : rowCoreForcing z rho sigma K D G i w ≤
      rowEnergy z rho sigma K D G i w/4 +
        (coreQuadratic z rho sigma K D G i w).re := by
    by_cases hw : w = 0
    · subst w
      simp [rowCoreForcing,rowEnergy,coreQuadratic,coreTrialVector]
    · have hb := (actual_row_forcing_physical_bounds z hz rho sigma hρ hs hv
        K D G hK hroot hcanon i w hw).1
      rw [congrArg Complex.re (core_quadratic_dotProduct z rho sigma K D G i w)] at hb
      exact hb
  have hGp (w : ℝ) : rowTailForcing z rho sigma K D G i w ≤
      rowEnergy z rho sigma K D G i w/4 +
        (tailQuadratic z rho sigma K D G i w).re := by
    by_cases hw : w = 0
    · subst w
      simp [rowTailForcing,rowEnergy,tailQuadratic,tailTrialVector]
    · have hb := (actual_row_forcing_physical_bounds z hz rho sigma hρ hs hv
        K D G hK hroot hcanon i w hw).2
      rw [congrArg Complex.re (tail_quadratic_dotProduct z rho sigma K D G i w)] at hb
      exact hb
  exact integrated_energy_le_two_forcings
    (rowEnergy z rho sigma K D G i)
    (rowCoreForcing z rho sigma K D G i)
    (rowTailForcing z rho sigma K D G i)
    (fun w => (coreQuadratic z rho sigma K D G i w).re)
    (fun w => (tailQuadratic z rho sigma K D G i w).re)
    ‖∫ w : ℝ, coreQuadratic z rho sigma K D G i w‖
    ‖∫ w : ℝ, tailQuadratic z rho sigma K D G i w‖
    hEi hCi hTi hqCr hqTr hsplit hFp hGp
    (integral_real_part_le_norm_integral _ hqiC)
    (integral_real_part_le_norm_integral _ hqiT)


/-- UNIFORM integrated spectral energy of every original-mixture row,
including retained tracers, over all canonical roots with bounded physical
couplings. The bound is independent of the MSA amplitude matrices D and G. -/
theorem actual_tracer_row_energy_integral_uniform
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hs : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B : ℝ) (i : Fin N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u a b, K u a b = K u b a) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      (∫ w : ℝ, rowEnergy z rho sigma K D G i w) ≤ M := by
  obtain ⟨Mcore,hMcore,hcore⟩ := actual_core_inverse_trial_integral_uniform
    z hz rho sigma hρ hs hv B i
  obtain ⟨Mtail,hMtail,htail⟩ := actual_tail_covariance_forcing_integral_uniform
    z hz rho sigma hρ hs hv R hR hRσ B i
  refine ⟨2*(Mcore+Mtail), by positivity,?_⟩
  intro K D G hB hK hroot hcanon
  have hc : ‖∫ w : ℝ, coreQuadratic z rho sigma K D G i w‖ ≤ Mcore := by
    simpa only [coreQuadratic] using hcore K D G hB hK hroot hcanon
  have ht : ‖∫ w : ℝ, tailQuadratic z rho sigma K D G i w‖ ≤ Mtail := by
    simpa only [tailQuadratic] using htail K D G hB hK hroot hcanon
  calc
    (∫ w : ℝ, rowEnergy z rho sigma K D G i w) ≤
      2*(‖∫ w : ℝ, coreQuadratic z rho sigma K D G i w‖ +
        ‖∫ w : ℝ, tailQuadratic z rho sigma K D G i w‖) :=
      actual_row_energy_le_two_quadratic_integrals z hz rho sigma hρ hs hv
        R hR hRσ B K D G hB hK hroot hcanon i
    _ ≤ 2*(Mcore+Mtail) := by gcongr

end FMSA.Convergence.TracerUniformRowEnergy
/-- info: 'FMSA.Convergence.TracerUniformRowEnergy.integral_real_part_le_norm_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUniformRowEnergy.integral_real_part_le_norm_integral
/-- info: 'FMSA.Convergence.TracerUniformRowEnergy.actual_row_energy_le_two_quadratic_integrals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUniformRowEnergy.actual_row_energy_le_two_quadratic_integrals
/-- info: 'FMSA.Convergence.TracerUniformRowEnergy.actual_tracer_row_energy_integral_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUniformRowEnergy.actual_tracer_row_energy_integral_uniform
