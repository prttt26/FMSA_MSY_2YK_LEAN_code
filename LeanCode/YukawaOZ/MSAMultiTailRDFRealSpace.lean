import LeanCode.YukawaOZ.MSAMultiTailRDFRegularity

/-! Joint actual RDF reconstruction: hard core plus radial real-space OZ.
Only BH equations and decay/explicit kernel size are assumed. -/
noncomputable section
open MeasureTheory Set Filter Real
open FMSA.HardSphere
namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

/-- An integrable excess of the actual Volterra solution suffices for a.e.
radial OZ. All Fubini and inversion regularity hypotheses are discharged. -/
theorem reconstructedH_realspace_oz (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    (hρ : rhoOf xi ≠ 0) (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) :
    reconstructedH xi z Dt G =ᵐ[volume.restrict (Ioi 0)]
      (fun r => correlation xi z Dt G r + rhoOf xi *
        radial3d_conv (correlation xi z Dt G) (reconstructedH xi z Dt G) r) := by
  apply radial_oz_of_moments
    (reconstructedH xi z Dt G) (correlation xi z Dt G) (rhoOf xi)
    (reconstructedH_moment_measurable xi z Dt G)
    (measurable_id.mul (correlation_measurable xi z Dt G))
  · simp_rw [reconstructedH_moment]
    exact rdfRadialMoment_integrable xi z Dt G he
  · exact correlation_moment_integrable xi z K Dt G hz hroot
  · exact correlation_first_moment_integrable xi z K Dt G hz hroot
  · exact reconstructedH_odd_ae_continuous xi z Dt G
  · exact correlation_odd_ae_continuous xi z K Dt G hz hroot
  · intro k hk
    exact reconstructedH_fourier_oz xi z K Dt G hxi hz hroot hρ he hk

/-- The core is a property of the constructed function, checked jointly with
the actual OZ equation, rather than assumed in an inverse-transform interface. -/
theorem reconstructedH_core_and_oz (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    (hρ : rhoOf xi ≠ 0) (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) :
    (∀ r ∈ Ioo (0 : ℝ) 1, reconstructedH xi z Dt G r = -1) ∧
    reconstructedH xi z Dt G =ᵐ[volume.restrict (Ioi 0)]
      (fun r => correlation xi z Dt G r + rhoOf xi *
        radial3d_conv (correlation xi z Dt G) (reconstructedH xi z Dt G) r) := by
  exact ⟨fun r hr => reconstructedH_core xi z Dt G hr.1 hr.2,
    reconstructedH_realspace_oz xi z K Dt G hxi hz hroot hρ he⟩

/-- An explicit sufficient region for actual RDF/core/OZ reconstruction.
No Wiener resolvent axiom, RDF/OZ assumption, or separate Fubini premise. -/
theorem reconstructedH_core_and_oz_of_small_budget (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    (hρ : rhoOf xi ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hsmall : weightedKernelBudget xi z Dt G δ < 1) :
    (∀ r ∈ Ioo (0 : ℝ) 1, reconstructedH xi z Dt G r = -1) ∧
    reconstructedH xi z Dt G =ᵐ[volume.restrict (Ioi 0)]
      (fun r => correlation xi z Dt G r + rhoOf xi *
        radial3d_conv (correlation xi z Dt G) (reconstructedH xi z Dt G) r) := by
  exact reconstructedH_core_and_oz xi z K Dt G hxi hz hroot hρ
    (rdfExcess_decay_of_small_budget xi z Dt G hxi hz hδ hδz hsmall).1

theorem reconstructedH_structureDen_pos (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    (hρ : rhoOf xi ≠ 0) (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0))
    {k : ℝ} (hk : k ≠ 0) :
    0 < 1 - rhoOf xi * radial_fourier (correlation xi z Dt G) k := by
  exact lt_of_le_of_ne (structureDen_nonneg xi z Dt G k hz hk)
    (oz_denominator_ne_zero (reconstructedH_fourier_oz xi z K Dt G hxi hz hroot hρ he hk)).symm

end FMSA.ExactMSA.MultiTail
