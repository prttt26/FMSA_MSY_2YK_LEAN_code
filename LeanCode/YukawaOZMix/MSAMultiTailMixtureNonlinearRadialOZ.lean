import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearSpectralOZ

/-! Actual positive-density nonlinear radial OZ, under finite coefficient
admissibility and the actual kernel budget. All analytic premises are internal.
Automatic admissibility of every physical BH branch is a separate question. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonlinearH_actual_radial_OZ_of_finite_certificates
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hr : NonlinearFiniteReciprocityCertificate z ρ σ Dt G)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G) (i j : Fin N) :
    nonlinearH z ρ σ Dt G i j =ᵐ[volume.restrict (Ioi 0)] fun r =>
      orderedRadialCorrelation z ρ σ K Dt G i j r+
        radialMixtureConv (orderedRadialCorrelation z ρ σ K Dt G) (nonlinearH z ρ σ Dt G) ρ i j r := by
  let c := orderedRadialCorrelation z ρ σ K Dt G
  let h := nonlinearH z ρ σ Dt G
  have cm : ∀ i j, Measurable (fun r => r*c i j r) := fun i j =>
    measurable_id.mul (orderedRadialCorrelation_measurable z hz ρ σ (fun i => (hσ i).le) K Dt G i j)
  have hm : ∀ i j, Measurable (fun r => r*h i j r) := fun i j =>
    measurable_id.mul ((nonlinearRDFMoment_measurable z ρ σ Dt G i j).div measurable_id)
  have ci := nonlinear_orderedCorrelation_radius_integrable z hz ρ σ K Dt G (fun i => (hσ i).le) hroot
  have ci2 := nonlinear_orderedCorrelation_second_moment_integrable z hz ρ σ K Dt G (fun i => (hσ i).le) hroot
  have hi := nonlinearH_radius_integrable_of_weighted_budget z ρ σ Dt G hz (fun i => (hσ i).le) hv δ hδ hδz hb
  have hconvzero : ∀ a b r, radialMixtureConv c (fun _ _ _ => 0) ρ a b r=0 := by
    intro a b r; simp [radialMixtureConv, radial3d_conv]
  have hFTzero (k : ℝ) : radialMatrixFourier (fun (_ _ : Fin N) (_ : ℝ) => 0) k=0 := by
    ext a b; simp [radialMatrixFourier, radial_fourier]
  have he := radialMixture_firstOrder_OZ_of_moments c (fun _ _ _ => 0) c h ρ
    cm (fun _ _ => by fun_prop) cm hm ci ci2 ci ci2
    (fun _ _ => by simpa using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℝ)))) hi
    (nonlinear_orderedCorrelation_odd_ae_continuous z hz ρ σ K Dt G (fun i => (hσ i).le))
    (fun a b => nonlinearH_odd_ae_continuous z ρ σ Dt G a b
      (by unfold edgeHi; linarith [hσ a,hσ b]))
    (fun k hk => by
      rw [hFTzero, Matrix.mul_zero, add_zero]
      exact nonlinearH_actual_Fourier_OZ_of_finite_certificates z ρ σ K Dt G hz hσ hv hroot hK
        δ hδ hδz hb hr hw k hk) i j
  simpa only [hconvzero, add_zero] using he

/-- Joint certificate for the same actual nonlinear mixture g/h/c. The only
admissibility premises beyond the BH root and integral budget are explicit
finite real polynomial coefficient checks; no supplied function or OZ data. -/
theorem nonlinearMixtureRDF_finite_admissibility_certificate
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hr : NonlinearFiniteReciprocityCertificate z ρ σ Dt G)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G) :
    (∀ i j r, r < edgeHi σ i j → nonlinearG z ρ σ Dt G i j r=0) ∧
    (∀ i j, Integrable (fun r => r*nonlinearH z ρ σ Dt G i j r)) ∧
    (∀ u i j, (∫ r in Ioi (0 : ℝ), exp (-z u*r)*(r*nonlinearG z ρ σ Dt G i j r))=
      exp (-z u*edgeHi σ i j)*G u i j) ∧
    (∀ i j r, 0 < r → nonlinearG z ρ σ Dt G i j r=nonlinearG z ρ σ Dt G j i r) ∧
    (∀ i j, nonlinearH z ρ σ Dt G i j =ᵐ[volume.restrict (Ioi 0)] fun r =>
      orderedRadialCorrelation z ρ σ K Dt G i j r+
        radialMixtureConv (orderedRadialCorrelation z ρ σ K Dt G) (nonlinearH z ρ σ Dt G) ρ i j r) :=
  ⟨nonlinearG_hardcore z ρ σ Dt G,
    nonlinearH_radius_integrable_of_weighted_budget z ρ σ Dt G hz (fun i => (hσ i).le) hv δ hδ hδz hb,
    nonlinearG_amplitude_eq_actual_radial_laplace z ρ σ K Dt G hz hσ hv hroot δ hδ hδz hb,
    nonlinear_finite_certificate_actual_pair_reciprocity z ρ σ Dt G hz (fun i => (hσ i).le) hv δ hδ hδz hb hr,
    nonlinearH_actual_radial_OZ_of_finite_certificates z ρ σ K Dt G hz hσ hv hroot hK δ hδ hδz hb hr hw⟩

end FMSA.ExactMSA.MultiTailMixture
