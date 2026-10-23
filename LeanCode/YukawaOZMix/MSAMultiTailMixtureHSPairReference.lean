import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairHSRegularity

/-! Independent actual pair-contact HS reference, and the corresponding
unequal-diameter finite-tail first-order RDF certificate. The weighted kernel
budget is sufficient. No supplied HS reference or reference OZ is a premise. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem rdfHSPairCandidate_actual_radial_OZ (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ)
    (hb : rdfWeightedKernelBudget ρ σ δ < 1) (i j : Fin N) :
    rdfHSPairCandidate ρ σ i j =ᵐ[volume.restrict (Ioi 0)] fun r => rdfActualHS z ρ σ i j r+
      radialMixtureConv (rdfActualHS z ρ σ) (rdfHSPairCandidate ρ σ) ρ i j r := by
  have cm : ∀ i j, Measurable (fun r => r*rdfActualHS z ρ σ i j r) := fun i j =>
    measurable_id.mul (orderedRadialCorrelation_measurable z hz ρ σ (fun i => (hσ i).le) 0 0 _ i j)
  have ci : ∀ i j, IntegrableOn (fun r => r*rdfActualHS z ρ σ i j r) (Ioi 0) :=
    orderedRadialCorrelation_zero_radius_integrable z hz ρ σ hv (fun i => (hρ i).le) hσ
  have ci2 : ∀ i j, IntegrableOn (fun r => r*(r*rdfActualHS z ρ σ i j r)) (Ioi 0) := fun i j =>
    orderedRadialCorrelation_zero_second_moment z hz ρ σ hv (fun i => (hρ i).le) hσ i j (ci i j)
  have hconvzero : ∀ a b r, radialMixtureConv (rdfActualHS z ρ σ)
      (fun _ _ _ => 0) ρ a b r=0 := by
    intro a b r
    simp [radialMixtureConv, radial3d_conv]
  have hFTzero (k : ℝ) : radialMatrixFourier (fun (_ _ : Fin N) (_ : ℝ) => 0) k=0 := by
    ext a b
    simp [radialMatrixFourier, radial_fourier]
  have he := radialMixture_firstOrder_OZ_of_moments (rdfActualHS z ρ σ) (fun _ _ _ => 0)
    (rdfActualHS z ρ σ) (rdfHSPairCandidate ρ σ) ρ cm (fun _ _ => by fun_prop) cm
    (rdfHSPairCandidate_radius_measurable ρ σ) ci ci2 ci ci2
    (fun _ _ => by simpa using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℝ))))
    (rdfHSPairCandidate_radius_integrable_of_weighted_budget ρ σ δ hδ hb)
    (rdfActualHS_odd_ae_continuous z hz ρ σ (fun i => (hσ i).le))
    (fun a b => rdfHSPairCandidate_odd_ae_continuous ρ σ a b
      (by unfold edgeHi; linarith [hσ a, hσ b]))
    (fun k hk => by
      rw [hFTzero, Matrix.mul_zero, add_zero]
      exact rdfHSPairH_actual_Fourier_OZ z hz ρ σ hv hρ hσ δ hδ hb k hk) i j
  simpa only [hconvzero, add_zero] using he

theorem rdfHSPairCandidate_valid_of_weighted_budget (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ)
    (hb : rdfWeightedKernelBudget ρ σ δ < 1) :
    ValidRadialHSReference z ρ σ (rdfHSPairCandidate ρ σ) :=
  ⟨rdfHSPairCandidate_radius_measurable ρ σ,
    rdfHSPairCandidate_radius_integrable_of_weighted_budget ρ σ δ hδ hb,
    rdfHSPairCandidate_hardcore ρ σ,
    rdfHSPairCandidate_actual_radial_OZ z hz ρ σ hv hρ hσ δ hδ hb⟩

theorem firstOrderMixtureRDF_pairContact_certificate_of_weighted_budget
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hzδ : ∀ u, δ ≤ z u) (hb : rdfWeightedKernelBudget ρ σ δ < 1) :
    (∀ i j r, r < edgeHi σ i j → rdfFirstOrderCausal z ρ σ K i j r=0) ∧
    (∀ τ i j r, 0 < r → r < edgeHi σ i j →
      rdfHSPairCandidate ρ σ i j r+τ*rdfFirstOrderCausal z ρ σ K i j r = -1) ∧
    (∀ i j, rdfFirstOrderCausal z ρ σ K i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => rdfActualC1 z ρ σ K i j r+
        radialMixtureConv (rdfActualHS z ρ σ) (rdfFirstOrderCausal z ρ σ K) ρ i j r+
          radialMixtureConv (rdfActualC1 z ρ σ K) (rdfHSPairCandidate ρ σ) ρ i j r) :=
  firstOrderMixtureRDF_certificate_of_weighted_budget z hz ρ σ hv hρ hσ K hK δ hδ hzδ hb
    (rdfHSPairCandidate ρ σ) (rdfHSPairCandidate_valid_of_weighted_budget z hz ρ σ hv hρ hσ δ hδ hb)

end FMSA.ExactMSA.MultiTailMixture
