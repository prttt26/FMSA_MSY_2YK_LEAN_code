import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSRadius

/-! Conditional actual mixture RDF capstone. The HS reference is an actual
radial function with hard core, actual radial OZ and explicit radius moments.
The first-order RDF is constructed by Volterra, not supplied as a premise. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfActualHS (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) : ℝ → ℝ :=
  orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j

def rdfActualC1 (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) : ℝ → ℝ :=
  orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j

/-- An actual valid HS reference; no abstract spectral matrix is substituted
for the reference RDF. No first-order h1, core or OZ premise is present. -/
structure ValidRadialHSReference (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (h0 : Fin N → Fin N → ℝ → ℝ) : Prop where
  h0_radius_measurable : ∀ i j, Measurable (fun r => r*h0 i j r)
  h0_radius_integrable : ∀ i j, Integrable (fun r => r*h0 i j r)
  hardcore : ∀ i j r, 0 < r → r < edgeHi σ i j → h0 i j r = -1
  radial_OZ : ∀ i j, h0 i j =ᵐ[volume.restrict (Ioi 0)]
    fun r => rdfActualHS z ρ σ i j r+radialMixtureConv (rdfActualHS z ρ σ) h0 ρ i j r

/-- Actual first-order radial OZ, a.e. on positive radii, for the same
Volterra h1 whose pointwise core is proved. Every first-order DCF regularity
and convolution condition is supplied internally. -/
theorem rdfFirstOrderCausal_actual_radial_OZ (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (h0 : Fin N → Fin N → ℝ → ℝ) (href : ValidRadialHSReference z ρ σ h0)
    (i j : Fin N) :
    rdfFirstOrderCausal z ρ σ K i j =ᵐ[volume.restrict (Ioi 0)] fun r => rdfActualC1 z ρ σ K i j r+
      radialMixtureConv (rdfActualHS z ρ σ) (rdfFirstOrderCausal z ρ σ K) ρ i j r+
        radialMixtureConv (rdfActualC1 z ρ σ K) h0 ρ i j r := by
  have cm : ∀ i j, Measurable (fun r => r*rdfActualHS z ρ σ i j r) := fun i j =>
    measurable_id.mul (orderedRadialCorrelation_measurable z hz ρ σ (fun i => (hσ i).le) 0 0 _ i j)
  have ci : ∀ i j, IntegrableOn (fun r => r*rdfActualHS z ρ σ i j r) (Ioi 0) :=
    orderedRadialCorrelation_zero_radius_integrable z hz ρ σ hv (fun i => (hρ i).le) hσ
  have ci2 : ∀ i j, IntegrableOn (fun r => r*(r*rdfActualHS z ρ σ i j r)) (Ioi 0) := fun i j =>
    orderedRadialCorrelation_zero_second_moment z hz ρ σ hv (fun i => (hρ i).le) hσ i j
      (ci i j)
  apply radialMixture_firstOrder_OZ_of_moments (rdfActualHS z ρ σ) h0 (rdfActualC1 z ρ σ K)
    (rdfFirstOrderCausal z ρ σ K) ρ cm href.h0_radius_measurable
    (orderedLinearizedCorrelation_radius_measurable z ρ σ _ _)
    (rdfFirstOrderCausal_radius_measurable z ρ σ K)
    ci ci2
    (orderedLinearizedCorrelation_radius_weighted_integrable z ρ σ K hz hv (fun i => (hρ i).le) hσ hK)
    (orderedLinearizedCorrelation_second_moment_integrable z hz ρ σ hv (fun i => (hρ i).le) hσ K hK)
    href.h0_radius_integrable (rdfFirstOrderCausal_radius_integrable z ρ σ hσ K hU)
    (orderedLinearizedCorrelation_odd_ae_continuous z hz ρ σ hv (fun i => (hρ i).le) hσ K hK)
    (rdfFirstOrderCausal_odd_ae_continuous z ρ σ K) _ i j
  intro k hk
  have hzero := radialMixture_reference_fourier_OZ (rdfActualHS z ρ σ) h0 ρ cm
    href.h0_radius_measurable ci ci2
    (fun i j => (href.h0_radius_integrable i j).integrableOn) href.radial_OZ k hk
  exact rdfFirstOrderCausal_actual_fourier_OZ z hz ρ σ hv hρ hσ K hK hU h0 k hk hzero

/-- Joint actual-function certificate: pointwise first-order core, pointwise
hard core of h0+tau*h1, and a.e. first-order radial matrix OZ. The construction
works with arbitrary finite signed symmetric tails and unequal diameters. -/
theorem firstOrderMixtureRDF_certificate (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (h0 : Fin N → Fin N → ℝ → ℝ) (href : ValidRadialHSReference z ρ σ h0) :
    (∀ i j r, r < edgeHi σ i j → rdfFirstOrderCausal z ρ σ K i j r=0) ∧
    (∀ τ i j r, 0 < r → r < edgeHi σ i j → h0 i j r+τ*rdfFirstOrderCausal z ρ σ K i j r = -1) ∧
    (∀ i j, rdfFirstOrderCausal z ρ σ K i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => rdfActualC1 z ρ σ K i j r+
        radialMixtureConv (rdfActualHS z ρ σ) (rdfFirstOrderCausal z ρ σ K) ρ i j r+
          radialMixtureConv (rdfActualC1 z ρ σ K) h0 ρ i j r) := by
  refine ⟨rdfFirstOrderCausal_hardcore z ρ σ K, ?_,
    rdfFirstOrderCausal_actual_radial_OZ z hz ρ σ hv hρ hσ K hK hU h0 href⟩
  intro τ i j r hr hR
  rw [rdfFirstOrderCausal_hardcore z ρ σ K i j r hR, mul_zero, add_zero]
  exact href.hardcore i j r hr hR

end FMSA.ExactMSA.MultiTailMixture
