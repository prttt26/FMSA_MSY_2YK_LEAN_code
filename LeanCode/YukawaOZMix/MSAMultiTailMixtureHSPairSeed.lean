import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairCausal

/-! Actual pair-contact full-space HS seed, with both physical density
weights and the reflected first arm. The actual exterior identity is proved.
The positive finite-core WT identity remains a separate unproved obligation. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfHSPairActualU (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  rdfHSPairMoment ρ σ i j r-∑ m, ρ m*∫ t : ℝ,
    dpSeedQ z ρ σ m i t*rdfHSPairMoment ρ σ m j (r-t)

def rdfHSPairActualSeed (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  rdfHSPairActualU z ρ σ i j r-∑ m, ρ m*∫ t : ℝ,
    dpSeedQ z ρ σ i m t*rdfHSPairActualU z ρ σ m j (r+t)

theorem dpSeedQ_zero_below_edge (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (i j : Fin N) (t : ℝ) (ht : t < edgeLo σ i j) : dpSeedQ z ρ σ i j t=0 := by
  simp [dpSeedQ, q, ht]

theorem rdfHSPairActualU_zero_outer (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j ≤ r) : rdfHSPairActualU z ρ σ i j r=0 := by
  unfold rdfHSPairActualU
  rw [rdfHSPairMoment_actual_outer_renewal z ρ σ hσ δ hδ hb i j r hr, sub_self]

/-- Each pair's actual seed vanishes already at its own contact R_ij.
The support shift r+lambda_im>=R_mj replaces the common-sigma outer gap. -/
theorem rdfHSPairActualSeed_zero_outer (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j ≤ r) : rdfHSPairActualSeed z ρ σ i j r=0 := by
  unfold rdfHSPairActualSeed
  rw [rdfHSPairActualU_zero_outer z ρ σ hσ δ hδ hb i j r hr, zero_sub, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro m _
  have he : (fun t : ℝ => dpSeedQ z ρ σ i m t*rdfHSPairActualU z ρ σ m j (r+t))=
      fun _ => (0 : ℝ) := by
    funext t
    by_cases ht : t < edgeLo σ i m
    · rw [dpSeedQ_zero_below_edge z ρ σ i m t ht, zero_mul]
    · have hrt : edgeHi σ m j ≤ r+t := by
        have ht' := le_of_not_gt ht
        simp only [edgeHi, edgeLo] at hr ht' ⊢
        linarith
      rw [rdfHSPairActualU_zero_outer z ρ σ hσ δ hδ hb m j (r+t) hrt, mul_zero]
  rw [he, integral_zero, mul_zero]

theorem rdfHSPairActualSeed_eq_actual_c0_exterior (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    rdfHSPairActualSeed z ρ σ i j r=r*rdfActualHS z ρ σ i j r := by
  rw [rdfHSPairActualSeed_zero_outer z ρ σ hσ δ hδ hb i j r hr.le]
  unfold rdfActualHS
  rw [orderedRadialCorrelation_zero_exterior z hz ρ σ hv hρ hσ i j r hr, mul_zero]

/-- The remaining physical WT obligation on each actual finite open core.
This is an explicit premise for a supplied, constructed function, not an axiom. -/
def HSPairCoreSeedIdentity (z : ι → ℝ) (ρ σ : Fin N → ℝ) : Prop :=
  ∀ i j, rdfHSPairActualSeed z ρ σ i j =ᵐ[volume.restrict (Ioo 0 (edgeHi σ i j))]
    fun r => r*rdfActualHS z ρ σ i j r

theorem rdfHSPairActualSeed_positive_ae_of_core_identity (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (hcore : HSPairCoreSeedIdentity z ρ σ) (i j : Fin N) :
    rdfHSPairActualSeed z ρ σ i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => r*rdfActualHS z ρ σ i j r := by
  have hc : ∀ᵐ r : ℝ ∂volume, r ∈ Ioo 0 (edgeHi σ i j) →
      rdfHSPairActualSeed z ρ σ i j r=r*rdfActualHS z ρ σ i j r :=
    (ae_restrict_iff' measurableSet_Ioo).mp (hcore i j)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hc,
    ae_restrict_of_ae (volume.ae_ne (edgeHi σ i j))] with r hr hc hR
  by_cases hh : r < edgeHi σ i j
  · exact hc ⟨hr, hh⟩
  · exact rdfHSPairActualSeed_eq_actual_c0_exterior z hz ρ σ hv hρ hσ δ hδ hb i j r
      (lt_of_le_of_ne (le_of_not_gt hh) hR.symm)

end FMSA.ExactMSA.MultiTailMixture
