import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairCausal

/-! Exact zero-density interface diagnostic. A common core larger than an
actual pair contact fails the actual canonical radial OZ on an open interval.
This is a definition/interface counterexample, not a finite positive-density
physical counterexample or a refutation of conditional generic seed lemmas. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfHSCommonCoreTrial (S : ℝ) (_i _j : Fin N) (r : ℝ) : ℝ :=
  if |r| < S then -1 else 0

theorem rdfHSPairExterior_zeroDensity (σ : Fin N → ℝ) (i j : Fin N)
    (u : ℝ) (hu : 0 ≤ u) : rdfHSPairExterior (fun _ => 0) σ u i j=0 := by
  have he := rdfHSPairExterior_renewal (fun _ => 0) σ i j u hu
  simpa [rdfHSCoreSource, rdfCausalKernel] using he

theorem rdfHSPairCandidate_zeroDensity_exterior (σ : Fin N → ℝ) (i j : Fin N)
    (hR : 0 < edgeHi σ i j) (r : ℝ) (hr : edgeHi σ i j ≤ r) :
    rdfHSPairCandidate (fun _ => 0) σ i j r=0 := by
  unfold rdfHSPairCandidate
  rw [rdfHSPairMoment_outer (fun _ => 0) σ i j hR r hr,
    rdfHSPairExterior_zeroDensity σ i j _ (sub_nonneg.mpr hr), zero_div]

theorem commonCore_trial_zeroDensity_OZ_failure (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (S : ℝ) (i j : Fin N)
    (r : ℝ) (hr : 0 < r) (hR : edgeHi σ i j < r) (hS : r < S) :
    rdfHSCommonCoreTrial S i j r ≠ rdfActualHS z (fun _ => 0) σ i j r+
      radialMixtureConv (rdfActualHS z (fun _ => 0) σ) (rdfHSCommonCoreTrial S) (fun _ => 0) i j r := by
  have hv : 0 < vacMix (fun _ : Fin N => (0 : ℝ)) σ := by simp [vacMix, etaMix]
  have hc := orderedRadialCorrelation_zero_exterior z hz (fun _ => 0) σ hv
    (fun _ => le_refl 0) hσ i j r hR
  change rdfHSCommonCoreTrial S i j r ≠
    orderedRadialCorrelation z (fun _ => 0) σ 0 0 (baseSeed z (fun _ => 0) σ) i j r+_
  rw [hc]
  simp [radialMixtureConv, rdfHSCommonCoreTrial, abs_of_pos hr, hS]

theorem commonCore_trial_twoSpecies_open_interval_failure (r : ℝ) (hr : r ∈ Ioo (1 : ℝ) 2) :
    rdfHSCommonCoreTrial (N := 2) 2 0 0 r ≠
      rdfActualHS (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 2 => 0)
        (fun i : Fin 2 => if i=0 then 1 else 2) 0 0 r+
      radialMixtureConv
        (rdfActualHS (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 2 => 0)
          (fun i : Fin 2 => if i=0 then 1 else 2))
        (rdfHSCommonCoreTrial 2) (fun _ => 0) 0 0 r := by
  apply commonCore_trial_zeroDensity_OZ_failure _ (fun _ => by norm_num) _ _ 2 0 0 r
    (by linarith [hr.1]) (by simpa [edgeHi] using hr.1) hr.2
  intro i
  split_ifs <;> norm_num

end FMSA.ExactMSA.MultiTailMixture
