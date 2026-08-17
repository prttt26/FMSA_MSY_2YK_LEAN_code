/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.HSMix
import LeanCode.HSMixture.MatrixQ0
import LeanCode.HSMixture.PhysHSMix
import LeanCode.HSMixture.MixtureBaxterSeed
import LeanCode.HSMixture.HSMixBaxterFactor
import LeanCode.HardSphere.BaxterRealSpace

/-!
# `ρ_k`-weighted Baxter seed kernel — the physical row-sum that reduces to the scalar `q0_poly`

The mixture seed `matBaxterUQm[Ψ, Q]` reduces to `r·c_HS` at equal diameters only under
`hrow: ∑ₖ Qᵢₖ(u) = q0_poly η σ ρ u` (`matBaxterUQm_eq_rcHS_of_rowSum`, `MixtureBaxterSeed.lean`),
where the scalar one-component Baxter polynomial `q0_poly` carries an explicit **total-density** `ρ`
factor.  The physical Lebowitz coefficients `Q0phys`/`Qppphys` (`MatrixQ0.lean`) are `ρ`-STRIPPED
per-pair coefficients, so the BARE row-sum `∑ₖ q0MixEntry` does NOT hit `q0_poly` (it is off by the
missing density weight — numerically ≈ `q0_poly / ⟨ρ⟩`, a ~`1/ρ` factor).

The fix is to weight the summed (second) index by its density `ρ_k`: the **column-scaled kernel**
`q0MixEntryW X i j := ρⱼ · q0MixEntry X i j`.  Then `∑ₖ q0MixEntryWᵢₖ = ∑ₖ ρ_k·q0MixEntryᵢₖ`, and at
equal diameters this equals the scalar `q0_poly` EXACTLY — because per-pair `Q0phys`/`Qppphys`
collapse to the scalar `q'_py`/`q''_py` (`Q0phys_equalDiam`/`Qppphys_equalDiam` below), and the
`ρ_k`-sum supplies the total density `∑ₖ ρ_k` that `q0_poly` needs.  This is the algebraic
content of "the physical seed needs `ρ_k`-weighted kernels": `physHSMixN` satisfies the weighted
`hrow`,
which the bare kernel could not (numerically confirmed to `1.5e-9` vs analytic `c_HS`,
`volterra_extseed.py`).

Yukawa-free (Mathlib + the HS-layer `HSMix`/`MatrixQ0`/`PhysHSMix` + scalar `BaxterRealSpace`).
-/

namespace FMSA.HSMix

open FMSA.MatrixQ0 FMSA.HardSphere

variable {N : ℕ}

/-- **`ρ_k`-weighted (column-scaled) Baxter kernel** — `q0MixEntryW X i j = ρⱼ · q0MixEntry X i j`.
The density weight on the summed (second) index that turns the seed's row-sum into the scalar
`q0_poly`; the bare `q0MixEntry` (physical `Q0phys` are `ρ`-stripped) does not. -/
noncomputable def q0MixEntryW (X : FMSA.HSMix N) (i j : Fin N) (r : ℝ) : ℝ :=
  X.rho j * X.q0MixEntry i j r

/-- **`q0MixEntryW` row-sum = the `ρ_k`-weighted `q0MixEntry` row-sum** (pull the constant `ρⱼ`
weights into the sum). -/
theorem q0MixEntryW_rowSum (X : FMSA.HSMix N) (i : Fin N) (r : ℝ) :
    (∑ k, X.q0MixEntryW i k r) = ∑ k, X.rho k * X.q0MixEntry i k r := rfl

/-- **Physical `Q0phys` collapses to the scalar `q'_py` at equal diameters.**  With every `σₖ = s`,
`Rᵢₖ = s`, `σᵢσₖ = s²`, and `π·ξ₂·s = 6η` (`ξ₂ = (∑ρ)s²`, `η = (π/6)(∑ρ)s³`), the Lebowitz
`Q0phys = (2π/vac)(s + π ξ₂ s²/(4vac))` simplifies to `π s (2+η)/(1−η)² = q'_py η s`. -/
theorem Q0phys_equalDiam {rho sigma : Fin N → ℝ} {s : ℝ} (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) :
    Q0phys rho sigma i k = q_prime_py (etaMix rho sigma) s := by
  have hkey : Real.pi * xi2 rho sigma * s = 6 * etaMix rho sigma := by
    simp only [xi2, etaMix, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by rw [hs j]; ring)
  have hps : Real.pi * s ≠ 0 := by positivity
  have hxi : xi2 rho sigma = 6 * etaMix rho sigma / (Real.pi * s) := by
    rw [eq_div_iff hps]; linarith [hkey]
  have hv : (1 : ℝ) - etaMix rho sigma ≠ 0 := hvac
  simp only [Q0phys, hs i, hs k, q_prime_py, hxi, vacMix]
  field_simp
  ring

/-- **Physical `Qppphys` collapses to the scalar `q''_py` at equal diameters.**  With `σₖ = s` and
`π ξ₂ s = 6η`, `Qppphys = (2π/vac)(1 + π ξ₂ s/(2vac))` becomes `2π(1+2η)/(1−η)² = q''_py η`. -/
theorem Qppphys_equalDiam {rho sigma : Fin N → ℝ} {s : ℝ} (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) :
    Qppphys rho sigma i k = q_doubleprime_py (etaMix rho sigma) := by
  have hkey : Real.pi * xi2 rho sigma * s = 6 * etaMix rho sigma := by
    simp only [xi2, etaMix, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by rw [hs j]; ring)
  have hps : Real.pi * s ≠ 0 := by positivity
  have hxi : xi2 rho sigma = 6 * etaMix rho sigma / (Real.pi * s) := by
    rw [eq_div_iff hps]; linarith [hkey]
  have hv : (1 : ℝ) - etaMix rho sigma ≠ 0 := hvac
  simp only [Qppphys, hs k, q_doubleprime_py, hxi, vacMix]
  field_simp
  ring

/-- **⭐ Physical `ρ_k`-weighted row-sum = scalar `q0_poly` at equal diameters** — the enabling
`hrow` for the seed reduction.  At equal diameters `Q0phys`/`Qppphys` collapse to the scalar
`q'_py`/`q''_py` (previous two lemmas), and the density weights sum to the total density `∑ₖ ρₖ`
that the scalar `q0_poly` carries: `∑ₖ ρₖ·q0MixEntry(physHSMixN)ᵢₖ(u) = q0_poly η s (∑ₖ ρₖ) u` for
`u ∈ [0,s]`.  This is precisely what the BARE `∑ₖ q0MixEntryᵢₖ` fails to satisfy (off by the missing
density weight) — the concrete Lean content of "the physical seed needs `ρ_k`-weighted kernels". -/
theorem physHSMixN_rhoWeighted_rowSum {rho sigma : Fin N → ℝ} {s : ℝ} (hsig : ∀ k, 0 < sigma k)
    (hs : ∀ k, sigma k = s) (hs0 : 0 < s) (hvac : vacMix rho sigma ≠ 0)
    (i : Fin N) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) s) :
    (∑ k, (physHSMixN rho sigma hsig).rho k * (physHSMixN rho sigma hsig).q0MixEntry i k u)
      = q0_poly (etaMix rho sigma) s (∑ k, rho k) u := by
  have hR : ∀ k, (physHSMixN rho sigma hsig).R i k = s := by
    intro k; simp only [physHSMixN, FMSA.HSMix.R, hs i, hs k]; ring
  have hlam : ∀ k, (physHSMixN rho sigma hsig).lam i k = 0 := by
    intro k; simp only [physHSMixN, FMSA.HSMix.lam, hs i, hs k]; ring
  have hentry : ∀ k, (physHSMixN rho sigma hsig).q0MixEntry i k u
      = q_prime_py (etaMix rho sigma) s * (u - s)
        + q_doubleprime_py (etaMix rho sigma) * ((u - s) ^ 2 / 2) := by
    intro k
    have hmem : u ∈ Set.Icc ((physHSMixN rho sigma hsig).lam i k)
        ((physHSMixN rho sigma hsig).R i k) := by rw [hlam k, hR k]; exact hu
    rw [FMSA.HSMix.q0MixEntry, Set.indicator_of_mem hmem, hR k]
    simp only [physHSMixN]
    rw [Q0phys_equalDiam hs hs0 hvac i k, Qppphys_equalDiam hs hs0 hvac k k]
    ring
  calc (∑ k, (physHSMixN rho sigma hsig).rho k * (physHSMixN rho sigma hsig).q0MixEntry i k u)
      = ∑ k, rho k * (q_prime_py (etaMix rho sigma) s * (u - s)
          + q_doubleprime_py (etaMix rho sigma) * ((u - s) ^ 2 / 2)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hentry k]; simp only [physHSMixN]
    _ = (∑ k, rho k) * (q_prime_py (etaMix rho sigma) s * (u - s)
          + q_doubleprime_py (etaMix rho sigma) * ((u - s) ^ 2 / 2)) := by rw [← Finset.sum_mul]
    _ = q0_poly (etaMix rho sigma) s (∑ k, rho k) u := by rw [q0_poly_inner hu.2]; ring

open MeasureTheory FMSA.MixtureOzStar FMSA.HardSphere in
/-- **⭐⭐ The `ρ_k`-weighted physical windowed seed reduces to `r·c_HS` at equal diameters.**  With
the column-scaled kernel `q0MixEntryW (physHSMixN)` (`= ρ_k·q0MixEntry`), the second Baxter
convolution `matBaxterUQm` equals `r·c_HS` for the physical Lebowitz mixture at equal diameters —
what the BARE `q0MixEntry` could NOT achieve (its row-sum misses the density weight, `hrow` fails).
The `hrow` input is discharged by `physHSMixN_rhoWeighted_rowSum`; the renewal side-conditions
`hUouter`/`hint` are taken as hypotheses here.  They are DISCHARGED (via the constructed
`ρ`-weighted Banach–Volterra renewal on the continuous `q0MixPolyMatW` kernel) in
`matBaxterUQm_physHSMixRhoWeight_eq_rcHS` (`YukawaOZMix/PhysMixRhoWeightRenewal.lean`), giving the
UNCONDITIONAL equal-diameter reduction.  This is the Lean realisation of the `ρ_k`-weighting fix. -/
theorem matBaxterUQm_rhoWeighted_physHSMix_eq_rcHS
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {rho sigma : Fin N → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (hetalt : etaMix rho sigma < 1)
    (hUouter : ∀ i j r, s ≤ r →
      matBaxterU Psi (fun a b => (physHSMixN rho sigma hsig).q0MixEntryW a b) s i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => (physHSMixN rho sigma hsig).q0MixEntryW i k t
        * matBaxterU Psi (fun a b => (physHSMixN rho sigma hsig).q0MixEntryW a b) s k j (r + t))
        volume 0 s)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-s) s → Psi k j v = -v)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQm Psi (fun a b => (physHSMixN rho sigma hsig).q0MixEntryW a b) s i j r
      = r * c_HS (etaMix rho sigma) s r := by
  have hetadef : etaMix rho sigma = Real.pi * (∑ k, rho k) * s ^ 3 / 6 := by
    have hsum : (∑ k, rho k * sigma k ^ 3) = (∑ k, rho k) * s ^ 3 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by rw [hs k])
    simp only [etaMix, hsum]; ring
  refine matBaxterUQm_eq_rcHS_of_rowSum Psi _ hs0 hetalt hetadef hUouter hint ?_ ?_ ?_ hcore hr i j
  · intro i' u hu
    exact physHSMixN_rhoWeighted_rowSum hsig hs hs0 hvac i' u hu
  · intro i' k
    exact (q0MixEntry_intervalIntegrable (physHSMixN rho sigma hsig) i' k 0 s).const_mul _
  · intro i' k
    convert (q0MixEntry_mul_id_intervalIntegrable (physHSMixN rho sigma hsig) i' k 0 s).const_mul
      ((physHSMixN rho sigma hsig).rho k) using 1
    funext t; simp only [q0MixEntryW]; ring

end FMSA.HSMix

