/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.PhysHSMixRhoWeight
import LeanCode.HSMixture.PhysHSMixWindowing
import LeanCode.YukawaOZMix.MixtureRowSum

/-!
# `ρ_k`-weighted physical windowed seed — renewal side-conditions DISCHARGED

`matBaxterUQm_rhoWeighted_physHSMix_eq_rcHS` (`HSMixture/PhysHSMixRhoWeight.lean`) took the renewal
side-conditions `hUouter`/`hint` as hypotheses.  Here they are discharged by constructing the actual
`ρ`-weighted Banach–Volterra renewal, so the equal-diameter reduction to `r·c_HS` is UNCONDITIONAL
(only physical-data hypotheses remain).

The kernel is the **column-scaled continuous** Baxter poly-matrix
`q0MixPolyMatW X r := (ρ_k·q0MixPoly X i k r)ᵢₖ` — column-scaled (`ρ_k` on the summed 2nd index) to
carry the density weight, using the *continuous* `q0MixPoly` (not truncated `q0MixEntry`) because
the Banach–Volterra renewal and the generic `matBaxterPsi_hUouter` need continuity; the two agree on
`[0,σ]`, all `matBaxterUQm` samples.  `hUouter`/`hint` are the generic
`matBaxterPsi_hUouter`/`matBaxterPsi_hint`; `hrow` is `physHSMixN_rhoWeighted_rowSum` transported
from `q0MixEntry` to `q0MixPoly` (they coincide on the core at equal diameters).
-/

namespace FMSA.HSMix

open MeasureTheory FMSA.MatrixQ0 FMSA.HardSphere FMSA.MixtureOzStar

variable {N : ℕ}

/-- **Column-scaled continuous Baxter poly-matrix kernel** —
`q0MixPolyMatW X r := (ρ_k·q0MixPoly X i k r)ᵢₖ`.  The `ρ_k`-weight on the summed 2nd/column index;
continuous (unlike `q0MixEntryW`) so the Banach–Volterra renewal machinery applies. -/
noncomputable def q0MixPolyMatW (X : FMSA.HSMix N) : ℝ → Matrix (Fin N) (Fin N) ℝ :=
  fun r => Matrix.of (fun i k => X.ρ k * X.q0MixPoly i k r)

theorem q0MixPolyMatW_continuous (X : FMSA.HSMix N) : Continuous (q0MixPolyMatW X) :=
  continuous_matrix (fun i k => by
    simp only [q0MixPolyMatW, Matrix.of_apply]
    exact (q0MixPoly_continuous X i k).const_mul _)

/-- `q0MixPolyMatW X v i k = 0` for `v ≥ Rᵢₖ` (the clamp freezes the poly to `0`). -/
theorem q0MixPolyMatW_eq_zero_of_ge (X : FMSA.HSMix N) (i k : Fin N) {v : ℝ}
    (hR : X.R i k ≤ v) : (q0MixPolyMatW X v) i k = 0 := by
  simp only [q0MixPolyMatW, Matrix.of_apply, q0MixPoly_eq_zero_of_ge X i k hR, mul_zero]

/-- **`q0MixPoly = q0MixEntry` on the core at equal diameters.**  With `Rᵢₖ = s`, `λᵢₖ = 0`, and
`u ∈ [0,s]`, the clamp `min u s = u` and the indicator `[0,s]` both give `Q0(u−s)+Qpp(u−s)²/2`. -/
theorem q0MixPoly_eq_q0MixEntry_core {rho sigma : Fin N → ℝ} {s : ℝ} (hsig : ∀ k, 0 < sigma k)
    (hs : ∀ k, sigma k = s) (i k : Fin N) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) s) :
    (physHSMixN rho sigma hsig).q0MixPoly i k u = (physHSMixN rho sigma hsig).q0MixEntry i k u := by
  have hR : (physHSMixN rho sigma hsig).R i k = s := by
    simp only [physHSMixN, FMSA.HSMix.R, hs i, hs k]; ring
  have hlam : (physHSMixN rho sigma hsig).lam i k = 0 := by
    simp only [physHSMixN, FMSA.HSMix.lam, hs i, hs k]; ring
  rw [FMSA.HSMix.q0MixEntry,
    Set.indicator_of_mem (show u ∈ Set.Icc ((physHSMixN rho sigma hsig).lam i k)
      ((physHSMixN rho sigma hsig).R i k) by rw [hlam, hR]; exact hu)]
  simp only [FMSA.HSMix.q0MixPoly, hR, min_eq_left hu.2]

/-- **`ρ_k`-weighted row-sum for the poly kernel** = `q0_poly` at equal diameters (transported from
the `q0MixEntry` row-sum via `q0MixPoly_eq_q0MixEntry_core`). -/
theorem physHSMixN_rhoWeighted_rowSum_poly {rho sigma : Fin N → ℝ} {s : ℝ} (hsig : ∀ k, 0 < sigma k)
    (hs : ∀ k, sigma k = s) (hs0 : 0 < s) (hvac : vacMix rho sigma ≠ 0)
    (i : Fin N) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) s) :
    (∑ k, (physHSMixN rho sigma hsig).ρ k * (physHSMixN rho sigma hsig).q0MixPoly i k u)
      = q0_poly (etaMix rho sigma) s (∑ k, rho k) u := by
  rw [show (∑ k, (physHSMixN rho sigma hsig).ρ k * (physHSMixN rho sigma hsig).q0MixPoly i k u)
      = ∑ k, (physHSMixN rho sigma hsig).ρ k * (physHSMixN rho sigma hsig).q0MixEntry i k u from
    Finset.sum_congr rfl (fun k _ => by rw [q0MixPoly_eq_q0MixEntry_core hsig hs i k hu])]
  exact physHSMixN_rhoWeighted_rowSum hsig hs hs0 hvac i u hu

/-- **The constructed `ρ`-weighted Banach–Volterra renewal `Ψ`** for `physHSMixN` at scale `s`:
glued core `−v` + `matBaxterPsiOuterFun` of the column-scaled poly kernel. -/
noncomputable def physHSMixNPsiW (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (s : ℝ) :
    Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  matBaxterPsi (fun a b r => (matBaxterPsiOuterFun s (q0MixPolyMatW (physHSMixN rho sigma hsig))
      (matForcingCore (q0MixPolyMatW (physHSMixN rho sigma hsig)) s)
      (q0MixPolyMatW_continuous (physHSMixN rho sigma hsig))
      (matForcingCore_continuous (q0MixPolyMatW (physHSMixN rho sigma hsig)) s
        (q0MixPolyMatW_continuous (physHSMixN rho sigma hsig))) r) a b)
    (fun _ _ v => -v) s

/-- **⭐⭐⭐ UNCONDITIONAL `ρ_k`-weighted physical windowed seed = `r·c_HS` at equal diameters.**
The renewal side-conditions `hUouter`/`hint` of `matBaxterUQm_rhoWeighted_physHSMix_eq_rcHS` are now
DISCHARGED by the constructed `ρ`-weighted renewal `physHSMixNPsiW`: `hUouter` =
`matBaxterPsi_hUouter` (support `q0MixPolyMatW_eq_zero_of_ge` + `matForcingCore` def), `hint` =
`matBaxterPsi_hint`, `hrow` = `physHSMixN_rhoWeighted_rowSum_poly`, `hQ0`/`hQ1` from `q0MixPoly`
continuity, `hcore` = `matBaxterPsi_core`.  Only physical-data hypotheses remain. -/
theorem matBaxterUQm_physHSMixRhoWeight_eq_rcHS {rho sigma : Fin N → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (hetalt : etaMix rho sigma < 1)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQm (physHSMixNPsiW rho sigma hsig s)
      (fun a b t => (q0MixPolyMatW (physHSMixN rho sigma hsig) t) a b) s i j r
      = r * c_HS (etaMix rho sigma) s r := by
  have hQ : Continuous (q0MixPolyMatW (physHSMixN rho sigma hsig)) :=
    q0MixPolyMatW_continuous _
  have hF : Continuous (matForcingCore (q0MixPolyMatW (physHSMixN rho sigma hsig)) s) :=
    matForcingCore_continuous _ s hQ
  have hetadef : etaMix rho sigma = Real.pi * (∑ k, rho k) * s ^ 3 / 6 := by
    have hsum : (∑ k, rho k * sigma k ^ 3) = (∑ k, rho k) * s ^ 3 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by rw [hs k])
    simp only [etaMix, hsum]; ring
  have hRle : ∀ a b, (physHSMixN rho sigma hsig).R a b ≤ s := by
    intro a b; simp only [physHSMixN, FMSA.HSMix.R, hs a, hs b]; linarith
  refine matBaxterUQm_eq_rcHS_of_rowSum (physHSMixNPsiW rho sigma hsig s)
    (fun a b t => (q0MixPolyMatW (physHSMixN rho sigma hsig) t) a b) hs0 hetalt hetadef
    ?_ ?_ ?_ ?_ ?_ ?_ hr i j
  · intro i' j' r' hr'
    exact matBaxterPsi_hUouter s hs0 _ _ hQ hF
      (fun v hv a b => q0MixPolyMatW_eq_zero_of_ge _ a b (le_trans (hRle a b) hv))
      (fun a b _ _ => by simp only [matForcingCore, Matrix.of_apply]) i' j' hr'
  · intro i' j' k' r'
    exact matBaxterPsi_hint s hs0.le _ _ hQ hF i' k' j' r'
  · intro i' u hu
    exact physHSMixN_rhoWeighted_rowSum_poly hsig hs hs0 hvac i' u hu
  · intro i' k
    have hc := (q0MixPolyMatW_continuous (physHSMixN rho sigma hsig)).matrix_elem i' k
    exact hc.intervalIntegrable 0 s
  · intro i' k
    have hc := (q0MixPolyMatW_continuous (physHSMixN rho sigma hsig)).matrix_elem i' k
    exact (continuous_id.mul hc).intervalIntegrable 0 s
  · intro k j' v hv
    exact matBaxterPsi_core _ _ k j' hv

end FMSA.HSMix

