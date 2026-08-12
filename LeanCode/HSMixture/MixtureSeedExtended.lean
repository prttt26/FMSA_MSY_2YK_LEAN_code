/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.MixtureBaxterSeed

/-!
# Extended (full-line) Baxter seed convolutions — the generic Matrix machinery (Yukawa-free)

The `∫_ℝ` (full-line) counterparts of `matBaxterU`'s `∫₀^σ` (windowed) first Baxter convolution, and
the transposed / extended variants, together with the three purely-algebraic bridges relating them.

**Every object here is Matrix-generic** — it takes abstract Baxter data `Psi Q : Matrix (Fin N)
(Fin N) (ℝ → ℝ)` and proves facts with Mathlib alone; there is no hard-sphere or Yukawa content.  It
was previously stranded in the Yukawa layer (`YukawaOZMix/MixtureRowSum.lean`,
`MixtureCorrectedSeed.lean`) only because those files' import chains run through the Yukawa `Mix`
structure.  Homing it here at the HSMixture layer lets the pure-HS windowing-loss bridges
(`HSMixture/HSMixWindowingBridge.lean`) be stated Yukawa-free; the Yukawa layer re-uses these by
import (same `FMSA.MixtureOzStar` namespace).
-/

open MeasureTheory Set

namespace FMSA.MixtureOzStar

variable {N : ℕ}

/-- **Transposed first Baxter convolution `Ψ ⋆ Qᵀ`** — inner factor `Qₘᵢ` (transpose of
`matBaxterU`'s `Qᵢₘ`).  As the second factor in the seed product this makes both `Q`-factors carry
the **second** index, i.e. the `matSelfConv` (`Q⋆Qᵀ`) structure. -/
noncomputable def matBaxterUt {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  Psi i j r - ∑ m, ∫ s in (0:ℝ)..sigma, Q m i s * Psi m j (r - s)

/-- **The transposed first convolution is `matBaxterU` at `Qᵀ`.**  `matBaxterUt Psi Q = matBaxterU
Psi Qᵀ` (`Qᵀ a b = Q b a`) — the two `∑`s coincide after renaming the species index.  So every
`matBaxterU`-lemma applies to `matBaxterUt` by instantiating at the transposed kernel; in particular
the transposed claim `(A)`/`(B)` are the existing `matBaxterU_outer`/`matBaxterU_core` at `Qᵀ`. -/
theorem matBaxterUt_eq_transpose (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (i j : Fin N)
    (r : ℝ) :
    matBaxterUt Psi Q sigma i j r = matBaxterU Psi (fun a b => Q b a) sigma i j r := rfl

/-- **Extended (full-line) first Baxter convolution** — `matBaxterU` with `∫_ℝ` instead of `∫₀^σ`,
so the Baxter factor `Q(i,k)` is integrated over its TRUE support `[λᵢₖ, Rᵢₖ]` (recovering the
sub-zero tail `[λᵢₖ, 0)` the `[0,σ]` window drops when `σₖ < σᵢ`).  The fix for the windowing loss:
its fold-kernel is the full-line DCF `matDCFfull`, symbol `Cmix0` (`matDCFfull_shell_laplace`), not
the lossy windowed `K`. -/
noncomputable def matBaxterUExt (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i j : Fin N) (r : ℝ) :
    ℝ :=
  Psi i j r - ∑ k, ∫ t, Q i k t * Psi k j (r - t)

/-- **Extended transposed first convolution** — `matBaxterUt` with `∫_ℝ`; same `Qᵀ`-instantiation
as the windowed version. -/
noncomputable def matBaxterUtExt (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i j : Fin N) (r : ℝ) :
    ℝ :=
  Psi i j r - ∑ m, ∫ s, Q m i s * Psi m j (r - s)

/-- **The extended transposed convolution is `matBaxterUExt` at `Qᵀ`** — pure `rfl`, as in the
windowed case (`matBaxterUt_eq_transpose`).  So the full-line transposed claims `(A)`/`(B)` are the
full-line `matBaxterUExt`-lemmas at `Qᵀ`. -/
theorem matBaxterUtExt_eq_transpose (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i j : Fin N) (r : ℝ) :
    matBaxterUtExt Psi Q i j r = matBaxterUExt Psi (fun a b => Q b a) i j r := rfl

/-- **The dropped tail, made explicit** — extended and windowed first convolutions differ by exactly
the sub-zero Baxter-factor tail: `matBaxterUExt = matBaxterU − ∑ₖ ∫_{Iic 0} Qᵢₖ(t)·Ψₖⱼ(r−t)`.  For
`Q = q0MixEntry` (support `[λᵢₖ, Rᵢₖ]`, `Rᵢₖ ≤ σ`) the `(σ,∞)` part is `0`, so the tail is the
`[λᵢₖ, 0)` piece the `[0,σ]` window drops — the concrete content of the extension. -/
theorem matBaxterUExt_eq_matBaxterU_sub_tail (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (i j : Fin N) (r : ℝ)
    (hsplit : ∀ k, (∫ t, Q i k t * Psi k j (r - t))
      = (∫ t in (0 : ℝ)..sigma, Q i k t * Psi k j (r - t))
        + ∫ t in Set.Iic (0 : ℝ), Q i k t * Psi k j (r - t)) :
    matBaxterUExt Psi Q i j r
      = matBaxterU Psi Q sigma i j r
        - ∑ k, ∫ t in Set.Iic (0 : ℝ), Q i k t * Psi k j (r - t) := by
  unfold matBaxterUExt matBaxterU
  simp only [hsplit, Finset.sum_add_distrib]
  ring

/-! ### Generic constructed-renewal helpers (Matrix-generic; moved from the Yukawa layer)

The core-convolution forcing `matForcingCore` and the measurability / boundedness of the glued
`matBaxterPsi` entry — all Matrix-generic, needed to discharge the constructed-renewal side-conditions
of the pure-HS physical windowing bridges (`HSMixture/PhysHSMixWindowing.lean`). -/

/-- **General core-convolution forcing** `Fm r := (∑ₖ ∫₀^σ Qm(r−s)ᵢₖ·(−s) ds)ᵢⱼ`. -/
noncomputable def matForcingCore {N : ℕ} (Qm : ℝ → Matrix (Fin N) (Fin N) ℝ) (sigma : ℝ) :
    ℝ → Matrix (Fin N) (Fin N) ℝ :=
  fun r => Matrix.of (fun i j => ∑ k, ∫ s in (0:ℝ)..sigma, (Qm (r - s)) i k * (-s))

theorem matForcingCore_continuous {N : ℕ} (Qm : ℝ → Matrix (Fin N) (Fin N) ℝ) (sigma : ℝ)
    (hQ : Continuous Qm) : Continuous (matForcingCore Qm sigma) := by
  refine continuous_matrix (fun i j => ?_)
  simp only [matForcingCore, Matrix.of_apply]
  refine continuous_finset_sum _ (fun k _ => ?_)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (r : ℝ) (s : ℝ) => (Qm (r - s)) i k * (-s))
  exact ((hQ.comp (continuous_fst.sub continuous_snd)).matrix_elem i k).mul continuous_snd.neg

/-- Measurability of the glued `matBaxterPsi` entry (measurable branches). -/
theorem matBaxterPsi_entry_measurable {N : ℕ} (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hPo : ∀ k j, Measurable (Po k j)) (hPc : ∀ k j, Measurable (Pc k j)) (k j : Fin N) :
    Measurable (matBaxterPsi Po Pc sigma k j) := by
  unfold matBaxterPsi
  refine Measurable.ite measurableSet_Ici (hPo k j) ?_
  exact Measurable.ite measurableSet_Iic (((hPo k j).comp measurable_neg).neg) (hPc k j)

/-- The glued `matBaxterPsi` entry is bounded on every `uIcc a b` (continuous branches). -/
theorem matBaxterPsi_entry_bddOn {N : ℕ} (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hPo : ∀ k j, Continuous (Po k j)) (hPc : ∀ k j, Continuous (Pc k j)) (k j : Fin N) (a b : ℝ) :
    ∃ C, ∀ x ∈ Set.uIcc a b, |matBaxterPsi Po Pc sigma k j x| ≤ C := by
  obtain ⟨Cpo, hCpo⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    (hPo k j).continuousOn
  obtain ⟨Cpo', hCpo'⟩ := (isCompact_uIcc (a := -b) (b := -a)).exists_bound_of_continuousOn
    (hPo k j).continuousOn
  obtain ⟨Cpc, hCpc⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    (hPc k j).continuousOn
  refine ⟨max Cpo 0 + max Cpo' 0 + max Cpc 0, fun x hx => ?_⟩
  have hn2 : (0:ℝ) ≤ max Cpo' 0 := le_max_right _ _
  have hn3 : (0:ℝ) ≤ max Cpc 0 := le_max_right _ _
  have hn1 : (0:ℝ) ≤ max Cpo 0 := le_max_right _ _
  unfold matBaxterPsi
  by_cases h1 : sigma ≤ x
  · rw [if_pos h1]
    have hb := hCpo x hx; rw [Real.norm_eq_abs] at hb
    have : |Po k j x| ≤ max Cpo 0 := le_trans hb (le_max_left _ _)
    linarith
  · rw [if_neg h1]
    by_cases h2 : x ≤ -sigma
    · rw [if_pos h2, abs_neg]
      have hneg : -x ∈ Set.uIcc (-b) (-a) := by
        rcases Set.mem_uIcc.mp hx with ⟨h, h'⟩ | ⟨h, h'⟩
        · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
        · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
      have hb := hCpo' (-x) hneg; rw [Real.norm_eq_abs] at hb
      have : |Po k j (-x)| ≤ max Cpo' 0 := le_trans hb (le_max_left _ _)
      linarith
    · rw [if_neg h2]
      have hb := hCpc x hx; rw [Real.norm_eq_abs] at hb
      have : |Pc k j x| ≤ max Cpc 0 := le_trans hb (le_max_left _ _)
      linarith

end FMSA.MixtureOzStar
