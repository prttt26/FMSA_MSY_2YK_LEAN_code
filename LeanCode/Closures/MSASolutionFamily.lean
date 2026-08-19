/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSABlumHoyeSystem
import LeanCode.Closures.FirstOrderEquivalence

/-!
# The MSA solution family in the coupling — Group `MSAFAM.3` and the `γ = 1` payoff

Records: `Lean_code/proof_notes_closures.md`, "Group MSAFAM".

This file carries the two parts of MSAFAM that live at Layer 5 (closures) and consume both the
concrete Blum–Høye system (`YukawaOZ/MSABlumHoyeSystem.lean`, MSAFAM.1–2) and FOEQ.5's `C¹` capstone
(`Closures/FirstOrderEquivalence.lean`):

* **MSAFAM.3** — `exists_contDiffAt_root_of_prodDomain_ift`, the `C^n` prod-domain implicit
  function, the drop-in `ContDiffAt` upgrade of FOEQ.5's `exists_hasDerivAt_root_of_prodDomain_ift`.
  This
  closes gap (B) (order: `γ = 1` → every `γ`) — Mathlib's pinned
  `ContDiffAt.contDiffAt_implicitFunction` supplies it directly.
* **the `γ = 1` payoff** — `msa_amplitude_differentiableAt_yukawa`: FOEQ.5's capstone applied to the
  *concrete* `bhF`/`bhP` with the four MSAFAM.2 properties discharged, so at `N = 1` the amplitude's
  differentiability at `K = 0` holds with **no** analytic hypothesis, only `ξ ∈ (0,1)` and `z > 0`.
  This closes gap (A).

⚠ These do **not** close the group.  Gap (C) — the amplitude `Dt(K)` → the pair family
`(H̃(τ), C̃(τ))` obeying OZ (MSAFAM.5) — is gated on **MSAEXACT.1**'s open closure-recovery core,
and MSAFAM.6/.7 sit above it.  The honest interim headline is *"FOEQ.5's capstone is now
hypothesis-free at `γ = 1`, and holds at every `γ`; it still produces an amplitude, not a solution
family."*
-/

namespace FMSA.MSASolutionFamily

open Real Filter Topology
open scoped ContDiff

/-! ## MSAFAM.3 — the `C^n` prod-domain implicit function -/

/-- **MSAFAM.3 — the `C^n` prod-domain implicit function theorem.**  A map
`g : ℝ × (ℝ × ℝ) → (ℝ × ℝ)` that is `C^n` at `(0, p₀)` (with `n ≠ 0`), with `g (0, p₀) = 0` and an
**invertible second-factor partial** `fderiv g (0,p₀) ∘L inr`, has an implicit root `ψ : ℝ → ℝ × ℝ`
through it — `ψ 0 = p₀`, `g (K, ψ K) = 0` for `K` near `0`, and now `ψ` is itself `C^n` at `0`.

This is the smoothness-preserving upgrade of FOEQ.5's `exists_hasDerivAt_root_of_prodDomain_ift`
(which delivers only `HasDerivAt ψ ψ' 0`), obtained from Mathlib's
`ContDiffAt.contDiffAt_implicitFunction`.  It is what carries Theorem I.1's `γ = 1`
differentiability to the `∀ γ`-fold differentiability FOEQ.7/.8 consume: because the Blum–Høye map
is `C^∞`, its root is `C^∞` at `τ = 0` (gap (B)). -/
theorem exists_contDiffAt_root_of_prodDomain_ift {n : ℕ∞ω} (hn : n ≠ 0)
    {g : ℝ × (ℝ × ℝ) → (ℝ × ℝ)} {p₀ : ℝ × ℝ}
    (cg : ContDiffAt ℝ n g (0, p₀)) (hbase : g (0, p₀) = 0)
    (hinv : (fderiv ℝ g (0, p₀) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).IsInvertible) :
    ∃ ψ : ℝ → ℝ × ℝ,
      ψ 0 = p₀ ∧ (∀ᶠ K in 𝓝 (0 : ℝ), g (K, ψ K) = 0) ∧ ContDiffAt ℝ n ψ 0 := by
  refine ⟨cg.implicitFunction hn hinv, ?_, ?_, ?_⟩
  · simpa using cg.implicitFunction_apply_self hn hinv
  · filter_upwards [cg.eventually_apply_implicitFunction hn hinv] with x hx
    rw [hx, hbase]
  · simpa using cg.contDiffAt_implicitFunction hn hinv

/-! ## The `γ = 1` payoff — FOEQ.5 hypothesis-free for the concrete Yukawa system -/

open FMSA.MSAExact FMSA.FirstOrderEquivalence in
/-- ⭐⭐ **MSAFAM.2, assembled — FOEQ.5's capstone, hypothesis-free at `γ = 1`.**  For the *concrete*
Blum–Høye system `bhF`/`bhP` at `N = 1` and its PY base point `G₀ = G0 ξ z`, all four hypotheses of
`msa_amplitude_differentiable_of_bh_shape` are discharged (MSAFAM.2): the `C^∞` smoothness, the
vanishing `G`-directional derivatives, the nonvanishing hard-sphere Baxter factor
`bhF (0, G₀) ≠ 0`, and the PY base equation `2π·G₀·bhF(0,G₀) = bhP(0,G₀)`.  Hence for any packing
fraction `ξ ∈ (0,1)` and inverse range `z > 0`, the exact-MSA tail amplitude is **differentiable at
`K = 0`** — the object FOEQ.1–4 take as a hypothesis, now *produced* with no analytic assumption.

This is the deliverable of gap (A): FOEQ.5 is no longer conditional on the transcription of
`F, P, A, q′, Q̂` at `N = 1`.  It is **not** the removal of Theorem I.1's hypothesis, which is the
whole pair family (gap (C), MSAFAM.5, gated on MSAEXACT.1). -/
theorem msa_amplitude_differentiableAt_yukawa {xi z : ℝ}
    (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) (hz : 0 < z) :
    ∃ D : ℝ → ℝ, D 0 = 0 ∧ DifferentiableAt ℝ D 0 :=
  msa_amplitude_differentiable_of_bh_shape (z := z)
    ((bhF_contDiff xi z).of_le (by exact_mod_cast le_top))
    ((bhP_contDiff xi z).of_le (by exact_mod_cast le_top))
    (bhF_fderiv_snd xi z (G0 xi z)) (bhP_fderiv_snd xi z (G0 xi z))
    (bhF_base_ne_zero hxi hz) (bh_base_eq hxi hz)

end FMSA.MSASolutionFamily
