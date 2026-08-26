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
theorem exists_contDiffAt_root_of_prodDomain_ift {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {n : ℕ∞ω} (hn : n ≠ 0)
    {g : ℝ × E → E} {p₀ : E}
    (cg : ContDiffAt ℝ n g (0, p₀)) (hbase : g (0, p₀) = 0)
    (hinv : (fderiv ℝ g (0, p₀) ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    ∃ ψ : ℝ → E,
      ψ 0 = p₀ ∧ (∀ᶠ K in 𝓝 (0 : ℝ), g (K, ψ K) = 0) ∧ ContDiffAt ℝ n ψ 0 := by
  refine ⟨cg.implicitFunction hn hinv, ?_, ?_, ?_⟩
  · simpa using cg.implicitFunction_apply_self hn hinv
  · filter_upwards [cg.eventually_apply_implicitFunction hn hinv] with x hx
    rw [hx, hbase]
  · simpa using cg.contDiffAt_implicitFunction hn hinv

/-! ## The `γ = 1` payoff — FOEQ.5 hypothesis-free for the concrete Yukawa system -/

open FMSA.ExactMSA FMSA.FirstOrderEquivalence in
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

/-! ## MSAFAM.5 — the transport half (the pair family from the Baxter transform)

MSAFAM.5 has two halves (proof note, gap (C)):

* **the transport** — given the Baxter transform `τ ↦ (Q̂(k,τ), Q̂(−k,τ))` along the coupling as a
  smooth family, non-vanishing at `τ = 0`, produce the pair `(H̃, C̃)` obeying OZ and smooth near `0`.
  `C̃ = 1 − Q̂(k)Q̂(−k)` is explicit and `H̃ = (1−C̃)⁻¹ − 1`, so OZ is definitional and the only real
  content is smoothness + the non-vanishing that lets `(·)⁻¹` be taken. **This is done below.**
* **the identity** — that the amplitudes `ψ(τ)` of the Blum–Høye system actually give a Baxter
  factorization `1 − ρĉ_MSA = Q̂(k)Q̂(−k)` with `ĉ_MSA` the MSA closure DCF. **This is MSAEXACT.1's
  open closure-recovery core** (a multi-file effort re-running `baxter_wiener_hopf_factorization` with
  the tails) and is NOT attempted here.

So `msaSolutionFamily_transport` closes the transport half unconditionally, reducing MSAFAM.5 to a
single remaining input: **the concrete `ContDiff` family `τ ↦ Q̂(±k, ψ(τ))`** — the `k`-space Baxter
transform of `msaBaxterFn` evaluated along the `MSAFAM.3` root `ψ` (`exists_contDiffAt_root_…`), with
`Q̂(k,0) ≠ 0` (no spinodal at the PY point on the `k`-axis).  That transform is MSAEXACT.1 territory. -/

open Filter in
/-- **MSAFAM.5, transport half.**  Let `Qp, Qm : ℝ → ℂ` be the Baxter transform `τ ↦ Q̂(±k, τ)` along
the coupling — smooth at `τ = 0` and with `Q̂(k,0)·Q̂(−k,0) ≠ 0` (which on the real `k` axis is
`|Q̂(k,0)|² > 0`, the no-spinodal condition at the Percus–Yevick point).  Then the MSA pair family
`C̃ = 1 − Q̂(k)Q̂(−k)`, `H̃ = (1−C̃)⁻¹ − 1` is smooth at `0` and obeys the Ornstein–Zernike relation
`(1 + H̃)(1 − C̃) = 1` on a neighbourhood of `0` — exactly the three hypotheses FOEQ.7/.8
(`oz_msa_taylor_eq_hierarchy`, MSAFAM.4-weakened) consume.

The OZ relation is definitional here (`H̃` is *built* from `C̃` through it), so the content is entirely
smoothness + the eventual non-vanishing of `Q̂(k)Q̂(−k)` that lets `(·)⁻¹` be taken.  What this does
**not** supply is the *identity* half — that `1 − C̃` is the MSA closure's DCF factor — which is
MSAEXACT.1. -/
theorem msaSolutionFamily_transport {n : ℕ∞ω} {Qp Qm : ℝ → ℂ}
    (hQp : ContDiffAt ℝ n Qp 0) (hQm : ContDiffAt ℝ n Qm 0)
    (h0 : Qp 0 * Qm 0 ≠ 0) :
    ∃ H C : ℝ → ℂ, ContDiffAt ℝ n C 0 ∧ ContDiffAt ℝ n H 0 ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), (1 + H τ) * (1 - C τ) = 1) := by
  have hW : ContDiffAt ℝ n (fun τ => Qp τ * Qm τ) 0 := hQp.mul hQm
  refine ⟨fun τ => (Qp τ * Qm τ)⁻¹ - 1, fun τ => 1 - Qp τ * Qm τ,
    contDiffAt_const.sub hW, (hW.inv h0).sub contDiffAt_const, ?_⟩
  filter_upwards [hW.continuousAt.eventually_ne h0] with τ hτ
  have : (1 + ((Qp τ * Qm τ)⁻¹ - 1)) * (1 - (1 - Qp τ * Qm τ))
      = (Qp τ * Qm τ)⁻¹ * (Qp τ * Qm τ) := by ring
  rw [this, inv_mul_cancel₀ hτ]

/-! ## MSAFAM.6 — Theorem I.1 at every order, for the transport-built family -/

open FMSA.FirstOrderEquivalence in
/-- **MSAFAM.6, assembled (abstract).**  Given the Baxter transform `τ ↦ (Q̂(k,τ), Q̂(−k,τ))` smooth
(`C^∞`) at `τ = 0` and non-vanishing there, the MSA pair family it transports
(`msaSolutionFamily_transport`) has — at **every** order `m ≥ 1` — order-`m` Taylor coefficients
satisfying the order-`m` line of the coupling hierarchy.  This is Theorem I.1's conclusion (FOEQ.7,
`oz_taylor_coeff_eq_cauchy_convolution`) applied to a *constructed* family instead of a hypothesised
one: `(D1) = (D2)` order by order, with the OZ + smoothness inputs no longer assumed but produced.

⚠ **Why MSAFAM.4 was load-bearing.**  The family solves OZ only on a *neighbourhood* of `0` (it folds
at finite coupling), so `msaSolutionFamily_transport` yields `∀ᶠ s in 𝓝 0` OZ, never the global `∀ s`.
The pre-MSAFAM.4 FOEQ.7/.8 demanded `∀ s` and would have been unusable here; the `∀ᶠ` weakening is
exactly what lets this composition typecheck.

The only input still missing for Theorem I.1 at `N = 1` is the **concrete** transform family
`τ ↦ Q̂(±k, ψ(τ))` — MSAEXACT.1's `k`-space Baxter transform (`msaBaxter_cos/sin_transform`) evaluated
along the MSAFAM.3 root `ψ` (`exists_contDiffAt_root_of_prodDomain_ift`), with `Q̂(k,0) ≠ 0` (no
spinodal at the PY point on the `k`-axis).  Everything downstream of that single input is assembled
here. -/
theorem msaFamily_taylor_eq_hierarchy {Qp Qm : ℝ → ℂ}
    (hQp : ContDiffAt ℝ ∞ Qp 0) (hQm : ContDiffAt ℝ ∞ Qm 0) (h0 : Qp 0 * Qm 0 ≠ 0) :
    ∃ H C : ℝ → ℂ,
      (∀ᶠ τ in 𝓝 (0 : ℝ), (1 + H τ) * (1 - C τ) = 1) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℂ) * iteratedDeriv i (fun s => 1 + H s) 0
            * iteratedDeriv (m - i) (fun s => 1 - C s) 0 = 0 := by
  obtain ⟨H, C, hC, hH, hOZ⟩ := msaSolutionFamily_transport hQp hQm h0
  refine ⟨H, C, hOZ, fun m hm => ?_⟩
  exact oz_taylor_coeff_eq_cauchy_convolution H C hm
    (hH.of_le (by exact_mod_cast le_top)) (hC.of_le (by exact_mod_cast le_top)) hOZ

end FMSA.MSASolutionFamily
