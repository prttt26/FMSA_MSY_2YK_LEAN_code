/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Paley–Wiener / Wiener-algebra renewal decay — Group MA axiom (awaiting processing)

Registry: `MATH_AXIOMS.md`, task `MA.13` (Paley–Wiener renewal). **Status: axiom, awaiting
processing (retire-by-proving intended).**

## Statement

For a **right-compactly-supported** continuous kernel `q` (`q = 0` on `(S, ∞)`) and a continuous
forcing `g` that vanishes on a right tail, if the **Laplace symbol** `1 − q̂(z)`,
`q̂(z) = ∫₀^S q(t) e^{−zt} dt`, has **no zero in the closed right half-plane** `{Re z ≥ 0}`, then
(unique, continuous) solution of the renewal / Volterra second-kind equation

  `ψ(r) = g(r) + ∫₀^r q(r−t) ψ(t) dt`   (`r ≥ 0`)

both decays (`ψ(r) → 0` as `r → ∞`) and is **integrable** on `(0,∞)`.  Both follow from the same
Paley–Wiener resolvent representation `ψ = g + R ⋆ g` with `g` compactly supported (hence `L¹`) and
`R ∈ L¹` the causal Wiener resolvent, so `ψ ∈ L¹(ℝ₊)` and `ψ → 0`.

**Only `q|_{[0,S]}` enters.** The equation evaluates `q` at `r − t ∈ [0, r] ≥ 0` and the symbol
integrates over `[0, S]`, so the kernel's values on `(−∞, 0)` are irrelevant to both the equation
and the conclusion. The hypothesis therefore requires only `q = 0` on `(S, ∞)` — **no `t < 0`
"causality" clause** (which would be unsatisfiable by the intended instance `q0_poly`, a nonzero
polynomial for `t < 0`). Dropping it strengthens the statement (weaker hypothesis) without affecting
truth, and makes it instantiable at `q0_poly`. Verified numerically (`ma13_verify.py`,
`ma13_dense.py`): dense **negative** kernels (matching `q0_poly`'s sign, `‖q‖₁ ≥ 1`) with symbol
nonvanishing on the RHP give decay; a symbol with any RHP zero gives exponential growth (the symbol
hypothesis is load-bearing, not vacuous).

## Why this is genuinely axiom-worthy (unlike MA.10/MA.11/MA.12, which were proved)

The proof is the classical **Wiener–Lévy / Paley–Wiener** argument: the symbol is `→ 1` at infinity
in the closed RHP (`q̂ → 0`, `q` compactly supported), so nonvanishing on `{Re z ≥ 0}` gives, by
**Wiener's `1/f` theorem** in the Banach algebra `ℂ · δ ⊕ L¹`, a resolvent kernel `R ∈ L¹` that is
**causal** (index/winding `0`, from the whole-half-plane nonvanishing), whence `ψ = g + R ⋆ g → 0`
for compactly-supported `g`. Mathlib currently lacks Wiener's `1/f` (Gelfand) theorem / the Wiener
algebra inversion, so this is registered as an axiom rather than proved — a genuine gap, not a
convenience. It is a **pure analysis** statement (no physics), the reason it belongs to Group MA.

## Intended instantiation (the deferred "processing")

Discharge the `Tendsto (baxterPsiOuter …) atTop (𝓝 0)` hypothesis of
`baxterPsi_bounded_Ici_of_tendsto_zero` / `r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero`
(`HardSphere/BaxterExteriorDecayReduction.lean`) at `q := q0_poly`, `g := baxterForcing`,
`ψ := baxterPsiOuter` — after the `[σ,∞) → [0,∞)` shift and the symbol identification `z = i k`
(so `{Re z ≥ 0} ↔ {Im k ≤ 0}`, matching `Qhat_complex(k) ≠ 1` on the closed lower half-plane; cf.
`HardSphere/BaxterHermiteBiehler.lean`). That wiring is the pending processing step.
-/

open MeasureTheory Filter Topology intervalIntegral

namespace FMSA

/-- **Paley–Wiener / Wiener-algebra renewal decay (Group MA, awaiting processing).**  A causal
compactly-supported kernel whose Laplace symbol is nonvanishing on the closed right half-plane
yields a decaying Volterra/renewal solution.  See the module docstring for provenance and the
intended physical instantiation. -/
axiom volterra_renewal_tendsto_zero {q g ψ : ℝ → ℝ} {S : ℝ} (hS : 0 < S)
    (hq : Continuous q) (hg : Continuous g)
    (hqsupp : ∀ t : ℝ, S < t → q t = 0)
    (hgsupp : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → g t = 0)
    (hψcont : ContinuousOn ψ (Set.Ici (0 : ℝ)))
    (hsymbol : ∀ z : ℂ, 0 ≤ z.re →
      1 - (∫ t in (0:ℝ)..S, (q t : ℂ) * Complex.exp (-z * (t : ℂ))) ≠ 0)
    (hψ : ∀ r : ℝ, 0 ≤ r → ψ r = g r + ∫ t in (0:ℝ)..r, q (r - t) * ψ t) :
    Tendsto ψ atTop (𝓝 0) ∧ IntegrableOn ψ (Set.Ioi 0)

end FMSA
