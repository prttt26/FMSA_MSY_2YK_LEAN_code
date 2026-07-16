/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.WHSupports

/-!
# Task Y1.3b — support-orthogonality causal projection ([LN] §6.3, Eq. 61–62)

The last step of the Wiener–Hopf isolation `B₁ = {T_U}^{[R,∞)}`: split the first-order OZ equation
`L = T_U + T_S` into its `[R,∞)` (causal) and `(−∞,R)` (anti-causal) parts.  `L = Q̂₀ᵀ Ĥ₁ Q̂₀` is
`[R,∞)`-supported (hard core: `h^{(1)}` vanishes below contact), and `T_S = [Q̂₀]⁻¹ S₁ [Q̂₀ᵀ]⁻¹` is
`(−∞,R)`-supported (`S₁` = inner-core DCF).  Matching the causal parts gives `L = {T_U}^{[R,∞)}`.

**Done in *real space*, not [LN]'s Hilbert-transform k-space.**  [LN] §6.3 performs this split via the
Hilbert transform / Cauchy P.V. — the `{·}^{[R,∞)}` projection is a singular integral operator in
`k`-space, and identifying it needs FT injectivity on half-line supports (which Mathlib lacks).  In
**real space** the projection is simply multiplication by the indicator `1_{[R,∞)}`: it is manifestly
linear, fixes `[R,∞)`-supported functions, and annihilates `(−∞,R)`-supported ones, so the
support-orthogonality argument is *elementary* (`Set.indicator`).  The OZ equation `hOZ` and the two
support hypotheses are the physical / Y1.3a-style inputs (the supports come from `WHSupports.lean`'s
`q0MixEntry_support_subset` etc. + the hard-core vanishing of `h^{(1)}`); the derivation itself is
complete and axiom-clean — no Hilbert transform, no FT-inversion of the distributional Baxter factors.

## Results

* `causal_projection_real` — the real-space support-orthogonality identity: given `L = T_U + T_S`,
  `support L ⊆ [R,∞)`, `support T_S ⊆ (−∞,R)`, then `L = 1_{[R,∞)} · T_U` (`= {T_U}^{[R,∞)}`).
* `causal_projection_fourier` — its Fourier form `L̂(k) = ∫_{[R,∞)} T_U(r) e^{−ikr} dr = {T̂_U}^{[R,∞)}`,
  the `B₁ = {T_U}^{[R,∞)}` statement.  Combined with Y1.3c (`outer_residue`, whose Yukawa-pole residue
  is `[G·K·Gᵀ]`) this closes the Wiener–Hopf derivation of the spectral amplitude `b_{ij}` (Y1.5).

Status: ✓ DONE (Y1.3b, support-orthogonality core), axiom-clean.  The remaining physics inputs (that
the concrete `L`/`T_S` satisfy the support hypotheses, and the OZ equation) are Y1.3a + standard.
-/

set_option linter.style.longLine false

open MeasureTheory Set

namespace FMSA.YukawaWH

/-- **Y1.3b — real-space support-orthogonality projection.**  From the OZ split `L = T_U + T_S` with
`L` supported on `[R,∞)` and `T_S` supported on `(−∞,R)`, the causal function `L` equals the
`[R,∞)`-projection of the outer term: `L = 1_{[R,∞)} · T_U` (real-space `{T_U}^{[R,∞)}`).  Elementary:
the indicator projection fixes `[R,∞)`-supported `L` and annihilates `(−∞,R)`-supported `T_S`. -/
theorem causal_projection_real {L TU TS : ℝ → ℂ} {R : ℝ}
    (hOZ : ∀ r, L r = TU r + TS r)
    (hL : Function.support L ⊆ Set.Ici R)
    (hTS : Function.support TS ⊆ Set.Iio R) :
    L = Set.indicator (Set.Ici R) TU := by
  funext r
  by_cases hr : r ∈ Set.Ici R
  · -- r ≥ R : T_S r = 0 (r ∉ (−∞,R)), so L r = T_U r = indicator r
    have hTSr : TS r = 0 := by
      by_contra h
      have hmem : r ∈ Set.Iio R := hTS (Function.mem_support.mpr h)
      rw [Set.mem_Iio] at hmem; rw [Set.mem_Ici] at hr; linarith
    rw [Set.indicator_of_mem hr, hOZ r, hTSr, add_zero]
  · -- r < R : L r = 0 (r ∉ [R,∞)), indicator r = 0
    have hLr : L r = 0 := by
      by_contra h
      exact hr (hL (Function.mem_support.mpr h))
    rw [Set.indicator_of_notMem hr, hLr]

/-- **Y1.3b — Fourier form `B₁ = {T_U}^{[R,∞)}`.**  The Fourier transform of the causal `L` equals the
half-line (`[R,∞)`) Fourier integral of the outer term `T_U`: `L̂(k) = ∫_{Ici R} T_U(r) e^{−ikr} dr`.
This is the Wiener–Hopf causal part of the first-order OZ equation. -/
theorem causal_projection_fourier {L TU TS : ℝ → ℂ} {R : ℝ} (k : ℝ)
    (hOZ : ∀ r, L r = TU r + TS r)
    (hL : Function.support L ⊆ Set.Ici R)
    (hTS : Function.support TS ⊆ Set.Iio R) :
    ∫ r, L r * Complex.exp (-Complex.I * k * r)
      = ∫ r in Set.Ici R, TU r * Complex.exp (-Complex.I * k * r) := by
  have hpt : ∀ r, Set.indicator (Set.Ici R) TU r * Complex.exp (-Complex.I * k * r)
      = Set.indicator (Set.Ici R) (fun r => TU r * Complex.exp (-Complex.I * k * r)) r := by
    intro r
    by_cases hr : r ∈ Set.Ici R
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul]
  rw [causal_projection_real hOZ hL hTS]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Ici]

end FMSA.YukawaWH
