/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixCoreUneq
import LeanCode.YukawaOZMix.MSAEMixBreakpointOrders

/-!
# BRK.9 (Step 2) — the concrete half, discharged against MSAEMIX.4 Stage 3

Group **BRK** (`proof_notes_breakpoints_MSA.md`).  BRK.9 (Step 2 of the BRK.7 scheme) is the
`K`-independence of the exact-MSA core's knot set.  The *abstract* half is
`MSAEMixBreakpointOrders.contDiffOn_paramDeriv_coeffBasis` (K in coefficients only ⇒ K-derivatives
keep the fixed basis, no new knot).  The *concrete* half needs the exact-MSA core to actually have
that form — a finite sum `Σ_k coeff_k(K)·basis_k(r)` with **`K`-free piece boundaries and fixed
basis** — which is **MSAEMIX.4 Stage 3** (`MSAEMixCoreUneq`): the core is 2-piece on `(0, σ_ij)` at
the geometric breakpoint `|λ_ij|`, and *both* pieces are the single form `gForm` in the shared
7-basis `{1, r, r², r³, r⁴, e^{−zr}, e^{zr}}` (the inner piece is `gForm` with `c2 = c3 = c4 = 0`),
with `K` entering only through the coefficients (`c0,…,cEp`), never the fixed basis.

Feeding that basis into the abstract lemma closes BRK.9 concrete: **every `K`-derivative of the core
form is, in `r`, `ContDiffOn` on any set** — so no order adds a knot beyond `|λ_ij|`.
The only remaining input is that the amplitudes are themselves `ContDiff` in `K` (the coefficients
`ContDiff ℝ ⊤`), which the BH root supplies (polynomial/analytic in K); it is carried here
as an explicit hypothesis, not baked in.
-/

open MSAEMixCoreUneq

namespace FMSA.MSAExact.BRK

/-- ⭐ **BRK.9 concrete.**  With `K` entering only the coefficients `c0..cEp` (`ContDiff ℝ ⊤`), every
`K`-derivative of the exact-MSA core form `gForm` is, as a function of `r`, `ContDiffOn ℝ ⊤` on any
set — the fixed basis `{1, r, r², r³, r⁴, e^{−zr}, e^{zr}}` carries no `K`, so no order adds a
knot.  Covers both pieces (the inner one is `gForm` with `c2 = c3 = c4 = 0`). -/
theorem gForm_paramDeriv_contDiffOn (c0 c1 c2 c3 c4 cEm cEp : ℝ → ℝ) (z : ℝ) {s : Set ℝ}
    (h0 : ContDiff ℝ ⊤ c0) (h1 : ContDiff ℝ ⊤ c1) (h2 : ContDiff ℝ ⊤ c2) (h3 : ContDiff ℝ ⊤ c3)
    (h4 : ContDiff ℝ ⊤ c4) (hm : ContDiff ℝ ⊤ cEm) (hp : ContDiff ℝ ⊤ cEp) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n
      (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) K₀) s := by
  have hfun : (fun r => iteratedDeriv n
        (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) K₀)
      = (fun r => iteratedDeriv n
          (fun K => ∑ k, (![c0, c1, c2, c3, c4, cEm, cEp] : Fin 7 → ℝ → ℝ) k K *
            (![fun _ => 1, fun r => r, fun r => r ^ 2, fun r => r ^ 3, fun r => r ^ 4,
              fun r => Real.exp (-z * r), fun r => Real.exp (z * r)] : Fin 7 → ℝ → ℝ) k r) K₀) := by
    funext r; congr 1; funext K
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      gForm]
    ring
  rw [hfun]
  refine contDiffOn_paramDeriv_coeffBasis Finset.univ _ _ ?_ ?_ n K₀
  · intro k _
    fin_cases k <;> assumption
  · intro k _; fin_cases k
    · change ContDiffOn ℝ ⊤ (fun _ => (1 : ℝ)) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r ^ 2) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r ^ 3) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r ^ 4) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => Real.exp (-z * r)) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => Real.exp (z * r)) s; fun_prop

/-- **BRK.8 (Step 1) — geometric smoothness of a core piece.**  Each piece of the exact-MSA core is
the entire function `gForm` (polynomial + exponentials), smooth on all of `ℝ`.  So the core's only
interior knot is the geometric `|λ_ij|`, where `matCoreUneq` switches pieces. -/
theorem contDiff_gForm (c0 c1 c2 c3 c4 cEm cEp z : ℝ) :
    ContDiff ℝ ⊤ (fun r => gForm c0 c1 c2 c3 c4 cEm cEp z r) := by
  unfold gForm; fun_prop

/-- ⭐ **BRK.12 (Step 5) — the all-orders knot set of the core, via the closed form.**  The exact-MSA
core piece is `c = gForm / (2π r)` (`matCoreUneq`).  With `K` in the coefficients only, every
`K`-derivative `∂ⁿ_K c` is, in `r`, `ContDiffOn` on any set avoiding `r = 0` — so `c^{(n)}` has no
interior knot beyond `|λ_ij|`, at every order and every `N`.  Because Stage 3 supplies the core in
closed form, this follows from BRK.9 (`gForm_paramDeriv_contDiffOn`) plus the smooth `1/(2π r)`
factor, **without** the `n`-fold convolution/Leibniz resummation (BRK.10/11/12 as planned): the
closed form makes that route unnecessary. -/
theorem coreForm_paramDeriv_contDiffOn (c0 c1 c2 c3 c4 cEm cEp : ℝ → ℝ) (z : ℝ) {s : Set ℝ}
    (h0 : ContDiff ℝ ⊤ c0) (h1 : ContDiff ℝ ⊤ c1) (h2 : ContDiff ℝ ⊤ c2) (h3 : ContDiff ℝ ⊤ c3)
    (h4 : ContDiff ℝ ⊤ c4) (hm : ContDiff ℝ ⊤ cEm) (hp : ContDiff ℝ ⊤ cEp)
    (hs : ∀ r ∈ s, r ≠ 0) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n
      (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r /
        (2 * Real.pi * r)) K₀) s := by
  have hgK : ∀ r : ℝ, ContDiff ℝ ⊤
      (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) := by
    intro r; unfold gForm; fun_prop
  have hrw : (fun r => iteratedDeriv n
        (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r /
          (2 * Real.pi * r)) K₀)
      = (fun r => iteratedDeriv n
          (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) K₀
            / (2 * Real.pi * r)) := by
    funext r
    have he : (fun K =>
          gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r / (2 * Real.pi * r))
        = (fun K => (1 / (2 * Real.pi * r)) *
            gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) := by
      funext K; ring
    rw [he, iteratedDeriv_const_mul _ ((hgK r).contDiffAt.of_le le_top)]; ring
  rw [hrw]
  refine ContDiffOn.div
    (gForm_paramDeriv_contDiffOn c0 c1 c2 c3 c4 cEm cEp z h0 h1 h2 h3 h4 hm hp n K₀)
    (by fun_prop) (fun r hr => mul_ne_zero (by positivity) (hs r hr))

end FMSA.MSAExact.BRK
