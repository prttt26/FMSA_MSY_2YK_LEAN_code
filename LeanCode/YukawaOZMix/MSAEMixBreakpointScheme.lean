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
the geometric breakpoint `|λ_ij|`, with

* INNER `g = a·r + b·sinh(zr)`  (basis `{r, sinh(zr)}`),
* OUTER `g = c0 + c1 r + c2 r² + c4 r⁴ + cEm e^{−zr} + cEp e^{zr}`  (basis `{1,r,r²,r⁴,e^{∓zr}}`),

and `K` enters only through the coefficients (`a,b,c0,…,cEp`), never the two fixed bases.  Feeding
those bases into the abstract lemma closes BRK.9 concrete: **every `K`-derivative of each core piece
is, in `r`, `ContDiffOn` on that piece** — so no order introduces an interior knot beyond `|λ_ij|`.

The only remaining input is that the amplitudes are themselves `ContDiff` in `K` (the coefficients
`ContDiff ℝ ⊤`), which the BH root supplies (polynomial/analytic in the coupling); it is carried
here as an explicit hypothesis, not baked in.
-/

open MSAEMixCoreUneq

namespace FMSA.MSAExact.BRK

/-- ⭐ **BRK.9 concrete — OUTER piece.**  With `K` entering only the coefficients `c0..cEp`
(`ContDiff ℝ ⊤`), every `K`-derivative of the OUTER core `gOuter` is, as a function of `r`,
`ContDiffOn ℝ ⊤` on any set — the fixed basis `{1, r, r², r⁴, e^{−zr}, e^{zr}}` carries no `K`, so
no order can create a knot inside the outer piece `(|λ_ij|, σ_ij)`. -/
theorem gOuter_paramDeriv_contDiffOn (c0 c1 c2 c4 cEm cEp : ℝ → ℝ) (z : ℝ) {s : Set ℝ}
    (h0 : ContDiff ℝ ⊤ c0) (h1 : ContDiff ℝ ⊤ c1) (h2 : ContDiff ℝ ⊤ c2)
    (h4 : ContDiff ℝ ⊤ c4) (hm : ContDiff ℝ ⊤ cEm) (hp : ContDiff ℝ ⊤ cEp) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n
      (fun K => gOuter (c0 K) (c1 K) (c2 K) (c4 K) (cEm K) (cEp K) z r) K₀) s := by
  have hfun : (fun r => iteratedDeriv n
        (fun K => gOuter (c0 K) (c1 K) (c2 K) (c4 K) (cEm K) (cEp K) z r) K₀)
      = (fun r => iteratedDeriv n
          (fun K => ∑ k, (![c0, c1, c2, c4, cEm, cEp] : Fin 6 → ℝ → ℝ) k K *
            (![fun _ => 1, fun r => r, fun r => r ^ 2, fun r => r ^ 4,
              fun r => Real.exp (-z * r), fun r => Real.exp (z * r)] : Fin 6 → ℝ → ℝ) k r) K₀) := by
    funext r; congr 1; funext K
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, gOuter]
    ring
  rw [hfun]
  refine contDiffOn_paramDeriv_coeffBasis Finset.univ _ _ ?_ ?_ n K₀
  · intro k _
    fin_cases k <;> first | exact h0 | exact h1 | exact h2 | exact h4 | exact hm | exact hp
  · intro k _; fin_cases k
    · show ContDiffOn ℝ ⊤ (fun _ => (1 : ℝ)) s; fun_prop
    · show ContDiffOn ℝ ⊤ (fun r => r) s; fun_prop
    · show ContDiffOn ℝ ⊤ (fun r => r ^ 2) s; fun_prop
    · show ContDiffOn ℝ ⊤ (fun r => r ^ 4) s; fun_prop
    · show ContDiffOn ℝ ⊤ (fun r => Real.exp (-z * r)) s; fun_prop
    · show ContDiffOn ℝ ⊤ (fun r => Real.exp (z * r)) s; fun_prop

/-- ⭐ **BRK.9 concrete — INNER piece.**  With `K` entering only the coefficients `a, b`, every
`K`-derivative of the INNER core `gInner = a·r + b·sinh(zr)` is, in `r`, `ContDiffOn ℝ ⊤` — the
fixed basis `{r, sinh(zr)}` carries no `K`, so no order can create a knot inside `(0, |λ_ij|)`. -/
theorem gInner_paramDeriv_contDiffOn (a b : ℝ → ℝ) (z : ℝ) {s : Set ℝ}
    (ha : ContDiff ℝ ⊤ a) (hb : ContDiff ℝ ⊤ b) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n (fun K => gInner (a K) (b K) z r) K₀) s := by
  have hfun : (fun r => iteratedDeriv n (fun K => gInner (a K) (b K) z r) K₀)
      = (fun r => iteratedDeriv n
          (fun K => ∑ k, (![a, b] : Fin 2 → ℝ → ℝ) k K *
            (![fun r => r, fun r => Real.sinh (z * r)] : Fin 2 → ℝ → ℝ) k r) K₀) := by
    funext r; congr 1; funext K
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, gInner]
  rw [hfun]
  refine contDiffOn_paramDeriv_coeffBasis Finset.univ _ _ ?_ ?_ n K₀
  · intro k _; fin_cases k
    · exact ha
    · exact hb
  · intro k _; fin_cases k
    · show ContDiffOn ℝ ⊤ (fun r => r) s; fun_prop
    · show ContDiffOn ℝ ⊤ (fun r => Real.sinh (z * r)) s; fun_prop

end FMSA.MSAExact.BRK
