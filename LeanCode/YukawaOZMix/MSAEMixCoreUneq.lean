/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixBreakpoints

/-!
# MSAEMIX.4 Stage 3 — the piecewise unequal-σ exact-MSA mixture core (structure + confirmed kernels)

The exact-MSA mixture direct correlation core `c_ij(r)` on `(0, σ_ij)` (correct orientation
`σ_i ≥ σ_j`) is **2-piece** with the interior breakpoint `|λ_ij| = |σ_i−σ_j|/2` (MSAEMIX.5,
`MSAEMixBreakpoints.lean`).  With `g := 2π r c_ij`:
* INNER `(0 < r < |λ_ij|)`:  `g = a r + b sinh(z r)`               (basis `{r, sinh(zr)}`)
* OUTER `(|λ_ij| < r < σ_ij)`: `g = c0 + c1 r + c2 r² + c4 r⁴ + cEm e^{-zr} + cEp e^{zr}`.

Each coefficient is  `(-Q'_ij self-term)  +  Σ_l ρ_l · [Σ_bilinear KERNEL·bilinear]`, and every
per-`l` KERNEL is **σ_l-INDEPENDENT** — a function of `(σ_i, σ_j, z)` only (verified N=3;
`msaemix_uneq_kernels.py`), so the intermediate species enters ONLY via its amplitudes
(`qp_il, A_l, Wt_il, Ct_il`) and `ρ_l`.

This file lands the **structure** with the CONFIRMED closed-form kernels wired in (12-state greedy
fit + held-out validation, `msaemix_uneq_kernels.py`).  The kernels still pending the symbolic-σ
derivation (the OUTER cross `qp_il·A_l`/`A_l²` terms, the OUTER `e^{-zr}` Yukawa terms, and BOTH
inner coefficients — all wall the empirical fit at ~1e-3 and blow up as `λ→0`) are isolated in
clearly-named `*_TODO` placeholder defs (`:= 0`), so the file builds cleanly and the missing pieces
are explicit.  Amplitudes are passed as plain `ℝ`-valued functions (standalone, C++-translatable).

`σ_ij = edgeHi σ i j`, `|λ_ij| = |edgeLo σ i j| = lamA σ i j`.
-/

namespace MSAEMixCoreUneq

open MSAEMix
open scoped BigOperators

variable {N : ℕ}

-- structure-landing skeleton: `*_TODO` stubs and the uniform coefficient signatures leave some
-- amplitude args unused until Stage 3c fills the pending kernels.
set_option linter.unusedVariables false

/-- Interior breakpoint `|λ_ij| = |σ_i − σ_j|/2`. -/
noncomputable def lamA (σ : Fin N → ℝ) (i j : Fin N) : ℝ := |edgeLo σ i j|

/-! ### Piecewise assembly (the structure) -/

/-- OUTER-piece `g` in the shared 6-basis `{1, r, r², r⁴, e^{-zr}, e^{+zr}}`. -/
noncomputable def gOuter (c0 c1 c2 c4 cEm cEp z r : ℝ) : ℝ :=
  c0 + c1 * r + c2 * r ^ 2 + c4 * r ^ 4 + cEm * Real.exp (-z * r) + cEp * Real.exp (z * r)

/-- INNER-piece `g = a r + b sinh(z r)` (vanishes at `r=0`, so `c = g/(2πr)` is finite). -/
noncomputable def gInner (a b z r : ℝ) : ℝ := a * r + b * Real.sinh (z * r)

/-- The piecewise exact-MSA core `c_ij(r) = g/(2π r)` with breakpoint `lam = |λ_ij|`. -/
noncomputable def coreUneq (a b c0 c1 c2 c4 cEm cEp lam z r : ℝ) : ℝ :=
  (if r ≤ lam then gInner a b z r else gOuter c0 c1 c2 c4 cEm cEp z r) / (2 * Real.pi * r)

/-! ### `*_TODO` placeholders — kernels pending the symbolic-σ derivation (Stage 3c) -/

/-- TODO(Stage 3c, symbolic-σ): OUTER `c0` cross terms `qp_il·A_l`, `A_l·qp_jl`, `A_l²`. -/
noncomputable def crossC0_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0
/-- TODO(Stage 3c): OUTER `c1` cross terms `qp_il·A_l`, `A_l·qp_jl`, `A_l²`. -/
noncomputable def crossC1_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0
/-- TODO(Stage 3c): OUTER `c2` cross terms `qp_il·A_l`, `A_l·qp_jl`, `A_l²`. -/
noncomputable def crossC2_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0
/-- TODO(Stage 3c): OUTER `r⁴` coefficient `c4` (bilinears `qp_il·A_l`, `A_l·qp_jl`, `A_l²`). -/
noncomputable def c4_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0
/-- TODO(Stage 3c): OUTER `e^{-zr}` coefficient — Yukawa kernels (`A_l·Ct_il`, `A_l·Wt_il`,
`Ct_il·qp_jl`, cross `qp_il·A_l`, `A_l²`); carry `e^{-zλ}`/`e^{-zσ_ij}` factors. -/
noncomputable def eMinus_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0
/-- TODO(Stage 3c): OUTER `e^{+zr}` coefficient — remaining Yukawa kernels beyond the confirmed
`A_l·Wt_jl → −e^{-zσ_ij}/z²`. -/
noncomputable def ePlus_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0
/-- TODO(Stage 3c): INNER `r`-coefficient `a` (per-`l`); blows up as `λ→0` (not `1/sinh(zλ)`). -/
noncomputable def aInner_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0
/-- TODO(Stage 3c): INNER `sinh(z r)`-coefficient `b` (per-`l`); blows up as `λ→0`. -/
noncomputable def bInner_TODO (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j l : Fin N) : ℝ := 0

/-! ### OUTER coefficient functions (CONFIRMED kernels wired in) -/

/-- OUTER `c0`.  Self `-Q'_ij`: `-qp_ij + A_j·σ_ij`.  Confirmed kernels: `qp_il·qp_jl → -σ²/2+σλ`,
`A_l·Ct_jl → -σ²/2`, `Ct_jl·qp_il → σ`, `Ct_il·qp_jl → -λ-1/z`, `A_l·Ct_il → -λ/z-λ²/2-1/z²`,
`A_l·Wt_jl → -σ/z+1/z²`.  (`+ crossC0_TODO`.) -/
noncomputable def cC0 (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let s := edgeHi σ i j; let lam := lamA σ i j
  (-qp i j + A j * s) + ∑ l, ρ l * (
      (-s ^ 2 / 2 + s * lam) * (qp i l * qp j l)
    + (-s ^ 2 / 2) * (A l * Ct j l)
    + s * (Ct j l * qp i l)
    + (-lam - 1 / z) * (Ct i l * qp j l)
    + (-lam / z - lam ^ 2 / 2 - 1 / z ^ 2) * (A l * Ct i l)
    + (-s / z + 1 / z ^ 2) * (A l * Wt j l)
    + crossC0_TODO z σ A qp i j l)

/-- OUTER `c1` (`r`-coefficient).  Self `-Q'_ij`: `-A_j`.  Confirmed: `qp_il·qp_jl → -λ`,
`A_l·Ct_jl → σ`, `A_l·Ct_il → λ+1/z`, `A_l·Wt_jl → 1/z`, `Ct_il·qp_jl → 1`, `Ct_jl·qp_il → -1`. -/
noncomputable def cC1 (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let s := edgeHi σ i j; let lam := lamA σ i j
  (-A j) + ∑ l, ρ l * (
      (-lam) * (qp i l * qp j l)
    + s * (A l * Ct j l)
    + (lam + 1 / z) * (A l * Ct i l)
    + (1 / z) * (A l * Wt j l)
    + (Ct i l * qp j l)
    - (Ct j l * qp i l)
    + crossC1_TODO z σ A qp i j l)

/-- OUTER `c2` (`r²`-coefficient).  Confirmed: `qp_il·qp_jl → 1/2`, `A_l·Ct_il → -1/2`,
`A_l·Ct_jl → -1/2`. -/
noncomputable def cC2 (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  ∑ l, ρ l * (
      (1 / 2) * (qp i l * qp j l)
    + (-1 / 2) * (A l * Ct i l)
    + (-1 / 2) * (A l * Ct j l)
    + crossC2_TODO z σ A qp i j l)

/-- OUTER `c4` (`r⁴`-coefficient).  All kernels pending (Stage 3c). -/
noncomputable def cC4 (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  ∑ l, ρ l * c4_TODO z σ A qp i j l

/-- OUTER `e^{-zr}`-coefficient.  Self `-Q'_ij`: `+z·Wt_ij·e^{-zλ}`.  Bilinear kernels pending. -/
noncomputable def cEm (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let lam := lamA σ i j
  z * Wt i j * Real.exp (-z * lam) + ∑ l, ρ l * eMinus_TODO z σ A qp Wt Ct i j l

/-- OUTER `e^{+zr}`-coefficient.  Confirmed: `A_l·Wt_jl → −e^{-zσ_ij}/z²`.  (`+ ePlus_TODO`.) -/
noncomputable def cEp (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let s := edgeHi σ i j
  ∑ l, ρ l * ((-Real.exp (-z * s) / z ^ 2) * (A l * Wt j l) + ePlus_TODO z σ A qp Wt Ct i j l)

/-! ### INNER coefficient functions (pending Stage 3c) -/

/-- INNER `r`-coefficient `a`. All kernels pending (blow up as `λ→0`). -/
noncomputable def aI (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  ∑ l, ρ l * aInner_TODO z σ A qp Wt Ct i j l

/-- INNER `sinh(z r)`-coefficient `b`. All kernels pending. -/
noncomputable def bI (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  ∑ l, ρ l * bInner_TODO z σ A qp Wt Ct i j l

/-- The assembled unequal-σ exact-MSA core `c_ij(r)` (correct orientation `σ_i ≥ σ_j`), plugging the
coefficient functions into the piecewise `coreUneq`.  Confirmed kernels are exact; `*_TODO` terms
are `0` pending the symbolic-σ derivation. -/
noncomputable def matCoreUneq (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  coreUneq (aI z ρ σ A qp Wt Ct i j) (bI z ρ σ A qp Wt Ct i j)
    (cC0 z ρ σ A qp Wt Ct i j) (cC1 z ρ σ A qp Wt Ct i j) (cC2 z ρ σ A qp Wt Ct i j)
    (cC4 z ρ σ A qp Wt Ct i j) (cEm z ρ σ A qp Wt Ct i j) (cEp z ρ σ A qp Wt Ct i j)
    (lamA σ i j) z r

end MSAEMixCoreUneq
