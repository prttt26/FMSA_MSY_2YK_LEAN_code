/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixBreakpoints

/-!
# MSAEMIX.4 Stage 3 — the piecewise unequal-σ exact-MSA mixture core (EXACT kernels)

The exact-MSA mixture direct-correlation core `c_ij(r)` on `(0, σ_ij)` (correct orientation
`σ_i ≥ σ_j`) is **2-piece** with the interior breakpoint `|λ_ij| = |σ_i−σ_j|/2` (MSAEMIX.5,
`MSAEMixBreakpoints.lean`).  With `g := 2π r c_ij` and `a := σ_i`, `b := σ_j`:
* OUTER `(|λ_ij| < r < σ_ij)`: `g = c0 + c1 r + c2 r² + c3 r³ + c4 r⁴ + cEm e^{-zr} + cEp e^{zr}`.
* INNER `(0 < r < |λ_ij|)`:  `g = c0 + c1 r + cEm e^{-zr} + cEp e^{zr}`  (`c2=c3=c4=0`).

Every coefficient is  `(-Q'_ij self-term) + Σ_l ρ_l · [Σ_bilinear KERNEL·bilinear]`, and every
per-`l` KERNEL is a **σ_l-INDEPENDENT** function of `(a,b,z)` only (species `l` enters ONLY via its
amplitudes `qp_il, A_l, Wt_il, Ct_il` and `ρ_l`).  The kernels are the EXACT closed forms from
the case-split-free symbolic-σ Baxter convolution (`symbolic_outer.py` / `symbolic_inner.py`),
each end-to-end validated against the numerical convolution to 1e-14 (`verify_{outer,inner}.py`).

Notes.  (1) On the physical (Blum–Høye root) amplitudes the per-`l` `c3` term and the inner constant
`c0` sum to `0` over `l` (on-root `g` is `{1,r,r²,r⁴,e^±}` outer / `{r,sinh(zr)}` inner); they are
kept here so the definition is exact for ANY amplitudes.  (2) `-Q'_ij` on both pieces (r in the poly
support `[λ_ij, σ_ij]`) contributes `(-qp_ij + A_j σ_ij)` to `c0`, `-A_j` to `c1`, and
`z Wt_ij e^{-zλ_ij} = z Wt_ij e^{-z(a-b)/2}` to `cEm`.  Amplitudes are plain `ℝ`-valued functions
(standalone, C++-translatable).  `σ_ij = edgeHi σ i j`, `|λ_ij| = |edgeLo σ i j| = lamA σ i j`.
-/

namespace MSAEMixCoreUneq

open MSAEMix
open scoped BigOperators

variable {N : ℕ}

-- the coefficient functions share a uniform signature for the uniform `matCoreUneq` calls, so a few
-- (z / Wt / Ct) args are unused in the poly-only coefficients (cC2o, cC3o, cC4o).
set_option linter.unusedVariables false

/-- Interior breakpoint `|λ_ij| = |σ_i − σ_j|/2`. -/
noncomputable def lamA (σ : Fin N → ℝ) (i j : Fin N) : ℝ := |edgeLo σ i j|

/-- The `g`-form in the shared 7-basis `{1, r, r², r³, r⁴, e^{-zr}, e^{+zr}}` (inner uses it with
`c2=c3=c4=0`). -/
noncomputable def gForm (c0 c1 c2 c3 c4 cEm cEp z r : ℝ) : ℝ :=
  c0 + c1 * r + c2 * r ^ 2 + c3 * r ^ 3 + c4 * r ^ 4
    + cEm * Real.exp (-z * r) + cEp * Real.exp (z * r)

/-! ### OUTER-piece coefficient functions (exact kernels, `a := σ i`, `b := σ j`) -/

/-- OUTER `c0`. -/
noncomputable def cC0o (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  (-qp i j + A j * ((a + b) / 2)) + ∑ l, ρ l * (
      (a ^ 2 / 8 - a * b / 4 - 3 * b ^ 2 / 8) * (qp i l * qp j l)
    + (a ^ 3 / 48 - a ^ 2 * b / 16 + a * b ^ 2 / 16 + 7 * b ^ 3 / 48) * (qp i l * A l)
    + (-a ^ 3 / 48 + a ^ 2 * b / 16 + 3 * a * b ^ 2 / 16 + 5 * b ^ 3 / 48) * (A l * qp j l)
    + (-a ^ 4 / 384 + a ^ 3 * b / 96 - a ^ 2 * b ^ 2 / 64 - 7 * a * b ^ 3 / 96 - 17 * b ^ 4 / 384)
        * (A l * A l)
    + ((z ^ 2 * (-a ^ 2 + 2 * a * b - b ^ 2) + 4 * z * (-a + b) - 8) / (8 * z ^ 2)) * (A l * Ct i l)
    + (-a ^ 2 / 8 - a * b / 4 - b ^ 2 / 8) * (A l * Ct j l)
    + ((-z * (a + b) + 2) / (2 * z ^ 2)) * (A l * Wt j l)
    + ((z * (-a + b) - 2) / (2 * z)) * (Ct i l * qp j l)
    + ((a + b) / 2) * (Ct j l * qp i l)
    + (1 / z) * (Wt j l * qp i l)
    + (-1) * (Ct i l * Ct j l))

/-- OUTER `c1` (`r`-coefficient). -/
noncomputable def cC1o (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  (-A j) + ∑ l, ρ l * (
      ((-a + b) / 2) * (qp i l * qp j l)
    + (-a ^ 2 / 8 + a * b / 4 - b ^ 2 / 8) * (qp i l * A l)
    + (a ^ 2 / 8 - a * b / 4 - 3 * b ^ 2 / 8) * (A l * qp j l)
    + (a ^ 3 / 48 - a ^ 2 * b / 16 + a * b ^ 2 / 16 + 7 * b ^ 3 / 48) * (A l * A l)
    + ((z * (a - b) + 2) / (2 * z)) * (A l * Ct i l)
    + ((a + b) / 2) * (A l * Ct j l)
    + (1 / z) * (A l * Wt j l)
    + (1 : ℝ) * (Ct i l * qp j l)
    + (-1) * (Ct j l * qp i l))

/-- OUTER `c2` (`r²`-coefficient). -/
noncomputable def cC2o (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  ∑ l, ρ l * (
      (1 / 2) * (qp i l * qp j l)
    + ((a - b) / 4) * (qp i l * A l)
    + ((-a + b) / 4) * (A l * qp j l)
    + (-a ^ 2 / 16 + a * b / 8 - b ^ 2 / 16) * (A l * A l)
    + (-1 / 2) * (A l * Ct i l)
    + (-1 / 2) * (A l * Ct j l))

/-- OUTER `c3` (`r³`-coefficient; sums to 0 over `l` on the physical root). -/
noncomputable def cC3o (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  ∑ l, ρ l * (
      ((a - b) / 12) * (A l * A l)
    + (-1 / 6) * (qp i l * A l)
    + (1 / 6) * (A l * qp j l))

/-- OUTER `c4` (`r⁴`-coefficient). -/
noncomputable def cC4o (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  ∑ l, ρ l * ((-1 / 24) * (A l * A l))

/-- OUTER `e^{-zr}`-coefficient. -/
noncomputable def cEmo (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  z * Wt i j * Real.exp (-z * (a - b) / 2) + ∑ l, ρ l * (
      (Real.exp (z * (a - b) / 2) / z ^ 2) * (A l * Ct i l)
    + ((-b ^ 2 * z ^ 2 * Real.exp (b * z) / 2 + b * z * Real.exp (b * z) - Real.exp (b * z) + 1)
        * Real.exp (-z * (a + b) / 2) / z ^ 2) * (A l * Wt i l)
    + (Real.exp (z * (a - b) / 2) / z) * (Ct i l * qp j l)
    + ((b * z * Real.exp (b * z) - Real.exp (b * z) + 1) * Real.exp (-z * (a + b) / 2) / z)
        * (Wt i l * qp j l)
    + ((1 / 2 - Real.exp (b * z)) * Real.exp (-z * (a + b) / 2)) * (Ct j l * Wt i l)
    + (-Real.exp (-z * (a - b) / 2) / 2) * (Wt i l * Wt j l)
    + (Real.exp (z * (a - b) / 2) / 2) * (Ct i l * Ct j l))

/-- OUTER `e^{+zr}`-coefficient. -/
noncomputable def cEpo (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  ∑ l, ρ l * (
      (-Real.exp (-z * (a + b) / 2) / z ^ 2) * (A l * Wt j l)
    + (-Real.exp (-z * (a + b) / 2) / z) * (Wt j l * qp i l)
    + (-Real.exp (-z * (a + b) / 2) / 2) * (Ct i l * Wt j l))

/-! ### INNER-piece coefficient functions (exact kernels; `c2 = c3 = c4 = 0`) -/

/-- INNER `c0`. -/
noncomputable def cC0i (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  (-qp i j + A j * ((a + b) / 2)) + ∑ l, ρ l * (
      (-b ^ 2 / 2) * (qp i l * qp j l)
    + (b ^ 3 / 6) * (qp i l * A l)
    + (b ^ 2 * (3 * a + b) / 12) * (A l * qp j l)
    + (-b ^ 3 * (2 * a + b) / 24) * (A l * A l)
    + ((-a * b * z ^ 2 + z * (-a + b) + 2) / (2 * z ^ 2)) * (A l * Ct j l)
    + ((-z * (a + b) + 2) / (2 * z ^ 2)) * (A l * Wt j l)
    + (b + 1 / z) * (Ct j l * qp i l)
    + (1 / z) * (Wt j l * qp i l))

/-- INNER `c1` (`r`-coefficient). -/
noncomputable def cC1i (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  (-A j) + ∑ l, ρ l * (
      (-b ^ 2 / 2) * (A l * qp j l)
    + (b ^ 3 / 6) * (A l * A l)
    + (b + 1 / z) * (A l * Ct j l)
    + (1 / z) * (A l * Wt j l))

/-- INNER `e^{-zr}`-coefficient (its `Wt_il`/`Ct_jl` kernels coincide with OUTER's). -/
noncomputable def cEmi (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  z * Wt i j * Real.exp (-z * (a - b) / 2) + ∑ l, ρ l * (
      ((-b ^ 2 * z ^ 2 * Real.exp (b * z) / 2 + b * z * Real.exp (b * z) - Real.exp (b * z) + 1)
        * Real.exp (-z * (a + b) / 2) / z ^ 2) * (A l * Wt i l)
    + ((b * z * Real.exp (b * z) - Real.exp (b * z) + 1) * Real.exp (-z * (a + b) / 2) / z)
        * (Wt i l * qp j l)
    + ((1 / 2 - Real.exp (b * z)) * Real.exp (-z * (a + b) / 2)) * (Ct j l * Wt i l)
    + (-Real.exp (-z * (a - b) / 2) / 2) * (Wt i l * Wt j l))

/-- INNER `e^{+zr}`-coefficient. -/
noncomputable def cEpi (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  let a := σ i; let b := σ j
  ∑ l, ρ l * (
      (-Real.exp (-z * (a - b) / 2) / z ^ 2) * (A l * Ct j l)
    + (-Real.exp (-z * (a + b) / 2) / z ^ 2) * (A l * Wt j l)
    + (-Real.exp (-z * (a - b) / 2) / z) * (Ct j l * qp i l)
    + (-Real.exp (-z * (a + b) / 2) / z) * (Wt j l * qp i l)
    + (-Real.exp (-z * (a + b) / 2) / 2) * (Ct i l * Wt j l)
    + (-Real.exp (-z * (a - b) / 2) / 2) * (Ct i l * Ct j l))

/-- ⭐ The assembled unequal-σ exact-MSA core `c_ij(r) = g/(2π r)` (orientation `σ_i ≥ σ_j`), 2-piece
at `|λ_ij|`, with the EXACT σ_l-free kernels of both pieces. -/
noncomputable def matCoreUneq (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  (if r ≤ lamA σ i j then
      gForm (cC0i z ρ σ A qp Wt Ct i j) (cC1i z ρ σ A qp Wt Ct i j) 0 0 0
        (cEmi z ρ σ A qp Wt Ct i j) (cEpi z ρ σ A qp Wt Ct i j) z r
    else
      gForm (cC0o z ρ σ A qp Wt Ct i j) (cC1o z ρ σ A qp Wt Ct i j) (cC2o z ρ σ A qp Wt Ct i j)
        (cC3o z ρ σ A qp Wt Ct i j) (cC4o z ρ σ A qp Wt Ct i j) (cEmo z ρ σ A qp Wt Ct i j)
        (cEpo z ρ σ A qp Wt Ct i j) z r) / (2 * Real.pi * r)

end MSAEMixCoreUneq
