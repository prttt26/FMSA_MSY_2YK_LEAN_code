/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.I1I2Integrals
import LeanCode.YukawaDCF.B5MixturePoly

/-!
# Tasks IB.1–IB.5 — Inner DCF Decomposition: Mediated Vanishing and Term IV Breakpoints

## Context

`B5MixturePoly.lean` establishes that `P_ij` has degree ≤ 4 (B.5) and provides the B.8
Laplace-moment inversion.  This file addresses the complementary *structural* question:
when does the cross-species **mediated** correction vanish in the inner region, where are
its breakpoints, and is the residue `P_ij` a single polynomial on all of `(0, R_ij)`?

For an unlike pair `(i, j)` the first-order inner DCF decomposes as

  c^(1)_ij(r) = [Term_I(r) + P_ij(r)] / (2π√(ρᵢρⱼ)·r) + c^HS_ij(r) + mediated_ij(r)

with `mediated = (II + III + IV) / (2π√(ρᵢρⱼ)·r)` — Terms II, III, IV of `_compute_mediated`
in `fmsa_ga_matrix_mix.py`.

## Faithfulness to the Python

Unlike the previous version of this file — whose theorems quantified over *unconstrained*
`mediated : ℝ → Fin N → Fin N → ℝ` and took the physical content as hypotheses (so they
asserted nothing) — every definition below mirrors `_compute_mediated`
(`fmsa_ga_matrix_mix.py:705-857`) line by line:

| Lean                | Python                                    |
|---------------------|-------------------------------------------|
| `Mix.lam k l`       | `lambda_ij[k,l] = (σ[l] − σ[k])/2` (:162) |
| `Mix.alphaII`       | `alpha = l + lambda_ij[i,a] − sigma[a]` (:744) |
| `lstar`             | `lstar = max(0, min(l, alpha))` (:745)    |
| `I1cl`, `I2cl`      | the `I1`, `I2` closed forms (:751-761)    |
| `Mix.DeltaAi`       | `Delta_ai = lambda_ij[i,a] − sigma[a]` (:800) |
| `Mix.cexp`,`Mix.dexp` | `c_exp`, `d_exp` (:802-803)             |
| `Mix.uLo`,`Mix.uHiEff`| `u_lo_bj`, `u_hi_eff` (:805-808)        |
| `Mix.termIVsub`     | the `(a,b)` body, incl. the `continue` guard (:809) |

`I1cl`/`I2cl` are stated *verbatim* as the right-hand sides of `FMSA.DCF.I1_formula` /
`I2_formula` (Tasks 1.1/1.2), so `I1cl_eq_integral` below is those theorems unchanged and
`I1cl_at_zero`/`I2cl_at_zero` are the closed-form face of Task 1.3.

## Results (all numerically verified, `verify_mediated_breakpoints.py`)

Sign convention: `lambda_ij[k,l] = (σ[l] − σ[k])/2`.  An earlier "factor-of-3 threshold"
analysis used the opposite convention and was **wrong**; see the CORRECTION note in
`numerical_notes/theory/mediated_breakpoints.md`.

**Terms II and III vanish unconditionally** (IB.1).  The activation variable collapses to
`alpha = r − σ[a] − R[i,j]`, which is `< 0` throughout the inner region since `r < R[i,j]`
and `σ[a] > 0`.  Hence `lstar = 0` and `I1 = I2 = 0`.  This also shows the guard
`if r < R[a,j]: continue` is **redundant**: when `r < R[a,j]` we have `l < 0`, and `alpha < 0`
holds regardless, so `lstar = 0` on both branches.

**Term IV geometry** (IB.2).  The identity that drives everything:

  `Δ_ai = lam[i,a] − σ[a] = (σₐ−σᵢ)/2 − σₐ = −(σᵢ+σₐ)/2 = −R[i,a]  < 0`

so `Alm = max(Δ_ai, 0) = 0` and `c_exp = d_exp = R[a,b] + R[i,a] =: r*`.  This **derives**
the breakpoint `r*` rather than positing it.  Since `u_hi_eff ≤ r` and `u_lo_eff ≥ c_exp = r*`,
the integration window is empty for every `r ≤ r*` — so the sub-term vanishes below `r*`
*unconditionally*, with no appeal to conditions A/B.

**Activation** (IB.3).  Conditions A/B are exactly the two ways the window can be nonempty
somewhere in the inner region:

  (A) `2σₐ + σ_b < σⱼ`  ⟺  `r* < R[i,j]`      (breakpoint lies inside the inner region)
  (B) `σⱼ < 3σ_b`       ⟺  `u_lo_bj < r`       (window nonempty above `r*`)

If either fails, sub-term `(a,b)` is identically zero on `(0, R_ij)`.  Together A ∧ B force
the strict size chain `σₐ < σ_b < σⱼ` (`active_pair_size_chain`, proved below), which needs
three distinct diameters — impossible for `N = 2`.  Hence **binary mixtures have mediated ≡ 0
for every pair at any σ-ratio**.

**Not formalized (numerical only):** that mediated is *strictly positive* just above `r*`.
That depends on the signs of the `b_grow` poles/coefficients from the converged Q-matrix and
does not follow from `σ > 0`.  Confirmed numerically for σ=[1,4,8] at `r* = 3.3859 / 4.8370 /
6.7717`; recorded in todo_lean.md's "Numerically verified" table.

## Status

| Task | Description | Status |
|------|-------------|--------|
| IB.1 | Terms II+III ≡ 0 in the inner region (unconditional) | ✓ proved |
| IB.2 | Term IV geometry: `Δ_ai = −R[i,a]`, `c_exp = d_exp = r*`; sub-term ≡ 0 below `r*` | done |
| IB.3 | mediated ≡ 0 when no `(a,b)` satisfies A∧B; binary corollary | ✓ proved ×2 |
| IB.4 | Residue is a *single* degree-≤4 polynomial on `(0,R_ij)` after subtraction | ✓ proved |
| IB.5 | Witness: σ=[1,4,8], `(a,b,j)=(0,1,2)` satisfies A∧B — sharpness | ✓ proved |
-/

set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedVariables false

open Real Set Finset

namespace FMSA.InnerDecomp

/-!
## The `I1` / `I2` closed forms and the `lstar` clamp

These are the scalar ingredients shared by Terms II and III.
-/

/-- Closed form of `I1(ell, alpha, z) = ∫₀^ell (alpha − v)·exp(z·v) dv`
(`_compute_mediated` lines 751-755).  Stated verbatim as the RHS of `FMSA.DCF.I1_formula`. -/
noncomputable def I1cl (z alpha ell : ℝ) : ℝ :=
    (alpha - ell) * Real.exp (z * ell) / z + (Real.exp (z * ell) - 1) / z ^ 2 - alpha / z

/-- Closed form of `I2(ell, alpha, z) = ∫₀^ell (alpha − v)²·exp(z·v) dv`
(`_compute_mediated` lines 756-761).  Stated verbatim as the RHS of `FMSA.DCF.I2_formula`. -/
noncomputable def I2cl (z alpha ell : ℝ) : ℝ :=
    (alpha - ell) ^ 2 * Real.exp (z * ell) / z + 2 * (alpha - ell) * Real.exp (z * ell) / z ^ 2
      + 2 * Real.exp (z * ell) / z ^ 3 - alpha ^ 2 / z - 2 * alpha / z ^ 2 - 2 / z ^ 3

/-- **Task 1.1 reuse.**  `I1cl` really is the integral it claims to be. -/
theorem I1cl_eq_integral {z alpha ell : ℝ} (hz : z ≠ 0) :
    ∫ v in (0 : ℝ)..ell, (alpha - v) * Real.exp (z * v) = I1cl z alpha ell :=
  FMSA.DCF.I1_formula hz

/-- **Task 1.2 reuse.**  `I2cl` really is the integral it claims to be. -/
theorem I2cl_eq_integral {z alpha ell : ℝ} (hz : z ≠ 0) :
    ∫ v in (0 : ℝ)..ell, (alpha - v) ^ 2 * Real.exp (z * v) = I2cl z alpha ell :=
  FMSA.DCF.I2_formula hz

/-- **Task 1.3, closed-form face.**  `I1` vanishes at `ell = 0` (empty integration range). -/
@[simp] theorem I1cl_at_zero (z alpha : ℝ) : I1cl z alpha 0 = 0 := by
  simp [I1cl]

/-- **Task 1.3, closed-form face.**  `I2` vanishes at `ell = 0` (empty integration range). -/
@[simp] theorem I2cl_at_zero (z alpha : ℝ) : I2cl z alpha 0 = 0 := by
  simp [I2cl]
  ring

/-- The `lstar = max(0, min(l, alpha))` clamp (`_compute_mediated` line 745). -/
noncomputable def lstar (l alpha : ℝ) : ℝ := max 0 (min l alpha)

/-- A negative activation variable clamps `lstar` to zero — regardless of `l`.  This is why
the `if r < R[a,j]: continue` guard in the Python is redundant. -/
theorem lstar_eq_zero_of_alpha_neg {l alpha : ℝ} (h : alpha < 0) : lstar l alpha = 0 :=
  max_eq_left (le_of_lt (lt_of_le_of_lt (min_le_right l alpha) h))

/-!
## Mixture data

Everything `_compute_mediated` reads off the converged FMSA solution: `M` is the number of
Yukawa poles carried by each `b_grow[a][b]` residue expansion.
-/

/-- The converged-solution data consumed by `_compute_mediated`. -/
structure Mix (N M : ℕ) where
  /-- BH-corrected hard-sphere diameters. -/
  σ   : Fin N → ℝ
  /-- Number densities. -/
  ρ   : Fin N → ℝ
  /-- `b_grow[a][b].poles`. -/
  zp  : Fin N → Fin N → Fin M → ℝ
  /-- `b_grow[a][b].coeffs`. -/
  cb  : Fin N → Fin N → Fin M → ℝ
  /-- Baxter `Q₀` matrix. -/
  Q0  : Fin N → Fin N → ℝ
  /-- Baxter `Q''` diagonal. -/
  Qpp : Fin N → ℝ
  /-- Diameters are strictly positive.  This is the *only* physical input the vanishing
  theorems IB.1–IB.3 need. -/
  hσ  : ∀ k, 0 < σ k

namespace Mix

variable {N M : ℕ} (X : Mix N M)

/-- Contact distance `R[i,j] = (σᵢ + σⱼ)/2`. -/
noncomputable def R (i j : Fin N) : ℝ := (X.σ i + X.σ j) / 2

/-- Size-asymmetry parameter `lambda_ij[k,l] = (σ[l] − σ[k])/2` (`fmsa_ga_matrix_mix.py:162`).
Note the order: **second index minus first**. -/
noncomputable def lam (k l : Fin N) : ℝ := (X.σ l - X.σ k) / 2

/-- Size-asymmetry lower cutoff `σ_min(i,j) = min(σᵢ, σⱼ)`. -/
noncomputable def σmin (i j : Fin N) : ℝ := min (X.σ i) (X.σ j)

theorem R_pos (i j : Fin N) : 0 < X.R i j := by
  have hi := X.hσ i
  have hj := X.hσ j
  unfold R
  linarith

/-!
### Terms II and III
-/

/-- `l = r − R[a,j]` for Term II (`_compute_mediated` line 743). -/
noncomputable def ellII (r : ℝ) (a j : Fin N) : ℝ := r - X.R a j

/-- `alpha = l + lambda_ij[i,a] − sigma[a]` for Term II (`_compute_mediated` line 744). -/
noncomputable def alphaII (r : ℝ) (i j a : Fin N) : ℝ :=
    X.ellII r a j + X.lam i a - X.σ a

/-- `l = r − R[i,b]` for Term III (`_compute_mediated` line 771). -/
noncomputable def ellIII (r : ℝ) (i b : Fin N) : ℝ := r - X.R i b

/-- `alpha = l + lambda_ij[j,b] − sigma[b]` for Term III (`_compute_mediated` line 772). -/
noncomputable def alphaIII (r : ℝ) (i j b : Fin N) : ℝ :=
    X.ellIII r i b + X.lam j b - X.σ b

/-- **The sign-convention identity.**  Term II's activation variable collapses to
`alpha = r − σ[a] − R[i,j]`.  Everything in IB.1 follows from this. -/
theorem alphaII_eq (r : ℝ) (i j a : Fin N) :
    X.alphaII r i j a = r - X.σ a - X.R i j := by
  unfold alphaII ellII lam R
  ring

/-- Term III's activation variable collapses to `alpha = r − σ[b] − R[i,j]`. -/
theorem alphaIII_eq (r : ℝ) (i j b : Fin N) :
    X.alphaIII r i j b = r - X.σ b - X.R i j := by
  unfold alphaIII ellIII lam R
  ring

/-- Term II: `Σ_a √(ρₐρᵢ) · Σ_k Rst_k · [Q₀[a,i]·I1 + ½·Q''[i]·I2]`
(`_compute_mediated` lines 737-763).  The Python's `continue` guards are omitted because
`lstar_eq_zero_of_alpha_neg` shows both branches agree in the inner region. -/
noncomputable def termII (r : ℝ) (i j : Fin N) : ℝ :=
    ∑ a : Fin N, Real.sqrt (X.ρ a * X.ρ i) *
      ∑ k : Fin M, X.cb a j k *
        (X.Q0 a i * I1cl (X.zp a j k) (X.alphaII r i j a)
            (lstar (X.ellII r a j) (X.alphaII r i j a))
          + (1 / 2) * X.Qpp i * I2cl (X.zp a j k) (X.alphaII r i j a)
            (lstar (X.ellII r a j) (X.alphaII r i j a)))

/-- Term III: `Σ_b √(ρ_bρⱼ) · Σ_k Rst_k · [Q₀[b,j]·I1 + ½·Q''[j]·I2]`
(`_compute_mediated` lines 765-791). -/
noncomputable def termIII (r : ℝ) (i j : Fin N) : ℝ :=
    ∑ b : Fin N, Real.sqrt (X.ρ b * X.ρ j) *
      ∑ k : Fin M, X.cb i b k *
        (X.Q0 b j * I1cl (X.zp i b k) (X.alphaIII r i j b)
            (lstar (X.ellIII r i b) (X.alphaIII r i j b))
          + (1 / 2) * X.Qpp j * I2cl (X.zp i b k) (X.alphaIII r i j b)
            (lstar (X.ellIII r i b) (X.alphaIII r i j b)))

/-!
### Term IV
-/

/-- `Delta_ai = lambda_ij[i,a] − sigma[a]` (`_compute_mediated` line 800). -/
noncomputable def DeltaAi (i a : Fin N) : ℝ := X.lam i a - X.σ a

/-- `c_exp = R[a,b] + max(0, −Delta_ai)` — where `lstar` first turns positive (line 802). -/
noncomputable def cexp (i a b : Fin N) : ℝ := X.R a b + max 0 (-(X.DeltaAi i a))

/-- `d_exp = R[a,b] − Delta_ai` (line 803). -/
noncomputable def dexp (i a b : Fin N) : ℝ := X.R a b - X.DeltaAi i a

/-- `u_lo_bj = r + lambda_ij[b,j] − sigma[b]` (line 805). -/
noncomputable def uLo (r : ℝ) (j b : Fin N) : ℝ := r + X.lam b j - X.σ b

/-- `u_hi_bj = r + lambda_ij[b,j]` (line 806). -/
noncomputable def uHi (r : ℝ) (j b : Fin N) : ℝ := r + X.lam b j

/-- `u_lo_eff = max(c_exp, u_lo_bj)` (line 807). -/
noncomputable def uLoEff (r : ℝ) (i j a b : Fin N) : ℝ := max (X.cexp i a b) (X.uLo r j b)

/-- `u_hi_eff = min(r, u_hi_bj)` (line 808). -/
noncomputable def uHiEff (r : ℝ) (j b : Fin N) : ℝ := min r (X.uHi r j b)

/-- The Term IV integrand for pole `k` of `b_grow[a][b]`.

`_antideriv_expquad` and `_antideriv_poly4` (lines 682-699) are precisely the antiderivatives
of this function, so the Python's `exp_int + poly_int` is the interval integral below. -/
noncomputable def ivIntegrand (r : ℝ) (i j a b : Fin N) (k : Fin M) (u : ℝ) : ℝ :=
    let z    := X.zp a b k
    let Rst  := X.cb a b k
    let Alm  := max (X.DeltaAi i a) 0
    let ce   := X.cexp i a b
    let de   := X.dexp i a b
    let ulo  := X.uLo r j b
    let Cbj  := Real.sqrt (X.ρ b * X.ρ j)
    let qP2  := -Cbj * (1 / 2) * X.Qpp j
    let qP1  := -Cbj * (-X.Q0 b j - X.Qpp j * ulo)
    let qP0  := -Cbj * (X.Q0 b j * ulo + (1 / 2) * X.Qpp j * ulo ^ 2)
    let Q0ai := X.Q0 a i
    let Qi   := (1 / 2) * X.Qpp i
    let E1   := (Alm / z + 1 / z ^ 2) * Real.exp (-z * ce)
    let E2   := (Alm ^ 2 / z + 2 * Alm / z ^ 2 + 2 / z ^ 3) * Real.exp (-z * ce)
    let G1   := de / z - 1 / z ^ 2
    let G2   := 2 * de / z - 2 / z ^ 2
    let H2   := -de ^ 2 / z + 2 * de / z ^ 2 - 2 / z ^ 3
    let Ak   := Rst * (Q0ai * E1 + Qi * E2)
    let p2   := Rst * Qi * (-(1 / z))
    let p1   := Rst * (Q0ai * (-(1 / z)) + Qi * G2)
    let p0   := Rst * (Q0ai * G1 + Qi * H2)
    Ak * Real.exp (z * u) * (qP0 + qP1 * u + qP2 * u ^ 2)
      + (p0 * qP0
         + (p1 * qP0 + p0 * qP1) * u
         + (p2 * qP0 + p1 * qP1 + p0 * qP2) * u ^ 2
         + (p2 * qP1 + p1 * qP2) * u ^ 3
         + (p2 * qP2) * u ^ 4)

/-- Term IV sub-term for intermediate species `(a, b)`.  The `if` mirrors the
`if u_lo_eff >= u_hi_eff: continue` guard (line 809) — note this is a *definitional clamp*,
not a property of the integral (a reversed interval integral is `−∫`, not `0`). -/
noncomputable def termIVsub (r : ℝ) (i j a b : Fin N) : ℝ :=
    if X.uHiEff r j b ≤ X.uLoEff r i j a b then 0
    else Real.sqrt (X.ρ a * X.ρ i) *
      ∑ k : Fin M, ∫ u in (X.uLoEff r i j a b)..(X.uHiEff r j b), X.ivIntegrand r i j a b k u

/-- `IV = −Σ_{a,b} (sub-term)` (line 855). -/
noncomputable def termIV (r : ℝ) (i j : Fin N) : ℝ :=
    - ∑ a : Fin N, ∑ b : Fin N, X.termIVsub r i j a b

/-- The full mediated correction `(II + III + IV) / (2π√(ρᵢρⱼ)·r)` (lines 856-857). -/
noncomputable def mediated (r : ℝ) (i j : Fin N) : ℝ :=
    (X.termII r i j + X.termIII r i j + X.termIV r i j)
      / (2 * π * Real.sqrt (X.ρ i * X.ρ j) * r)

/-!
### Term IV activation conditions
-/

/-- Condition **(A)**: `2σₐ + σ_b < σⱼ`.  Equivalent to `r* < R[i,j]`, i.e. the breakpoint
lies strictly inside the inner region. -/
def ActiveA (j a b : Fin N) : Prop := 2 * X.σ a + X.σ b < X.σ j

/-- Condition **(B)**: `σⱼ < 3σ_b`.  Equivalent to `u_lo_bj < r`, i.e. the integration window
is nonempty above `r*`. -/
def ActiveB (j b : Fin N) : Prop := X.σ j < 3 * X.σ b

/-!
### The second mediated knot `r**` and Condition C
-/

/-- The second mediated breakpoint `r** = r* + (3d_b − d_j)/2 = R[a,b] + R[i,a] + (3σ_b − σ_j)/2`
— where the effective lower limit switches from the constant `c_exp = r*` to the moving
`u_lo_bj(r)`. -/
noncomputable def rstarstar (i j a b : Fin N) : ℝ := X.R a b + X.R i a + (3 * X.σ b - X.σ j) / 2

/-- Condition **(C)**: `σₐ + 2σ_b < σⱼ`.  Equivalent to `r** < R[i,j]`, i.e. the second knot lies
strictly inside the inner region.  Strictly stronger than **(A)** together with **(B)**. -/
def CondC (j a b : Fin N) : Prop := X.σ a + 2 * X.σ b < X.σ j

/-- The b–j quadratic `qP(u) = qP0 + qP1·u + qP2·u²` assembled by `_compute_mediated`
(`fmsa_ga_matrix_mix.py:1092-1094`), whose coefficients are built from the moving lower limit
`u_lo_bj = uLo r j b`.  Exactly the `qP` factor inside `ivIntegrand`. -/
noncomputable def qPoly (r : ℝ) (j b : Fin N) (u : ℝ) : ℝ :=
    let ulo := X.uLo r j b
    let Cbj := Real.sqrt (X.ρ b * X.ρ j)
    let qP2 := -Cbj * (1 / 2) * X.Qpp j
    let qP1 := -Cbj * (-X.Q0 b j - X.Qpp j * ulo)
    let qP0 := -Cbj * (X.Q0 b j * ulo + (1 / 2) * X.Qpp j * ulo ^ 2)
    qP0 + qP1 * u + qP2 * u ^ 2

end Mix

/-!
## IB.1 — Terms II and III vanish in the inner region (unconditional)
-/

/-- **Task IB.1.**  Terms II and III of `_compute_mediated` are identically zero throughout
the inner region `(0, R[i,j])`, for every `N`, every pair `(i,j)` and every σ.

Proof sketch (all pieces are in place above):
* `Mix.alphaII_eq` : `alpha = r − σ[a] − R[i,j]`;
* `r < R[i,j]` (from `Ioo`) and `0 < σ[a]` (`Mix.hσ`) give `alpha < 0`;
* `lstar_eq_zero_of_alpha_neg` : `lstar = 0`;
* `I1cl_at_zero`, `I2cl_at_zero` (Task 1.3) : every pole term is `0`;
* `Finset.sum_eq_zero` twice.

Numerically confirmed for N=2,3 in `verify_mediated_breakpoints.py`. -/
theorem terms_II_III_zero {N M : ℕ} (X : Mix N M) (i j : Fin N) :
    ∀ r ∈ Ioo (0 : ℝ) (X.R i j), X.termII r i j = 0 ∧ X.termIII r i j = 0 := by
  intro r hr
  obtain ⟨hr0, hrR⟩ := hr
  refine ⟨?_, ?_⟩
  · -- Term II: every summand's `lstar` clamps to 0, so `I1cl = I2cl = 0`.
    unfold Mix.termII
    apply Finset.sum_eq_zero
    intro a _
    have halpha : X.alphaII r i j a < 0 := by
      rw [X.alphaII_eq]; have := X.hσ a; linarith
    rw [lstar_eq_zero_of_alpha_neg halpha]
    simp
  · -- Term III: symmetric, via `alphaIII_eq`.
    unfold Mix.termIII
    apply Finset.sum_eq_zero
    intro b _
    have halpha : X.alphaIII r i j b < 0 := by
      rw [X.alphaIII_eq]; have := X.hσ b; linarith
    rw [lstar_eq_zero_of_alpha_neg halpha]
    simp

/-!
## IB.2 — Term IV geometry and vanishing below the breakpoint
-/

/-- **Task IB.2.**  The geometry of Term IV's integration window, and the unconditional
vanishing of sub-term `(a,b)` below the breakpoint `r* = R[a,b] + R[i,a]`.

The four identities say: `Δ_ai` is *always* `−R[i,a] < 0`, hence `Alm` collapses to `0` and
the two exponential offsets coincide, `c_exp = d_exp = r*`.  This **derives** `r*`; it is not
an assumption.

The vanishing then needs nothing further: `u_hi_eff ≤ r` by definition, and
`u_lo_eff ≥ c_exp = r*`, so `r ≤ r*` forces `u_hi_eff ≤ u_lo_eff` — the `continue` branch.
No appeal to conditions A/B. -/
theorem termIV_geometry_and_vanishing {N M : ℕ} (X : Mix N M) (i j a b : Fin N) :
    X.DeltaAi i a = -X.R i a
      ∧ max (X.DeltaAi i a) 0 = 0
      ∧ X.cexp i a b = X.R a b + X.R i a
      ∧ X.dexp i a b = X.R a b + X.R i a
      ∧ ∀ r ≤ X.R a b + X.R i a, X.termIVsub r i j a b = 0 := by
  -- The driving identity: `Δ_ai = (σₐ−σᵢ)/2 − σₐ = −(σᵢ+σₐ)/2 = −R[i,a]`.
  have hDelta : X.DeltaAi i a = -X.R i a := by
    unfold Mix.DeltaAi Mix.lam Mix.R; ring
  have hRia : 0 < X.R i a := X.R_pos i a
  have hcexp : X.cexp i a b = X.R a b + X.R i a := by
    unfold Mix.cexp; rw [hDelta, neg_neg, max_eq_right (le_of_lt hRia)]
  refine ⟨hDelta, ?_, hcexp, ?_, ?_⟩
  · -- `Alm = max Δ_ai 0 = 0` since `Δ_ai < 0`.
    rw [hDelta]; exact max_eq_right (by linarith)
  · -- `d_exp = R[a,b] − Δ_ai = R[a,b] + R[i,a]`.
    unfold Mix.dexp; rw [hDelta]; ring
  · -- Empty window below `r*`: `u_hi_eff ≤ r ≤ r* = c_exp ≤ u_lo_eff`.
    intro r hr
    have hcond : X.uHiEff r j b ≤ X.uLoEff r i j a b := by
      have h1 : X.uHiEff r j b ≤ r := by unfold Mix.uHiEff; exact min_le_left _ _
      have h2 : X.cexp i a b ≤ X.uLoEff r i j a b := by
        unfold Mix.uLoEff; exact le_max_left _ _
      have h3 : r ≤ X.cexp i a b := by rw [hcexp]; exact hr
      linarith
    unfold Mix.termIVsub
    exact if_pos hcond

/-!
## IB.3 — Mediated vanishes when no `(a,b)` pair is active; the binary corollary
-/

/-- **Task IB.3, structural lemma (PROVED).**  Conditions A and B together force the strict
size chain `σₐ < σ_b < σⱼ`.

From (A) `2σₐ + σ_b < σⱼ` and `σₐ > 0`: `σ_b < σⱼ`.
From (A) and (B) `σⱼ < 3σ_b`: `2σₐ < σⱼ − σ_b < 2σ_b`, so `σₐ < σ_b`.

Three strictly increasing diameters are needed — which is exactly why `N = 2` cannot
activate Term IV (`binary_mediated_zero`). -/
theorem active_pair_size_chain {N M : ℕ} (X : Mix N M) (j a b : Fin N)
    (hA : X.ActiveA j a b) (hB : X.ActiveB j b) :
    X.σ a < X.σ b ∧ X.σ b < X.σ j := by
  unfold Mix.ActiveA at hA
  unfold Mix.ActiveB at hB
  have ha := X.hσ a
  exact ⟨by linarith, by linarith⟩

/-- **Task IB.3.**  If no intermediate pair `(a,b)` satisfies both activation conditions,
the entire mediated correction vanishes on the inner region.

Proof sketch: Terms II and III vanish by IB.1.  For Term IV, fix `(a,b)`; by `hno` either
(A) or (B) fails.
* If (A) fails, `σⱼ ≤ 2σₐ + σ_b`, i.e. `r* ≥ R[i,j] > r`, so IB.2's vanishing applies.
* If (B) fails, `3σ_b ≤ σⱼ`, so `u_lo_bj = r + (σⱼ − 3σ_b)/2 ≥ r ≥ u_hi_eff`, hence
  `u_lo_eff ≥ u_hi_eff` and the `continue` branch is taken. -/
theorem mediated_zero_of_no_active_pair {N M : ℕ} (X : Mix N M) (i j : Fin N)
    (hno : ∀ a b : Fin N, ¬ (X.ActiveA j a b ∧ X.ActiveB j b)) :
    ∀ r ∈ Ioo (0 : ℝ) (X.R i j), X.mediated r i j = 0 := by
  intro r hr
  obtain ⟨hr0, hrR⟩ := hr
  -- Terms II and III vanish by IB.1.
  have hII : X.termII r i j = 0 := (terms_II_III_zero X i j r ⟨hr0, hrR⟩).1
  have hIII : X.termIII r i j = 0 := (terms_II_III_zero X i j r ⟨hr0, hrR⟩).2
  -- Term IV vanishes sub-term by sub-term.
  have hIV : X.termIV r i j = 0 := by
    unfold Mix.termIV
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rcases not_and_or.mp (hno a b) with hnA | hnB
    · -- (A) fails: `σⱼ ≤ 2σₐ + σ_b`, so `r < R[i,j] ≤ r*`; IB.2's vanishing applies.
      simp only [Mix.ActiveA, not_lt] at hnA
      have hle : r ≤ X.R a b + X.R i a := by
        have hRle : X.R i j ≤ X.R a b + X.R i a := by simp only [Mix.R]; linarith
        linarith
      exact (termIV_geometry_and_vanishing X i j a b).2.2.2.2 r hle
    · -- (B) fails: `3σ_b ≤ σⱼ`, so `u_lo_bj ≥ r ≥ u_hi_eff`; the window is empty.
      simp only [Mix.ActiveB, not_lt] at hnB
      have hcond : X.uHiEff r j b ≤ X.uLoEff r i j a b := by
        have h1 : X.uHiEff r j b ≤ r := by unfold Mix.uHiEff; exact min_le_left _ _
        have h2 : r ≤ X.uLo r j b := by unfold Mix.uLo Mix.lam; linarith
        have h3 : X.uLo r j b ≤ X.uLoEff r i j a b := by
          unfold Mix.uLoEff; exact le_max_right _ _
        linarith
      unfold Mix.termIVsub
      exact if_pos hcond
  unfold Mix.mediated
  rw [hII, hIII, hIV]
  simp

/-- **Task IB.3, binary corollary.**  For a two-component mixture the mediated correction is
identically zero on the inner region — for **every** pair and **any** σ-ratio.

Proof sketch: by `mediated_zero_of_no_active_pair` it suffices that no `(a,b)` is active.
An active pair would give `σₐ < σ_b < σⱼ` (`active_pair_size_chain`) with `a, b, j : Fin 2`;
three pairwise-distinct values among two species is impossible (`Fin.cases` on `a`, `b`, `j`
leaves 8 goals, each closed by `linarith` from the chain).

This is the σ=[1,2] and σ=[1,4] rows of `verify_mediated_breakpoints.py`. -/
theorem binary_mediated_zero {M : ℕ} (X : Mix 2 M) (i j : Fin 2) :
    ∀ r ∈ Ioo (0 : ℝ) (X.R i j), X.mediated r i j = 0 := by
  apply mediated_zero_of_no_active_pair
  intro a b hact
  obtain ⟨hab, hbj⟩ := active_pair_size_chain X j a b hact.1 hact.2
  -- `σₐ < σ_b < σⱼ` needs three distinct diameters — impossible for `Fin 2`.
  fin_cases a <;> fin_cases b <;> fin_cases j <;> linarith

/-!
## IB.4 — The residue is a *single* polynomial on the inner region
-/

/-- **Task IB.4.**  After exact subtraction of `c_HS` and `mediated`, the residue is one
polynomial of degree ≤ 4 on all of `(0, R[i,j])` — with **no piecewise split** at the Term IV
breakpoint `r*` or at the `c_HS` kink `|λ_ij|`.

This is what licenses `oz_numerical._update_polycorr` to run a *single* B.8 moment inversion
over the whole inner region after subtracting `get_HS_FMT` and `_compute_mediated`.

The degree bound is imported from B.5 (`b5_degree_bound`, `B5MixturePoly.lean`); the content
here is that the same `P` works on both sides of every breakpoint, because `mediated` — the
only source of a breakpoint at `r*` — has been removed exactly rather than approximated. -/
theorem residue_is_polynomial {N M : ℕ} (X : Mix N M)
    (c1_inner c_hs term_I prefac : ℝ → ℝ) (i j : Fin N)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ 4)
    (hpf : ∀ r ∈ Ioo (0 : ℝ) (X.R i j), prefac r ≠ 0)
    (hdecomp : ∀ r ∈ Ioo (0 : ℝ) (X.R i j),
        c1_inner r = (term_I r + P.eval r) * prefac r + c_hs r + X.mediated r i j) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ 4 ∧
      ∀ r ∈ Ioo (0 : ℝ) (X.R i j),
        (c1_inner r - c_hs r - X.mediated r i j) / prefac r - term_I r = Q.eval r := by
  -- `Q = P`: subtracting `c_HS + mediated` leaves exactly `(term_I + P)·prefac`, and
  -- dividing by `prefac ≠ 0` then removing `term_I` recovers `P.eval r`.
  refine ⟨P, hdeg, fun r hr => ?_⟩
  have hpf' : prefac r ≠ 0 := hpf r hr
  have key : c1_inner r - c_hs r - X.mediated r i j = (term_I r + P.eval r) * prefac r := by
    rw [hdecomp r hr]; ring
  rw [key, mul_div_assoc, div_self hpf', mul_one]
  ring

/-!
## IB.5 — The activation conditions are satisfiable (the characterisation is sharp)
-/

/-- **Task IB.5 (PROVED).**  Witness that conditions A ∧ B *can* hold, so IB.3 is not
vacuously "always zero": the ternary mixture σ = [1, 4, 8] activates Term IV via the
intermediate pair `(a,b) = (0,1)` for target species `j = 2`.

  (A) `2·σ₀ + σ₁ = 2·1 + 4 = 6 < 8 = σ₂`   ✓
  (B) `σ₂ = 8 < 12 = 3·σ₁`                 ✓

and the breakpoint lies strictly inside the inner region of pair `(0,2)`:
`r* = R[0,1] + R[0,0] = 2.5 + 1 = 3.5 < 4.5 = R[0,2]`.

This is the Tern148 block of `verify_mediated_breakpoints.py`, where mediated is confirmed
nonzero for pairs (0,2), (1,2), (2,2). -/
theorem ternary_148_active {M : ℕ} (X : Mix 3 M) (hσ : X.σ = ![1, 4, 8]) :
    X.ActiveA 2 0 1 ∧ X.ActiveB 2 1 ∧ X.R 0 1 + X.R 0 0 < X.R 0 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Mix.ActiveA, Mix.ActiveB, Mix.R, hσ] <;> norm_num

/-!
## IB.7 — The second knot `r**` is interior iff Condition C; and `C ∧ B ⟹ A`
-/

/-- **Task IB.7.**  The second mediated knot lies strictly inside the inner region `(0, R[i,j])`
exactly when Condition C holds:
`r** = R[a,b] + R[i,a] + (3σ_b − σ_j)/2 < R[i,j]  ⟺  σ_a + 2σ_b < σ_j`.
Substituting the `R`'s reduces both directions to `2σ_a + 4σ_b < 2σ_j` — pure diameter arithmetic. -/
theorem rstarstar_interior_iff_C {N M : ℕ} (X : Mix N M) (i j a b : Fin N) :
    X.rstarstar i j a b < X.R i j ↔ X.CondC j a b := by
  unfold Mix.rstarstar Mix.R Mix.CondC
  constructor <;> intro h <;> linarith

/-- **Task IB.7 (corollary).**  Condition C together with activation B forces activation A:
`σ_a + 2σ_b < σ_j` and `σ_j < 3σ_b` give `σ_a < σ_b`, hence `2σ_a + σ_b < σ_a + 2σ_b < σ_j`.
So whenever the *second* knot `r**` is interior (C) and the window is nonempty (B), the *first*
knot `r*` is interior too (A). -/
theorem condC_activeB_imp_activeA {N M : ℕ} (X : Mix N M) (j a b : Fin N)
    (hC : X.CondC j a b) (hB : X.ActiveB j b) : X.ActiveA j a b := by
  unfold Mix.CondC at hC
  unfold Mix.ActiveB at hB
  unfold Mix.ActiveA
  linarith

/-!
## IB.8 — Mediated knot completeness: the upper limit never switches (`u_hi_eff = r`)
-/

/-- **Task IB.8.**  When `σ_b < σ_j` the upper integration limit is pinned to `r`:
`u_hi_eff = min(r, u_hi_bj) = r`, because `u_hi_bj = r + (σ_j − σ_b)/2 ≥ r`.
Only the *lower* limit `u_lo_eff` can move, so the `(a,b)` sub-term changes analytic form only
where the lower limit switches — at `r*` and (if C) `r**`, and nowhere else. -/
theorem uHiEff_eq_r {N M : ℕ} (X : Mix N M) (r : ℝ) (j b : Fin N) (h : X.σ b < X.σ j) :
    X.uHiEff r j b = r := by
  unfold Mix.uHiEff Mix.uHi Mix.lam
  exact min_eq_left (by linarith)

/-- **Task IB.8 (activated form).**  Under both activation conditions the size chain gives
`σ_b < σ_j` (`active_pair_size_chain`), so the upper limit is pinned to `r`. -/
theorem uHiEff_eq_r_of_active {N M : ℕ} (X : Mix N M) (r : ℝ) (j a b : Fin N)
    (hA : X.ActiveA j a b) (hB : X.ActiveB j b) : X.uHiEff r j b = r :=
  uHiEff_eq_r X r j b (active_pair_size_chain X j a b hA hB).2

/-!
## IB.6 — The `r**` switch identity `qP(u_lo_bj) = 0` and the C¹ mechanism
-/

/-- **Task IB.6.**  The b–j quadratic vanishes at its own lower-limit anchor:
`qP0 + qP1·u_lo_bj + qP2·u_lo_bj² = 0`.  A pure `ring` identity (the `½ − 1 + ½ = 0`
cancellation), the Term-IV analog of IB.2's `Δ_ai = −R[i,a]`. -/
theorem qP_at_uLo_zero {N M : ℕ} (X : Mix N M) (r : ℝ) (j b : Fin N) :
    X.qPoly r j b (X.uLo r j b) = 0 := by
  simp only [Mix.qPoly]
  ring

/-- **Task IB.6 (C¹ mechanism).**  Because `ivIntegrand u = qP(u)·(Ak·exp(z·u) + p(u))` and
`qP(u_lo_bj) = 0` (`qP_at_uLo_zero`), the *whole* integrand vanishes at the moving lower boundary:
`ivIntegrand r i j a b k (u_lo_bj) = 0`.  Hence the Leibniz boundary term
`−ivIntegrand(u_lo_bj)·(d u_lo_bj/dr)` in `d/dr mediated` is `0` at the crossover — value **and**
slope of `mediated` are continuous across `r**` (no slope jump: **C¹**).  A `ring` identity. -/
theorem ivIntegrand_at_uLo_zero {N M : ℕ} (X : Mix N M) (r : ℝ) (i j a b : Fin N) (k : Fin M) :
    X.ivIntegrand r i j a b k (X.uLo r j b) = 0 := by
  simp only [Mix.ivIntegrand]
  ring

end FMSA.InnerDecomp
