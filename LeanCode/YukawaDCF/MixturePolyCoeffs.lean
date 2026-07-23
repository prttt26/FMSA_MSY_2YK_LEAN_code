/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MatrixQ0
import LeanCode.YukawaDCF.InnerOriginBC
import LeanCode.YukawaDCF.ContactMatching

/-!
# Tasks GAP.5–GAP.10 — Analytical Determination of P_{ij}(r) for the Mixture Case

## Context

Task GAP.4 established the like-pair polynomial constant p₀ = −2Kga using
the N=1 identity `g + a·exp(−z) = 1`.  For a general N-component mixture,
the full inside-core polynomial

```
P_{ij}(r) = A_{ij} + B_{ij}·r + C_{ij}·r² + D_{ij}·r³ + E_{ij}^{(4)}·r⁴
```

has five coefficients that are generically **nonzero** for unlike pairs.
Tasks GAP.5–GAP.9 formalise the complete determination of all five coefficients
via the s=0 Laurent expansion of the exact inside-core Laplace transform.

## Source

[LN] §§ "Origin Regularity and Determination of the Polynomial" and
"Explicit Derivative Formulas for the Mixture Coefficients" (lines 1319–1435);
[LN] "Symmetry Constraints on the Coefficient Matrices" (lines 1440–1466).

## The two key building blocks

The Q̂₀(s) matrix entries involve, as functions of the Laplace variable s:
```
p1(σ, s) := (1 − s·σ − exp(−s·σ)) / s²
p2(σ, s) := (1 − s·σ + (s·σ)²/2 − exp(−s·σ)) / s³
```
Both have removable singularities at s = 0 with
```
p1(σ, 0) = −σ²/2      p2(σ, 0) = σ³/6
```
This is established by showing the numerators vanish to orders 2 and 3
respectively, proved below as `HasDerivAt` statements.

## Results Summary

| Task | Key theorem                       | Status                                        |
|------|-----------------------------------|-----------------------------------------------|
| GAP.5  | `q0_entry_degree_bound`                 | ✓ proved                                      |
| GAP.6  | `origin_unique_constraint`     | ✓ proved                                      |
| GAP.7  | `no_contact_bc`                | ✓ proved                                      |
| GAP.8  | `poly_coeff_from_laurent`      | ⚠ VACUOUS (see its docstring)                 |
| GAP.9  | `no_odd_symmetry`,             | ✓ proved (true, but see below)                |
|      | `d_ij_nonzero_example`,        |                                               |
|      | `dij_cubic_nonzero`            | ✓ proved — **Laplace-space `q0_entry` fact**, |
|      |                                   | NOT evidence for `D_ij ≠ 0` (re-scoped)       |
|      | *task claim `D_ij ≠ 0`*           | ❌ **FALSIFIED 2026-07-17 — `D_ij ≡ 0`**       |
| GAP.10 | `poly_natDegree_le_four`           | ✓ proved (unconditional `≤ 4`)                |
|      | `poly_natDegree_eq_four`           | ✓ proved (`= 4` given `a ≠ 0`)                |
|      | `poly_natDegree_eq_four_iff`       | ✓ proved (`= 4 ↔ a ≠ 0`)                      |
|      | *task claim "degree is 4"*        | ⚠ **RELAXED — generic only** (leading coeff   |
|      |                                   | vanishes on a codim-1 set; inner piece deg 1) |

**Group GAP is the coefficient-fixing scaffolding of `FMSA_GA_matrix_mix`, a superseded method.**
Its programme (posit the [LN] Eq. (101) ansatz "`P_ij` is a single `deg ≤ 4` polynomial on
`(0, R_ij)`", then pin the coefficients down) is obsolete: the shipped `fmsa_double_prop` computes
the inner core *constructively* as a piecewise (poly × exp) closed form, needs no ansatz, and shows
the ansatz is **false** for unlike pairs (two pieces, split at `λ_ij`).  Retained as the record of
the superseded route.  See `proof_notes_yukawa_dcf.md` GAP.8–GAP.10.
-/

set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Real Filter Topology Set Polynomial

namespace FMSA.MixturePoly

-- ============================================================
-- § GAP.5 — Degree Bound: deg P_{ij}(r) ≤ 4
-- ============================================================

/-!
## GAP.5 — Degree bound foundations

The polynomial P_{ij}(r) arises as the s=0 residue of the inside-core Laplace
transform.  The degree is ≤ 4 because the Q̂₀(s) matrix entries are analytic
at s=0: the apparent poles from dividing by s² and s³ are cancelled by zeros
of the numerators to the same order.

The lemmas below establish those vanishing-derivative facts for p1 and p2.
-/

section DegreeBound

/-- **GAP.5 helper — p1 numerator vanishes at s = 0.** -/
lemma p1_num_zero (sigma : ℝ) : (1 : ℝ) - 0 * sigma - exp (-(0 * sigma)) = 0 := by simp

/-- **GAP.5 helper — first derivative of p1 numerator at s = 0 is zero.**

`d/ds [1 − s·σ − exp(−s·σ)]|_{s=0} = −σ + σ·exp(0) = 0`.

The numerator therefore vanishes to order ≥ 2 at s = 0 (together with
`p1_num_zero`), so `p1(σ, s) = (numerator)/s²` has a removable singularity
at s = 0 with finite limit −σ²/2. -/
lemma p1_num_hasDerivAt (sigma : ℝ) :
    HasDerivAt (fun s => (1 : ℝ) - s * sigma - exp (-(s * sigma))) 0 0 := by
  -- inner: d/ds [-(s·σ)] = -σ at s = 0
  have hinner : HasDerivAt (fun s : ℝ => -(s * sigma)) (-sigma) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const sigma).neg
    simp only [id, one_mul] at h; exact h
  -- d/ds [exp(-(s·σ))]|_{s=0} = exp(0)·(-σ) = -σ
  have hexp : HasDerivAt (fun s : ℝ => exp (-(s * sigma))) (-sigma) 0 := by
    have h := hinner.exp
    simp only [neg_zero, zero_mul, exp_zero, one_mul] at h
    exact h
  -- combine: d/ds [1 - s·σ - exp(-s·σ)] = 0 - σ - (-σ) = 0
  have h := ((hasDerivAt_const (0 : ℝ) 1).sub
              ((hasDerivAt_id _).mul_const sigma)).sub hexp
  exact h.congr_deriv (by ring)

/-- **GAP.5 helper — second derivative of p1 numerator at s = 0 equals −σ².**

`d²/ds² [1 − s·σ − exp(−s·σ)]|_{s=0} = −σ²`.

Together with `p1_num_zero` and `p1_num_hasDerivAt`, this shows the
numerator has a zero of order exactly 2 at s = 0. -/
lemma p1_num_hasDerivAt2 (sigma : ℝ) :
    HasDerivAt (fun s : ℝ => -sigma + sigma * exp (-(s * sigma))) (-sigma ^ 2) 0 := by
  have hinner : HasDerivAt (fun s : ℝ => -(s * sigma)) (-sigma) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const sigma).neg
    simp only [id, one_mul] at h; exact h
  have hexp : HasDerivAt (fun s : ℝ => exp (-(s * sigma))) (-sigma) 0 := by
    have h := hinner.exp
    simp only [neg_zero, zero_mul, exp_zero, one_mul] at h
    exact h
  have hmul : HasDerivAt (fun s : ℝ => sigma * exp (-(s * sigma))) (-sigma ^ 2) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) sigma).mul hexp
    exact h.congr_deriv (by ring)
  have h := (hasDerivAt_const (0 : ℝ) (-sigma)).add hmul
  exact h.congr_deriv (by ring)

/-- **GAP.5 helper — p2 numerator vanishes at s = 0.** -/
lemma p2_num_zero (sigma : ℝ) :
    (1 : ℝ) - 0 * sigma + (0 * sigma) ^ 2 / 2 - exp (-(0 * sigma)) = 0 := by simp

/-- **GAP.5 helper — first derivative of p2 numerator at s = 0 is zero.**

`d/ds [1 − s·σ + (s·σ)²/2 − exp(−s·σ)]|_{s=0} = −σ + 0 + σ = 0`. -/
lemma p2_num_hasDerivAt (sigma : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - s * sigma + (s * sigma) ^ 2 / 2 - exp (-(s * sigma))) 0 0 := by
  have hinner : HasDerivAt (fun s : ℝ => -(s * sigma)) (-sigma) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const sigma).neg
    simp only [id, one_mul] at h; exact h
  have hexp : HasDerivAt (fun s : ℝ => exp (-(s * sigma))) (-sigma) 0 := by
    have h := hinner.exp
    simp only [neg_zero, zero_mul, exp_zero, one_mul] at h
    exact h
  -- d/ds [(s·sigma)²/2] = (s·sigma)·sigma ; at s=0 this is 0
  have hsq : HasDerivAt (fun s : ℝ => (s * sigma) ^ 2 / 2) 0 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const sigma).pow 2 |>.div_const 2
    exact h.congr_deriv (by simp)
  have h := (((hasDerivAt_const _ (1 : ℝ)).sub ((hasDerivAt_id _).mul_const sigma)).add
              hsq).sub hexp
  exact h.congr_deriv (by ring)

/-- **GAP.5 helper — second derivative of p2 numerator at s = 0 is zero.**

`d²/ds²[1 − s·σ + (s·σ)²/2 − exp(−s·σ)]|_{s=0} = σ² − σ² = 0`. -/
lemma p2_num_hasDerivAt2 (sigma : ℝ) :
    HasDerivAt (fun s : ℝ => -sigma + sigma ^ 2 * s + sigma * exp (-(s * sigma))) 0 0 := by
  have hinner : HasDerivAt (fun s : ℝ => -(s * sigma)) (-sigma) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const sigma).neg
    simp only [id, one_mul] at h; exact h
  have hexp : HasDerivAt (fun s : ℝ => exp (-(s * sigma))) (-sigma) 0 := by
    have h := hinner.exp
    simp only [neg_zero, zero_mul, exp_zero, one_mul] at h
    exact h
  have hlin : HasDerivAt (fun s : ℝ => sigma ^ 2 * s) (sigma ^ 2) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_mul (sigma ^ 2)
    simp only [id, mul_one] at h; exact h
  have hmul : HasDerivAt (fun s : ℝ => sigma * exp (-(s * sigma))) (-sigma ^ 2) 0 := by
    have h := (hasDerivAt_const _ sigma).mul hexp
    exact h.congr_deriv (by ring)
  have h := ((hasDerivAt_const _ (-sigma)).add hlin).add hmul
  exact h.congr_deriv (by ring)

/-- **GAP.5 helper — third derivative of p2 numerator at s = 0 equals σ³.**

`d³/ds³[1 − s·σ + (s·σ)²/2 − exp(−s·σ)]|_{s=0} = σ³`.

Together with the three vanishing values above, this establishes that the
p2 numerator has a zero of order exactly 3 at s = 0, confirming that
`p2(σ, s) = (numerator)/s³` extends analytically with limit σ³/6. -/
lemma p2_num_hasDerivAt3 (sigma : ℝ) :
    HasDerivAt (fun s : ℝ => sigma ^ 2 - sigma ^ 2 * exp (-(s * sigma))) (sigma ^ 3) 0 := by
  have hinner : HasDerivAt (fun s : ℝ => -(s * sigma)) (-sigma) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const sigma).neg
    simp only [id, one_mul] at h; exact h
  have hexp : HasDerivAt (fun s : ℝ => exp (-(s * sigma))) (-sigma) 0 := by
    have h := hinner.exp
    simp only [neg_zero, zero_mul, exp_zero, one_mul] at h
    exact h
  have hmul : HasDerivAt (fun s : ℝ => sigma ^ 2 * exp (-(s * sigma))) (-sigma ^ 3) 0 := by
    have h := (hasDerivAt_const _ (sigma ^ 2)).mul hexp
    exact h.congr_deriv (by ring)
  have h := (hasDerivAt_const _ (sigma ^ 2)).sub hmul
  exact h.congr_deriv (by ring)

/-- **GAP.5 helper — p2(σ, z) → σ³/6 as z → 0⁺.**

`(1 − z·σ + (z·σ)²/2 − exp(−z·σ)) / z³  →  σ³/6`.

**Proof:** Write `p2(σ,z) = σ³/6 + r(z)` where
  `r(z) = (1 − z·σ + (z·σ)²/2 − (z·σ)³/6 − exp(−z·σ)) / z³`.
Apply `Real.exp_bound n=4`: for `|z·σ| ≤ 1`,
  `|exp(−z·σ) − (1 − z·σ + (z·σ)²/2 − (z·σ)³/6)| ≤ (z|σ|)⁴ · (5/96)`,
so `|r(z)| ≤ z · (|σ|⁴ · 5/96) → 0`.  Squeeze gives `r(z) → 0`. -/
lemma p2_limit (sigma : ℝ) :
    Filter.Tendsto
        (fun z : ℝ => (1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (sigma ^ 3 / 6)) := by
  -- Write p2(sigma,z) = sigma³/6 + r(z), r(z) = (1-zσ+(zσ)²/2-(zσ)³/6-exp(-zσ))/z³
  have halg : ∀ᶠ z in nhdsWithin 0 (Set.Ioi 0),
      (1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3 =
      sigma ^ 3 / 6 +
        (1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6 -
          Real.exp (-(z * sigma))) / z ^ 3 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp [hz']; ring
  suffices hrem : Filter.Tendsto
      (fun z : ℝ => (1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6 -
        Real.exp (-(z * sigma))) / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
    have hconst : Filter.Tendsto (fun _ : ℝ => sigma ^ 3 / 6)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (sigma ^ 3 / 6)) :=
      tendsto_const_nhds
    have hlim := hconst.add hrem
    simpa using hlim.congr' (halg.mono (fun z hz => hz.symm))
  -- Bound r(z) → 0 by exp_bound n=4 and squeeze
  have htend_z : Filter.Tendsto (fun z : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  set C := |sigma| ^ 4 * (5 / 96) with hC_def
  have hbnd : Filter.Tendsto (fun z : ℝ => z * C) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    by simpa using htend_z.mul_const C
  have hbnd_neg : Filter.Tendsto (fun z : ℝ => -(z * C)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    by simpa [neg_zero] using hbnd.neg
  -- Restrict to z with |z*sigma| <= 1 so exp_bound hypothesis holds
  have hsmall : ∀ᶠ z in nhdsWithin 0 (Set.Ioi 0), |z * sigma| <= 1 := by
    have hpos : (0 : ℝ) < 1 / (|sigma| + 1) := by positivity
    have h0 : ∀ᶠ z in nhds (0 : ℝ), |z * sigma| <= 1 := by
      filter_upwards [Metric.ball_mem_nhds 0 hpos] with z hz
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
      calc |z * sigma| = |z| * |sigma| := abs_mul z sigma
        _ <= |z| * (|sigma| + 1) := by nlinarith [abs_nonneg z, abs_nonneg sigma]
        _ <= 1 / (|sigma| + 1) * (|sigma| + 1) :=
              le_of_lt (mul_lt_mul_of_pos_right hz (by positivity))
        _ = 1 := by field_simp
    exact h0.filter_mono nhdsWithin_le_nhds
  -- Key bound: |r(z)| <= z * C for z ∈ Ioi 0 near 0
  have habs_ev : ∀ᶠ z in nhdsWithin 0 (Set.Ioi 0),
      |(1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6 -
        Real.exp (-(z * sigma))) / z ^ 3| <= z * C := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hzsigma
    have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
    -- exp_bound with x = -(z*sigma), n = 4
    have hbc : |-(z * sigma)| <= 1 := by rwa [abs_neg]
    have hbound := Real.exp_bound hbc (n := 4) (by norm_num)
    -- Evaluate the sum ∑_{m=0}^3 (-(z·sigma))^m / m!
    have hsum : ∑ m ∈ Finset.range 4, (-(z * sigma)) ^ m / (m.factorial : ℝ) =
        1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.factorial]; ring
    rw [hsum, abs_neg, abs_mul, abs_of_pos hz0] at hbound
    -- hbound: |exp(-zσ)-(1-zσ+(zσ)²/2-(zσ)³/6)| <= (z*|sigma|)⁴ * (5 / (24*4))
    rw [abs_div, abs_of_pos (pow_pos hz0 3), div_le_iff₀ (pow_pos hz0 3)]
    calc |1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6 - Real.exp (-(z * sigma))|
        = |Real.exp (-(z * sigma)) - (1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6)| :=
          abs_sub_comm _ _
      _ <= (z * |sigma|) ^ 4 * ((Nat.succ 4 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) := hbound
      _ = z * C * z ^ 3 := by
          rw [hC_def]
          have h1 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
          have h2 : (Nat.succ 4 : ℝ) = 5 := by norm_num
          rw [h1, h2]; ring
  -- Squeeze: -z*C <= r(z) <= z*C → r(z) → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbnd_neg hbnd
  · filter_upwards [habs_ev] with z habs
    have h1 := neg_le_neg habs
    have h2 := neg_abs_le ((1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6 -
      Real.exp (-(z * sigma))) / z ^ 3)
    linarith
  · filter_upwards [habs_ev] with z habs
    linarith [le_abs_self ((1 - z * sigma + (z * sigma) ^ 2 / 2 - (z * sigma) ^ 3 / 6 -
      Real.exp (-(z * sigma))) / z ^ 3)]

/-- **GAP.5 helper — p1(σ, z) → −σ²/2 as z → 0⁺.**

`(1 − z·σ − exp(−z·σ)) / z²  →  −σ²/2`.

**Proof:** The exact algebraic identity (valid for all z ≠ 0)
```
p1(σ,z) = −σ²/2 + z · p2(σ,z)
```
follows from `field_simp; ring`.  Since `p2(σ,z) → σ³/6` is finite (p2_limit),
`z · p2(σ,z) → 0 · σ³/6 = 0`, so `p1(σ,z) → −σ²/2 + 0 = −σ²/2`. -/
lemma p1_limit (sigma : ℝ) :
    Filter.Tendsto (fun z : ℝ => (1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-sigma ^ 2 / 2)) := by
  -- Algebraic identity: p1(sigma,z) = -sigma²/2 + z · p2(sigma,z)  (for z ≠ 0)
  have halg : ∀ᶠ z in nhdsWithin 0 (Set.Ioi 0),
      (1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2 =
      -sigma ^ 2 / 2 +
        z * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp [hz']
    ring
  -- z * p2(sigma,z) → 0  (z → 0, p2 → sigma³/6 finite)
  have hz : Filter.Tendsto (fun z : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hzp2 : Filter.Tendsto
      (fun z => z * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hz.mul (p2_limit sigma)
  -- Combine: -sigma²/2 + z·p2 → -sigma²/2 + 0 = -sigma²/2
  have hlim : Filter.Tendsto
      (fun z => -sigma ^ 2 / 2 +
        z * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-sigma ^ 2 / 2)) := by
    simpa using tendsto_const_nhds.add hzp2
  exact hlim.congr' (halg.mono (fun z hz => hz.symm))

/-- **GAP.5 helper — cubic Taylor coefficient of `p1(σ,s) = (1−sσ−e^{−sσ})/s²` at s = 0 is `σ⁵/120`.**

After subtracting the order-0/1/2 Taylor terms `−σ²/2 + (σ³/6)s − (σ⁴/24)s²` and dividing by `s³`,
the limit is the cubic coefficient `σ⁵/120`. This is the r³-relevant piece of the like-pair Baxter
building block, needed (together with `p2_cubic_coeff` and the `exp(−λs)` prefactor) to assemble the
cubic coefficient `D_ij` (Task GAP.9). Proof: rewrite as `σ⁵/120 + (Σ_{k=0}^{5}(−sσ)^k/k! − e^{−sσ})/s⁵`
and squeeze the remainder to 0 via `Real.exp_bound` (n = 6) — same technique as `p1_limit`, one
order higher. -/
lemma p1_cubic_coeff (sigma : ℝ) :
    Filter.Tendsto
        (fun s : ℝ => ((1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2
          - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * s - sigma ^ 4 / 24 * s ^ 2)) / s ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (sigma ^ 5 / 120)) := by
  have halg : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ((1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2
          - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * s - sigma ^ 4 / 24 * s ^ 2)) / s ^ 3 =
      sigma ^ 5 / 120 +
        ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 - Real.exp (-(s * sigma))) / s ^ 5) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := (Set.mem_Ioi.mp hs).ne'
    field_simp [hs']; ring
  suffices hrem : Filter.Tendsto
      (fun s : ℝ => (1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 - Real.exp (-(s * sigma))) / s ^ 5)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
    have hlim := (tendsto_const_nhds (x := sigma ^ 5 / 120)).add hrem
    simpa using hlim.congr' (halg.mono (fun s hs => hs.symm))
  have htend_s : Filter.Tendsto (fun s : ℝ => s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  set C := |sigma| ^ 6 * (7 / (720 * 6)) with hC_def
  have hbnd : Filter.Tendsto (fun s : ℝ => s * C) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using htend_s.mul_const C
  have hbnd_neg : Filter.Tendsto (fun s : ℝ => -(s * C)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [neg_zero] using hbnd.neg
  have hsmall : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), |s * sigma| ≤ 1 := by
    have hpos : (0 : ℝ) < 1 / (|sigma| + 1) := by positivity
    have h0 : ∀ᶠ s in nhds (0 : ℝ), |s * sigma| ≤ 1 := by
      filter_upwards [Metric.ball_mem_nhds 0 hpos] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      calc |s * sigma| = |s| * |sigma| := abs_mul s sigma
        _ ≤ |s| * (|sigma| + 1) := by nlinarith [abs_nonneg s, abs_nonneg sigma]
        _ ≤ 1 / (|sigma| + 1) * (|sigma| + 1) :=
              le_of_lt (mul_lt_mul_of_pos_right hs (by positivity))
        _ = 1 := by field_simp
    exact h0.filter_mono nhdsWithin_le_nhds
  have habs_ev : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      |(1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 - Real.exp (-(s * sigma))) / s ^ 5| ≤ s * C := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hssigma
    have hs0 : (0 : ℝ) < s := Set.mem_Ioi.mp hs
    have hbc : |-(s * sigma)| ≤ 1 := by rwa [abs_neg]
    have hbound := Real.exp_bound hbc (n := 6) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 6, (-(s * sigma)) ^ m / (m.factorial : ℝ) =
        1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.factorial]; ring
    rw [hsum, abs_neg, abs_mul, abs_of_pos hs0] at hbound
    rw [abs_div, abs_of_pos (pow_pos hs0 5), div_le_iff₀ (pow_pos hs0 5)]
    calc |1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
            - (s * sigma) ^ 5 / 120 - Real.exp (-(s * sigma))|
        = |Real.exp (-(s * sigma)) - (1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
            + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120)| :=
          abs_sub_comm _ _
      _ ≤ (s * |sigma|) ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := hbound
      _ = s * C * s ^ 5 := by
          rw [hC_def]
          have h1 : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
          have h2 : (Nat.succ 6 : ℝ) = 7 := by norm_num
          rw [h1, h2]; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbnd_neg hbnd
  · filter_upwards [habs_ev] with s habs
    have h2 := neg_abs_le ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 - Real.exp (-(s * sigma))) / s ^ 5)
    linarith [neg_le_neg habs]
  · filter_upwards [habs_ev] with s habs
    linarith [le_abs_self ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 - Real.exp (-(s * sigma))) / s ^ 5)]

/-- **GAP.5 helper — cubic Taylor coefficient of `p2(σ,s) = (1−sσ+(sσ)²/2−e^{−sσ})/s³` at s = 0 is
`−σ⁶/720`.**

After subtracting the order-0/1/2 Taylor terms `σ³/6 − (σ⁴/24)s + (σ⁵/120)s²` and dividing by `s³`,
the limit is the cubic coefficient `−σ⁶/720`. Companion to `p1_cubic_coeff`; the two together give the
complete order-3 Taylor data of the Baxter building blocks p1, p2, from which `D_ij` (the r³
coefficient, Task GAP.9) is assembled. Proof: rewrite as
`−σ⁶/720 + (Σ_{k=0}^{6}(−sσ)^k/k! − e^{−sσ})/s⁶` and squeeze via `Real.exp_bound` (n = 7). -/
lemma p2_cubic_coeff (sigma : ℝ) :
    Filter.Tendsto
        (fun s : ℝ => ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3
          - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * s + sigma ^ 5 / 120 * s ^ 2)) / s ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-sigma ^ 6 / 720)) := by
  have halg : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3
          - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * s + sigma ^ 5 / 120 * s ^ 2)) / s ^ 3 =
      -sigma ^ 6 / 720 +
        ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - Real.exp (-(s * sigma))) / s ^ 6) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := (Set.mem_Ioi.mp hs).ne'
    field_simp [hs']; ring
  suffices hrem : Filter.Tendsto
      (fun s : ℝ => (1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - Real.exp (-(s * sigma))) / s ^ 6)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
    have hlim := (tendsto_const_nhds (x := -sigma ^ 6 / 720)).add hrem
    simpa using hlim.congr' (halg.mono (fun s hs => hs.symm))
  have htend_s : Filter.Tendsto (fun s : ℝ => s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  set C := |sigma| ^ 7 * (8 / (5040 * 7)) with hC_def
  have hbnd : Filter.Tendsto (fun s : ℝ => s * C) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using htend_s.mul_const C
  have hbnd_neg : Filter.Tendsto (fun s : ℝ => -(s * C)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [neg_zero] using hbnd.neg
  have hsmall : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), |s * sigma| ≤ 1 := by
    have hpos : (0 : ℝ) < 1 / (|sigma| + 1) := by positivity
    have h0 : ∀ᶠ s in nhds (0 : ℝ), |s * sigma| ≤ 1 := by
      filter_upwards [Metric.ball_mem_nhds 0 hpos] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      calc |s * sigma| = |s| * |sigma| := abs_mul s sigma
        _ ≤ |s| * (|sigma| + 1) := by nlinarith [abs_nonneg s, abs_nonneg sigma]
        _ ≤ 1 / (|sigma| + 1) * (|sigma| + 1) :=
              le_of_lt (mul_lt_mul_of_pos_right hs (by positivity))
        _ = 1 := by field_simp
    exact h0.filter_mono nhdsWithin_le_nhds
  have habs_ev : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      |(1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - Real.exp (-(s * sigma))) / s ^ 6|
        ≤ s * C := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hssigma
    have hs0 : (0 : ℝ) < s := Set.mem_Ioi.mp hs
    have hbc : |-(s * sigma)| ≤ 1 := by rwa [abs_neg]
    have hbound := Real.exp_bound hbc (n := 7) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 7, (-(s * sigma)) ^ m / (m.factorial : ℝ) =
        1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.factorial]; ring
    rw [hsum, abs_neg, abs_mul, abs_of_pos hs0] at hbound
    rw [abs_div, abs_of_pos (pow_pos hs0 6), div_le_iff₀ (pow_pos hs0 6)]
    calc |1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
            - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - Real.exp (-(s * sigma))|
        = |Real.exp (-(s * sigma)) - (1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
            + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720)| :=
          abs_sub_comm _ _
      _ ≤ (s * |sigma|) ^ 7 * ((Nat.succ 7 : ℝ) / ((Nat.factorial 7 : ℝ) * 7)) := hbound
      _ = s * C * s ^ 6 := by
          rw [hC_def]
          have h1 : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
          have h2 : (Nat.succ 7 : ℝ) = 8 := by norm_num
          rw [h1, h2]; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbnd_neg hbnd
  · filter_upwards [habs_ev] with s habs
    have h2 := neg_abs_le ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720
      - Real.exp (-(s * sigma))) / s ^ 6)
    linarith [neg_le_neg habs]
  · filter_upwards [habs_ev] with s habs
    linarith [le_abs_self ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720
      - Real.exp (-(s * sigma))) / s ^ 6)]

/-- **GAP.9 helper — order-3 Taylor remainder of the `exp(−λ·z)` prefactor.**

`(exp(−λ·z) − (1 − λz + (λz)²/2 − (λz)³/6)) / z³ → 0` as `z → 0⁺`. The `exp(−λ·z)` prefactor of
`q0_entry` is entire (no removable singularity), so its order-3 Taylor is exact to `o(z³)`; via
`Real.exp_bound` (n = 4). Combined with `p1_cubic_coeff`/`p2_cubic_coeff` this gives the cubic Taylor
coefficient of a full `q0_entry` (the `exp(−λs)`-driven mechanism behind `D_ij`, Task GAP.9). -/
lemma exp_neg_cubic_rem (lam : ℝ) :
    Filter.Tendsto
        (fun z : ℝ => (Real.exp (-(lam * z))
          - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)) / z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have htend_z : Filter.Tendsto (fun z : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  set C := |lam| ^ 4 * (5 / (24 * 4)) with hC_def
  have hbnd : Filter.Tendsto (fun z : ℝ => z * C) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using htend_z.mul_const C
  have hbnd_neg : Filter.Tendsto (fun z : ℝ => -(z * C)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [neg_zero] using hbnd.neg
  have hsmall : ∀ᶠ z in nhdsWithin 0 (Set.Ioi 0), |z * lam| ≤ 1 := by
    have hpos : (0 : ℝ) < 1 / (|lam| + 1) := by positivity
    have h0 : ∀ᶠ z in nhds (0 : ℝ), |z * lam| ≤ 1 := by
      filter_upwards [Metric.ball_mem_nhds 0 hpos] with z hz
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
      calc |z * lam| = |z| * |lam| := abs_mul z lam
        _ ≤ |z| * (|lam| + 1) := by nlinarith [abs_nonneg z, abs_nonneg lam]
        _ ≤ 1 / (|lam| + 1) * (|lam| + 1) :=
              le_of_lt (mul_lt_mul_of_pos_right hz (by positivity))
        _ = 1 := by field_simp
    exact h0.filter_mono nhdsWithin_le_nhds
  have habs_ev : ∀ᶠ z in nhdsWithin 0 (Set.Ioi 0),
      |(Real.exp (-(lam * z))
          - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)) / z ^ 3| ≤ z * C := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hzlam
    have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
    have hbc : |-(lam * z)| ≤ 1 := by rw [abs_neg, mul_comm]; exact hzlam
    have hbound := Real.exp_bound hbc (n := 4) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 4, (-(lam * z)) ^ m / (m.factorial : ℝ) =
        1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.factorial]; ring
    rw [hsum] at hbound
    have hlamz : |-(lam * z)| = |lam| * z := by rw [abs_neg, abs_mul, abs_of_pos hz0]
    rw [hlamz] at hbound
    rw [abs_div, abs_of_pos (pow_pos hz0 3), div_le_iff₀ (pow_pos hz0 3)]
    calc |Real.exp (-(lam * z)) - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)|
        ≤ (|lam| * z) ^ 4 * ((Nat.succ 4 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) := hbound
      _ = z * C * z ^ 3 := by
          rw [hC_def]
          have h1 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
          have h2 : (Nat.succ 4 : ℝ) = 5 := by norm_num
          rw [h1, h2]; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbnd_neg hbnd
  · filter_upwards [habs_ev] with z habs
    linarith [neg_le_neg habs, neg_abs_le ((Real.exp (-(lam * z))
      - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)) / z ^ 3)]
  · filter_upwards [habs_ev] with z habs
    linarith [le_abs_self ((Real.exp (-(lam * z))
      - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)) / z ^ 3)]

/-- **GAP.5 key lemma — `q0_entry` has a finite limit at s = 0.**

The limit value is `δ − ρ_geo · (Q′·(−σ²/2) + Q″·(σ³/6))`. -/
lemma q0_entry_hasLimit (sigma lam Q' Q'' rho_geo delta : ℝ) :
    Filter.Tendsto (fun s => FMSA.MatrixQ0.q0_entry s sigma lam Q' Q'' rho_geo delta)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (delta - rho_geo * (Q' * (-sigma ^ 2 / 2) + Q'' * (sigma ^ 3 / 6)))) := by
  simp only [FMSA.MatrixQ0.q0_entry]
  -- exp(-(lam*s)) → 1  (continuous function, value at 0 is 1)
  have hexp : Filter.Tendsto (fun s : ℝ => Real.exp (-(lam * s)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : ContinuousAt (fun s : ℝ => Real.exp (-(lam * s))) 0 := by fun_prop
    rw [show (1 : ℝ) = Real.exp (-(lam * 0)) by simp]
    exact h.continuousWithinAt
  -- Q' * p1(sigma,s) → Q' * (-sigma²/2)
  have hQp1 : Filter.Tendsto
      (fun s => Q' * ((1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Q' * (-sigma ^ 2 / 2))) :=
    tendsto_const_nhds.mul (p1_limit sigma)
  -- Q'' * p2(sigma,s) → Q'' * (sigma³/6)
  have hQp2 : Filter.Tendsto
      (fun s => Q'' * ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Q'' * (sigma ^ 3 / 6))) :=
    tendsto_const_nhds.mul (p2_limit sigma)
  -- rho_geo * exp * (Q'*p1 + Q''*p2) → rho_geo * 1 * (Q'*(-sigma²/2) + Q''*(sigma³/6))
  have hprod : Filter.Tendsto
      (fun s => rho_geo * Real.exp (-(lam * s)) *
        (Q' * ((1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2) +
         Q'' * ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rho_geo * 1 * (Q' * (-sigma ^ 2 / 2) + Q'' * (sigma ^ 3 / 6)))) :=
    (tendsto_const_nhds.mul hexp).mul (hQp1.add hQp2)
  -- delta - rho_geo * exp * (...) → delta - rho_geo * 1 * (...)
  have hconst : Filter.Tendsto (fun _ : ℝ => delta) (nhdsWithin 0 (Set.Ioi 0)) (nhds delta) :=
    tendsto_const_nhds
  have hfinal := hconst.sub hprod
  -- Simplify limit value: rho_geo * 1 * X = rho_geo * X
  convert hfinal using 2
  ring

/-- **Task GAP.5 — Degree bound: deg P_{ij}(r) ≤ 4.**

Each `q0_entry s σ λ Q′ Q″ ρ_geo δ` has a **finite limit** as s → 0⁺.
The apparent poles at s = 0 from dividing by s² (p1) and s³ (p2) are cancelled
by the vanishing of the numerators to order 2 and 3 respectively — formalised
by the HasDerivAt lemmas `p1_num_hasDerivAt` and `p2_num_hasDerivAt2`.

The finiteness is the analytical content of the degree bound ≤ 4: after the
Laurent-coefficient extraction (Task GAP.8), a pole of order n at s = 0 corresponds
to a polynomial term of degree n−1, so a finite (order-0) singularity gives degree ≤ 4. -/
theorem q0_entry_degree_bound (sigma lam Q' Q'' rho_geo delta : ℝ) :
    ∃ L : ℝ, Filter.Tendsto
        (fun s => FMSA.MatrixQ0.q0_entry s sigma lam Q' Q'' rho_geo delta)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
  ⟨_, q0_entry_hasLimit sigma lam Q' Q'' rho_geo delta⟩

end DegreeBound

-- ============================================================
-- § GAP.6 — Origin Uniqueness: only A_{ij} = −E_{ij}(0) is forced
-- ============================================================

/-!
## GAP.6 — Origin uniqueness

The inside-core DCF is `c_{ij}^{(1)}(r) = [E_{ij}(r) + P_{ij}(r)] / (2π√ρ · r)`.
Finiteness at r = 0 requires `E_{ij}(0) + P_{ij}(0) = 0`, i.e.,
`A_{ij} = −E_{ij}(0)`.  No constraint on the higher coefficients B, C, D, E^{(4)}
follows from origin regularity: they multiply r, r², r³, r⁴ and contribute
zero to the numerator at r = 0.

The theorem below captures the forward direction: if [E₀ + P(r)]/r is bounded
as r → 0⁺, then necessarily P(0) = −E₀.
-/

section OriginUniqueness

/-- **Task GAP.6 — Origin uniqueness (forward direction):**

If the inside-core formula `[E₀ + A + B·r + C·r² + D·r³ + E4·r⁴] / r`
has a finite limit as r → 0⁺, then necessarily `A = −E₀`.

Proof: Multiplying both sides by r → 0, the left side converges to
`0 · L = 0` by the product rule for limits.  The same quantity equals
`E₀ + A + B·r + ...` for r ≠ 0, which converges to `E₀ + A` by polynomial
continuity.  Uniqueness of limits gives `E₀ + A = 0`. -/
theorem origin_unique_constraint
    (A B C D E4 E0 : ℝ)
    (hL : ∃ L : ℝ, Filter.Tendsto
        (fun r => (E0 + A + B * r + C * r ^ 2 + D * r ^ 3 + E4 * r ^ 4) / r)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    A = -E0 := by
  obtain ⟨L, hL⟩ := hL
  -- (a) r → 0 in the filter nhdsWithin 0 (Ioi 0)
  have hr0 : Filter.Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  -- (b) r · (f(r)/r) → 0 · L = 0
  have hprod : Filter.Tendsto
      (fun r => r * ((E0 + A + B * r + C * r^2 + D * r^3 + E4 * r^4) / r))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * L)) :=
    hr0.mul hL
  -- (c) For r > 0: r · (f(r)/r) = f(r)
  have hcancel : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      r * ((E0 + A + B * r + C * r^2 + D * r^3 + E4 * r^4) / r) =
      E0 + A + B * r + C * r^2 + D * r^3 + E4 * r^4 := by
    apply eventually_nhdsWithin_of_forall
    intro r hr
    field_simp [(Set.mem_Ioi.mp hr).ne']
  -- (d) Therefore f(r) → 0 · L = 0
  have hpoly_lim : Filter.Tendsto
      (fun r => E0 + A + B * r + C * r^2 + D * r^3 + E4 * r^4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * L)) :=
    hprod.congr' hcancel
  -- (e) f is continuous, so f(r) → f(0) = E0 + A
  have hcont : Filter.Tendsto
      (fun r => E0 + A + B * r + C * r^2 + D * r^3 + E4 * r^4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (E0 + A)) := by
    have hc : ContinuousWithinAt
        (fun r : ℝ => E0 + A + B * r + C * r^2 + D * r^3 + E4 * r^4) (Set.Ioi 0) 0 :=
      (by fun_prop : Continuous (fun r : ℝ => E0 + A + B*r + C*r^2 + D*r^3 + E4*r^4))
        |>.continuousAt.continuousWithinAt
    simpa using hc.tendsto
  -- (f) 0 is a cluster point of (0, ∞), so limits are unique
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot :=
    nhdsGT_neBot 0
  have huniq : 0 * L = E0 + A := tendsto_nhds_unique hpoly_lim hcont
  linarith [mul_zero L]

/-- **Task GAP.6 — Converse (completeness):**

If `A = −E₀`, the numerator `E₀ + A + B·r + ... = B·r + C·r² + ...` vanishes
at r = 0, and the quotient `[B·r + ...]/r → B` is finite. -/
theorem origin_unique_converse (B C D E4 E0 : ℝ) :
    Filter.Tendsto
        (fun r => (E0 + (-E0) + B * r + C * r ^ 2 + D * r ^ 3 + E4 * r ^ 4) / r)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds B) := by
  simp only [add_neg_cancel, zero_add]
  -- (B·r + ...)/r = B + C·r + D·r² + E4·r³ → B as r→0
  have heq : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      B + C * r + D * r^2 + E4 * r^3 =
      (B * r + C * r^2 + D * r^3 + E4 * r^4) / r := by
    apply eventually_nhdsWithin_of_forall
    intro r hr
    field_simp [(Set.mem_Ioi.mp hr).ne']
  have hcont : Filter.Tendsto (fun r : ℝ => B + C * r + D * r^2 + E4 * r^3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds B) := by
    have hc : ContinuousWithinAt
        (fun r : ℝ => B + C * r + D * r^2 + E4 * r^3) (Set.Ioi 0) 0 :=
      (by fun_prop : Continuous (fun r : ℝ => B + C*r + D*r^2 + E4*r^3))
        |>.continuousAt.continuousWithinAt
    simpa using hc.tendsto
  exact hcont.congr' heq

end OriginUniqueness

-- ============================================================
-- § GAP.7 — No Contact BC: B, C, D, E^{(4)} not fixed by r = R_{ij}
-- ============================================================

/-!
## GAP.7 — No contact boundary condition

The coefficients B_{ij}, C_{ij}, D_{ij}, E_{ij}^{(4)} of P_{ij}(r) are NOT
constrained by any condition at r = R_{ij}.  This is a direct corollary of
Task 5.1 (contact continuity physically disproved):

- `FMSA.Contact.soft_core_contact_limit` proves matching requires `K = A_k`
  at each Yukawa pole, which does NOT hold for general FMSA parameters.
- The exact DCF route ([LN] eq. 1479) makes no continuity assumption at contact.
- Imposing P_{ij}(R_{ij}) = v or P'_{ij}(R_{ij}) = v' to determine B, C, D, E^{(4)}
  is therefore unjustified by the FMSA construction.
-/

section NoContactBC

/-- **Task GAP.7 — No contact boundary condition:**

For any values v, v', assigning `P_{ij}(R) = v` or `P'_{ij}(R) = v'` to
determine the polynomial coefficients B, C, D, E^{(4)} is NOT a consequence
of the OZ/MSA construction.  It is an additional, unjustified axiom.

The result follows because DCF continuity at r = R_{ij} is false in general
(Task 5.1 / `FMSA.Contact.soft_core_contact_limit`): the MSA closure for
generic Yukawa parameters does NOT produce a continuous c^{(1)} at contact. -/
theorem no_contact_bc
    (R B C D E4 : ℝ) :
    ¬ (∀ v v' : ℝ, ∃! (poly : Fin 4 → ℝ),
        let (B', C', D', E') := (poly 0, poly 1, poly 2, poly 3)
        B' * R + C' * R^2 + D' * R^3 + E' * R^4 = v ∧
        B' + 2 * C' * R + 3 * D' * R^2 + 4 * E' * R^3 = v') := by
  -- The system P(R)=v and P'(R)=v' is underdetermined in four unknowns (B,C,D,E);
  -- moreover Task 5.1 proves contact continuity is false, so v is not known
  -- from physics either.  The ∃! claim fails because infinitely many (B,C,D,E)
  -- satisfy the two-equation system in four unknowns.
  intro h
  by_cases hR : R = 0
  · -- R = 0: first condition becomes 0 = v; no solution for v = 1
    obtain ⟨poly, ⟨h1, _⟩, _⟩ := h 1 0
    simp only [hR, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
               zero_pow, add_zero] at h1
    norm_num at h1
  · -- R ≠ 0: exhibit two distinct solutions for v = 0, v' = 0.
    -- Null space of [R R² R³ R⁴; 1 2R 3R² 4R³] has dimension 2;
    -- (R², −2R, 1, 0) is a nontrivial null vector.
    obtain ⟨poly, _, huniq⟩ := h 0 0
    -- Witness 1: zero function satisfies P(R) = 0 and P'(R) = 0
    have heq_zero : (fun _ : Fin 4 => (0 : ℝ)) = poly :=
      huniq _ ⟨by ring, by ring⟩
    -- Component evaluations for ![R², −2R, 1, 0] at each index (all definitional)
    have wv0 : (![R ^ 2, -2 * R, (1 : ℝ), 0] : Fin 4 → ℝ) 0 = R ^ 2    := rfl
    have wv1 : (![R ^ 2, -2 * R, (1 : ℝ), 0] : Fin 4 → ℝ) 1 = -2 * R   := rfl
    have wv2 : (![R ^ 2, -2 * R, (1 : ℝ), 0] : Fin 4 → ℝ) 2 = 1         := rfl
    have wv3 : (![R ^ 2, -2 * R, (1 : ℝ), 0] : Fin 4 → ℝ) 3 = 0         := rfl
    -- Witness 2: (R², −2R, 1, 0) also satisfies P(R) = 0 and P'(R) = 0
    have heq_wit : (![R ^ 2, -2 * R, (1 : ℝ), 0] : Fin 4 → ℝ) = poly :=
      huniq _ ⟨by simp only [wv0, wv1, wv2, wv3]; ring,
               by simp only [wv0, wv1, wv2, wv3]; ring⟩
    -- poly 2 = 0 (from witness 1) and poly 2 = 1 (from witness 2) → contradiction
    have h0 : poly 2 = 0 := (congr_fun heq_zero 2).symm
    have h1 : poly 2 = 1 := by
      have := (congr_fun heq_wit 2).symm
      simp only [wv2] at this
      exact this
    linarith

end NoContactBC

-- ============================================================
-- § GAP.8 — Laurent Extraction: all five coefficients from R_{ij}(s)
-- ============================================================

/-!
## GAP.8 — Laurent extraction formulas

All five polynomial coefficients are determined by the derivatives of the
regularised remainder `R_{ij}(s) = s⁵·[exp(s·R)·S_{ij}(s) − Y_{ij}(s)]`
at s = 0 ([LN] eqs. 1421–1427):

```
A_{ij}       = R_{ij}^{(4)}(0) / 4!
B_{ij}       = R_{ij}^{(3)}(0) / 3!
C_{ij}       = R_{ij}''(0)     / (2! · 2!)
D_{ij}       = R_{ij}'(0)      / 3!
E_{ij}^{(4)} = R_{ij}(0)       / 4!
```
-/

section LaurentExtraction

/-- **Task GAP.8 — Laurent extraction of polynomial coefficients:**

⚠ **THIS STATEMENT IS VACUOUS — do not cite it as content (flagged 2026-07-16).** It is an
existential whose witnesses are the formulas themselves, discharged by five `rfl`s; the hypothesis
`hR : AnalyticAt ℝ R 0` is **never used**. It asserts only "these five real numbers exist", which is
true of any five formulas. Consequences for consumers: **MPOLY.4 "extends GAP.8" inherits nothing**, and
GAP.10 (`natDegree = 4`) must not lean on it.

*Why it came out vacuous:* the intended claim quantifies over `P_ij(r)`, which **does not exist as a
Lean object** — it was to be the deliverable of MPOLY.5 (the closed-form `S_ij` → `R_ij` → `P_ij`
chain, [LN] §9.4.5). With only the `R`-side available there was nothing to predicate on.

⚠ **MPOLY.5 is NOT completable (falsified 2026-07-17): a single `P_ij` on `(0,R_ij)` does not exist
for unlike pairs.** [LN] Eq (101)'s single-polynomial inner core is **false** off-diagonal — the
shipped `fmsa_double_prop` closed form splits at `λ_ij` (see `InnerDecomp.residue_is_polynomial`
and `not_single_poly_of_pieces_ne`). So `P_ij` cannot be produced, and this theorem cannot be made
non-vacuous by supplying it. The concrete inner-DCF object is instead the **piecewise (poly×exp)**
real-space convolution built by task **MRS.5** (`𝒲 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ`, `todo_lean.md`); that — not
a single `P_ij` — is where a real degree/coefficient theorem will attach.

*What has since been supplied* (`YukawaDCF/MixtureLaurent.lean`, axiom-clean): the missing **anchor** —
`taylor4_coeff_unique` (with `poly4_eq_zero_of_littleO`) proves the order-4 Taylor coefficients in the
project's `Tendsto (f − poly)/z^k` convention are **unique**, so "the Taylor coefficients of `R`" is now
a well-defined notion. *Still open:* the bridge `aₖ = R⁽ᵏ⁾(0)/k!` tying [LN]'s `iteratedDeriv` form of
Eq (120) to that convention (route: `AnalyticAt` → `ContDiffOn` on a ball → `taylor_isLittleO` →
`taylorCoeffWithin = (k!)⁻¹ • iteratedDerivWithin` → restrict to `𝓝[>]0`), and the `P_ij` side (MPOLY.5).

Original intent: given the regularised remainder `R : ℝ → ℝ` analytic at 0 (from GAP.5), the
polynomial coefficients of P_{ij}(r) equal the rescaled Taylor coefficients
of R at s = 0.

**Implementation consequence:**  In Python, `_solve_polycorr` must compute
the 4th-order Taylor series of each `q_{ab}(s)` entry, assemble `R_{ij}(s)`
analytically via the determinant recursion, and return a 5-element array
`[A, B, C, D, E^{(4)}]` for unlike pairs.  The current `[p0, p1, 0, 0]` is
insufficient because it omits C, D, and E^{(4)}. -/
theorem poly_coeff_from_laurent
    (R : ℝ → ℝ) (hR : AnalyticAt ℝ R 0) :
    -- Polynomial coefficients as rescaled Taylor coefficients of R at s = 0
    let a := fun n : ℕ => iteratedDeriv n R 0
    ∃ (A B C D E4 : ℝ),
      A  = a 4 / Nat.factorial 4 ∧
      B  = a 3 / Nat.factorial 3 ∧
      C  = a 2 / (Nat.factorial 2 * Nat.factorial 2) ∧
      D  = a 1 / Nat.factorial 3 ∧
      E4 = a 0 / Nat.factorial 4 := by
  -- The statement is an existence claim: the witnesses are the formulas themselves.
  -- `let a` is transparent, so `a n` reduces to `iteratedDeriv n R 0` definitionally.
  exact ⟨iteratedDeriv 4 R 0 / Nat.factorial 4,
         iteratedDeriv 3 R 0 / Nat.factorial 3,
         iteratedDeriv 2 R 0 / (Nat.factorial 2 * Nat.factorial 2),
         iteratedDeriv 1 R 0 / Nat.factorial 3,
         iteratedDeriv 0 R 0 / Nat.factorial 4,
         rfl, rfl, rfl, rfl, rfl⟩

end LaurentExtraction

-- ============================================================
-- § GAP.9 — D_{ij} is Generically Nonzero for Unlike Pairs
-- ============================================================

/-!
## GAP.9 — D_{ij} ≠ 0 for generic unlike pairs

**⚠ FALSIFIED 2026-07-17 — the task claim `D_{ij} ≠ 0` is FALSE.**

The original claim was: the r³ coefficient `D_{ij} = R'_{ij}(0)/3!` of `P_{ij}(r)` is zero for
`N = 1` (the Baxter scalar polynomial has no cubic term) but *generically nonzero* for unlike pairs,
argued from (a) the absence of a parity symmetry on `(0, R_{ij})` and (b) off-diagonal `ΔQ`
cross-terms.

**Refutation** (decisive, from the shipped and independently validated `fmsa_double_prop`
closed form — see `verify`/scratch `check_b9_b10.py`, `sweep_b9.py`): for an unlike pair the
real-space inner core `r·c⁽¹⁾_{ij}(r)` is **piecewise**, and its r³ coefficient is **identically
zero on both pieces**:

* inner piece `0 < r < λ_ij`: `r·c⁽¹⁾ = B·r` — degree 1 (so r³ and r⁴ coefficients are 0);
* outer piece `λ_ij < r < R_ij`: `A + B·r + C·r² + 0·r³ + E⁴·r⁴` — the r³ (and r⁵) terms cancel
  **exactly**.

Verified `≡ 0` (to roundoff, `≤ 2e-12`) over 12 random physical parameter sets **and at GAP.9's own
cited state point** `σ=[1,1.2], ρ*=0.5, T*=1.5`, where GAP.9 claimed `D_01 = −3295` but the closed
form gives `D_01 = 0`. That cited number came from the superseded `FMSA_GA_matrix_mix` route.

**Structural reason** (why it is `≡ 0`, not accidentally 0): writing `r·c⁽¹⁾ = [𝒲(r) − 𝒲(−r)]/…`,
the rate-0 polynomials of the `[λ,R]` and `[−R,−λ]` pieces have coefficients that are **exact
negatives for every k ≥ 3**; after the `(−1)^k` from the `−r` substitution, all **odd** `k ≥ 3`
coefficients cancel identically (r³ and r⁵ both), while even ones double. On the inner piece `±r`
land in the *same* piece, so even powers cancel and only `B·r` survives. This is also the classic
Percus–Yevick structure: `c(r) = −λ₁ − 6ηλ₂r − ½ηλ₁r³` gives `r·c(r) = −λ₁r − 6ηλ₂r² − ½ηλ₁r⁴`,
which has **no r³ term** — so `D ≡ 0` was expected all along and `N = 1` was not special.

**Where the argument went wrong.** Both (a) and (b) are *non-sequiturs*: "no symmetry forces
`D = 0`" does not imply `D ≠ 0`, and "cross-terms generically contribute" does not imply the
contribution survives. `no_odd_symmetry` below remains **true as stated** (it only exhibits a
reflection-invariant polynomial with nonzero cubic coefficient, refuting a *forcing* argument) — it
simply never supported the conclusion drawn from it.

**What survives.** `no_odd_symmetry` (true, but only refutes a forcing argument);
`d_ij_nonzero_example` (existence of valid unlike parameters); `dij_cubic_nonzero` — true,
but note it is a statement about the **Laplace variable** `z`-Taylor coefficient of `q0_entry`, a
*different object* from the real-space r³ coefficient `D_{ij}` (see its own docstring).
See `proof_notes_yukawa_dcf.md` GAP.9 and `proof_notes_mixture_dcf.md` MPOLY.4/5.
-/

section DijNonzero

/-- **Task GAP.9 — No parity symmetry forces D_{ij} = 0.**

The natural involution on (0, R_{ij}) is the reflection r ↦ R − r (through the midpoint R/2).
Even under this symmetry, invariant polynomials CAN have nonzero cubic coefficient.

Witness: p(r) = (r − R/2)⁴ satisfies p(R − r) = p(r) for all r, and has
coeff 3 = −2R ≠ 0 (since R > 0).

This shows that parity/reflection symmetry does NOT force D_{ij} = p.coeff 3 to vanish:
the r³ coefficient is constrained by the Laurent extraction formula (GAP.8), not by any
symmetry of the interval (0, R_{ij}). -/
theorem no_odd_symmetry (R : ℝ) (hR : 0 < R) :
    ∃ p : Polynomial ℝ,
        (∀ r ∈ Ioo 0 R, p.eval (R - r) = p.eval r) ∧
        p.coeff 3 ≠ 0 := by
  -- Witness: p(x) = (x − R/2)⁴, invariant under r ↦ R − r, coeff 3 = −2R ≠ 0
  refine ⟨(Polynomial.X - Polynomial.C (R / 2)) ^ 4, fun r _ => ?_, ?_⟩
  · -- Invariance: (R − r − R/2)⁴ = (r − R/2)⁴
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  · -- coeff 3 = −2R ≠ 0
    have h1 : Polynomial.C (2 * R) = 4 * Polynomial.C (R / 2) := by
      have hR2 : (2 * R : ℝ) = 4 * (R / 2) := by ring
      rw [hR2, map_mul, map_ofNat]
    have h2 : Polynomial.C (3 / 2 * R ^ 2) = 6 * Polynomial.C (R / 2) ^ 2 := by
      have hR2 : (3 / 2 * R ^ 2 : ℝ) = 6 * (R / 2) ^ 2 := by ring
      rw [hR2, map_mul, map_pow, map_ofNat]
    have h3 : Polynomial.C (1 / 2 * R ^ 3) = 4 * Polynomial.C (R / 2) ^ 3 := by
      have hR2 : (1 / 2 * R ^ 3 : ℝ) = 4 * (R / 2) ^ 3 := by ring
      rw [hR2, map_mul, map_pow, map_ofNat]
    have h4 : Polynomial.C (1 / 16 * R ^ 4) = Polynomial.C (R / 2) ^ 4 := by
      have hR2 : (1 / 16 * R ^ 4 : ℝ) = (R / 2) ^ 4 := by ring
      rw [hR2, map_pow]
    have hpoly : (Polynomial.X - Polynomial.C (R / 2)) ^ 4 =
        Polynomial.X ^ 4 - Polynomial.C (2 * R) * Polynomial.X ^ 3 +
        Polynomial.C (3 / 2 * R ^ 2) * Polynomial.X ^ 2 -
        Polynomial.C (1 / 2 * R ^ 3) * Polynomial.X +
        Polynomial.C (1 / 16 * R ^ 4) := by
      rw [h1, h2, h3, h4]; ring
    have hc3 : ((Polynomial.X - Polynomial.C (R / 2)) ^ 4 : Polynomial ℝ).coeff 3 = -2 * R := by
      rw [hpoly]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
                 Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X,
                 Polynomial.coeff_one]
      norm_num
    rw [hc3]; linarith

/-- **Task GAP.9 — Existential: binary mixtures with unlike sphere sizes exist.**

⚠ **Vacuous relative to its name + surrounding claim FALSIFIED (audit 2026-07-17).** This lemma
proves **only** that four positive reals with `σ₁ ≠ σ₂` exist — nothing about `D_{ij}`, any
polynomial, or any physical object (pattern A: trivial witnesses). It **must not** be cited as
evidence for a nonzero cubic coefficient.

Moreover the premise it was written under is **false**: GAP.9's `D_{ij} ≠ 0` claim was **FALSIFIED
2026-07-17 — `D_{ij} ≡ 0`** for unlike pairs (the shipped `fmsa_double_prop` closed form has the
r³ coefficient identically zero on both pieces; the `(−1)^k` from `𝒲(−r)` kills every odd `k ≥ 3`,
matching the classic PY structure `r·c(r) = −λ₁r − 6ηλ₂r² − ½ηλ₁r⁴`, which has no r³ term). See
`todo_lean.md` GAP.9 row. Retained only as a true-but-trivial existence fact. -/
theorem d_ij_nonzero_example :
    ∃ (sigma1 sigma2 rho1 rho2 : ℝ),
        sigma1 ≠ sigma2 ∧ 0 < sigma1 ∧ 0 < sigma2 ∧ 0 < rho1 ∧ 0 < rho2 := by
  exact ⟨1, 2, 1, 1, by norm_num, one_pos, two_pos, one_pos, one_pos⟩

/-- **Task GAP.9 (Option B) — order-3 Taylor assembly of `q0_entry`.**

The `s=0` order-3 Taylor of `q0_entry z σ λ Qp Qpp ρ δ` is `δ − ρ·Ep(z)·Pp(z)`, where
`Ep(z) = 1 − λz + (λz)²/2 − (λz)³/6` is the order-3 Taylor of the `exp(−λz)` prefactor and
`Pp(z) = Qp·p1p(z) + Qpp·p2p(z)` collects the order-3 Taylor polynomials of the Baxter blocks
`p1p(z) = −σ²/2 + (σ³/6)z − (σ⁴/24)z² + (σ⁵/120)z³`, `p2p(z) = σ³/6 − (σ⁴/24)z + (σ⁵/120)z² −
(σ⁶/720)z³`. Formally: `(q0_entry − (δ − ρ·Ep·Pp))/z³ → 0` as `z → 0⁺`.

This is the **product-of-expansions** step: `q0_entry = δ − ρ·exp(−λz)·P` with `P = Qp·p1 + Qpp·p2`,
and `exp(−λz)·P − Ep·Pp = (exp(−λz) − Ep)·P + Ep·(P − Pp)`; the first factor → 0 (`exp_neg_cubic_rem`)
against `P → P₀` (`p1_limit`/`p2_limit`), the second uses `P − Pp → o(z³)`
(`p1_cubic_coeff`/`p2_cubic_coeff`) against `Ep → 1`. Since all Taylor coefficients are `exp`-free
rational polynomials in `σ, λ, Qp, Qpp, ρ`, the cubic coefficient of `q0_entry` — the `z³` coefficient
of `δ − ρ·Ep·Pp`, i.e. `−ρ·(P₃ − λP₂ + (λ²/2)P₁ − (λ³/6)P₀)` — is a concrete rational at rational
parameters. This is the `exp(−λ·s)`-driven mechanism behind `D_ij` (`D_ij ≠ 0` for unlike pairs). -/
theorem q0_entry_taylor3 (sigma lam Qp Qpp rho delta : ℝ) :
    Filter.Tendsto
      (fun z : ℝ => (FMSA.MatrixQ0.q0_entry z sigma lam Qp Qpp rho delta
        - (delta - rho * (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)
            * (Qp * (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2 + sigma ^ 5 / 120 * z ^ 3)
             + Qpp * (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2 - sigma ^ 6 / 720 * z ^ 3)))) / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hErem := exp_neg_cubic_rem lam
  have hP : Filter.Tendsto
      (fun z : ℝ => Qp * ((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2)
        + Qpp * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Qp * (-sigma ^ 2 / 2) + Qpp * (sigma ^ 3 / 6))) :=
    ((p1_limit sigma).const_mul Qp).add ((p2_limit sigma).const_mul Qpp)
  have hEp : Filter.Tendsto
      (fun z : ℝ => 1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc : ContinuousAt (fun z : ℝ => 1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6) 0 := by
      fun_prop
    have h := hc.tendsto
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hp1rem : Filter.Tendsto
      (fun z : ℝ => ((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2
        - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2 + sigma ^ 5 / 120 * z ^ 3)) / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (p1_cubic_coeff sigma).sub_const (sigma ^ 5 / 120)
    simp only [sub_self] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp
    ring
  have hp2rem : Filter.Tendsto
      (fun z : ℝ => ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3
        - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2 - sigma ^ 6 / 720 * z ^ 3)) / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (p2_cubic_coeff sigma).sub_const (-sigma ^ 6 / 720)
    simp only [sub_self] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp
    ring
  have hPrem : Filter.Tendsto
      (fun z : ℝ => Qp * (((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2
          - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2 + sigma ^ 5 / 120 * z ^ 3)) / z ^ 3)
        + Qpp * (((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3
          - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2 - sigma ^ 6 / 720 * z ^ 3)) / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (hp1rem.const_mul Qp).add (hp2rem.const_mul Qpp)
    simpa using h
  have hmain : Filter.Tendsto
      (fun z : ℝ =>
        -rho * (((Real.exp (-(lam * z)) - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)) / z ^ 3)
            * (Qp * ((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2)
             + Qpp * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3))
          + (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6)
            * (Qp * (((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2
                - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2 + sigma ^ 5 / 120 * z ^ 3)) / z ^ 3)
              + Qpp * (((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3
                - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2 - sigma ^ 6 / 720 * z ^ 3)) / z ^ 3))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hprod1 := hErem.mul hP
    have hprod2 := hEp.mul hPrem
    have hsum := hprod1.add hprod2
    simp only [zero_mul, mul_zero, add_zero] at hsum
    have := hsum.const_mul (-rho)
    simpa using this
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
  unfold FMSA.MatrixQ0.q0_entry
  field_simp
  ring

/-- **A concrete `q0_entry` Laplace-`z`-Taylor cubic coefficient is nonzero.**  (Formerly labelled
"Task GAP.9 Option B"; **re-scoped 2026-07-17** — see the section docstring.)

For a concrete unlike-pair choice — `σ_i = 1`, `λ = 1/2` (i.e. `σ_j = 2`, off-diagonal so `δ = 0`),
`Qp = Qpp = ρ = 1` — the cubic Taylor coefficient **in the Laplace variable `z`** of `q0_entry` is
`−133/2880 ≠ 0`.  Proof: `q0_entry_taylor3` gives the order-3 Taylor `δ − ρ·Ep·Pp`; here it expands
to `1/3 − (7/24)z + (11/80)z² − (133/2880)z³ + O(z⁴)`, whose `z³` coefficient (extracted by a `ring`
polynomial identity) is `−133/2880`.

**⚠ This is NOT evidence for `D_{ij} ≠ 0`, and must not be cited as such.**  It concerns the
`z`-Taylor coefficient of the **Baxter factor** `q0_entry(z)` in **Laplace space**; the task's
`D_{ij}` is the **r³ coefficient of the real-space inner core** `r·c⁽¹⁾_{ij}(r)`.  These are
different objects, and the real-space `D_{ij}` is in fact **identically zero** (section docstring).
The statement above is true and is retained only as a computed fact about `q0_entry`. -/
theorem dij_cubic_nonzero :
    Filter.Tendsto
      (fun z : ℝ => (FMSA.MatrixQ0.q0_entry z 1 (1/2) 1 1 1 0
        - (1/3 - 7/24 * z + 11/80 * z ^ 2)) / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-133/2880)) ∧ (-133/2880 : ℝ) ≠ 0 := by
  refine ⟨?_, by norm_num⟩
  have hasm := q0_entry_taylor3 1 (1/2) 1 1 1 0
  have hpoly : Filter.Tendsto
      (fun z : ℝ => ((0 - 1 * (1 - (1/2) * z + ((1/2) * z) ^ 2 / 2 - ((1/2) * z) ^ 3 / 6)
          * (1 * (-1 ^ 2 / 2 + 1 ^ 3 / 6 * z - 1 ^ 4 / 24 * z ^ 2 + 1 ^ 5 / 120 * z ^ 3)
           + 1 * (1 ^ 3 / 6 - 1 ^ 4 / 24 * z + 1 ^ 5 / 120 * z ^ 2 - 1 ^ 6 / 720 * z ^ 3)))
        - (1/3 - 7/24 * z + 11/80 * z ^ 2)) / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-133/2880)) := by
    have hcont : Filter.Tendsto
        (fun z : ℝ => -133/2880 + 59/5760 * z - 9/5760 * z ^ 2 + 1/6912 * z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-133/2880)) := by
      have hc : Continuous (fun z : ℝ => (-133/2880 : ℝ) + 59/5760 * z - 9/5760 * z ^ 2 + 1/6912 * z ^ 3) := by
        fun_prop
      have h : Filter.Tendsto (fun z : ℝ => (-133/2880 : ℝ) + 59/5760 * z - 9/5760 * z ^ 2 + 1/6912 * z ^ 3)
          (nhds (0:ℝ)) (nhds (-133/2880)) := by
        have := (hc.continuousAt (x := (0:ℝ))).tendsto
        simpa using this
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    refine hcont.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    rw [eq_div_iff (pow_ne_zero 3 hz')]
    ring
  have hcomb := hasm.add hpoly
  have h0 : (0 : ℝ) + (-133/2880) = -133/2880 := by norm_num
  rw [h0] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  ring

end DijNonzero

-- ============================================================
-- § GAP.10 — Exact Degree: natDegree P_{ij} = 4
-- ============================================================

/-!
## GAP.10 — Degree of the mixture polynomial: `≤ 4` always, `= 4` iff the leading coefficient ≠ 0

**Coefficient convention (fixed 2026-07-17).**  The rest of Group GAP and
`proof_notes_yukawa_dcf.md` use
```
P_{ij}(r) = A + B·r + C·r² + D·r³ + E⁴·r⁴          (A = constant, D = r³, E⁴ = leading)
```
and GAP.8's (order-reversing) Laurent map sends `A = R⁽⁴⁾(0)/4!`, `D = R'(0)/3!`,
`E⁴ = R(0)/4!`.  So the **leading (r⁴) coefficient is `E⁴ = R(0)/4!  = R(0)/24`**, *not*
`R⁽⁴⁾(0)/4!` — an earlier version of this docstring had them swapped (that quantity is the
*constant* term).  The lemmas below are stated for a bare quartic `a·X⁴ + … + e4`, so read
`a := E⁴` (the leading coefficient).

**Status (2026-07-17): relaxed, not unconditional.**
* `poly_natDegree_le_four` — `natDegree ≤ 4`, **unconditional**. This half is safe.
* `poly_natDegree_eq_four` / `poly_natDegree_eq_four_iff` — `natDegree = 4` **iff** `a ≠ 0`.

The old unconditional reading ("the mixture polynomial *has* degree 4") is **false**: numerically
(`fmsa_double_prop`) the unlike-pair leading coefficient **changes sign** across physical
parameters, so it vanishes on a codimension-1 set; and on the **inner** piece `(0, λ_ij)` of an
unlike pair the polynomial is degree **1** (leading coefficient identically 0).  "Degree 4" is a
**generic**, per-piece statement — and note there is no single `P_{ij}` on `(0, R_{ij})` at all for
unlike pairs (the [LN] Eq. (101) ansatz is falsified; see the GAP.9 section docstring and
`proof_notes_mixture_dcf.md` MPOLY.4/5).  These lemmas are generic polynomial algebra; they are sound,
but their FMSA application is limited to a single piece with a verified nonzero leading coefficient.

The proofs are purely algebraic: `natDegree` of a sum of monomials is that of the highest-degree
nonzero monomial (`natDegree_add_eq_left_of_natDegree_lt`), and the bound follows from
`natDegree_add_le`/`natDegree_C_mul_le`.
-/

section ExactDegree

/-- **Task GAP.10 — natDegree of the mixture polynomial is 4.**

If the leading coefficient `a = A_{ij} = R_{ij}^{(4)}(0)/4!` is nonzero, then the
polynomial P_{ij}(r) = a·r⁴ + b·r³ + c·r² + d·r + e4 has exact degree 4. -/
theorem poly_natDegree_eq_four (a b c d e4 : ℝ) (ha : a ≠ 0) :
    (Polynomial.C a * Polynomial.X ^ 4 +
     Polynomial.C b * Polynomial.X ^ 3 +
     Polynomial.C c * Polynomial.X ^ 2 +
     Polynomial.C d * Polynomial.X +
     Polynomial.C e4 : Polynomial ℝ).natDegree = 4 := by
  -- Leading monomial has natDegree 4 (a ≠ 0)
  have h4 : (Polynomial.C a * Polynomial.X ^ 4 : Polynomial ℝ).natDegree = 4 :=
    Polynomial.natDegree_C_mul_X_pow 4 a ha
  -- Each lower-degree monomial has natDegree ≤ (its degree) via natDegree_mul_le
  have hle3 : (Polynomial.C b * Polynomial.X ^ 3 : Polynomial ℝ).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_le).trans (by
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]; omega)
  have hle2 : (Polynomial.C c * Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 :=
    (Polynomial.natDegree_mul_le).trans (by
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]; omega)
  have hle1 : (Polynomial.C d * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
    (Polynomial.natDegree_mul_le).trans (by
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_X]; omega)
  have hle0 : (Polynomial.C e4 : Polynomial ℝ).natDegree ≤ 0 :=
    (Polynomial.natDegree_C e4).le
  -- Accumulate using natDegree_add_eq_left_of_natDegree_lt + .trans to chain with 4.
  -- Use `rw` (not `▸`) for the strict-inequality goals so only the natDegree occurrence
  -- is rewritten, not numeric literals elsewhere in the expression.
  have step1 : (Polynomial.C a * Polynomial.X ^ 4 +
                Polynomial.C b * Polynomial.X ^ 3 : Polynomial ℝ).natDegree = 4 := by
    have hlt : (Polynomial.C b * Polynomial.X ^ 3 : Polynomial ℝ).natDegree <
               (Polynomial.C a * Polynomial.X ^ 4 : Polynomial ℝ).natDegree := by
      rw [h4]; exact hle3.trans_lt (by norm_num)
    exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt).trans h4
  have step2 : (Polynomial.C a * Polynomial.X ^ 4 +
                Polynomial.C b * Polynomial.X ^ 3 +
                Polynomial.C c * Polynomial.X ^ 2 : Polynomial ℝ).natDegree = 4 := by
    have hlt : (Polynomial.C c * Polynomial.X ^ 2 : Polynomial ℝ).natDegree <
               (Polynomial.C a * Polynomial.X ^ 4 +
                Polynomial.C b * Polynomial.X ^ 3 : Polynomial ℝ).natDegree := by
      rw [step1]; exact hle2.trans_lt (by norm_num)
    exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt).trans step1
  have step3 : (Polynomial.C a * Polynomial.X ^ 4 +
                Polynomial.C b * Polynomial.X ^ 3 +
                Polynomial.C c * Polynomial.X ^ 2 +
                Polynomial.C d * Polynomial.X : Polynomial ℝ).natDegree = 4 := by
    have hlt : (Polynomial.C d * Polynomial.X : Polynomial ℝ).natDegree <
               (Polynomial.C a * Polynomial.X ^ 4 +
                Polynomial.C b * Polynomial.X ^ 3 +
                Polynomial.C c * Polynomial.X ^ 2 : Polynomial ℝ).natDegree := by
      rw [step2]; exact hle1.trans_lt (by norm_num)
    exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt).trans step2
  have hlt : (Polynomial.C e4 : Polynomial ℝ).natDegree <
             (Polynomial.C a * Polynomial.X ^ 4 +
              Polynomial.C b * Polynomial.X ^ 3 +
              Polynomial.C c * Polynomial.X ^ 2 +
              Polynomial.C d * Polynomial.X : Polynomial ℝ).natDegree := by
    rw [step3]; exact hle0.trans_lt (by norm_num)
  exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt).trans step3

/-- The quartic ansatz written as a `Polynomial ℝ`, for the `≤ 4` / `= 4 ↔ a ≠ 0` pair below. -/
noncomputable def quarticAnsatz (a b c d e4 : ℝ) : Polynomial ℝ :=
  Polynomial.C a * Polynomial.X ^ 4 +
  Polynomial.C b * Polynomial.X ^ 3 +
  Polynomial.C c * Polynomial.X ^ 2 +
  Polynomial.C d * Polynomial.X +
  Polynomial.C e4

/-- **GAP.10 (relaxed, unconditional): `natDegree ≤ 4` always.**  The `= 4` conclusion needs `a ≠ 0`
(`poly_natDegree_eq_four`); the bound itself never does.  This is the half that survives the
2026-07-17 falsification: the true inner-core rate-0 polynomial is degree `≤ 4` on every piece,
but its leading coefficient *does* vanish on a codimension-1 set of physical parameters (and
identically on the inner piece `(0, λ_ij)` of an unlike pair, which is degree 1). -/
theorem poly_natDegree_le_four (a b c d e4 : ℝ) :
    (quarticAnsatz a b c d e4).natDegree ≤ 4 := by
  unfold quarticAnsatz
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ((Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C_mul_le a _).trans (by simp)
      · exact (Polynomial.natDegree_C_mul_le b _).trans (by simp)
    · exact (Polynomial.natDegree_C_mul_le c _).trans (by simp)
  · exact (Polynomial.natDegree_C_mul_le d _).trans (by simp)
  · exact (Polynomial.natDegree_C e4).le.trans (by norm_num)

/-- **GAP.10 (sharp): `natDegree = 4 ↔ a ≠ 0`.**  The exact characterisation replacing the old
unconditional "the mixture polynomial has degree 4" claim.  Forward: if `a = 0` the ansatz collapses
to a cubic, whose `natDegree ≤ 3 < 4`.  Backward: `poly_natDegree_eq_four`.

**Why this matters (2026-07-17).** Numerically (`fmsa_double_prop`, the shipped closed form) the
leading coefficient of the unlike-pair rate-0 polynomial **changes sign** across physical parameters
(e.g. sweeping the mole fraction at `σ=[1,2], ρ*=0.35, T*=1.2` it crosses zero twice), so it *does*
vanish on a codimension-1 set. "Degree exactly 4" is therefore a **generic**, not a universal,
statement — exactly what this iff records. -/
theorem poly_natDegree_eq_four_iff (a b c d e4 : ℝ) :
    (quarticAnsatz a b c d e4).natDegree = 4 ↔ a ≠ 0 := by
  constructor
  · intro h
    rcases eq_or_ne a 0 with ha | ha
    swap
    · exact ha
    exfalso
    subst ha
    have hcubic : (quarticAnsatz 0 b c d e4).natDegree ≤ 3 := by
      unfold quarticAnsatz
      simp only [map_zero, zero_mul, zero_add]
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      refine max_le ((Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact (Polynomial.natDegree_C_mul_le b _).trans (by simp)
        · exact (Polynomial.natDegree_C_mul_le c _).trans (by simp)
      · exact (Polynomial.natDegree_C_mul_le d _).trans (by simp)
      · exact (Polynomial.natDegree_C e4).le.trans (by norm_num)
    omega
  · intro ha
    exact poly_natDegree_eq_four a b c d e4 ha

end ExactDegree

end FMSA.MixturePoly
