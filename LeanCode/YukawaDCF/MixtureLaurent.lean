/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.B5MixturePoly

/-!
# Task MPOLY — Faithful inner-core polynomial coefficients via the `s=0` Laurent expansion

This file builds toward the **faithful** N=2 inner-core coefficient `D_ij = R'_ij(0)/6` ([LN] §9.4,
Eqs 106–120), where `R_ij(s) = s⁵·[e^{sRᵢⱼ}·S_ij(s) − Y_ij(s)]` is the regularised remainder whose
Taylor coefficients at `s=0` give `A,B,C,D,E⁴` (extending B.8's `b8_poly_coeff_from_laurent`).

**Tasks** (MPOLY umbrella, split into independent tasks — see `proof_notes_yukawa_wh.md`): **MPOLY.1**
(this file) — the **order-4 Taylor** of `q0_entry` (`q0_entry_taylor4`), the 5-coefficient structure
`q_ij(s)=q^[0]+…+q^[4]s⁴+O(s⁵)` ([LN] Eq 134), extending B.9's `q0_entry_taylor3` by one order.
**MPOLY.2** — the reciprocal-series recursion for `1/Δ_Q` (Eq 136–137). **MPOLY.3** — `Δ_Q =
q₁₁q₂₂−q₁₂q₂₁` + the inverse-entry series (Eq 130). **MPOLY.4** — the Laurent→coefficient extraction
machinery (Eq 105/120, extends B.8; the fallback endpoint). **MPOLY.5 (crux)** — the exact `S_01(s)`
from the transform equation (§9.4.5) ⇒ concrete `D_01`.

The Taylor-remainder lemmas mirror B.9's cubic ones (`p1_cubic_coeff`, `p2_cubic_coeff`,
`exp_neg_cubic_rem`), one order higher, via `Real.exp_bound`.
-/

set_option linter.style.longLine false

open Filter

namespace FMSA.MixtureLaurent

/-- Order-4 remainder of `exp(−λz)`: `(exp(−λz) − Σ_{k=0}^4 (−λz)^k/k!)/z⁴ → 0`. -/
lemma exp_neg_quartic_rem (lam : ℝ) :
    Filter.Tendsto
        (fun z : ℝ => (Real.exp (-(lam * z))
          - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)) / z ^ 4)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have htend_z : Filter.Tendsto (fun z : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  set C := |lam| ^ 5 * (6 / (120 * 5)) with hC_def
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
          - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)) / z ^ 4|
        ≤ z * C := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hzlam
    have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
    have hbc : |-(lam * z)| ≤ 1 := by rw [abs_neg, mul_comm]; exact hzlam
    have hbound := Real.exp_bound hbc (n := 5) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 5, (-(lam * z)) ^ m / (m.factorial : ℝ) =
        1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.factorial]; ring
    rw [hsum] at hbound
    have hlamz : |-(lam * z)| = |lam| * z := by rw [abs_neg, abs_mul, abs_of_pos hz0]
    rw [hlamz] at hbound
    rw [abs_div, abs_of_pos (pow_pos hz0 4), div_le_iff₀ (pow_pos hz0 4)]
    calc |Real.exp (-(lam * z))
            - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)|
        ≤ (|lam| * z) ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := hbound
      _ = z * C * z ^ 4 := by
          rw [hC_def]
          have h1 : (Nat.factorial 5 : ℝ) = 120 := by norm_num [Nat.factorial]
          have h2 : (Nat.succ 5 : ℝ) = 6 := by norm_num
          rw [h1, h2]; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbnd_neg hbnd
  · filter_upwards [habs_ev] with z habs
    linarith [neg_le_neg habs, neg_abs_le ((Real.exp (-(lam * z))
      - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)) / z ^ 4)]
  · filter_upwards [habs_ev] with z habs
    linarith [le_abs_self ((Real.exp (-(lam * z))
      - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)) / z ^ 4)]

/-- Order-4 Taylor coefficient of `p1(σ,s) = (1−sσ−e^{−sσ})/s²` at 0 is `−σ⁶/720`. -/
lemma p1_quartic_coeff (sigma : ℝ) :
    Filter.Tendsto
        (fun s : ℝ => ((1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2
          - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * s - sigma ^ 4 / 24 * s ^ 2 + sigma ^ 5 / 120 * s ^ 3))
            / s ^ 4)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-sigma ^ 6 / 720)) := by
  have halg : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ((1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2
          - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * s - sigma ^ 4 / 24 * s ^ 2 + sigma ^ 5 / 120 * s ^ 3))
            / s ^ 4 =
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
    linarith [neg_le_neg habs, neg_abs_le ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720
        - Real.exp (-(s * sigma))) / s ^ 6)]
  · filter_upwards [habs_ev] with s habs
    linarith [le_abs_self ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720
        - Real.exp (-(s * sigma))) / s ^ 6)]

/-- Order-4 Taylor coefficient of `p2(σ,s) = (1−sσ+(sσ)²/2−e^{−sσ})/s³` at 0 is `σ⁷/5040`. -/
lemma p2_quartic_coeff (sigma : ℝ) :
    Filter.Tendsto
        (fun s : ℝ => ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3
          - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * s + sigma ^ 5 / 120 * s ^ 2 - sigma ^ 6 / 720 * s ^ 3))
            / s ^ 4)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (sigma ^ 7 / 5040)) := by
  have halg : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3
          - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * s + sigma ^ 5 / 120 * s ^ 2 - sigma ^ 6 / 720 * s ^ 3))
            / s ^ 4 =
      sigma ^ 7 / 5040 +
        ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - (s * sigma) ^ 7 / 5040
          - Real.exp (-(s * sigma))) / s ^ 7) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := (Set.mem_Ioi.mp hs).ne'
    field_simp [hs']; ring
  suffices hrem : Filter.Tendsto
      (fun s : ℝ => (1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - (s * sigma) ^ 7 / 5040
          - Real.exp (-(s * sigma))) / s ^ 7)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
    have hlim := (tendsto_const_nhds (x := sigma ^ 7 / 5040)).add hrem
    simpa using hlim.congr' (halg.mono (fun s hs => hs.symm))
  have htend_s : Filter.Tendsto (fun s : ℝ => s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  set C := |sigma| ^ 8 * (9 / (40320 * 8)) with hC_def
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
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - (s * sigma) ^ 7 / 5040
          - Real.exp (-(s * sigma))) / s ^ 7| ≤ s * C := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hssigma
    have hs0 : (0 : ℝ) < s := Set.mem_Ioi.mp hs
    have hbc : |-(s * sigma)| ≤ 1 := by rwa [abs_neg]
    have hbound := Real.exp_bound hbc (n := 8) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 8, (-(s * sigma)) ^ m / (m.factorial : ℝ) =
        1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
          - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - (s * sigma) ^ 7 / 5040 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.factorial]; ring
    rw [hsum, abs_neg, abs_mul, abs_of_pos hs0] at hbound
    rw [abs_div, abs_of_pos (pow_pos hs0 7), div_le_iff₀ (pow_pos hs0 7)]
    calc |1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6 + (s * sigma) ^ 4 / 24
            - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - (s * sigma) ^ 7 / 5040
            - Real.exp (-(s * sigma))|
        = |Real.exp (-(s * sigma)) - (1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
            + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720
            - (s * sigma) ^ 7 / 5040)| :=
          abs_sub_comm _ _
      _ ≤ (s * |sigma|) ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := hbound
      _ = s * C * s ^ 7 := by
          rw [hC_def]
          have h1 : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
          have h2 : (Nat.succ 8 : ℝ) = 9 := by norm_num
          rw [h1, h2]; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbnd_neg hbnd
  · filter_upwards [habs_ev] with s habs
    linarith [neg_le_neg habs, neg_abs_le ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - (s * sigma) ^ 7 / 5040
        - Real.exp (-(s * sigma))) / s ^ 7)]
  · filter_upwards [habs_ev] with s habs
    linarith [le_abs_self ((1 - s * sigma + (s * sigma) ^ 2 / 2 - (s * sigma) ^ 3 / 6
      + (s * sigma) ^ 4 / 24 - (s * sigma) ^ 5 / 120 + (s * sigma) ^ 6 / 720 - (s * sigma) ^ 7 / 5040
        - Real.exp (-(s * sigma))) / s ^ 7)]

/-- **MPOLY.1 — order-4 Taylor assembly of `q0_entry`.** The `s=0` order-4 Taylor of
`q0_entry z σ λ Qp Qpp ρ δ` is `δ − ρ·Ep₄·Pp₄`, where `Ep₄` is the order-4 Taylor of `exp(−λz)` and
`Pp₄ = Qp·p1p₄ + Qpp·p2p₄` collects the order-4 Taylors of the Baxter blocks. Extends
`q0_entry_taylor3` (order 3) by one order — the fifth coefficient needed for the `Δ_Q`/`1/Δ_Q`
series (Eq 134) toward the faithful `D_ij`. -/
theorem q0_entry_taylor4 (sigma lam Qp Qpp rho delta : ℝ) :
    Filter.Tendsto
      (fun z : ℝ => (FMSA.MatrixQ0.q0_entry z sigma lam Qp Qpp rho delta
        - (delta - rho * (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)
            * (Qp * (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2
                + sigma ^ 5 / 120 * z ^ 3 - sigma ^ 6 / 720 * z ^ 4)
             + Qpp * (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2
                - sigma ^ 6 / 720 * z ^ 3 + sigma ^ 7 / 5040 * z ^ 4)))) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hErem := exp_neg_quartic_rem lam
  have hP : Filter.Tendsto
      (fun z : ℝ => Qp * ((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2)
        + Qpp * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Qp * (-sigma ^ 2 / 2) + Qpp * (sigma ^ 3 / 6))) :=
    ((FMSA.MixturePoly.b5_p1_limit sigma).const_mul Qp).add
      ((FMSA.MixturePoly.b5_p2_limit sigma).const_mul Qpp)
  have hEp : Filter.Tendsto
      (fun z : ℝ => 1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc : ContinuousAt (fun z : ℝ =>
        1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24) 0 := by fun_prop
    have h := hc.tendsto
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hp1rem : Filter.Tendsto
      (fun z : ℝ => ((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2
        - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2 + sigma ^ 5 / 120 * z ^ 3
          - sigma ^ 6 / 720 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (p1_quartic_coeff sigma).sub_const (-sigma ^ 6 / 720)
    simp only [sub_self] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp
    ring
  have hp2rem : Filter.Tendsto
      (fun z : ℝ => ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3
        - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2 - sigma ^ 6 / 720 * z ^ 3
          + sigma ^ 7 / 5040 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (p2_quartic_coeff sigma).sub_const (sigma ^ 7 / 5040)
    simp only [sub_self] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp
    ring
  have hPrem : Filter.Tendsto
      (fun z : ℝ => Qp * (((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2
          - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2 + sigma ^ 5 / 120 * z ^ 3
            - sigma ^ 6 / 720 * z ^ 4)) / z ^ 4)
        + Qpp * (((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3
          - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2 - sigma ^ 6 / 720 * z ^ 3
            + sigma ^ 7 / 5040 * z ^ 4)) / z ^ 4))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (hp1rem.const_mul Qp).add (hp2rem.const_mul Qpp)
    simpa using h
  have hmain : Filter.Tendsto
      (fun z : ℝ =>
        -rho * (((Real.exp (-(lam * z))
              - (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)) / z ^ 4)
            * (Qp * ((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2)
             + Qpp * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3))
          + (1 - lam * z + (lam * z) ^ 2 / 2 - (lam * z) ^ 3 / 6 + (lam * z) ^ 4 / 24)
            * (Qp * (((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2
                - (-sigma ^ 2 / 2 + sigma ^ 3 / 6 * z - sigma ^ 4 / 24 * z ^ 2
                  + sigma ^ 5 / 120 * z ^ 3 - sigma ^ 6 / 720 * z ^ 4)) / z ^ 4)
              + Qpp * (((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3
                - (sigma ^ 3 / 6 - sigma ^ 4 / 24 * z + sigma ^ 5 / 120 * z ^ 2
                  - sigma ^ 6 / 720 * z ^ 3 + sigma ^ 7 / 5040 * z ^ 4)) / z ^ 4))))
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

end FMSA.MixtureLaurent


