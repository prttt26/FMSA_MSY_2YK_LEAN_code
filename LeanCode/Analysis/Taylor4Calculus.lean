/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Fourth-order Taylor calculus for `ℝ → ℝ` germs at `0`

A little algebra of "`f` has quartic Taylor data `(a0,…,a4)` at `0`", meaning
`f r = a0 + a1 r + a2 r² + a3 r³ + a4 r⁴ + o(r⁴)`, closed under the ring operations and
reciprocal, plus the uniqueness of the coefficients.

Everything here is stated for **arbitrary** `f g : ℝ → ℝ` — no hard-sphere or Yukawa object
appears, which is why it lives in `Analysis/` (split out of `MixtureLaurent.lean` on 2026-07-19;
the `p1`/`p2`/`exp` Baxter-block Taylor family below was consolidated here from
`MixtureLaurent`/`MixturePolyCoeffs` across `MRS.9d`, 2026-07-27).

* `taylor4_mul` / `taylor4_sub` / `taylor4_neg` / `taylor4_recip` — the closure rules; `taylor4_recip`
  needs `d0 ≠ 0` and the reciprocal coefficients supplied as hypotheses.
* `taylor4_deltaQ` / `taylor4_inv_entry`-style assembly for a `2×2` determinant is left with its
  concrete consumer.
* `poly4_eq_zero_of_littleO` — a degree-`≤ 4` polynomial that is `o(r⁴)` has all coefficients zero;
  the engine behind `taylor4_coeff_unique`.
* The `p1`/`p2` Baxter-block Taylor family — removable-singularity limits and Taylor coefficients of
  `p1(σ,s) = (1−sσ−e^{−sσ})/s²` and `p2(σ,s) = (1−sσ+(sσ)²/2−e^{−sσ})/s³`, elementary functions of a
  free real `σ`: `p1_limit`/`p2_limit` (order 0), `p1_cubic_coeff`/`p2_cubic_coeff` (order 3),
  `p1_quartic_coeff`/`p2_quartic_coeff` (order 4); plus the `e^{−λr}` remainders
  `exp_neg_cubic_rem`/`exp_neg_quartic_rem`.
-/

set_option linter.style.longLine false

open Filter

namespace FMSA.Taylor4

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

/-- Order-4 Taylor data forces the `0⁺` limit to be the constant term. -/
lemma taylor4_tendsto_const (f : ℝ → ℝ) (a0 a1 a2 a3 a4 : ℝ)
    (hf : Filter.Tendsto
      (fun z : ℝ => (f z - (a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds a0) := by
  have hz4 : Filter.Tendsto (fun z : ℝ => z ^ 4) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun z : ℝ => z ^ 4) (nhds 0) (nhds 0) := by
      simpa using (continuous_pow 4).tendsto (0 : ℝ)
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have hP : Filter.Tendsto (fun z : ℝ => a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a0) := by
    have hc : Continuous (fun z : ℝ => a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4) := by
      fun_prop
    have h0 : Filter.Tendsto (fun z : ℝ => a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)
        (nhds 0) (nhds a0) := by simpa using hc.tendsto 0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have hdiff : Filter.Tendsto
      (fun z : ℝ => f z - (a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hmul := hf.mul hz4
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp
  have := hdiff.add hP
  simpa using this

/-- **MPOLY.2 — reciprocal-series recursion for `1/Δ_Q`** ([LN] Eqs 136–137). -/
theorem taylor4_recip (Δ : ℝ → ℝ) (d0 d1 d2 d3 d4 r0 r1 r2 r3 r4 : ℝ) (hd0 : d0 ≠ 0)
    (hΔ : Filter.Tendsto
      (fun z : ℝ => (Δ z - (d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hr0 : r0 = 1 / d0)
    (hr1 : r1 = -(1 / d0) * (d1 * r0))
    (hr2 : r2 = -(1 / d0) * (d1 * r1 + d2 * r0))
    (hr3 : r3 = -(1 / d0) * (d1 * r2 + d2 * r1 + d3 * r0))
    (hr4 : r4 = -(1 / d0) * (d1 * r3 + d2 * r2 + d3 * r1 + d4 * r0)) :
    Filter.Tendsto
      (fun z : ℝ => (1 / Δ z - (r0 + r1 * z + r2 * z ^ 2 + r3 * z ^ 3 + r4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- cleared convolution forms (Eq 137 with the `1/d0` cleared)
  have e0 : d0 * r0 = 1 := by rw [hr0]; field_simp
  have e1 : d0 * r1 + d1 * r0 = 0 := by rw [hr1]; field_simp; ring
  have e2 : d0 * r2 + d1 * r1 + d2 * r0 = 0 := by rw [hr2]; field_simp; ring
  have e3 : d0 * r3 + d1 * r2 + d2 * r1 + d3 * r0 = 0 := by rw [hr3]; field_simp; ring
  have e4 : d0 * r4 + d1 * r3 + d2 * r2 + d3 * r1 + d4 * r0 = 0 := by rw [hr4]; field_simp; ring
  -- the z^5-tail identity: 1 - P₄·Q₄ = z^5·(c5 + c6 z + c7 z² + c8 z³)
  have key : ∀ z : ℝ,
      1 - (d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)
          * (r0 + r1 * z + r2 * z ^ 2 + r3 * z ^ 3 + r4 * z ^ 4)
        = z ^ 5 * ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1))
                 + (-(d2 * r4 + d3 * r3 + d4 * r2)) * z
                 + (-(d3 * r4 + d4 * r3)) * z ^ 2
                 + (-(d4 * r4)) * z ^ 3) := by
    intro z
    linear_combination (-1 : ℝ) * e0 + (-z) * e1 + (-z ^ 2) * e2 + (-z ^ 3) * e3 + (-z ^ 4) * e4
  -- P₄ → d0
  have hP4 : Filter.Tendsto (fun z : ℝ => d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d0) := by
    have hc : Continuous (fun z : ℝ => d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4) := by
      fun_prop
    have h0 : Filter.Tendsto (fun z : ℝ => d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)
        (nhds 0) (nhds d0) := by simpa using hc.tendsto 0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  -- Q₄ → r0
  have hQ4 : Filter.Tendsto (fun z : ℝ => r0 + r1 * z + r2 * z ^ 2 + r3 * z ^ 3 + r4 * z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds r0) := by
    have hc : Continuous (fun z : ℝ => r0 + r1 * z + r2 * z ^ 2 + r3 * z ^ 3 + r4 * z ^ 4) := by
      fun_prop
    have h0 : Filter.Tendsto (fun z : ℝ => r0 + r1 * z + r2 * z ^ 2 + r3 * z ^ 3 + r4 * z ^ 4)
        (nhds 0) (nhds r0) := by simpa using hc.tendsto 0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have hz4 : Filter.Tendsto (fun z : ℝ => z ^ 4) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun z : ℝ => z ^ 4) (nhds 0) (nhds 0) := by
      simpa using (continuous_pow 4).tendsto (0:ℝ)
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  -- Δ → d0, hence 1/Δ → 1/d0
  have hdiff : Filter.Tendsto
      (fun z : ℝ => Δ z - (d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hmul := hΔ.mul hz4
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp
  have hΔlim : Filter.Tendsto Δ (nhdsWithin 0 (Set.Ioi 0)) (nhds d0) := by
    have := hdiff.add hP4
    simpa using this
  have hinv : Filter.Tendsto (fun z : ℝ => 1 / Δ z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / d0)) := by
    simpa [one_div] using hΔlim.inv₀ hd0
  have hΔne : ∀ᶠ z in nhdsWithin 0 (Set.Ioi 0), Δ z ≠ 0 :=
    hΔlim.eventually_ne hd0
  -- the assembled limit
  have hz1 : Filter.Tendsto (fun z : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have htail : Filter.Tendsto
      (fun z : ℝ => z * ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1))
                 + (-(d2 * r4 + d3 * r3 + d4 * r2)) * z
                 + (-(d3 * r4 + d4 * r3)) * z ^ 2
                 + (-(d4 * r4)) * z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun z : ℝ => ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1))
                 + (-(d2 * r4 + d3 * r3 + d4 * r2)) * z
                 + (-(d3 * r4 + d4 * r3)) * z ^ 2
                 + (-(d4 * r4)) * z ^ 3)) := by fun_prop
    have hG : Filter.Tendsto (fun z : ℝ => ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1))
                 + (-(d2 * r4 + d3 * r3 + d4 * r2)) * z
                 + (-(d3 * r4 + d4 * r3)) * z ^ 2
                 + (-(d4 * r4)) * z ^ 3))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1)))) := by
      have h0' : Filter.Tendsto (fun z : ℝ => ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1))
                 + (-(d2 * r4 + d3 * r3 + d4 * r2)) * z
                 + (-(d3 * r4 + d4 * r3)) * z ^ 2
                 + (-(d4 * r4)) * z ^ 3)) (nhds 0)
          (nhds ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1)))) := by
        simpa using hc.tendsto (0:ℝ)
      exact tendsto_nhdsWithin_of_tendsto_nhds h0'
    have := hz1.mul hG
    simpa using this
  have hmain : Filter.Tendsto
      (fun z : ℝ => (z * ((-(d1 * r4 + d2 * r3 + d3 * r2 + d4 * r1))
                 + (-(d2 * r4 + d3 * r3 + d4 * r2)) * z
                 + (-(d3 * r4 + d4 * r3)) * z ^ 2
                 + (-(d4 * r4)) * z ^ 3)
        - ((Δ z - (d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)) / z ^ 4)
            * (r0 + r1 * z + r2 * z ^ 2 + r3 * z ^ 3 + r4 * z ^ 4)) * (1 / Δ z))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h2 := hΔ.mul hQ4
    rw [zero_mul] at h2
    have h3 := (htail.sub h2).mul hinv
    simpa using h3
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hΔne] with z hz hΔz
  have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
  have hzne : z ≠ 0 := hz0.ne'
  have hk := key z
  field_simp
  linear_combination -hk


/-! ### MPOLY.3 — order-4 Taylor calculus, `Δ_Q`, and the inverse entry ([LN] Eqs 130/131/135) -/

/-- **Order-4 Cauchy product** ([LN] "ordinary series multiplication and collection"). -/
theorem taylor4_mul (f g : ℝ → ℝ) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (hf : Filter.Tendsto
      (fun z : ℝ => (f z - (a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hg : Filter.Tendsto
      (fun z : ℝ => (g z - (b0 + b1 * z + b2 * z ^ 2 + b3 * z ^ 3 + b4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto
      (fun z : ℝ => (f z * g z
        - (a0 * b0
         + (a0 * b1 + a1 * b0) * z
         + (a0 * b2 + a1 * b1 + a2 * b0) * z ^ 2
         + (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * z ^ 3
         + (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hgc : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds b0) :=
    taylor4_tendsto_const g b0 b1 b2 b3 b4 hg
  have hPf : Filter.Tendsto (fun z : ℝ => a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a0) := by
    have hc : Continuous (fun z : ℝ => a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4) := by
      fun_prop
    have h0 : Filter.Tendsto (fun z : ℝ => a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)
        (nhds 0) (nhds a0) := by simpa using hc.tendsto 0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have hz1 : Filter.Tendsto (fun z : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have htail : Filter.Tendsto
      (fun z : ℝ => z * ((a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
        + (a2 * b4 + a3 * b3 + a4 * b2) * z
        + (a3 * b4 + a4 * b3) * z ^ 2
        + (a4 * b4) * z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun z : ℝ => ((a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
        + (a2 * b4 + a3 * b3 + a4 * b2) * z
        + (a3 * b4 + a4 * b3) * z ^ 2
        + (a4 * b4) * z ^ 3)) := by fun_prop
    have hG : Filter.Tendsto (fun z : ℝ => ((a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
        + (a2 * b4 + a3 * b3 + a4 * b2) * z
        + (a3 * b4 + a4 * b3) * z ^ 2
        + (a4 * b4) * z ^ 3)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)) := by
      have h0 : Filter.Tendsto (fun z : ℝ => ((a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
          + (a2 * b4 + a3 * b3 + a4 * b2) * z
          + (a3 * b4 + a4 * b3) * z ^ 2
          + (a4 * b4) * z ^ 3)) (nhds 0)
          (nhds (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)) := by simpa using hc.tendsto 0
      exact tendsto_nhdsWithin_of_tendsto_nhds h0
    have := hz1.mul hG
    simpa using this
  have h1 := hf.mul hgc
  rw [zero_mul] at h1
  have h2 := hPf.mul hg
  rw [mul_zero] at h2
  have hsum := (h1.add h2).add htail
  rw [add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
  field_simp
  ring

/-- Order-4 Taylor of a difference (coefficientwise). -/
theorem taylor4_sub (f g : ℝ → ℝ) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (hf : Filter.Tendsto
      (fun z : ℝ => (f z - (a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hg : Filter.Tendsto
      (fun z : ℝ => (g z - (b0 + b1 * z + b2 * z ^ 2 + b3 * z ^ 3 + b4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto
      (fun z : ℝ => (f z - g z
        - ((a0 - b0) + (a1 - b1) * z + (a2 - b2) * z ^ 2 + (a3 - b3) * z ^ 3
           + (a4 - b4) * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hd := hf.sub hg
  rw [sub_zero] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
  field_simp
  ring

/-- Order-4 Taylor of a negation (coefficientwise). -/
theorem taylor4_neg (f : ℝ → ℝ) (a0 a1 a2 a3 a4 : ℝ)
    (hf : Filter.Tendsto
      (fun z : ℝ => (f z - (a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto
      (fun z : ℝ => (-(f z) - ((-a0) + (-a1) * z + (-a2) * z ^ 2 + (-a3) * z ^ 3
        + (-a4) * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hn := hf.neg
  rw [neg_zero] at hn
  refine hn.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
  field_simp
  ring

/-- **MPOLY.3 — `Δ_Q = q₀₀q₁₁ − q₀₁q₁₀` order-4 coefficients** ([LN] Eq 131/135). -/
theorem taylor4_deltaQ (q00 q01 q10 q11 : ℝ → ℝ)
    (a0 a1 a2 a3 a4 e0 e1 e2 e3 e4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : ℝ)
    (h00 : Filter.Tendsto
      (fun z : ℝ => (q00 z - (a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h11 : Filter.Tendsto
      (fun z : ℝ => (q11 z - (e0 + e1 * z + e2 * z ^ 2 + e3 * z ^ 3 + e4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h01 : Filter.Tendsto
      (fun z : ℝ => (q01 z - (b0 + b1 * z + b2 * z ^ 2 + b3 * z ^ 3 + b4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h10 : Filter.Tendsto
      (fun z : ℝ => (q10 z - (c0 + c1 * z + c2 * z ^ 2 + c3 * z ^ 3 + c4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto
      (fun z : ℝ => (q00 z * q11 z - q01 z * q10 z
        - ((a0 * e0 - b0 * c0)
         + ((a0 * e1 + a1 * e0) - (b0 * c1 + b1 * c0)) * z
         + ((a0 * e2 + a1 * e1 + a2 * e0) - (b0 * c2 + b1 * c1 + b2 * c0)) * z ^ 2
         + ((a0 * e3 + a1 * e2 + a2 * e1 + a3 * e0)
            - (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0)) * z ^ 3
         + ((a0 * e4 + a1 * e3 + a2 * e2 + a3 * e1 + a4 * e0)
            - (b0 * c4 + b1 * c3 + b2 * c2 + b3 * c1 + b4 * c0)) * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  taylor4_sub (fun z => q00 z * q11 z) (fun z => q01 z * q10 z)
    (a0 * e0) (a0 * e1 + a1 * e0) (a0 * e2 + a1 * e1 + a2 * e0)
    (a0 * e3 + a1 * e2 + a2 * e1 + a3 * e0) (a0 * e4 + a1 * e3 + a2 * e2 + a3 * e1 + a4 * e0)
    (b0 * c0) (b0 * c1 + b1 * c0) (b0 * c2 + b1 * c1 + b2 * c0)
    (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) (b0 * c4 + b1 * c3 + b2 * c2 + b3 * c1 + b4 * c0)
    (taylor4_mul q00 q11 a0 a1 a2 a3 a4 e0 e1 e2 e3 e4 h00 h11)
    (taylor4_mul q01 q10 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 h01 h10)

/-- A polynomial of degree ≤ 4 that is `o(z⁴)` at `0⁺` has all coefficients zero. -/
theorem poly4_eq_zero_of_littleO (d0 d1 d2 d3 d4 : ℝ)
    (h : Filter.Tendsto (fun z : ℝ => (d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ d3 = 0 ∧ d4 = 0 := by
  have hzp : ∀ n : ℕ, Filter.Tendsto (fun z : ℝ => z ^ n) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 ^ n)) := by
    intro n
    exact tendsto_nhdsWithin_of_tendsto_nhds ((continuous_pow n).tendsto 0)
  -- d0 = 0
  have hd0 : d0 = 0 := by
    have hpoly : Filter.Tendsto (fun z : ℝ => d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds d0) := by
      have hc : Continuous (fun z : ℝ => d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4) := by
        fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hc.tendsto 0)
    have hzero : Filter.Tendsto (fun z : ℝ => d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hm := h.mul (by simpa using hzp 4)
      rw [zero_mul] at hm
      refine hm.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
      field_simp
    exact tendsto_nhds_unique hpoly hzero
  subst hd0
  -- peel: (d1 z + d2 z² + d3 z³ + d4 z⁴)/z⁴ = (d1 + d2 z + d3 z² + d4 z³)/z³
  have h1 : Filter.Tendsto (fun z : ℝ => (d1 + d2 * z + d3 * z ^ 2 + d4 * z ^ 3) / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp; ring
  have hd1 : d1 = 0 := by
    have hpoly : Filter.Tendsto (fun z : ℝ => d1 + d2 * z + d3 * z ^ 2 + d4 * z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds d1) := by
      have hc : Continuous (fun z : ℝ => d1 + d2 * z + d3 * z ^ 2 + d4 * z ^ 3) := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hc.tendsto 0)
    have hzero : Filter.Tendsto (fun z : ℝ => d1 + d2 * z + d3 * z ^ 2 + d4 * z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hm := h1.mul (by simpa using hzp 3)
      rw [zero_mul] at hm
      refine hm.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
      field_simp
    exact tendsto_nhds_unique hpoly hzero
  subst hd1
  have h2 : Filter.Tendsto (fun z : ℝ => (d2 + d3 * z + d4 * z ^ 2) / z ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp; ring
  have hd2 : d2 = 0 := by
    have hpoly : Filter.Tendsto (fun z : ℝ => d2 + d3 * z + d4 * z ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds d2) := by
      have hc : Continuous (fun z : ℝ => d2 + d3 * z + d4 * z ^ 2) := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hc.tendsto 0)
    have hzero : Filter.Tendsto (fun z : ℝ => d2 + d3 * z + d4 * z ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hm := h2.mul (by simpa using hzp 2)
      rw [zero_mul] at hm
      refine hm.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
      field_simp
    exact tendsto_nhds_unique hpoly hzero
  subst hd2
  have h3 : Filter.Tendsto (fun z : ℝ => (d3 + d4 * z) / z ^ 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp; ring
  have hd3 : d3 = 0 := by
    have hpoly : Filter.Tendsto (fun z : ℝ => d3 + d4 * z)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds d3) := by
      have hc : Continuous (fun z : ℝ => d3 + d4 * z) := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hc.tendsto 0)
    have hzero : Filter.Tendsto (fun z : ℝ => d3 + d4 * z)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hm := h3.mul (by simpa using hzp 1)
      rw [zero_mul] at hm
      refine hm.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
      field_simp
    exact tendsto_nhds_unique hpoly hzero
  subst hd3
  have hd4 : d4 = 0 := by
    have hpoly : Filter.Tendsto (fun z : ℝ => d4) (nhdsWithin 0 (Set.Ioi 0)) (nhds d4) :=
      tendsto_const_nhds
    have hzero : Filter.Tendsto (fun z : ℝ => d4) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
      field_simp
      ring
    exact tendsto_nhds_unique hpoly hzero
  exact ⟨rfl, rfl, rfl, rfl, hd4⟩

/-- **Order-4 Taylor coefficients are unique.** -/
theorem taylor4_coeff_unique (f : ℝ → ℝ) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (ha : Filter.Tendsto
      (fun z : ℝ => (f z - (a0 + a1 * z + a2 * z ^ 2 + a3 * z ^ 3 + a4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hb : Filter.Tendsto
      (fun z : ℝ => (f z - (b0 + b1 * z + b2 * z ^ 2 + b3 * z ^ 3 + b4 * z ^ 4)) / z ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 := by
  have hdiff : Filter.Tendsto
      (fun z : ℝ => ((b0 - a0) + (b1 - a1) * z + (b2 - a2) * z ^ 2 + (b3 - a3) * z ^ 3
        + (b4 - a4) * z ^ 4) / z ^ 4) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hm := ha.sub hb
    rw [sub_zero] at hm
    refine hm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
    field_simp; ring
  obtain ⟨e0, e1, e2, e3, e4⟩ := poly4_eq_zero_of_littleO _ _ _ _ _ hdiff
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

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


/-- Order-3 Taylor coefficient of `p1(σ,s) = (1−sσ−e^{−sσ})/s²` at `0` is `σ⁵/120` — the order-3
companion of `p1_limit` and `p1_quartic_coeff`. -/
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

/-- Order-3 Taylor coefficient of `p2(σ,s) = (1−sσ+(sσ)²/2−e^{−sσ})/s³` at `0` is `−σ⁶/720` — the
order-3 companion of `p2_limit` and `p2_quartic_coeff`. -/
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

/-- Order-3 Taylor remainder of the entire function `e^{−λz}`:
`(e^{−λz} − (1 − λz + (λz)²/2 − (λz)³/6))/z³ → 0` as `z → 0⁺` — the order-3 companion of
`exp_neg_quartic_rem`. -/
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

end FMSA.Taylor4
