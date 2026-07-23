/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.OzCollapseTwoSigma

/-!
# Task OZFIX.12 — the inner region `σ < r < 2σ`: reduction of `hcollapse` to the core identity

`OZFIX.11` proved `hcollapse` outright for `2σ ≤ r`. On `σ < r < 2σ` the collapse is genuinely
**not** per-pole (`OZFIX.6`'s `-2.72` finding lives here): `oz_forcing ≠ 0`, and
`max(r-t,σ)` switches from `r-t` to `σ` at `t = r-σ`. This file reduces that region to a single,
self-contained identity about the residue series alone — no `oz_forcing`, no `oz_linear_op`:

**(★)** `∑'ₙ [Hterm n u - Hterm n σ] = π(σ² - u²)` for `u ∈ (0, σ]`

whose content is exactly: *the exterior residue series, continued into the core, reproduces
`h = -1`* (differentiate: `∑' h_explicit_term(u) = -2πu ⟺ h_explicit(u) = -1`). This is the
Wertheim–Thiele core-closure statement for the concrete PY series.

**Summability caveat, and why the `K`-form is the right one.** `‖Hterm n u‖ ≲ ‖kₙ‖^{-2u/σ}`, so
(★)'s series is absolutely convergent only for `u > σ/2` — stating (★) as a `HasSum` on all of
`(0,σ]` would be a *false* hypothesis (and would make any theorem consuming it vacuous). One more
antiderivative fixes this: `Kterm` (this file) satisfies `‖Kterm n u‖ ≲ ‖kₙ‖^{-1-2u/σ}`, summable
for **every** `u > 0`. Integrating (★) from `σ` to `u` gives the equivalent, always-summable

**(★K)** `∑'ₙ [Kterm n u - Kterm n σ - (u-σ)·Hterm n σ] = π(σ²(u-σ) - (u³-σ³)/3)`, `u ∈ (0,σ]`

which is what `oz_collapse_inner_of_star` consumes. Per-pole integration by parts (`Kterm' =
Hterm`) converts the outer `t`-integral into `K`-values at the two endpoints plus one interval
integral, all absolutely convergent for `r > σ`; (★K) then makes the whole thing collapse to
`-2πΦ(r) = -(r/ρ)·oz_forcing(r)` by pure polynomial algebra.

**Numerically validated first** (`ozfix12_star_check.py`, scratch; η=0.3, σ=1, 400 Newton-refined
poles): (★) converges to `π(σ²-u²)` like `~1/N` at every `u ∈ {0.55,…,0.99}` (diff `-1.9e-3` at
N=400, halving per doubling); `∑' Dₙ(r) → -2πΦ(r)` at `r ∈ {1.2, 1.5, 1.8, 1.95}`; `Hterm` is
exactly real (mirror pairing).

**Status of (★) itself — the circularity finding (`OZFIX.14`).** (★) is *not* provable from the
contour machinery: closing the UHP contour on `S(z)Ξ(z)` (`S := 1/(1-ρĈ)`, `Ξ` the entire kernel
whose residues are (★K)'s summands) makes the `1` of `S` cancel *exactly* between the real line
and the arc, leaving `2πi·∑'Res = ρ·∫_ℝ Ĥ(x)Ξ(x)dx` — i.e. the contour merely transports the
claim from the pole sum to the *value of the real-line integral of `Ĥ`*, which is the core
closure itself. See `proof_notes_ozfix.md` `OZFIX.14`.

**Status:** ✓ DONE (the reduction), axiom-clean; (★K) carried as an explicit hypothesis.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-! ### `Kterm` — one more antiderivative than `Hterm` -/

/-- **`Kterm`**: the pole+mirror antiderivative of `Hterm` (`residue_term` over `(I·k)²`). Decays
one power of `‖k‖` better than `Hterm`, hence summable at every `y > 0` (not just `y ≥ σ`). -/
def Kterm (eta sigma rho : ℝ) (kfam : ℕ → ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  residue_term eta sigma rho r (kfam n) / (Complex.I * kfam n) ^ 2 +
    residue_term eta sigma rho r (-(starRingEnd ℂ) (kfam n)) /
      (Complex.I * (-(starRingEnd ℂ) (kfam n))) ^ 2

/-- `Kterm` is an antiderivative of `Hterm`. -/
theorem Kterm_hasDerivAt {eta sigma rho : ℝ} {kfam : ℕ → ℂ} (hkfam_ne : ∀ n, kfam n ≠ 0)
    (n : ℕ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => Kterm eta sigma rho kfam n x) (Hterm eta sigma rho kfam n r) r := by
  have hk : kfam n ≠ 0 := hkfam_ne n
  have hk' : -(starRingEnd ℂ) (kfam n) ≠ 0 := by simpa using hk
  have h1 : HasDerivAt
      (fun x : ℝ => residue_term eta sigma rho x (kfam n) / (Complex.I * kfam n) ^ 2)
      (residue_term eta sigma rho r (kfam n) / (Complex.I * kfam n)) r := by
    have h := (residue_term_hasDerivAt (eta := eta) (sigma := sigma) (rho := rho) hk r).div_const
      (Complex.I * kfam n)
    simpa [sq, div_div] using h
  have h2 : HasDerivAt
      (fun x : ℝ => residue_term eta sigma rho x (-(starRingEnd ℂ) (kfam n)) /
        (Complex.I * (-(starRingEnd ℂ) (kfam n))) ^ 2)
      (residue_term eta sigma rho r (-(starRingEnd ℂ) (kfam n)) /
        (Complex.I * (-(starRingEnd ℂ) (kfam n)))) r := by
    have h := (residue_term_hasDerivAt (eta := eta) (sigma := sigma) (rho := rho) hk' r).div_const
      (Complex.I * (-(starRingEnd ℂ) (kfam n)))
    simpa [sq, div_div] using h
  exact h1.add h2

/-- **`Kterm`'s magnitude, uniformly summable in `n`, for every `y ≥ y0` with `y0 > 0`** — the
`Kterm` counterpart of `OZFIX.4`'s `Hterm_uniform_summable_bound_of_pole_family`. The threshold is
`y0 > 0` (not `y0 > σ`, nor even `y0 > σ/2`): the extra `1/‖k‖` from `(I·k)²` puts the effective
exponent at `-1 - 2·y0/σ < -1` for **any** positive `y0`, which is exactly what lets the inner
region `σ < r < 2σ` (where the series is sampled at `u = r-t` down to `r-σ`, arbitrarily close to
`0`) be handled at all. Mirrors that lemma's `corrOverK`-threading structure with `σ ↦ y0` and one
more power of `‖k‖`. -/
theorem Kterm_uniform_summable_bound_of_pole_family {eta sigma rho y0 : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hy0 : 0 < y0)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n : ℕ, ∀ {y : ℝ}, y0 ≤ y → ‖Kterm eta sigma rho kfam n y‖ ≤ u n := by
  obtain ⟨C, M, hCpos, hM1, hbound⟩ := residue_term_norm_bound heta0 heta1 hsigma hrho hy0
  set p : ℝ := (1 - 2 * y0 / sigma) - 2 with hpdef
  have hp0 : p < 0 := by
    rw [hpdef]
    have : 0 < 2 * y0 / sigma := by positivity
    linarith
  have hp1 : p < -1 := by
    rw [hpdef]
    have : 0 < 2 * y0 / sigma := by positivity
    linarith
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp1
  have h1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ p) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ p) 1).mpr h0
  have hg0' : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
    convert h1 using 2 with n
    push_cast
    ring
  set g : ℕ → ℝ := fun n => 2 * C * (min c d) ^ p * ((n : ℝ) + 1) ^ p with hgdef
  have hg : Summable g := by
    rw [hgdef]
    have := hg0'.mul_left (2 * C * (min c d) ^ p)
    simpa [mul_assoc] using this
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M ≤ c * (N : ℝ) + d := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((M - d) / c)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ hc] at hN
    linarith [hN]
  -- the central quantity: the two `residue_term` norms *at y0*, divided by `‖kfam n‖²`
  set corrOverK : ℕ → ℝ := fun n => (‖residue_term eta sigma rho y0 (kfam n)‖ +
    ‖residue_term eta sigma rho y0 (-(starRingEnd ℂ) (kfam n))‖) / ‖kfam n‖ ^ 2 with hcorrdef
  have hgN : ∀ n : ℕ, N ≤ n → corrOverK n ≤ g n := by
    intro n hn
    have hNn : M ≤ c * (n : ℝ) + d := by
      have hcn : c * (N : ℝ) ≤ c * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact_mod_cast hn
      linarith [hN, hcn]
    have hMk : M ≤ ‖kfam n‖ := le_trans hNn (hkfam_re n)
    have hnormeq : ‖-(starRingEnd ℂ) (kfam n)‖ = ‖kfam n‖ := by rw [norm_neg, RCLike.norm_conj]
    have himeq : (-(starRingEnd ℂ) (kfam n)).im = (kfam n).im := by
      simp only [Complex.neg_im, Complex.conj_im, neg_neg]
    have hzeroMirror : G_baxter eta sigma rho (-(starRingEnd ℂ) (kfam n)) = 0 :=
      G_baxter_zero_mirror (hkfam_zero n)
    have hkimMirror : 0 ≤ (-(starRingEnd ℂ) (kfam n)).im := by rw [himeq]; exact hkfam_im n
    have hkMMirror : M ≤ ‖(-(starRingEnd ℂ) (kfam n))‖ := by rw [hnormeq]; exact hMk
    have hb1 := hbound (hkfam_zero n) (hkfam_im n) hMk
    have hb2 := hbound hzeroMirror hkimMirror hkMMirror
    rw [hnormeq] at hb2
    have hLpos : 0 < c * (n : ℝ) + d := by
      have hcnn : (0:ℝ) ≤ c * (n:ℝ) := by positivity
      linarith [hM1, hNn]
    have hkpos : 0 < ‖kfam n‖ := lt_of_lt_of_le hLpos (hkfam_re n)
    have hnp1pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hinv1 : ‖kfam n‖ ^ (1 - 2 * y0 / sigma) / ‖kfam n‖ ^ 2 = ‖kfam n‖ ^ p := by
      have h2 : (‖kfam n‖ ^ (2:ℕ)) = ‖kfam n‖ ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [h2, hpdef, ← Real.rpow_sub hkpos]
    have hcorr_le : corrOverK n ≤ 2 * C * ‖kfam n‖ ^ p := by
      rw [hcorrdef]
      calc (‖residue_term eta sigma rho y0 (kfam n)‖ +
          ‖residue_term eta sigma rho y0 (-(starRingEnd ℂ) (kfam n))‖) / ‖kfam n‖ ^ 2
          ≤ (C * ‖kfam n‖ ^ (1 - 2 * y0 / sigma) + C * ‖kfam n‖ ^ (1 - 2 * y0 / sigma))
              / ‖kfam n‖ ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            linarith [hb1, hb2]
        _ = 2 * C * (‖kfam n‖ ^ (1 - 2 * y0 / sigma) / ‖kfam n‖ ^ 2) := by ring
        _ = 2 * C * ‖kfam n‖ ^ p := by rw [hinv1]
    have hmono : ‖kfam n‖ ^ p ≤ (c * (n:ℝ) + d) ^ p :=
      (Real.rpow_le_rpow_iff_of_neg hkpos hLpos hp0).mpr (hkfam_re n)
    have hminpos : 0 < min c d := lt_min hc hd
    have hcdge : (min c d) * ((n:ℝ) + 1) ≤ c * (n:ℝ) + d := by
      rcases le_or_gt c d with hle | hle
      · rw [min_eq_left hle]; nlinarith [Nat.cast_nonneg n (α := ℝ)]
      · rw [min_eq_right hle.le]; nlinarith [Nat.cast_nonneg n (α := ℝ), hle]
    have hmono2 : (c * (n:ℝ) + d) ^ p ≤ ((min c d) * ((n:ℝ) + 1)) ^ p :=
      (Real.rpow_le_rpow_iff_of_neg hLpos (by positivity) hp0).mpr hcdge
    have hmono3 : ((min c d) * ((n:ℝ) + 1)) ^ p = (min c d) ^ p * ((n:ℝ) + 1) ^ p :=
      Real.mul_rpow hminpos.le hnp1pos.le
    have hchain : ‖kfam n‖ ^ p ≤ (min c d) ^ p * ((n:ℝ) + 1) ^ p := by
      calc ‖kfam n‖ ^ p ≤ (c * (n:ℝ) + d) ^ p := hmono
        _ ≤ ((min c d) * ((n:ℝ) + 1)) ^ p := hmono2
        _ = (min c d) ^ p * ((n:ℝ) + 1) ^ p := hmono3
    calc corrOverK n ≤ 2 * C * ‖kfam n‖ ^ p := hcorr_le
      _ ≤ 2 * C * ((min c d) ^ p * ((n:ℝ) + 1) ^ p) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
      _ = g n := by rw [hgdef]; ring
  set u : ℕ → ℝ := fun n => g n + (if n ∈ Finset.range N then corrOverK n else 0) with hudef
  have hufin : Summable (fun n : ℕ => (if n ∈ Finset.range N then corrOverK n else 0)) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro b hb
    simp [hb]
  have hu : Summable u := hg.add hufin
  have hu_corr : ∀ n : ℕ, corrOverK n ≤ u n := by
    intro n
    rcases lt_or_ge n N with hn | hn
    · have hun : u n = g n + corrOverK n := by
        change g n + (if n ∈ Finset.range N then _ else 0) = _
        simp [Finset.mem_range.mpr hn]
      have hg_nonneg : 0 ≤ g n := by rw [hgdef]; positivity
      rw [hun]; linarith [hg_nonneg]
    · have hgb := hgN n hn
      have hun : g n ≤ u n := by
        change g n ≤ g n + (if n ∈ Finset.range N then _ else 0)
        have hthis : (if n ∈ Finset.range N then corrOverK n else (0:ℝ)) = 0 := by
          simp [Finset.mem_range, not_lt.mpr hn]
        linarith [hthis]
      linarith [hgb, hun]
  refine ⟨u, hu, fun n {y} hy => ?_⟩
  have hkpos : 0 < ‖kfam n‖ := by
    have h1 : (0:ℝ) < c * (n:ℝ) + d := by positivity
    linarith [hkfam_re n, h1]
  have hkim' : 0 ≤ (-(starRingEnd ℂ) (kfam n)).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hkfam_im n
  have hnormeq : ‖-(starRingEnd ℂ) (kfam n)‖ = ‖kfam n‖ := by rw [norm_neg, RCLike.norm_conj]
  have hstep : ‖Kterm eta sigma rho kfam n y‖ ≤ corrOverK n := by
    rw [hcorrdef]
    unfold Kterm
    calc ‖residue_term eta sigma rho y (kfam n) / (Complex.I * kfam n) ^ 2 +
        residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n)) /
          (Complex.I * (-(starRingEnd ℂ) (kfam n))) ^ 2‖
        ≤ ‖residue_term eta sigma rho y (kfam n) / (Complex.I * kfam n) ^ 2‖ +
          ‖residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n)) /
            (Complex.I * (-(starRingEnd ℂ) (kfam n))) ^ 2‖ := norm_add_le _ _
      _ = ‖residue_term eta sigma rho y (kfam n)‖ / ‖kfam n‖ ^ 2 +
          ‖residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n))‖ / ‖kfam n‖ ^ 2 := by
          rw [norm_div, norm_div, norm_pow, norm_pow, norm_mul, norm_mul, Complex.norm_I,
            one_mul, one_mul, hnormeq]
      _ ≤ ‖residue_term eta sigma rho y0 (kfam n)‖ / ‖kfam n‖ ^ 2 +
          ‖residue_term eta sigma rho y0 (-(starRingEnd ℂ) (kfam n))‖ / ‖kfam n‖ ^ 2 := by
          gcongr
          · exact residue_term_norm_le_of_le (hkfam_im n) hy
          · exact residue_term_norm_le_of_le hkim' hy
      _ = (‖residue_term eta sigma rho y0 (kfam n)‖ +
          ‖residue_term eta sigma rho y0 (-(starRingEnd ℂ) (kfam n))‖) / ‖kfam n‖ ^ 2 := by ring
  linarith [hstep, hu_corr n]

/-- `Kterm`'s series is summable at every `y > 0`. -/
theorem Kterm_summable_of_pole_family {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun n => Kterm eta sigma rho kfam n y) := by
  obtain ⟨u, hu, hub⟩ := Kterm_uniform_summable_bound_of_pole_family heta0 heta1 hsigma hrho hy
    hc hd hkfam_zero hkfam_im hkfam_re
  exact Summable.of_norm_bounded hu (fun n => hub n le_rfl)

/-! ### The reduction target, recorded as a predicate -/

/-- **(★K) — the core-closure identity for the residue series, in always-summable `K`-form.**

`CoreSeriesClosure` says: `∑'ₙ [Kterm n u - Kterm n σ - (u-σ)·Hterm n σ] = π(σ²(u-σ) - (u³-σ³)/3)`
for every `u ∈ (0,σ]`. Its content is exactly the Wertheim–Thiele core closure for the *concrete*
PY residue series: differentiating twice recovers `h_explicit(u) = -1` on the core.

This is the (still open) hypothesis to which `OZFIX.12` reduces `hcollapse` on `σ < r < 2σ`; the
complementary region `2σ ≤ r` is unconditional (`oz_collapse_of_two_sigma_le`, `OZFIX.11`).

Stated in the `K`-form rather than the more natural `∑'ₙ[Hterm n u - Hterm n σ] = π(σ²-u²)`
because the latter's series is absolutely summable only for `u > σ/2` — as a `HasSum`/`tsum`
hypothesis on all of `(0,σ]` it would be **false**, hence vacuous. `Kterm`'s extra `1/‖k‖` makes
the `K`-form's series absolutely summable for every `u > 0`
(`Kterm_summable_of_pole_family`), so this predicate is a faithful, non-vacuous statement.

Numerically: confirmed to `~1/N` (`ozfix12_star_check.py`, η=0.3, σ=1, N=400 poles).

**⚠ This is a `Prop`, deliberately NOT an axiom — and it must NOT be promoted to one in this form.**
As a *hypothesis* it is safe: a consumer can only discharge it for a family that genuinely
enumerates the poles. But an axiom
`… (hkfam_zero) (hkfam_im) (hkfam_re) (hkfam_ne) : CoreSeriesClosure eta sigma rho kfam`
would be **FALSE**, hence inconsistent: the current pole-family pack constrains `kfam` only to be
*some* injective-growth sequence of `G_baxter` zeros, and **sub-families satisfy it too**.
Verified counterexample (η=0.3, σ=1): `kfam' n := k_{2n}` satisfies `hkfam_zero`/`hkfam_im`/
`hkfam_ne` and `hkfam_re` (explicitly, with `c = d = 6`), yet at `u = 0.7` its sum is `0.982`
against the target `1.602` (odd sub-family: `0.618`; dropping the first 5 poles: `0.077`) — while
the full family gives `1.600`. This is the same class of bug as MA.5's literal-zero-set and MA.2's
ordered-partial-sums traps (`MATH_AXIOMS.md`), caught here *before* promotion.

**An axiom form would additionally need the completeness bundle**: `Function.Injective kfam`;
exhaustion of the UHP zeros up to the mirror pairing (`∀ z, 0 < z.im → G_baxter … z = 0 →
∃ n, z = kfam n ∨ z = -conj (kfam n)`); and non-degeneracy of that pairing (no purely-imaginary
poles, i.e. `(kfam n).re ≠ 0`, else `k = -conj k` and `Hterm`/`Kterm` double-count; and
`kfam m ≠ -conj (kfam n)`, so pair representatives are not repeated). None of these is currently
available in the project — `POLE.8`'s `Qhat_complex_zeros_infinite_unconditional` gives
*infinitude*, **not** exhaustion. See `proof_notes_ozfix.md` `OZFIX.14` option (b). -/
def CoreSeriesClosure (eta sigma rho : ℝ) (kfam : ℕ → ℂ) : Prop :=
  ∀ u : ℝ, 0 < u → u ≤ sigma →
    (∑' n, (Kterm eta sigma rho kfam n u - Kterm eta sigma rho kfam n sigma -
        ((u - sigma : ℝ) : ℂ) * Hterm eta sigma rho kfam n sigma)) =
      ((Real.pi * (sigma ^ 2 * (u - sigma) - (u ^ 3 - sigma ^ 3) / 3) : ℝ) : ℂ)

/-- `CoreSeriesClosure`'s summand series is genuinely summable at every `u > 0` — so
`CoreSeriesClosure` is a non-vacuous statement about a convergent `tsum` (unlike the `Hterm`-form
(★), whose series diverges absolutely for `u ≤ σ/2`). -/
theorem coreSeriesClosure_summand_summable {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    {u : ℝ} (hu : 0 < u) :
    Summable (fun n => Kterm eta sigma rho kfam n u - Kterm eta sigma rho kfam n sigma -
      ((u - sigma : ℝ) : ℂ) * Hterm eta sigma rho kfam n sigma) := by
  have hK1 : Summable (fun n => Kterm eta sigma rho kfam n u) :=
    Kterm_summable_of_pole_family heta0 heta1 hsigma hrho hc hd hkfam_zero hkfam_im hkfam_re hu
  have hK2 : Summable (fun n => Kterm eta sigma rho kfam n sigma) :=
    Kterm_summable_of_pole_family heta0 heta1 hsigma hrho hc hd hkfam_zero hkfam_im hkfam_re hsigma
  have hH : Summable (fun n => Hterm eta sigma rho kfam n sigma) :=
    Hterm_summable_of_pole_family heta0 heta1 hsigma hrho hc hd hkfam_zero hkfam_im hkfam_re
      le_rfl
  exact (hK1.sub hK2).sub (hH.mul_left _)

end

end FMSA.HardSphere
