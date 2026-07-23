/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterPoleGuess
import LeanCode.HardSphere.HExplicitConcrete

/-!
# Task POLE.8 — the Baxter pole-family theorems fire unconditionally for `k1_guess`

`BaxterPoles.lean`'s pole-family consumers (`Qhat_complex_zeros_infinite`,
`G_baxter_zeros_infinite`, `G_baxter_pole_family_exists_growth`) are all conditional on a
"good guess" hypothesis block: a centre sequence `k1` with exact real parts `2πn/σ`, disks
that stay far from the origin (`hMball`), a coefficient-domination inequality on the disks
(`hDball`), a contraction constant `K < 1` (`hC`), and the chord-residual smallness `hstep`.
`BaxterPoleGuess.lean` (POLE.7) built the fit-free derived guess `k1_guess` and proved
`hstep` *eventually* (`k1_guess_hstep_eventually`), plus two-sided `Im`-bounds. This file
closes the loop: **every** hypothesis of the consumers holds for `k1_guess` for suitable
explicit `r`, `M`, `K` and all `n` past a threshold `N`, with no assumptions beyond the
physical parameter ranges `0 < η < 1`, `0 < σ`, `0 < ρ`.

All quantitative facts are stated over the public mirrors `guessP0/1/2`, which are
definitionally equal to the `private` `baxterP0/1/2` of `BaxterPoles.lean`, so `exact`
transports the proofs across the privacy boundary (the `rfl`-bridge pattern of POLE.7).

## Results

* `mem_closedBall_re_ge` / `mem_closedBall_abs_im_le` / `mem_closedBall_norm_le` — disk
  geometry: coordinatewise control of every point of `Metric.closedBall c r`.
* `k1_guess_Mball` — the `hMball` hypothesis from the single threshold `M + r ≤ 2πn/σ`.
* `dball_key_of` / `k1_guess_Dball_of` — the `hDball` hypothesis from a linear threshold on
  `x = 2πn/σ` once `Im(k1_guess n) ≤ x/2` (the POLE.7 sublinear log cap).
* `im_key_of` — the `k1_guess_im_ge_of` key inequality from a linear threshold.
* `k1_guess_im_bounds_of` — `0 ≤ Im(k1_guess n) ≤ x/2` from the POLE.7 envelope bounds.
* `k1_guess_family_conditions` — the packaged existence of `r`, `M`, `K`, `N` satisfying the
  complete consumer hypothesis block (plus `r ≤ Im(k1_guess n)` for POLE.6).
* `Qhat_complex_zeros_infinite_unconditional`, `G_baxter_zeros_infinite_unconditional`,
  `h_explicit_summable_unconditional` — the three final unconditional theorems.

**Status:** ✓ DONE, axiom-clean (no `sorry`, no new axiom).
-/

namespace FMSA.HardSphere

noncomputable section

/-! ### Disk geometry helpers -/

/-- Every point of a closed disk has real part at least `Re(centre) − radius`. -/
theorem mem_closedBall_re_ge {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    c.re - r ≤ k.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have h1 : |(k - c).re| ≤ ‖k - c‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at h1
  have h2 := abs_le.mp (le_trans h1 hk)
  linarith [h2.1]

/-- Every point of a closed disk has `|Im|` at most `|Im(centre)| + radius`. -/
theorem mem_closedBall_abs_im_le {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    |k.im| ≤ |c.im| + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have h1 : |(k - c).im| ≤ ‖k - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h1
  have h2 : |k.im| ≤ |c.im| + |k.im - c.im| := by
    calc |k.im| = |c.im + (k.im - c.im)| := by congr 1; ring
      _ ≤ |c.im| + |k.im - c.im| := abs_add_le _ _
  linarith

/-- Every point of a closed disk has norm at most `‖centre‖ + radius`. -/
theorem mem_closedBall_norm_le {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    ‖k‖ ≤ ‖c‖ + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  calc ‖k‖ = ‖c + (k - c)‖ := by congr 1; ring
    _ ≤ ‖c‖ + ‖k - c‖ := norm_add_le _ _
    _ ≤ ‖c‖ + r := by linarith

/-! ### The `hMball` and `hDball` hypotheses for `k1_guess` -/

/-- **The `hMball` hypothesis** for `k1_guess`: once `M + r ≤ 2πn/σ`, every point of the
radius-`r` disk around `k1_guess n` has norm at least `M` (via the exact real part). -/
theorem k1_guess_Mball (eta sigma rho : ℝ) {M r : ℝ} (n : ℕ)
    (h : M + r ≤ 2 * Real.pi * n / sigma) :
    ∀ k ∈ Metric.closedBall (k1_guess eta sigma rho n) r, M ≤ ‖k‖ := by
  intro k hk
  have h1 := mem_closedBall_re_ge hk
  rw [k1_guess_re] at h1
  have h2 : k.re ≤ ‖k‖ := Complex.re_le_norm k
  linarith

/-- Arithmetic core of the `hDball` threshold: with `y ≤ x/2` (the sublinear cap on
`Im(k1_guess n)`), `r ≤ 1 ≤ x`, and `x` past the explicit linear threshold, the disk
inequality budget `CL·(x+y+r) < Q·((x−r)² − (y+r)²)` holds. -/
theorem dball_key_of {Q CL r x y : ℝ} (hQ : 0 < Q) (hCL : 0 ≤ CL) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx1 : 1 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ 1 / 2 * x)
    (hxD : 4 / (3 * Q) * (5 / 2 * CL + 3 * Q * r + 1) ≤ x) :
    CL * (x + y + r) < Q * ((x - r) ^ 2 - (y + r) ^ 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h3Q : (0 : ℝ) < 3 * Q := by linarith
  -- from the threshold: `(5/2)·CL + 3·Q·r + 1 ≤ (3/4)·Q·x`
  have h1 : 5 / 2 * CL + 3 * Q * r + 1 ≤ 3 / 4 * Q * x := by
    rw [div_mul_eq_mul_div, div_le_iff₀ h3Q] at hxD
    linarith [hxD]
  -- multiply through by `x ≥ 1`
  have h4 : (5 / 2 * CL + 3 * Q * r + 1) * x ≤ 3 / 4 * Q * x * x :=
    mul_le_mul_of_nonneg_right h1 hx0.le
  -- square comparisons
  have h5 : (y + r) ^ 2 ≤ (1 / 2 * x + r) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h6 : Q * (y + r) ^ 2 ≤ Q * (1 / 2 * x + r) ^ 2 := mul_le_mul_of_nonneg_left h5 hQ.le
  have h7 : CL * (x + y + r) ≤ CL * (5 / 2 * x) :=
    mul_le_mul_of_nonneg_left (by linarith) hCL
  nlinarith [h4, h6, h7, hx1]

/-- **The `hDball` hypothesis** for `k1_guess`, from the per-`n` budget inequality `hkey` on
`x = 2πn/σ` and `y = Im(k1_guess n)` (discharged by `dball_key_of` past the threshold). -/
theorem k1_guess_Dball_of (eta sigma rho : ℝ) (n : ℕ) {CL r : ℝ}
    (hCL : 0 ≤ CL) (hr0 : 0 ≤ r)
    (hy0 : 0 ≤ (k1_guess eta sigma rho n).im)
    (hrx : r ≤ 2 * Real.pi * n / sigma)
    (hQp : 0 ≤ rho * q_prime_py eta sigma)
    (hkey : CL * (2 * Real.pi * n / sigma + (k1_guess eta sigma rho n).im + r) <
      rho * q_prime_py eta sigma *
        ((2 * Real.pi * n / sigma - r) ^ 2 - ((k1_guess eta sigma rho n).im + r) ^ 2)) :
    ∀ k ∈ Metric.closedBall (k1_guess eta sigma rho n) r,
      CL * ‖k‖ < rho * q_prime_py eta sigma * (k ^ 2).re := by
  intro k hk
  have hx0 : (0 : ℝ) ≤ 2 * Real.pi * n / sigma := le_trans hr0 hrx
  have hxr0 : (0 : ℝ) ≤ 2 * Real.pi * n / sigma - r := by linarith
  -- disk geometry at the centre `k1_guess n`
  have hre : 2 * Real.pi * n / sigma - r ≤ k.re := by
    have h := mem_closedBall_re_ge hk
    rwa [k1_guess_re] at h
  have him : |k.im| ≤ (k1_guess eta sigma rho n).im + r := by
    have h := mem_closedBall_abs_im_le hk
    rwa [abs_of_nonneg hy0] at h
  have hnorm : ‖k‖ ≤ 2 * Real.pi * n / sigma + (k1_guess eta sigma rho n).im + r := by
    have h := mem_closedBall_norm_le hk
    have h2 := Complex.norm_le_abs_re_add_abs_im (k1_guess eta sigma rho n)
    rw [k1_guess_re, abs_of_nonneg hx0, abs_of_nonneg hy0] at h2
    linarith
  -- `(k²).re` in coordinates
  have hsq : (k ^ 2).re = k.re * k.re - k.im * k.im := by
    rw [pow_two, Complex.mul_re]
  have hre2 : (2 * Real.pi * n / sigma - r) ^ 2 ≤ k.re ^ 2 :=
    pow_le_pow_left₀ hxr0 hre 2
  have him2 : k.im ^ 2 ≤ ((k1_guess eta sigma rho n).im + r) ^ 2 := by
    rw [← sq_abs k.im]
    exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hQle : rho * q_prime_py eta sigma *
      ((2 * Real.pi * n / sigma - r) ^ 2 - ((k1_guess eta sigma rho n).im + r) ^ 2) ≤
      rho * q_prime_py eta sigma * (k ^ 2).re := by
    refine mul_le_mul_of_nonneg_left ?_ hQp
    rw [hsq]
    linarith [hre2, him2]
  have hCLle : CL * ‖k‖ ≤
      CL * (2 * Real.pi * n / sigma + (k1_guess eta sigma rho n).im + r) :=
    mul_le_mul_of_nonneg_left hnorm hCL
  linarith [hkey, hQle, hCLle]

/-! ### The `Im(k1_guess) ≥ r` key inequality -/

/-- Arithmetic core of the `Im ≥ r` threshold (`k1_guess_im_ge_of`'s `hkey`): past the linear
threshold `1 + B + E·(Q + 2C₂) ≤ x` (with `x ≥ 1`), `E·(Q·x + 2C₂) ≤ x³ − B·x`. -/
theorem im_key_of {Q B C2 E x : ℝ} (hC2 : 0 ≤ C2) (hE : 0 < E)
    (hx1 : 1 ≤ x) (hxI : 1 + B + E * (Q + 2 * C2) ≤ x) :
    E * (Q * x + 2 * C2) ≤ x ^ 3 - B * x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h1 : x ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have h2 : 1 + B + E * (Q + 2 * C2) ≤ x ^ 2 := le_trans hxI h1
  have h3 : (1 + B + E * (Q + 2 * C2)) * x ≤ x ^ 2 * x :=
    mul_le_mul_of_nonneg_right h2 hx0.le
  have h4 : 0 ≤ E * C2 * (x - 1) :=
    mul_nonneg (mul_nonneg hE.le hC2) (by linarith)
  nlinarith [h3, h4]

/-! ### The sublinear cap `0 ≤ Im(k1_guess n) ≤ x/2` -/

/-- **Two-sided `Im`-bounds for `k1_guess`** past explicit linear/logarithmic thresholds in
`x = 2πn/σ`: nonnegativity via the `upD ≤ lowN` gap, and the sublinear cap `Im ≤ x/2` via the
POLE.7 envelope constants and the `log x / x → 0` cap (`ε = 1/2` instance of the assembly in
`k1_guess_hstep_eventually`). -/
theorem k1_guess_im_bounds_of (eta sigma rho : ℝ) (n : ℕ) (hsigma : 0 < sigma)
    (hQp : 0 < rho * q_prime_py eta sigma)
    (hx1 : 1 ≤ 2 * Real.pi * n / sigma)
    (hxB : 2 * |guessP1 eta sigma rho| ≤ 2 * Real.pi * n / sigma)
    (hxD : 2 * guessCD eta sigma rho ≤ 2 * Real.pi * n / sigma)
    (hlog : Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma)) +
        2 * Real.log (2 * Real.pi * n / sigma) ≤
      sigma * (1 / 2) * (2 * Real.pi * n / sigma)) :
    0 ≤ (k1_guess eta sigma rho n).im ∧
      (k1_guess eta sigma rho n).im ≤ 1 / 2 * (2 * Real.pi * n / sigma) := by
  have hcU := guessCU_pos eta sigma rho
  have hx0 : (0 : ℝ) < 2 * Real.pi * (n : ℝ) / sigma := lt_of_lt_of_le one_pos hx1
  have hx_le_sq : 2 * Real.pi * (n : ℝ) / sigma ≤ (2 * Real.pi * (n : ℝ) / sigma) ^ 2 := by
    linarith [mul_nonneg hx0.le
      (by linarith : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ) / sigma - 1)]
  have hxB2 : 2 * |guessP1 eta sigma rho| ≤ (2 * Real.pi * (n : ℝ) / sigma) ^ 2 := by
    linarith
  have hlowN := lowN_half_ge_of eta sigma rho hx0 hxB2
  have hx3 : (0 : ℝ) < (2 * Real.pi * (n : ℝ) / sigma) ^ 3 := pow_pos hx0 3
  have hlowN_pos : 0 < lowN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) := by linarith
  have hlowD_pos : 0 < lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) := by
    unfold lowD
    exact mul_pos hQp hx0
  -- `0 ≤ Im(k1_guess n)` via the `upD ≤ lowN` gap
  have hupD := upD_le_of eta sigma rho hx1
  have hcDx : guessCD eta sigma rho * (2 * Real.pi * (n : ℝ) / sigma) ≤
      (2 * Real.pi * (n : ℝ) / sigma) ^ 3 / 2 := by
    have h := mul_le_mul_of_nonneg_right
      (show 2 * guessCD eta sigma rho ≤ (2 * Real.pi * (n : ℝ) / sigma) ^ 2 by linarith)
      hx0.le
    linarith [h]
  have hgapND : upD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) ≤
      lowN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) := by
    linarith [hupD, hcDx, hlowN]
  have hy0 := k1_guess_im_nonneg_of eta sigma rho n hsigma hQp.le rfl hlowD_pos hgapND
  -- the sublinear cap `Im(k1_guess n) ≤ x/2`
  have him_le := k1_guess_im_le_of eta sigma rho n hsigma rfl hlowN_pos hlowD_pos
  have hupN := upN_le_of eta sigma rho hx1
  have hupN_pos : 0 < upN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) := by
    unfold upN
    have h1 := mul_nonneg (abs_nonneg (guessP0 eta sigma rho))
      (sq_nonneg (2 * Real.pi * (n : ℝ) / sigma))
    have h2 := mul_nonneg (abs_nonneg (guessP1 eta sigma rho)) hx0.le
    linarith [hx3, abs_nonneg (guessP2 eta sigma rho)]
  have hratio1 : upN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) /
      lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) ≤
      guessCU eta sigma rho * (2 * Real.pi * (n : ℝ) / sigma) ^ 3 /
        (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma)) := by
    have hlowD_eq : lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) =
        rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma) := rfl
    rw [hlowD_eq]
    exact div_le_div_bound hupN (mul_nonneg hcU.le hx3.le) (mul_pos hQp hx0) le_rfl
  have hratio2 : guessCU eta sigma rho * (2 * Real.pi * (n : ℝ) / sigma) ^ 3 /
      (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma)) =
      guessCU eta sigma rho / (rho * q_prime_py eta sigma) *
        (2 * Real.pi * (n : ℝ) / sigma) ^ 2 := by
    field_simp [hQp.ne', hx0.ne']
  have hlog1 : Real.log (upN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) /
      lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma)) ≤
      Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma) *
        (2 * Real.pi * (n : ℝ) / sigma) ^ 2) := by
    apply Real.log_le_log (div_pos hupN_pos hlowD_pos)
    rw [← hratio2]
    exact hratio1
  have hlog2 : Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma) *
      (2 * Real.pi * (n : ℝ) / sigma) ^ 2) =
      Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma)) +
        2 * Real.log (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [Real.log_mul (ne_of_gt (div_pos hcU hQp)) (ne_of_gt (pow_pos hx0 2)),
      Real.log_pow]
    norm_num
  refine ⟨hy0, ?_⟩
  have hcap : Real.log (upN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) /
      lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma)) ≤
      sigma * (1 / 2) * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [hlog2] at hlog1
    linarith [hlog, hlog1]
  have hdiv : Real.log (upN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) /
      lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma)) / sigma ≤
      1 / 2 * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [div_le_iff₀ hsigma]
    linarith [hcap]
  linarith [him_le, hdiv]

/-! ### The packaged family conditions -/

/-- **POLE.8, packaged conditions.** For every physical parameter set there are an explicit
radius `r`, floor `M`, contraction constant `K < 1`, and threshold `N ≥ 1` such that the
derived log-lift guess `k1_guess` satisfies **every** hypothesis of the pole-family consumers
of `BaxterPoles.lean` (stated over the public mirrors `guessP0/1/2`, definitionally the
`private` `baxterP0/1/2`, so the proofs transport by `exact`). The final conjunct
(`r ≤ Im(k1_guess n)`) additionally feeds `h_explicit_summable_concrete`'s `hk1im`. -/
theorem k1_guess_family_conditions {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    ∃ (r M : ℝ) (K : NNReal) (N : ℕ), 0 < r ∧ r < Real.pi / sigma ∧ 1 ≤ M ∧ 1 ≤ N ∧
      (K : ℝ) < 1 ∧
      2 * (|guessP0 eta sigma rho| + |guessP1 eta sigma rho| +
        |2 * guessP2 eta sigma rho|) ≤ M ∧
      2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M ∧
      (8 + 4 * |guessP0 eta sigma rho| + 2 * |guessP1 eta sigma rho|) / (sigma * M) ≤
        (K : ℝ) ∧
      (∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1_guess eta sigma rho n) r, M ≤ ‖k‖) ∧
      (∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1_guess eta sigma rho n) r,
        ((rho * q_doubleprime_py eta) +
            (rho * q_prime_py eta sigma) * (|guessP0 eta sigma rho| +
              |guessP1 eta sigma rho| + |2 * guessP2 eta sigma rho|) +
            (rho * q_doubleprime_py eta) * (|guessP0 eta sigma rho| +
              |guessP1 eta sigma rho| + |2 * guessP2 eta sigma rho|)) * ‖k‖ <
          (rho * q_prime_py eta sigma) * (k ^ 2).re) ∧
      (∀ n, N ≤ n →
        dist (k1_guess eta sigma rho n)
          (baxterPhi eta sigma rho n (k1_guess eta sigma rho n)) ≤ r * (1 - (K : ℝ))) ∧
      (∀ n, N ≤ n → r ≤ (k1_guess eta sigma rho n).im) := by
  have hQp : 0 < rho * q_prime_py eta sigma := baxterMu_pos heta0 heta1 hsigma hrho
  have hQQ : 0 < rho * q_doubleprime_py eta := baxterNu_pos heta0 heta1 hrho
  set S : ℝ := |guessP0 eta sigma rho| + |guessP1 eta sigma rho| +
    |2 * guessP2 eta sigma rho| with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  set CL : ℝ := rho * q_doubleprime_py eta + rho * q_prime_py eta sigma * S +
    rho * q_doubleprime_py eta * S with hCLdef
  have hCL0 : 0 ≤ CL := by
    rw [hCLdef]
    have h1 := mul_nonneg hQp.le hS0
    have h2 := mul_nonneg hQQ.le hS0
    linarith [hQQ.le]
  -- the radius: `r ≤ 1` and `r < π/σ` with room to spare
  set r : ℝ := min 1 (Real.pi / (2 * sigma)) with hrdef
  have hr0 : 0 < r := by
    rw [hrdef]
    exact lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := by rw [hrdef]; exact min_le_left _ _
  have hrspace : r < Real.pi / sigma := by
    have h1 : Real.pi / (2 * sigma) < Real.pi / sigma := by
      have h2 : Real.pi / (2 * sigma) = Real.pi / sigma / 2 := by ring
      rw [h2]
      exact half_lt_self (div_pos Real.pi_pos hsigma)
    calc r ≤ Real.pi / (2 * sigma) := by rw [hrdef]; exact min_le_right _ _
      _ < Real.pi / sigma := h1
  -- the floor `M`: dominates all four required lower bounds
  set M : ℝ := max (max 1 (2 * S))
    (max (2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma))
      (2 * (8 + 4 * |guessP0 eta sigma rho| + 2 * |guessP1 eta sigma rho|) / sigma))
    with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]; exact le_trans (le_max_left 1 (2 * S)) (le_max_left _ _)
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hMS : 2 * S ≤ M := by
    rw [hMdef]; exact le_trans (le_max_right 1 (2 * S)) (le_max_left _ _)
  have hMD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M := by
    rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hMC : 2 * (8 + 4 * |guessP0 eta sigma rho| + 2 * |guessP1 eta sigma rho|) / sigma ≤
      M := by
    rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- the contraction constant: `K = (8+4|P0|+2|P1|)/(σM) ≤ 1/2`
  set v : ℝ := (8 + 4 * |guessP0 eta sigma rho| + 2 * |guessP1 eta sigma rho|) /
    (sigma * M) with hvdef
  have hv0 : 0 < v := by
    rw [hvdef]
    exact div_pos (by positivity) (mul_pos hsigma hM0)
  have hv_half : v ≤ 1 / 2 := by
    rw [div_le_iff₀ hsigma] at hMC
    rw [hvdef, div_le_iff₀ (mul_pos hsigma hM0)]
    linarith
  set K : NNReal := Real.toNNReal v with hKdef
  have hKv : (K : ℝ) = v := by rw [hKdef]; exact Real.coe_toNNReal v hv0.le
  have hK1 : (K : ℝ) < 1 := by rw [hKv]; linarith
  have htarget : 0 < r * (1 - (K : ℝ)) := mul_pos hr0 (by rw [hKv]; linarith)
  -- the POLE.7 chord-residual threshold
  obtain ⟨N₁, hN₁⟩ := k1_guess_hstep_eventually eta sigma rho r (K : ℝ) hsigma hQp htarget
  -- the remaining real-variable thresholds, bundled into one eventual statement
  have hlogcap := eventually_log_cap
    (Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma))) (sigma * (1 / 2))
    (by positivity)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      1 ≤ x ∧ M + r ≤ x ∧ 2 * |guessP1 eta sigma rho| ≤ x ∧
      2 * guessCD eta sigma rho ≤ x ∧
      4 / (3 * (rho * q_prime_py eta sigma)) *
        (5 / 2 * CL + 3 * (rho * q_prime_py eta sigma) * r + 1) ≤ x ∧
      1 + |guessP1 eta sigma rho| +
        Real.exp (sigma * r) * (rho * q_prime_py eta sigma +
          2 * |guessP2 eta sigma rho|) ≤ x ∧
      Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma)) +
        2 * Real.log x ≤ sigma * (1 / 2) * x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop (M + r),
      Filter.eventually_ge_atTop (2 * |guessP1 eta sigma rho|),
      Filter.eventually_ge_atTop (2 * guessCD eta sigma rho),
      Filter.eventually_ge_atTop (4 / (3 * (rho * q_prime_py eta sigma)) *
        (5 / 2 * CL + 3 * (rho * q_prime_py eta sigma) * r + 1)),
      Filter.eventually_ge_atTop (1 + |guessP1 eta sigma rho| +
        Real.exp (sigma * r) * (rho * q_prime_py eta sigma +
          2 * |guessP2 eta sigma rho|)),
      hlogcap] with x h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have htends : Filter.Tendsto (fun n : ℕ => 2 * Real.pi * (n : ℝ) / sigma)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hsigma
      (Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (htends.eventually hev)
  refine ⟨r, M, K, max (max N₁ N₂) 1, hr0, hrspace, hM1, le_max_right _ 1, hK1, hMS, hMD,
    hKv.ge, ?_, ?_, ?_, ?_⟩
  -- `hMball`
  · intro n hn
    obtain ⟨-, hxM, -, -, -, -, -⟩ := hN₂ n
      (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) 1)) hn)
    exact k1_guess_Mball eta sigma rho n hxM
  -- `hDball`
  · intro n hn
    obtain ⟨hx1, -, hxB, hxD, hxDD, -, hlogx⟩ := hN₂ n
      (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) 1)) hn)
    obtain ⟨hy0, hyx⟩ := k1_guess_im_bounds_of eta sigma rho n hsigma hQp hx1 hxB hxD hlogx
    have hkey := dball_key_of hQp hCL0 hr0.le hr1 hx1 hy0 hyx hxDD
    exact k1_guess_Dball_of eta sigma rho n hCL0 hr0.le hy0 (le_trans hr1 hx1) hQp.le hkey
  -- `hstep`
  · intro n hn
    exact hN₁ n (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) 1)) hn)
  -- `r ≤ Im(k1_guess n)`
  · intro n hn
    obtain ⟨hx1, -, -, -, -, hxI, -⟩ := hN₂ n
      (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) 1)) hn)
    have hden_pos : 0 < rho * q_prime_py eta sigma * (2 * Real.pi * n / sigma) +
        2 * |guessP2 eta sigma rho| := by
      have h1 : (0 : ℝ) < 2 * Real.pi * n / sigma := lt_of_lt_of_le one_pos hx1
      have h2 := mul_pos hQp h1
      linarith [abs_nonneg (guessP2 eta sigma rho)]
    have hkey := im_key_of (abs_nonneg (guessP2 eta sigma rho))
      (Real.exp_pos (sigma * r)) hx1 hxI
    exact k1_guess_im_ge_of eta sigma rho r n hsigma hQp.le hden_pos hkey

/-! ### The three unconditional final theorems -/

/-- **POLE.8, final statement 1**: `1 − Q̂(k)` has infinitely many complex zeros, for every
physical parameter set — `Qhat_complex_zeros_infinite` fired on `k1_guess` via
`k1_guess_family_conditions` (the `guessP`/`baxterP` defeq bridge closes the hypotheses). -/
theorem Qhat_complex_zeros_infinite_unconditional {eta sigma rho : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) :
    {k : ℂ | 1 - Qhat_complex eta sigma rho k = 0}.Infinite := by
  obtain ⟨r, M, K, N, hr0, hrspace, hM1, _hN1, hK1, hkN, hkD, hC, hMball, hDball, hstep,
    _him⟩ := k1_guess_family_conditions heta0 heta1 hsigma hrho
  exact Qhat_complex_zeros_infinite heta0 heta1 hsigma hrho hr0 hrspace hM1 N
    (k1_guess eta sigma rho) (fun n _ => k1_guess_re eta sigma rho n) hMball hkN hkD hDball
    K hK1 hC hstep

/-- **POLE.8, final statement 2**: `G_baxter` has infinitely many zeros, unconditionally. -/
theorem G_baxter_zeros_infinite_unconditional {eta sigma rho : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) :
    {k : ℂ | G_baxter eta sigma rho k = 0}.Infinite := by
  obtain ⟨r, M, K, N, hr0, hrspace, hM1, _hN1, hK1, hkN, hkD, hC, hMball, hDball, hstep,
    _him⟩ := k1_guess_family_conditions heta0 heta1 hsigma hrho
  exact G_baxter_zeros_infinite heta0 heta1 hsigma hrho hr0 hrspace hM1 N
    (k1_guess eta sigma rho) (fun n _ => k1_guess_re eta sigma rho n) hMball hkN hkD hDball
    K hK1 hC hstep

/-- **POLE.8, final statement 3**: an injective upper-half-plane `G_baxter` zero family with
`h_explicit_term` summable at every radial distance `y > σ` exists unconditionally —
`G_baxter_pole_family_exists_growth` + `h_explicit_summable_concrete` fired on `k1_guess`. -/
theorem h_explicit_summable_unconditional {eta sigma rho y : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hy : sigma < y) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧ (∀ n, G_baxter eta sigma rho (g n) = 0) ∧
      (∀ n, 0 ≤ (g n).im) ∧ Summable (h_explicit_term eta sigma rho y g) := by
  obtain ⟨r, M, K, N, hr0, hrspace, hM1, hN1, hK1, hkN, hkD, hC, hMball, hDball, hstep,
    him⟩ := k1_guess_family_conditions heta0 heta1 hsigma hrho
  have hfam := G_baxter_pole_family_exists_growth heta0 heta1 hsigma hrho hr0 hrspace hM1 N
    hN1 (k1_guess eta sigma rho) (fun n _ => k1_guess_re eta sigma rho n) hMball hkN hkD
    hDball K hK1 hC hstep
  exact h_explicit_summable_concrete heta0 heta1 hsigma hrho hy him hfam

end

end FMSA.HardSphere
