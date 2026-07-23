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
# Task POLE.9 — a concrete `ChordPoleFamily` for `G_baxter`

Constructs, for physical parameters (`0 < η < 1`, `σ > 0`, `ρ > 0`), a
`FMSA.BanachPoleFamily.ChordPoleFamily (G_baxter eta sigma rho)` — the shared Banach
chord-Newton obligation of POLE.3/MZERO.5 — and fires
`G_baxter_zeros_infinite_of_chordPoleFamily` to conclude that `G_baxter` has infinitely many
complex zeros.

## Instantiation

* centres `s1 n := k1_guess eta sigma rho n` (the POLE.7 log-lift guess, `Re = 2πn/σ` exact),
* derivative `F' := G_baxter_deriv`, frozen `Fp1 n := G_baxter_deriv (k1_guess n)`,
* radius `r := 1/(10σ)` (so `σr = 1/10`), Lipschitz constant `K := 1/2`.

## The mathematical core

Writing `x := 2πn/σ`, `y := Im (k1_guess n)`, `t := ‖Npoly(x)‖/‖Dpoly(x)‖`, `Q := ρ·q'_PY`:

* **Phase kill** (`exp_at_k1_guess`): `exp(−i·k1_guess(n)·σ) = t` *exactly* — the real part of
  `k1_guess` kills the oscillation (`xσ = 2πn`) and the imaginary part is the log-lift, so the
  exponential collapses to the positive real modulus ratio.
* **Frozen-derivative lower bound** (`G_baxter_deriv_k1_norm_lower`):
  `‖G′(k1)‖ ≥ (σ/2)·Q·x·t` once `x` clears explicit linear thresholds.
* **Chord contraction** (`G_baxter_deriv_ball_diff_le`): on the ball of radius `1/(10σ)` the
  derivative moves by at most `(σ/4)·Q·x·t` — the dominant term is
  `2σr·(σ‖D‖t) ≈ (1/5)·σQxt`, and `1/5 + small < 1/4`.
* **Chord step** (`G_baxter_k1_norm_le`): `‖G(k1)‖ ≤ (1/40)·Q·x·t`; the key third term
  `‖N(x) − t·D(x)‖ ≤ 2·|Im(N(x)·conj D(x))|/‖D(x)‖` is the purely algebraic
  `norm_sub_ratio_mul_le` below (no trigonometry).

All thresholds are bundled into one `∀ᶠ` pass (mirroring `k1_guess_hstep_eventually`) and
pushed along `n ↦ 2πn/σ → ∞`; separation `hsep` is free from `Re(k1_guess n) = 2πn/σ` since
`2r = 1/(5σ) < 2π/σ`.

**Status:** ✓ complete, axiom-clean — `chordPoleFamily_G_baxter_exists` and
`G_baxter_zeros_infinite_chord`.
-/

set_option linter.style.longLine false

open MeasureTheory Real Set

namespace FMSA.HardSphere

noncomputable section

/-! ### Bridges: `G_baxter_deriv` in public-coefficient (`guessP`) form -/

/-- **Privacy bridge for `G_baxter_deriv`** — closes by `rfl` since `guessP0/1` are
definitionally the `private` `baxterP0/1` (same pattern as `Npoly_eq_guess`). -/
theorem G_baxter_deriv_eq_guess (eta sigma rho : ℝ) (k : ℂ) :
    G_baxter_deriv eta sigma rho k =
      (3 * Complex.I * k ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * k +
          Complex.I * (guessP1 eta sigma rho : ℂ)) -
        ((Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * k * sigma) +
          Dpoly eta sigma rho k * (-Complex.I * sigma) *
            Complex.exp (-Complex.I * k * sigma)) := rfl

/-- `Dpoly` is affine with slope `i·ρQ′`: the exact two-point difference formula. -/
theorem Dpoly_sub_eq (eta sigma rho : ℝ) (a b : ℂ) :
    Dpoly eta sigma rho a - Dpoly eta sigma rho b =
      Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) * (a - b) := by
  have hlead : ((guessP1 eta sigma rho : ℂ) + 2 * (guessP2 eta sigma rho : ℂ) * (sigma : ℂ)) =
      ((rho * q_prime_py eta sigma : ℝ) : ℂ) := by
    calc ((guessP1 eta sigma rho : ℂ) + 2 * (guessP2 eta sigma rho : ℂ) * (sigma : ℂ))
        = ((guessP1 eta sigma rho + 2 * guessP2 eta sigma rho * sigma : ℝ) : ℂ) := by
          push_cast; ring
      _ = ((rho * q_prime_py eta sigma : ℝ) : ℂ) := by rw [Dpoly_lead_eq]
  rw [Dpoly_eq_guess, Dpoly_eq_guess]
  linear_combination (Complex.I * (a - b)) * hlead

/-- Norm form of `Dpoly_sub_eq`: `‖D(a) − D(b)‖ = ρQ′·‖a−b‖` (for `ρQ′ ≥ 0`). -/
theorem Dpoly_sub_norm_eq (eta sigma rho : ℝ) (a b : ℂ)
    (hQp : 0 ≤ rho * q_prime_py eta sigma) :
    ‖Dpoly eta sigma rho a - Dpoly eta sigma rho b‖ =
      rho * q_prime_py eta sigma * ‖a - b‖ := by
  rw [Dpoly_sub_eq, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hQp]

/-! ### The pivotal phase-kill lemma -/

/-- **Exact phase kill at the log-lift guess** (the pivotal lemma): the oscillatory factor of
`G_baxter` at `k1_guess n` collapses to the *positive real* modulus ratio
`t := ‖Npoly(xₙ)‖/‖Dpoly(xₙ)‖`, because `Re(k1_guess n)·σ = 2πn` exactly and
`Im(k1_guess n)·σ = log t` by construction. -/
theorem exp_at_k1_guess (eta sigma rho : ℝ) (hsigma : 0 < sigma) (n : ℕ)
    (hN : 0 < ‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖)
    (hD : 0 < ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖) :
    Complex.exp (-Complex.I * k1_guess eta sigma rho n * sigma) =
      ((‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ /
        ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ : ℝ) : ℂ) := by
  set L : ℝ := Real.log (‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ /
    ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖) with hLdef
  -- the guess in x + i·(L/σ) form
  have hk : k1_guess eta sigma rho n =
      ((2 * Real.pi * n / sigma : ℝ) : ℂ) + Complex.I * ((L / sigma : ℝ) : ℂ) := rfl
  -- the exponent splits into the real log part and an exact 2πn phase
  have hexp_arg : -Complex.I * k1_guess eta sigma rho n * sigma =
      (L : ℂ) + ((-(n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hk]
    have hLs : ((L / sigma : ℝ) : ℂ) * (sigma : ℂ) = (L : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    have hxs : ((2 * Real.pi * n / sigma : ℝ) : ℂ) * (sigma : ℂ) =
        2 * (Real.pi : ℂ) * (n : ℂ) := by
      rw [← Complex.ofReal_mul]
      have hval : (2 * Real.pi * n / sigma) * sigma = 2 * Real.pi * n := by
        field_simp
      rw [hval]
      push_cast
      ring
    have hIcast : ((-(n : ℤ) : ℤ) : ℂ) = -(n : ℂ) := by push_cast; ring
    calc -Complex.I * (((2 * Real.pi * n / sigma : ℝ) : ℂ) +
          Complex.I * ((L / sigma : ℝ) : ℂ)) * (sigma : ℂ)
        = -Complex.I * (((2 * Real.pi * n / sigma : ℝ) : ℂ) * (sigma : ℂ)) -
            Complex.I * Complex.I * (((L / sigma : ℝ) : ℂ) * (sigma : ℂ)) := by ring
      _ = -Complex.I * (2 * (Real.pi : ℂ) * (n : ℂ)) - Complex.I * Complex.I * (L : ℂ) := by
          rw [hLs, hxs]
      _ = (L : ℂ) + (-(n : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
          rw [Complex.I_mul_I]; ring
      _ = (L : ℂ) + ((-(n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          rw [hIcast]
  rw [hexp_arg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    ← Complex.ofReal_exp, hLdef, Real.exp_log (div_pos hN hD)]

/-! ### The algebraic chord-step lemma (no trigonometry) -/

/-- **Modulus-matched residual bound**: for `B ≠ 0` and `Re(A·conj B) ≥ 0`, subtracting the
modulus-matched multiple `(‖A‖/‖B‖)·B` from `A` leaves at most `2·|Im(A·conj B)|/‖B‖` —
purely algebraic (squares/`normSq` only, no `arg`). This is the "third term" engine of the
chord `hstep` bound: at the log-lift guess, `G(k1) = N(k1) − t·D(k1)` with `t = ‖N(x)‖/‖D(x)‖`,
and on the real axis the mismatch is controlled by the *phase* difference alone, i.e. by
`Im(N(x)·conj D(x))`. -/
theorem norm_sub_ratio_mul_le (A B : ℂ) (hB : B ≠ 0)
    (hre : 0 ≤ (A * (starRingEnd ℂ) B).re) :
    ‖A - ((‖A‖ / ‖B‖ : ℝ) : ℂ) * B‖ ≤ 2 * |(A * (starRingEnd ℂ) B).im| / ‖B‖ := by
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  rcases eq_or_ne A 0 with hA | hA
  · subst hA
    simp only [norm_zero, zero_div, Complex.ofReal_zero, zero_mul, sub_zero]
    positivity
  · have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
    set R : ℝ := (A * (starRingEnd ℂ) B).re with hRdef
    set m : ℝ := (A * (starRingEnd ℂ) B).im with hmdef
    -- (‖A‖‖B‖)² = R² + m²
    have habsq : (‖A‖ * ‖B‖) ^ 2 = R ^ 2 + m ^ 2 := by
      have h1 : Complex.normSq (A * (starRingEnd ℂ) B) = R ^ 2 + m ^ 2 := by
        rw [Complex.normSq_apply, hRdef, hmdef]; ring
      have h2 : Complex.normSq (A * (starRingEnd ℂ) B) = (‖A‖ * ‖B‖) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj]
      rw [← h2, h1]
    have hab_pos : 0 < ‖A‖ * ‖B‖ := mul_pos hApos hBpos
    have hRle : R ≤ ‖A‖ * ‖B‖ := by nlinarith [sq_nonneg m]
    -- normSq expansion of the residual
    have hexp : Complex.normSq (A - ((‖A‖ / ‖B‖ : ℝ) : ℂ) * B) =
        Complex.normSq A - 2 * (‖A‖ / ‖B‖) * R + (‖A‖ / ‖B‖) ^ 2 * Complex.normSq B := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hRdef,
        Complex.conj_re, Complex.conj_im]
      ring
    -- multiplied-out key inequality (all divisions cleared)
    have hkey : Complex.normSq (A - ((‖A‖ / ‖B‖ : ℝ) : ℂ) * B) * ‖B‖ ^ 2 ≤
        (2 * |m|) ^ 2 := by
      have hns : Complex.normSq (A - ((‖A‖ / ‖B‖ : ℝ) : ℂ) * B) * ‖B‖ ^ 2 =
          2 * (‖A‖ * ‖B‖) * (‖A‖ * ‖B‖ - R) := by
        rw [hexp, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        field_simp
        ring
      have h1 : (‖A‖ * ‖B‖ - R) * (‖A‖ * ‖B‖) ≤ m ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hRle) hre]
      have h2 : m ^ 2 ≤ |m| ^ 2 := by rw [sq_abs]
      nlinarith [h1, h2, sq_nonneg m]
    -- pass to norms and take square roots
    have hsq : ‖A - ((‖A‖ / ‖B‖ : ℝ) : ℂ) * B‖ ^ 2 ≤ (2 * |m| / ‖B‖) ^ 2 := by
      have h3 : ‖A - ((‖A‖ / ‖B‖ : ℝ) : ℂ) * B‖ ^ 2 =
          Complex.normSq (A - ((‖A‖ / ‖B‖ : ℝ) : ℂ) * B) :=
        (Complex.normSq_eq_norm_sq _).symm
      rw [h3, div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < ‖B‖ ^ 2)]
      exact hkey
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- The chord-step "third term", instantiated: on the real axis,
`‖N(x) − t·D(x)‖ ≤ 2·|wIm x|/‖D(x)‖` with `t := ‖N(x)‖/‖D(x)‖`, provided the branch-safety
quantity `wRe x = Re(N(x)·conj D(x))` is nonnegative. -/
theorem Npoly_sub_ratio_Dpoly_le (eta sigma rho : ℝ) (x : ℝ)
    (hD : Dpoly eta sigma rho (x : ℂ) ≠ 0) (hre : 0 ≤ wRe eta sigma rho x) :
    ‖Npoly eta sigma rho (x : ℂ) -
        ((‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖ : ℝ) : ℂ) *
          Dpoly eta sigma rho (x : ℂ)‖ ≤
      2 * |wIm eta sigma rho x| / ‖Dpoly eta sigma rho (x : ℂ)‖ := by
  have hreval : (Npoly eta sigma rho (x : ℂ) *
      (starRingEnd ℂ) (Dpoly eta sigma rho (x : ℂ))).re = wRe eta sigma rho x := by
    rw [NconjD_re]; rfl
  have himval : (Npoly eta sigma rho (x : ℂ) *
      (starRingEnd ℂ) (Dpoly eta sigma rho (x : ℂ))).im = wIm eta sigma rho x := by
    rw [NconjD_im]; rfl
  have h := norm_sub_ratio_mul_le (Npoly eta sigma rho (x : ℂ))
    (Dpoly eta sigma rho (x : ℂ)) hD (by rw [hreval]; exact hre)
  rwa [himval] at h

/-! ### Real-axis norm facts feeding the chord bounds -/

/-- `x³/2 ≤ ‖Npoly(x)‖` once `x ≥ 1` and `2|P1| ≤ x`. -/
theorem Npoly_x_norm_half_cubic (eta sigma rho : ℝ) {x : ℝ} (hx1 : 1 ≤ x)
    (hxB : 2 * |guessP1 eta sigma rho| ≤ x) :
    x ^ 3 / 2 ≤ ‖Npoly eta sigma rho (x : ℂ)‖ := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxB2 : 2 * |guessP1 eta sigma rho| ≤ x ^ 2 := by nlinarith
  have h1 := lowN_half_ge_of eta sigma rho hx0 hxB2
  have h2 := Npoly_norm_lower eta sigma rho hx0.le
  unfold lowN at h1
  linarith

/-- Modulus-ratio lower bound `x² ≤ 2·guessCD·t`, `t := ‖N(x)‖/‖D(x)‖` (multiplied-out form
of `t ≥ x²/(2·guessCD)`). -/
theorem t_ratio_lower (eta sigma rho : ℝ) (hQp : 0 < rho * q_prime_py eta sigma)
    {x : ℝ} (hx1 : 1 ≤ x) (hxB : 2 * |guessP1 eta sigma rho| ≤ x) :
    x ^ 2 ≤ 2 * guessCD eta sigma rho *
      (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hNlow := Npoly_x_norm_half_cubic eta sigma rho hx1 hxB
  have hDup : ‖Dpoly eta sigma rho (x : ℂ)‖ ≤ guessCD eta sigma rho * x := by
    have h1 := Dpoly_norm_upper eta sigma rho hx0.le hQp.le
    have h2 := upD_le_of eta sigma rho hx1
    unfold upD at h2
    linarith
  have hDpos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := by
    have h := Dpoly_norm_lower eta sigma rho x
    nlinarith [mul_pos hQp hx0]
  have hgCD : 0 < guessCD eta sigma rho := guessCD_pos eta sigma rho hQp
  have hdiv : (x ^ 3 / 2) / (guessCD eta sigma rho * x) ≤
      ‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖ :=
    div_le_div_bound hNlow (le_trans (by positivity) hNlow) hDpos hDup
  have heq : (x ^ 3 / 2) / (guessCD eta sigma rho * x) =
      x ^ 2 / (2 * guessCD eta sigma rho) := by
    field_simp
  rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * guessCD eta sigma rho)] at hdiv
  linarith [hdiv]

/-! ### The frozen-derivative lower bound -/

/-- **`‖G′(k1_guess n)‖ ≥ (σ/2)·Q·x·t`** under explicit linear thresholds on `x = 2πn/σ`:
the dominant `σ·‖D(k1)‖·t ≥ σQxt` term beats the `μt` and `‖N′(k1)‖ ≤ guessCN·x²` corrections
once `σx ≥ 4` and `σQx ≥ 8·guessCN·guessCD`. -/
theorem G_baxter_deriv_k1_norm_lower (eta sigma rho : ℝ) (n : ℕ)
    (hsigma : 0 < sigma) (hQp : 0 < rho * q_prime_py eta sigma)
    {x y : ℝ}
    (hxdef : x = 2 * Real.pi * n / sigma)
    (hydef : y = (k1_guess eta sigma rho n).im)
    (hx1 : 1 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ x)
    (hxB : 2 * |guessP1 eta sigma rho| ≤ x)
    (hx6 : 4 ≤ sigma * x)
    (hx7 : 8 * guessCN eta sigma rho * guessCD eta sigma rho ≤
      sigma * (rho * q_prime_py eta sigma) * x) :
    sigma / 2 * (rho * q_prime_py eta sigma) * x *
      (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖) ≤
    ‖G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n)‖ := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hNpos : 0 < ‖Npoly eta sigma rho (x : ℂ)‖ := by
    have := Npoly_x_norm_half_cubic eta sigma rho hx1 hxB
    nlinarith [pow_pos hx0 3]
  have hDpos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := by
    have h := Dpoly_norm_lower eta sigma rho x
    nlinarith [mul_pos hQp hx0]
  -- phase kill at the guess
  have hNpos' : 0 < ‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ := by
    rw [← hxdef]; exact hNpos
  have hDpos' : 0 < ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ := by
    rw [← hxdef]; exact hDpos
  have hP := exp_at_k1_guess eta sigma rho hsigma n hNpos' hDpos'
  rw [← hxdef] at hP
  set t : ℝ := ‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖ with htdef
  have htpos : 0 < t := div_pos hNpos hDpos
  have ht2 := t_ratio_lower eta sigma rho hQp hx1 hxB
  rw [← htdef] at ht2
  -- the guess in `x + y·i` shape, and its norm bound
  have hK : k1_guess eta sigma rho n = (x : ℂ) + (y : ℂ) * Complex.I := by
    rw [hxdef, hydef]; exact k1_guess_eq eta sigma rho n
  have hKnorm : ‖k1_guess eta sigma rho n‖ ≤ x + y := by
    calc ‖k1_guess eta sigma rho n‖
        ≤ |(k1_guess eta sigma rho n).re| + |(k1_guess eta sigma rho n).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |x| + |y| := by rw [k1_guess_re, ← hxdef, ← hydef]
      _ = x + y := by rw [abs_of_pos hx0, abs_of_nonneg hy0]
  -- D at the guess is large (y-independent imaginary part)
  have hDK1low : rho * q_prime_py eta sigma * x ≤
      ‖Dpoly eta sigma rho (k1_guess eta sigma rho n)‖ := by
    rw [hK]; exact Dpoly_offReal_norm_lower eta sigma rho x y
  -- N′ at the guess is small: `≤ guessCN·x²`
  have hNd : ‖3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
      2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
      Complex.I * (guessP1 eta sigma rho : ℂ)‖ ≤ guessCN eta sigma rho * x ^ 2 := by
    have h1 := Npoly_deriv_norm_le eta sigma rho hKnorm
    have hA0 : (0 : ℝ) ≤ |guessP0 eta sigma rho| := abs_nonneg _
    have hB0 : (0 : ℝ) ≤ |guessP1 eta sigma rho| := abs_nonneg _
    have hparen : 3 * (x + y) ^ 2 + 2 * |guessP0 eta sigma rho| * (x + y) +
        |guessP1 eta sigma rho| ≤ guessCN eta sigma rho * x ^ 2 := by
      unfold guessCN
      have h2 : (x + y) ^ 2 ≤ 4 * x ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - y)
          (by linarith : (0 : ℝ) ≤ 3 * x + y)]
      have h3 : 2 * |guessP0 eta sigma rho| * (x + y) ≤
          4 * |guessP0 eta sigma rho| * x ^ 2 := by
        nlinarith [mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ x - y),
          mul_nonneg (mul_nonneg hA0 hx0.le) (by linarith : (0 : ℝ) ≤ x - 1)]
      have h5 : |guessP1 eta sigma rho| ≤ |guessP1 eta sigma rho| * x ^ 2 := by
        nlinarith [mul_nonneg hB0
          (by nlinarith [sq_nonneg (x - 1)] : (0 : ℝ) ≤ x ^ 2 - 1)]
      nlinarith
    linarith
  -- the exact formula for `G′` at the guess (phase already killed)
  have hGd : G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) =
      Complex.I * (sigma : ℂ) * Dpoly eta sigma rho (k1_guess eta sigma rho n) *
          ((t : ℝ) : ℂ) -
        (Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) * ((t : ℝ) : ℂ) -
          (3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
            2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
            Complex.I * (guessP1 eta sigma rho : ℂ))) := by
    rw [G_baxter_deriv_eq_guess, hP]
    ring
  -- norm lower bound via the reverse triangle inequality
  have hmain : ‖Complex.I * (sigma : ℂ) * Dpoly eta sigma rho (k1_guess eta sigma rho n) *
      ((t : ℝ) : ℂ)‖ = sigma * ‖Dpoly eta sigma rho (k1_guess eta sigma rho n)‖ * t := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsigma,
      abs_of_nonneg htpos.le]
  have hcorr : ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) * ((t : ℝ) : ℂ) -
      (3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
        2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
        Complex.I * (guessP1 eta sigma rho : ℂ))‖ ≤
      rho * q_prime_py eta sigma * t + guessCN eta sigma rho * x ^ 2 := by
    have h1 : ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ =
        rho * q_prime_py eta sigma * t := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hQp,
        abs_of_nonneg htpos.le]
    calc ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) * ((t : ℝ) : ℂ) -
        (3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
          2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
          Complex.I * (guessP1 eta sigma rho : ℂ))‖
        ≤ ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ +
          ‖3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
            2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
            Complex.I * (guessP1 eta sigma rho : ℂ)‖ := norm_sub_le _ _
      _ ≤ rho * q_prime_py eta sigma * t + guessCN eta sigma rho * x ^ 2 := by
          rw [h1]; linarith [hNd]
  have hrevtri : ‖Complex.I * (sigma : ℂ) * Dpoly eta sigma rho (k1_guess eta sigma rho n) *
        ((t : ℝ) : ℂ)‖ -
      ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) * ((t : ℝ) : ℂ) -
        (3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
          2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
          Complex.I * (guessP1 eta sigma rho : ℂ))‖ ≤
      ‖G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n)‖ := by
    rw [hGd]
    exact norm_sub_norm_le _ _
  -- assemble the budget: `σ‖D(k1)‖t − Qt − guessCN·x² ≥ (σ/2)Qxt`
  have hDterm : sigma * (rho * q_prime_py eta sigma * x) * t ≤
      sigma * ‖Dpoly eta sigma rho (k1_guess eta sigma rho n)‖ * t := by
    have := mul_le_mul_of_nonneg_left hDK1low hsigma.le
    exact mul_le_mul_of_nonneg_right this htpos.le
  have hbud1 : rho * q_prime_py eta sigma * t ≤
      sigma / 4 * (rho * q_prime_py eta sigma) * x * t := by
    have hprod : 0 ≤ (sigma * x - 4) * (rho * q_prime_py eta sigma * t) :=
      mul_nonneg (by linarith) (mul_nonneg hQp.le htpos.le)
    nlinarith [hprod]
  have hbud2 : guessCN eta sigma rho * x ^ 2 ≤
      sigma / 4 * (rho * q_prime_py eta sigma) * x * t := by
    have hcN := guessCN_pos eta sigma rho
    have ha := mul_le_mul_of_nonneg_left ht2 hcN.le
    have hb := mul_le_mul_of_nonneg_right hx7 htpos.le
    nlinarith [ha, hb]
  calc sigma / 2 * (rho * q_prime_py eta sigma) * x * t
      ≤ sigma * (rho * q_prime_py eta sigma * x) * t -
        (rho * q_prime_py eta sigma * t + guessCN eta sigma rho * x ^ 2) := by
        nlinarith [hbud1, hbud2]
    _ ≤ sigma * ‖Dpoly eta sigma rho (k1_guess eta sigma rho n)‖ * t -
        (rho * q_prime_py eta sigma * t + guessCN eta sigma rho * x ^ 2) := by
        linarith [hDterm]
    _ ≤ ‖G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n)‖ := by
        rw [← hmain]
        linarith [hrevtri, hcorr]

/-! ### The chord contraction bound on the disk -/

/-- **Derivative variation on the chord disk**: for `s` in the closed ball of radius
`1/(10σ)` around `k1_guess n`, `‖G′(k1) − G′(s)‖ ≤ (σ/4)·Q·x·t`. The dominant contribution is
`‖iμ − iσD(s)‖·t·‖e^{−i(s−k1)σ} − 1‖ ≲ σ·Qx·t·(2σr) = (1/5)·σQxt`; the `N′` variation, the
`D`-drift and all constant-order corrections fit in the remaining `(1/4 − 1/5)` slack via the
explicit linear thresholds `hx8`–`hx10`. -/
theorem G_baxter_deriv_ball_diff_le (eta sigma rho : ℝ) (n : ℕ)
    (hsigma : 0 < sigma) (hQp : 0 < rho * q_prime_py eta sigma)
    {x y : ℝ}
    (hxdef : x = 2 * Real.pi * n / sigma)
    (hydef : y = (k1_guess eta sigma rho n).im)
    (hx1 : 1 ≤ x) (hy0 : 0 ≤ y) (hy20 : 20 * y ≤ x)
    (hxB : 2 * |guessP1 eta sigma rho| ≤ x)
    (hx8 : 22 * (rho * q_prime_py eta sigma) + 40 * sigma * |guessP2 eta sigma rho| ≤
      sigma * (rho * q_prime_py eta sigma) * x)
    (hx9 : 100 * guessCD eta sigma rho * (1 / (10 * sigma)) *
        (12 + 3 * (1 / (10 * sigma)) + 2 * |guessP0 eta sigma rho|) ≤
      sigma * (rho * q_prime_py eta sigma) * x)
    (hx10 : 10 ≤ sigma * x)
    {s : ℂ} (hs : s ∈ Metric.closedBall (k1_guess eta sigma rho n) (1 / (10 * sigma))) :
    ‖G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) -
        G_baxter_deriv eta sigma rho s‖ ≤
      sigma / 4 * (rho * q_prime_py eta sigma) * x *
        (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hNpos : 0 < ‖Npoly eta sigma rho (x : ℂ)‖ := by
    have := Npoly_x_norm_half_cubic eta sigma rho hx1 hxB
    nlinarith [pow_pos hx0 3]
  have hDpos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := by
    have h := Dpoly_norm_lower eta sigma rho x
    nlinarith [mul_pos hQp hx0]
  have hNpos' : 0 < ‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ := by
    rw [← hxdef]; exact hNpos
  have hDpos' : 0 < ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ := by
    rw [← hxdef]; exact hDpos
  have hP := exp_at_k1_guess eta sigma rho hsigma n hNpos' hDpos'
  rw [← hxdef] at hP
  set r : ℝ := 1 / (10 * sigma) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hσr : sigma * r = 1 / 10 := by rw [hrdef]; field_simp
  set t : ℝ := ‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖ with htdef
  have htpos : 0 < t := div_pos hNpos hDpos
  have ht2 := t_ratio_lower eta sigma rho hQp hx1 hxB
  rw [← htdef] at ht2
  have hgCD : 0 < guessCD eta sigma rho := guessCD_pos eta sigma rho hQp
  have hK : k1_guess eta sigma rho n = (x : ℂ) + (y : ℂ) * Complex.I := by
    rw [hxdef, hydef]; exact k1_guess_eq eta sigma rho n
  have hKnorm : ‖k1_guess eta sigma rho n‖ ≤ x + y := by
    calc ‖k1_guess eta sigma rho n‖
        ≤ |(k1_guess eta sigma rho n).re| + |(k1_guess eta sigma rho n).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |x| + |y| := by rw [k1_guess_re, ← hxdef, ← hydef]
      _ = x + y := by rw [abs_of_pos hx0, abs_of_nonneg hy0]
  have hsK : ‖s - k1_guess eta sigma rho n‖ ≤ r := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hs
  -- exponential splitting along the disk
  have hexp_split : Complex.exp (-Complex.I * s * sigma) =
      ((t : ℝ) : ℂ) * Complex.exp (-Complex.I * (s - k1_guess eta sigma rho n) * sigma) := by
    have harg : -Complex.I * s * (sigma : ℂ) =
        -Complex.I * k1_guess eta sigma rho n * sigma +
          -Complex.I * (s - k1_guess eta sigma rho n) * sigma := by ring
    rw [harg, Complex.exp_add, hP]
  -- the three-piece decomposition of the derivative difference
  have hdecomp : G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) -
      G_baxter_deriv eta sigma rho s =
      ((3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
          2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
          Complex.I * (guessP1 eta sigma rho : ℂ)) -
        (3 * Complex.I * s ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * s +
          Complex.I * (guessP1 eta sigma rho : ℂ))) +
      ((Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
          Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s) * ((t : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * (s - k1_guess eta sigma rho n) * sigma) - 1)) +
      Complex.I * (sigma : ℂ) *
        (Dpoly eta sigma rho (k1_guess eta sigma rho n) - Dpoly eta sigma rho s) *
        ((t : ℝ) : ℂ) := by
    rw [G_baxter_deriv_eq_guess eta sigma rho (k1_guess eta sigma rho n),
      G_baxter_deriv_eq_guess eta sigma rho s, hexp_split, hP]
    ring
  -- piece 1: the `N′` variation
  have hn1 : ‖(3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
      2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
      Complex.I * (guessP1 eta sigma rho : ℂ)) -
      (3 * Complex.I * s ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * s +
        Complex.I * (guessP1 eta sigma rho : ℂ))‖ ≤
      r * ((12 + 3 * r + 2 * |guessP0 eta sigma rho|) * x) := by
    have hfact : (3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
        2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
        Complex.I * (guessP1 eta sigma rho : ℂ)) -
        (3 * Complex.I * s ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * s +
          Complex.I * (guessP1 eta sigma rho : ℂ)) =
        (k1_guess eta sigma rho n - s) *
          (3 * Complex.I * (k1_guess eta sigma rho n + s) -
            2 * (guessP0 eta sigma rho : ℂ)) := by ring
    rw [hfact, norm_mul]
    have h1 : ‖k1_guess eta sigma rho n - s‖ ≤ r := by
      rw [norm_sub_rev]; exact hsK
    have hsnorm : ‖s‖ ≤ x + y + r := by
      calc ‖s‖ = ‖k1_guess eta sigma rho n + (s - k1_guess eta sigma rho n)‖ := by ring_nf
        _ ≤ ‖k1_guess eta sigma rho n‖ + ‖s - k1_guess eta sigma rho n‖ := norm_add_le _ _
        _ ≤ x + y + r := by linarith [hKnorm, hsK]
    have h2 : ‖3 * Complex.I * (k1_guess eta sigma rho n + s) -
        2 * (guessP0 eta sigma rho : ℂ)‖ ≤
        (12 + 3 * r + 2 * |guessP0 eta sigma rho|) * x := by
      have h3 : ‖3 * Complex.I * (k1_guess eta sigma rho n + s)‖ =
          3 * ‖k1_guess eta sigma rho n + s‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        norm_num
      have h4 : ‖2 * (guessP0 eta sigma rho : ℂ)‖ = 2 * |guessP0 eta sigma rho| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      have h5 : ‖k1_guess eta sigma rho n + s‖ ≤ 2 * (x + y) + r := by
        calc ‖k1_guess eta sigma rho n + s‖
            ≤ ‖k1_guess eta sigma rho n‖ + ‖s‖ := norm_add_le _ _
          _ ≤ 2 * (x + y) + r := by linarith [hKnorm, hsnorm]
      have hA0 : (0 : ℝ) ≤ |guessP0 eta sigma rho| := abs_nonneg _
      have hyx : y ≤ x := by linarith
      calc ‖3 * Complex.I * (k1_guess eta sigma rho n + s) -
          2 * (guessP0 eta sigma rho : ℂ)‖
          ≤ ‖3 * Complex.I * (k1_guess eta sigma rho n + s)‖ +
            ‖2 * (guessP0 eta sigma rho : ℂ)‖ := norm_sub_le _ _
        _ ≤ 3 * (2 * (x + y) + r) + 2 * |guessP0 eta sigma rho| := by
            rw [h3, h4]; linarith [h5]
        _ ≤ (12 + 3 * r + 2 * |guessP0 eta sigma rho|) * x := by
            nlinarith [mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ x - 1),
              mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ x - 1)]
    exact mul_le_mul h1 h2 (norm_nonneg _) hr0.le
  -- piece 1 budget: `≤ (1/50)·σQxt`
  have hn1bud : r * ((12 + 3 * r + 2 * |guessP0 eta sigma rho|) * x) ≤
      1 / 50 * (sigma * (rho * q_prime_py eta sigma) * x * t) := by
    have hC0 : (0 : ℝ) ≤ 12 + 3 * r + 2 * |guessP0 eta sigma rho| := by
      have := abs_nonneg (guessP0 eta sigma rho)
      linarith
    have hxsq : x ≤ x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1) hx0.le]
    have hx2gCDt : x ≤ 2 * guessCD eta sigma rho * t := by linarith [ht2, hxsq]
    have ha : r * (12 + 3 * r + 2 * |guessP0 eta sigma rho|) * x ≤
        r * (12 + 3 * r + 2 * |guessP0 eta sigma rho|) * (2 * guessCD eta sigma rho * t) :=
      mul_le_mul_of_nonneg_left hx2gCDt (mul_nonneg hr0.le hC0)
    have hb : 100 * guessCD eta sigma rho * r *
        (12 + 3 * r + 2 * |guessP0 eta sigma rho|) * t ≤
        sigma * (rho * q_prime_py eta sigma) * x * t :=
      mul_le_mul_of_nonneg_right hx9 htpos.le
    linarith [ha, hb]
  -- piece 2: the oscillatory factor
  have hDs : ‖Dpoly eta sigma rho s‖ ≤
      rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| +
        rho * q_prime_py eta sigma * (y + r) := by
    have hDx_up := Dpoly_norm_upper eta sigma rho hx0.le hQp.le
    have hk1x : k1_guess eta sigma rho n - (x : ℂ) = (y : ℂ) * Complex.I := by
      rw [hK]; ring
    have hsx : ‖s - (x : ℂ)‖ ≤ y + r := by
      calc ‖s - (x : ℂ)‖
          = ‖(s - k1_guess eta sigma rho n) + (k1_guess eta sigma rho n - (x : ℂ))‖ := by
            ring_nf
        _ ≤ ‖s - k1_guess eta sigma rho n‖ + ‖k1_guess eta sigma rho n - (x : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ r + y := by
            rw [hk1x, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hy0]
            linarith [hsK]
        _ = y + r := by ring
    have hdiff : ‖Dpoly eta sigma rho s - Dpoly eta sigma rho (x : ℂ)‖ ≤
        rho * q_prime_py eta sigma * (y + r) := by
      rw [Dpoly_sub_norm_eq eta sigma rho s (x : ℂ) hQp.le]
      exact mul_le_mul_of_nonneg_left hsx hQp.le
    calc ‖Dpoly eta sigma rho s‖
        = ‖Dpoly eta sigma rho (x : ℂ) +
            (Dpoly eta sigma rho s - Dpoly eta sigma rho (x : ℂ))‖ := by ring_nf
      _ ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ +
          ‖Dpoly eta sigma rho s - Dpoly eta sigma rho (x : ℂ)‖ := norm_add_le _ _
      _ ≤ rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| +
          rho * q_prime_py eta sigma * (y + r) := by linarith [hDx_up, hdiff]
  have hEfac : ‖Complex.exp (-Complex.I * (s - k1_guess eta sigma rho n) * sigma) - 1‖ ≤
      2 * (sigma * r) := by
    have hznorm : ‖-Complex.I * (s - k1_guess eta sigma rho n) * (sigma : ℂ)‖ =
        sigma * ‖s - k1_guess eta sigma rho n‖ := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hsigma]
      ring
    have hz1 : ‖-Complex.I * (s - k1_guess eta sigma rho n) * (sigma : ℂ)‖ ≤ 1 := by
      rw [hznorm]
      have := mul_le_mul_of_nonneg_left hsK hsigma.le
      rw [hσr] at this
      linarith
    calc ‖Complex.exp (-Complex.I * (s - k1_guess eta sigma rho n) * sigma) - 1‖
        ≤ 2 * ‖-Complex.I * (s - k1_guess eta sigma rho n) * (sigma : ℂ)‖ :=
          Complex.norm_exp_sub_one_le hz1
      _ ≤ 2 * (sigma * r) := by
          rw [hznorm]
          have := mul_le_mul_of_nonneg_left hsK hsigma.le
          linarith
  have hn2 : ‖(Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
      Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s) * ((t : ℝ) : ℂ) *
      (Complex.exp (-Complex.I * (s - k1_guess eta sigma rho n) * sigma) - 1)‖ ≤
      (rho * q_prime_py eta sigma + sigma *
        (rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| +
          rho * q_prime_py eta sigma * (y + r))) * t * (2 * (sigma * r)) := by
    rw [norm_mul, norm_mul]
    have hf1 : ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
        Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s‖ ≤
        rho * q_prime_py eta sigma + sigma *
          (rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| +
            rho * q_prime_py eta sigma * (y + r)) := by
      have hIQ : ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ)‖ =
          rho * q_prime_py eta sigma := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hQp]
      have hIσD : ‖Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s‖ =
          sigma * ‖Dpoly eta sigma rho s‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hsigma]
      calc ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
          Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s‖
          ≤ ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ)‖ +
            ‖Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s‖ := norm_sub_le _ _
        _ ≤ rho * q_prime_py eta sigma + sigma *
            (rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| +
              rho * q_prime_py eta sigma * (y + r)) := by
            rw [hIQ, hIσD]
            have := mul_le_mul_of_nonneg_left hDs hsigma.le
            linarith
    have hft : ‖((t : ℝ) : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    rw [hft]
    have hnn1 : (0 : ℝ) ≤ ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
        Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s‖ * t :=
      mul_nonneg (norm_nonneg _) htpos.le
    have hstep1 : ‖Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
        Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s‖ * t ≤
        (rho * q_prime_py eta sigma + sigma *
          (rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| +
            rho * q_prime_py eta sigma * (y + r))) * t :=
      mul_le_mul_of_nonneg_right hf1 htpos.le
    exact mul_le_mul hstep1 hEfac (norm_nonneg _) (by positivity)
  -- piece 2 budget: `≤ (1/5 + 2/100)·σQxt`
  have hn2bud : (rho * q_prime_py eta sigma + sigma *
      (rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| +
        rho * q_prime_py eta sigma * (y + r))) * t * (2 * (sigma * r)) ≤
      1 / 5 * (sigma * (rho * q_prime_py eta sigma) * x * t) +
        2 / 100 * (sigma * (rho * q_prime_py eta sigma) * x * t) := by
    rw [hσr]
    -- now the factor `2·(σr)` is the literal `2·(1/10) = 1/5`
    have hyt : sigma * (rho * q_prime_py eta sigma) * y * t ≤
        1 / 20 * (sigma * (rho * q_prime_py eta sigma) * x * t) := by
      have h20 := mul_le_mul_of_nonneg_left hy20
        (mul_nonneg (mul_nonneg hsigma.le hQp.le) htpos.le)
      linarith [h20]
    have hσQrt : sigma * (rho * q_prime_py eta sigma) * r * t =
        1 / 10 * (rho * q_prime_py eta sigma * t) := by
      calc sigma * (rho * q_prime_py eta sigma) * r * t
          = (sigma * r) * (rho * q_prime_py eta sigma * t) := by ring
        _ = 1 / 10 * (rho * q_prime_py eta sigma * t) := by rw [hσr]
    have hconst : (rho * q_prime_py eta sigma + 2 * sigma * |guessP2 eta sigma rho| +
        1 / 10 * (rho * q_prime_py eta sigma)) * t ≤
        1 / 20 * (sigma * (rho * q_prime_py eta sigma) * x * t) := by
      have h8t := mul_le_mul_of_nonneg_right hx8 htpos.le
      linarith [h8t]
    linarith [hyt, hconst, hσQrt]
  -- piece 3: the `D`-drift
  have hn3 : ‖Complex.I * (sigma : ℂ) *
      (Dpoly eta sigma rho (k1_guess eta sigma rho n) - Dpoly eta sigma rho s) *
      ((t : ℝ) : ℂ)‖ ≤ sigma * (rho * q_prime_py eta sigma * r) * t := by
    have hnorm : ‖Complex.I * (sigma : ℂ) *
        (Dpoly eta sigma rho (k1_guess eta sigma rho n) - Dpoly eta sigma rho s) *
        ((t : ℝ) : ℂ)‖ = sigma *
        ‖Dpoly eta sigma rho (k1_guess eta sigma rho n) - Dpoly eta sigma rho s‖ * t := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsigma,
        abs_of_pos htpos]
    rw [hnorm]
    have hdd : ‖Dpoly eta sigma rho (k1_guess eta sigma rho n) - Dpoly eta sigma rho s‖ ≤
        rho * q_prime_py eta sigma * r := by
      rw [Dpoly_sub_norm_eq eta sigma rho _ _ hQp.le]
      have hks : ‖k1_guess eta sigma rho n - s‖ ≤ r := by
        rw [norm_sub_rev]; exact hsK
      exact mul_le_mul_of_nonneg_left hks hQp.le
    have := mul_le_mul_of_nonneg_left hdd hsigma.le
    exact mul_le_mul_of_nonneg_right this htpos.le
  -- piece 3 budget: `≤ (1/100)·σQxt`
  have hn3bud : sigma * (rho * q_prime_py eta sigma * r) * t ≤
      1 / 100 * (sigma * (rho * q_prime_py eta sigma) * x * t) := by
    have hσQrt : sigma * (rho * q_prime_py eta sigma * r) * t =
        1 / 10 * (rho * q_prime_py eta sigma * t) := by
      calc sigma * (rho * q_prime_py eta sigma * r) * t
          = (sigma * r) * (rho * q_prime_py eta sigma * t) := by ring
        _ = 1 / 10 * (rho * q_prime_py eta sigma * t) := by rw [hσr]
    rw [hσQrt]
    have h10t := mul_le_mul_of_nonneg_right hx10
      (mul_nonneg hQp.le htpos.le)
    linarith [h10t]
  -- assemble
  rw [hdecomp]
  calc ‖((3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
          2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
          Complex.I * (guessP1 eta sigma rho : ℂ)) -
        (3 * Complex.I * s ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * s +
          Complex.I * (guessP1 eta sigma rho : ℂ))) +
      ((Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
          Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s) * ((t : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * (s - k1_guess eta sigma rho n) * sigma) - 1)) +
      Complex.I * (sigma : ℂ) *
        (Dpoly eta sigma rho (k1_guess eta sigma rho n) - Dpoly eta sigma rho s) *
        ((t : ℝ) : ℂ)‖
      ≤ ‖(3 * Complex.I * (k1_guess eta sigma rho n) ^ 2 -
          2 * (guessP0 eta sigma rho : ℂ) * (k1_guess eta sigma rho n) +
          Complex.I * (guessP1 eta sigma rho : ℂ)) -
        (3 * Complex.I * s ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * s +
          Complex.I * (guessP1 eta sigma rho : ℂ))‖ +
        ‖(Complex.I * ((rho * q_prime_py eta sigma : ℝ) : ℂ) -
          Complex.I * (sigma : ℂ) * Dpoly eta sigma rho s) * ((t : ℝ) : ℂ) *
          (Complex.exp (-Complex.I * (s - k1_guess eta sigma rho n) * sigma) - 1)‖ +
        ‖Complex.I * (sigma : ℂ) *
          (Dpoly eta sigma rho (k1_guess eta sigma rho n) - Dpoly eta sigma rho s) *
          ((t : ℝ) : ℂ)‖ := norm_add₃_le
    _ ≤ sigma / 4 * (rho * q_prime_py eta sigma) * x * t := by
        have e1 := le_trans hn1 hn1bud
        have e2 := le_trans hn2 hn2bud
        have e3 := le_trans hn3 hn3bud
        linarith [e1, e2, e3]

/-! ### The chord step bound at the guess -/

set_option maxHeartbeats 800000 in
-- Raised limit: a single long estimate chain over large `Npoly`/`Dpoly` norm atoms.
/-- **`‖G(k1_guess n)‖ ≤ (1/40)·Q·x·t`** under explicit thresholds: after the phase kill,
`G(k1) = [N(k1)−N(x)] − t·[D(k1)−D(x)] + [N(x)−t·D(x)]`; the first two pieces are the vertical
drifts (bounded via the sublinear `y`-caps `hy120`/`hydN`), and the third is the algebraic
`norm_sub_ratio_mul_le` residual, `O(x²)` against the `O(x³)` budget (threshold `hx11`). -/
theorem G_baxter_k1_norm_le (eta sigma rho : ℝ) (n : ℕ)
    (hsigma : 0 < sigma) (hQp : 0 < rho * q_prime_py eta sigma)
    {x y : ℝ}
    (hxdef : x = 2 * Real.pi * n / sigma)
    (hydef : y = (k1_guess eta sigma rho n).im)
    (hx1 : 1 ≤ x) (hy0 : 0 ≤ y) (hy120 : 120 * y ≤ x)
    (hydN : 240 * guessCN eta sigma rho * guessCD eta sigma rho * y ≤
      rho * q_prime_py eta sigma * x)
    (hxB : 2 * |guessP1 eta sigma rho| ≤ x)
    (hxR : 2 * guessCR eta sigma rho / (rho * q_prime_py eta sigma) ≤ x)
    (hx11 : 480 * guessCI eta sigma rho * guessCD eta sigma rho ≤
      (rho * q_prime_py eta sigma) ^ 2 * x) :
    ‖G_baxter eta sigma rho (k1_guess eta sigma rho n)‖ ≤
      1 / 40 * (rho * q_prime_py eta sigma * x *
        (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hyx : y ≤ x := by linarith
  have hNpos : 0 < ‖Npoly eta sigma rho (x : ℂ)‖ := by
    have := Npoly_x_norm_half_cubic eta sigma rho hx1 hxB
    nlinarith [pow_pos hx0 3]
  have hDpos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := by
    have h := Dpoly_norm_lower eta sigma rho x
    nlinarith [mul_pos hQp hx0]
  have hNpos' : 0 < ‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ := by
    rw [← hxdef]; exact hNpos
  have hDpos' : 0 < ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ := by
    rw [← hxdef]; exact hDpos
  have hP := exp_at_k1_guess eta sigma rho hsigma n hNpos' hDpos'
  rw [← hxdef] at hP
  set t : ℝ := ‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖ with htdef
  have htpos : 0 < t := div_pos hNpos hDpos
  have ht2 := t_ratio_lower eta sigma rho hQp hx1 hxB
  rw [← htdef] at ht2
  have hgCD : 0 < guessCD eta sigma rho := guessCD_pos eta sigma rho hQp
  have hcN : 0 < guessCN eta sigma rho := guessCN_pos eta sigma rho
  have hK : k1_guess eta sigma rho n = (x : ℂ) + (y : ℂ) * Complex.I := by
    rw [hxdef, hydef]; exact k1_guess_eq eta sigma rho n
  -- the phase-killed three-piece decomposition
  have hG : G_baxter eta sigma rho (k1_guess eta sigma rho n) =
      (Npoly eta sigma rho (k1_guess eta sigma rho n) - Npoly eta sigma rho (x : ℂ)) +
      (-(((t : ℝ) : ℂ) * (Dpoly eta sigma rho (k1_guess eta sigma rho n) -
        Dpoly eta sigma rho (x : ℂ)))) +
      (Npoly eta sigma rho (x : ℂ) - ((t : ℝ) : ℂ) * Dpoly eta sigma rho (x : ℂ)) := by
    unfold G_baxter
    rw [hP]
    ring
  -- piece 1: the `N` vertical drift
  have hT1 : ‖Npoly eta sigma rho (k1_guess eta sigma rho n) -
      Npoly eta sigma rho (x : ℂ)‖ ≤ guessCN eta sigma rho * x ^ 2 * y := by
    have hvd := Npoly_vertical_diff_le eta sigma rho hx0.le hy0
    rw [hK]
    have hA0 : (0 : ℝ) ≤ |guessP0 eta sigma rho| := abs_nonneg _
    have hB0 : (0 : ℝ) ≤ |guessP1 eta sigma rho| := abs_nonneg _
    have hparen : 3 * (x + y) ^ 2 + 2 * |guessP0 eta sigma rho| * (x + y) +
        |guessP1 eta sigma rho| ≤ guessCN eta sigma rho * x ^ 2 := by
      unfold guessCN
      have h2 : (x + y) ^ 2 ≤ 4 * x ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - y)
          (by linarith : (0 : ℝ) ≤ 3 * x + y)]
      have h3 : 2 * |guessP0 eta sigma rho| * (x + y) ≤
          4 * |guessP0 eta sigma rho| * x ^ 2 := by
        nlinarith [mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ x - y),
          mul_nonneg (mul_nonneg hA0 hx0.le) (by linarith : (0 : ℝ) ≤ x - 1)]
      have h5 : |guessP1 eta sigma rho| ≤ |guessP1 eta sigma rho| * x ^ 2 := by
        nlinarith [mul_nonneg hB0
          (by nlinarith [sq_nonneg (x - 1)] : (0 : ℝ) ≤ x ^ 2 - 1)]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hparen hy0
    linarith [hvd, hmul]
  have hT1bud : guessCN eta sigma rho * x ^ 2 * y ≤
      1 / 120 * (rho * q_prime_py eta sigma * x * t) := by
    have h1 : 240 * guessCN eta sigma rho * guessCD eta sigma rho * y * x ^ 2 ≤
        rho * q_prime_py eta sigma * x * x ^ 2 :=
      mul_le_mul_of_nonneg_right hydN (sq_nonneg x)
    have h2 : rho * q_prime_py eta sigma * x * x ^ 2 ≤
        rho * q_prime_py eta sigma * x * (2 * guessCD eta sigma rho * t) :=
      mul_le_mul_of_nonneg_left ht2 (mul_nonneg hQp.le hx0.le)
    have h3 : (2 * guessCD eta sigma rho) * (120 * (guessCN eta sigma rho * x ^ 2 * y)) ≤
        (2 * guessCD eta sigma rho) * (rho * q_prime_py eta sigma * x * t) := by
      linarith [h1, h2]
    have h4 := le_of_mul_le_mul_left h3
      (by positivity : (0 : ℝ) < 2 * guessCD eta sigma rho)
    linarith [h4]
  -- piece 2: the `D` vertical drift
  have hT2 : ‖-(((t : ℝ) : ℂ) * (Dpoly eta sigma rho (k1_guess eta sigma rho n) -
      Dpoly eta sigma rho (x : ℂ)))‖ ≤ t * (rho * q_prime_py eta sigma * y) := by
    rw [norm_neg, norm_mul]
    have hft : ‖((t : ℝ) : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    rw [hft]
    have hk1x : k1_guess eta sigma rho n - (x : ℂ) = (y : ℂ) * Complex.I := by
      rw [hK]; ring
    have hdd : ‖Dpoly eta sigma rho (k1_guess eta sigma rho n) -
        Dpoly eta sigma rho (x : ℂ)‖ = rho * q_prime_py eta sigma * y := by
      rw [Dpoly_sub_norm_eq eta sigma rho _ _ hQp.le, hk1x, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]
    rw [hdd]
  have hT2bud : t * (rho * q_prime_py eta sigma * y) ≤
      1 / 120 * (rho * q_prime_py eta sigma * x * t) := by
    have h := mul_le_mul_of_nonneg_left hy120 (mul_nonneg hQp.le htpos.le)
    linarith [h]
  -- piece 3: the algebraic modulus-matched residual
  have hwre : 0 ≤ wRe eta sigma rho x := by
    have hx_le_sq : x ≤ x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1) hx0.le]
    have hxR2 : 2 * guessCR eta sigma rho ≤ rho * q_prime_py eta sigma * x ^ 2 := by
      rw [div_le_iff₀ hQp] at hxR
      have := mul_le_mul_of_nonneg_left hx_le_sq hQp.le
      linarith [hxR, this]
    have hhalf := wRe_half_ge_of eta sigma rho hx0.le hQp.le hxR2
    have h4 : (0 : ℝ) ≤ rho * q_prime_py eta sigma * x ^ 4 :=
      mul_nonneg hQp.le (pow_nonneg hx0.le 4)
    linarith [hhalf, h4]
  have hDne : Dpoly eta sigma rho (x : ℂ) ≠ 0 := norm_pos_iff.mp hDpos
  have hT3 : ‖Npoly eta sigma rho (x : ℂ) -
      ((t : ℝ) : ℂ) * Dpoly eta sigma rho (x : ℂ)‖ ≤
      2 * (guessCI eta sigma rho * x ^ 3) / (rho * q_prime_py eta sigma * x) := by
    rw [htdef]
    have h := Npoly_sub_ratio_Dpoly_le eta sigma rho x hDne hwre
    have hwim := wIm_abs_le_of eta sigma rho hx1 hQp.le
    have hDlow := Dpoly_norm_lower eta sigma rho x
    have h2 : 2 * |wIm eta sigma rho x| / ‖Dpoly eta sigma rho (x : ℂ)‖ ≤
        2 * (guessCI eta sigma rho * x ^ 3) / (rho * q_prime_py eta sigma * x) :=
      div_le_div_bound (by linarith)
        (mul_nonneg (by norm_num) (mul_nonneg (guessCI_nonneg eta sigma rho hQp.le)
          (pow_nonneg hx0.le 3)))
        (mul_pos hQp hx0) hDlow
    exact le_trans h h2
  have hT3bud : 2 * (guessCI eta sigma rho * x ^ 3) / (rho * q_prime_py eta sigma * x) ≤
      1 / 120 * (rho * q_prime_py eta sigma * x * t) := by
    rw [div_le_iff₀ (mul_pos hQp hx0)]
    have h1 : 480 * guessCI eta sigma rho * guessCD eta sigma rho * x ^ 2 ≤
        (rho * q_prime_py eta sigma) ^ 2 * x * x ^ 2 :=
      mul_le_mul_of_nonneg_right hx11 (sq_nonneg x)
    have h2 : (rho * q_prime_py eta sigma) ^ 2 * x * x ^ 2 ≤
        (rho * q_prime_py eta sigma) ^ 2 * x * (2 * guessCD eta sigma rho * t) :=
      mul_le_mul_of_nonneg_left ht2 (mul_nonneg (pow_nonneg hQp.le 2) hx0.le)
    have h3 : (2 * guessCD eta sigma rho) * (240 * (guessCI eta sigma rho * x ^ 2)) ≤
        (2 * guessCD eta sigma rho) * ((rho * q_prime_py eta sigma) ^ 2 * x * t) := by
      linarith [h1, h2]
    have h4 := le_of_mul_le_mul_left h3
      (by positivity : (0 : ℝ) < 2 * guessCD eta sigma rho)
    have h5 := mul_le_mul_of_nonneg_right h4 hx0.le
    linarith [h5]
  -- assemble
  rw [hG]
  refine le_trans norm_add₃_le ?_
  have e1 := le_trans hT1 hT1bud
  have e2 := le_trans hT2 hT2bud
  have e3 := le_trans hT3 hT3bud
  linarith [e1, e2, e3]

/-! ### The threshold/eventually pass -/

set_option maxHeartbeats 1000000 in
-- Raised limit: one pass assembles eleven eventual thresholds plus three core estimates.
/-- **All chord-family conditions hold eventually**: beyond an explicit index threshold `N`,
the frozen derivative at `k1_guess n` is nonzero, the chord bound `‖1 − G′(s)/G′(k1)‖ ≤ 1/2`
holds on the disk of radius `1/(10σ)`, and the chord step satisfies
`‖G(k1)/G′(k1)‖ ≤ (1/(10σ))·(1 − 1/2)`. All `x = 2πn/σ` thresholds are linear (bundled via
`Filter.eventually_ge_atTop`), and the sublinear cap `Im(k1_guess n) ≤ ε·x` comes from
`eventually_log_cap` exactly as in `k1_guess_hstep_eventually`. -/
theorem chord_conditions_eventually (eta sigma rho : ℝ)
    (hsigma : 0 < sigma) (hQp : 0 < rho * q_prime_py eta sigma) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) ≠ 0 ∧
      (∀ s ∈ Metric.closedBall (k1_guess eta sigma rho n) (1 / (10 * sigma)),
        ‖1 - G_baxter_deriv eta sigma rho s /
            G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n)‖ ≤ 1 / 2) ∧
      ‖G_baxter eta sigma rho (k1_guess eta sigma rho n) /
          G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n)‖ ≤
        1 / (10 * sigma) * (1 - 1 / 2) := by
  have hcN := guessCN_pos eta sigma rho
  have hcD := guessCD_pos eta sigma rho hQp
  have hcU := guessCU_pos eta sigma rho
  -- the sublinear cap parameter
  set ε : ℝ := min (1 / 120)
    (rho * q_prime_py eta sigma / (240 * guessCN eta sigma rho * guessCD eta sigma rho))
    with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    refine lt_min (by norm_num) ?_
    exact div_pos hQp (by positivity)
  have hε120 : ε ≤ 1 / 120 := by rw [hεdef]; exact min_le_left _ _
  have hεQ : ε ≤ rho * q_prime_py eta sigma /
      (240 * guessCN eta sigma rho * guessCD eta sigma rho) := by
    rw [hεdef]; exact min_le_right _ _
  -- eventual thresholds in the real variable x
  have hlogcap := eventually_log_cap
    (Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma))) (sigma * ε)
    (mul_pos hsigma hε0)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (1 ≤ x) ∧ (2 * |guessP1 eta sigma rho| ≤ x) ∧
      (2 * guessCR eta sigma rho / (rho * q_prime_py eta sigma) ≤ x) ∧
      (2 * guessCD eta sigma rho ≤ x) ∧
      (4 / sigma ≤ x) ∧
      (8 * guessCN eta sigma rho * guessCD eta sigma rho /
        (sigma * (rho * q_prime_py eta sigma)) ≤ x) ∧
      ((22 * (rho * q_prime_py eta sigma) + 40 * sigma * |guessP2 eta sigma rho|) /
        (sigma * (rho * q_prime_py eta sigma)) ≤ x) ∧
      (100 * guessCD eta sigma rho * (1 / (10 * sigma)) *
          (12 + 3 * (1 / (10 * sigma)) + 2 * |guessP0 eta sigma rho|) /
        (sigma * (rho * q_prime_py eta sigma)) ≤ x) ∧
      (10 / sigma ≤ x) ∧
      (480 * guessCI eta sigma rho * guessCD eta sigma rho /
        (rho * q_prime_py eta sigma) ^ 2 ≤ x) ∧
      (Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma)) + 2 * Real.log x ≤
        sigma * ε * x) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop (2 * |guessP1 eta sigma rho|),
      Filter.eventually_ge_atTop
        (2 * guessCR eta sigma rho / (rho * q_prime_py eta sigma)),
      Filter.eventually_ge_atTop (2 * guessCD eta sigma rho),
      Filter.eventually_ge_atTop (4 / sigma),
      Filter.eventually_ge_atTop (8 * guessCN eta sigma rho * guessCD eta sigma rho /
        (sigma * (rho * q_prime_py eta sigma))),
      Filter.eventually_ge_atTop
        ((22 * (rho * q_prime_py eta sigma) + 40 * sigma * |guessP2 eta sigma rho|) /
          (sigma * (rho * q_prime_py eta sigma))),
      Filter.eventually_ge_atTop (100 * guessCD eta sigma rho * (1 / (10 * sigma)) *
          (12 + 3 * (1 / (10 * sigma)) + 2 * |guessP0 eta sigma rho|) /
        (sigma * (rho * q_prime_py eta sigma))),
      Filter.eventually_ge_atTop (10 / sigma),
      Filter.eventually_ge_atTop (480 * guessCI eta sigma rho * guessCD eta sigma rho /
        (rho * q_prime_py eta sigma) ^ 2),
      hlogcap] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  -- push the thresholds along n ↦ 2πn/σ → ∞
  have htends : Filter.Tendsto (fun n : ℕ => 2 * Real.pi * (n : ℝ) / sigma)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hsigma
      (Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htends.eventually hev)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hx1, hxB, hxR, hxD, hx6', hx7', hx8', hx9', hx10', hx11', hlog⟩ := hN n hn
  -- basic facts about x = 2πn/σ
  have hx0 : (0 : ℝ) < 2 * Real.pi * (n : ℝ) / sigma := lt_of_lt_of_le one_pos hx1
  have hx_le_sq : 2 * Real.pi * (n : ℝ) / sigma ≤ (2 * Real.pi * (n : ℝ) / sigma) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ) / sigma - 1) hx0.le]
  have hσQ : 0 < sigma * (rho * q_prime_py eta sigma) := mul_pos hsigma hQp
  -- convert the divided thresholds to multiplied form
  have hx6 : 4 ≤ sigma * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [div_le_iff₀ hsigma] at hx6'; linarith
  have hx7 : 8 * guessCN eta sigma rho * guessCD eta sigma rho ≤
      sigma * (rho * q_prime_py eta sigma) * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [div_le_iff₀ hσQ] at hx7'; linarith
  have hx8 : 22 * (rho * q_prime_py eta sigma) + 40 * sigma * |guessP2 eta sigma rho| ≤
      sigma * (rho * q_prime_py eta sigma) * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [div_le_iff₀ hσQ] at hx8'; linarith
  have hx9 : 100 * guessCD eta sigma rho * (1 / (10 * sigma)) *
      (12 + 3 * (1 / (10 * sigma)) + 2 * |guessP0 eta sigma rho|) ≤
      sigma * (rho * q_prime_py eta sigma) * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [div_le_iff₀ hσQ] at hx9'; linarith
  have hx10 : 10 ≤ sigma * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [div_le_iff₀ hsigma] at hx10'; linarith
  have hx11 : 480 * guessCI eta sigma rho * guessCD eta sigma rho ≤
      (rho * q_prime_py eta sigma) ^ 2 * (2 * Real.pi * (n : ℝ) / sigma) := by
    rw [div_le_iff₀ (pow_pos hQp 2)] at hx11'; linarith
  -- lowN/lowD positivity
  have hxB2 : 2 * |guessP1 eta sigma rho| ≤ (2 * Real.pi * (n : ℝ) / sigma) ^ 2 := by
    linarith
  have hlowN := lowN_half_ge_of eta sigma rho hx0 hxB2
  have hx3 : (0 : ℝ) < (2 * Real.pi * (n : ℝ) / sigma) ^ 3 := pow_pos hx0 3
  have hlowN_pos : 0 < lowN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) := by linarith
  have hlowD_pos : 0 < lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) := by
    unfold lowD
    exact mul_pos hQp hx0
  -- 0 ≤ Im(k1_guess n) via the upD ≤ lowN gap
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
  -- the sublinear cap Im(k1_guess n) ≤ ε·x
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
  have hycap : (k1_guess eta sigma rho n).im ≤ ε * (2 * Real.pi * (n : ℝ) / sigma) := by
    have hcap : Real.log (upN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) /
        lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma)) ≤
        sigma * ε * (2 * Real.pi * (n : ℝ) / sigma) := by
      rw [hlog2] at hlog1
      linarith [hlog, hlog1]
    have hdiv : Real.log (upN eta sigma rho (2 * Real.pi * (n : ℝ) / sigma) /
        lowD eta sigma rho (2 * Real.pi * (n : ℝ) / sigma)) / sigma ≤
        ε * (2 * Real.pi * (n : ℝ) / sigma) := by
      rw [div_le_iff₀ hsigma]
      linarith [hcap]
    linarith [him_le, hdiv]
  -- the y-caps consumed by the core lemmas
  have hy120 : 120 * (k1_guess eta sigma rho n).im ≤ 2 * Real.pi * (n : ℝ) / sigma := by
    linarith [hycap, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 120 * ε) hx0.le]
  have hy20 : 20 * (k1_guess eta sigma rho n).im ≤ 2 * Real.pi * (n : ℝ) / sigma := by
    linarith [hy120, hy0]
  have hyx : (k1_guess eta sigma rho n).im ≤ 2 * Real.pi * (n : ℝ) / sigma := by
    linarith [hy120, hy0]
  have hydN : 240 * guessCN eta sigma rho * guessCD eta sigma rho *
      (k1_guess eta sigma rho n).im ≤
      rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma) := by
    have hc240 : (0 : ℝ) < 240 * guessCN eta sigma rho * guessCD eta sigma rho := by
      positivity
    have h1 := mul_le_mul_of_nonneg_left hycap hc240.le
    rw [le_div_iff₀ hc240] at hεQ
    have h2 := mul_le_mul_of_nonneg_right hεQ hx0.le
    linarith [h1, h2]
  -- positivity of the frozen-derivative budget
  have hNpos : 0 < ‖Npoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖ := by
    have := Npoly_x_norm_half_cubic eta sigma rho hx1 hxB
    linarith [hx3]
  have hDpos : 0 < ‖Dpoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖ := by
    have h := Dpoly_norm_lower eta sigma rho (2 * Real.pi * (n : ℝ) / sigma)
    linarith [mul_pos hQp hx0]
  have htpos : 0 < ‖Npoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖ /
      ‖Dpoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖ :=
    div_pos hNpos hDpos
  -- the three core bounds
  have hlower := G_baxter_deriv_k1_norm_lower eta sigma rho n hsigma hQp rfl rfl
    hx1 hy0 hyx hxB hx6 hx7
  have hden_pos : 0 < sigma / 2 * (rho * q_prime_py eta sigma) *
      (2 * Real.pi * (n : ℝ) / sigma) *
      (‖Npoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖ /
        ‖Dpoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖) := by
    have h1 : (0 : ℝ) < sigma / 2 * (rho * q_prime_py eta sigma) *
        (2 * Real.pi * (n : ℝ) / sigma) := by positivity
    exact mul_pos h1 htpos
  have hFp1_pos : 0 < ‖G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n)‖ :=
    lt_of_lt_of_le hden_pos hlower
  have hFp1_ne : G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) ≠ 0 :=
    norm_pos_iff.mp hFp1_pos
  refine ⟨hFp1_ne, fun s hs => ?_, ?_⟩
  · -- the chord bound on the disk
    have hdiff := G_baxter_deriv_ball_diff_le eta sigma rho n hsigma hQp rfl rfl
      hx1 hy0 hy20 hxB hx8 hx9 hx10 hs
    have h1 : (1 : ℂ) - G_baxter_deriv eta sigma rho s /
        G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) =
        (G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) -
          G_baxter_deriv eta sigma rho s) /
          G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n) := by
      field_simp
    rw [h1, norm_div, div_le_iff₀ hFp1_pos]
    linarith [hdiff, hlower]
  · -- the chord step
    have hGle := G_baxter_k1_norm_le eta sigma rho n hsigma hQp rfl rfl
      hx1 hy0 hy120 hydN hxB hxR hx11
    rw [norm_div, div_le_iff₀ hFp1_pos]
    have hc : 1 / (10 * sigma) * (1 - 1 / 2) *
        (sigma / 2 * (rho * q_prime_py eta sigma) * (2 * Real.pi * (n : ℝ) / sigma) *
          (‖Npoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖ /
            ‖Dpoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖)) =
        1 / 40 * (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma) *
          (‖Npoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖ /
            ‖Dpoly eta sigma rho ((2 * Real.pi * (n : ℝ) / sigma : ℝ) : ℂ)‖)) := by
      field_simp
      ring
    have h2 := mul_le_mul_of_nonneg_left hlower
      (by positivity : (0 : ℝ) ≤ 1 / (10 * sigma) * (1 - 1 / 2))
    rw [hc] at h2
    linarith [hGle, h2]

/-! ### Separation and the family -/

/-- **Separation of the guesses**: distinct centres are farther apart than `2r = 1/(5σ)` —
their real parts differ by a nonzero multiple of `2π/σ`, and `1/5 < 2π`
(mirrors `G_baxter_pole_family_exists`'s spacing argument). -/
theorem k1_guess_dist_gt (eta sigma rho : ℝ) (hsigma : 0 < sigma)
    {m n : ℕ} (hmn : m ≠ n) :
    2 * (1 / (10 * sigma)) < dist (k1_guess eta sigma rho m) (k1_guess eta sigma rho n) := by
  have hre : (k1_guess eta sigma rho m).re - (k1_guess eta sigma rho n).re =
      2 * Real.pi / sigma * ((m : ℝ) - (n : ℝ)) := by
    rw [k1_guess_re, k1_guess_re]
    ring
  have hnat : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
    have hmm : (m : ℤ) - (n : ℤ) ≠ 0 := by
      simpa using sub_ne_zero.mpr (fun h => hmn (by exact_mod_cast h))
    have h1 : (1 : ℤ) ≤ |(m : ℤ) - (n : ℤ)| := Int.one_le_abs hmm
    have h2 : ((|(m : ℤ) - (n : ℤ)| : ℤ) : ℝ) = |(m : ℝ) - (n : ℝ)| := by push_cast; ring
    rw [← h2]
    exact_mod_cast h1
  have hre2 : |(k1_guess eta sigma rho m).re - (k1_guess eta sigma rho n).re| =
      2 * Real.pi / sigma * |(m : ℝ) - (n : ℝ)| := by
    rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / sigma)]
  have hreabs : 2 * Real.pi / sigma ≤
      |(k1_guess eta sigma rho m).re - (k1_guess eta sigma rho n).re| := by
    rw [hre2]
    calc 2 * Real.pi / sigma = 2 * Real.pi / sigma * 1 := by ring
      _ ≤ 2 * Real.pi / sigma * |(m : ℝ) - (n : ℝ)| :=
          mul_le_mul_of_nonneg_left hnat (by positivity)
  have hdistre : |(k1_guess eta sigma rho m - k1_guess eta sigma rho n).re| ≤
      ‖k1_guess eta sigma rho m - k1_guess eta sigma rho n‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at hdistre
  rw [dist_eq_norm]
  have hgap : 2 * (1 / (10 * sigma)) < 2 * Real.pi / sigma := by
    have hpi : (1 : ℝ) / 5 < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h5 : (0 : ℝ) < (2 * Real.pi - 1 / 5) / sigma := div_pos (by linarith) hsigma
    have heq2 : 2 * Real.pi / sigma - 2 * (1 / (10 * sigma)) =
        (2 * Real.pi - 1 / 5) / sigma := by
      field_simp
      ring
    linarith [h5, heq2]
  linarith [hreabs, hdistre, hgap]

/-- **POLE.9 (main construction)**: a concrete `ChordPoleFamily (G_baxter η σ ρ)` for physical
parameters — centres `k1_guess`, radius `r = 1/(10σ)`, contraction constant `K = 1/2`, index
threshold from `chord_conditions_eventually`. This is the shared Banach obligation of
POLE.3/MZERO.5, discharged concretely on the `G_baxter` side. -/
theorem chordPoleFamily_G_baxter_exists {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    Nonempty (FMSA.BanachPoleFamily.ChordPoleFamily (G_baxter eta sigma rho)) := by
  have hQp : 0 < rho * q_prime_py eta sigma := baxterMu_pos heta0 heta1 hsigma hrho
  obtain ⟨N, hN⟩ := chord_conditions_eventually eta sigma rho hsigma hQp
  have hKcoe : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  exact ⟨{
    N := N
    s1 := fun n => k1_guess eta sigma rho n
    Fp1 := fun n => G_baxter_deriv eta sigma rho (k1_guess eta sigma rho n)
    F' := G_baxter_deriv eta sigma rho
    r := 1 / (10 * sigma)
    K := 1 / 2
    hr := by positivity
    hK1 := by
      rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one]
      norm_num
    hFp1 := fun n hn => (hN n hn).1
    hderiv := fun n _ s _ => G_baxter_hasDerivAt eta sigma rho s
    hbound := fun n hn s hs => by
      rw [hKcoe]
      exact (hN n hn).2.1 s hs
    hstep := fun n hn => by
      rw [hKcoe]
      exact (hN n hn).2.2
    hsep := fun m n _ _ hmn => k1_guess_dist_gt eta sigma rho hsigma hmn
  }⟩

/-- **POLE.3, discharged along the chord route**: `G_baxter` has infinitely many complex zeros
for physical parameters — `chordPoleFamily_G_baxter_exists` fires
`G_baxter_zeros_infinite_of_chordPoleFamily`. -/
theorem G_baxter_zeros_infinite_chord {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    {k : ℂ | G_baxter eta sigma rho k = 0}.Infinite :=
  (chordPoleFamily_G_baxter_exists heta0 heta1 hsigma hrho).elim fun fam =>
    G_baxter_zeros_infinite_of_chordPoleFamily fam

end

end FMSA.HardSphere
