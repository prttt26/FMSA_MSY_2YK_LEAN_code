/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterPoles

/-!
# Task POLE.7 — the derived log-lift pole guess `k1_guess` (cluster (a))

First Lean pass for `POLE.7` (discharging `POLE.3`'s `hstep`): the **fit-free derived guess**

  `k1_guess n := 2πn/σ + (i/σ)·log(‖Npoly(xₙ)‖/‖Dpoly(xₙ)‖)`,  `xₙ := 2πn/σ`,

(the modulus part of one `baxterPhi` application at the real point `xₙ`; supersedes `POLE.2`'s
numerically-fitted `2·ln(2πn/σ) − 2.12`), together with **cluster (a)** of the scoping's proof
plan: real-axis two-sided norm bounds for `Npoly`/`Dpoly` and the resulting `hk1re`/`hk1im`
facts. See `proof_notes_pole.md` Task `POLE.7` for the full (a)–(e) plan and the numerical
margins (residual `≈3.5·ln xₙ/xₙ`, minimal `N = 4/4/6/17` at `η=.05/.1/.3/.45`, `r=1`).

## The privacy bridge

`Npoly`/`Dpoly`'s coefficients `baxterP0/1/2` are `private` to `BaxterPoles.lean`, so this file
cannot *name* them — but privacy is a name-visibility constraint, not a kernel one: public
mirrors `guessP0/1/2` with **byte-identical bodies** are definitionally equal to them, so the
bridging identities `Npoly_eq_guess`/`Dpoly_eq_guess` close by `rfl` (delta-reduction). This is
a third pattern for the cross-file privacy constraint, complementing `POLE.5`'s existential
wrappers and `POLE.6`'s conclusion-tuple hypotheses.

## Results (cluster (a))

* `Npoly_eq_guess` / `Dpoly_eq_guess` — `rfl` bridges to the public-coefficient forms.
* `Dpoly_lead_eq` — the `Dpoly` leading coefficient is `guessP1 + 2·guessP2·σ = ρ·q_prime_py`
  (strictly positive for physical parameters) — the cancellation making `‖Dpoly(x)‖ ~ ρQ′·x`.
* `Npoly_ofReal` / `Dpoly_ofReal` (+ `_re`/`_im`) — real-axis `a + b·I` decompositions.
* `Npoly_norm_lower/upper`, `Dpoly_norm_lower/upper` — the two-sided bounds
  `x³ − |P1|·x ≤ ‖Npoly(x)‖ ≤ x³ + |P0|x² + |P1|x + 2|P2|`,
  `ρQ′·x ≤ ‖Dpoly(x)‖ ≤ ρQ′·x + 2|P2|` (`x ≥ 0`).
* `k1_guess_re` — `Re(k1_guess n) = 2πn/σ` **exactly** (`hk1re` by construction).
* `k1_guess_im_ge_of` — the `hk1im` workhorse: `r ≤ Im(k1_guess n)` follows from the explicit
  real inequality `exp(σr)·(ρQ′·xₙ + 2|P2|) ≤ xₙ³ − |P1|·xₙ` (an elementary polynomial-vs-
  constant threshold in `n`, dischargeable per parameter set or asymptotically in cluster (e)).

**Status:** cluster (a) ✓ (this file, axiom-clean); clusters (b)–(e) (segment/disk `|φ′|`
bounds, argument bound, branch safety, MVT assembly) are the follow-on passes.
-/

open MeasureTheory Real Set

namespace FMSA.HardSphere

noncomputable section

/-! ### Public mirrors of the private `baxterP0/1/2` (definitionally equal) -/

/-- Public mirror of `baxterP0` (byte-identical body ⇒ definitionally equal). -/
def guessP0 (eta sigma rho : ℝ) : ℝ :=
  rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma

/-- Public mirror of `baxterP1`. -/
def guessP1 (eta sigma rho : ℝ) : ℝ :=
  rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma

/-- Public mirror of `baxterP2`. -/
def guessP2 (eta _sigma rho : ℝ) : ℝ :=
  rho * q_doubleprime_py eta / 2

/-- **Privacy bridge for `Npoly`** — closes by `rfl` since `guessP0/1/2` are definitionally
the `private` `baxterP0/1/2`. -/
theorem Npoly_eq_guess (eta sigma rho : ℝ) (k : ℂ) :
    Npoly eta sigma rho k =
      Complex.I * k ^ 3 - (guessP0 eta sigma rho : ℂ) * k ^ 2 +
        Complex.I * (guessP1 eta sigma rho : ℂ) * k + 2 * (guessP2 eta sigma rho : ℂ) := rfl

/-- **Privacy bridge for `Dpoly`.** -/
theorem Dpoly_eq_guess (eta sigma rho : ℝ) (k : ℂ) :
    Dpoly eta sigma rho k =
      Complex.I * ((guessP1 eta sigma rho : ℂ) + 2 * (guessP2 eta sigma rho : ℂ) * sigma) * k +
        2 * (guessP2 eta sigma rho : ℂ) := rfl

/-- The `Dpoly` leading coefficient collapses to `ρ·Q′ > 0`: `P1 + 2P2σ = ρ·q_prime_py`. -/
theorem Dpoly_lead_eq (eta sigma rho : ℝ) :
    guessP1 eta sigma rho + 2 * guessP2 eta sigma rho * sigma = rho * q_prime_py eta sigma := by
  unfold guessP1 guessP2
  ring

/-! ### Real-axis `a + b·I` decompositions -/

/-- `Npoly` at a real point: `Npoly(x) = (−P0x² + 2P2) + (x³ + P1x)·i`. -/
theorem Npoly_ofReal (eta sigma rho x : ℝ) :
    Npoly eta sigma rho (x : ℂ) =
      ((-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho : ℝ) : ℂ) +
        ((x ^ 3 + guessP1 eta sigma rho * x : ℝ) : ℂ) * Complex.I := by
  rw [Npoly_eq_guess]
  push_cast
  ring

theorem Npoly_ofReal_re (eta sigma rho x : ℝ) :
    (Npoly eta sigma rho (x : ℂ)).re =
      -(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho := by
  rw [Npoly_ofReal]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem Npoly_ofReal_im (eta sigma rho x : ℝ) :
    (Npoly eta sigma rho (x : ℂ)).im = x ^ 3 + guessP1 eta sigma rho * x := by
  rw [Npoly_ofReal]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `Dpoly` at a real point: `Dpoly(x) = 2P2 + (ρQ′·x)·i` (using `Dpoly_lead_eq`). -/
theorem Dpoly_ofReal (eta sigma rho x : ℝ) :
    Dpoly eta sigma rho (x : ℂ) =
      ((2 * guessP2 eta sigma rho : ℝ) : ℂ) +
        ((rho * q_prime_py eta sigma * x : ℝ) : ℂ) * Complex.I := by
  rw [Dpoly_eq_guess, ← Dpoly_lead_eq eta sigma rho]
  push_cast
  ring

theorem Dpoly_ofReal_re (eta sigma rho x : ℝ) :
    (Dpoly eta sigma rho (x : ℂ)).re = 2 * guessP2 eta sigma rho := by
  rw [Dpoly_ofReal]; simp

theorem Dpoly_ofReal_im (eta sigma rho x : ℝ) :
    (Dpoly eta sigma rho (x : ℂ)).im = rho * q_prime_py eta sigma * x := by
  rw [Dpoly_ofReal]; simp

/-! ### Cluster (a): two-sided real-axis norm bounds -/

/-- Lower bound `x³ − |P1|·x ≤ ‖Npoly(x)‖` for `x ≥ 0` (via the imaginary part). -/
theorem Npoly_norm_lower (eta sigma rho : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ 3 - |guessP1 eta sigma rho| * x ≤ ‖Npoly eta sigma rho (x : ℂ)‖ := by
  have him : |(Npoly eta sigma rho (x : ℂ)).im| ≤ ‖Npoly eta sigma rho (x : ℂ)‖ :=
    Complex.abs_im_le_norm _
  rw [Npoly_ofReal_im] at him
  have habs : x ^ 3 - |guessP1 eta sigma rho| * x ≤ |x ^ 3 + guessP1 eta sigma rho * x| := by
    have h1 : -(|guessP1 eta sigma rho| * x) ≤ guessP1 eta sigma rho * x := by
      have := neg_abs_le (guessP1 eta sigma rho)
      nlinarith [abs_nonneg (guessP1 eta sigma rho)]
    have h2 : x ^ 3 + guessP1 eta sigma rho * x ≤ |x ^ 3 + guessP1 eta sigma rho * x| :=
      le_abs_self _
    linarith
  linarith

/-- Upper bound `‖Npoly(x)‖ ≤ x³ + |P0|x² + |P1|x + 2|P2|` for `x ≥ 0`. -/
theorem Npoly_norm_upper (eta sigma rho : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖Npoly eta sigma rho (x : ℂ)‖ ≤
      x ^ 3 + |guessP0 eta sigma rho| * x ^ 2 + |guessP1 eta sigma rho| * x +
        2 * |guessP2 eta sigma rho| := by
  rw [Npoly_ofReal]
  have habs1 : |(-(guessP0 eta sigma rho)) * x ^ 2 + 2 * guessP2 eta sigma rho| ≤
      |guessP0 eta sigma rho| * x ^ 2 + 2 * |guessP2 eta sigma rho| := by
    calc |(-(guessP0 eta sigma rho)) * x ^ 2 + 2 * guessP2 eta sigma rho|
        ≤ |(-(guessP0 eta sigma rho)) * x ^ 2| + |2 * guessP2 eta sigma rho| := abs_add_le _ _
      _ = |guessP0 eta sigma rho| * x ^ 2 + 2 * |guessP2 eta sigma rho| := by
          rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hx 2)]
          norm_num
  have habs2 : |x ^ 3 + guessP1 eta sigma rho * x| ≤ x ^ 3 + |guessP1 eta sigma rho| * x := by
    calc |x ^ 3 + guessP1 eta sigma rho * x|
        ≤ |x ^ 3| + |guessP1 eta sigma rho * x| := abs_add_le _ _
      _ = x ^ 3 + |guessP1 eta sigma rho| * x := by
          rw [abs_of_nonneg (pow_nonneg hx 3), abs_mul, abs_of_nonneg hx]
  calc ‖((-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho : ℝ) : ℂ) +
        ((x ^ 3 + guessP1 eta sigma rho * x : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho : ℝ) : ℂ)‖ +
        ‖((x ^ 3 + guessP1 eta sigma rho * x : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |(-(guessP0 eta sigma rho)) * x ^ 2 + 2 * guessP2 eta sigma rho| +
        |x ^ 3 + guessP1 eta sigma rho * x| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (|guessP0 eta sigma rho| * x ^ 2 + 2 * |guessP2 eta sigma rho|) +
        (x ^ 3 + |guessP1 eta sigma rho| * x) := add_le_add habs1 habs2
    _ = x ^ 3 + |guessP0 eta sigma rho| * x ^ 2 + |guessP1 eta sigma rho| * x +
        2 * |guessP2 eta sigma rho| := by ring

/-- Lower bound `ρQ′·x ≤ ‖Dpoly(x)‖` (via the imaginary part; no sign hypotheses needed). -/
theorem Dpoly_norm_lower (eta sigma rho x : ℝ) :
    rho * q_prime_py eta sigma * x ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ := by
  have him : |(Dpoly eta sigma rho (x : ℂ)).im| ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ :=
    Complex.abs_im_le_norm _
  rw [Dpoly_ofReal_im] at him
  have h1 : rho * q_prime_py eta sigma * x ≤ |rho * q_prime_py eta sigma * x| := le_abs_self _
  linarith

/-- Upper bound `‖Dpoly(x)‖ ≤ ρQ′·x + 2|P2|` for `x ≥ 0`, `ρQ′ ≥ 0`. -/
theorem Dpoly_norm_upper (eta sigma rho : ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hQp : 0 ≤ rho * q_prime_py eta sigma) :
    ‖Dpoly eta sigma rho (x : ℂ)‖ ≤
      rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| := by
  rw [Dpoly_ofReal]
  calc ‖((2 * guessP2 eta sigma rho : ℝ) : ℂ) +
        ((rho * q_prime_py eta sigma * x : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((2 * guessP2 eta sigma rho : ℝ) : ℂ)‖ +
        ‖((rho * q_prime_py eta sigma * x : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |2 * guessP2 eta sigma rho| + |rho * q_prime_py eta sigma * x| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
    _ = rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg hQp hx)]
          norm_num
          ring

/-! ### The derived guess and its `hk1re`/`hk1im` facts -/

/-- **The derived log-lift guess** (`POLE.7`): `k1_guess n := xₙ + (i/σ)·log(‖N(xₙ)‖/‖D(xₙ)‖)`
with `xₙ := 2πn/σ` — the modulus part of one `baxterPhi` application at the real point `xₙ`.
Fit-free (contrast `POLE.2`'s fitted `2·ln(2πn/σ) − 2.12`), with `Re = xₙ` exactly. -/
def k1_guess (eta sigma rho : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi * n / sigma : ℝ) +
    Complex.I * (Real.log (‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ /
      ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖) / sigma : ℝ)

/-- `hk1re` **by construction**: `Re(k1_guess n) = 2πn/σ` exactly. -/
theorem k1_guess_re (eta sigma rho : ℝ) (n : ℕ) :
    (k1_guess eta sigma rho n).re = 2 * Real.pi * n / sigma := by
  unfold k1_guess
  simp

/-- `Im(k1_guess n)` is the log-lift value. -/
theorem k1_guess_im (eta sigma rho : ℝ) (n : ℕ) :
    (k1_guess eta sigma rho n).im =
      Real.log (‖Npoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖ /
        ‖Dpoly eta sigma rho ((2 * Real.pi * n / sigma : ℝ) : ℂ)‖) / sigma := by
  unfold k1_guess
  simp

/-- **The `hk1im` workhorse**: `r ≤ Im(k1_guess n)` reduces to the explicit real-axis
inequality `exp(σr)·(ρQ′·xₙ + 2|P2|) ≤ xₙ³ − |P1|·xₙ` — an elementary polynomial-vs-constant
threshold in `n` (cluster (e) discharges it asymptotically; per-parameter numeric instances are
immediate). Requires `σ > 0`, `ρQ′ ≥ 0`, and strict positivity of the denominator bound. -/
theorem k1_guess_im_ge_of (eta sigma rho r : ℝ) (n : ℕ) (hsigma : 0 < sigma)
    (hQp : 0 ≤ rho * q_prime_py eta sigma)
    (hden_pos : 0 < rho * q_prime_py eta sigma * (2 * Real.pi * n / sigma) +
      2 * |guessP2 eta sigma rho|)
    (hkey : Real.exp (sigma * r) *
        (rho * q_prime_py eta sigma * (2 * Real.pi * n / sigma) +
          2 * |guessP2 eta sigma rho|) ≤
      (2 * Real.pi * n / sigma) ^ 3 - |guessP1 eta sigma rho| * (2 * Real.pi * n / sigma)) :
    r ≤ (k1_guess eta sigma rho n).im := by
  set x : ℝ := 2 * Real.pi * n / sigma with hxdef
  have hx : 0 ≤ x := by
    rw [hxdef]
    positivity
  -- norm bounds
  have hNlow : x ^ 3 - |guessP1 eta sigma rho| * x ≤ ‖Npoly eta sigma rho (x : ℂ)‖ :=
    Npoly_norm_lower eta sigma rho hx
  have hDup : ‖Dpoly eta sigma rho (x : ℂ)‖ ≤
      rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho| :=
    Dpoly_norm_upper eta sigma rho hx hQp
  -- positivity of the two norms
  have hDpos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := by
    have him : |(Dpoly eta sigma rho (x : ℂ)).im| ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ :=
      Complex.abs_im_le_norm _
    have hre : |(Dpoly eta sigma rho (x : ℂ)).re| ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ :=
      Complex.abs_re_le_norm _
    rw [Dpoly_ofReal_im] at him
    rw [Dpoly_ofReal_re] at hre
    have h1 : rho * q_prime_py eta sigma * x ≤ |rho * q_prime_py eta sigma * x| :=
      le_abs_self _
    have h2 : |2 * guessP2 eta sigma rho| = 2 * |guessP2 eta sigma rho| := by
      rw [abs_mul]
      norm_num
    rw [h2] at hre
    linarith [hden_pos]
  have hexp_pos : (0 : ℝ) < Real.exp (sigma * r) := Real.exp_pos _
  have hNpos : 0 < ‖Npoly eta sigma rho (x : ℂ)‖ := by
    have h1 : 0 < Real.exp (sigma * r) *
        (rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho|) :=
      mul_pos hexp_pos hden_pos
    linarith [hkey, hNlow]
  -- assemble: exp(σr) ≤ ‖N‖/‖D‖
  have hratio : Real.exp (sigma * r) ≤
      ‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖ := by
    rw [le_div_iff₀ hDpos]
    calc Real.exp (sigma * r) * ‖Dpoly eta sigma rho (x : ℂ)‖
        ≤ Real.exp (sigma * r) *
          (rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho|) :=
          mul_le_mul_of_nonneg_left hDup hexp_pos.le
      _ ≤ x ^ 3 - |guessP1 eta sigma rho| * x := hkey
      _ ≤ ‖Npoly eta sigma rho (x : ℂ)‖ := hNlow
  -- convert to the log statement
  have hlog : sigma * r ≤
      Real.log (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖) :=
    calc sigma * r = Real.log (Real.exp (sigma * r)) := (Real.log_exp _).symm
      _ ≤ Real.log (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖) :=
          Real.log_le_log hexp_pos hratio
  rw [k1_guess_im, ← hxdef, le_div_iff₀ hsigma]
  linarith [hlog]

end

end FMSA.HardSphere
