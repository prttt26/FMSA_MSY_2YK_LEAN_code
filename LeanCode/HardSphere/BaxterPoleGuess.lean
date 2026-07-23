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

/-! ### Cluster (b): off-axis bounds along the vertical segment `[x, x+y·i]`

`Npoly_hasDerivAt`/`Dpoly_hasDerivAt` already exist in `BaxterPoles.lean` (stated over the
`private` `baxterP0/1/2`); the `rfl`-bridge makes them directly usable here — a `HasDerivAt`
goal stated over `guessP0/1/2` is *definitionally* the same fact, so `exact` accepts it. -/

/-- Triangle-inequality bound on `Npoly`'s derivative (`Npoly_hasDerivAt`'s value, in
`guessP`-form): `‖N′(k)‖ ≤ 3s² + 2|P0|s + |P1|` for `‖k‖ ≤ s`. -/
theorem Npoly_deriv_norm_le (eta sigma rho : ℝ) {k : ℂ} {s : ℝ} (hk : ‖k‖ ≤ s) :
    ‖3 * Complex.I * k ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * k +
      Complex.I * (guessP1 eta sigma rho : ℂ)‖ ≤
      3 * s ^ 2 + 2 * |guessP0 eta sigma rho| * s + |guessP1 eta sigma rho| := by
  have hk0 : (0 : ℝ) ≤ ‖k‖ := norm_nonneg k
  have e1 : ‖3 * Complex.I * k ^ 2‖ ≤ 3 * s ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, norm_pow]
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [h3]
    nlinarith [pow_le_pow_left₀ hk0 hk 2]
  have e2 : ‖2 * (guessP0 eta sigma rho : ℂ) * k‖ ≤ 2 * |guessP0 eta sigma rho| * s := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    nlinarith [abs_nonneg (guessP0 eta sigma rho)]
  have e3 : ‖Complex.I * (guessP1 eta sigma rho : ℂ)‖ = |guessP1 eta sigma rho| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖3 * Complex.I * k ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * k +
        Complex.I * (guessP1 eta sigma rho : ℂ)‖
      ≤ ‖3 * Complex.I * k ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) * k‖ +
        ‖Complex.I * (guessP1 eta sigma rho : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖3 * Complex.I * k ^ 2‖ + ‖2 * (guessP0 eta sigma rho : ℂ) * k‖ +
        ‖Complex.I * (guessP1 eta sigma rho : ℂ)‖ := by
          have := norm_sub_le (3 * Complex.I * k ^ 2)
            (2 * (guessP0 eta sigma rho : ℂ) * k)
          linarith
    _ ≤ 3 * s ^ 2 + 2 * |guessP0 eta sigma rho| * s + |guessP1 eta sigma rho| := by
          rw [e3]
          linarith [e1, e2]

/-- **Segment MVT for `Npoly`** along the vertical segment `[x, x+y·i]`:
`‖N(x+y·i) − N(x)‖ ≤ (3(x+y)² + 2|P0|(x+y) + |P1|)·y`. -/
theorem Npoly_vertical_diff_le (eta sigma rho : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) - Npoly eta sigma rho (x : ℂ)‖ ≤
      (3 * (x + y) ^ 2 + 2 * |guessP0 eta sigma rho| * (x + y) + |guessP1 eta sigma rho|) *
        y := by
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => Npoly eta sigma rho ((x : ℂ) + (t : ℂ) *
          ((y : ℂ) * Complex.I)))
        ((3 * Complex.I * ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) ^ 2 -
            2 * (guessP0 eta sigma rho : ℂ) * ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) +
            Complex.I * (guessP1 eta sigma rho : ℂ)) * ((y : ℂ) * Complex.I))
        (Icc (0 : ℝ) 1) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
      (hasDerivAt_id ((t : ℝ) : ℂ)).comp_ofReal
    have hg : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * ((y : ℂ) * Complex.I))
        ((y : ℂ) * Complex.I) t := by
      have h2 := (h1.mul_const ((y : ℂ) * Complex.I)).const_add ((x : ℂ))
      simpa using h2
    have hN : HasDerivAt (Npoly eta sigma rho)
        (3 * Complex.I * ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) ^ 2 -
          2 * (guessP0 eta sigma rho : ℂ) * ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) +
          Complex.I * (guessP1 eta sigma rho : ℂ))
        ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) :=
      Npoly_hasDerivAt eta sigma rho _
    exact (hN.comp t hg).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖(3 * Complex.I * ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) ^ 2 -
          2 * (guessP0 eta sigma rho : ℂ) * ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) +
          Complex.I * (guessP1 eta sigma rho : ℂ)) * ((y : ℂ) * Complex.I)‖ ≤
        (3 * (x + y) ^ 2 + 2 * |guessP0 eta sigma rho| * (x + y) +
          |guessP1 eta sigma rho|) * y := by
    intro t ht
    have hznorm : ‖(x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)‖ ≤ x + y := by
      calc ‖(x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)‖
          ≤ ‖(x : ℂ)‖ + ‖(t : ℂ) * ((y : ℂ) * Complex.I)‖ := norm_add_le _ _
        _ = |x| + |t| * |y| := by
            simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ x + y := by
            rw [abs_of_nonneg hx, abs_of_nonneg ht.1, abs_of_nonneg hy]
            nlinarith [ht.1, ht.2.le, hy]
    have hderiv := Npoly_deriv_norm_le eta sigma rho hznorm
    have hyI : ‖(y : ℂ) * Complex.I‖ = y := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hy]
    rw [norm_mul, hyI]
    nlinarith [hderiv, hy, norm_nonneg (3 * Complex.I * ((x : ℂ) + (t : ℂ) *
      ((y : ℂ) * Complex.I)) ^ 2 - 2 * (guessP0 eta sigma rho : ℂ) *
      ((x : ℂ) + (t : ℂ) * ((y : ℂ) * Complex.I)) +
      Complex.I * (guessP1 eta sigma rho : ℂ))]
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' hpath hbound
  simpa using key

/-- `Dpoly` off the real axis, exactly: `Dpoly(x+y·i) = (2P2 − ρQ′y) + (ρQ′x)·i`. -/
theorem Dpoly_offReal (eta sigma rho x y : ℝ) :
    Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((2 * guessP2 eta sigma rho - rho * q_prime_py eta sigma * y : ℝ) : ℂ) +
        ((rho * q_prime_py eta sigma * x : ℝ) : ℂ) * Complex.I := by
  have hlead : ((guessP1 eta sigma rho : ℂ) + 2 * (guessP2 eta sigma rho : ℂ) * (sigma : ℂ)) =
      (rho : ℂ) * ((q_prime_py eta sigma : ℝ) : ℂ) := by
    calc ((guessP1 eta sigma rho : ℂ) + 2 * (guessP2 eta sigma rho : ℂ) * (sigma : ℂ))
        = ((guessP1 eta sigma rho + 2 * guessP2 eta sigma rho * sigma : ℝ) : ℂ) := by
          push_cast; ring
      _ = ((rho * q_prime_py eta sigma : ℝ) : ℂ) := by rw [Dpoly_lead_eq]
      _ = (rho : ℂ) * ((q_prime_py eta sigma : ℝ) : ℂ) := by push_cast; ring
  rw [Dpoly_eq_guess]
  push_cast
  linear_combination (((x : ℂ) + (y : ℂ) * Complex.I) * Complex.I) * hlead +
    ((rho : ℂ) * ((q_prime_py eta sigma : ℝ) : ℂ) * (y : ℂ)) * Complex.I_mul_I

theorem Dpoly_offReal_re (eta sigma rho x y : ℝ) :
    (Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      2 * guessP2 eta sigma rho - rho * q_prime_py eta sigma * y := by
  rw [Dpoly_offReal]; simp

theorem Dpoly_offReal_im (eta sigma rho x y : ℝ) :
    (Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)).im =
      rho * q_prime_py eta sigma * x := by
  rw [Dpoly_offReal]; simp

/-- Off-axis lower bound for `Dpoly` (via the imaginary part — `y`-independent!). -/
theorem Dpoly_offReal_norm_lower (eta sigma rho x y : ℝ) :
    rho * q_prime_py eta sigma * x ≤
      ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  have him : |(Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)).im| ≤
      ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
  rw [Dpoly_offReal_im] at him
  have h1 : rho * q_prime_py eta sigma * x ≤ |rho * q_prime_py eta sigma * x| := le_abs_self _
  linarith

/-- Off-axis `Dpoly` difference from the real-axis value: `‖D(x+y·i) − D(x)‖ = ρQ′·y` (exact,
stated as `≤` — the affine `Dpoly` needs no MVT). -/
theorem Dpoly_vertical_diff_le (eta sigma rho : ℝ) (x : ℝ) {y : ℝ} (hy : 0 ≤ y)
    (hQp : 0 ≤ rho * q_prime_py eta sigma) :
    ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) - Dpoly eta sigma rho (x : ℂ)‖ ≤
      rho * q_prime_py eta sigma * y := by
  have hdiff : Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
      Dpoly eta sigma rho (x : ℂ) =
      ((-(rho * q_prime_py eta sigma * y) : ℝ) : ℂ) := by
    rw [Dpoly_offReal, Dpoly_ofReal]
    push_cast
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (mul_nonneg hQp hy)]

/-! ### Cluster (c)/(d) helpers: log-ratio, Jordan-argument, product perturbation -/

/-- Two-sided log-ratio bound: `|log a − log b| ≤ Δ/(b−Δ)` when `|a−b| ≤ Δ < b`. -/
theorem abs_log_sub_log_le {a b d : ℝ} (hb : 0 < b) (hab : |a - b| ≤ d) (hd : d < b) :
    |Real.log a - Real.log b| ≤ d / (b - d) := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hab
  have habs := abs_le.mp hab
  have ha : 0 < a := by linarith [habs.1]
  have hbd : 0 < b - d := by linarith
  rw [← Real.log_div ha.ne' hb.ne', abs_le]
  constructor
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
    have h2 : Real.log (a / b) = -Real.log (b / a) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    have h3 : b / a - 1 = (b - a) / a := by field_simp
    have h4 : (b - a) / a ≤ d / (b - d) := by
      rw [div_le_div_iff₀ ha hbd]
      nlinarith [habs.1, habs.2]
    rw [h2]
    linarith
  · have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
    have h3 : a / b - 1 = (a - b) / b := by field_simp
    have h4 : (a - b) / b ≤ d / (b - d) := by
      rw [div_le_div_iff₀ hb hbd]
      nlinarith [habs.1, habs.2]
    linarith

/-- **Jordan-type argument bound**: for `Re w ≥ 0`, `w ≠ 0`,
`|arg w| ≤ (π/2)·|Im w|/‖w‖`. -/
theorem abs_arg_le_jordan {w : ℂ} (hre : 0 ≤ w.re) (hw : w ≠ 0) :
    |Complex.arg w| ≤ Real.pi / 2 * (|w.im| / ‖w‖) := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : |Complex.arg w| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre
  have hsin : Real.sin (Complex.arg w) = w.im / ‖w‖ := Complex.sin_arg w
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsinabs : Real.sin |Complex.arg w| = |w.im| / ‖w‖ := by
    rcases le_or_gt 0 (Complex.arg w) with h | h
    · have hs : 0 ≤ Real.sin (Complex.arg w) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi h
        have h2 := abs_of_nonneg h ▸ h1
        linarith
      have him : 0 ≤ w.im := by
        rw [hsin, le_div_iff₀ hnorm] at hs
        simpa using hs
      rw [abs_of_nonneg h, hsin, abs_of_nonneg him]
    · have h2 : -(Real.pi / 2) ≤ Complex.arg w := by
        have h3 := abs_le.mp h1
        linarith [h3.1]
      have hs : Real.sin (Complex.arg w) ≤ 0 := by
        have h3 : 0 ≤ Real.sin (-(Complex.arg w)) := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
          linarith
        rw [Real.sin_neg] at h3
        linarith
      have him : w.im ≤ 0 := by
        rw [hsin, div_le_iff₀ hnorm] at hs
        simpa using hs
      rw [abs_of_neg h, Real.sin_neg, hsin, abs_of_nonpos him, neg_div]
  have hj : 2 / Real.pi * |Complex.arg w| ≤ Real.sin |Complex.arg w| :=
    Real.mul_le_sin (abs_nonneg _) h1
  rw [hsinabs] at hj
  have h3 := mul_le_mul_of_nonneg_right hj hπ.le
  have h4 : 2 / Real.pi * |Complex.arg w| * Real.pi = 2 * |Complex.arg w| := by
    field_simp
  rw [h4] at h3
  nlinarith [h3]

/-- Perturbation bound for `A·conj B`: moving each factor by `ΔA`, `ΔB` moves the product by at
most `‖ΔA‖‖B‖ + ‖A‖‖ΔB‖ + ‖ΔA‖‖ΔB‖`. -/
theorem mul_conj_perturb_norm_le (A B A' B' : ℂ) :
    ‖A' * (starRingEnd ℂ) B' - A * (starRingEnd ℂ) B‖ ≤
      ‖A' - A‖ * ‖B‖ + ‖A‖ * ‖B' - B‖ + ‖A' - A‖ * ‖B' - B‖ := by
  have key : A' * (starRingEnd ℂ) B' - A * (starRingEnd ℂ) B =
      (A' - A) * (starRingEnd ℂ) B + A * (starRingEnd ℂ) (B' - B) +
        (A' - A) * (starRingEnd ℂ) (B' - B) := by
    simp only [map_sub]
    ring
  rw [key]
  calc ‖(A' - A) * (starRingEnd ℂ) B + A * (starRingEnd ℂ) (B' - B) +
        (A' - A) * (starRingEnd ℂ) (B' - B)‖
      ≤ ‖(A' - A) * (starRingEnd ℂ) B + A * (starRingEnd ℂ) (B' - B)‖ +
        ‖(A' - A) * (starRingEnd ℂ) (B' - B)‖ := norm_add_le _ _
    _ ≤ ‖(A' - A) * (starRingEnd ℂ) B‖ + ‖A * (starRingEnd ℂ) (B' - B)‖ +
        ‖(A' - A) * (starRingEnd ℂ) (B' - B)‖ := by
          linarith [norm_add_le ((A' - A) * (starRingEnd ℂ) B)
            (A * (starRingEnd ℂ) (B' - B))]
    _ = ‖A' - A‖ * ‖B‖ + ‖A‖ * ‖B' - B‖ + ‖A' - A‖ * ‖B' - B‖ := by
          simp only [norm_mul, Complex.norm_conj]

/-- `Re(N(x)·conj(D(x)))` explicitly (the `~ρQ′·x⁴` quantity driving branch safety). -/
theorem NconjD_re (eta sigma rho x : ℝ) :
    (Npoly eta sigma rho (x : ℂ) * (starRingEnd ℂ) (Dpoly eta sigma rho (x : ℂ))).re =
      (-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
          (2 * guessP2 eta sigma rho) +
        (x ^ 3 + guessP1 eta sigma rho * x) * (rho * q_prime_py eta sigma * x) := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Npoly_ofReal_re,
    Npoly_ofReal_im, Dpoly_ofReal_re, Dpoly_ofReal_im]
  ring

/-- `Im(N(x)·conj(D(x)))` explicitly (the `~x³` quantity the argument bound divides by `Re`). -/
theorem NconjD_im (eta sigma rho x : ℝ) :
    (Npoly eta sigma rho (x : ℂ) * (starRingEnd ℂ) (Dpoly eta sigma rho (x : ℂ))).im =
      (x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho) -
        (-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
          (rho * q_prime_py eta sigma * x) := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Npoly_ofReal_re,
    Npoly_ofReal_im, Dpoly_ofReal_re, Dpoly_ofReal_im]
  ring

/-! ### Cluster (e): assembly — abbreviations, helpers, and the `hstep` master theorem

The residual decomposition (no branch-cut analysis needed — `Complex.log`'s *definition*
`log W = log‖W‖ + arg(W)·i` splits the residual exactly):

  `φₙ(k1) − k1 = (i/σ)·(log(N(k1)/D(k1)) − σy)`,  `σy = log(‖N(x)‖/‖D(x)‖)`,

so `σ·‖residual‖ ≤ |log‖N(k1)‖−log‖N(x)‖| + |log‖D(k1)‖−log‖D(x)‖| + |arg(N(k1)·conj D(k1))|`,
and the three parts are bounded by the cluster (a)/(b) norm data via `abs_log_sub_log_le` and
`abs_arg_le_jordan`. -/

/-- MVT budget for `‖N(x+yi) − N(x)‖` (cluster (b)). -/
def deltaN (eta sigma rho x y : ℝ) : ℝ :=
  (3 * (x + y) ^ 2 + 2 * |guessP0 eta sigma rho| * (x + y) + |guessP1 eta sigma rho|) * y

/-- Real-axis lower bound for `‖N(x)‖`. -/
def lowN (eta sigma rho x : ℝ) : ℝ := x ^ 3 - |guessP1 eta sigma rho| * x

/-- Real-axis upper bound for `‖N(x)‖`. -/
def upN (eta sigma rho x : ℝ) : ℝ :=
  x ^ 3 + |guessP0 eta sigma rho| * x ^ 2 + |guessP1 eta sigma rho| * x +
    2 * |guessP2 eta sigma rho|

/-- Exact budget for `‖D(x+yi) − D(x)‖`. -/
def deltaD (eta sigma rho y : ℝ) : ℝ := rho * q_prime_py eta sigma * y

/-- Lower bound for `‖D‖` — valid on *and off* the real axis (`Dpoly_offReal_norm_lower`). -/
def lowD (eta sigma rho x : ℝ) : ℝ := rho * q_prime_py eta sigma * x

/-- Real-axis upper bound for `‖D(x)‖`. -/
def upD (eta sigma rho x : ℝ) : ℝ :=
  rho * q_prime_py eta sigma * x + 2 * |guessP2 eta sigma rho|

/-- `Re(N(x)·conj D(x))` (`NconjD_re`) — the branch-safety quantity, `~ρQ′x⁴`. -/
def wRe (eta sigma rho x : ℝ) : ℝ :=
  (-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
      (2 * guessP2 eta sigma rho) +
    (x ^ 3 + guessP1 eta sigma rho * x) * (rho * q_prime_py eta sigma * x)

/-- `Im(N(x)·conj D(x))` (`NconjD_im`) — the argument numerator, `~x³`. -/
def wIm (eta sigma rho x : ℝ) : ℝ :=
  (x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho) -
    (-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
      (rho * q_prime_py eta sigma * x)

/-- Perturbation budget for `N·conj D` when moving from `x` to `x+yi`
(`mul_conj_perturb_norm_le`). -/
def deltaW (eta sigma rho x y : ℝ) : ℝ :=
  deltaN eta sigma rho x y * upD eta sigma rho x + upN eta sigma rho x * deltaD eta sigma rho y +
    deltaN eta sigma rho x y * deltaD eta sigma rho y

/-- `Complex.log`'s definitional split gives `‖log W − L‖ ≤ |log‖W‖ − L| + |arg W|`. -/
theorem log_sub_ofReal_norm_le (W : ℂ) (L : ℝ) :
    ‖Complex.log W - (L : ℂ)‖ ≤ |Real.log ‖W‖ - L| + |Complex.arg W| := by
  have h := Complex.norm_le_abs_re_add_abs_im (Complex.log W - (L : ℂ))
  simpa [Complex.sub_re, Complex.sub_im, Complex.log_re, Complex.log_im] using h

/-- `arg(u/v) = arg(u·conj v)` — division by `v` is a positive-real multiple of `·conj v`. -/
theorem arg_div_eq_arg_mul_conj (u v : ℂ) (hv : v ≠ 0) :
    Complex.arg (u / v) = Complex.arg (u * (starRingEnd ℂ) v) := by
  have hnsq : (0 : ℝ) < Complex.normSq v := Complex.normSq_pos.mpr hv
  have h : u / v = (((Complex.normSq v)⁻¹ : ℝ) : ℂ) * (u * (starRingEnd ℂ) v) := by
    rw [div_eq_mul_inv, Complex.inv_def]
    push_cast
    ring
  rw [h, Complex.arg_real_mul _ (inv_pos.mpr hnsq)]

/-- `k1_guess` in the `x + y·i` shape the cluster (b) lemmas consume. -/
theorem k1_guess_eq (eta sigma rho : ℝ) (n : ℕ) :
    k1_guess eta sigma rho n = ((2 * Real.pi * n / sigma : ℝ) : ℂ) +
      (((k1_guess eta sigma rho n).im : ℝ) : ℂ) * Complex.I := by
  rw [k1_guess_im]
  unfold k1_guess
  ring

/-- **The `hstep` master theorem (`POLE.7`).** For the derived log-lift guess, the chord
residual `dist(k1, φₙ(k1))` is bounded by the fully explicit three-part budget; every
hypothesis is an elementary real-polynomial/`log` inequality in `x = 2πn/σ` and
`y = Im(k1_guess n)`. The final threshold pass discharges them for `n ≥ N` explicit. -/
theorem k1_guess_hstep_of (eta sigma rho rr KK : ℝ) (n : ℕ)
    (hsigma : 0 < sigma) (hQp : 0 < rho * q_prime_py eta sigma)
    {x y : ℝ}
    (hxdef : x = 2 * Real.pi * n / sigma)
    (hydef : y = (k1_guess eta sigma rho n).im)
    (hx0 : 0 < x) (hy0 : 0 ≤ y)
    (hNgap : deltaN eta sigma rho x y < lowN eta sigma rho x)
    (hDgap : deltaD eta sigma rho y < lowD eta sigma rho x)
    (hwgap : deltaW eta sigma rho x y < wRe eta sigma rho x)
    (hbudget : (1 / sigma) *
        (deltaN eta sigma rho x y / (lowN eta sigma rho x - deltaN eta sigma rho x y) +
          deltaD eta sigma rho y / (lowD eta sigma rho x - deltaD eta sigma rho y) +
          Real.pi / 2 * ((|wIm eta sigma rho x| + deltaW eta sigma rho x y) /
            (wRe eta sigma rho x - deltaW eta sigma rho x y))) ≤ rr * (1 - KK)) :
    dist (k1_guess eta sigma rho n) (baxterPhi eta sigma rho n (k1_guess eta sigma rho n)) ≤
      rr * (1 - KK) := by
  have hx0' : (0 : ℝ) ≤ x := hx0.le
  -- nonnegativity of the budgets
  have hdN0 : 0 ≤ deltaN eta sigma rho x y := by
    unfold deltaN; positivity
  have hdD0 : 0 ≤ deltaD eta sigma rho y := by
    unfold deltaD; positivity
  have hdW0 : 0 ≤ deltaW eta sigma rho x y := by
    unfold deltaW upN upD
    positivity
  -- the K point
  have hK : k1_guess eta sigma rho n = (x : ℂ) + (y : ℂ) * Complex.I := by
    rw [hxdef, hydef]
    exact k1_guess_eq eta sigma rho n
  -- real-axis norms
  have hNx_low : lowN eta sigma rho x ≤ ‖Npoly eta sigma rho (x : ℂ)‖ :=
    Npoly_norm_lower eta sigma rho hx0'
  have hNx_up : ‖Npoly eta sigma rho (x : ℂ)‖ ≤ upN eta sigma rho x :=
    Npoly_norm_upper eta sigma rho hx0'
  have hDx_low : lowD eta sigma rho x ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ :=
    Dpoly_norm_lower eta sigma rho x
  have hDx_up : ‖Dpoly eta sigma rho (x : ℂ)‖ ≤ upD eta sigma rho x :=
    Dpoly_norm_upper eta sigma rho hx0' hQp.le
  have hNx_pos : 0 < ‖Npoly eta sigma rho (x : ℂ)‖ := lt_of_lt_of_le
    (lt_of_le_of_lt hdN0 hNgap) hNx_low
  have hDx_pos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := lt_of_lt_of_le
    (lt_of_le_of_lt hdD0 hDgap) hDx_low
  -- vertical diffs
  have hdN : ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
      Npoly eta sigma rho (x : ℂ)‖ ≤ deltaN eta sigma rho x y :=
    Npoly_vertical_diff_le eta sigma rho hx0' hy0
  have hdD : ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
      Dpoly eta sigma rho (x : ℂ)‖ ≤ deltaD eta sigma rho y :=
    Dpoly_vertical_diff_le eta sigma rho x hy0 hQp.le
  -- norms at the K point
  have hNK_low : lowN eta sigma rho x - deltaN eta sigma rho x y ≤
      ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
    have h1 : |‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
        ‖Npoly eta sigma rho (x : ℂ)‖| ≤ deltaN eta sigma rho x y :=
      le_trans (abs_norm_sub_norm_le _ _) hdN
    have h2 := abs_le.mp h1
    linarith [h2.1, hNx_low]
  have hNK_pos : 0 < ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ :=
    lt_of_lt_of_le (by linarith [hNgap]) hNK_low
  have hDK_low : lowD eta sigma rho x ≤
      ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ :=
    Dpoly_offReal_norm_lower eta sigma rho x y
  have hDK_pos : 0 < ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
    have : (0 : ℝ) < lowD eta sigma rho x := by
      unfold lowD
      positivity
    linarith [hDK_low]
  have hNK_ne : Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
    norm_pos_iff.mp hNK_pos
  have hDK_ne : Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
    norm_pos_iff.mp hDK_pos
  have hNx_ne : Npoly eta sigma rho (x : ℂ) ≠ 0 := norm_pos_iff.mp hNx_pos
  have hDx_ne : Dpoly eta sigma rho (x : ℂ) ≠ 0 := norm_pos_iff.mp hDx_pos
  -- div-monotonicity helper
  have hdivmono : ∀ {a b c : ℝ}, 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c := by
    intro a b c ha hc hcb
    rw [div_le_div_iff₀ (lt_of_lt_of_le hc hcb) hc]
    nlinarith
  -- log-ratio bounds
  have hlogN : |Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
      Real.log ‖Npoly eta sigma rho (x : ℂ)‖| ≤
      deltaN eta sigma rho x y / (lowN eta sigma rho x - deltaN eta sigma rho x y) := by
    have h1 : |‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
        ‖Npoly eta sigma rho (x : ℂ)‖| ≤ deltaN eta sigma rho x y :=
      le_trans (abs_norm_sub_norm_le _ _) hdN
    have h2 := abs_log_sub_log_le hNx_pos h1 (lt_of_lt_of_le hNgap hNx_low)
    calc |Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
        Real.log ‖Npoly eta sigma rho (x : ℂ)‖|
        ≤ deltaN eta sigma rho x y /
          (‖Npoly eta sigma rho (x : ℂ)‖ - deltaN eta sigma rho x y) := h2
      _ ≤ deltaN eta sigma rho x y /
          (lowN eta sigma rho x - deltaN eta sigma rho x y) := by
          apply hdivmono hdN0 (by linarith [hNgap])
          linarith [hNx_low]
  have hlogD : |Real.log ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
      Real.log ‖Dpoly eta sigma rho (x : ℂ)‖| ≤
      deltaD eta sigma rho y / (lowD eta sigma rho x - deltaD eta sigma rho y) := by
    have h1 : |‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
        ‖Dpoly eta sigma rho (x : ℂ)‖| ≤ deltaD eta sigma rho y :=
      le_trans (abs_norm_sub_norm_le _ _) hdD
    have h2 := abs_log_sub_log_le hDx_pos h1 (lt_of_lt_of_le hDgap hDx_low)
    calc |Real.log ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
        Real.log ‖Dpoly eta sigma rho (x : ℂ)‖|
        ≤ deltaD eta sigma rho y /
          (‖Dpoly eta sigma rho (x : ℂ)‖ - deltaD eta sigma rho y) := h2
      _ ≤ deltaD eta sigma rho y /
          (lowD eta sigma rho x - deltaD eta sigma rho y) := by
          apply hdivmono hdD0 (by linarith [hDgap])
          linarith [hDx_low]
  -- w = N(K)·conj D(K) bounds
  have hw_diff : ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) *
      (starRingEnd ℂ) (Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)) -
      Npoly eta sigma rho (x : ℂ) * (starRingEnd ℂ) (Dpoly eta sigma rho (x : ℂ))‖ ≤
      deltaW eta sigma rho x y := by
    have h := mul_conj_perturb_norm_le (Npoly eta sigma rho (x : ℂ))
      (Dpoly eta sigma rho (x : ℂ))
      (Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I))
      (Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I))
    unfold deltaW
    calc ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) *
        (starRingEnd ℂ) (Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)) -
        Npoly eta sigma rho (x : ℂ) * (starRingEnd ℂ) (Dpoly eta sigma rho (x : ℂ))‖
        ≤ ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
            Npoly eta sigma rho (x : ℂ)‖ * ‖Dpoly eta sigma rho (x : ℂ)‖ +
          ‖Npoly eta sigma rho (x : ℂ)‖ *
            ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
              Dpoly eta sigma rho (x : ℂ)‖ +
          ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
            Npoly eta sigma rho (x : ℂ)‖ *
            ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
              Dpoly eta sigma rho (x : ℂ)‖ := h
      _ ≤ deltaN eta sigma rho x y * upD eta sigma rho x +
          upN eta sigma rho x * deltaD eta sigma rho y +
          deltaN eta sigma rho x y * deltaD eta sigma rho y := by
          have hn1 := norm_nonneg (Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
            Npoly eta sigma rho (x : ℂ))
          have hn2 := norm_nonneg (Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) -
            Dpoly eta sigma rho (x : ℂ))
          have hn3 := norm_nonneg (Npoly eta sigma rho (x : ℂ))
          have hn4 := norm_nonneg (Dpoly eta sigma rho (x : ℂ))
          have hu1 : (0:ℝ) ≤ upD eta sigma rho x := le_trans hn4 hDx_up
          nlinarith [mul_le_mul hdN hDx_up hn4 hdN0, mul_le_mul hNx_up hdD hn2
            (le_trans hn3 hNx_up), mul_le_mul hdN hdD hn2 hdN0]
  -- w's re/im control
  have hwre_val := NconjD_re eta sigma rho x
  have hwim_val := NconjD_im eta sigma rho x
  set w : ℂ := Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) *
    (starRingEnd ℂ) (Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)) with hwdef
  set w0 : ℂ := Npoly eta sigma rho (x : ℂ) *
    (starRingEnd ℂ) (Dpoly eta sigma rho (x : ℂ)) with hw0def
  have hre_diff : |w.re - w0.re| ≤ deltaW eta sigma rho x y := by
    have h1 : |(w - w0).re| ≤ ‖w - w0‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    exact le_trans h1 hw_diff
  have him_diff : |w.im - w0.im| ≤ deltaW eta sigma rho x y := by
    have h1 : |(w - w0).im| ≤ ‖w - w0‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    exact le_trans h1 hw_diff
  have hwre_low : wRe eta sigma rho x - deltaW eta sigma rho x y ≤ w.re := by
    have h1 := abs_le.mp hre_diff
    have h2 : w0.re = wRe eta sigma rho x := by rw [hw0def, hwre_val]; rfl
    linarith [h1.1, h2.ge, h2.le]
  have hwre_pos : 0 < w.re := lt_of_lt_of_le (by linarith [hwgap]) hwre_low
  have hwim_up : |w.im| ≤ |wIm eta sigma rho x| + deltaW eta sigma rho x y := by
    have h2 : w0.im = wIm eta sigma rho x := by rw [hw0def, hwim_val]; rfl
    have h3 : |w.im| ≤ |w0.im| + |w.im - w0.im| := by
      calc |w.im| = |w0.im + (w.im - w0.im)| := by congr 1; ring
        _ ≤ |w0.im| + |w.im - w0.im| := abs_add_le _ _
    rw [h2] at h3 him_diff
    linarith [him_diff, h3]
  have hw_ne : w ≠ 0 := by
    intro h0
    rw [h0] at hwre_pos
    simp at hwre_pos
  -- argument bound
  have harg : |Complex.arg (Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) /
      Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I))| ≤
      Real.pi / 2 * ((|wIm eta sigma rho x| + deltaW eta sigma rho x y) /
        (wRe eta sigma rho x - deltaW eta sigma rho x y)) := by
    rw [arg_div_eq_arg_mul_conj _ _ hDK_ne]
    have h1 : |Complex.arg w| ≤ Real.pi / 2 * (|w.im| / ‖w‖) :=
      abs_arg_le_jordan hwre_pos.le hw_ne
    have h2 : |w.im| / ‖w‖ ≤ (|wIm eta sigma rho x| + deltaW eta sigma rho x y) /
        (wRe eta sigma rho x - deltaW eta sigma rho x y) := by
      have hwn : wRe eta sigma rho x - deltaW eta sigma rho x y ≤ ‖w‖ :=
        le_trans hwre_low (Complex.re_le_norm w)
      have hpos : (0:ℝ) < wRe eta sigma rho x - deltaW eta sigma rho x y := by
        linarith [hwgap]
      rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hwn) hpos]
      nlinarith [abs_nonneg w.im, hwim_up, hwn, norm_nonneg w]
    calc |Complex.arg w| ≤ Real.pi / 2 * (|w.im| / ‖w‖) := h1
      _ ≤ Real.pi / 2 * ((|wIm eta sigma rho x| + deltaW eta sigma rho x y) /
          (wRe eta sigma rho x - deltaW eta sigma rho x y)) := by
          have hπ2 : (0:ℝ) ≤ Real.pi / 2 := by positivity
          exact mul_le_mul_of_nonneg_left h2 hπ2
  -- σy identity
  have hsy : sigma * y = Real.log ‖Npoly eta sigma rho (x : ℂ)‖ -
      Real.log ‖Dpoly eta sigma rho (x : ℂ)‖ := by
    have h1 : y = Real.log (‖Npoly eta sigma rho (x : ℂ)‖ /
        ‖Dpoly eta sigma rho (x : ℂ)‖) / sigma := by
      rw [hydef, k1_guess_im, ← hxdef]
    rw [h1, ← Real.log_div hNx_pos.ne' hDx_pos.ne']
    field_simp
  -- residual identity
  have hres : baxterPhi eta sigma rho n (k1_guess eta sigma rho n) -
      k1_guess eta sigma rho n =
      (Complex.I / (sigma : ℂ)) *
        (Complex.log (Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) /
          Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)) - ((sigma * y : ℝ) : ℂ)) := by
    unfold baxterPhi
    rw [hK, hxdef]
    have hσ : ((sigma : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsigma.ne'
    push_cast
    field_simp
    ring
  -- assemble
  rw [dist_eq_norm, ← norm_sub_rev, hres]
  have hInorm : ‖Complex.I / (sigma : ℂ)‖ = 1 / sigma := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsigma]
  rw [norm_mul, hInorm]
  have hlogW : |Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) /
      Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ - sigma * y| ≤
      deltaN eta sigma rho x y / (lowN eta sigma rho x - deltaN eta sigma rho x y) +
        deltaD eta sigma rho y / (lowD eta sigma rho x - deltaD eta sigma rho y) := by
    rw [norm_div, Real.log_div hNK_pos.ne' hDK_pos.ne', hsy]
    have htri : |Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
        Real.log ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
        (Real.log ‖Npoly eta sigma rho (x : ℂ)‖ -
          Real.log ‖Dpoly eta sigma rho (x : ℂ)‖)| ≤
        |Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
          Real.log ‖Npoly eta sigma rho (x : ℂ)‖| +
        |Real.log ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
          Real.log ‖Dpoly eta sigma rho (x : ℂ)‖| := by
      have h := abs_add_le
        (Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
          Real.log ‖Npoly eta sigma rho (x : ℂ)‖)
        (-(Real.log ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
          Real.log ‖Dpoly eta sigma rho (x : ℂ)‖))
      rw [abs_neg] at h
      calc |Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
          Real.log ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
          (Real.log ‖Npoly eta sigma rho (x : ℂ)‖ -
            Real.log ‖Dpoly eta sigma rho (x : ℂ)‖)|
          = |(Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
              Real.log ‖Npoly eta sigma rho (x : ℂ)‖) +
            -(Real.log ‖Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ -
              Real.log ‖Dpoly eta sigma rho (x : ℂ)‖)| := by
            congr 1
            ring
        _ ≤ _ := h
    exact le_trans htri (add_le_add hlogN hlogD)
  calc (1 / sigma) * ‖Complex.log (Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) /
        Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)) - ((sigma * y : ℝ) : ℂ)‖
      ≤ (1 / sigma) * (|Real.log ‖Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) /
          Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I)‖ - sigma * y| +
        |Complex.arg (Npoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I) /
          Dpoly eta sigma rho ((x : ℂ) + (y : ℂ) * Complex.I))|) := by
        have hσ1 : (0:ℝ) ≤ 1 / sigma := by positivity
        exact mul_le_mul_of_nonneg_left (log_sub_ofReal_norm_le _ _) hσ1
    _ ≤ (1 / sigma) *
        (deltaN eta sigma rho x y / (lowN eta sigma rho x - deltaN eta sigma rho x y) +
          deltaD eta sigma rho y / (lowD eta sigma rho x - deltaD eta sigma rho y) +
          Real.pi / 2 * ((|wIm eta sigma rho x| + deltaW eta sigma rho x y) /
            (wRe eta sigma rho x - deltaW eta sigma rho x y))) := by
        have hσ1 : (0:ℝ) ≤ 1 / sigma := by positivity
        apply mul_le_mul_of_nonneg_left _ hσ1
        linarith [hlogW, harg]
    _ ≤ rr * (1 - KK) := hbudget

/-! ### `Im(k1_guess)` two-sided log bounds (threshold-pass inputs) -/

/-- Upper bound: `Im(k1_guess n) ≤ log(upN/lowD)/σ` — the `~(3·log x)/σ` growth cap that the
threshold pass feeds into the monotone budget. -/
theorem k1_guess_im_le_of (eta sigma rho : ℝ) (n : ℕ) (hsigma : 0 < sigma)
    {x : ℝ} (hxdef : x = 2 * Real.pi * n / sigma)
    (hlowN_pos : 0 < lowN eta sigma rho x) (hlowD_pos : 0 < lowD eta sigma rho x) :
    (k1_guess eta sigma rho n).im ≤
      Real.log (upN eta sigma rho x / lowD eta sigma rho x) / sigma := by
  have hx0 : 0 ≤ x := by
    rw [hxdef]; positivity
  have hNx_low : lowN eta sigma rho x ≤ ‖Npoly eta sigma rho (x : ℂ)‖ :=
    Npoly_norm_lower eta sigma rho hx0
  have hNx_up : ‖Npoly eta sigma rho (x : ℂ)‖ ≤ upN eta sigma rho x :=
    Npoly_norm_upper eta sigma rho hx0
  have hDx_low : lowD eta sigma rho x ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ :=
    Dpoly_norm_lower eta sigma rho x
  have hNx_pos : 0 < ‖Npoly eta sigma rho (x : ℂ)‖ := lt_of_lt_of_le hlowN_pos hNx_low
  have hDx_pos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := lt_of_lt_of_le hlowD_pos hDx_low
  have him : (k1_guess eta sigma rho n).im =
      Real.log (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖) / sigma := by
    rw [k1_guess_im, ← hxdef]
  rw [him]
  have hratio : ‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖ ≤
      upN eta sigma rho x / lowD eta sigma rho x := by
    rw [div_le_div_iff₀ hDx_pos hlowD_pos]
    nlinarith [hNx_up, hDx_low, hNx_pos.le, hlowD_pos.le]
  have hlog := Real.log_le_log (div_pos hNx_pos hDx_pos) hratio
  gcongr

/-- Lower bound / nonnegativity: `upD ≤ lowN ⇒ 0 ≤ Im(k1_guess n)` (the ratio is `≥ 1`). -/
theorem k1_guess_im_nonneg_of (eta sigma rho : ℝ) (n : ℕ) (hsigma : 0 < sigma)
    (hQp : 0 ≤ rho * q_prime_py eta sigma)
    {x : ℝ} (hxdef : x = 2 * Real.pi * n / sigma)
    (hlowD_pos : 0 < lowD eta sigma rho x)
    (hgap : upD eta sigma rho x ≤ lowN eta sigma rho x) :
    0 ≤ (k1_guess eta sigma rho n).im := by
  have hx0 : 0 ≤ x := by
    rw [hxdef]; positivity
  have hNx_low : lowN eta sigma rho x ≤ ‖Npoly eta sigma rho (x : ℂ)‖ :=
    Npoly_norm_lower eta sigma rho hx0
  have hDx_up : ‖Dpoly eta sigma rho (x : ℂ)‖ ≤ upD eta sigma rho x :=
    Dpoly_norm_upper eta sigma rho hx0 hQp
  have hDx_low : lowD eta sigma rho x ≤ ‖Dpoly eta sigma rho (x : ℂ)‖ :=
    Dpoly_norm_lower eta sigma rho x
  have hDx_pos : 0 < ‖Dpoly eta sigma rho (x : ℂ)‖ := lt_of_lt_of_le hlowD_pos hDx_low
  have him : (k1_guess eta sigma rho n).im =
      Real.log (‖Npoly eta sigma rho (x : ℂ)‖ / ‖Dpoly eta sigma rho (x : ℂ)‖) / sigma := by
    rw [k1_guess_im, ← hxdef]
  rw [him]
  apply div_nonneg _ hsigma.le
  apply Real.log_nonneg
  rw [le_div_iff₀ hDx_pos, one_mul]
  linarith [hDx_up, hgap, hNx_low]

/-! ### POLE.7 threshold pass — explicit envelope constants

For the threshold ("eventually") pass every budget quantity is bounded by a polynomial
envelope in `x` with explicit (generous, non-tight) constants.  Writing `A := |guessP0|`,
`B := |guessP1|`, `C := |guessP2|`, `Q := ρ·q_prime_py` and assuming `x ≥ 1`,
`0 ≤ y ≤ ε·x`, `0 ≤ ε ≤ 1`:

* `deltaN ≤ guessCN·ε·x³`, `lowN ≥ x³/2` (once `2B ≤ x²`), `upN ≤ guessCU·x³`,
* `deltaD ≤ Q·ε·x`, `upD ≤ guessCD·x`, `deltaW ≤ guessCW·ε·x⁴`,
* `wRe ≥ Q·x⁴/2` (once `2·guessCR ≤ Q·x²`), `|wIm| ≤ guessCI·x³`. -/

/-- Envelope constant for `deltaN`: `deltaN ≤ guessCN·ε·x³`. -/
def guessCN (eta sigma rho : ℝ) : ℝ :=
  12 + 4 * |guessP0 eta sigma rho| + |guessP1 eta sigma rho|

/-- Envelope constant for `upN`: `upN ≤ guessCU·x³` for `x ≥ 1`. -/
def guessCU (eta sigma rho : ℝ) : ℝ :=
  1 + |guessP0 eta sigma rho| + |guessP1 eta sigma rho| + 2 * |guessP2 eta sigma rho|

/-- Envelope constant for `upD`: `upD ≤ guessCD·x` for `x ≥ 1`. -/
def guessCD (eta sigma rho : ℝ) : ℝ :=
  rho * q_prime_py eta sigma + 2 * |guessP2 eta sigma rho|

/-- Envelope constant for `deltaW`: `deltaW ≤ guessCW·ε·x⁴`. -/
def guessCW (eta sigma rho : ℝ) : ℝ :=
  guessCN eta sigma rho * guessCD eta sigma rho +
    guessCU eta sigma rho * (rho * q_prime_py eta sigma) +
    guessCN eta sigma rho * (rho * q_prime_py eta sigma)

/-- Defect constant for `wRe`: `wRe ≥ Q·x⁴ − guessCR·x²`. -/
def guessCR (eta sigma rho : ℝ) : ℝ :=
  rho * q_prime_py eta sigma * |guessP1 eta sigma rho| +
    2 * |guessP0 eta sigma rho| * |guessP2 eta sigma rho|

/-- Envelope constant for `|wIm|`: `|wIm| ≤ guessCI·x³` for `x ≥ 1`. -/
def guessCI (eta sigma rho : ℝ) : ℝ :=
  2 * |guessP2 eta sigma rho| * (1 + |guessP1 eta sigma rho|) +
    rho * q_prime_py eta sigma * (|guessP0 eta sigma rho| + 2 * |guessP2 eta sigma rho|)

theorem guessCN_pos (eta sigma rho : ℝ) : 0 < guessCN eta sigma rho := by
  unfold guessCN
  positivity

theorem guessCU_pos (eta sigma rho : ℝ) : 0 < guessCU eta sigma rho := by
  unfold guessCU
  positivity

theorem guessCD_pos (eta sigma rho : ℝ) (hQp : 0 < rho * q_prime_py eta sigma) :
    0 < guessCD eta sigma rho := by
  unfold guessCD
  linarith [abs_nonneg (guessP2 eta sigma rho)]

theorem guessCW_pos (eta sigma rho : ℝ) (hQp : 0 < rho * q_prime_py eta sigma) :
    0 < guessCW eta sigma rho := by
  unfold guessCW
  linarith [mul_pos (guessCN_pos eta sigma rho) (guessCD_pos eta sigma rho hQp),
    mul_pos (guessCU_pos eta sigma rho) hQp,
    mul_pos (guessCN_pos eta sigma rho) hQp]

theorem guessCR_nonneg (eta sigma rho : ℝ) (hQp : 0 ≤ rho * q_prime_py eta sigma) :
    0 ≤ guessCR eta sigma rho := by
  unfold guessCR
  have h1 := mul_nonneg hQp (abs_nonneg (guessP1 eta sigma rho))
  have h2 := mul_nonneg (abs_nonneg (guessP0 eta sigma rho))
    (abs_nonneg (guessP2 eta sigma rho))
  linarith

theorem guessCI_nonneg (eta sigma rho : ℝ) (hQp : 0 ≤ rho * q_prime_py eta sigma) :
    0 ≤ guessCI eta sigma rho := by
  unfold guessCI
  have hB0 := abs_nonneg (guessP1 eta sigma rho)
  have hA0 := abs_nonneg (guessP0 eta sigma rho)
  have hC0 := abs_nonneg (guessP2 eta sigma rho)
  have h1 : (0 : ℝ) ≤ 2 * |guessP2 eta sigma rho| * (1 + |guessP1 eta sigma rho|) :=
    mul_nonneg (mul_nonneg (by norm_num) hC0) (by linarith)
  have h2 : (0 : ℝ) ≤ rho * q_prime_py eta sigma *
      (|guessP0 eta sigma rho| + 2 * |guessP2 eta sigma rho|) :=
    mul_nonneg hQp (by linarith)
  linarith

/-- Two-sided division monotonicity: enlarge the numerator, shrink the denominator. -/
theorem div_le_div_bound {a a0 b b0 : ℝ} (ha : a ≤ a0) (ha0 : 0 ≤ a0)
    (hb0 : 0 < b0) (hb : b0 ≤ b) : a / b ≤ a0 / b0 := by
  have hbpos : 0 < b := lt_of_lt_of_le hb0 hb
  rw [div_le_div_iff₀ hbpos hb0]
  nlinarith

/-- **Sublinear log cap**: for every `ε > 0`, eventually `c + 2·log x ≤ ε·x`
(the `log x / x → 0` limit, packaged for the threshold pass). -/
theorem eventually_log_cap (c ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, c + 2 * Real.log x ≤ ε * x := by
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x / x < ε / 4 :=
    h1.eventually_lt_const (by positivity)
  filter_upwards [h2, Filter.eventually_ge_atTop (2 * c / ε),
    Filter.eventually_gt_atTop (0 : ℝ)] with x hx1 hx2 hx3
  have hlog : Real.log x ≤ ε / 4 * x := by
    rw [div_lt_iff₀ hx3] at hx1
    linarith
  have hc : c ≤ ε / 2 * x := by
    rw [div_le_iff₀ hε] at hx2
    linarith
  linarith

/-! ### Envelope bounds for the budget quantities -/

/-- `deltaN ≤ guessCN·ε·x³` for `x ≥ 1`, `0 ≤ y ≤ ε·x`, `ε ≤ 1`. -/
theorem deltaN_le_of (eta sigma rho : ℝ) {x y ε : ℝ} (hx1 : 1 ≤ x)
    (hy0 : 0 ≤ y) (hyx : y ≤ ε * x) (hε1 : ε ≤ 1) :
    deltaN eta sigma rho x y ≤ guessCN eta sigma rho * ε * x ^ 3 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hε0 : 0 ≤ ε :=
    (mul_nonneg_iff_of_pos_right hx0).mp (le_trans hy0 hyx)
  have hεx : ε * x ≤ x := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) hx0.le]
  have hyx' : y ≤ x := le_trans hyx hεx
  have hA0 : (0 : ℝ) ≤ |guessP0 eta sigma rho| := abs_nonneg _
  have hB0 : (0 : ℝ) ≤ |guessP1 eta sigma rho| := abs_nonneg _
  unfold deltaN guessCN
  have hparen : 3 * (x + y) ^ 2 + 2 * |guessP0 eta sigma rho| * (x + y) +
      |guessP1 eta sigma rho| ≤
      (12 + 4 * |guessP0 eta sigma rho| + |guessP1 eta sigma rho|) * x ^ 2 := by
    have h2 : (x + y) ^ 2 ≤ 4 * x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - y)
        (by linarith : (0 : ℝ) ≤ 3 * x + y)]
    have h3 : 2 * |guessP0 eta sigma rho| * (x + y) ≤
        4 * |guessP0 eta sigma rho| * x ^ 2 := by
      nlinarith [mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ x - y),
        mul_nonneg (mul_nonneg hA0 hx0.le) (by linarith : (0 : ℝ) ≤ x - 1)]
    have h5 : |guessP1 eta sigma rho| ≤ |guessP1 eta sigma rho| * x ^ 2 := by
      nlinarith [mul_nonneg hB0 (by nlinarith [sq_nonneg (x - 1)] : (0 : ℝ) ≤ x ^ 2 - 1)]
    linarith
  have hfin : (3 * (x + y) ^ 2 + 2 * |guessP0 eta sigma rho| * (x + y) +
      |guessP1 eta sigma rho|) * y ≤
      ((12 + 4 * |guessP0 eta sigma rho| + |guessP1 eta sigma rho|) * x ^ 2) * (ε * x) := by
    apply mul_le_mul hparen hyx hy0
    positivity
  nlinarith [hfin]

/-- `lowN ≥ x³/2` once `2·|P1| ≤ x²` (`x > 0`). -/
theorem lowN_half_ge_of (eta sigma rho : ℝ) {x : ℝ} (hx0 : 0 < x)
    (hxB : 2 * |guessP1 eta sigma rho| ≤ x ^ 2) :
    x ^ 3 / 2 ≤ lowN eta sigma rho x := by
  unfold lowN
  nlinarith [mul_le_mul_of_nonneg_right hxB hx0.le]

/-- `upN ≤ guessCU·x³` for `x ≥ 1`. -/
theorem upN_le_of (eta sigma rho : ℝ) {x : ℝ} (hx1 : 1 ≤ x) :
    upN eta sigma rho x ≤ guessCU eta sigma rho * x ^ 3 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h23 : x ^ 2 ≤ x ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ x - 1)]
  have h13 : x ≤ x ^ 3 := by
    nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ x - 1)]
  have h03 : (1 : ℝ) ≤ x ^ 3 := by linarith
  unfold upN guessCU
  nlinarith [mul_le_mul_of_nonneg_left h23 (abs_nonneg (guessP0 eta sigma rho)),
    mul_le_mul_of_nonneg_left h13 (abs_nonneg (guessP1 eta sigma rho)),
    mul_le_mul_of_nonneg_left h03 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (abs_nonneg (guessP2 eta sigma rho)))]

/-- `upD ≤ guessCD·x` for `x ≥ 1`. -/
theorem upD_le_of (eta sigma rho : ℝ) {x : ℝ} (hx1 : 1 ≤ x) :
    upD eta sigma rho x ≤ guessCD eta sigma rho * x := by
  unfold upD guessCD
  nlinarith [mul_nonneg (abs_nonneg (guessP2 eta sigma rho))
    (by linarith : (0 : ℝ) ≤ x - 1)]

/-- `wRe ≥ Q·x⁴/2` once `2·guessCR ≤ Q·x²` (`x ≥ 0`, `Q ≥ 0`). -/
theorem wRe_half_ge_of (eta sigma rho : ℝ) {x : ℝ} (_hx0 : 0 ≤ x)
    (hQp : 0 ≤ rho * q_prime_py eta sigma)
    (hxR : 2 * guessCR eta sigma rho ≤ rho * q_prime_py eta sigma * x ^ 2) :
    rho * q_prime_py eta sigma * x ^ 4 / 2 ≤ wRe eta sigma rho x := by
  unfold guessCR at hxR
  unfold wRe
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have h1 : guessP0 eta sigma rho * guessP2 eta sigma rho ≤
      |guessP0 eta sigma rho| * |guessP2 eta sigma rho| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h2 : -|guessP1 eta sigma rho| ≤ guessP1 eta sigma rho := neg_abs_le _
  nlinarith [sq_nonneg (guessP2 eta sigma rho),
    mul_le_mul_of_nonneg_right h1 hx2,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hQp) hx2,
    mul_le_mul_of_nonneg_right hxR hx2]

/-- `|wIm| ≤ guessCI·x³` for `x ≥ 1`, `Q ≥ 0`. -/
theorem wIm_abs_le_of (eta sigma rho : ℝ) {x : ℝ} (hx1 : 1 ≤ x)
    (hQp : 0 ≤ rho * q_prime_py eta sigma) :
    |wIm eta sigma rho x| ≤ guessCI eta sigma rho * x ^ 3 := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
  have hx0' : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h13 : x ≤ x ^ 3 := by
    nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ x - 1),
      mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ x - 1)]
  have hB0 : (0 : ℝ) ≤ |guessP1 eta sigma rho| := abs_nonneg _
  have hA0 : (0 : ℝ) ≤ |guessP0 eta sigma rho| := abs_nonneg _
  have hC0 : (0 : ℝ) ≤ |guessP2 eta sigma rho| := abs_nonneg _
  -- triangle bounds on the two factors
  have habs1 : |x ^ 3 + guessP1 eta sigma rho * x| ≤ x ^ 3 + |guessP1 eta sigma rho| * x := by
    calc |x ^ 3 + guessP1 eta sigma rho * x|
        ≤ |x ^ 3| + |guessP1 eta sigma rho * x| := abs_add_le _ _
      _ = x ^ 3 + |guessP1 eta sigma rho| * x := by
          rw [abs_of_nonneg (pow_nonneg hx0 3), abs_mul, abs_of_nonneg hx0]
  have habs2 : |(-(guessP0 eta sigma rho)) * x ^ 2 + 2 * guessP2 eta sigma rho| ≤
      |guessP0 eta sigma rho| * x ^ 2 + 2 * |guessP2 eta sigma rho| := by
    calc |(-(guessP0 eta sigma rho)) * x ^ 2 + 2 * guessP2 eta sigma rho|
        ≤ |(-(guessP0 eta sigma rho)) * x ^ 2| + |2 * guessP2 eta sigma rho| := abs_add_le _ _
      _ = |guessP0 eta sigma rho| * x ^ 2 + 2 * |guessP2 eta sigma rho| := by
          rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg x), abs_mul]
          norm_num
  unfold wIm
  -- |a − b| ≤ |a| + |b| via abs_add_le on a + (−b)
  have htri : |(x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho) -
      (-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
        (rho * q_prime_py eta sigma * x)| ≤
      |(x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho)| +
        |(-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
          (rho * q_prime_py eta sigma * x)| := by
    have h := abs_add_le ((x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho))
      (-((-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
        (rho * q_prime_py eta sigma * x)))
    rw [abs_neg] at h
    calc |(x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho) -
        (-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
          (rho * q_prime_py eta sigma * x)|
        = |(x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho) +
          -((-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
            (rho * q_prime_py eta sigma * x))| := by
          rw [sub_eq_add_neg]
      _ ≤ _ := h
  have e1 : |(x ^ 3 + guessP1 eta sigma rho * x) * (2 * guessP2 eta sigma rho)| ≤
      (x ^ 3 + |guessP1 eta sigma rho| * x) * (2 * |guessP2 eta sigma rho|) := by
    rw [abs_mul]
    have h2C : |2 * guessP2 eta sigma rho| = 2 * |guessP2 eta sigma rho| := by
      rw [abs_mul]
      norm_num
    rw [h2C]
    exact mul_le_mul_of_nonneg_right habs1 (by linarith)
  have e2 : |(-(guessP0 eta sigma rho) * x ^ 2 + 2 * guessP2 eta sigma rho) *
      (rho * q_prime_py eta sigma * x)| ≤
      (|guessP0 eta sigma rho| * x ^ 2 + 2 * |guessP2 eta sigma rho|) *
        (rho * q_prime_py eta sigma * x) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hQp hx0)]
    exact mul_le_mul_of_nonneg_right habs2 (mul_nonneg hQp hx0)
  -- assemble and pass to the `x³` envelope
  unfold guessCI
  nlinarith [htri, e1, e2,
    mul_le_mul_of_nonneg_left h13 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0) hB0),
    mul_le_mul_of_nonneg_left h13 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0) hQp)]

/-- `deltaW ≤ guessCW·ε·x⁴` for `x ≥ 1`, `0 ≤ y ≤ ε·x`, `ε ≤ 1`, `Q ≥ 0`. -/
theorem deltaW_le_of (eta sigma rho : ℝ) {x y ε : ℝ}
    (hQp : 0 ≤ rho * q_prime_py eta sigma) (hx1 : 1 ≤ x)
    (hy0 : 0 ≤ y) (hyx : y ≤ ε * x) (hε1 : ε ≤ 1) :
    deltaW eta sigma rho x y ≤ guessCW eta sigma rho * ε * x ^ 4 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hε0 : 0 ≤ ε :=
    (mul_nonneg_iff_of_pos_right hx0).mp (le_trans hy0 hyx)
  have hεx : ε * x ≤ x := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) hx0.le]
  have hdN := deltaN_le_of eta sigma rho hx1 hy0 hyx hε1
  have hdN0 : 0 ≤ deltaN eta sigma rho x y := by
    unfold deltaN
    positivity
  have hupN := upN_le_of eta sigma rho hx1
  have hupD := upD_le_of eta sigma rho hx1
  have hupD0 : 0 ≤ upD eta sigma rho x := by
    unfold upD
    have := mul_nonneg hQp hx0.le
    linarith [abs_nonneg (guessP2 eta sigma rho)]
  have hdD_le : deltaD eta sigma rho y ≤ rho * q_prime_py eta sigma * (ε * x) := by
    unfold deltaD
    exact mul_le_mul_of_nonneg_left hyx hQp
  have hdD_le' : deltaD eta sigma rho y ≤ rho * q_prime_py eta sigma * x :=
    le_trans hdD_le (mul_le_mul_of_nonneg_left hεx hQp)
  have hdD0 : 0 ≤ deltaD eta sigma rho y := by
    unfold deltaD
    exact mul_nonneg hQp hy0
  have hcN0 : 0 ≤ guessCN eta sigma rho * ε * x ^ 3 :=
    mul_nonneg (mul_nonneg (guessCN_pos eta sigma rho).le hε0) (by positivity)
  have hcU0 : 0 ≤ guessCU eta sigma rho * x ^ 3 :=
    mul_nonneg (guessCU_pos eta sigma rho).le (by positivity)
  have t1 : deltaN eta sigma rho x y * upD eta sigma rho x ≤
      (guessCN eta sigma rho * ε * x ^ 3) * (guessCD eta sigma rho * x) :=
    mul_le_mul hdN hupD hupD0 hcN0
  have t2 : upN eta sigma rho x * deltaD eta sigma rho y ≤
      (guessCU eta sigma rho * x ^ 3) * (rho * q_prime_py eta sigma * (ε * x)) :=
    mul_le_mul hupN hdD_le hdD0 hcU0
  have t3 : deltaN eta sigma rho x y * deltaD eta sigma rho y ≤
      (guessCN eta sigma rho * ε * x ^ 3) * (rho * q_prime_py eta sigma * x) :=
    mul_le_mul hdN hdD_le' hdD0 hcN0
  unfold deltaW guessCW
  nlinarith [t1, t2, t3]

/-! ### Threshold sufficiency and the eventually theorem -/

/-- **Threshold sufficiency** (`POLE.7` cluster (e), per-`n` step): explicit smallness
conditions on `ε` and linear lower thresholds on `x = 2πn/σ` discharge every hypothesis of
the master `k1_guess_hstep_of`. -/
theorem k1_guess_hstep_of_thresholds (eta sigma rho rr KK ε : ℝ) (n : ℕ)
    (hsigma : 0 < sigma) (hQp : 0 < rho * q_prime_py eta sigma)
    {x y : ℝ}
    (hxdef : x = 2 * Real.pi * n / sigma)
    (hydef : y = (k1_guess eta sigma rho n).im)
    (hx1 : 1 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ ε * x)
    (hε1 : ε ≤ 1 / 2)
    (hεN : 4 * guessCN eta sigma rho * ε ≤ 1)
    (hεW : 4 * guessCW eta sigma rho * ε ≤ rho * q_prime_py eta sigma)
    (hxB : 2 * |guessP1 eta sigma rho| ≤ x)
    (hxR : 2 * guessCR eta sigma rho / (rho * q_prime_py eta sigma) ≤ x)
    (hbud : (1 / sigma) * (4 * guessCN eta sigma rho * ε + 2 * ε +
        Real.pi / 2 * (4 * guessCI eta sigma rho / (rho * q_prime_py eta sigma * x) +
          4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma))) ≤ rr * (1 - KK)) :
    dist (k1_guess eta sigma rho n) (baxterPhi eta sigma rho n (k1_guess eta sigma rho n)) ≤
      rr * (1 - KK) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hε0 : 0 ≤ ε :=
    (mul_nonneg_iff_of_pos_right hx0).mp (le_trans hy0 hyx)
  have hx_le_sq : x ≤ x ^ 2 := by
    linarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ x - 1)]
  -- quadratic thresholds from the linear ones
  have hxB2 : 2 * |guessP1 eta sigma rho| ≤ x ^ 2 := by linarith
  have hxR2 : 2 * guessCR eta sigma rho ≤ rho * q_prime_py eta sigma * x ^ 2 := by
    rw [div_le_iff₀ hQp] at hxR
    have := mul_le_mul_of_nonneg_left hx_le_sq hQp.le
    linarith [hxR]
  -- envelope bounds
  have hdN := deltaN_le_of eta sigma rho hx1 hy0 hyx (by linarith)
  have hlowN := lowN_half_ge_of eta sigma rho hx0 hxB2
  have hdW := deltaW_le_of eta sigma rho hQp.le hx1 hy0 hyx (by linarith)
  have hwRe := wRe_half_ge_of eta sigma rho hx0.le hQp.le hxR2
  have hwIm := wIm_abs_le_of eta sigma rho hx1 hQp.le
  have hx3 : (0 : ℝ) < x ^ 3 := by positivity
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  have hcN := guessCN_pos eta sigma rho
  have hcW := guessCW_pos eta sigma rho hQp
  have hcI0 := guessCI_nonneg eta sigma rho hQp.le
  -- quarter-envelope bounds from the ε-smallness conditions
  have hdN4 : deltaN eta sigma rho x y ≤ x ^ 3 / 4 := by
    have h := mul_le_mul_of_nonneg_right
      (show guessCN eta sigma rho * ε ≤ 1 / 4 by linarith) hx3.le
    linarith [hdN, h]
  have hdW4 : deltaW eta sigma rho x y ≤ rho * q_prime_py eta sigma * x ^ 4 / 4 := by
    have h := mul_le_mul_of_nonneg_right
      (show guessCW eta sigma rho * ε ≤ rho * q_prime_py eta sigma / 4 by linarith) hx4.le
    linarith [hdW, h]
  -- the three gap hypotheses
  have hNgap : deltaN eta sigma rho x y < lowN eta sigma rho x := by
    have : x ^ 3 / 4 < x ^ 3 / 2 := by linarith
    linarith [hdN4, hlowN]
  have hDgap : deltaD eta sigma rho y < lowD eta sigma rho x := by
    unfold deltaD lowD
    have hyx2 : y ≤ x / 2 := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - ε) hx0.le]
    linarith [mul_pos hQp (show (0 : ℝ) < x - y by linarith)]
  have hwgap : deltaW eta sigma rho x y < wRe eta sigma rho x := by
    have h : rho * q_prime_py eta sigma * x ^ 4 / 4 <
        rho * q_prime_py eta sigma * x ^ 4 / 2 := by
      linarith [mul_pos hQp hx4]
    linarith [hdW4, hwRe]
  -- budget term 1: deltaN/(lowN − deltaN) ≤ 4·cN·ε
  have hlowN_den : (0 : ℝ) < lowN eta sigma rho x - deltaN eta sigma rho x y := by
    linarith [hNgap]
  have ht1 : deltaN eta sigma rho x y / (lowN eta sigma rho x - deltaN eta sigma rho x y) ≤
      4 * guessCN eta sigma rho * ε := by
    have hden : x ^ 3 / 4 ≤ lowN eta sigma rho x - deltaN eta sigma rho x y := by
      linarith [hlowN, hdN4]
    rw [div_le_iff₀ hlowN_den]
    have h4cN : (0 : ℝ) ≤ 4 * guessCN eta sigma rho * ε :=
      mul_nonneg (mul_nonneg (by norm_num) hcN.le) hε0
    linarith [mul_le_mul_of_nonneg_left hden h4cN, hdN]
  -- budget term 2: deltaD/(lowD − deltaD) ≤ 2·ε
  have ht2 : deltaD eta sigma rho y / (lowD eta sigma rho x - deltaD eta sigma rho y) ≤
      2 * ε := by
    have hden : (0 : ℝ) < lowD eta sigma rho x - deltaD eta sigma rho y := by
      linarith [hDgap]
    rw [div_le_iff₀ hden]
    unfold deltaD lowD
    have hkey : 2 * ε ^ 2 ≤ ε := by
      linarith [mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
    linarith [mul_le_mul_of_nonneg_left hyx (mul_nonneg hQp.le hε0),
      mul_le_mul_of_nonneg_left hyx hQp.le,
      mul_le_mul_of_nonneg_right hkey (mul_nonneg hQp.le hx0.le)]
  -- budget term 3: the Jordan/argument quotient
  have hwden : (0 : ℝ) < wRe eta sigma rho x - deltaW eta sigma rho x y := by
    linarith [hwgap]
  have ht3 : (|wIm eta sigma rho x| + deltaW eta sigma rho x y) /
      (wRe eta sigma rho x - deltaW eta sigma rho x y) ≤
      4 * guessCI eta sigma rho / (rho * q_prime_py eta sigma * x) +
        4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma) := by
    have hden : rho * q_prime_py eta sigma * x ^ 4 / 4 ≤
        wRe eta sigma rho x - deltaW eta sigma rho x y := by
      linarith [hwRe, hdW4]
    have hnum : |wIm eta sigma rho x| + deltaW eta sigma rho x y ≤
        guessCI eta sigma rho * x ^ 3 + guessCW eta sigma rho * ε * x ^ 4 := by
      linarith [hwIm, hdW]
    have hnum0 : (0 : ℝ) ≤ guessCI eta sigma rho * x ^ 3 +
        guessCW eta sigma rho * ε * x ^ 4 := by
      have hn1 := mul_nonneg hcI0 hx3.le
      have hn2 := mul_nonneg (mul_nonneg hcW.le hε0) hx4.le
      linarith
    have hQx4 : (0 : ℝ) < rho * q_prime_py eta sigma * x ^ 4 / 4 := by
      have := mul_pos hQp hx4
      linarith
    have hstep := div_le_div_bound hnum hnum0 hQx4 hden
    have heq : (guessCI eta sigma rho * x ^ 3 + guessCW eta sigma rho * ε * x ^ 4) /
        (rho * q_prime_py eta sigma * x ^ 4 / 4) =
        4 * guessCI eta sigma rho / (rho * q_prime_py eta sigma * x) +
          4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma) := by
      field_simp [hQp.ne', hx0.ne']
    rw [heq] at hstep
    exact hstep
  -- assemble the budget and close via the master theorem
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hσ1 : (0 : ℝ) ≤ 1 / sigma := by positivity
  have hsum : deltaN eta sigma rho x y / (lowN eta sigma rho x - deltaN eta sigma rho x y) +
      deltaD eta sigma rho y / (lowD eta sigma rho x - deltaD eta sigma rho y) +
      Real.pi / 2 * ((|wIm eta sigma rho x| + deltaW eta sigma rho x y) /
        (wRe eta sigma rho x - deltaW eta sigma rho x y)) ≤
      4 * guessCN eta sigma rho * ε + 2 * ε +
        Real.pi / 2 * (4 * guessCI eta sigma rho / (rho * q_prime_py eta sigma * x) +
          4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma)) := by
    have h3 := mul_le_mul_of_nonneg_left ht3 hπ2
    linarith [ht1, ht2, h3]
  exact k1_guess_hstep_of eta sigma rho rr KK n hsigma hQp hxdef hydef hx0 hy0
    hNgap hDgap hwgap (le_trans (mul_le_mul_of_nonneg_left hsum hσ1) hbud)

/-- **The `POLE.7` threshold/eventually theorem**: for every positive chord target
`rr·(1−KK)` the residual bound of the master `k1_guess_hstep_of` holds for all
sufficiently large `n`.  The smallness parameter `ε` is chosen explicitly from the
envelope constants; the `n`-thresholds come from `x = 2πn/σ → ∞` together with the
sublinear log cap `eventually_log_cap` controlling `Im(k1_guess n) ≤ ε·x`. -/
theorem k1_guess_hstep_eventually (eta sigma rho rr KK : ℝ)
    (hsigma : 0 < sigma) (hQp : 0 < rho * q_prime_py eta sigma)
    (htarget : 0 < rr * (1 - KK)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      dist (k1_guess eta sigma rho n) (baxterPhi eta sigma rho n (k1_guess eta sigma rho n)) ≤
        rr * (1 - KK) := by
  have hcN := guessCN_pos eta sigma rho
  have hcU := guessCU_pos eta sigma rho
  have hcD := guessCD_pos eta sigma rho hQp
  have hcW := guessCW_pos eta sigma rho hQp
  -- the explicit smallness parameter ε
  set Ks : ℝ := 4 * guessCN eta sigma rho + 2 +
    2 * Real.pi * guessCW eta sigma rho / (rho * q_prime_py eta sigma) with hKsdef
  have hKs_pos : 0 < Ks := by
    rw [hKsdef]
    have h1 : 0 < 2 * Real.pi * guessCW eta sigma rho / (rho * q_prime_py eta sigma) :=
      div_pos (mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hcW) hQp
    linarith
  set ε : ℝ := min (1 / 2) (min (1 / (4 * guessCN eta sigma rho))
    (min (rho * q_prime_py eta sigma / (4 * guessCW eta sigma rho))
      (sigma * (rr * (1 - KK)) / (2 * Ks)))) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    refine lt_min (by norm_num) (lt_min ?_ (lt_min ?_ ?_))
    · exact div_pos one_pos (by linarith)
    · exact div_pos hQp (by linarith)
    · exact div_pos (mul_pos hsigma htarget) (by linarith)
  have hε12 : ε ≤ 1 / 2 := by
    rw [hεdef]
    exact min_le_left _ _
  have hεN : 4 * guessCN eta sigma rho * ε ≤ 1 := by
    have h : ε ≤ 1 / (4 * guessCN eta sigma rho) := by
      rw [hεdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * guessCN eta sigma rho)] at h
    linarith
  have hεW : 4 * guessCW eta sigma rho * ε ≤ rho * q_prime_py eta sigma := by
    have h : ε ≤ rho * q_prime_py eta sigma / (4 * guessCW eta sigma rho) := by
      rw [hεdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * guessCW eta sigma rho)] at h
    linarith
  have hεK : ε * (2 * Ks) ≤ sigma * (rr * (1 - KK)) := by
    have h : ε ≤ sigma * (rr * (1 - KK)) / (2 * Ks) := by
      rw [hεdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * Ks)] at h
    linarith
  -- eventual thresholds in the real variable x
  have hlogcap := eventually_log_cap
    (Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma))) (sigma * ε)
    (mul_pos hsigma hε0)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ 2 * |guessP1 eta sigma rho| ≤ x ∧
      2 * guessCR eta sigma rho / (rho * q_prime_py eta sigma) ≤ x ∧
      2 * guessCD eta sigma rho ≤ x ∧
      4 * Real.pi * guessCI eta sigma rho /
        (sigma * (rho * q_prime_py eta sigma) * (rr * (1 - KK))) ≤ x ∧
      Real.log (guessCU eta sigma rho / (rho * q_prime_py eta sigma)) + 2 * Real.log x ≤
        sigma * ε * x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop (2 * |guessP1 eta sigma rho|),
      Filter.eventually_ge_atTop
        (2 * guessCR eta sigma rho / (rho * q_prime_py eta sigma)),
      Filter.eventually_ge_atTop (2 * guessCD eta sigma rho),
      Filter.eventually_ge_atTop (4 * Real.pi * guessCI eta sigma rho /
        (sigma * (rho * q_prime_py eta sigma) * (rr * (1 - KK)))),
      hlogcap] with x h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  -- push the thresholds along n ↦ 2πn/σ → ∞
  have htends : Filter.Tendsto (fun n : ℕ => 2 * Real.pi * (n : ℝ) / sigma)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hsigma
      (Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htends.eventually hev)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hx1, hxB, hxR, hxD, hxI, hlog⟩ := hN n hn
  -- basic facts about x = 2πn/σ
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
  -- the per-n budget hypothesis
  have hbud : (1 / sigma) * (4 * guessCN eta sigma rho * ε + 2 * ε +
      Real.pi / 2 * (4 * guessCI eta sigma rho /
        (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma)) +
        4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma))) ≤ rr * (1 - KK) := by
    have hpart1 : (1 / sigma) * (4 * guessCN eta sigma rho * ε + 2 * ε +
        Real.pi / 2 * (4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma))) ≤
        rr * (1 - KK) / 2 := by
      have he : 4 * guessCN eta sigma rho * ε + 2 * ε +
          Real.pi / 2 * (4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma)) =
          ε * Ks := by
        rw [hKsdef]
        ring
      rw [he]
      have h1 : (1 / sigma) * (ε * Ks) = ε * Ks / sigma := by ring
      rw [h1, div_le_div_iff₀ hsigma (by norm_num : (0 : ℝ) < 2)]
      linarith [hεK]
    have hστQ : (0 : ℝ) < sigma * (rho * q_prime_py eta sigma) * (rr * (1 - KK)) :=
      mul_pos (mul_pos hsigma hQp) htarget
    rw [div_le_iff₀ hστQ] at hxI
    have hQx : (0 : ℝ) < rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma) :=
      mul_pos hQp hx0
    have hpart2 : (1 / sigma) * (Real.pi / 2 * (4 * guessCI eta sigma rho /
        (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma)))) ≤
        rr * (1 - KK) / 2 := by
      have hL : (1 / sigma) * (Real.pi / 2 * (4 * guessCI eta sigma rho /
          (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma)))) =
          2 * Real.pi * guessCI eta sigma rho /
            (sigma * (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma))) := by
        ring
      rw [hL, div_le_iff₀ (mul_pos hsigma hQx)]
      linarith [hxI]
    calc (1 / sigma) * (4 * guessCN eta sigma rho * ε + 2 * ε +
        Real.pi / 2 * (4 * guessCI eta sigma rho /
          (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma)) +
          4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma))) =
        (1 / sigma) * (4 * guessCN eta sigma rho * ε + 2 * ε +
          Real.pi / 2 * (4 * guessCW eta sigma rho * ε / (rho * q_prime_py eta sigma))) +
        (1 / sigma) * (Real.pi / 2 * (4 * guessCI eta sigma rho /
          (rho * q_prime_py eta sigma * (2 * Real.pi * (n : ℝ) / sigma)))) := by ring
      _ ≤ rr * (1 - KK) / 2 + rr * (1 - KK) / 2 := add_le_add hpart1 hpart2
      _ = rr * (1 - KK) := by ring
  exact k1_guess_hstep_of_thresholds eta sigma rho rr KK ε n hsigma hQp rfl rfl
    hx1 hy0 hycap hε12 hεN hεW hxB hxR hbud

end

end FMSA.HardSphere
