/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureInnerDCF
import LeanCode.Analysis.PoleSeriesSummable

/-!
# Matrix real-space infrastructure I — the antiderivative layer of term (II)

Task **MML.14** (the first genuine building block of MML.8's real-space collapse).  The scalar
`hcollapse` (`OZFIX.11`/`OZFIX.12`) is powered by an **antiderivative tower** over the per-pole
Fourier residue: `residue_term → Hterm → Kterm` (`OzCollapseInner.lean`), each rung one integration
in `r` and one power of `1/‖k‖` better in summability.  `Kterm` (two rungs) is summable at **every**
`u > 0`, which is what lets the inner region — sampled down toward `r = 0` — be handled.

The mixture (RDF) per-pole term is already in hand: `mixHSterm2 α β s r = (α + β·r)·e^{−s·r}`
(`MixtureInnerDCF.lean`, MML.8; the double pole's `(α + β·r)` envelope, MML.9/MML.11 pinning both
coefficients).  What was missing is its antiderivative tower.  The key structural fact, proved here:

> **The family `{(a + b·r)·e^{−s·r} : a, b ∈ ℂ}` is closed under antidifferentiation in `r`**, with
> the coefficient map `(a, b) ↦ (−a/s − b/s², −b/s)`; each step improves the leading coefficient's
> `‖s‖`-decay by one power.

So no new function shapes are needed — the whole tower stays inside `expLinTerm`, and the matrix
`Hterm`/`Kterm` analogs are just `expLinTerm` at once- or twice-iterated coefficients.  This is the
mixture counterpart of `Kterm_hasDerivAt` and the reason the scalar collapse's polynomial-algebra
bridge has a matrix analog at all.

## Results

* `expLinTerm a b s r` — the `(a + b·r)·e^{−s·r}` shape; `mixHSterm2_eq_expLinTerm` identifies the
  per-pole term with it.
* `expLinTerm_deriv` — the exact derivative in `r`, `(b − s·a − s·b·r)·e^{−s·r}`.
* `antiCoeff s (a,b) = (−a/s − b/s², −b/s)` and `expLinTerm_antideriv` — `expLinTerm (antiCoeff …)`
  is an antiderivative of `expLinTerm a b s` (`HasDerivAt`, `s ≠ 0`).
* `expLinAntideriv1`/`expLinAntideriv2` — the once/twice-iterated primitives (matrix `Hterm`/`Kterm`
  analogs), with their `HasDerivAt` chain (`expLinAntideriv2_hasDerivAt` differentiates to
  `expLinAntideriv1`, which differentiates to the term).

Status: ✓ axiom-clean.  Foundational — no collapse is proved here; this is the tower the collapse
will integrate against.
-/

set_option linter.style.longLine false

open Filter Topology

namespace FMSA.MixtureRDF

noncomputable section

/-! ### The `(a + b·r)·e^{−s·r}` shape and its derivative -/

/-- The per-pole envelope shape `(a + b·r)·e^{−s·r}` (a rank-≤1 polynomial times a decaying
exponential).  `mixHSterm2`'s summand is this at `(a,b,s) = (α_n, β_n, s_n)`. -/
def expLinTerm (a b s : ℂ) (r : ℝ) : ℂ := (a + b * (r : ℂ)) * Complex.exp (-s * (r : ℂ))

/-- The mixture term (II) summand is `expLinTerm` at the pole's `(α, β, s)`. -/
theorem mixHSterm2_eq_expLinTerm (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) :
    FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam r n
      = expLinTerm (alpha n) (beta n) (sfam n) r := rfl

/-- **Derivative of `expLinTerm` in `r`.**  `d/dr[(a + b·r)·e^{−s·r}] = (b − s·a − s·b·r)·e^{−s·r}`.
The product/chain rule with the real variable `r` cast to `ℂ`. -/
theorem expLinTerm_hasDerivAt (a b s : ℂ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => expLinTerm a b s x)
      ((b - s * a - s * b * (r : ℂ)) * Complex.exp (-s * (r : ℂ))) r := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r := Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun x : ℝ => a + b * (x : ℂ)) b r := by
    have h := (hcast.const_mul b).const_add a
    simpa using h
  have harg : HasDerivAt (fun x : ℝ => -s * (x : ℂ)) (-s) r := by
    have h := hcast.const_mul (-s)
    simpa using h
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (-s * (x : ℂ)))
      (Complex.exp (-s * (r : ℂ)) * (-s)) r := harg.cexp
  unfold expLinTerm
  rw [show (b - s * a - s * b * (r : ℂ)) * Complex.exp (-s * (r : ℂ))
      = b * Complex.exp (-s * (r : ℂ))
        + (a + b * (r : ℂ)) * (Complex.exp (-s * (r : ℂ)) * (-s)) from by ring]
  exact hlin.mul hexp

/-- The `expLinTerm` derivative, written as another `expLinTerm` (the derivative of `(a+b·r)e^{−sr}`
is `((b−s·a) + (−s·b)·r)e^{−sr}`). -/
theorem expLinTerm_deriv_eq (a b s : ℂ) (r : ℝ) :
    (b - s * a - s * b * (r : ℂ)) * Complex.exp (-s * (r : ℂ))
      = expLinTerm (b - s * a) (-s * b) s r := by
  unfold expLinTerm
  ring

/-! ### The antiderivative coefficient map and the primitive tower -/

/-- **The antiderivative coefficient map.**  An antiderivative of `(a + b·r)·e^{−s·r}` is
`(A + B·r)·e^{−s·r}` with `(A, B) = (−a/s − b/s², −b/s)`; `antiCoeff s (a,b)` names it.  This map is
the whole content of "the family is closed under antidifferentiation": iterating it walks the tower.
Each step divides by `s`, improving the leading coefficient's `‖s‖`-decay by one power (the
summability gain that carries `Hterm → Kterm`). -/
def antiCoeff (s a b : ℂ) : ℂ × ℂ := (-a / s - b / s ^ 2, -b / s)

/-- **`expLinTerm` is closed under antidifferentiation.**  For `s ≠ 0`, `expLinTerm A B s` with
`(A,B) = antiCoeff s a b` is an antiderivative of `expLinTerm a b s`: its `r`-derivative is
`expLinTerm a b s r`.  This is the mixture analog of `Kterm_hasDerivAt` (the scalar per-pole
antiderivative), at the level of the abstract `(a+b·r)e^{−sr}` shape. -/
theorem expLinTerm_antideriv_hasDerivAt (a b s : ℂ) (hs : s ≠ 0) (r : ℝ) :
    HasDerivAt (fun x : ℝ => expLinTerm (-a / s - b / s ^ 2) (-b / s) s x)
      (expLinTerm a b s r) r := by
  have h := expLinTerm_hasDerivAt (-a / s - b / s ^ 2) (-b / s) s r
  convert h using 1
  unfold expLinTerm
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp
  ring

/-! ### The concrete two-rung tower over `mixHSterm2` -/

/-- **First antiderivative** of the per-pole term `(α+β·r)e^{−s·r}` (the matrix `Hterm` analog):
`expLinTerm (−α/s − β/s², −β/s) s`. -/
def mixHSAntideriv1 (alpha beta sfam : ℕ → ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  expLinTerm (-alpha n / sfam n - beta n / (sfam n) ^ 2) (-beta n / sfam n) (sfam n) r

/-- **Second antiderivative** (the matrix `Kterm` analog): `antiCoeff` applied twice.  With one more
`1/s` on the leading coefficient it is the rung whose per-pole magnitude decays fast enough to be
summable arbitrarily close to `r = 0` — the mixture counterpart of `Kterm`'s all-`u>0` summability. -/
def mixHSAntideriv2 (alpha beta sfam : ℕ → ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  expLinTerm
    (-(-alpha n / sfam n - beta n / (sfam n) ^ 2) / sfam n - (-beta n / sfam n) / (sfam n) ^ 2)
    (-(-beta n / sfam n) / sfam n) (sfam n) r

/-- `mixHSAntideriv1` differentiates to the per-pole term `mixHSterm2` (needs `s_n ≠ 0`). -/
theorem mixHSAntideriv1_hasDerivAt (alpha beta sfam : ℕ → ℂ) (hs : ∀ n, sfam n ≠ 0)
    (n : ℕ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => mixHSAntideriv1 alpha beta sfam n x)
      (FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam r n) r := by
  rw [mixHSterm2_eq_expLinTerm]
  exact expLinTerm_antideriv_hasDerivAt (alpha n) (beta n) (sfam n) (hs n) r

/-- `mixHSAntideriv2` differentiates to `mixHSAntideriv1` (the second rung over the first). -/
theorem mixHSAntideriv2_hasDerivAt (alpha beta sfam : ℕ → ℂ) (hs : ∀ n, sfam n ≠ 0)
    (n : ℕ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => mixHSAntideriv2 alpha beta sfam n x)
      (mixHSAntideriv1 alpha beta sfam n r) r := by
  unfold mixHSAntideriv2 mixHSAntideriv1
  exact expLinTerm_antideriv_hasDerivAt _ _ (sfam n) (hs n) r

/-! ### Magnitude and the per-rung `‖s‖`-decay gain

Why the tower buys summability: `‖expLinTerm a b s r‖ = ‖a + b·r‖·e^{−r·Re s}`, and each rung's
`antiCoeff` divides the coefficients by `s`.  So on the reflected pole family (`Re s_n > 0`, whence
`e^{−r·Re s_n} ≤ 1` for `r ≥ 0`) the leading-coefficient magnitude drops by a factor `1/‖s_n‖` per
rung — two rungs push the effective decay exponent below `−1` uniformly, which is exactly what makes
the `Kterm` analog (`mixHSAntideriv2`) summable arbitrarily close to `r = 0`. -/

/-- **Magnitude of `expLinTerm`.**  `‖(a + b·r)·e^{−s·r}‖ = ‖a + b·r‖·e^{−r·Re s}` — the exponential
factor is a pure real decay set by `Re s`. -/
theorem expLinTerm_norm (a b s : ℂ) (r : ℝ) :
    ‖expLinTerm a b s r‖ = ‖a + b * (r : ℂ)‖ * Real.exp (-r * s.re) := by
  unfold expLinTerm
  rw [norm_mul, Complex.norm_exp]
  congr 1
  have : (-s * (r : ℂ)).re = -r * s.re := by
    simp [Complex.mul_re]; ring
  rw [this]

/-- **On the reflected family the exponential is a genuine decay.**  For `0 ≤ r` and `0 ≤ Re s`,
`‖expLinTerm a b s r‖ ≤ ‖a + b·r‖` — the envelope is controlled by its polynomial factor alone. -/
theorem expLinTerm_norm_le_of_re_nonneg {a b s : ℂ} {r : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s.re) :
    ‖expLinTerm a b s r‖ ≤ ‖a + b * (r : ℂ)‖ := by
  rw [expLinTerm_norm]
  have hexp : Real.exp (-r * s.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ r * s.re := mul_nonneg hr hs
    linarith
  calc ‖a + b * (r : ℂ)‖ * Real.exp (-r * s.re)
      ≤ ‖a + b * (r : ℂ)‖ * 1 := by
        apply mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ = ‖a + b * (r : ℂ)‖ := mul_one _

/-- **The linear-coefficient of the antiderivative decays by `1/‖s‖`.**
`‖(antiCoeff s a b).2‖ = ‖b‖/‖s‖`. -/
theorem antiCoeff_snd_norm (s a b : ℂ) : ‖(antiCoeff s a b).2‖ = ‖b‖ / ‖s‖ := by
  unfold antiCoeff
  simp

/-- **The constant-coefficient of the antiderivative gains `1/‖s‖`** (leading) and `1/‖s‖²`
(subleading): `‖(antiCoeff s a b).1‖ ≤ ‖a‖/‖s‖ + ‖b‖/‖s‖²`. -/
theorem antiCoeff_fst_norm_le (s a b : ℂ) :
    ‖(antiCoeff s a b).1‖ ≤ ‖a‖ / ‖s‖ + ‖b‖ / ‖s‖ ^ 2 := by
  unfold antiCoeff
  calc ‖-a / s - b / s ^ 2‖
      ≤ ‖-a / s‖ + ‖b / s ^ 2‖ := norm_sub_le _ _
    _ = ‖a‖ / ‖s‖ + ‖b‖ / ‖s‖ ^ 2 := by
        rw [norm_div, norm_div, norm_neg, norm_pow]

/-! ### Summability of the tower — reduced to a coefficient bound

The second antiderivative rung, viewed as an `r`-absorbed `poleExpTerm`, is `Summable` at **every**
`r` for which its coefficient obeys a `‖s‖^p` bound with `p < −1`.  On the reflected family the two
`antiCoeff` divisions supply two spare powers of `1/‖s_n‖` over the raw residue, which is what should
push `p` below `−1` **without** the `rdist > max(σ₀/2, λ₀₁)` threshold that the untowered series
(MML.5) needs — i.e. the tower reaches arbitrarily close to `r = 0`, the mixture counterpart of
`Kterm`'s all-`u>0` summability.  The coefficient bound itself (magnitudes of the double-pole `α_n`,
`β_n` in `‖s_n‖`, the analog of the scalar `residue_term_norm_bound`) is the remaining analysis
obligation, isolated here as the hypothesis `hbound`. -/

/-- The `r`-absorbed coefficient of `mixHSAntideriv2` (its constant-plus-linear envelope, packaged so
the rung is a plain `poleExpTerm`). -/
def mixHSAntideriv2Coeff (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  (-(-alpha n / sfam n - beta n / (sfam n) ^ 2) / sfam n - (-beta n / sfam n) / (sfam n) ^ 2)
    + (-(-beta n / sfam n) / sfam n) * (r : ℂ)

/-- `mixHSAntideriv2` is the plain `poleExpTerm` at its `r`-absorbed coefficient (definitional). -/
theorem mixHSAntideriv2_eq_mixHSterm (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) :
    mixHSAntideriv2 alpha beta sfam n r
      = FMSA.PoleSeries.poleExpTerm (mixHSAntideriv2Coeff alpha beta sfam r) sfam r n := rfl

/-- **Summability of the `Kterm`-analog rung, reduced to the coefficient bound.**  Given the pole
family's linear growth and a `‖s_n‖^p` bound (`p < −1`) on the `r`-absorbed second-antiderivative
coefficient, `mixHSAntideriv2 … r` is `Summable`.  Direct reuse of `poleExpTerm_summable_of_growth` through
`mixHSAntideriv2_eq_mixHSterm`; the point is that the tower's two `1/‖s‖` gains are what make such a
`p < −1` bound attainable at every `r ≥ 0`, threshold-free. -/
theorem mixHSAntideriv2_summable_of_growth {alpha beta sfam : ℕ → ℂ} {r : ℝ} {C p c d : ℝ}
    (hp : p < -1) (hC : 0 ≤ C) (hc : 0 < c) (hd : 0 < d)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖sfam n‖)
    (hbound : ∀ n : ℕ, ‖FMSA.PoleSeries.poleExpTerm (mixHSAntideriv2Coeff alpha beta sfam r) sfam r n‖
      ≤ C * ‖sfam n‖ ^ p) :
    Summable (fun n => mixHSAntideriv2 alpha beta sfam n r) := by
  have hsum := FMSA.PoleSeries.poleExpTerm_summable_of_growth (Bcoef := mixHSAntideriv2Coeff alpha beta sfam r)
    (sfam := sfam) (r := r) hp hC hc hd hgrowth hbound
  exact hsum.congr (fun n => (mixHSAntideriv2_eq_mixHSterm alpha beta sfam r n).symm)

/-! ### Rung 1 — discharging the coefficient bound from `‖s‖`-power bounds on `α, β`

The `hbound` hypothesis of `mixHSAntideriv2_summable_of_growth` is now proved from the *inputs a
concrete pole family actually supplies*: a common `‖s_n‖^q` bound (`q < 1`) on the double-pole
coefficients `α_n`, `β_n`, together with reflected-family positivity (`Re s_n ≥ 0`) and `‖s_n‖ ≥ 1`.
The two `antiCoeff` divisions turn `q` into `q − 2 < −1`, so the tower is summable at **every**
`r ≥ 0` — threshold-free, the mixture form of `Kterm`'s all-`u>0` summability, with **no**
`rdist > max(σ₀/2, λ₀₁)` restriction.  The one remaining concrete task is the `α, β` bounds
themselves (the mixture analog of the scalar `residue_term_norm_bound`), stated here as `hα`, `hβ`. -/

/-- The `Kterm`-rung coefficient in closed form: `α/s² + 2β/s³ + (β/s²)·r` (`s ≠ 0`). -/
theorem mixHSAntideriv2Coeff_eq (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) (hs : sfam n ≠ 0) :
    mixHSAntideriv2Coeff alpha beta sfam r n
      = alpha n / (sfam n) ^ 2 + 2 * beta n / (sfam n) ^ 3
        + (beta n / (sfam n) ^ 2) * (r : ℂ) := by
  unfold mixHSAntideriv2Coeff
  have h2 : (sfam n) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h3 : (sfam n) ^ 3 ≠ 0 := pow_ne_zero 3 hs
  field_simp; ring

/-- **The `Kterm`-rung coefficient norm bound** (`‖s_n‖ ≥ 1`, `r ≥ 0`):
`‖coeff‖ ≤ (‖α_n‖ + (2+r)·‖β_n‖) / ‖s_n‖²`.  The `1/‖s‖³ ≤ 1/‖s‖²` collapse (using `‖s‖ ≥ 1`) folds
the two `antiCoeff` gains into a single `1/‖s‖²`. -/
theorem mixHSAntideriv2Coeff_norm_le (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ)
    (hs : sfam n ≠ 0) (hs1 : 1 ≤ ‖sfam n‖) (hr : 0 ≤ r) :
    ‖mixHSAntideriv2Coeff alpha beta sfam r n‖
      ≤ (‖alpha n‖ + (2 + r) * ‖beta n‖) / ‖sfam n‖ ^ 2 := by
  rw [mixHSAntideriv2Coeff_eq alpha beta sfam r n hs]
  set S := ‖sfam n‖ with hS
  have hSpos : 0 < S := by rw [hS]; exact norm_pos_iff.mpr hs
  have hS2 : (0 : ℝ) < S ^ 2 := by positivity
  have hnormeq : ‖alpha n / (sfam n) ^ 2 + 2 * beta n / (sfam n) ^ 3 + (beta n / (sfam n) ^ 2) * (r : ℂ)‖
      ≤ ‖alpha n‖ / S ^ 2 + 2 * ‖beta n‖ / S ^ 3 + ‖beta n‖ * r / S ^ 2 := by
    have e1 : ‖alpha n / (sfam n) ^ 2‖ = ‖alpha n‖ / S ^ 2 := by rw [norm_div, norm_pow, hS]
    have e2 : ‖2 * beta n / (sfam n) ^ 3‖ = 2 * ‖beta n‖ / S ^ 3 := by
      rw [norm_div, norm_mul, norm_pow, hS, show ‖(2 : ℂ)‖ = 2 from by norm_num]
    have e3 : ‖(beta n / (sfam n) ^ 2) * (r : ℂ)‖ = ‖beta n‖ * r / S ^ 2 := by
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, hS]
      ring
    calc ‖alpha n / (sfam n) ^ 2 + 2 * beta n / (sfam n) ^ 3 + (beta n / (sfam n) ^ 2) * (r : ℂ)‖
        ≤ ‖alpha n / (sfam n) ^ 2‖ + ‖2 * beta n / (sfam n) ^ 3‖
            + ‖(beta n / (sfam n) ^ 2) * (r : ℂ)‖ := norm_add₃_le
      _ = ‖alpha n‖ / S ^ 2 + 2 * ‖beta n‖ / S ^ 3 + ‖beta n‖ * r / S ^ 2 := by rw [e1, e2, e3]
  refine le_trans hnormeq ?_
  have hS3le : 2 * ‖beta n‖ / S ^ 3 ≤ 2 * ‖beta n‖ / S ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) hS2
    nlinarith [hSpos, hs1]
  have hRHS : (‖alpha n‖ + (2 + r) * ‖beta n‖) / S ^ 2
      = ‖alpha n‖ / S ^ 2 + 2 * ‖beta n‖ / S ^ 2 + ‖beta n‖ * r / S ^ 2 := by field_simp; ring
  rw [hRHS]; linarith [hS3le]

/-- **Rung 1 — threshold-free summability of the tower from `‖s‖`-power coefficient bounds.**  With
a common bound `‖α_n‖, ‖β_n‖ ≤ Cc·‖s_n‖^q` (`q < 1`) on the double-pole coefficients, reflected
positivity `Re s_n ≥ 0`, `‖s_n‖ ≥ 1`, and linear pole growth, the `Kterm`-rung series
`Σ_n mixHSAntideriv2` is `Summable` at **every** `r ≥ 0`.  The exponent lands at `p = q − 2 < −1`
(the two `antiCoeff` powers), with no `rdist` threshold — the mixture form of `Kterm`'s all-`u>0`
summability.  The `α, β` bounds are the sole remaining concrete input (the mixture analog of the
scalar `residue_term_norm_bound`). -/
theorem mixHSAntideriv2_summable_of_coeff_bounds {alpha beta sfam : ℕ → ℂ} {r q Cc c d : ℝ}
    (hq : q < 1) (hCc : 0 ≤ Cc) (hc : 0 < c) (hd : 0 < d) (hr : 0 ≤ r)
    (hs1 : ∀ n, 1 ≤ ‖sfam n‖) (hre : ∀ n, 0 ≤ (sfam n).re)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖sfam n‖)
    (hα : ∀ n, ‖alpha n‖ ≤ Cc * ‖sfam n‖ ^ q)
    (hβ : ∀ n, ‖beta n‖ ≤ Cc * ‖sfam n‖ ^ q) :
    Summable (fun n => mixHSAntideriv2 alpha beta sfam n r) := by
  refine mixHSAntideriv2_summable_of_growth (C := Cc * (3 + r)) (p := q - 2)
    (by linarith) (by positivity) hc hd hgrowth (fun n => ?_)
  set S := ‖sfam n‖ with hS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hs1 n)
  have hsne : sfam n ≠ 0 := by rw [← norm_pos_iff, ← hS]; exact hSpos
  -- `‖poleExpTerm coeff‖ = ‖coeff‖·e^{−r·Re s} ≤ ‖coeff‖` on the reflected family
  have hterm : ‖FMSA.PoleSeries.poleExpTerm (mixHSAntideriv2Coeff alpha beta sfam r) sfam r n‖
      ≤ ‖mixHSAntideriv2Coeff alpha beta sfam r n‖ := by
    unfold FMSA.PoleSeries.poleExpTerm
    rw [norm_mul, Complex.norm_exp]
    have hexp : Real.exp (-(sfam n) * (r : ℂ)).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hre' : (-(sfam n) * (r : ℂ)).re = -(r * (sfam n).re) := by
        simp [Complex.mul_re]; ring
      rw [hre']
      have : 0 ≤ r * (sfam n).re := mul_nonneg hr (hre n)
      linarith
    calc ‖mixHSAntideriv2Coeff alpha beta sfam r n‖ * Real.exp (-(sfam n) * (r : ℂ)).re
        ≤ ‖mixHSAntideriv2Coeff alpha beta sfam r n‖ * 1 :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = ‖mixHSAntideriv2Coeff alpha beta sfam r n‖ := mul_one _
  refine le_trans hterm ?_
  refine le_trans (mixHSAntideriv2Coeff_norm_le alpha beta sfam r n hsne (hs1 n) hr) ?_
  have hα' : ‖alpha n‖ ≤ Cc * S ^ q := hα n
  have hβ' : ‖beta n‖ ≤ Cc * S ^ q := hβ n
  have h1 : (2 + r) * ‖beta n‖ ≤ (2 + r) * (Cc * S ^ q) :=
    mul_le_mul_of_nonneg_left hβ' (by linarith)
  have hnum : ‖alpha n‖ + (2 + r) * ‖beta n‖ ≤ Cc * (3 + r) * S ^ q := by nlinarith [hα', h1]
  have hS2 : (0 : ℝ) < S ^ 2 := by positivity
  calc (‖alpha n‖ + (2 + r) * ‖beta n‖) / S ^ 2
      ≤ (Cc * (3 + r) * S ^ q) / S ^ 2 := by
        apply div_le_div_of_nonneg_right hnum hS2.le
    _ = Cc * (3 + r) * S ^ (q - 2) := by
        rw [Real.rpow_sub hSpos, show S ^ 2 = S ^ (2 : ℝ) from by rw [Real.rpow_two]]
        ring

/-! ### Rung 1 — reducing the coefficient bound to the RDF's component magnitudes

The coefficients are `β_n = N(s_n)/det′(s_n)²` and `α_n = N′(s_n)/det′(s_n)² −
N(s_n)·det″(s_n)/det′(s_n)³` (MML.11 / `double_pole_leading_coeff` /
`double_pole_second_coeff_deriv_form`), with `N = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀)ᵢⱼ` the RDF numerator.  The
two lemmas here reduce the `α, β` bounds `mixHSAntideriv2_summable_of_coeff_bounds` wants to
**component** magnitudes — `‖N‖`, `‖N′‖`, `‖N·det″‖` upper, `‖det′‖` lower — using only the
`det′` lower bound (`disk_facts` f3 supplies a *constant* one).  This is the algebraic half of the
mixture `residue_term_norm_bound`; the remaining half is the concrete component magnitudes
themselves (whose crux is the Yukawa numerator `B₁`'s growth on the pole family). -/

/-- **`β = N/det′²` bound from a `det′` lower bound.**  `‖N/D²‖ ≤ ‖N‖/c₀²` when `c₀ ≤ ‖D‖`. -/
theorem coeff_div_sq_norm_le (Nval Dprime : ℂ) {c0 : ℝ} (hc0 : 0 < c0) (hD : c0 ≤ ‖Dprime‖) :
    ‖Nval / Dprime ^ 2‖ ≤ ‖Nval‖ / c0 ^ 2 := by
  rw [norm_div, norm_pow]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  exact pow_le_pow_left₀ hc0.le hD 2

/-- **`α = N′/det′² − N·det″/det′³` bound from a `det′` lower bound.**
`‖N′/D² − N·D″/D³‖ ≤ ‖N′‖/c₀² + ‖N‖·‖D″‖/c₀³` when `c₀ ≤ ‖D‖`. -/
theorem coeff_alpha_norm_le (Ndval Nval Dpp Dprime : ℂ) {c0 : ℝ} (hc0 : 0 < c0)
    (hD : c0 ≤ ‖Dprime‖) :
    ‖Ndval / Dprime ^ 2 - Nval * Dpp / Dprime ^ 3‖
      ≤ ‖Ndval‖ / c0 ^ 2 + ‖Nval‖ * ‖Dpp‖ / c0 ^ 3 := by
  calc ‖Ndval / Dprime ^ 2 - Nval * Dpp / Dprime ^ 3‖
      ≤ ‖Ndval / Dprime ^ 2‖ + ‖Nval * Dpp / Dprime ^ 3‖ := norm_sub_le _ _
    _ = ‖Ndval‖ / ‖Dprime‖ ^ 2 + ‖Nval‖ * ‖Dpp‖ / ‖Dprime‖ ^ 3 := by
        rw [norm_div, norm_pow, norm_div, norm_mul, norm_pow]
    _ ≤ ‖Ndval‖ / c0 ^ 2 + ‖Nval‖ * ‖Dpp‖ / c0 ^ 3 := by
        have h1 : ‖Ndval‖ / ‖Dprime‖ ^ 2 ≤ ‖Ndval‖ / c0 ^ 2 := by
          apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          exact pow_le_pow_left₀ hc0.le hD 2
        have h2 : ‖Nval‖ * ‖Dpp‖ / ‖Dprime‖ ^ 3 ≤ ‖Nval‖ * ‖Dpp‖ / c0 ^ 3 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_left₀ hc0.le hD 3
        linarith [h1, h2]

/-- **Rung 1 — tower summability from the RDF's component magnitude bounds.**  With
`β_n = N(s_n)/det′(s_n)²`, `α_n = N′(s_n)/det′(s_n)² − N(s_n)·det″(s_n)/det′(s_n)³`, a constant
`det′` lower bound `c₀`, and common `‖s_n‖^q` (`q < 1`) upper bounds on `‖N‖`, `‖N′‖` and the product
`‖N‖·‖det″‖`, the `Kterm`-rung series is `Summable` at every `r ≥ 0`.  Reduces (via the two lemmas
above + `mixHSAntideriv2_summable_of_coeff_bounds`) the tower's convergence to exactly the standard
component estimates — the mixture form of `residue_term_norm_bound`'s output feeding
`Kterm_summable_of_pole_family`.

⚠ The `‖N‖·‖det″‖` product is bounded jointly (not each factor separately): `det″` grows
polynomially while `N` is controlled by the (bounded-to-decaying) adjugate times the Yukawa
numerator, so it is their product that lands at a single `‖s_n‖^q`. -/
theorem mixHSAntideriv2_summable_of_component_bounds
    {alpha beta Nval Ndval Dpp Dprime sfam : ℕ → ℂ} {r q CN c0 c d : ℝ}
    (hq : q < 1) (hCN : 0 ≤ CN) (hc : 0 < c) (hd : 0 < d) (hr : 0 ≤ r) (hc0 : 0 < c0)
    (hs1 : ∀ n, 1 ≤ ‖sfam n‖) (hre : ∀ n, 0 ≤ (sfam n).re)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖sfam n‖)
    (hbeta : ∀ n, beta n = Nval n / (Dprime n) ^ 2)
    (halpha : ∀ n, alpha n = Ndval n / (Dprime n) ^ 2 - Nval n * Dpp n / (Dprime n) ^ 3)
    (hDlo : ∀ n, c0 ≤ ‖Dprime n‖)
    (hN : ∀ n, ‖Nval n‖ ≤ CN * ‖sfam n‖ ^ q)
    (hNd : ∀ n, ‖Ndval n‖ ≤ CN * ‖sfam n‖ ^ q)
    (hNDpp : ∀ n, ‖Nval n‖ * ‖Dpp n‖ ≤ CN * ‖sfam n‖ ^ q) :
    Summable (fun n => mixHSAntideriv2 alpha beta sfam n r) := by
  set Cc : ℝ := CN * (1 / c0 ^ 2 + 1 / c0 ^ 3) with hCc
  have hCcpos : 0 ≤ Cc := by rw [hCc]; positivity
  refine mixHSAntideriv2_summable_of_coeff_bounds (q := q) (Cc := Cc)
    hq hCcpos hc hd hr hs1 hre hgrowth (fun n => ?_) (fun n => ?_)
  · -- ‖α n‖ ≤ Cc·‖s_n‖^q
    rw [halpha n]
    refine le_trans (coeff_alpha_norm_le (Ndval n) (Nval n) (Dpp n) (Dprime n) hc0 (hDlo n)) ?_
    have hsq : 0 ≤ ‖sfam n‖ ^ q := Real.rpow_nonneg (le_trans zero_le_one (hs1 n)) q
    have e1 : ‖Ndval n‖ / c0 ^ 2 ≤ CN * ‖sfam n‖ ^ q / c0 ^ 2 := by
      apply div_le_div_of_nonneg_right (hNd n) (by positivity)
    have e2 : ‖Nval n‖ * ‖Dpp n‖ / c0 ^ 3 ≤ CN * ‖sfam n‖ ^ q / c0 ^ 3 := by
      apply div_le_div_of_nonneg_right (hNDpp n) (by positivity)
    have : CN * ‖sfam n‖ ^ q / c0 ^ 2 + CN * ‖sfam n‖ ^ q / c0 ^ 3 = Cc * ‖sfam n‖ ^ q := by
      rw [hCc]; ring
    linarith [e1, e2, this]
  · -- ‖β n‖ ≤ Cc·‖s_n‖^q
    rw [hbeta n]
    refine le_trans (coeff_div_sq_norm_le (Nval n) (Dprime n) hc0 (hDlo n)) ?_
    have hsq : 0 ≤ ‖sfam n‖ ^ q := Real.rpow_nonneg (le_trans zero_le_one (hs1 n)) q
    have hβbd : ‖Nval n‖ / c0 ^ 2 ≤ CN * ‖sfam n‖ ^ q / c0 ^ 2 :=
      div_le_div_of_nonneg_right (hN n) (by positivity)
    have hle : CN * ‖sfam n‖ ^ q / c0 ^ 2 ≤ Cc * ‖sfam n‖ ^ q := by
      rw [hCc]
      have hstep : CN * ‖sfam n‖ ^ q / c0 ^ 2
          ≤ CN * ‖sfam n‖ ^ q / c0 ^ 2 + CN * ‖sfam n‖ ^ q / c0 ^ 3 := by
        have : 0 ≤ CN * ‖sfam n‖ ^ q / c0 ^ 3 := by positivity
        linarith
      refine le_trans hstep (le_of_eq ?_); ring
    linarith [hβbd, hle]

/-! ### Rung 3 — the per-pole integration-by-parts toolkit

The scalar `hcollapse` reduction (`OZFIX.12`, `oz_collapse_of_two_sigma_le`) runs on **per-pole
integration by parts**: the antiderivative tower `Kterm' = Hterm`, `Hterm' = h_explicit_term` turns
the outer `t`-integral of the residue series into endpoint antiderivative values plus a lower-order
integral, which the core series identity then closes.  These lemmas are the mixture analog, built
directly on the proved `HasDerivAt` chain `mixHSAntideriv2 → mixHSAntideriv1 → mixHSterm2`:

* `expLinTerm_continuous` — the shape is continuous in `r` (⇒ interval-integrable).
* `mixHSterm2_integral` / `mixHSAntideriv1_integral` — **per-pole FTC**: `∫_a^b mixHSterm2 =
  [mixHSAntideriv1]_a^b` and `∫_a^b mixHSAntideriv1 = [mixHSAntideriv2]_a^b` (the two rungs).
* `mixHSterm2_weighted_ibp` — **per-pole integration by parts** against a weight `w`:
  `∫_a^b w·mixHSterm2 = [w·mixHSAntideriv1]_a^b − ∫_a^b w′·mixHSAntideriv1`, moving the derivative
  off the term onto `w` — the step that lowers the integrand's `r`-order (the mechanism the collapse's
  outer integral needs).
* `mixHSterm2_integral_tsum` — **termwise integration of the series**: `∫_a^b (∑ₙ mixHSterm2 · n) =
  ∑ₙ [mixHSAntideriv1 n]_a^b`, from `MeasureTheory.integral_tsum` + the per-pole FTC. The `L¹`
  hypothesis holds on the annulus, where the term series is summable (MML.5).

These are the reduction's plumbing.  The *full* matrix `oz_collapse_of_two_sigma_le` additionally
needs (i) Rung 2's matrix `CoreSeriesClosure` (the series identity that closes the endpoint terms) and
(ii) the matrix OZ★ real-space convolution that exhibits the collapse as such an integral identity —
neither built yet. -/

open MeasureTheory intervalIntegral Set ENNReal

/-- The `(a + b·r)·e^{−s·r}` shape is continuous in `r`. -/
theorem expLinTerm_continuous (a b s : ℂ) : Continuous (fun r : ℝ => expLinTerm a b s r) := by
  unfold expLinTerm; fun_prop

/-- **Rung 3 — per-pole FTC, rung 1.**  `∫_a^b mixHSterm2 α β s u du = mixHSAntideriv1(b) −
mixHSAntideriv1(a)` (`mixHSterm2 = mixHSAntideriv1′`, `integral_eq_sub_of_hasDerivAt`). -/
theorem mixHSterm2_integral (alpha beta sfam : ℕ → ℂ) (hs : ∀ n, sfam n ≠ 0) (n : ℕ) (a b : ℝ) :
    ∫ u in a..b, FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n
      = mixHSAntideriv1 alpha beta sfam n b - mixHSAntideriv1 alpha beta sfam n a := by
  have hcont : Continuous (fun u : ℝ => FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n) := by
    have hrw : (fun u : ℝ => FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n)
        = fun u => expLinTerm (alpha n) (beta n) (sfam n) u := by
      funext u; rw [mixHSterm2_eq_expLinTerm]
    rw [hrw]; exact expLinTerm_continuous _ _ _
  exact integral_eq_sub_of_hasDerivAt
    (fun x _ => mixHSAntideriv1_hasDerivAt alpha beta sfam hs n x) (hcont.intervalIntegrable a b)

/-- **Rung 3 — per-pole FTC, rung 2.**  `∫_a^b mixHSAntideriv1 α β s u du = mixHSAntideriv2(b) −
mixHSAntideriv2(a)`. -/
theorem mixHSAntideriv1_integral (alpha beta sfam : ℕ → ℂ) (hs : ∀ n, sfam n ≠ 0) (n : ℕ) (a b : ℝ) :
    ∫ u in a..b, mixHSAntideriv1 alpha beta sfam n u
      = mixHSAntideriv2 alpha beta sfam n b - mixHSAntideriv2 alpha beta sfam n a := by
  have hcont : Continuous (fun u : ℝ => mixHSAntideriv1 alpha beta sfam n u) := by
    unfold mixHSAntideriv1; exact expLinTerm_continuous _ _ _
  exact integral_eq_sub_of_hasDerivAt
    (fun x _ => mixHSAntideriv2_hasDerivAt alpha beta sfam hs n x) (hcont.intervalIntegrable a b)

/-- **Rung 3 — per-pole integration by parts against a weight `w`.**
`∫_a^b w·mixHSterm2 = [w·mixHSAntideriv1]_a^b − ∫_a^b w′·mixHSAntideriv1`.  The step that moves the
derivative off the per-pole term onto the weight (`integral_mul_deriv_eq_deriv_mul`), lowering the
integrand's `r`-order — the core of the collapse's outer-integral reduction. -/
theorem mixHSterm2_weighted_ibp (alpha beta sfam : ℕ → ℂ) (hs : ∀ n, sfam n ≠ 0) (n : ℕ)
    (w w' : ℝ → ℂ) (a b : ℝ) (hw : ∀ x ∈ uIcc a b, HasDerivAt w (w' x) x)
    (hw'int : IntervalIntegrable w' volume a b) :
    ∫ u in a..b, w u * FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n
      = w b * mixHSAntideriv1 alpha beta sfam n b - w a * mixHSAntideriv1 alpha beta sfam n a
        - ∫ u in a..b, w' u * mixHSAntideriv1 alpha beta sfam n u := by
  have hcont : Continuous (fun u : ℝ => FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n) := by
    have hrw : (fun u : ℝ => FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n)
        = fun u => expLinTerm (alpha n) (beta n) (sfam n) u := by
      funext u; rw [mixHSterm2_eq_expLinTerm]
    rw [hrw]; exact expLinTerm_continuous _ _ _
  exact integral_mul_deriv_eq_deriv_mul hw
    (fun x _ => mixHSAntideriv1_hasDerivAt alpha beta sfam hs n x)
    hw'int (hcont.intervalIntegrable a b)

/-- **Rung 3 — termwise integration of the term series.**  `∫_a^b (∑ₙ mixHSterm2 · n) du =
∑ₙ (mixHSAntideriv1(b) − mixHSAntideriv1(a))`, from `MeasureTheory.integral_tsum` (each summand
continuous ⇒ measurable) + the per-pole FTC.  The `L¹` hypothesis `∑ₙ ∫⁻ ‖·‖ₑ ≠ ∞` holds on the
annulus, where the term series is summable (MML.5).  This is what lets the collapse pass from
`r·h₁ = r·(∑ …)` to a per-pole endpoint sum. -/
theorem mixHSterm2_integral_tsum (alpha beta sfam : ℕ → ℂ) (hs : ∀ n, sfam n ≠ 0) (a b : ℝ)
    (hab : a ≤ b)
    (hL1 : ∑' n, ∫⁻ u in Ioc a b, ‖FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n‖ₑ ≠ ∞) :
    ∫ u in a..b, (∑' n, FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n)
      = ∑' n, (mixHSAntideriv1 alpha beta sfam n b - mixHSAntideriv1 alpha beta sfam n a) := by
  rw [intervalIntegral.integral_of_le hab]
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun u => FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n) (volume.restrict (Ioc a b)) := by
    intro n
    have hcont : Continuous (fun u : ℝ => FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n) := by
      have hrw : (fun u : ℝ => FMSA.MixtureHSPoles.mixHSterm2 alpha beta sfam u n)
          = fun u => expLinTerm (alpha n) (beta n) (sfam n) u := by
        funext u; rw [mixHSterm2_eq_expLinTerm]
      rw [hrw]; exact expLinTerm_continuous _ _ _
    exact hcont.aestronglyMeasurable.restrict
  rw [MeasureTheory.integral_tsum hmeas hL1]
  refine tsum_congr (fun n => ?_)
  rw [← intervalIntegral.integral_of_le hab]
  exact mixHSterm2_integral alpha beta sfam hs n a b

/-! ### Rung 2 — the matrix `CoreSeriesClosure` predicate and its non-vacuity

The scalar collapse (`OZFIX.12`) is reduced to a single series identity `CoreSeriesClosure`
(`OzCollapseInner.lean`): the twice-antidifferentiated (`Kterm`-form), **always-summable** residue
series, corrected by its first-order Taylor data at the anchor `σ`, equals an explicit polynomial in
`u` — its content being *the exterior residue series, continued into the core, reproduces the inner
value*. Rung 2 is the matrix analog.

⚠ **The `Kterm`-form, not `Hterm`, is essential** — MML.12's vacuity lesson at the series level. The
`Hterm`-form (`mixHSAntideriv1`) series diverges near `r = 0` (summable only for `q < 0` at a fixed
point, and its *raw* analog only above the MML.5 threshold), so a predicate stated on it would be a
false/vacuous hypothesis on part of its domain. The `Kterm`-form (`mixHSAntideriv2`) is summable at
every `r ≥ 0` (Rung 1), and the first-order-remainder combination
`mixHSAntideriv2(r) − [mixHSAntideriv2(anchor) + (r−anchor)·mixHSAntideriv1(anchor)]` — the Taylor
remainder of `mixHSAntideriv2` at `anchor` (since `mixHSAntideriv2′ = mixHSAntideriv1`) — is
genuinely summable (`mixCoreSeriesClosure_summand_summable`), so the predicate is a statement about a
*convergent* `tsum`.

* `MixCoreSeriesClosure` — the predicate: the remainder series `= poly r` on `(0, anchor]`, `poly` a
  general `ℝ → ℂ` (the matrix analog of the scalar's `π(σ²(u−σ) − (u³−σ³)/3)`; the concrete `poly`
  comes from the inner value, supplied when the matrix OZ★ is built).
* `mixCoreSeriesClosure_summand_summable` — **non-vacuity**: the summand is summable given the three
  Rung-1 summabilities (`mixHSAntideriv2` at `r` and at `anchor`, `mixHSAntideriv1` at `anchor`),
  exactly mirroring the scalar `coreSeriesClosure_summand_summable`.
* `mixHSAntideriv1_summable_of_coeff_bounds` — the `Hterm`-rung summability (one `antiCoeff` gain, so
  exponent `q−1`, needs `q < 0`; the RDF's `q ≈ −1` clears it) that discharges the `mixHSAntideriv1`
  hypothesis. `mixHSAntideriv1Coeff` / `_eq_mixHSterm` / `_norm_le` are its plumbing.

Held as a `Prop` (not an assumed statement), exactly like the scalar `CoreSeriesClosure`: a naive
series-value assumption would be satisfiable by sub-families summing to the wrong value (the
`MZERO.1`-infinitude ≠ pole-exhaustion trap). It is discharged only by a family genuinely enumerating
the poles, and the concrete `poly` needs the matrix OZ★ real-space identity — the one input Rung 2
does not supply. -/

/-- **Rung 2 — the `Hterm`-rung coefficient** `−α/s − β/s² + (−β/s)·r` (as a plain `poleExpTerm`). -/
def mixHSAntideriv1Coeff (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  (-alpha n / sfam n - beta n / (sfam n) ^ 2) + (-beta n / sfam n) * (r : ℂ)

/-- `mixHSAntideriv1` is the plain `poleExpTerm` at its `r`-absorbed coefficient (definitional). -/
theorem mixHSAntideriv1_eq_mixHSterm (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) :
    mixHSAntideriv1 alpha beta sfam n r
      = FMSA.PoleSeries.poleExpTerm (mixHSAntideriv1Coeff alpha beta sfam r) sfam r n := rfl

/-- The `Hterm`-rung coefficient in a sign-explicit closed form (`s ≠ 0`). -/
theorem mixHSAntideriv1Coeff_eq (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) (hs : sfam n ≠ 0) :
    mixHSAntideriv1Coeff alpha beta sfam r n
      = alpha n / (-sfam n) + beta n / (-(sfam n) ^ 2) + (beta n / (-sfam n)) * (r : ℂ) := by
  unfold mixHSAntideriv1Coeff
  have h2 : (sfam n) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp; ring

/-- The `Hterm`-rung coefficient norm bound (`‖s_n‖ ≥ 1`, `r ≥ 0`):
`≤ (‖α‖ + (1+r)·‖β‖) / ‖s_n‖` — **one** `1/‖s‖` gain (vs the `Kterm` rung's `1/‖s‖²`). -/
theorem mixHSAntideriv1Coeff_norm_le (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ)
    (hs : sfam n ≠ 0) (hs1 : 1 ≤ ‖sfam n‖) (hr : 0 ≤ r) :
    ‖mixHSAntideriv1Coeff alpha beta sfam r n‖
      ≤ (‖alpha n‖ + (1 + r) * ‖beta n‖) / ‖sfam n‖ := by
  rw [mixHSAntideriv1Coeff_eq alpha beta sfam r n hs]
  set S := ‖sfam n‖ with hS
  have hSpos : 0 < S := by rw [hS]; exact norm_pos_iff.mpr hs
  have hnormeq : ‖alpha n / (-sfam n) + beta n / (-(sfam n) ^ 2) + (beta n / (-sfam n)) * (r : ℂ)‖
      ≤ ‖alpha n‖ / S + ‖beta n‖ / S ^ 2 + ‖beta n‖ * r / S := by
    have e1 : ‖alpha n / (-sfam n)‖ = ‖alpha n‖ / S := by rw [norm_div, norm_neg, hS]
    have e2 : ‖beta n / (-(sfam n) ^ 2)‖ = ‖beta n‖ / S ^ 2 := by
      rw [norm_div, norm_neg, norm_pow, hS]
    have e3 : ‖(beta n / (-sfam n)) * (r : ℂ)‖ = ‖beta n‖ * r / S := by
      rw [norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, hS]
      ring
    calc ‖alpha n / (-sfam n) + beta n / (-(sfam n) ^ 2) + (beta n / (-sfam n)) * (r : ℂ)‖
        ≤ ‖alpha n / (-sfam n)‖ + ‖beta n / (-(sfam n) ^ 2)‖ + ‖(beta n / (-sfam n)) * (r : ℂ)‖ :=
          norm_add₃_le
      _ = ‖alpha n‖ / S + ‖beta n‖ / S ^ 2 + ‖beta n‖ * r / S := by rw [e1, e2, e3]
  refine le_trans hnormeq ?_
  have hS2 : (0 : ℝ) < S ^ 2 := by positivity
  have hstep : ‖beta n‖ / S ^ 2 ≤ ‖beta n‖ / S := by
    apply div_le_div_of_nonneg_left (norm_nonneg _) hSpos
    nlinarith [hSpos, hs1]
  have hRHS : (‖alpha n‖ + (1 + r) * ‖beta n‖) / S
      = ‖alpha n‖ / S + ‖beta n‖ / S + ‖beta n‖ * r / S := by field_simp; ring
  rw [hRHS]; linarith [hstep]

/-- **Rung 2 — `Hterm`-rung summability.**  With `‖α_n‖, ‖β_n‖ ≤ Cc·‖s_n‖^q` and `q < 0` (one
`antiCoeff` gain lands the exponent at `q − 1 < −1`), reflected positivity and growth,
`Σ_n mixHSAntideriv1 · r` is `Summable`.  The RDF's `q ≈ −1` clears `q < 0`.  Discharges the
`mixHSAntideriv1` hypothesis of the non-vacuity lemma. -/
theorem mixHSAntideriv1_summable_of_coeff_bounds {alpha beta sfam : ℕ → ℂ} {r q Cc c d : ℝ}
    (hq : q < 0) (hCc : 0 ≤ Cc) (hc : 0 < c) (hd : 0 < d) (hr : 0 ≤ r)
    (hs1 : ∀ n, 1 ≤ ‖sfam n‖) (hre : ∀ n, 0 ≤ (sfam n).re)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖sfam n‖)
    (hα : ∀ n, ‖alpha n‖ ≤ Cc * ‖sfam n‖ ^ q) (hβ : ∀ n, ‖beta n‖ ≤ Cc * ‖sfam n‖ ^ q) :
    Summable (fun n => mixHSAntideriv1 alpha beta sfam n r) := by
  have hsum := FMSA.PoleSeries.poleExpTerm_summable_of_growth
    (Bcoef := mixHSAntideriv1Coeff alpha beta sfam r) (sfam := sfam) (r := r)
    (C := Cc * (2 + r)) (p := q - 1) (by linarith) (by positivity) hc hd hgrowth (fun n => ?_)
  · exact hsum.congr (fun n => (mixHSAntideriv1_eq_mixHSterm alpha beta sfam r n).symm)
  · set S := ‖sfam n‖ with hS
    have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hs1 n)
    have hsne : sfam n ≠ 0 := by rw [← norm_pos_iff, ← hS]; exact hSpos
    have hterm : ‖FMSA.PoleSeries.poleExpTerm (mixHSAntideriv1Coeff alpha beta sfam r) sfam r n‖
        ≤ ‖mixHSAntideriv1Coeff alpha beta sfam r n‖ := by
      unfold FMSA.PoleSeries.poleExpTerm
      rw [norm_mul, Complex.norm_exp]
      have hexp : Real.exp (-(sfam n) * (r : ℂ)).re ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hre' : (-(sfam n) * (r : ℂ)).re = -(r * (sfam n).re) := by
          simp [Complex.mul_re]; ring
        rw [hre']; nlinarith [mul_nonneg hr (hre n)]
      calc ‖mixHSAntideriv1Coeff alpha beta sfam r n‖ * Real.exp (-(sfam n) * (r : ℂ)).re
          ≤ ‖mixHSAntideriv1Coeff alpha beta sfam r n‖ * 1 :=
            mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = ‖mixHSAntideriv1Coeff alpha beta sfam r n‖ := mul_one _
    refine le_trans hterm ?_
    refine le_trans (mixHSAntideriv1Coeff_norm_le alpha beta sfam r n hsne (hs1 n) hr) ?_
    have hα' : ‖alpha n‖ ≤ Cc * S ^ q := hα n
    have hβ' : ‖beta n‖ ≤ Cc * S ^ q := hβ n
    have h1 : (1 + r) * ‖beta n‖ ≤ (1 + r) * (Cc * S ^ q) :=
      mul_le_mul_of_nonneg_left hβ' (by linarith)
    have hnum : ‖alpha n‖ + (1 + r) * ‖beta n‖ ≤ Cc * (2 + r) * S ^ q := by nlinarith [hα', h1]
    calc (‖alpha n‖ + (1 + r) * ‖beta n‖) / S
        ≤ (Cc * (2 + r) * S ^ q) / S := by apply div_le_div_of_nonneg_right hnum hSpos.le
      _ = Cc * (2 + r) * S ^ (q - 1) := by
          rw [Real.rpow_sub hSpos, Real.rpow_one]; ring

/-- **Rung 2 — the matrix `CoreSeriesClosure` predicate.**  The `Kterm`-form first-order-remainder
series equals `poly r` on `(0, anchor]`.  The `Kterm`-form (`mixHSAntideriv2`) is used so the series
converges everywhere (Rung 1) — the `Hterm`-form would be vacuous near `r = 0` (MML.12 lesson).
`poly` is a general `ℝ → ℂ`; its concrete value comes from the inner core, via the (unbuilt) matrix
OZ★. Held as a `Prop`, not an axiom (the sub-family / pole-exhaustion trap). -/
def MixCoreSeriesClosure (alpha beta sfam : ℕ → ℂ) (anchor : ℝ) (poly : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r ≤ anchor →
    (∑' n, (mixHSAntideriv2 alpha beta sfam n r - mixHSAntideriv2 alpha beta sfam n anchor
        - ((r - anchor : ℝ) : ℂ) * mixHSAntideriv1 alpha beta sfam n anchor)) = poly r

/-- **Rung 2 — non-vacuity of `MixCoreSeriesClosure`.**  The summand — the first-order Taylor
remainder of `mixHSAntideriv2` at `anchor` (`mixHSAntideriv2′ = mixHSAntideriv1`) — is `Summable`
given the three Rung-1 summabilities.  So the predicate is a statement about a convergent `tsum`,
not a vacuous one.  Mirrors the scalar `coreSeriesClosure_summand_summable`. -/
theorem mixCoreSeriesClosure_summand_summable {alpha beta sfam : ℕ → ℂ} {r anchor : ℝ}
    (h2r : Summable (fun n => mixHSAntideriv2 alpha beta sfam n r))
    (h2a : Summable (fun n => mixHSAntideriv2 alpha beta sfam n anchor))
    (h1a : Summable (fun n => mixHSAntideriv1 alpha beta sfam n anchor)) :
    Summable (fun n => mixHSAntideriv2 alpha beta sfam n r - mixHSAntideriv2 alpha beta sfam n anchor
        - ((r - anchor : ℝ) : ℂ) * mixHSAntideriv1 alpha beta sfam n anchor) :=
  (h2r.sub h2a).sub (h1a.mul_left _)

end

end FMSA.MixtureRDF
