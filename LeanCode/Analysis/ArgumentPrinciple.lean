/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.ContourDeformation

/-!
# The argument principle / signed zero-pole count — no new axiom

Group MA (`MATH_AXIOMS.md`), task `MA.11`. The classical **argument principle**: for a meromorphic
`f` whose zeros/poles inside a circle `C(c,R)` are simple (or of finite order), the contour integral
of the logarithmic derivative counts them,

  `(1/2πi) ∮_{C(c,R)} f'/f = Z − P`

(zeros minus poles, each weighted by order). Reconnaissance (2026-07-17) confirmed Mathlib has
**no** argument principle, Rouché, winding number, or `∮ f'/f` result — corroborated by its own
`docs/1000.yaml`, which lists "Rouché's theorem" as tracked-but-unformalized. It is nonetheless
**derivable, not axiom-worthy**: it is the MA.1 contour-deformation axiom
(`circleIntegral_eq_sum_of_small_circles`) applied to `F := logDeriv f`, together with the one
genuinely new bridge below.

## The per-circle bridge (the new content)

Near a point `k` of order `n` (a zero if `n>0`, a pole if `n<0`), `f` factors as `(w-k)^n · g` with
`g` analytic and nonzero, and the logarithmic derivative **splits**:

  `logDeriv f = n·(w-k)⁻¹ + logDeriv g`   (`logDeriv_zpow_smul_eq`).

The first term integrates to `2πi·n` (`circleIntegral.integral_sub_center_inv`); the second vanishes
by Cauchy–Goursat (`logDeriv g` is analytic on the disk since `g` is analytic and nonzero). Hence

  `∮_{C(k,r)} logDeriv f = 2πi·n`   (`circleIntegral_logDeriv_zpow_smul_eq`, **axiom-clean**).

## Results

* `logDeriv_zpow_smul_eq` — the pointwise split `logDeriv ((·-k)^n · g) = n·(z-k)⁻¹ + logDeriv g`.
* `circleIntegral_logDeriv_zpow_smul_eq` — the per-circle bridge `∮ = 2πi·n`; **no axiom**
  (`#print axioms` = the standard three).
* `argumentPrinciple_sum` — MA.1 + the bridge: `∮_{C(c,R)} F = ∑ i, 2πi·(n i)` for `F = logDeriv f`
  with per-hole factorizations. `#print axioms` = MA.1's `circleIntegral_eq_sum_of_small_circles`
  plus the standard three — **no new axiom for MA.11**.
* `argumentPrinciple_count` — the same with `2πi` factored out: `∮ = 2πi·∑ i, (n i)`; for simple
  zeros/poles (`n i = ±1`) the sum is exactly `Z − P`.

## Scope

Mirroring the existing pattern in `ContourDeformation.lean`
(`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles`, which takes each pole's numerator as a
hypothesis rather than deriving the pole structure), the local factorization at each singularity is
supplied as an explicit hypothesis (`g i` analytic-nonzero, and `F = logDeriv ((·-c' i)^{n i}·g i)`
on the small sphere). This is the honest general statement and avoids re-proving a removable-
singularity gluing that Mathlib's `meromorphicOrderAt` factorization — a *punctured-neighborhood-of-
center* fact — does not directly provide on the outer contour. **Rouché's theorem is a genuinely
separate effort** (it needs winding-number / homotopy-invariance machinery Mathlib lacks) and is not
included here.
-/

open Set Metric Complex circleIntegral

noncomputable section

/-- Pointwise split of the log-derivative of a factored function
`(w-k)^n * g w` at a point `z ≠ k` where `g` is differentiable and nonzero. -/
lemma logDeriv_zpow_smul_eq {k : ℂ} {g : ℂ → ℂ} {n : ℤ} {z : ℂ} (hz : z ≠ k)
    (hg : DifferentiableAt ℂ g z) (hgz : g z ≠ 0) :
    logDeriv (fun w => (w - k) ^ n * g w) z = (n : ℂ) * (z - k)⁻¹ + logDeriv g z := by
  have hlin : DifferentiableAt ℂ (fun w => w - k) z := differentiableAt_id.sub_const k
  have hlinz : (z - k) ≠ 0 := sub_ne_zero.mpr hz
  have hpow : DifferentiableAt ℂ (fun w => (w - k) ^ n) z := hlin.zpow (Or.inl hlinz)
  have hpowne : (z - k) ^ n ≠ 0 := zpow_ne_zero n hlinz
  rw [logDeriv_mul z hpowne hgz hpow hg]
  congr 1
  rw [logDeriv_fun_zpow hlin n, logDeriv_apply]
  have hderiv : deriv (fun w => w - k) z = 1 := by simp
  rw [hderiv, one_div]

/-- **Per-circle argument-principle bridge.** For `g` analytic and nonzero on a neighbourhood of the
closed disk `closedBall k r` and `n : ℤ`, the circle integral of the log-derivative of the factored
function `(w-k)^n * g w` equals `2πi·n`. This is the single-singularity heart of the argument
principle: `n` is the order of the zero (if `n>0`) or pole (if `n<0`) at the center. -/
theorem circleIntegral_logDeriv_zpow_smul_eq {k : ℂ} {r : ℝ} (hr : 0 < r)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall k r))
    (hgne : ∀ z ∈ closedBall k r, g z ≠ 0) (n : ℤ) :
    (∮ z in C(k, r), logDeriv (fun w => (w - k) ^ n * g w) z)
      = 2 * (Real.pi : ℂ) * I * (n : ℂ) := by
  -- log-derivative of g is analytic (hence continuous/differentiable) on a nbhd of the closed disk
  have hana : AnalyticOnNhd ℂ (logDeriv g) (closedBall k r) := by
    intro z hz
    have : AnalyticAt ℂ (fun w => deriv g w / g w) z := (hg z hz).deriv.div (hg z hz) (hgne z hz)
    exact this
  -- rewrite the integrand on the sphere via the pointwise split
  have hsplit : EqOn (fun z => logDeriv (fun w => (w - k) ^ n * g w) z)
      (fun z => (n : ℂ) * (z - k)⁻¹ + logDeriv g z) (sphere k r) := by
    intro z hz
    have hzk : z ≠ k := Metric.ne_of_mem_sphere hz hr.ne'
    have hzcl : z ∈ closedBall k r := sphere_subset_closedBall hz
    exact logDeriv_zpow_smul_eq hzk (hg z hzcl).differentiableAt (hgne z hzcl)
  rw [circleIntegral.integral_congr hr.le hsplit]
  -- integrability of the two pieces on the sphere
  have hcont_inv : ContinuousOn (fun z => (n : ℂ) * (z - k)⁻¹) (sphere k r) := by
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn)
    intro z hz
    exact sub_ne_zero.mpr (Metric.ne_of_mem_sphere hz hr.ne')
  have hcont_log : ContinuousOn (logDeriv g) (sphere k r) :=
    hana.continuousOn.mono sphere_subset_closedBall
  have hint1 : CircleIntegrable (fun z => (n : ℂ) * (z - k)⁻¹) k r :=
    hcont_inv.circleIntegrable hr.le
  have hint2 : CircleIntegrable (logDeriv g) k r := hcont_log.circleIntegrable hr.le
  rw [circleIntegral.integral_add hint1 hint2]
  -- evaluate the two pieces
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv k hr.ne']
  have hzero : (∮ z in C(k, r), logDeriv g z) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      (hana.continuousOn)
    intro z hz
    exact (hana z (ball_subset_closedBall hz.1)).differentiableAt
  rw [hzero]
  ring

/-- **Argument principle (finite signed zero/pole count).** Let `F` be the log-derivative of a
meromorphic function whose only zeros/poles inside the big circle `C(c,R)` are at the points
`c' i`, where near `c' i` the function factors as `(w - c' i)^(n i) * g i w` with `g i` analytic and
nonzero. Then `∮_{C(c,R)} F = ∑ i, 2πi·(n i)`, i.e. `2πi` times the signed count of zeros minus
poles (each weighted by its order). Built from the MA.1 contour-deformation axiom plus the
per-circle bridge `circleIntegral_logDeriv_zpow_smul_eq`. -/
theorem argumentPrinciple_sum {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} (hr'pos : ∀ i, 0 < r' i)
    (hinside : ∀ i, closedBall (c' i) (r' i) ⊆ ball c R)
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn F (closedBall c R \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ (closedBall c R \ ⋃ i, closedBall (c' i) (r' i)) \ s, DifferentiableAt ℂ F z)
    {n : ι → ℤ} {g : ι → ℂ → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (closedBall (c' i) (r' i)))
    (hgne : ∀ i, ∀ z ∈ closedBall (c' i) (r' i), g i z ≠ 0)
    (hFlog : ∀ i, EqOn F (logDeriv (fun w => (w - c' i) ^ n i * g i w)) (sphere (c' i) (r' i))) :
    (∮ z in C(c, R), F z) = ∑ i, 2 * (Real.pi : ℂ) * I * (n i : ℂ) := by
  rw [circleIntegral_eq_sum_of_small_circles hR hr'pos hinside hdisj hs hc hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [circleIntegral.integral_congr (hr'pos i).le (hFlog i)]
  exact circleIntegral_logDeriv_zpow_smul_eq (hr'pos i) (hg i) (hgne i) (n i)

/-- **Argument principle, count form.** Same hypotheses as `argumentPrinciple_sum`, with the
constant `2πi` pulled out: `∮_{C(c,R)} F = 2πi·∑ i, (n i)`. The sum `∑ i, n i` is the signed count
(each order-`n i` zero contributes `+n i`, each order-`n i` pole `−|n i|`); for simple zeros/poles
(`n i = ±1`) it is exactly `Z − P`. -/
theorem argumentPrinciple_count {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} (hr'pos : ∀ i, 0 < r' i)
    (hinside : ∀ i, closedBall (c' i) (r' i) ⊆ ball c R)
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn F (closedBall c R \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ (closedBall c R \ ⋃ i, closedBall (c' i) (r' i)) \ s, DifferentiableAt ℂ F z)
    {n : ι → ℤ} {g : ι → ℂ → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (closedBall (c' i) (r' i)))
    (hgne : ∀ i, ∀ z ∈ closedBall (c' i) (r' i), g i z ≠ 0)
    (hFlog : ∀ i, EqOn F (logDeriv (fun w => (w - c' i) ^ n i * g i w)) (sphere (c' i) (r' i))) :
    (∮ z in C(c, R), F z) = 2 * (Real.pi : ℂ) * I * (∑ i, (n i : ℂ)) := by
  rw [argumentPrinciple_sum hR hr'pos hinside hdisj hs hc hd hg hgne hFlog, Finset.mul_sum]

end
