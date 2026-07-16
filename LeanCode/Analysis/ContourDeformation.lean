/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Contour deformation for finitely many off-center holes (general-purpose, not project-specific)

**Why this file exists.** `OZFIX.6` (`Lean_code/proof_notes_ozfix.md`) needs a genuine Cauchy
residue theorem — the classical fact that a large circle's contour integral equals `2πi` times the
sum of residues at finitely many poles inside it — to close the algebraic collapse
`oz_forcing(r)+oz_linear_op[h_explicit](r) = h_explicit(r)` (found, by direct numerical check, to
require the *full* residue series, not a termwise argument). A dedicated reconnaissance pass
(2026-07-15) confirmed this machinery is **absent from Mathlib** (`v4.31.0`, commit `fabf563a`):
no `Complex.residue` definition, no winding number (hence no argument principle/Rouché), no general
Mittag-Leffler theorem, no contour-based Fourier/Laplace inversion — corroborated by Mathlib's own
`docs/1000.yaml` tracker, which lists "Residue theorem," "Mittag-Leffler's theorem," and "Rouché's
theorem" as tracked but unformalized. Group MZERO's Route B (`MZERO.8`–`MZERO.11`, `proof_notes_yukawa_wh.md`)
independently hit the identical gap ("Mathlib has NO ready Rouché/argument-principle").

**What Mathlib *does* have, and why it's not quite enough.** The disk Cauchy integral formula
(`Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`) already gives, for free, the
"small-circle integral around a *single* simple pole equals `2πi·residue`" fact — no axiom needed
for that half (see `circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles` below, a genuine theorem).
Mathlib also has an annulus deformation theorem
(`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`, Cauchy–Goursat for an
annulus) — but it only handles a *single* hole **concentric** with the outer circle; it does not
apply even to a single *off-center* hole, let alone finitely many poles scattered at different
points. The genuinely missing piece — proved classically via a keyhole/slit contour argument, real
topological content Mathlib currently has no machinery for (no winding numbers, no general contour
API beyond rectangles/circles) — is exactly the axiom below: deformation invariance for finitely
many *off-center* holes.

**Scope discipline.** This is deliberately the *narrowest* piece that closes the gap, not a
general-purpose "axiomatize the residue theorem" statement: stated purely in terms of Mathlib's
own `circleIntegral`/`C(c,R)` vocabulary (no new geometric definitions, no abstract notion of
"residue"), restricted to circles (not general Jordan contours, which the application never
needs), and everything else (the per-pole `2πi·residue` value itself) is derived as a genuine
theorem from *already-proved* Mathlib content, not folded into the axiom. This is a
general-purpose, project-independent addition (no `FMSA.HardSphere`/`FMSA.YukawaDCF` dependency,
root namespace, general `E`) — reusable by both `OZFIX.6` and Y2's Route B.

## Results

* `circleIntegral_eq_sum_of_small_circles` — the axiom: a big circle's integral of `f` equals the
  sum of finitely many disjoint small circles' integrals, given `f` continuous/differentiable
  (off a countable exceptional set) on the big closed disk minus the small open/closed disks.
* `circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles` — genuine theorem (no new axiom beyond the
  one above): specializes to `f` with a simple pole `g i z/(z-c' i)` at each small-circle center,
  concluding `∮_{C(c,R)} f = ∑ i, 2πi·g i (c' i)` — the actual finite residue-sum formula.

**Status:** ✓ DONE. `circleIntegral_eq_sum_of_small_circles` is a new named axiom (Phase 1 of the
plan recorded in `proof_notes_ozfix.md` `OZFIX.6`);
`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles` is a genuine theorem, `#print axioms`
confirms it depends on exactly this one new axiom plus the standard three.

## Half-disk boundary variant (Route B, 2026-07-15)

`OZFIX.6`'s **Route B** (whole-series Fourier inversion via a growing contour, the alternative to
the termwise Route A pursued via `OZFIX.9`) needs to close a *semicircular* contour — `[-R,R]`
diameter plus the upper arc — not a full circle: `jordan_lemma_arc_bound`
(`LeanCode/Analysis/JordanLemma.lean`, itself fully provable, no axiom) bounds only the arc, and
turning that into a residue-sum identity needs the closed-contour fact for *this* shape. This is a
genuinely different outer boundary from the circle above (same keyhole/slit topological content,
Mathlib has no more machinery for one shape than the other), so it needs its own axiom —
`halfDiskBoundary_eq_sum_of_small_circles` below, with `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`
its genuine-theorem specialization, mirroring the circle pair above exactly (same proof shape,
reusing Mathlib's disk Cauchy integral formula per pole).
-/

open Set Metric Complex

noncomputable section

/-- **Contour deformation for finitely many off-center holes.** If `f : ℂ → E` is continuous on
the closed big disk minus finitely many pairwise-disjoint *open* small disks, and complex
differentiable (off a countable exceptional set `s`) on the big closed disk minus the small
*closed* disks, then the big circle's integral of `f` equals the sum of the small circles'
integrals. This is the classical keyhole/slit-contour deformation fact (real topological content:
Mathlib has no winding numbers, no residue theorem, no general contour API beyond rectangles and
concentric annuli) — see the file docstring for the precise gap this closes. Generalizes Mathlib's
own `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable` (single hole,
*concentric* with the outer circle only) to finitely many *off-center* holes. -/
axiom circleIntegral_eq_sum_of_small_circles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} (hr'pos : ∀ i, 0 < r' i)
    (hinside : ∀ i, closedBall (c' i) (r' i) ⊆ ball c R)
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ (closedBall c R \ ⋃ i, closedBall (c' i) (r' i)) \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = ∑ i, ∮ z in C(c' i, r' i), f z

/-- **Finite simple-pole residue-sum formula** — genuine theorem, no new axiom beyond
`circleIntegral_eq_sum_of_small_circles`. Combines the deformation axiom (reducing the big-circle
integral to a sum of small-circle integrals) with Mathlib's own disk Cauchy integral formula
(`circleIntegral_div_sub_of_differentiable_on_off_countable`, applied once per pole to evaluate
each small-circle integral in closed form) to get the actual residue-sum identity: for `f` with a
simple pole `g i z/(z-c' i)` at each hole's center, `∮_{C(c,R)} f = ∑ i, 2πi·g i (c' i)`. -/
theorem circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} (hr'pos : ∀ i, 0 < r' i)
    (hinside : ∀ i, closedBall (c' i) (r' i) ⊆ ball c R)
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ (closedBall c R \ ⋃ i, closedBall (c' i) (r' i)) \ s, DifferentiableAt ℂ f z)
    {g : ι → ℂ → ℂ} (hgeq : ∀ i, ∀ z ∈ closedBall (c' i) (r' i), f z = g i z / (z - c' i))
    (hgc : ∀ i, ContinuousOn (g i) (closedBall (c' i) (r' i)))
    (hgd : ∀ i, ∀ z ∈ ball (c' i) (r' i) \ s, DifferentiableAt ℂ (g i) z) :
    (∮ z in C(c, R), f z) = ∑ i, (2 * (Real.pi : ℂ) * I) * g i (c' i) := by
  rw [circleIntegral_eq_sum_of_small_circles hR hr'pos hinside hdisj hs hc hd]
  apply Finset.sum_congr rfl
  intro i _
  have hcong : (∮ z in C(c' i, r' i), f z) = ∮ z in C(c' i, r' i), g i z / (z - c' i) := by
    apply circleIntegral.integral_congr (hr'pos i).le
    intro z hz
    exact hgeq i z (sphere_subset_closedBall hz)
  rw [hcong]
  exact circleIntegral_div_sub_of_differentiable_on_off_countable hs (mem_ball_self (hr'pos i))
    (hgc i) (hgd i)

/-- **Contour deformation for the upper half-disk boundary, finitely many off-center holes.**
Half-disk analogue of `circleIntegral_eq_sum_of_small_circles`: if `f : ℂ → E` is continuous on
the closed upper half-disk minus finitely many pairwise-disjoint *open* small disks (all strictly
inside the *open* upper half-disk), and complex differentiable (off a countable exceptional set
`s`) on the closed half-disk minus the small *closed* disks, then the half-disk's boundary
integral (`[-R,R]` diameter, then the upper semicircular arc back, matching
`jordan_lemma_arc_bound`'s exact parametrization for easy composition) equals the sum of the small
circles' integrals. Same keyhole/slit-contour topological content as
`circleIntegral_eq_sum_of_small_circles`, just a differently-shaped outer boundary — see the file
docstring for why Mathlib has no ready machinery for either shape. -/
axiom halfDiskBoundary_eq_sum_of_small_circles {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 0 < R)
    {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} (hr'pos : ∀ i, 0 < r' i)
    (hinside : ∀ i, closedBall (c' i) (r' i) ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, closedBall (c' i) (r' i)) \ s,
      DifferentiableAt ℂ f z) :
    ((∫ x in (-R)..R, f (x : ℂ)) +
        ∫ θ in (0:ℝ)..Real.pi,
          (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
            f ((R:ℂ) * Complex.exp (θ * Complex.I))) =
      ∑ i, ∮ z in C(c' i, r' i), f z

/-- **Finite simple-pole residue-sum formula, half-disk boundary** — genuine theorem, no new axiom
beyond `halfDiskBoundary_eq_sum_of_small_circles`, mirroring
`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles`'s derivation exactly. -/
theorem halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} (hr'pos : ∀ i, 0 < r' i)
    (hinside : ∀ i, closedBall (c' i) (r' i) ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, closedBall (c' i) (r' i)) \ s,
      DifferentiableAt ℂ f z)
    {g : ι → ℂ → ℂ} (hgeq : ∀ i, ∀ z ∈ closedBall (c' i) (r' i), f z = g i z / (z - c' i))
    (hgc : ∀ i, ContinuousOn (g i) (closedBall (c' i) (r' i)))
    (hgd : ∀ i, ∀ z ∈ ball (c' i) (r' i) \ s, DifferentiableAt ℂ (g i) z) :
    ((∫ x in (-R)..R, f (x : ℂ)) +
        ∫ θ in (0:ℝ)..Real.pi,
          (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
            f ((R:ℂ) * Complex.exp (θ * Complex.I))) =
      ∑ i, (2 * (Real.pi : ℂ) * I) * g i (c' i) := by
  rw [halfDiskBoundary_eq_sum_of_small_circles hR hr'pos hinside hdisj hs hc hd]
  apply Finset.sum_congr rfl
  intro i _
  have hcong : (∮ z in C(c' i, r' i), f z) = ∮ z in C(c' i, r' i), g i z / (z - c' i) := by
    apply circleIntegral.integral_congr (hr'pos i).le
    intro z hz
    exact hgeq i z (sphere_subset_closedBall hz)
  rw [hcong]
  exact circleIntegral_div_sub_of_differentiable_on_off_countable hs (mem_ball_self (hr'pos i))
    (hgc i) (hgd i)

end
