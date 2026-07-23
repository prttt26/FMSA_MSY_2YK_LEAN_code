/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Homotopy invariance of contour integrals (axiom), general-purpose

Group MA (`MATH_AXIOMS.md`), task `MA.8` (user-requested, following the "unified residue-theorem
axiom?" design discussion). The classical **homotopy form of Cauchy's theorem** (Ahlfors Ch. 4
Thm 16 / Conway IV.6.7): if two `C¹` loops are freely homotopic through loops inside an open set
`U`, and `f` is holomorphic on `U` (continuous everywhere, differentiable off a countable set),
their contour integrals agree.

**Design rationale.** This is the one "general residue theorem" candidate statable in current
Mathlib vocabulary (no winding numbers, no general contour API — a fully general Jordan-curve
statement cannot even be written down without new definitions, which the admissibility discipline
forbids inside axioms). It is the *fundamental* principle: Axioms 1 and 2 (circle and half-disk
contour deformation, `ContourDeformation.lean`) are classical corollaries — via explicit
keyhole-homotopy constructions that are deferred as future work (each is a substantial Lean
development; until they land, Axioms 1/2 remain independent). Loops are taken `C¹` on `[0,1]`
with explicit derivative data — piecewise-`C¹` consumers reparametrize with flat spots at the
corners (standard trick, keeps the statement corner-free).

**Statement scrutiny** (against the failure modes that produced this group's two false first
drafts, see `MATH_AXIOMS.md`): no value-set hypotheses (junk-value trap n/a); no limits or
infinite sums (convergence-mode trap n/a); the free-homotopy-through-**loops** condition
(`hHloop`, `H a 0 = H a 1` for every intermediate `a`) is essential and present — without it the
statement is false (open intermediate curves acquire endpoint contributions); derivative data is
tied to the curves by `HasDerivAt` (no junk mismatch); the homotopy itself needs only continuity
(classical). Numerically pre-checked (scratch `homotopy_check.py`, 2026-07-16) with positive,
null-homotopic, and negative controls: two genuinely different loops around two poles with a
verified pole-avoiding straight-line homotopy agree to `6·10⁻¹⁰` (= `2πi·Σres`); a null-homotopic
loop integrates to `10⁻¹⁶`; loops in *different* homotopy classes differ by exactly
`|2πi·res₁| = 4.7851` (the hypothesis does real work).

**Derived here (genuine theorems):** `contourIntegral_eq_zero_of_null_homotopic` (specialize
`γ₁` to a constant loop) and `circleIntegral_eq_unitLoop_integral` (the bridge identifying
`∮ z in C(c,R), f z` with the axiom's normalized unit-interval loop form — no axiom needed,
`intervalIntegral.smul_integral_comp_mul_left`).

**Retirement condition.** Same event as Axioms 1/2: Mathlib gaining winding-number/homotopy
machinery (`docs/1000.yaml`). Conversely, once keyhole homotopies are formalized *here*, Axioms
1/2 retire into corollaries of THIS axiom — the intended long-term direction.
-/

open Set Metric Complex Filter Topology intervalIntegral

noncomputable section

/-- **Homotopy invariance of contour integrals** (classical homotopy form of Cauchy's theorem).
If the `C¹` loops `γ₀, γ₁ : [0,1] → U` (explicit derivative data `γ₀', γ₁'`, continuous) are
freely homotopic through loops within the open set `U` (continuous `H`, `H 0 = γ₀`, `H 1 = γ₁`,
each intermediate curve closed, image in `U`), and `f` is continuous on `U` and differentiable
off a countable set, then `∫₀¹ γ₀'(t) • f(γ₀ t) dt = ∫₀¹ γ₁'(t) • f(γ₁ t) dt`. -/
axiom contourIntegral_eq_of_homotopic_loops {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    {γ₀ γ₁ γ₀' γ₁' : ℝ → ℂ} {H : ℝ → ℝ → ℂ}
    (hγ₀ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ₀ (γ₀' t) t)
    (hγ₁ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ₁ (γ₁' t) t)
    (hγ₀'c : ContinuousOn γ₀' (Set.Icc 0 1))
    (hγ₁'c : ContinuousOn γ₁' (Set.Icc 0 1))
    (hHc : ContinuousOn (Function.uncurry H) (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
    (hH0 : ∀ t ∈ Set.Icc (0:ℝ) 1, H 0 t = γ₀ t)
    (hH1 : ∀ t ∈ Set.Icc (0:ℝ) 1, H 1 t = γ₁ t)
    (hHloop : ∀ a ∈ Set.Icc (0:ℝ) 1, H a 0 = H a 1)
    (hHU : ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, H a t ∈ U)
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f U)
    (hd : ∀ z ∈ U \ s, DifferentiableAt ℂ f z) :
    ∫ t in (0:ℝ)..1, γ₀' t • f (γ₀ t) = ∫ t in (0:ℝ)..1, γ₁' t • f (γ₁ t)

/-- **Cauchy's theorem, null-homotopic form** — genuine corollary (specialize `γ₁` to the
constant loop at `z₁`, whose integral vanishes). `#print axioms` = the homotopy axiom + the
standard three. -/
theorem contourIntegral_eq_zero_of_null_homotopic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    {γ γ' : ℝ → ℂ} {H : ℝ → ℝ → ℂ} {z₁ : ℂ}
    (hγ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ'c : ContinuousOn γ' (Set.Icc 0 1))
    (hHc : ContinuousOn (Function.uncurry H) (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
    (hH0 : ∀ t ∈ Set.Icc (0:ℝ) 1, H 0 t = γ t)
    (hH1 : ∀ t ∈ Set.Icc (0:ℝ) 1, H 1 t = z₁)
    (hHloop : ∀ a ∈ Set.Icc (0:ℝ) 1, H a 0 = H a 1)
    (hHU : ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, H a t ∈ U)
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f U)
    (hd : ∀ z ∈ U \ s, DifferentiableAt ℂ f z) :
    ∫ t in (0:ℝ)..1, γ' t • f (γ t) = 0 := by
  have key := contourIntegral_eq_of_homotopic_loops hU
    (γ₁ := fun _ => z₁) (γ₁' := fun _ => 0)
    hγ (fun t _ => hasDerivAt_const t z₁) hγ'c continuousOn_const
    hHc hH0 hH1 hHloop hHU hs hc hd
  simpa using key

/-- **Bridge to `circleIntegral`**: `∮ z in C(c,R), f z` equals the axiom's normalized
unit-interval loop integral for `γ(t) = circleMap c R (2πt)`. Genuine theorem, no axiom —
pure change of variables (`intervalIntegral.smul_integral_comp_mul_left`). -/
theorem circleIntegral_eq_unitLoop_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z) =
      ∫ t in (0:ℝ)..1, ((2 * Real.pi : ℝ) • deriv (circleMap c R) (2 * Real.pi * t)) •
        f (circleMap c R (2 * Real.pi * t)) := by
  rw [circleIntegral]
  have key := intervalIntegral.smul_integral_comp_mul_left
    (fun θ => deriv (circleMap c R) θ • f (circleMap c R θ)) (2 * Real.pi) (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at key
  rw [← key, ← intervalIntegral.integral_smul]
  congr 1
  funext t
  rw [smul_assoc]

end
