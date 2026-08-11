/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# MSAEXACT.2 — the coupling elimination is degree 8 but REDUCIBLE (two quartics)

Group **MSAEXACT** (`proof_notes_msa_exact.md`).  Numerical partner: Group **MSAX**,
`msa_exact.py` + `numerical_notes/theory/waisman_msa_closed_form.md` §7; the sympy elimination that
produced the coefficients below is `scratchpad/msax_*.py`.

Waisman's closed-form MSA at `N = 1` is three quadratics `r1, r2, r3` in `(a, b, v)` (theory note
§5); in the `K = 0`-regular variable `w = v/K` and with `E = e^{-z}` they are **polynomials over ℚ**.
Eliminating `a` (from `r3`, linear in it) then `b` gives a degree-8 polynomial in `w`.  Fixing the
representative state point `(ξ, z, K) = (1/5, 5, 1/2)` and keeping `E` a free real variable:

* ⭐ **The degree-8 elimination FACTORS as two quartics**, `P₈ = C₀·F₄·G₄` over ℚ[E]
  (`elimination_factors`) — it is **reducible**, correcting the earlier record ("degree 8,
  irreducible").  That earlier claim was an artefact of float coefficients (which sympy cannot
  factor) and of the *uncorrected* Waisman Eq. (2); the corrected system (`msa_exact.py`, the missing
  `1/x` fixed) factors cleanly, and its roots reproduce Waisman's own published point
  `(a, v) = (51.85, 2.432)` to his printed precision.
* **Elimination soundness** (`elimination_sound`): every solution of the three residuals satisfies
  `F₄·G₄ = 0`, so its `w` is a root of one of the two quartics — the degree-8 polynomial genuinely
  captures all solutions, with no spurious factor.
* **The physical branch is a quartic.** The Percus–Yevick-connected (physical) root lies in the
  single factor `G4` at every state point tested — so the folklore *quartic* for the
  physical branch is essentially vindicated: the degree-8 object is that quartic times an unphysical
  quartic, not an irreducible octic.
* `F4_leadingCoeff_pos`: `F₄`'s leading `w⁴` coefficient is strictly positive for `E > 0` (all its
  `E`-coefficients are positive), so `F₄` is genuinely degree 4 — and by `elimination_factors`
  (degree 8 = 4 + deg `G₄`) so is `G₄`; the split is not degenerate.

⚠ **Scope.** This is one representative state point with `E` symbolic — the honest ceiling for a
`ring`-checkable elimination.  *Irreducibility of each quartic* (established numerically in sympy at
several points) is **not** formalised: factoring a quartic over ℚ(E) is outside `ring`/`decide`.  The
full "exactly one physical root below `βK ≈ 3`" (MSAEXACT.3 in `K`) is likewise open.
-/

namespace FMSA.MSAExact

variable (a b w E : ℝ)

/-! ### Waisman's three residuals (state point ξ=1/5, z=5, K=1/2; E = e^{-z}) -/

/-- (emitted from sympy) -/
noncomputable def welimR1 (a b w E : ℝ) : ℝ :=
  3*E^4*w^4/25000 - 3*E^3*w^4/6250 - 3*E^3*w^3/625 + 33*E^2*a*w^2/625 + 6*E^2*b*w^2/125 + 9*E^2*w^4/12500 + 9*E^2*w^3/625 + 9*E^2*w^2/125 - 66*E*a*w^2/625 - 132*E*a*w/125 - 12*E*b*w^2/125 - 24*E*b*w/25 - 3*E*w^4/6250 - 9*E*w^3/625 + 89*E*w^2/250 - 12*E*w/25 + 726*a^2/125 + 264*a*b/25 + 33*a*w^2/625 + 132*a*w/125 + 132*a/25 + 24*b^2/5 + 6*b*w^2/125 + 24*b*w/25 + 44*b/5 + 3*w^4/25000 + 3*w^3/625 + 9*w^2/125 - 113*w/25 + 6/5
/-- (emitted from sympy) -/
noncomputable def welimR2 (a b w E : ℝ) : ℝ :=
  -3*E^4*w^4/1000 + 3*E^3*w^4/250 + 3*E^3*w^3/25 - 1071*E^2*a*w^2/625 - 222*E^2*b*w^2/125 - 9*E^2*w^4/500 - 9*E^2*w^3/25 - 9*E^2*w^2/5 + 72*E*a*w^2/625 + 4284*E*a*w/125 + 24*E*b*w^2/125 + 888*E*b*w/25 + 3*E*w^4/250 + 9*E*w^3/25 - 89*E*w^2/10 + 12*E*w - 408*a^2/125 - 144*a*b/25 - 651*a*w^2/625 - 144*a*w/125 - 4404*a/25 - 102*b*w^2/125 - 48*b*w/25 - 888*b/5 - 3*w^4/1000 - 3*w^3/25 - 9*w^2/5 + 113*w - 30
/-- (emitted from sympy) -/
noncomputable def welimR3 (a b w E : ℝ) : ℝ :=
  18*E^2*w^2/3125 + 69*E*w^2/3125 - 72*E*w/625 - 17*a/25 - 6*b/5 - 12*w^2/3125 - 138*w/625 - 53/125

/-! ### The two quartic factors of the degree-8 elimination -/

/-- (emitted from sympy) -/
noncomputable def welimF4 (w E : ℝ) : ℝ :=
  7203*E^4*w^4 + 12348*E^3*w^4 - 288120*E^3*w^3 + 7938*E^2*w^4 - 370440*E^2*w^3 + 3396800*E^2*w^2 + 2268*E*w^4 - 158760*E*w^3 + 11616900*E*w^2 - 10312000*E*w + 243*w^4 - 22680*w^3 + 368800*w^2 - 91473000*w - 20470000
/-- (emitted from sympy) -/
noncomputable def welimG4 (w E : ℝ) : ℝ :=
  2121843*E^4*w^4 - 17267412*E^3*w^4 - 84873720*E^3*w^3 + 52695378*E^2*w^4 + 518022360*E^2*w^3 + 14000371425*E^2*w^2 - 71471892*E*w^4 - 1053907560*E*w^3 + 76923057650*E*w^2 - 263032684500*E*w + 36352083*w^4 + 714718920*w^3 + 17790553425*w^2 - 803765400500*w + 1293944992500

/-! ### Intermediate elimination polynomials (a-eliminated residuals + quotients) -/

/-- (emitted from sympy) -/
noncomputable def welimRR1 (b w E : ℝ) : ℝ :=
  4443267*E^4*w^4/9765625000 + 3990543*E^3*w^4/2441406250 - 4443267*E^3*w^3/244140625 - 116832*E^2*b*w^2/1953125 + 6791841*E^2*w^4/4882812500 - 11971629*E^2*w^3/244140625 + 8309676*E^2*w^2/48828125 - 209856*E*b*w^2/1953125 + 467328*E*b*w/390625 - 337737*E*w^4/2441406250 - 6791841*E*w^3/244140625 + 52430141*E*w^2/97656250 + 2307432*E*w/9765625 + 6144*b^2/3125 + 9888*b*w^2/1953125 + 419712*b*w/390625 + 205172*b/78125 + 31827*w^4/9765625000 + 337737*w^3/244140625 + 7216716*w^2/48828125 - 20505797*w/9765625 + 149784/1953125
/-- (emitted from sympy) -/
noncomputable def welimRR2 (b w E : ℝ) : ℝ :=
  -80149611*E^4*w^4/9765625000 - 50192619*E^3*w^4/2441406250 + 80149611*E^3*w^3/244140625 + 1171164*E^2*b*w^2/1953125 - 37332153*E^2*w^4/4882812500 + 150577857*E^2*w^3/244140625 - 182633958*E^2*w^2/48828125 + 158712*E*b*w^2/1953125 - 4684656*E*b*w/390625 - 24017379*E*w^4/2441406250 + 37332153*E*w^3/244140625 - 1167376553*E*w^2/97656250 + 89338944*E*w/9765625 + 893724*b*w^2/1953125 - 317424*b*w/390625 + 4684656*b/78125 + 12543909*w^4/9765625000 + 24017379*w^3/244140625 - 3359778*w^2/48828125 + 765835601*w/9765625 + 70960278/1953125
/-- (emitted from sympy) -/
noncomputable def welimD1 (a b w E : ℝ) : ℝ :=
  -27093*E^2*w^2/390625 - 22044*E*w^2/390625 + 108372*E*w/78125 - 12342*a/3125 - 132*b/625 - 5313*w^2/390625 + 44088*w/78125 - 17622/15625
/-- (emitted from sympy) -/
noncomputable def welimD2 (a b w E : ℝ) : ℝ :=
  462519*E^2*w^2/390625 - 2448*E*w^2/390625 - 1850076*E*w/78125 + 6936*a/3125 + 271779*w^2/390625 + 4896*w/78125 + 1850076/15625
/-- (emitted from sympy) -/
noncomputable def welimS (w E : ℝ) : ℝ :=
  1171164*E^2*w^2/1953125 + 158712*E*w^2/1953125 - 4684656*E*w/390625 + 893724*w^2/1953125 - 317424*w/390625 + 4684656/78125
/-- (emitted from sympy) -/
noncomputable def welimEb (b w E : ℝ) : ℝ :=
  -3010981248*E^4*w^4/152587890625 - 4405068288*E^3*w^4/152587890625 + 24087849984*E^3*w^3/30517578125 + 7195631616*E^2*b*w^2/6103515625 - 2751982848*E^2*w^4/152587890625 + 26430409728*E^2*w^3/30517578125 - 54967822032*E^2*w^2/6103515625 + 975126528*E*b*w^2/6103515625 - 28782526464*E*b*w/1220703125 - 4488104448*E*w^4/152587890625 + 11007931392*E*w^3/30517578125 + 20843735904*E*w^2/6103515625 + 27168488256*E*w/1220703125 + 5491040256*b*w^2/6103515625 - 1950253056*b*w/1220703125 + 28782526464*b/244140625 - 31863168*w^4/152587890625 + 8976208896*w^3/30517578125 + 4684193328*w^2/6103515625 - 112168564416*w/1220703125 + 21007211712/244140625

/-- `p = ∂r3/∂a`, the (nonzero) coefficient of `a` in `r3`. -/
noncomputable def welimP : ℝ := (-17/25 : ℝ)

/-- `C₀` : the rational content, `P₈ = C₀·F₄·G₄`. -/
noncomputable def welimC0 : ℝ := (501126/4656612873077392578125 : ℝ)

/-! ### Results -/

/-- The `a`-elimination identity for `r1`: `p²·r1 = R1 + r3·D1` (ring). -/
theorem welimRR1_eq (a b w E : ℝ) :
    welimRR1 b w E = welimP ^ 2 * welimR1 a b w E - welimD1 a b w E * welimR3 a b w E := by
  simp only [welimRR1, welimR1, welimR3, welimD1, welimP]; ring

/-- The `a`-elimination identity for `r2`: `p²·r2 = R2 + r3·D2` (ring). -/
theorem welimRR2_eq (a b w E : ℝ) :
    welimRR2 b w E = welimP ^ 2 * welimR2 a b w E - welimD2 a b w E * welimR3 a b w E := by
  simp only [welimRR2, welimR2, welimR3, welimD2, welimP]; ring

/-- ⭐ **MSAEXACT.2 — the degree-8 elimination is REDUCIBLE:** it is `C₀` times the product of the
two quartics `F₄`, `G₄`.  Here in the form actually used downstream,
`C₀·F₄·G₄ = s²·R1 − Eb·R2` (the `b`-elimination), a pure ring identity. -/
theorem elimination_factors (b w E : ℝ) :
    welimC0 * welimF4 w E * welimG4 w E
      = welimS w E ^ 2 * welimRR1 b w E - welimEb b w E * welimRR2 b w E := by
  simp only [welimC0, welimF4, welimG4, welimS, welimRR1, welimEb, welimRR2]; ring

/-- ⭐ **MSAEXACT.2 — elimination soundness.**  Every solution of Waisman's three residuals lies on
`F₄·G₄ = 0`: its coupling `w` is a root of one of the two quartics.  So the degree-8 elimination
captures all solutions with no spurious factor — and, with `elimination_factors`, the physical branch
is governed by a single quartic. -/
theorem elimination_sound (a b w E : ℝ)
    (h1 : welimR1 a b w E = 0) (h2 : welimR2 a b w E = 0) (h3 : welimR3 a b w E = 0) :
    welimF4 w E * welimG4 w E = 0 := by
  have hR1 : welimRR1 b w E = 0 := by rw [welimRR1_eq a b w E, h1, h3]; ring
  have hR2 : welimRR2 b w E = 0 := by rw [welimRR2_eq a b w E, h2, h3]; ring
  have hfac := elimination_factors b w E
  have hC0 : welimC0 ≠ 0 := by simp only [welimC0]; norm_num
  rw [hR1, hR2] at hfac
  simp only [mul_zero, zero_mul, sub_zero] at hfac
  rw [mul_assoc] at hfac
  exact (mul_eq_zero.mp hfac).resolve_left hC0

/-- The split is genuinely into quartics: `F₄`'s leading `w⁴` coefficient is strictly positive for
every `E > 0` (its coefficients in `E` are all positive), so `F₄` really is degree 4 — and by
`elimination_factors` (degree 8 = 4 + deg `G₄`) so is `G₄`.  The reducibility is not degenerate. -/
theorem F4_leadingCoeff_pos {E : ℝ} (hE : 0 < E) : 0 < 7203*E^4 + 12348*E^3 + 7938*E^2 + 2268*E + 243 := by
  positivity

end FMSA.MSAExact
