/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Van der Corput first-derivative test (axiom), general-purpose

Group MA (`MATH_AXIOMS.md`), task `MA.4`. The classical **van der Corput lemma**
(first-derivative / non-stationary-phase test, with amplitude; Stein, *Harmonic Analysis*,
Prop. VIII.1.2 + its corollary): for a phase `φ` with monotonic derivative bounded away from zero
(`|φ'| ≥ λ > 0`) and a `C¹` amplitude `ψ`,

`‖∫_a^b e^{iφ(θ)}·ψ(θ) dθ‖ ≤ (3/λ)·(‖ψ(b)‖ + ∫_a^b ‖ψ'‖)`.

Absent from Mathlib (no oscillatory-integral estimates of any kind — same reconnaissance as
`ContourDeformation.lean`). Plausibly *provable* from Mathlib's interval-integral integration by
parts (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`) — flagged as the preferred follow-up
that would retire this axiom; landed as an axiom now (user-requested) since it is a named,
textbook-citable classical estimate satisfying the `MATH_AXIOMS.md` admissibility discipline.

Numerically verified (scratch `ma45_check.py`, 2026-07-15): `φ(θ)=λθ+θ²` (monotone-increasing
branch, `λ∈{1,5,20,100,500}`) and `φ(θ)=-(λθ+θ²/2)` (antitone branch, `λ∈{2,30,300}`) against two
amplitudes — bound holds with wide margin at every tested point, LHS decaying `~1/λ` as predicted.

Historical note (`proof_notes_ozfix.md` `OZFIX.10`): plain van der Corput was shown *insufficient*
for the once-blocked monolithic `k·Ĥ(k)·e^{ikr}` arc estimate (amplitude `O(R)` × VdC gain
`1/(rR)` = `O(1)`, not `o(1)`); that consumer was instead resolved by the `MA.2`+`MA.3`
Mittag-Leffler decomposition. This axiom is general toolbox material.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

/-- **Van der Corput first-derivative test, with amplitude.** For `φ : ℝ → ℝ` differentiable on
`[a,b]` with monotonic derivative satisfying `λ ≤ |φ'|`, and `ψ : ℝ → ℂ` differentiable with
integrable derivative norm: `‖∫_a^b e^{iφ}ψ‖ ≤ (3/λ)·(‖ψ(b)‖ + ∫_a^b ‖ψ'‖)`. -/
axiom vanDerCorput_first_derivative_test {phi phi' : ℝ → ℝ} {psi psi' : ℝ → ℂ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam)
    (hphi : ∀ θ ∈ Set.Icc a b, HasDerivAt phi (phi' θ) θ)
    (hmono : MonotoneOn phi' (Set.Icc a b) ∨ AntitoneOn phi' (Set.Icc a b))
    (hlb : ∀ θ ∈ Set.Icc a b, lam ≤ |phi' θ|)
    (hpsi : ∀ θ ∈ Set.Icc a b, HasDerivAt psi (psi' θ) θ)
    (hpsi'int : IntervalIntegrable (fun θ => ‖psi' θ‖) volume a b) :
    ‖∫ θ in a..b, Complex.exp (Complex.I * (phi θ : ℂ)) * psi θ‖ ≤
      3 / lam * (‖psi b‖ + ∫ θ in a..b, ‖psi' θ‖)

end
