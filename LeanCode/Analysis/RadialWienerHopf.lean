/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Bounded (`L∞`) Wiener–Hopf injectivity for a radial shell convolution operator

Group MA (`MATH_AXIOMS.md`), task `MA.15` (consumer: `OZ.10`). General-purpose: an arbitrary kernel `C : ℝ → ℝ`
supported in `[0, σ]`, an arbitrary density `rho`, no project-specific definitions.

## Statement

For the exterior radial shell operator

  `(K d)(r) = (2πρ/r) · ∫₀^σ t·C(t) · (∫_{max(r−t,σ)}^{r+t} s·d(s) ds) dt`   (`r ≥ σ`)

whose radial (sine) symbol is `ρ·Ĉ(k)`, `Ĉ(k) = (4π/k)∫₀^∞ r·C(r)·sin(kr) dr`: if the symbol is
**coercive** (`1 − ρĈ ≥ ε > 0` for all `k`), then `I − K` is injective on **bounded** functions that
are continuous on `[σ,∞)` and vanish on the core — i.e. `d = K d` on `[σ,∞)` forces `d ≡ 0`.

## Why this is an axiom, while the `L²` analogue is a theorem

`Analysis/WienerHopf.lean`'s `wienerHopf_positive_symbol_injective` (task `MA.12`) proves exactly
this statement **on `L²`**, and does so cheaply: for a real symbol `a ≥ ε > 0` the operator is
coercive, `⟪(I−K)u, u⟫ = ∫ a(ξ)|û(ξ)|² dξ ≥ ε‖u‖²`, by Plancherel. That argument **does not survive
the passage to `L∞`** — a bounded function need not be `L²`, and there is no Plancherel pairing to
run. The classical bounded/`L∞` route instead needs Wiener-algebra resolvent inversion (`δ + L¹`
invertibility), the same gap that makes `MA.13` an axiom: Mathlib has no Wiener algebra, no
`L¹`-convolution Banach algebra, and no bounded Wiener–Hopf inversion.

So the `L²`/`L∞` pair is deliberately asymmetric: `MA.12` proved, this one assumed, for a reason
that is about the function space, not about the physics.

## ⚠ The support hypothesis is load-bearing

`hCsupp` (`C = 0` on `[σ,∞)`) may look like harmless tidiness, but **the statement is false without
it**: the operator integrates `C` only over `[0,σ]`, whereas the symbol `Ĉ` integrates over
`(0,∞)`. Absent the support condition, coercivity could be supplied entirely by mass of `C` beyond
`σ` that the operator never sees, while the operator itself is (say) the identity's kernel — giving
a coercive symbol with a non-injective operator. The hypothesis is what forces symbol and operator
to refer to the same kernel.

## Consumer

Instantiated at `C := c_HS eta sigma` (whose support condition is `c_HS_outer`) to give the concrete
`oz_linear_op_bounded_injective` (`HardSphere/OzWienerHopfBounded.lean`), the spectral input that
retired the physics axiom `oz_fixed_pt_unique` to the theorem `oz_fixed_pt_unique_thm`. The symbol
coercivity is discharged there from `pyhs_no_spinodal`, so **no physics enters this file**.
-/

open MeasureTheory Set Real

noncomputable section

namespace FMSA

/-- **Bounded (`L∞`) Wiener–Hopf injectivity, radial shell operator (Group MA axiom).**  For a
kernel `C` supported in `[0,σ]` whose radial symbol satisfies `1 − ρĈ ≥ ε > 0`, the homogeneous
exterior equation `d = K d` on `[σ,∞)` has only the zero solution among bounded functions that are
continuous on `[σ,∞)` and vanish on the core.  The `L∞` analogue of the *proved* `L²` result
`wienerHopf_positive_symbol_injective` (`MA.12`); see the module docstring for why the space matters
and why `hCsupp` cannot be dropped. -/
axiom radialShell_bounded_injective {C : ℝ → ℝ} {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hCsupp : ∀ t : ℝ, sigma ≤ t → C t = 0)
    (hcoercive : ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℝ,
      ε ≤ 1 - rho * ((4 * Real.pi / k) * ∫ r in Set.Ioi (0:ℝ), r * C r * Real.sin (k * r)))
    {d : ℝ → ℝ} (hbdd : ∃ M : ℝ, ∀ r : ℝ, |d r| ≤ M)
    (hcont : ContinuousOn d (Set.Ici sigma))
    (hcore : ∀ r : ℝ, r < sigma → d r = 0)
    (hhom : ∀ r : ℝ, sigma ≤ r → d r =
      (2 * Real.pi * rho / r) * ∫ t in (0:ℝ)..sigma, t * C t *
        ∫ s in max (r - t) sigma..(r + t), s * d s) :
    ∀ r : ℝ, d r = 0

end FMSA
