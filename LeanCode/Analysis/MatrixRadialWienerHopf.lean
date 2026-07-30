/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib

/-!
# Bounded (`L∞`) Wiener–Hopf injectivity for a **matrix** radial shell convolution operator

The multicomponent analog of `radialShell_bounded_injective` (`Analysis/RadialWienerHopf.lean`, task
`MA.15`).  General-purpose: an arbitrary matrix kernel `C : Matrix (Fin N) (Fin N) (ℝ → ℝ)` supported
in `[0, σ]`, an arbitrary density `rho`, no project-specific definitions — stated entirely in raw
integrals.

## Statement

For the homogeneous matrix radial shell operator (`r > 0`)

  `dᵢⱼ(r) = ρ·r·∑ₖ (2π/r)·∫₀^∞ t·Cᵢₖ(t)·(∫_{|r−t|}^{r+t} s·(dₖⱼ(s)/s) ds) dt`,

whose Fourier symbol is the matrix `I − ρ·Ĉ(k)`, `Ĉ(k)ᵢⱼ = (4π/k)∫₀^∞ r·Cᵢⱼ(r)·sin(kr) dr`: if the
symbol is **coercive** (`vᵀ(I − ρĈ(k))v ≥ ε‖v‖²` for all `k, v`), then `I − K` is injective on
**bounded**, exterior-continuous, core-vanishing matrix functions — `d ≡ 0`.

## Why this is an axiom (identical reason to the scalar `MA.15`)

`Analysis/WienerHopf.lean`'s `wienerHopf_positive_symbol_injective` (`MA.12`) proves the coercive
injectivity **on `L²`** (Plancherel: `⟪(I−K)u, u⟫ = ∫ ⟨(I−ρĈ(ξ))û(ξ), û(ξ)⟩ dξ ≥ ε‖u‖²`).  That
argument **does not survive the passage to `L∞`** — a bounded function need not be `L²`, and there is
no Plancherel pairing.  The classical bounded/`L∞` route needs Wiener-algebra resolvent inversion
(`δ + L¹` invertibility), the same gap that makes `MA.13` an axiom; Mathlib has no Wiener algebra, no
`L¹`-convolution Banach algebra, no bounded Wiener–Hopf inversion.  So the `L²`/`L∞` pair is
deliberately asymmetric here exactly as in the scalar case.

## Consumer

`HSMixture/MixtureRDFUniqueness.lean` instantiates it at the mixture forcing `Φ` (via the matrix
radial convolution `matRadialConv`, whose unfolding is definitionally this raw operator) to derive the
unconditional matrix `oz_fixed_pt_unique` (`matOzStar_unique`, the `MML.8` value route).  The symbol
coercivity is discharged there from the multicomponent no-spinodal / positive-definite structure
factor `T₀ ⪰ εI` (invertibility `det Q̂₀ ≠ 0`), so no physics enters this file.
-/

open MeasureTheory Set

namespace FMSA

/-- **Matrix bounded (`L∞`) Wiener–Hopf injectivity** — the multicomponent analog of the scalar kept
axiom `radialShell_bounded_injective`, in raw-integral form.  A coercive matrix symbol makes the
homogeneous matrix radial shell operator injective on bounded, exterior-continuous, core-vanishing
matrix functions.  `L∞`-Wiener-algebra gap (`MA.13`-class); the `L²` Plancherel `MA.12` does not reach
it. -/
axiom matRadialShell_bounded_injective {N : ℕ} {C : Matrix (Fin N) (Fin N) (ℝ → ℝ)} {sigma rho : ℝ}
    (hsigma : 0 < sigma)
    (hCsupp : ∀ (i j : Fin N) (t : ℝ), sigma ≤ t → C i j t = 0)
    (hcoercive : ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℝ) (v : Fin N → ℝ),
      ε * (∑ i, v i ^ 2) ≤ (∑ i, v i ^ 2)
        - rho * ∑ i, ∑ j,
            ((4 * Real.pi / k) * ∫ r in Ioi (0 : ℝ), r * C i j r * Real.sin (k * r)) * v i * v j)
    {d : Matrix (Fin N) (Fin N) (ℝ → ℝ)}
    (hbdd : ∀ i j, ∃ M : ℝ, ∀ r : ℝ, |d i j r| ≤ M)
    (hcont : ∀ i j, ContinuousOn (d i j) (Ici sigma))
    (hcore : ∀ (i j : Fin N) (r : ℝ), r < sigma → d i j r = 0)
    (hhom : ∀ (i j : Fin N) (r : ℝ), 0 < r → d i j r =
      rho * (r * ∑ k, (2 * Real.pi / r)
        * ∫ t in Ioi (0 : ℝ), t * C i k t
            * ∫ s in Icc |r - t| (r + t), s * (d k j s / s))) :
    ∀ (i j : Fin N) (r : ℝ), d i j r = 0

end FMSA
