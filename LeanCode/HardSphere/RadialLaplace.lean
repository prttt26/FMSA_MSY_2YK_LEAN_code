/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.PYOZ

/-!
# Radial 3D convolution and the `r`-weighted Laplace transform

This file provides two definitions used elsewhere:

- `radial3d_conv` — the 3D Ornstein–Zernike convolution for radially symmetric functions,
  `(f ⊛₃D g)(r) = (2π/r) · ∫_0^∞ t·f(t) · [∫_{|r−t|}^{r+t} s·g(s) ds] dt`. A live,
  transform-independent object reused throughout the OZ chain (both the Laplace- and the
  Fourier-domain bridges, and the `g0_HS_contact_value` / BAXTER.8 assembly).
- `radial_laplace` — the `r`-weighted one-sided Laplace transform
  `ℒ_r[f](s) = ∫_0^∞ r·f(r)·e^{-sr} dr`. Kept as a correct definition; currently caller-less
  after the Laplace dead-end line was deleted (see below), available for a future OZ.8
  Laplace-route.

## Retired: `radial_laplace_conv` (radial Laplace convolution theorem)

An axiom `radial_laplace_conv` claiming a clean product factorization
`ℒ_r[f ⊛₃D g](s) = ℒ_r[f](s) · ℒ_r[g](s)` used to live here. It was found **mathematically
false** (verified by exact symbolic re-derivation and independent numerical checks): the correct
swap-of-order identity carries an extra bilateral Green's-function term that does not factor. The
OZ multiplicative structure lives in Fourier space (real `k`) / Baxter's Wiener–Hopf
factorization, not on the real Laplace axis. The axiom was **deleted** (2026-07-15); its correct
replacement is the radial *sine* transform convolution theorem `radial_fourier_conv`
(`RadialFourier.lean`, Task OZ.6), with the OZ-domain equation `oz_fourier_oz_eq_of_core_closure`
(`OZFourierBridge.lean`, Task OZ.7) built on it. The Laplace-domain results that only existed to
consume it (`oz_laplace_oz_eq`, `oz_laplace_oz_eq_of_core_closure`, `g0_HS_laplace_spec`) were
deleted along with it — none had live callers, and no true result was lost. See
`proof_notes_hard_sphere.md`.

## References

- Baxter, R.J. (1970) J. Chem. Phys. 52, 4559 — radial factorization for 3D OZ
- Wertheim, M.S. (1963) Phys. Rev. Lett. 10, 321 — PY hard-sphere analytical solution
-/

open MeasureTheory Set Real

namespace FMSA.HardSphere

/-! ### Radial 3D convolution and Laplace transform -/

/-- **3D radial convolution of radially symmetric functions.**

For two radial functions `f, g : ℝ → ℝ`, the 3D convolution
`(f * g)(r) = ∫ f(|r−r'|) g(|r'|) d³r'`
reduces (after angular integration) to:

    `(f ⊛₃D g)(r) = (2π/r) · ∫_0^∞ t · f(t) · [∫_{|r−t|}^{r+t} s · g(s) ds] dt`

The factor `2π/r` arises from integrating over the azimuthal angle and the cosine of the
polar angle.  The inner integral `∫_{|r-t|}^{r+t} s·g(s) ds` sweeps over the shell of
radii accessible from distance `t` at angle `θ` from `r`. -/
noncomputable def radial3d_conv (f g : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0
  else (2 * Real.pi / r) *
       ∫ t in Set.Ioi (0 : ℝ), t * f t *
         ∫ s in Set.Icc (|r - t|) (r + t), s * g s

/-- **Modified (r-weighted) one-sided Laplace transform.**

    `ℒ_r[f](s) = ∫_0^∞ r · f(r) · e^{-sr} dr`

This differs from the ordinary Laplace transform by the factor `r`, which enters naturally
when computing the Laplace transform of `h(r) = g(r) - 1` for radially symmetric functions
in 3D: the Fourier transform `ĥ(k) = 4π ∫_0^∞ r² h(r) sinc(kr) dr` reduces to
`(4π/k) · ∫_0^∞ r sin(kr) h(r) dr` and in the Laplace limit gives this form. -/
noncomputable def radial_laplace (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), r * f r * Real.exp (-s * r)

end FMSA.HardSphere
