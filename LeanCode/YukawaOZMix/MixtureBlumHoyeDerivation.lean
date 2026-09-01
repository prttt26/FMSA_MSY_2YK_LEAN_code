/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBaxterConv
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneq

/-!
# Mixture leg-3 (general `N`, matrix) — the matrix Baxter transform (MPhase 1)

The multi-component / matrix analog of the scalar leg-3
(`YukawaOZ/MSABlumHoyeDerivation.lean`).  The goal of the whole mixture leg-3 is to **derive** the
posited matrix Blum–Høye root `MSAMixture.MixBHRootUneq` (the matrix constraints (29′)/(33′)) from the
real-space OZ/Baxter primitives — see `proof_notes_leg3_mixture.md`.

**This file — MPhase 1: the matrix Baxter transform** `∫₀^∞ Q_ij(r) e^{−sr} dr = qhatMixCuneq`
(the matrix analog of the scalar `bhBaxter_transform`).  The real-space Baxter factor
`FMSA.ExactMSA.Breakpoint.baxterQ` is piecewise — `0` below `edgeLo σ i j = (σ_j−σ_i)/2`, a
quadratic-plus-exponential core on `[edgeLo, edgeHi]` (`edgeHi = (σ_i+σ_j)/2`), and a two-exponential
tail beyond `edgeHi`.  Its Laplace transform regroups into four support-clean pieces:

* the dressed polynomial `qp·(x−λ−σ_i) + (A/2)(x−λ−σ_i)²` on `[edgeLo, edgeHi]`;
* the Yukawa term `Wt·e^{−z(x−edgeLo)}` on **all** of `[edgeLo, ∞)` (it spans core *and* tail);
* the constant `Ct` on `[edgeLo, edgeHi]`;
* the tail Yukawa `Ct·e^{−z(x−edgeHi)}` on `[edgeHi, ∞)`.

The two Yukawa pieces are handled by the foundational half-line moment `yukawa_shift_laplace_Ioi`
below; the polynomial and constant pieces are compact-interval moments (to come).

## Blueprint

Scalar `bhBaxter_transform` = `bhBaxter_transform_split` (core interval `[0,1]` + pure-exp tail) then
`bhCore_moment_gen`.  Here every scalar identity acquires the `edgeLo`/`edgeHi` support shifts and, in
the assembled (29′)/(33′), a `∑_l ρ_l` species contraction.
-/

open Real MeasureTheory

namespace FMSA.ExactMSA.MixLeg3

/-- **The Yukawa-shift Laplace moment over a half-line** — the workhorse for the two exponential
pieces of the mixture Baxter factor.  For `s + z > 0`,
`∫_{x > c} e^{−z(x−p)}·e^{−sx} dx = e^{zp}·e^{−(s+z)c}/(s+z)`.  (With `p = c = edgeLo` it gives the
`Wt` term's `e^{−sλ}·Wt/(s+z)`; with `p = c = edgeHi` the tail's `Ct·e^{−s·σij}/(s+z)`.)  Pure
exponential, via `integral_exp_mul_Ioi`. -/
theorem yukawa_shift_laplace_Ioi (z p s c : ℝ) (hsz : 0 < s + z) :
    ∫ x in Set.Ioi c, Real.exp (-z * (x - p)) * Real.exp (-s * x)
      = Real.exp (z * p) * Real.exp (-(s + z) * c) / (s + z) := by
  have hc : (fun x => Real.exp (-z * (x - p)) * Real.exp (-s * x))
      = fun x => Real.exp (z * p) * Real.exp (-(s + z) * x) := by
    funext x
    rw [← Real.exp_add, show -z * (x - p) + -s * x = z * p + -(s + z) * x from by ring,
        Real.exp_add]
  rw [hc, MeasureTheory.integral_const_mul,
      integral_exp_mul_Ioi (show -(s + z) < 0 by linarith) c, neg_div_neg_eq]
  ring

end FMSA.ExactMSA.MixLeg3
