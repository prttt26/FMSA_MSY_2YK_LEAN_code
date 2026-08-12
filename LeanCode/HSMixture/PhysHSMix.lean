/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.HSMix
import LeanCode.HSMixture.MatrixQ0

/-!
# `physHSMix` — the physical (Lebowitz-PY) hard-sphere mixture, at the HS layer (Yukawa-free)

The canonical physical hard-sphere mixture as an `HSMix N`: diameters `σ`, densities `ρ`, and the
Lebowitz Percus–Yevick Baxter coefficients `Q0phys`/`Qppphys` (`HSMixture/MatrixQ0.lean`).  It is
the pure-HS home of the physical mixture; the Yukawa `physMixN : Mix N 0`
(`MixtureDCFAEInjective.lean`)
is its `M=0` lift, and `(physMixN …).toHSMix = physHSMixN …` is `rfl` (see there).

Yukawa-free: imports only Mathlib + the HS-layer `HSMix`/`MatrixQ0`.
-/

namespace FMSA.HSMix

open FMSA.MatrixQ0

variable {N : ℕ}

/-- **The physical hard-sphere mixture at general `N`.**  Fields `σ`/`ρ` free, Baxter coefficients
the Lebowitz-PY closed forms `Q0phys`/`Qppphys`. -/
noncomputable def physHSMixN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) : FMSA.HSMix N where
  σ := sigma
  ρ := rho
  Q0 := Q0phys rho sigma
  Qpp := fun j => Qppphys rho sigma j j
  hσ := hsig

/-- **The physical binary hard-sphere mixture.**  The `Fin 2` specialisation; `Qpp` is written with
the `Qppphys rho sigma 0 j` row (the first index of `Qppphys` is discarded), matching the Yukawa
`physMix` field so `physMix.toHSMix = physHSMix` is `rfl`. -/
noncomputable def physHSMix (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) : FMSA.HSMix 2 where
  σ := sigma
  ρ := rho
  Q0 := Q0phys rho sigma
  Qpp := fun j => Qppphys rho sigma 0 j
  hσ := hsig

end FMSA.HSMix
