/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib

/-!
# `HSMix` — the pure hard-sphere mixture structure (Yukawa-free)

The `M`-independent (hard-sphere) core of a mixture: diameters `σ`, densities `ρ`, and the Baxter
`Q₀`/`Q''` coefficients — **without** the Yukawa-tail fields `zp`/`cb` that the general `Mix N M`
carries.  The whole HS-mixture Baxter/DCF stack (`q0MixEntry`, geometry, seed route, `c_HS`) uses
only these fields, so it lives here at the HSMixture layer, Yukawa-free.  At the YukawaOZMix layer
the
Yukawa `Mix N M` connects via `Mix.toHSMix` (any `M`, `M=0` = pure HS); see `WHSupports.lean`.
-/

namespace FMSA.HSMix

/-- Pure hard-sphere mixture data (no Yukawa tail). -/
structure _root_.FMSA.HSMix (N : ℕ) where
  /-- Hard-sphere diameters. -/
  sigma : Fin N → ℝ
  /-- Number densities. -/
  rho : Fin N → ℝ
  /-- Baxter `Q₀` matrix. -/
  Q0 : Fin N → Fin N → ℝ
  /-- Baxter `Q''` diagonal. -/
  Qpp : Fin N → ℝ
  /-- Diameters are strictly positive. -/
  hsigma : ∀ k, 0 < sigma k

variable {N : ℕ} (X : FMSA.HSMix N)

/-- Contact distance `R[i,j] = (σᵢ + σⱼ)/2`. -/
noncomputable def R (i j : Fin N) : ℝ := (X.sigma i + X.sigma j) / 2

/-- Size-asymmetry parameter `λ[k,l] = (σ[l] − σ[k])/2` (second index minus first). -/
noncomputable def lam (k l : Fin N) : ℝ := (X.sigma l - X.sigma k) / 2

/-- The real-space Baxter entry — the quadratic on `[λᵢⱼ, Rᵢⱼ]`, `0` outside. -/
noncomputable def q0MixEntry (i j : Fin N) (r : ℝ) : ℝ :=
  Set.indicator (Set.Icc (X.lam i j) (X.R i j))
    (fun r => X.Q0 i j * (r - X.R i j) + X.Qpp j * (r - X.R i j) ^ 2 / 2) r

/-- `q0MixEntry X i j` is compactly supported inside `[λᵢⱼ, Rᵢⱼ]`. -/
theorem q0MixEntry_support_subset (i j : Fin N) :
    Function.support (X.q0MixEntry i j) ⊆ Set.Icc (X.lam i j) (X.R i j) := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hns
  exact hx (Set.indicator_of_notMem hns _)

end FMSA.HSMix
