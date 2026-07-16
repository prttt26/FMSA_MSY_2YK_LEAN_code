/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.YukawaWienerHopf
import LeanCode.YukawaDCF.SpectralAmplitude

/-!
# Task Y1.3c — causal projection = Yukawa-pole residue extraction ([LN] §6.4.1, Eq. 63–66)

The Wiener–Hopf causal part `B₁ = {T_U}^{[R,∞)}` is obtained (closing the contour in the upper
half-plane) as the sum of the residues of `T_U(k) = [Q̂₀(−k)]⁻¹ U₁(k) [Q̂₀ᵀ(−k)]⁻¹` at its
upper-half-plane Yukawa poles.  The inverse-Baxter factors are analytic there, so only `U₁`'s simple
pole (`s = −z`, from Y1.2) contributes, and the residue is that of `U₁` **conjugated** by the
pole-values of the Baxter factors.  This file does that residue-extraction step concretely, on top of
`matrix_conj_residue_analytic` (Y1.3c support, `YukawaWienerHopf.lean`).

The remaining half of the Wiener–Hopf derivation — the **projection identity**
`{T_U}^{[R,∞)} = B₁` (that the causal part really equals this single residue term), which rests on the
support statements (Y1.3a, `WHSupports.lean`) via FT injectivity — is **Y1.3b**, deferred.

## Results

* `U1mat` / `U1mat_residue` — the single-tail outer-DCF matrix `U₁(s)` (simple Yukawa pole at
  `s = −z`) has entrywise residue the coupling matrix `K` ([LN] Eq. 46; reuses `simplePole_residue`).
* `outer_residue` — the residue of the conjugated outer term `T_U(s) = Lf s · U₁(s) · Rf s` at the
  Yukawa pole is `Lval · K · Rval` (`Lval`, `Rval` = pole-values of the inverse-Baxter factors).
* `outer_residue_eq_spectralAmp_residue` — with `Lf → G = Q̂₀(z)⁻¹`, `Rf → Gᵀ`, the residue is the
  doubly-propagated `[G·K·Gᵀ]_{ij}`, **identical to** `SpectralAmplitude.spectralAmp_residue`.  So the
  causal outer term `T_U` and the spectral amplitude `b_{ij}` (Y1.5) share the same Yukawa-pole
  residue: `Res T_U = Res b_{ij}`.

Status: ✓ DONE (Y1.3c), axiom-clean.  Y1.3b (projection identity) deferred.
-/

set_option linter.style.longLine false

open Filter Topology Matrix

namespace FMSA.YukawaWH

open FMSA.SpectralAmplitude

/-- Single-tail outer-DCF matrix `U₁(s)` (residue-carrying part, [LN] Eq. 46): a simple Yukawa pole
at `s = −z` with residue the coupling matrix `K`.  (The `e^{−ikR}` phase is analytic at the pole and
absorbed into `K`; cf. `FMSA.OuterDCF.outerDCF_transform`.) -/
noncomputable def U1mat {n : ℕ} (Kmat : Matrix (Fin n) (Fin n) ℂ) (z s : ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => Kmat i j / (s + z)

/-- The entrywise Yukawa-pole residue of `U₁` is the coupling matrix `K`: `Res_{s=−z} U₁(s)_{ij} =
K_{ij}`.  (Elementary `(s+z)·K/(s+z) → K`, via `simplePole_residue`.) -/
theorem U1mat_residue {n : ℕ} (Kmat : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i j : Fin n) :
    Tendsto (fun s => (s - (-z)) * U1mat Kmat z s i j) (𝓝[≠] (-z)) (𝓝 (Kmat i j)) := by
  simpa only [U1mat] using simplePole_residue (Kmat i j) z

/-- **Y1.3c — Yukawa-pole residue of the Wiener–Hopf outer term.**  For the conjugated outer term
`T_U(s) = Lf s · U₁(s) · Rf s` with inverse-Baxter factors `Lf`, `Rf` analytic at the pole (pole-values
`Lval`, `Rval`), the residue at `s = −z` is `Lval · K · Rval` — the `U₁`-residue `K` conjugated by the
Baxter pole-values (`matrix_conj_residue_analytic` + `U1mat_residue`). -/
theorem outer_residue {n : ℕ} (Lf Rf : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (Kmat Lval Rval : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i j : Fin n)
    (hL : ∀ p q, Tendsto (fun s => Lf s p q) (𝓝[≠] (-z)) (𝓝 (Lval p q)))
    (hR : ∀ p q, Tendsto (fun s => Rf s p q) (𝓝[≠] (-z)) (𝓝 (Rval p q))) :
    Tendsto (fun s => (s - (-z)) * (Lf s * U1mat Kmat z s * Rf s) i j) (𝓝[≠] (-z))
      (𝓝 ((Lval * Kmat * Rval : Matrix (Fin n) (Fin n) ℂ) i j)) :=
  matrix_conj_residue_analytic Lf Rf (U1mat Kmat z) (-z) Lval Rval Kmat i j hL hR
    (U1mat_residue Kmat z)

/-- **Y1.3c closure — `Res T_U = Res b_{ij}`.**  With inverse-Baxter factors `Lf → G = Q̂₀(z)⁻¹`,
`Rf → Gᵀ = Q̂₀(z)⁻ᵀ`, the outer term's Yukawa-pole residue is the doubly-propagated `[G·K·Gᵀ]_{ij}` —
**identical** to `SpectralAmplitude.spectralAmp_residue Kmat Gmat z i j`.  So the causal outer term
`T_U` and the spectral amplitude `b_{ij}` of Y1.5 share the same Yukawa-pole residue; once the
projection identity `{T_U}^{[R,∞)} = B₁` (Y1.3b) is established, `b_{ij}` is recovered. -/
theorem outer_residue_eq_spectralAmp_residue {n : ℕ} (Lf Rf : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (Kmat Gmat : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i j : Fin n)
    (hL : ∀ p q, Tendsto (fun s => Lf s p q) (𝓝[≠] (-z)) (𝓝 (Gmat p q)))
    (hR : ∀ p q, Tendsto (fun s => Rf s p q) (𝓝[≠] (-z)) (𝓝 (Gmatᵀ p q))) :
    Tendsto (fun s => (s - (-z)) * (Lf s * U1mat Kmat z s * Rf s) i j) (𝓝[≠] (-z))
      (𝓝 ((Gmat * Kmat * Gmatᵀ : Matrix (Fin n) (Fin n) ℂ) i j)) :=
  outer_residue Lf Rf Kmat Gmat Gmatᵀ z i j hL hR

end FMSA.YukawaWH
