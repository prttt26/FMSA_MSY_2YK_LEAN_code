/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task C.5 (concrete, single-tail) — the exact Yukawa-pole residue of the spectral amplitude

Concrete follow-up to `YukawaPoleResidue.lean` (C.5 conditional core), grounded in the **[LN]**
lecture notes (Tang & Lu 1995, `pdf/lecture_notes_OZ_Yukawa_poly.pdf`).

The first-order RDF is `Ĥ₁(k) = [Q̂₀ᵀ(k)]⁻¹ B₁(k) [Q̂₀(k)]⁻¹` ([LN] Eq. 68), where `B₁(k)_{ij} =
b_{ij}(ik)·e^{-ikR_{ij}}` and the **spectral amplitude** `b_{ij}(s)` ([LN] Eq. 73) is the four-term
sum whose Yukawa-pole residues carry the hard-sphere propagators `A_{ij}` — with
`A_{ij}(z) = [Q̂₀(z)⁻¹]_{ij} − δ_{ij}` ([LN] Eq. 70).  For a **single tail** (common inverse-range
`z`) the four terms collapse to a matrix product:
```
b_{ij}(s) = [ (I+A)·K·(I+A)ᵀ ]_{ij} / (s + z) = [ Q̂₀(z)⁻¹·K·Q̂₀(z)⁻ᵀ ]_{ij} / (s + z),
```
since `I + A = Q̂₀(z)⁻¹`.  (Check: `Σ_{m,n}(δ_{im}+A_{im})K_{mn}(δ_{jn}+A_{jn})` reproduces the four
`δδ`, `δA`, `Aδ`, `AA` terms of Eq. 73.)

## Result

`spectralAmp_residue` — the residue at the Yukawa pole `s = −z` is the **doubly-propagated**
coupling `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}`: `K` sandwiched by **two** inverse-Baxter factors.

**Correction to the numerical shorthand.**  The Route-C handoff described this residue as
"`K·G·exp`" (`K` times a *single* GA-matrix entry `G_{ij}`).  The exact [LN] structure is
`Q̂₀⁻¹·K·Q̂₀⁻ᵀ` — doubly propagated.  `spectralAmp_residue_n1` makes it explicit at `N=1`: the
leading residue is `K·G²`, **not** `K·G`.  So `get_c1_inner`'s `K·G·exp` is a *leading-order
approximation* of the exact `Q̂₀⁻¹·K·Q̂₀⁻ᵀ`, not the exact residue.

## Still deferred (full concrete C.5)

The **multi-tail** `b_{ij}(s)` (Eq. 73 with distinct `z_{αβ}`) and the derivation of `b_{ij}` itself
from the Wiener–Hopf/Hilbert-transform split ([LN] §6.1–§6.4) — that whole first-order-RDF
derivation is a Group-BAXTER-scale effort, not attempted here.  `A_{ij}(z)` as `[Q̂₀(z)⁻¹]_{ij}−δ`
needs the complex Laplace-space `Q̂₀(s)` ([LN] Eq. 10); the codebase `Q0_mat` is real.

Status: ◑ single-tail exact residue DONE (2026-07-15), axiom-clean; multi-tail + `b_{ij}` derivation
deferred.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Filter Topology Matrix

namespace FMSA.SpectralAmplitude

/-- Single-tail spectral amplitude `b_{ij}(s) = [G·K·Gᵀ]_{ij}/(s+z)` ([LN] Eq. 73, common
inverse-range `z`), where `K` is the Yukawa coupling matrix and `G = Q̂₀(z)⁻¹ = I + A(z)` is the
inverse Baxter matrix ([LN] Eq. 70: `A_{ij} = [Q̂₀⁻¹]_{ij} − δ_{ij}`). -/
noncomputable def spectralAmp {n : ℕ} (Kmat Gmat : Matrix (Fin n) (Fin n) ℂ) (z s : ℂ)
    (i j : Fin n) : ℂ :=
  ((Gmat * Kmat * Gmatᵀ : Matrix (Fin n) (Fin n) ℂ) i j) / (s + z)

/-- **Concrete C.5 (single-tail).**  The Yukawa-pole residue of the spectral amplitude at `s = −z`
is the *doubly-propagated* coupling `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` — `K` sandwiched by two inverse-Baxter
factors (the exact [LN] form, richer than the linear `K·G` shorthand). -/
theorem spectralAmp_residue {n : ℕ} (Kmat Gmat : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i j : Fin n) :
    Tendsto (fun s => (s - (-z)) * spectralAmp Kmat Gmat z s i j) (𝓝[≠] (-z))
      (𝓝 ((Gmat * Kmat * Gmatᵀ : Matrix (Fin n) (Fin n) ℂ) i j)) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have hsz : s + z ≠ 0 := fun h => hs (by rwa [add_eq_zero_iff_eq_neg] at h)
  simp only [spectralAmp, sub_neg_eq_add]
  rw [mul_comm, div_mul_cancel₀ _ hsz]

/-- **N=1 makes the correction explicit:** the leading residue is `K·G²`, **not** `K·G`.  (For
`Fin 1`, `[G·K·Gᵀ]_{00} = G_{00}·K_{00}·G_{00}`.) -/
theorem spectralAmp_residue_n1 (Kmat Gmat : Matrix (Fin 1) (Fin 1) ℂ) (z : ℂ) :
    Tendsto (fun s => (s - (-z)) * spectralAmp Kmat Gmat z s 0 0) (𝓝[≠] (-z))
      (𝓝 (Kmat 0 0 * (Gmat 0 0) ^ 2)) := by
  have h := spectralAmp_residue Kmat Gmat z 0 0
  have he : (Gmat * Kmat * Gmatᵀ : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = Kmat 0 0 * (Gmat 0 0) ^ 2 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]; ring
  rwa [he] at h

/-!
## Y1.5 — multi-tail spectral amplitude ([LN] Eq. 66/73)
-/

/-- **Multi-tail spectral amplitude** ([LN] Eq. 66/73): with per-family pole positions `z_{mn}`,
`b_{ij}(s) = Σ_{m,n} (I+A)_{im} K_{mn} (I+A)_{jn} / (s + z_{mn})`.  The `δδ/δA/Aδ/AA` expansion of
`(I+A)(I+A)` reproduces exactly the four terms of Eq. 73; `I+A = Q̂₀(z)⁻¹` ([LN] Eq. 70). -/
noncomputable def bMulti {n : ℕ} (Kmat Amat : Matrix (Fin n) (Fin n) ℂ)
    (zmat : Fin n → Fin n → ℂ) (s : ℂ) (i j : Fin n) : ℂ :=
  ∑ m, ∑ p, (1 + Amat) i m * Kmat m p * (1 + Amat) j p / (s + zmat m p)

/-- Single-term simple-pole residue: `Res_{s=−z}[c/(s+z)] = c`.  (Elementary `(s+z)·c/(s+z) → c`.) -/
theorem simplePole_residue (c z : ℂ) :
    Tendsto (fun s => (s - (-z)) * (c / (s + z))) (𝓝[≠] (-z)) (𝓝 c) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have hsz : s + z ≠ 0 := fun h => hs (by rwa [add_eq_zero_iff_eq_neg] at h)
  rw [sub_neg_eq_add, mul_comm, div_mul_cancel₀ _ hsz]

/-- **Y1.5 (multi-tail → single-tail collapse).**  With a common inverse-range `z₀` the four-term
`bMulti` collapses to `spectralAmp` (`Gmat = I + A`): `Σ_{m,n}(I+A)_{im}K_{mn}(I+A)_{jn}/(s+z₀) =
[(I+A)·K·(I+A)ᵀ]_{ij}/(s+z₀)`. -/
theorem bMulti_single_eq {n : ℕ} (Kmat Amat : Matrix (Fin n) (Fin n) ℂ) (z0 s : ℂ) (i j : Fin n) :
    bMulti Kmat Amat (fun _ _ => z0) s i j = spectralAmp Kmat (1 + Amat) z0 s i j := by
  simp only [bMulti, spectralAmp, ← Finset.sum_div]
  congr 1
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Y1.5 (multi-tail single-tail residue).**  Consequently the single-tail `bMulti` has the same
exact Yukawa-pole residue as `spectralAmp`: `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` (with `Q̂₀⁻¹ = I+A`). -/
theorem bMulti_single_residue {n : ℕ} (Kmat Amat : Matrix (Fin n) (Fin n) ℂ) (z0 : ℂ) (i j : Fin n) :
    Tendsto (fun s => (s - (-z0)) * bMulti Kmat Amat (fun _ _ => z0) s i j) (𝓝[≠] (-z0))
      (𝓝 (((1 + Amat) * Kmat * (1 + Amat)ᵀ : Matrix (Fin n) (Fin n) ℂ) i j)) := by
  simp only [bMulti_single_eq]
  exact spectralAmp_residue Kmat (1 + Amat) z0 i j

end FMSA.SpectralAmplitude
