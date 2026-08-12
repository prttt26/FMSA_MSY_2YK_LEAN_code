/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.Q0DetContourOrientation
import LeanCode.HSMixture.Q0ComplexRepr

/-!
# The finite Baxter factor at the removable origin (`hB₀` for the near-`0` Gram factorization)

The corrected near-`0` coercivity route (`MixtureCoercivityReduction.lean`) discharges PD-at-`0`
(`matSymbol_pd_at_zero_of_gram` / `matSymbolCoercive_of_gramFactors`) from a Gram factorization
`1 − ρĈ(0) = B₀B₀ᵀ` with `det B₀ ≠ 0`.  The raw Baxter matrix `Q0_mat_c_phys` divides by `s²`, `s³`,
so `Q0_mat_c_phys 0` is Lean junk — but the singularity is **removable**: the entire representative
`q0_entry_c_repr` (`Q0ComplexRepr.lean`) redefines the value at `0` to the removable limit and is
`Differentiable ℂ` everywhere.  This file assembles the representative into a matrix
`Q0_mat_c_repr`, the FINITE Baxter factor including `s = 0`, and proves it is nonsingular there:

* `Q0_mat_c_repr` — the matrix built from `q0_entry_c_repr` (finite at the origin).
* `Q0_mat_c_repr_eq_of_ne` — agrees with `Q0_mat_c_phys` for `s ≠ 0`.
* `continuous_Q0_mat_c_repr` — continuous through `s = 0` (entrywise entire).
* `det_Q0_mat_c_repr_origin_ne_zero` — **`det (Q0_mat_c_repr 0) ≠ 0`**: the finite origin factor is
  nonsingular.  The representative is continuous through `0` and equals `Q0_mat_c_phys` off it, so
  `det (Q0_mat_c_repr 0)` IS the removable value `c` of `det_Q0_contour_origin_ne_zero`, hence `≠ 0`
  — with **no physics axiom** (the `k = 0` compressibility positivity is *proved* from `moment_key`,
  not assumed; `pyhs_mixture_no_spinodal` covers only `k ≠ 0`).

This supplies the `hB₀` (`det B₀ ≠ 0`) input of the origin Gram factorization, with `B₀` the
transpose of `Q0_mat_c_repr 0` (matching `Cmix0_factorization`'s `Q̂₀(k)·Q̂₀(−k)ᵀ`).  The remaining
input — the Gram *identity* `hfac0` in `matRadialSymbol Φ` terms — is the shared real-space ⇄
Fourier DCF bridge (`Ĉ₀ =` the radial DCF transform, MRS.8-level), the SAME bridge the middle
region's `hfack` needs; it is not a separate origin obstacle.
-/

open Filter Topology
namespace FMSA.MixtureGenN

/-- Matrix built from the ENTIRE representative `q0_entry_c_repr` — the finite Baxter factor
including the removable origin `s = 0` (mirrors `Q0_mat_c_phys`'s entry assembly). -/
noncomputable def Q0_mat_c_repr {N : ℕ} (s : ℂ) (σ ρ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => FMSA.Q0Complex.q0_entry_c_repr
    ((σ i : ℂ)) (((σ j : ℂ) - (σ i : ℂ)) / 2)
    ((FMSA.MatrixQ0.Q0phys ρ σ i j : ℂ)) ((FMSA.MatrixQ0.Qppphys ρ σ i j : ℂ))
    ((FMSA.MatrixQ0.rhoGeoPhys ρ i j : ℂ)) (if i = j then 1 else 0) s

/-- The representative matrix agrees with the raw physical Baxter matrix away from the origin. -/
theorem Q0_mat_c_repr_eq_of_ne {N : ℕ} {s : ℂ} (hs : s ≠ 0) (σ ρ : Fin N → ℝ) :
    Q0_mat_c_repr s σ ρ = FMSA.MixtureNoSpinodal.Q0_mat_c_phys s σ ρ := by
  funext i j
  rw [Q0_mat_c_repr, FMSA.Q0Complex.q0_entry_c_repr_eq_of_ne hs]
  rfl

/-- The representative matrix is continuous everywhere, including the removable origin. -/
theorem continuous_Q0_mat_c_repr {N : ℕ} (σ ρ : Fin N → ℝ) :
    Continuous (fun s => Q0_mat_c_repr s σ ρ) := by
  apply continuous_matrix
  intro i j
  exact (FMSA.Q0Complex.differentiable_q0_entry_c_repr _ _ _ _ _ _).continuous

/-- **The finite Baxter factor at the origin is nonsingular.**  `det (Q0_mat_c_repr 0) ≠ 0` — the
matrix form of the removable `k = 0` compressibility point.  The representative is continuous
through `s = 0` and agrees with `Q0_mat_c_phys` off `0`, so `det (Q0_mat_c_repr 0)` IS the removable
value `c` of `det_Q0_contour_origin_ne_zero`, whence nonzero.  **No physics axiom** — the
compressibility positivity is proved from `moment_key`.  Supplies the `hB₀` (`det B₀ ≠ 0`) input of
the origin Gram factorization (`matSymbol_pd_at_zero_of_gram`), with `B₀ = (Q0_mat_c_repr 0)ᵀ`. -/
theorem det_Q0_mat_c_repr_origin_ne_zero {N : ℕ} {σ ρ : Fin N → ℝ}
    (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i) (heta : FMSA.MatrixQ0.etaMix ρ σ < 1) :
    (Q0_mat_c_repr 0 σ ρ).det ≠ 0 := by
  have hcont : Continuous (fun s => (Q0_mat_c_repr s σ ρ).det) :=
    (continuous_Q0_mat_c_repr σ ρ).matrix_det
  have h0 : Tendsto (fun s => (Q0_mat_c_repr s σ ρ).det) (𝓝[≠] (0 : ℂ))
      (𝓝 ((Q0_mat_c_repr 0 σ ρ).det)) :=
    (hcont.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have htend : Tendsto (fun s => (FMSA.MixtureNoSpinodal.Q0_mat_c_phys s σ ρ).det) (𝓝[≠] (0 : ℂ))
      (𝓝 ((Q0_mat_c_repr 0 σ ρ).det)) := by
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Q0_mat_c_repr_eq_of_ne (Set.mem_compl_singleton_iff.mp hs) σ ρ]
  exact det_Q0_contour_origin_ne_zero hσ hρ heta htend

end FMSA.MixtureGenN
