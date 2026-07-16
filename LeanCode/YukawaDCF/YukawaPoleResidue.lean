/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.ResidueAtSimplePole

/-!
# Task C.5 — `K·G·exp` is the exact leading Yukawa-pole residue (provable core)

**Claim (Blum 1975 multicomponent Yukawa MSA).**  The leading residue of the Laplace-domain inner
DCF `ĉ^(1)_{ij}(s)` at a Yukawa pole `s = z_t` is, for an unlike pair `i ≠ j`,
```
Res_{s=z_t} ĉ^(1)_{ij}(s) = K_t · [Q̂₀(z_t)⁻¹]_{ij} = K_t · G_{ij}(z_t),
```
where `G = Q̂₀⁻¹` is the GA-matrix (inverse Baxter `Q̂₀`).  Inverse-Laplace then gives the
real-space `K_t · G_{ij} · exp(−z_t r)` term that `get_c1_inner` in `fmsa_hs_pole_residue.py` uses.

## What is proved here (the provable core)

The mathematical content splits into two reusable pieces, both fully proved and axiom-clean:

* `g_entry_eq_adj_div_det` — the matrix-algebra identity `[Q̂₀⁻¹]_{ij} = adj(Q̂₀)_{ij} / det Q̂₀`
  (`Matrix.inv_def`); this is the "`[adj Q̂₀]_{ij}/det Q̂₀ = G_{ij}`" simplification of the residue.
* `c5_residue_eq_K_mul_Ginv` — the residue assembly: given the Blum simple-pole shape of `ĉ^(1)`
  near `z_t` (`N/D` with a simple zero of `D` at `z_t`, and `N(z_t)/D'(z_t) = K_t·G_{ij}(z_t)`), the
  residue-defining limit `(s−z_t)·ĉ^(1) → K_t·G_{ij}(z_t)`.  Reuses the general simple-pole residue
  lemma `FMSA.HardSphere.residue_of_simple_pole` (`ResidueAtSimplePole.lean`).

## Modeling input (deferred)

The **Blum-1975 Laplace-space formula** for `ĉ^(1)_{ij}(s)` — i.e. *why* `N(z_t)/D'(z_t)` equals
`K_t·[Q̂₀(z_t)⁻¹]_{ij}` — is the hypothesis `hblum`.  Discharging it (defining
`ĉ^(1)_{ij}(s)` outright from Blum's partial-fraction formula, which needs a **complex** `Q̂₀(s)`
matrix — the codebase's `Q0_mat` is real) upgrades C.5 from conditional to concrete.  Left for a
follow-up once the Laplace-space formula is pinned down.

Status: ◑ conditional core DONE (2026-07-15), axiom-clean; concrete Blum form deferred.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Filter Topology

namespace FMSA.YukawaPoleResidue

/-- **C.5 matrix-algebra core.**  The `(i,j)` entry of the inverse Baxter propagator is the
adjugate entry over the determinant: `[Q̂₀⁻¹]_{ij} = adj(Q̂₀)_{ij} / det Q̂₀`.  Unconditional
(`Matrix.inv_def`: when `det` is not a unit both sides are `0`).  This is the GA-matrix identity
`G_{ij} = adj(Q̂₀)_{ij}/det Q̂₀` that the Yukawa-pole residue simplifies to. -/
theorem g_entry_eq_adj_div_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    M⁻¹ i j = M.adjugate i j / M.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', inv_mul_eq_div]

/-- **C.5 residue assembly (conditional on the Blum simple-pole shape).**  Model `ĉ^(1)_{ij}` near
the Yukawa pole `z_t` as `N/D` with a *simple* zero of `D` at `z_t` (`HasDerivAt D D' z_t`,
`D z_t = 0`, `D' ≠ 0`), `N` continuous at `z_t`, and the **Blum hypothesis**
`N(z_t)/D'(z_t) = K_t · [Q̂₀(z_t)⁻¹]_{ij}`.  Then the residue-defining limit is exactly `K_t` times
the GA-matrix entry:
```
(s − z_t)·(N s / D s)  →  K_t · (adj(Q̂₀)_{ij} / det Q̂₀)   as s → z_t  (s ≠ z_t).
```
The residue picks up `K_t·G_{ij}(z_t)` — Route C's inner `K·G·exp` term is correct at leading order.
Reuses `residue_of_simple_pole` (elementary `(z−z0)·N/D → N(z0)/D'(z0)`) and
`g_entry_eq_adj_div_det`. -/
theorem c5_residue_eq_K_mul_Ginv (N Dfun : ℂ → ℂ) (Dprime z_t Kt : ℂ) {n : ℕ}
    (Q0 : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hD : HasDerivAt Dfun Dprime z_t) (hDz : Dfun z_t = 0) (hDp : Dprime ≠ 0)
    (hN : ContinuousAt N z_t)
    (hblum : N z_t / Dprime = Kt * Q0⁻¹ i j) :
    Tendsto (fun s => (s - z_t) * (N s / Dfun s)) (𝓝[≠] z_t)
      (𝓝 (Kt * (Q0.adjugate i j / Q0.det))) := by
  rw [← g_entry_eq_adj_div_det Q0 i j]
  have h := FMSA.HardSphere.residue_of_simple_pole N Dfun Dprime z_t hD hDz hDp hN
  rwa [hblum] at h

end FMSA.YukawaPoleResidue
