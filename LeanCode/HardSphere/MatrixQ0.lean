/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.QhatDecomposition

/-!
# Task M.3 — det(Q̂₀) ≠ 0 for valid multi-component parameters

## Context

The multi-component Baxter Q-matrix Q̂₀(z) is an n×n matrix whose (i,j) entry
(from Task M.10 / `b2_qhat_entry_decomp`) has the form:
```
Q̂₀_{ij}(z) = δ_{ij} − √(ρᵢρⱼ) · exp(−λᵢⱼ·z) · [Q'ᵢⱼ·p₁(σᵢ,z) + Q''ᵢⱼ·p₂(σᵢ,z)]
```
where:
- `λᵢⱼ = (σⱼ − σᵢ)/2`  (size asymmetry shift)
- `p₁(σ,z) = (1 − z·σ − exp(−z·σ)) / z²`
- `p₂(σ,z) = (1 − z·σ + (z·σ)²/2 − exp(−z·σ)) / z³`
- `Q'ᵢⱼ`, `Q''ᵢⱼ` are Baxter DCF coefficients (from the multicomponent PY hard-sphere DCF)
- `√(ρᵢρⱼ)` is the geometric-mean density factor

## Statement

For a physically valid n-component mixture (total packing fraction η < 1, all σᵢ > 0,
all ρᵢ ≥ 0, and Yukawa pole z > 0):
```
det(Q̂₀(z)) ≠ 0
```
equivalently, `IsUnit (Q0_mat ...).det`, which supplies `hD : IsUnit D.det`
for the abstract matrix identity `P·D⁻¹ + c·(E·D⁻¹) = I` (Task M.1).

## Status

| Statement | Status |
|---|---|
| `q0_entry` | defined (concrete M.10 formula) |
| `Q0_mat` | defined (assembled n×n matrix) |
| `Q0_mat_decomp` | proved (entry-wise application of M.10) |
| `Q0_mat_isUnit_det` (old, free `Qp`/`Qpp`) | **REMOVED — disproved** (see note below) |
| `Q0phys`/`Qppphys`/`rhoGeoPhys` | defined (concrete Lebowitz/Baxter PY coefficients) |
| `Q0_mat_phys` | defined (Q0_mat with physical coefficients substituted) |
| `Q0_mat_phys_isUnit_det_of_diag_dom` | **✓ proved**, conditional on diagonal dominance |
| `Q0_mat_n1_eq_scalar` | proved (N=1 consistency: matrix entry matches scalar Q₀) |

## Why the original axiom was wrong, and what replaces it

With `Qp`, `Qpp` left as free real-valued parameters (unconstrained by `sigma`/`rho`), the
original axiom is **false**, not just hard: `hz`, `hsigma`, `hrho`, `heta` say nothing about
`Qp`/`Qpp`, so they can be chosen adversarially to force `det = 0`. Concrete counterexample
(`n=2`, `σ₁=σ₂=1`, `z=1`, `rho_geo ≡ 0.1` giving `η ≈ 0.0105 ∈ (0,1)`, `Qpp≡0`,
`Qp ≈ −13.59`): `Q0_mat = !![0.5, -0.5; -0.5, 0.5]`, `det = 0`, yet every hypothesis holds.

The fix is to stop treating `Qp`/`Qpp` as free and substitute the actual multicomponent PY
(Lebowitz/Baxter) closed-form coefficients — `Q0phys`, `Qppphys` below, matching
`fmsa_ga_matrix_mix.py`'s `_build_Q0_Qpp`/`_build_Qhat` exactly. That turns M.3 into a
genuine (not vacuously false) mathematical claim.

**Proving it unconditionally for all `z > 0` is still open** (task M.4, `todo_lean.md`):
numerically, individual off-diagonal entries of the *raw* `Q0_mat_phys` blow up
exponentially as `z → ∞` whenever species diameters differ (`exp(-z·λᵢⱼ)` with `λᵢⱼ < 0`)
— the same exponential-cancellation obstruction as the FMSA_chsY/GA_matrix_mix 2YK failure
documented elsewhere in this project. So a direct per-entry bound (Gershgorin diagonal
dominance) can only hold for a *bounded* range of `z`, not unconditionally.

**What's proved now:** `Q0_mat_phys_isUnit_det_of_diag_dom` — *conditional* on an explicit,
checkable strict-diagonal-dominance hypothesis, via Mathlib's Gershgorin circle theorem
(`det_ne_zero_of_sum_row_lt_diag`). This is real, unconditional-modulo-hypothesis progress:
no axiom, and the hypothesis is a concrete inequality one can check numerically at any given
state point (rather than an opaque `‖C‖ < 1` operator-norm bound).

**Task M.4 — rank-2 reduction: now formalized in `LeanCode/HardSphere/Q0DetRankTwo.lean`.**
Everything below except the final scalar inequality is a **proved theorem**, no `sorry`/
`axiom`: `Umat`, `Vmat`, `Q0_mat_phys_eq_one_sub_mul` (the `1-U*V` factorization),
`Q0_mat_phys_det_eq_two_by_two` (Sylvester reduction to the 2×2 `det`), and `fFun_neg`/
`gFun_neg` (the sign facts below). The one remaining gap is stated as an explicit hypothesis
on `Q0_mat_phys_isUnit_det_of_two_by_two` — see that file for the final theorem.

`Q0_mat_phys(z)` is exactly a **rank-2 perturbation of the identity** for every `n`. Writing
`u := σ ↦ 2π/vac` etc. for brevity, define (per species `i`, at fixed `z`):
```
f(σ,z) := (π/vac)·(p₁(σ,z)·σ + 2·p₂(σ,z))
g(σ,z) := (π/vac)·p₁(σ,z) + (π²·ξ₂/vac²)·(p₁(σ,z)·σ/2 + p₂(σ,z))
u1_i := √ρᵢ · exp(z·σᵢ/2) · f(σᵢ,z)        v1_j := √ρⱼ · exp(-z·σⱼ/2)
u2_i := √ρᵢ · exp(z·σᵢ/2) · g(σᵢ,z)        v2_j := √ρⱼ · exp(-z·σⱼ/2) · σⱼ
```
Then (verified numerically to machine precision at every `z` tested, including `z` where
individual entries are `~10^84`): `Q0_mat_phys z sigma rho = 1 - U * V` where `U : Matrix
(Fin n) (Fin 2) ℝ` has columns `u1,u2` and `V : Matrix (Fin 2) (Fin n) ℝ` has rows `v1,v2`.
Mathlib's Weinstein–Aronszajn/Sylvester identity `det_one_sub_mul_comm : det (1 - A*B) =
det (1 - B*A)` (`Mathlib.LinearAlgebra.Matrix.SchurComplement`) then gives
`det (Q0_mat_phys z sigma rho) = det (1 - V * U)`, a **fixed 2×2 determinant regardless of
n** — explaining why individual entries diverge as `z → ∞` while `det` stays bounded: in
`V*U`, every entry is `Σᵢ ρᵢ·(...)`, and the `exp(zσᵢ/2)·exp(-zσᵢ/2) = 1` cancellation removes
the `z`-blowup entirely (it only survived in `U,V` because of the outer-product structure).

**Sign facts (provable, same `p(0)=0,p'(0)=0,p''>0` derivative-chain technique as
`bigD0/bigD1/bigD2` in `BaxterFactor.lean`):**
- `p₁(σ,z) < 0` for `σ,z > 0`: `p₁·z² = h(zσ)` where `h(u) := 1-u-e^{-u}`, `h(0)=0`,
  `h'(u) = -1+e^{-u} < 0` for `u>0`, so `h<0` on `(0,∞)` — a *one-step* derivative argument
  (simpler than 2.2/M.3, no need for a second derivative level).
- `p₂(σ,z) > 0` for `σ,z > 0`: `p₂·z³ = k(zσ)` where `k(u) := 1-u+u²/2-e^{-u}`, `k(0)=0,
  k'(0)=0, k''(u)=1-e^{-u}>0` for `u>0` ⟹ `k'` increasing from 0 ⟹ `k'>0` ⟹ `k` increasing
  from 0 ⟹ `k>0` on `(0,∞)`.
- `f(σ,z) < 0`: reduces to `m(u) := (2-u) - e^{-u}(u+2) < 0` for `u>0` via
  `m(0)=0, m'(0)=0, m''(u) = -u·e^{-u} < 0`.
- `g(σ,z) < 0`: the `(π/vac)·p₁` term is already `<0`; the remaining bracket reduces to
  `n(u) := (1-u/2) - e^{-u}(1+u/2) < 0` for `u>0` via `n(0)=0, n'(0)=0,
  n''(u) = -u·e^{-u}/2 < 0`.

So the reduced 2×2 matrix `M := V*U` has **all four entries strictly negative**
(`M₁₁=Σρᵢf(σᵢ), M₁₂=Σρᵢg(σᵢ), M₂₁=Σρᵢσᵢf(σᵢ), M₂₂=Σρᵢσᵢg(σᵢ)`, each a nonneg-weighted sum of a
strictly-negative quantity). Writing `a,b,c,d > 0` for `-M₁₁,-M₁₂,-M₂₁,-M₂₂`, the remaining
goal is the fully explicit, `n`-independent inequality:
```
(1+a)(1+d) > b·c
```
**Not yet closed:** this is NOT simple Cauchy-Schwarz on the moment sums (checked: `b·c` can
exceed `a·d`, e.g. `a=0.232,d=1.068,ad=0.248` vs `b=0.643,c=0.408,bc=0.262 > ad`), so it needs
a sharper relation between `f` and `g` specifically (not just their common sign). Numerically
very robust (20,000 random physical trials, `η` up to 0.999, `z ∈ [10⁻³,10⁴]`: smallest
`|det|` found was `1.0000013`, no zero crossing), but the exact algebraic reason is still
open. `Q0DetRankTwo.lean`'s `Q0_mat_phys_isUnit_det_of_two_by_two` takes this inequality as
an explicit hypothesis (in terms of `(Vmat*Umat) k l`, not `a,b,c,d`, but the same content)
rather than a `sorry` — this is the smallest honest remaining gap for M.4: one scalar
inequality between four finite species-sums, not an n×n claim.
-/

set_option linter.style.longLine false

open Real

namespace FMSA.MatrixQ0

/-! ### Scalar entry formula -/

/-- The (i,j) scalar entry of Q̂₀(z), parameterized by:
- `z`: Yukawa pole (> 0)
- `sigma_i`: diameter of species i
- `lam_ij = (sigma_j − sigma_i)/2`: size asymmetry parameter
- `Qp_ij`, `Qpp_ij`: Baxter DCF coefficients Q'ᵢⱼ, Q''ᵢⱼ
- `rho_geo_ij = √(ρᵢρⱼ)`: geometric-mean density
- `delta_ij`: Kronecker delta (1 if i=j, 0 otherwise) -/
noncomputable def q0_entry (z sigma_i lam_ij Qp_ij Qpp_ij rho_geo_ij delta_ij : ℝ) : ℝ :=
  delta_ij - rho_geo_ij * exp (-(lam_ij * z)) *
    (Qp_ij  * ((1 - z * sigma_i - exp (-(z * sigma_i))) / z ^ 2) +
     Qpp_ij * ((1 - z * sigma_i + (z * sigma_i) ^ 2 / 2 - exp (-(z * sigma_i))) / z ^ 3))

/-- The n×n Baxter Q-matrix Q̂₀(z), assembled from `q0_entry`.

Parameters:
- `sigma : Fin n → ℝ`: species diameters
- `rho_geo : Fin n → Fin n → ℝ`: `rho_geo i j = √(ρᵢ · ρⱼ)`
- `Qp Qpp : Fin n → Fin n → ℝ`: Baxter DCF coefficients -/
noncomputable def Q0_mat {n : ℕ} (z : ℝ)
    (sigma : Fin n → ℝ)
    (rho_geo : Fin n → Fin n → ℝ)
    (Qp Qpp : Fin n → Fin n → ℝ)
    : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => q0_entry z (sigma i) ((sigma j - sigma i) / 2)
               (Qp i j) (Qpp i j) (rho_geo i j) (if i = j then 1 else 0)

/-! ### Entry decomposition (proved from Task M.10) -/

/-- Each (i,j) entry of Q̂₀ satisfies the M.10 decomposition
`Q̂₀_{ij} = P̂_{ij} + Ê_{ij} · exp(-z · σ_min)`. -/
theorem Q0_mat_entry_decomp {n : ℕ} (z sigma_min : ℝ) (hz : z ≠ 0)
    (sigma : Fin n → ℝ)
    (rho_geo : Fin n → Fin n → ℝ)
    (Qp Qpp : Fin n → Fin n → ℝ)
    (i j : Fin n)
    (hR : (sigma j - sigma i) / 2 + sigma i = (sigma i + sigma j) / 2) :
    Q0_mat z sigma rho_geo Qp Qpp i j =
    ((if i = j then 1 else 0) -
     rho_geo i j * exp (-((sigma j - sigma i) / 2 * z)) *
       (Qp i j * ((1 - z * sigma i) / z ^ 2) +
        Qpp i j * ((1 - z * sigma i + (z * sigma i) ^ 2 / 2) / z ^ 3))) +
    rho_geo i j * exp (-(z * ((sigma i + sigma j) / 2 - sigma_min))) *
      (Qp i j / z ^ 2 + Qpp i j / z ^ 3) * exp (-(z * sigma_min)) := by
  unfold Q0_mat q0_entry
  exact FMSA.PathB.b2_qhat_entry_decomp z (sigma i) ((sigma j - sigma i) / 2)
    ((sigma i + sigma j) / 2) sigma_min (rho_geo i j) (Qp i j) (Qpp i j)
    (if i = j then 1 else 0) hz hR

/-! ### Task M.3 — concrete physical coefficients (Lebowitz/Baxter multicomponent PY) -/

/-- Second packing-fraction moment `ξ₂ = Σᵢ ρᵢ σᵢ²` (no π/6 prefactor; matches
`fmsa_ga_matrix_mix.py`'s `xi[2]`). -/
noncomputable def xi2 {n : ℕ} (rho sigma : Fin n → ℝ) : ℝ :=
  ∑ i, rho i * sigma i ^ 2

/-- Total packing fraction `η = (π/6) Σᵢ ρᵢ σᵢ³`. -/
noncomputable def etaMix {n : ℕ} (rho sigma : Fin n → ℝ) : ℝ :=
  Real.pi / 6 * ∑ i, rho i * sigma i ^ 3

/-- `vac = 1 − η`, the packing "vacancy" fraction. -/
noncomputable def vacMix {n : ℕ} (rho sigma : Fin n → ℝ) : ℝ :=
  1 - etaMix rho sigma

/-- Physical Baxter coefficient `Q'ᵢⱼ = Q₀[i,j]` (Lebowitz multicomponent PY solution),
matching `fmsa_ga_matrix_mix.py`'s `_build_Q0_Qpp`:
`Q₀[i,j] = (2π/vac) · (Rᵢⱼ + π·ξ₂·σᵢ·σⱼ/(4·vac))`, `Rᵢⱼ = (σᵢ+σⱼ)/2`. -/
noncomputable def Q0phys {n : ℕ} (rho sigma : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (2 * Real.pi / vacMix rho sigma) *
    ((sigma i + sigma j) / 2 +
      Real.pi * xi2 rho sigma * sigma i * sigma j / (4 * vacMix rho sigma))

/-- Physical Baxter coefficient `Q''ᵢⱼ = Qpp[j]` (independent of `i`), matching
`fmsa_ga_matrix_mix.py`'s `_build_Q0_Qpp`: `Qpp[j] = (2π/vac) · (1 + π·ξ₂·σⱼ/(2·vac))`. -/
noncomputable def Qppphys {n : ℕ} (rho sigma : Fin n → ℝ) (_i j : Fin n) : ℝ :=
  (2 * Real.pi / vacMix rho sigma) *
    (1 + Real.pi * xi2 rho sigma * sigma j / (2 * vacMix rho sigma))

/-- Geometric-mean density `√(ρᵢρⱼ)`. -/
noncomputable def rhoGeoPhys {n : ℕ} (rho : Fin n → ℝ) (i j : Fin n) : ℝ :=
  Real.sqrt (rho i * rho j)

/-- The physical (Lebowitz/Baxter) multicomponent Q̂₀(z) matrix, with `Qp`/`Qpp`/`rho_geo`
substituted by their concrete PY-mixture formulas instead of left as free parameters. -/
noncomputable def Q0_mat_phys {n : ℕ} (z : ℝ) (sigma rho : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Q0_mat z sigma (rhoGeoPhys rho) (Q0phys rho sigma) (Qppphys rho sigma)

/-- **Task M.3 (conditional, proved):** if the physical `Q0_mat_phys` satisfies strict row
diagonal dominance — an explicit, checkable inequality on the concrete Lebowitz/Baxter
coefficients — then it is invertible.

This replaces the previous *unconditional* axiom, which was **false**: with `Qp`, `Qpp` left
as free parameters (not tied to `sigma`/`rho`), one can choose them adversarially to force
`det = 0` even when every stated hypothesis (`z > 0`, `σᵢ > 0`, `ρᵢ ≥ 0`, `η ∈ (0,1)`) holds.
Concrete counterexample: `n=2`, equal diameters, `z=1`, `rho_geo ≡ 0.1`, `Qpp≡0`,
`Qp ≈ −13.59` gives `Q0_mat = !![0.5, -0.5; -0.5, 0.5]`, `det = 0`.

Proving the unconditional statement (`∀ z > 0`) for `Q0_mat_phys` is task M.4
(`todo_lean.md`): numerically, diagonal dominance fails for large `z` whenever species
diameters differ (the same exponential-growth obstruction as the FMSA_chsY/GA_matrix_mix
2YK failure), so it likely needs the M.10 `P̂+Ê·exp(−z·σmin)` split rather than a direct bound
on the raw matrix. This theorem is the useful, checkable, unconditional-modulo-hypothesis
partial result available now. -/
theorem Q0_mat_phys_isUnit_det_of_diag_dom {n : ℕ} {z : ℝ} {sigma rho : Fin n → ℝ}
    (hdom : ∀ k, ∑ j ∈ Finset.univ.erase k, |Q0_mat_phys z sigma rho k j| <
                 |Q0_mat_phys z sigma rho k k|) :
    IsUnit (Q0_mat_phys z sigma rho).det := by
  rw [isUnit_iff_ne_zero]
  apply det_ne_zero_of_sum_row_lt_diag
  simpa only [Real.norm_eq_abs] using hdom

/-! ### N=1 consistency check -/

/-- For n=1, the Q̂₀ matrix is 1×1, and its single entry matches the scalar
single-component Q₀ formula.

Concretely: `Q0_mat z σ ρ_geo Qp Qpp 0 0 = 1 − ρ · [Q'·p₁(σ,z) + Q''·p₂(σ,z)]`
with `λ₀₀ = 0` (no size asymmetry for a single component). -/
theorem Q0_mat_n1_entry (z sigma rho_geo Qp Qpp : ℝ) :
    Q0_mat z (fun _ : Fin 1 => sigma)
             (fun _ _ : Fin 1 => rho_geo)
             (fun _ _ : Fin 1 => Qp)
             (fun _ _ : Fin 1 => Qpp) 0 0 =
    1 - rho_geo * exp 0 *
      (Qp  * ((1 - z * sigma - exp (-(z * sigma))) / z ^ 2) +
       Qpp * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - exp (-(z * sigma))) / z ^ 3)) := by
  unfold Q0_mat q0_entry
  simp

end FMSA.MatrixQ0
