/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterOzStar
import LeanCode.HardSphere.RadialLaplace
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.HardSphere.ShellKernel

/-!
# Matrix OZ★ — the mixture real-space Ornstein–Zernike identity (foundation)

Task **MRS.9 / matrix OZ★** — the START of the mixture real-space Baxter core that MML.8's collapse
needs. The scalar OZ★ `baxterPsi_ozstar` (`BaxterOzStar.lean`, unconditional) is the real-space OZ
convolution equation for the constructed hard-sphere Baxter solution `baxterPsi`:

    baxterPsi(r) = r·c_HS(r) + ρ·r·radial3d_conv(c_HS, baxterPsi/·)(r).

The full mixture analog — the matrix real-space Baxter renewal identity for the constructed *matrix*
`baxterPsi`, discharging its integrability side-conditions — is the analog of the entire
`BaxterRenewal.lean` + `BaxterOzStar.lean` apparatus (`OZFIX.15–20`), a large undertaking. This file
lays the **structural foundation**:

* `matRadialConv` — the entrywise matrix radial convolution `(A ⋆ B)ᵢⱼ = ∑ₖ radial3d_conv Aᵢₖ Bₖⱼ`,
  so the matrix OZ equation reduces to the *scalar* `radial3d_conv` machinery per entry (with a
  coupling sum over the intermediate species `k`).
* `MatOZStar` — the matrix OZ★ predicate: each entry `Ψᵢⱼ` satisfies the scalar-OZ-shaped equation
  with forcing `Φᵢⱼ` and the species-coupling convolution sum.
* `matOZStar_entry` — the explicit coupled entry equation (exhibiting the `∑ₖ` species coupling that
  distinguishes the matrix case from `N` independent scalar problems).
* `matOZStar_fin_one_of_scalar` — the **`n = 1` soundness bridge**: at one component `MatOZStar` is
  *exactly* the proved scalar `baxterPsi_ozstar`. The framework specializes correctly to the known
  scalar theory (the MML.13 / MRS.0b discipline), and this doubles as a non-vacuity witness.

## What this is not

This does not prove the general-`N` matrix OZ★ — that needs the constructed matrix `baxterPsi`, the
matrix Baxter factorization inverse-transformed to real space, and the matrix analogs of the
fourteen integrability side-conditions. It fixes the *target shape* and validates it against the
scalar case; the analytic construction is the remaining research-scale work.

Status: ✓ axiom-clean (foundation only).
-/

set_option linter.style.longLine false

open scoped Matrix

namespace FMSA.MixtureOzStar

open FMSA.HardSphere

noncomputable section

/-! ### The entrywise matrix radial convolution -/

/-- **Matrix radial convolution.**  `(A ⋆ B)ᵢⱼ(r) = ∑ₖ radial3d_conv(Aᵢₖ, Bₖⱼ)(r)` — the matrix
product of the scalar radial convolutions, summed over the intermediate species `k`.  Reduces the
matrix OZ convolution to the scalar `radial3d_conv` machinery (`RadialLaplace.lean`), per entry. -/
def matRadialConv {N : ℕ} (A B : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (r : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ k, radial3d_conv (A i k) (B k j) r

/-- The entry formula for `matRadialConv` (definitional). -/
theorem matRadialConv_apply {N : ℕ} (A B : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (r : ℝ) (i j : Fin N) :
    matRadialConv A B r i j = ∑ k, radial3d_conv (A i k) (B k j) r := rfl

/-- **At one component the matrix convolution is the scalar one.**  `matRadialConv A B r 0 0 =
radial3d_conv (A 0 0) (B 0 0) r` — the single-term sum over `Fin 1`. -/
theorem matRadialConv_fin_one (A B : Matrix (Fin 1) (Fin 1) (ℝ → ℝ)) (r : ℝ) :
    matRadialConv A B r 0 0 = radial3d_conv (A 0 0) (B 0 0) r := by
  simp [matRadialConv]

/-! ### The matrix OZ★ predicate -/

/-- **Matrix OZ★.**  The mixture real-space Ornstein–Zernike identity for the `r`-weighted matrix
solution `Ψ` (the matrix `baxterPsi` analog) with forcing `Φ` (the matrix `c_HS` analog):

    Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·r·(matRadialConv Φ (Ψ/·))ᵢⱼ(r),   for `r > 0`.

Each entry satisfies a scalar-OZ-shaped equation, coupled across species by the `∑ₖ` of
`matRadialConv`.  Held as a `Prop` — the concrete `Ψ, Φ` and the proof that it holds are the
matrix-Baxter construction (the remaining research-scale work); this fixes the target shape.  At
`N = 1` it is exactly the scalar `baxterPsi_ozstar` (`matOZStar_fin_one_of_scalar`). -/
def MatOZStar {N : ℕ} (Psi Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ) : Prop :=
  ∀ (i j : Fin N) (r : ℝ), 0 < r →
    Psi i j r = r * Phi i j r
      + rho * (r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j)

/-- **The coupled entry equation.**  Unfolding `MatOZStar` at `(i, j)`: the forcing is `Φᵢⱼ`, but the
convolution term sums over the intermediate species `k`, `∑ₖ radial3d_conv(Φᵢₖ, Ψₖⱼ/·)` — the species
coupling that makes the matrix OZ★ genuinely more than `N` independent scalar problems. -/
theorem matOZStar_entry {N : ℕ} {Psi Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)} {rho : ℝ}
    (h : MatOZStar Psi Phi rho) (i j : Fin N) (r : ℝ) (hr : 0 < r) :
    Psi i j r = r * Phi i j r
      + rho * (r * ∑ k, radial3d_conv (Phi i k) (fun x => Psi k j x / x) r) := by
  have := h i j r hr
  rwa [matRadialConv_apply] at this

/-! ### The `n = 1` soundness bridge -/

/-- **`n = 1` bridge — the matrix OZ★ specializes to the proved scalar OZ★.**  With the single entry
`Ψ = baxterPsi`, `Φ = c_HS`, `MatOZStar` at `Fin 1` is exactly `baxterPsi_ozstar` (unconditional,
`BaxterOzStar.lean`).  This validates the target shape against the known scalar theory (the MML.13 /
MRS.0b discipline) and witnesses that `MatOZStar` is instantiable — it is not a vacuous `Prop`. -/
theorem matOZStar_fin_one_of_scalar {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    MatOZStar (N := 1) (fun _ _ => baxterPsi eta sigma rho) (fun _ _ => c_HS eta sigma) rho := by
  intro i j r hr
  fin_cases i; fin_cases j
  simp only [matRadialConv, Fin.sum_univ_one]
  exact baxterPsi_ozstar hsigma heta heta_def r hr

/-! ### The matrix Baxter factorization in real space (foundation of the renewal equation)

The scalar OZ★ construction is built on the **real-space Baxter factorization** (`OZFIX.18` KDEF,
`rho_baxterK_eq_q0_self_conv`): `ρ·K(v) = q0(v) − ∫_v^σ q0(t)·q0(t−v)dt` — the real-space content of
`1 − ρĈ = Q̂(k)·Q̂(−k)`, from which the renewal equation and hence OZ★ follow. The matrix analog
starts here: the mixture factorization `I − Ĉ₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (MRS.6 `Cmix0_factorization`,
Fourier) inverse-transforms to a matrix real-space identity whose convolution term is the
**species-summed correlation** `∑ₖ ∫ q0ᵢₖ(t)·q0ⱼₖ(t−v)dt` (the `ᵀ` of `Q̂₀ᵀ(−k)` contributes the
shared `k`-sum; the `−k` reflection makes it a correlation). -/

/-- **Matrix self-convolution.**  `(Q ⋆ Qᵀ)ᵢⱼ(v) = ∑ₖ ∫_v^σ Qᵢₖ(t)·Qⱼₖ(t−v) dt` — the real-space
image of `Q̂₀(k)·Q̂₀ᵀ(−k)`, summed over the intermediate species `k` (the `ᵀ`) and correlated (the
`−k`).  Reduces to the scalar self-convolution `∫ q0(t)·q0(t−v)` per entry-pair. -/
def matSelfConv {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma v : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ k, ∫ t in v..sigma, Q i k t * Q j k (t - v)

/-- The entry formula for `matSelfConv` (definitional). -/
theorem matSelfConv_apply {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma v : ℝ) (i j : Fin N) :
    matSelfConv Q sigma v i j = ∑ k, ∫ t in v..sigma, Q i k t * Q j k (t - v) := rfl

/-- At one component the matrix self-convolution is the scalar one. -/
theorem matSelfConv_fin_one (Q : Matrix (Fin 1) (Fin 1) (ℝ → ℝ)) (sigma v : ℝ) :
    matSelfConv Q sigma v 0 0 = ∫ t in v..sigma, Q 0 0 t * Q 0 0 (t - v) := by
  simp [matSelfConv]

/-- **Matrix Baxter factorization (real-space KDEF).**  `ρ·Kᵢⱼ(v) = qᵢⱼ(v) − (matSelfConv q)ᵢⱼ(v)`
on `(0, σ)` — the mixture analog of `rho_baxterK_eq_q0_self_conv`, the real-space content of the
matrix WH factorization. Held as a `Prop`; the concrete matrix `K, q` (from `Q0_mat_c`) and its proof
are the matrix-Baxter construction. At `N = 1` it is exactly the scalar KDEF
(`matBaxterFactorization_fin_one_of_scalar`). -/
def MatBaxterFactorization {N : ℕ} (Kmat Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho sigma : ℝ) :
    Prop :=
  ∀ (i j : Fin N) (v : ℝ), v ∈ Set.Ioo (0 : ℝ) sigma →
    rho * Kmat i j v = Q i j v - matSelfConv Q sigma v i j

/-- **`n = 1` bridge — the matrix factorization specializes to the proved scalar KDEF.**  With the
single entry `K = baxterK`, `q = q0_poly`, `MatBaxterFactorization` at `Fin 1` is exactly
`rho_baxterK_eq_q0_self_conv` (`OZFIX.18`). Validates the target shape and witnesses non-vacuity. -/
theorem matBaxterFactorization_fin_one_of_scalar {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    MatBaxterFactorization (N := 1) (fun _ _ => baxterK eta sigma)
      (fun _ _ => q0_poly eta sigma rho) rho sigma := by
  intro i j v hv
  fin_cases i; fin_cases j
  simp only [matSelfConv, Fin.sum_univ_one]
  exact rho_baxterK_eq_q0_self_conv hsigma heta heta_def hv

/-! ### The matrix shell-conv = K-conv bridge (`OZFIX.19` analog)

The scalar `radial3d_conv_eq_baxterK_shell` (`OZFIX.19`) is the bridge that converts the 3D radial
convolution into a 1D convolution with the Baxter shell kernel:

    r·radial3d_conv(c_HS, g)(r) = ∫₀^σ baxterK(u)·(oddExt g(r−u) + oddExt g(r+u)) du.

It is what ties the OZ★ convolution term (`matRadialConv`, the OZ★ shape) to the Baxter kernel `K`
(`matSelfConv`, the factorization). **The matrix analog is the scalar identity summed over the
intermediate species `k`** — no new analysis, because `matRadialConv` is a sum of scalar
`radial3d_conv`s and `r` pulls inside the sum. The genuine matrix content is the assembly; the
per-entry `(i,k)` identity is scalar. -/

/-- **Matrix shell convolution.**  `(matShellConv K G)ᵢⱼ(r) = ∑ₖ ∫₀^σ Kᵢₖ(u)·(oddExt Gₖⱼ(r−u) +
oddExt Gₖⱼ(r+u)) du` — the 1D Baxter-kernel form of the matrix radial convolution, species-summed. -/
def matShellConv {N : ℕ} (Kmat G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ k, ∫ u in (0 : ℝ)..sigma,
    Kmat i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u))

/-- The entry formula for `matShellConv` (definitional). -/
theorem matShellConv_apply {N : ℕ} (Kmat G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ)
    (i j : Fin N) :
    matShellConv Kmat G sigma r i j
      = ∑ k, ∫ u in (0 : ℝ)..sigma,
          Kmat i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)) := rfl

/-- **The matrix shell-conv = K-conv bridge (`OZFIX.19` analog).**  Given the per-`(i,k)` scalar
shell identity, `r·(matRadialConv C G)ᵢⱼ(r) = (matShellConv K G)ᵢⱼ(r)`.  Pure assembly: `r` pulls
inside the species sum (`Finset.mul_sum`) and each summand is the scalar identity (`hentry`). -/
theorem matRadialConv_eq_matShellConv {N : ℕ} (C G Kmat : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma r : ℝ) (i j : Fin N)
    (hentry : ∀ k, r * radial3d_conv (C i k) (G k j) r
      = ∫ u in (0 : ℝ)..sigma, Kmat i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u))) :
    r * matRadialConv C G r i j = matShellConv Kmat G sigma r i j := by
  unfold matRadialConv matShellConv
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => hentry k)

/-- **`n = 1` bridge — the shell-conv identity's per-entry input is the proved scalar `OZFIX.19`.**
At one component the `hentry` of `matRadialConv_eq_matShellConv` (with `C = c_HS`, `K = baxterK`) is
exactly `radial3d_conv_eq_baxterK_shell`, so the matrix bridge holds there. Validates the assembly
against the proved scalar shell identity (carrying its two integrability hypotheses `hshell`,
`hjoint`, discharged unconditionally in `BaxterOzStar.lean` for the `g = baxterPsi/·` instance). -/
theorem matShellBridge_fin_one_of_scalar {eta sigma : ℝ} (hsigma : 0 < sigma) (g : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hshell : ∀ t ∈ Set.Ioi (0 : ℝ),
      IntervalIntegrable (oddExt g) MeasureTheory.volume (r - t) (r + t))
    (hjoint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * c_HS eta sigma s) s
        * (oddExt g (r - u) + oddExt g (r + u)))
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma)))) :
    r * matRadialConv (N := 1) (fun _ _ => c_HS eta sigma) (fun _ _ => g) r 0 0
      = matShellConv (N := 1) (fun _ _ => baxterK eta sigma) (fun _ _ => g) sigma r 0 0 := by
  apply matRadialConv_eq_matShellConv
  intro k
  fin_cases k
  exact radial3d_conv_eq_baxterK_shell hsigma hr hshell hjoint

/-- **The matrix shell bridge for arbitrary mixture entries** (general-`c`, `OZFIX.19` generalized).
With the shell kernel *built from the entries* `Kᵢₖ = shellKernel (Cᵢₖ)`, the per-`(i,k)` `hentry` is
discharged by `radial3d_conv_eq_shellKernel` (`ShellKernel.lean`) — no longer needing a separate
kernel input, and valid for the mixture DCF entries `C₀ᵢₖ` (each a different `c`-shape at its own
`σ_ik`), not just the single `c_HS`.  This is the general-`N` form the mixture OZ★ assembly consumes,
with only the per-entry support + integrability side-conditions as hypotheses. -/
theorem matRadialConv_eq_matShellConv_of_shellKernel {N : ℕ}
    (C G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {sigma : ℝ} (hsigma : 0 < sigma) {r : ℝ} (hr : 0 < r)
    (i j : Fin N)
    (hCsupp : ∀ k s, sigma ≤ s → C i k s = 0)
    (hshell : ∀ k, ∀ t ∈ Set.Ioi (0 : ℝ),
      IntervalIntegrable (oddExt (G k j)) MeasureTheory.volume (r - t) (r + t))
    (hjoint : ∀ k, MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * C i k s) s
        * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)))
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma)))) :
    r * matRadialConv C G r i j
      = matShellConv (fun i k => shellKernel (C i k) sigma) G sigma r i j := by
  apply matRadialConv_eq_matShellConv
  intro k
  exact radial3d_conv_eq_shellKernel hsigma (hCsupp k) hr (hshell k) (hjoint k)

/-! ### The matrix `baxterPsi` construction (shape + renewal equation)

The scalar `baxterPsi` (`BaxterRenewal.lean`) is the three-branch glued solution: the outer Volterra
renewal solution `baxterPsiOuter` on `[σ,∞)`, its odd reflection on `(−∞,−σ]`, and the *definitional*
core value `−v` on `(−σ,σ)`. It satisfies `baxterPsiOuter_spec`, the renewal equation. The matrix
`baxterPsi` has the same shape, coupled across species in the renewal integral.

* `matBaxterPsi Ψouter Ψcore σ` — the matrix glued solution, same three branches (`Ψouter` the outer
  matrix Volterra solution, `Ψcore` the definitional core, e.g. `−v` per entry).
* `matBaxterPsi_core` / `matBaxterPsi_outer` / `matBaxterPsi_reflect` — the branch equations.
* `MatRenewalEq Ψouter F Q σ` — the matrix renewal equation `Ψouterᵢⱼ(r) = Fᵢⱼ(r) + ∑ₖ ∫_σ^r
  Qᵢₖ(r−t)·Ψouterₖⱼ(t) dt` (`r ≥ σ`), the **coupled** Volterra system across species `k`.
* `matBaxterPsi_fin_one_of_scalar` / `matRenewalEq_fin_one_of_scalar` — the **`n = 1` bridges**: the
  matrix `baxterPsi` core branch is the scalar `baxterPsi`, and `MatRenewalEq` is exactly the proved
  scalar `baxterPsiOuter_spec`.

`Ψouter` is taken as a parameter — constructing it (solving the coupled matrix Volterra system, the
matrix analog of `volterraGlobal`/`MA.10`) is the remaining analytic core; this fixes the object's
shape and its defining equation, and validates both at `n = 1`. -/

/-- **Matrix `baxterPsi`.**  The glued solution: outer `Ψouter` on `[σ,∞)`, its odd reflection on
`(−∞,−σ]`, and the definitional core `Ψcore` on `(−σ,σ)` — the matrix analog of `baxterPsi`. -/
def matBaxterPsi {N : ℕ} (Psiouter Psicore : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) :
    Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  fun i j v => if sigma ≤ v then Psiouter i j v
    else if v ≤ -sigma then -Psiouter i j (-v)
    else Psicore i j v

/-- The core branch: `matBaxterPsi = Ψcore` on `(−σ,σ)` (definitional, no proof obligation). -/
theorem matBaxterPsi_core {N : ℕ} (Psiouter Psicore : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {sigma : ℝ}
    (i j : Fin N) {v : ℝ} (hv : v ∈ Set.Ioo (-sigma) sigma) :
    matBaxterPsi Psiouter Psicore sigma i j v = Psicore i j v := by
  rw [matBaxterPsi, if_neg (not_le.mpr hv.2), if_neg (not_le.mpr hv.1)]

/-- The outer branch: `matBaxterPsi = Ψouter` on `[σ,∞)`. -/
theorem matBaxterPsi_outer {N : ℕ} (Psiouter Psicore : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {sigma : ℝ}
    (i j : Fin N) {v : ℝ} (hv : sigma ≤ v) :
    matBaxterPsi Psiouter Psicore sigma i j v = Psiouter i j v := by
  rw [matBaxterPsi, if_pos hv]

/-- The reflected branch: `matBaxterPsi(v) = −Ψouter(−v)` on `(−∞,−σ]` (for `σ > 0`, so `v < σ`). -/
theorem matBaxterPsi_reflect {N : ℕ} (Psiouter Psicore : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {sigma : ℝ}
    (hsigma : 0 < sigma) (i j : Fin N) {v : ℝ} (hv : v ≤ -sigma) :
    matBaxterPsi Psiouter Psicore sigma i j v = -Psiouter i j (-v) := by
  have hvs : ¬ sigma ≤ v := by
    intro h; have : sigma ≤ -sigma := le_trans h hv; linarith
  rw [matBaxterPsi, if_neg hvs, if_pos hv]

/-- **The matrix renewal equation** — the coupled Volterra system across species `k` that the outer
matrix solution satisfies: `Ψouterᵢⱼ(r) = Fᵢⱼ(r) + ∑ₖ ∫_σ^r Qᵢₖ(r−t)·Ψouterₖⱼ(t) dt`, `r ≥ σ`. -/
def MatRenewalEq {N : ℕ} (Psiouter Fmat Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) : Prop :=
  ∀ (i j : Fin N) (r : ℝ), sigma ≤ r →
    Psiouter i j r = Fmat i j r + ∑ k, ∫ t in sigma..r, Q i k (r - t) * Psiouter k j t

/-- **`n = 1` bridge — the matrix `baxterPsi` core is the scalar `baxterPsi`.** -/
theorem matBaxterPsi_fin_one_of_scalar {eta sigma rho : ℝ} (i j : Fin 1) {v : ℝ}
    (hv : v ∈ Set.Ioo (-sigma) sigma) :
    matBaxterPsi (N := 1) (fun _ _ => baxterPsiOuter eta sigma rho) (fun _ _ v => -v) sigma i j v
      = baxterPsi eta sigma rho v := by
  fin_cases i; fin_cases j
  rw [matBaxterPsi_core _ _ _ _ hv, baxterPsi_core hv]

/-- **`n = 1` bridge — `MatRenewalEq` is the proved scalar `baxterPsiOuter_spec`.** -/
theorem matRenewalEq_fin_one_of_scalar {eta sigma rho : ℝ} :
    MatRenewalEq (N := 1) (fun _ _ => baxterPsiOuter eta sigma rho)
      (fun _ _ => baxterForcing eta sigma rho) (fun _ _ => q0_poly eta sigma rho) sigma := by
  intro i j r hr
  fin_cases i; fin_cases j
  simp only [Fin.sum_univ_one]
  exact baxterPsiOuter_spec hr

end

end FMSA.MixtureOzStar
