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
import LeanCode.Analysis.VolterraBanach

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

/-- **Constructing `Ψouter` — the matrix Volterra system is solvable.**  The mixture Baxter renewal
`Ψ(r) = F(r) + ∫_σ^r Q(r−t)·Ψ(t) dt` (matrix product; the species-coupling `∑ₖ Qᵢₖ·Ψₖⱼ` *is*
`(Q·Ψ)ᵢⱼ`) has a **unique continuous matrix solution** on `[σ,b]` — the `Ψouter` the matrix
`baxterPsi` needs. Direct instantiation of the Banach generalization of `MA.10`
(`volterra_convolution_existsUniqueE`, `Analysis/VolterraBanach.lean`) at the complete normed ring
`E = Matrix (Fin N) (Fin N) ℝ` (with the submultiplicative `Matrix.linftyOp` norm). The entrywise
`MatRenewalEq` form follows by the matrix-entry evaluation commuting with the integral
(`Matrix.mul_apply` + `ContinuousLinearMap.intervalIntegral_comp_comm`), a mechanical step. -/
theorem matVolterra_convolution_existsUnique {N : ℕ} {sigma b : ℝ} (hsb : sigma ≤ b)
    (Q F : ℝ → Matrix (Fin N) (Fin N) ℝ) (hQ : Continuous Q) (hF : Continuous F) :
    letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
    ∃! u : C(Set.Icc sigma b, Matrix (Fin N) (Fin N) ℝ), ∀ r : Set.Icc sigma b,
      u r = F r + ∫ t in sigma..(r : ℝ), Q ((r : ℝ) - t) * Set.IccExtend hsb u t := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  exact FMSA.VolterraBanach.volterra_convolution_existsUniqueE hsb Q F hQ hF

/-! ### Entry extraction — from the matrix-product renewal to the `∑ₖ` `MatRenewalEq` form

`matVolterra_convolution_existsUnique` gives `Ψouter` in **matrix-product** form
`u(r) = F(r) + ∫ Q(r−t)·u(t) dt`. Getting the entrywise `MatRenewalEq` (`∑ₖ ∫ Qᵢₖ·Ψₖⱼ`) needs the
matrix-entry evaluation to commute with the Bochner integral. This routes through
`ContinuousLinearMap.intervalIntegral_comp_comm` at the entry CLM `Matrix.entryLinearMap.toCLM`, which
requires `IntervalIntegrable (f : ℝ → Matrix ℝ)`.

⚠ **Matrix-norm instance-diamond fix.** Under the `letI`'d `Matrix.linftyOp` norm, that predicate does
**not** elaborate on its own — `ENormedAddMonoid (Matrix ℝ)` is not synthesized (the default `Matrix`
product topology competes with the norm's, so `NormedAddCommGroup.toENormedAddCommMonoid`'s topology
does not unify). The fix is to **provide it explicitly**:
`letI : ENormedAddCommMonoid (Matrix ℝ) := NormedAddCommGroup.toENormedAddCommMonoid`, which pins the
norm-induced topology. With that one `letI`, the entry-of-integral commute goes through. -/

/-- **Entry of a matrix interval integral = interval integral of the entry.**  `(∫ f)ᵢⱼ = ∫ fᵢⱼ` for
`f : ℝ → Matrix ℝ`, via `ContinuousLinearMap.intervalIntegral_comp_comm` at the entry CLM.  The
`ENormedAddCommMonoid` `letI` is the instance-diamond fix (see the section note). -/
theorem matrix_intervalIntegral_apply {N : ℕ}
    (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (a b : ℝ) (i j : Fin N)
    (hf : letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
          letI : ENormedAddCommMonoid (Matrix (Fin N) (Fin N) ℝ) :=
            NormedAddCommGroup.toENormedAddCommMonoid
          IntervalIntegrable f MeasureTheory.volume a b) :
    letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
    (∫ t in a..b, f t) i j = ∫ t in a..b, (f t) i j := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  letI : ENormedAddCommMonoid (Matrix (Fin N) (Fin N) ℝ) :=
    NormedAddCommGroup.toENormedAddCommMonoid
  let hL : Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)
  exact (hL.intervalIntegral_comp_comm hf).symm

/-- **The renewal's convolution term, entrywise = the `∑ₖ` `MatRenewalEq` form.**
`(∫ Q(t)·U(t) dt)ᵢⱼ = ∑ₖ ∫ Qᵢₖ(t)·Uₖⱼ(t) dt` for continuous matrix-valued `Q, U` — the composite of
`matrix_intervalIntegral_apply`, `Matrix.mul_apply`, and `intervalIntegral.integral_finsetSum`. This
turns the matrix-product `Ψouter` (`matVolterra_convolution_existsUnique`) into the `∑ₖ` species-sum
of `MatRenewalEq`. -/
theorem matrix_mul_intervalIntegral_entry {N : ℕ}
    (Q U : ℝ → Matrix (Fin N) (Fin N) ℝ) (a b : ℝ) (i j : Fin N)
    (hQ : Continuous Q) (hU : Continuous U) :
    letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
    (∫ t in a..b, Q t * U t) i j = ∑ k, ∫ t in a..b, (Q t) i k * (U t) k j := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  letI : ENormedAddCommMonoid (Matrix (Fin N) (Fin N) ℝ) :=
    NormedAddCommGroup.toENormedAddCommMonoid
  have hint : IntervalIntegrable (fun t => Q t * U t) MeasureTheory.volume a b :=
    (hQ.mul hU).intervalIntegrable a b
  rw [matrix_intervalIntegral_apply _ a b i j hint]
  have hstep : (fun t => (Q t * U t) i j) = fun t => ∑ k, (Q t) i k * (U t) k j := by
    funext t; rw [Matrix.mul_apply]
  rw [hstep, intervalIntegral.integral_finsetSum]
  intro k _
  exact ((hQ.matrix_elem i k).mul (hU.matrix_elem k j)).intervalIntegrable a b

/-- **Entry extraction, end-to-end — the matrix-product renewal *is* `MatRenewalEq`.**  From a
matrix-product renewal `Ψ(r) = F(r) + ∫_σ^r Q(r−t)·Ψ(t) dt` (the `matVolterra_convolution_existsUnique`
form) with continuous `Ψ, Q`, the entrywise `MatRenewalEq` holds for the entry families
`Ψᵢⱼ = (Ψ ·)ᵢⱼ`, `Fᵢⱼ = (F ·)ᵢⱼ`, `Qᵢₖ = (Q ·)ᵢₖ`.  Pure application of
`matrix_mul_intervalIntegral_entry` per entry — so `Ψouter` is now constructed **in the `∑ₖ`
`MatRenewalEq` form the matrix `baxterPsi` consumes**, the plumbing fully resolved. -/
theorem matRenewalEq_of_matrixProduct {N : ℕ} {sigma : ℝ}
    (Psi Q F : ℝ → Matrix (Fin N) (Fin N) ℝ) (hQ : Continuous Q) (hPsi : Continuous Psi)
    (hrenewal : letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
      letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
      ∀ r : ℝ, sigma ≤ r → Psi r = F r + ∫ t in sigma..r, Q (r - t) * Psi t) :
    MatRenewalEq (fun i j => fun r => (Psi r) i j) (fun i j => fun r => (F r) i j)
      (fun i k => fun s => (Q s) i k) sigma := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  intro i j r hr
  change (Psi r) i j = (F r) i j + ∑ k, ∫ t in sigma..r, (Q (r - t)) i k * (Psi t) k j
  have hentry : (Psi r) i j = (F r) i j + (∫ t in sigma..r, Q (r - t) * Psi t) i j := by
    rw [hrenewal r hr]; rfl
  rw [hentry]
  congr 1
  exact matrix_mul_intervalIntegral_entry (fun t => Q (r - t)) Psi sigma r i j
    (hQ.comp (continuous_const.sub continuous_id)) hPsi

/-! ### The concrete matrix outer solution `Ψouter` (Banach global Volterra at the matrix ring)

The scaffolding above took `Ψouter` as a parameter (`MatRenewalEq` for an *assumed* outer solution).
Instantiating the Banach **global** Volterra solution (`VolterraBanach.volterraGlobalE`) at the matrix
ring `Matrix (Fin N) (Fin N) ℝ` (the `linftyOp` norm) constructs it concretely.  Its `max σ ·`-
precomposed representative `matBaxterPsiOuterFun` is continuous on all of `ℝ` and agrees with the
solution on `[σ,∞)`, so it feeds `matRenewalEq_of_matrixProduct` and yields the entrywise `∑ₖ`
`MatRenewalEq` — `Ψouter` is now a **constructed** object, not a hypothesis, for any continuous
mixture Baxter data `Q, F`. -/

/-- **The concrete matrix outer solution.**  The Banach global Volterra solution at the matrix ring,
precomposed with `max σ ·` so it is continuous on all of `ℝ` (and equals the solution on `[σ,∞)`). -/
def matBaxterPsiOuterFun {N : ℕ} (sigma : ℝ) (Q F : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hQ : Continuous Q) (hF : Continuous F) : ℝ → Matrix (Fin N) (Fin N) ℝ :=
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  fun r => FMSA.VolterraBanach.volterraGlobalE sigma Q F hQ hF (max sigma r)

/-- The constructed outer solution is continuous everywhere. -/
theorem matBaxterPsiOuterFun_continuous {N : ℕ} (sigma : ℝ) (Q F : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hQ : Continuous Q) (hF : Continuous F) : Continuous (matBaxterPsiOuterFun sigma Q F hQ hF) := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  exact (FMSA.VolterraBanach.volterraGlobalE_continuousOn_Ici sigma Q F hQ hF).comp_continuous
    (continuous_const.max continuous_id) (fun r => le_max_left sigma r)

/-- On `[σ,∞)` the constructed outer solution satisfies the matrix-product renewal equation. -/
theorem matBaxterPsiOuterFun_renewal {N : ℕ} (sigma : ℝ) (Q F : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hQ : Continuous Q) (hF : Continuous F) :
    letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
    ∀ r : ℝ, sigma ≤ r → matBaxterPsiOuterFun sigma Q F hQ hF r
      = F r + ∫ t in sigma..r, Q (r - t) * matBaxterPsiOuterFun sigma Q F hQ hF t := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  intro r hr
  have hbase := FMSA.VolterraBanach.volterraGlobalE_spec sigma Q F hQ hF hr
  have hself : matBaxterPsiOuterFun sigma Q F hQ hF r
      = FMSA.VolterraBanach.volterraGlobalE sigma Q F hQ hF r := by
    simp only [matBaxterPsiOuterFun, max_eq_right hr]
  rw [hself, hbase]
  congr 1
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hr] at ht
  simp only [matBaxterPsiOuterFun, max_eq_right ht.1]

/-- **`Ψouter` constructed — the matrix outer solution satisfies `MatRenewalEq`.**  For any
continuous matrix Baxter data `Q, F`, the entries of `matBaxterPsiOuterFun` solve the entrywise
species-summed renewal equation.  This discharges the "`Ψouter` is taken as a parameter" gap: the
outer solution is now **built** (Banach global Volterra at the matrix ring) rather than assumed. -/
theorem matBaxterPsiOuter_matRenewalEq {N : ℕ} (sigma : ℝ) (Q F : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hQ : Continuous Q) (hF : Continuous F) :
    MatRenewalEq (fun i j => fun r => (matBaxterPsiOuterFun sigma Q F hQ hF r) i j)
      (fun i j => fun r => (F r) i j) (fun i k => fun s => (Q s) i k) sigma :=
  matRenewalEq_of_matrixProduct (matBaxterPsiOuterFun sigma Q F hQ hF) Q F hQ
    (matBaxterPsiOuterFun_continuous sigma Q F hQ hF)
    (matBaxterPsiOuterFun_renewal sigma Q F hQ hF)

/-! ### Matrix `F[K]=Ĉ` (`OZFIX.18` F-part) — per entry via the general-`c` shell identity

The scalar `baxterK_cos_eq_radial_fourier` (`OZFIX.18` F-part) matches the Fourier transform of the
Baxter shell kernel with the DCF `radial_fourier`. Its matrix form is that identity **per entry**
`(i,j)`, with the general-`c` `shellKernel_cos_eq_radial_fourier` (`ShellKernel.lean`) as the input —
each mixture DCF entry `C₀ᵢⱼ` being a different `c`-shape. The `n = 1` bridge recovers the scalar. -/

/-- **Matrix `F[K]=Ĉ`, entrywise.**  `2∫₀^σ shellKernel(C₀ᵢⱼ)·cos(kv) dv = radial_fourier(C₀ᵢⱼ)(k)`
for `k ≠ 0`, from the general-`c` `shellKernel_cos_eq_radial_fourier`. The Fourier-side factorization
`I − ρĈ` matches `F[ρK]` for the matrix Baxter kernels, per entry. -/
theorem matShellKernel_cos_eq_radial_fourier {N : ℕ} (C : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {sigma : ℝ} (hsigma : 0 < sigma) (i j : Fin N)
    (hc_outer : ∀ s, sigma ≤ s → C i j s = 0)
    (hint : ∀ a b, IntervalIntegrable (fun s : ℝ => s * C i j s) MeasureTheory.volume a b)
    (hccore : ∀ v ∈ Set.Ioo (0 : ℝ) sigma, ContinuousAt (fun s : ℝ => s * C i j s) v)
    (hmeas : ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      StronglyMeasurableAtFilter (fun s : ℝ => s * C i j s) (nhds v))
    {k : ℝ} (hk : k ≠ 0) :
    2 * ∫ v in (0 : ℝ)..sigma, shellKernel (C i j) sigma v * Real.cos (k * v)
      = radial_fourier (C i j) k :=
  shellKernel_cos_eq_radial_fourier hsigma hc_outer hint hccore hmeas hk

/-- **`n = 1` bridge — matrix `F[K]=Ĉ` at one component is the scalar `baxterK_cos_eq_radial_fourier`.** -/
theorem matShellKernel_cos_eq_radial_fourier_fin_one_of_scalar {eta sigma : ℝ} (hsigma : 0 < sigma)
    {k : ℝ} (hk : k ≠ 0) :
    2 * ∫ v in (0 : ℝ)..sigma,
        shellKernel ((fun _ _ => c_HS eta sigma : Matrix (Fin 1) (Fin 1) (ℝ → ℝ)) 0 0) sigma v
          * Real.cos (k * v)
      = radial_fourier ((fun _ _ => c_HS eta sigma : Matrix (Fin 1) (Fin 1) (ℝ → ℝ)) 0 0) k := by
  show 2 * ∫ v in (0 : ℝ)..sigma, shellKernel (c_HS eta sigma) sigma v * Real.cos (k * v)
      = radial_fourier (c_HS eta sigma) k
  simp only [shellKernel_c_HS]
  exact baxterK_cos_eq_radial_fourier hsigma hk

/-! ### Matrix 2D reindex (`OZFIX.20`) — the double-convolution associativity, two-function form -/

/-- **Matrix 2D reindex (`OZFIX.20`).**  Summing the two-function reindex over the intermediate
species `k`: the matrix double convolution `∑ₖ (Qᵢₖ ⋆ Qⱼₖ) ⋆ ψ` collapses to the matrix
self-kernel `matSelfConv` in the two asymmetric weights.  The kernels are `matSelfConv Q σ u i j`
(weighting `ψ(r+u)`) and its transpose `matSelfConv Q σ u j i` (weighting `ψ(r−u)`). -/
theorem matDblConv_reindex {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (psi : ℝ → ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma) (r : ℝ) (i j : Fin N)
    (hswapP : ∀ k, MeasureTheory.Integrable
      (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => Q i k t * Q j k (t - u) * psi (r + u)) t)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hswapM : ∀ k, MeasureTheory.Integrable
      (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => Q j k t * Q i k (t - u) * psi (r - u)) t)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hswapA : ∀ k, MeasureTheory.Integrable
      (Function.uncurry fun t s => (Set.Ioi t).indicator
        (fun s => Q i k t * Q j k s * psi (r + t - s)) s)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hsliceLa : ∀ k (t : ℝ), IntervalIntegrable (fun s => Q i k t * Q j k s * psi (r + t - s))
      MeasureTheory.volume 0 t)
    (hsliceRa : ∀ k (t : ℝ), IntervalIntegrable (fun s => Q i k t * Q j k s * psi (r + t - s))
      MeasureTheory.volume t sigma)
    (haddI : ∀ k, IntervalIntegrable (fun t => ∫ s in (0:ℝ)..t, Q i k t * Q j k s * psi (r + t - s))
      MeasureTheory.volume 0 sigma)
    (haddII : ∀ k, IntervalIntegrable (fun t => ∫ s in t..sigma, Q i k t * Q j k s * psi (r + t - s))
      MeasureTheory.volume 0 sigma)
    (haddRp : ∀ k, IntervalIntegrable
      (fun u => (∫ t in u..sigma, Q i k t * Q j k (t - u)) * psi (r + u))
      MeasureTheory.volume 0 sigma)
    (haddRm : ∀ k, IntervalIntegrable
      (fun u => (∫ t in u..sigma, Q j k t * Q i k (t - u)) * psi (r - u))
      MeasureTheory.volume 0 sigma) :
    (∑ k, ∫ t in (0:ℝ)..sigma, Q i k t * ∫ s in (0:ℝ)..sigma, Q j k s * psi (r + t - s))
      = ∫ u in (0:ℝ)..sigma,
          (matSelfConv Q sigma u i j * psi (r + u) + matSelfConv Q sigma u j i * psi (r - u)) := by
  have hper : ∀ k, (∫ t in (0:ℝ)..sigma, Q i k t * ∫ s in (0:ℝ)..sigma, Q j k s * psi (r + t - s))
      = ∫ u in (0:ℝ)..sigma, ((∫ t in u..sigma, Q i k t * Q j k (t - u)) * psi (r + u)
          + (∫ t in u..sigma, Q j k t * Q i k (t - u)) * psi (r - u)) := fun k =>
    dbl_conv_reindex_two hsigma (Q i k) (Q j k) psi r (hswapP k) (hswapM k) (hswapA k)
      (hsliceLa k) (hsliceRa k) (haddI k) (haddII k) (haddRp k) (haddRm k)
  calc (∑ k, ∫ t in (0:ℝ)..sigma, Q i k t * ∫ s in (0:ℝ)..sigma, Q j k s * psi (r + t - s))
      = ∑ k, ∫ u in (0:ℝ)..sigma, ((∫ t in u..sigma, Q i k t * Q j k (t - u)) * psi (r + u)
          + (∫ t in u..sigma, Q j k t * Q i k (t - u)) * psi (r - u)) :=
        Finset.sum_congr rfl (fun k _ => hper k)
    _ = ∫ u in (0:ℝ)..sigma, ∑ k, ((∫ t in u..sigma, Q i k t * Q j k (t - u)) * psi (r + u)
          + (∫ t in u..sigma, Q j k t * Q i k (t - u)) * psi (r - u)) :=
        (intervalIntegral.integral_finsetSum (fun k _ => (haddRp k).add (haddRm k))).symm
    _ = ∫ u in (0:ℝ)..sigma,
          (matSelfConv Q sigma u i j * psi (r + u) + matSelfConv Q sigma u j i * psi (r - u)) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        rfl

/-- **`n = 1` bridge — matrix 2D reindex at `Fin 1` is the scalar two-function reindex (`q0a=q0b`).** -/
theorem matDblConv_reindex_fin_one {q0 psi : ℝ → ℝ} {sigma : ℝ} (hsigma : 0 < sigma) (r : ℝ)
    (Q : Matrix (Fin 1) (Fin 1) (ℝ → ℝ)) (hQ : Q 0 0 = q0)
    (hswapP : MeasureTheory.Integrable
      (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => q0 t * q0 (t - u) * psi (r + u)) t)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hswapM : MeasureTheory.Integrable
      (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => q0 t * q0 (t - u) * psi (r - u)) t)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hswapA : MeasureTheory.Integrable
      (Function.uncurry fun t s => (Set.Ioi t).indicator
        (fun s => q0 t * q0 s * psi (r + t - s)) s)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hsliceLa : ∀ t : ℝ, IntervalIntegrable (fun s => q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume 0 t)
    (hsliceRa : ∀ t : ℝ, IntervalIntegrable (fun s => q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume t sigma)
    (haddI : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..t, q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume 0 sigma)
    (haddII : IntervalIntegrable (fun t => ∫ s in t..sigma, q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume 0 sigma)
    (haddR : IntervalIntegrable
      (fun u => (∫ t in u..sigma, q0 t * q0 (t - u)) * psi (r + u))
      MeasureTheory.volume 0 sigma)
    (haddR' : IntervalIntegrable
      (fun u => (∫ t in u..sigma, q0 t * q0 (t - u)) * psi (r - u))
      MeasureTheory.volume 0 sigma) :
    (∑ k, ∫ t in (0:ℝ)..sigma, Q 0 k t * ∫ s in (0:ℝ)..sigma, Q 0 k s * psi (r + t - s))
      = ∫ u in (0:ℝ)..sigma,
          (matSelfConv Q sigma u 0 0 * psi (r + u) + matSelfConv Q sigma u 0 0 * psi (r - u)) := by
  subst hQ
  exact matDblConv_reindex Q psi hsigma r 0 0
    (fun k => by fin_cases k; exact hswapP) (fun k => by fin_cases k; exact hswapM)
    (fun k => by fin_cases k; exact hswapA) (fun k => by fin_cases k; exact hsliceLa)
    (fun k => by fin_cases k; exact hsliceRa) (fun k => by fin_cases k; exact haddI)
    (fun k => by fin_cases k; exact haddII) (fun k => by fin_cases k; exact haddR)
    (fun k => by fin_cases k; exact haddR')

/-! ### Matrix OZ★ assembly (`OZFIX.15/19/20` combined) — `MatOZStar` from renewal + KDEF + bridge -/

/-- **claimB, KDEF split.**  Substituting the matrix factorization `ρ·Kᵢₖ = Qᵢₖ − matSelfConv(i,k)`
(a.e. on the open core) into `ρ·matShellConv` splits it into the linear `Q`-shell minus the
self-convolution shell — the matrix analog of the scalar `hsplitB`/`hFirst` step. -/
theorem matShellConv_kdef_split {N : ℕ} (Kmat Q G : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {rho sigma r : ℝ} (hsigma : 0 < sigma) (i j : Fin N)
    (hfact : MatBaxterFactorization Kmat Q rho sigma)
    (hQint : ∀ k, IntervalIntegrable
      (fun u => Q i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)))
      MeasureTheory.volume 0 sigma)
    (hSint : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u i k * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)))
      MeasureTheory.volume 0 sigma) :
    rho * matShellConv Kmat G sigma r i j
      = (∑ k, ∫ u in (0:ℝ)..sigma,
            Q i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)))
        - ∑ k, ∫ u in (0:ℝ)..sigma,
            matSelfConv Q sigma u i k * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)) := by
  rw [matShellConv_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hQint k) (hSint k)]
  have hne : ∀ᵐ (x : ℝ), x ≠ sigma := by
    rw [MeasureTheory.ae_iff]; simp [MeasureTheory.measure_singleton]
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hsigma.le]
  filter_upwards [hne] with u hune hmem
  have hu : u ∈ Set.Ioo (0:ℝ) sigma := ⟨hmem.1, lt_of_le_of_ne hmem.2 hune⟩
  show rho * (Kmat i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)))
      = Q i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u))
        - matSelfConv Q sigma u i k * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u))
  rw [show rho * (Kmat i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)))
      = (rho * Kmat i k u) * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)) by ring,
    hfact i k u hu]
  ring

/-- **Matrix OZ★, assembled (`OZFIX.15/19/20` combined).**  From the matrix renewal identity in
shell form (`hclaimA`, the `OZFIX.15` analog of `baxter_psi_conv_eq_phi`), the shell-conv bridge
(`hbridge`, `OZFIX.19` = `matRadialConv_eq_matShellConv`), the factorization (`hfact`, KDEF), and
the shell integrability, the matrix real-space Ornstein–Zernike identity `MatOZStar` holds.  Mirrors
the scalar `baxterPsi_eq_phi_add_rho_conv`: `claimA` (renewal) supplies `Ψ − r·Φ`, and `ρ·matShellConv`
(bridge + KDEF split) supplies the same shell expression. -/
theorem matOzStar_of_shellClaims {N : ℕ} (Psi Phi Kmat Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {rho sigma : ℝ} (hsigma : 0 < sigma)
    (hfact : MatBaxterFactorization Kmat Q rho sigma)
    (hbridge : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
        = matShellConv Kmat (fun k l => fun x => Psi k l x / x) sigma r i j)
    (hQint : ∀ (i j : Fin N) (r : ℝ), 0 < r → ∀ k, IntervalIntegrable
      (fun u => Q i k u * (oddExt (fun x => Psi k j x / x) (r - u)
        + oddExt (fun x => Psi k j x / x) (r + u))) MeasureTheory.volume 0 sigma)
    (hSint : ∀ (i j : Fin N) (r : ℝ), 0 < r → ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u i k * (oddExt (fun x => Psi k j x / x) (r - u)
        + oddExt (fun x => Psi k j x / x) (r + u))) MeasureTheory.volume 0 sigma)
    (hclaimA : ∀ (i j : Fin N) (r : ℝ), 0 < r → Psi i j r = r * Phi i j r
        + ((∑ k, ∫ u in (0:ℝ)..sigma, Q i k u
              * (oddExt (fun x => Psi k j x / x) (r - u) + oddExt (fun x => Psi k j x / x) (r + u)))
          - ∑ k, ∫ u in (0:ℝ)..sigma, matSelfConv Q sigma u i k
              * (oddExt (fun x => Psi k j x / x) (r - u) + oddExt (fun x => Psi k j x / x) (r + u)))) :
    MatOZStar Psi Phi rho := by
  intro i j r hr
  rw [hclaimA i j r hr]
  congr 1
  rw [hbridge i j r hr,
    matShellConv_kdef_split Kmat Q (fun k l => fun x => Psi k l x / x) hsigma i j hfact
      (hQint i j r hr) (hSint i j r hr)]

end

end FMSA.MixtureOzStar
