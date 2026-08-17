/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MixtureDCFAEInjective
import LeanCode.HSMixture.MixtureNoSpinodalN1
import LeanCode.HSMixture.HSMixWindowing
import LeanCode.HSMixture.HSMixWindowingBridge
import LeanCode.HSMixture.PhysHSMixWindowing

/-!
# N=1 consistency of the mixture HS DCF with the scalar `c_HS`

The zeroth-order construction in `MixtureHSDCF` builds `cHSmixRaw = qFwd + pMixEntry − ∑ qpConv`
(the real-space image of `Cmix0 = I − Q̂₀Q̂₀ᵀ`) and its odd part `cHSodd`.  That odd extraction is
**degenerate on the diagonal** — `cHSmixRaw X i i` is even, so `cHSodd X i i ≡ 0`
(`MixtureHSDCF.cHSodd_diag_eq_zero`), hence the `cHSodd`-based `c_HS_mix X i i ≡ 0`.  It therefore
does NOT reduce to the (nonzero, even) scalar `c_HS` at one component.

This file records the **corrected** N=1 statement.  The physical DCF `c^HS(r)` is even, and the
object the OZ★/Baxter route actually uses is the odd `S(r) = r·c^HS(r)`, given by the Baxter
*derivative* form (`HardSphere.baxter_factorization_inner`):
`2πρ r c_HS = ∫_r^σ q0_poly(r'−r)·q0_poly'(r') − q0_poly'(r)` (the shell-kernel inverse of
`cHSmixRaw`, carrying `q0_poly'` and a boundary term).  At `N=1` the physical Lebowitz coefficients
of `physMixN` collapse to the scalar PY values (`Q0phys_n1`/`Qppphys_n1`) so
`ρ₀·q0MixEntry(physMixN) 0 0 = q0_poly` on the core, and the identity evaluates to `2πρ₀ r c_HS`.

So the mixture kernel *does* reproduce the scalar `c_HS` at one component — through the derivative
form, not the odd extraction.
-/

set_option linter.style.longLine false

open MeasureTheory Set
open FMSA.InnerDecomp FMSA.WHSupports FMSA.MatrixQ0 FMSA.HardSphere FMSA.MixtureOzStar
open FMSA.MixtureBaxter
open FMSA.MixtureNoSpinodalN1

namespace FMSA.MixtureHSDCFFin1

/-- **N=1 kernel reduction** — on the core `[0,σ₀]`, `ρ₀·q0MixEntry(physMixN) 0 0 = q0_poly`.  The
physical Lebowitz coefficients collapse to the scalar PY `q_prime_py`/`q_doubleprime_py` via
`Q0phys_n1`/`Qppphys_n1`; the extra `ρ₀` is the density that `q0_poly` carries and `q0MixEntry` does
not (`Q0phys` at one component is `q_prime_py`, *without* a `ρ₀` factor). -/
theorem q0MixEntry_physMixN_fin1_core (rho sigma : Fin 1 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (heta : etaMix rho sigma ≠ 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (sigma 0)) :
    rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u
      = q0_poly (etaMix rho sigma) (sigma 0) (rho 0) u := by
  obtain ⟨hu0, husigC⟩ := hu
  set X := physMixN rho sigma hsig with hX
  have hR : X.R 0 0 = sigma 0 := by simp only [hX, physMixN, Mix.R]; ring
  have hlam : X.lam 0 0 = 0 := by simp only [hX, physMixN, Mix.lam]; ring
  have hmem : u ∈ Set.Icc (X.lam 0 0) (X.R 0 0) := by
    rw [hlam, hR]; exact Set.mem_Icc.mpr ⟨hu0, husigC⟩
  have hQ0 : X.Q0 0 0 = q_prime_py (etaMix rho sigma) (sigma 0) := Q0phys_n1 (hsig 0) heta
  have hQpp : X.Qpp 0 = q_doubleprime_py (etaMix rho sigma) := Qppphys_n1 (hsig 0) heta
  unfold q0MixEntry
  rw [Set.indicator_of_mem hmem, hR, hQ0, hQpp, q0_poly_inner husigC]
  ring

/-- **⭐ N=1 consistency (CORRECTED) — the true `r·c^HS` at one component is `2π·ρ₀·r·c_HS`.**  The
correct real-space DCF is the Baxter *derivative* form (`baxter_factorization_inner`), NOT the
degenerate odd part `cHSodd` (`MixtureHSDCF.cHSodd_diag_eq_zero`).  At `N=1`, with `η = π ρ₀ σ₀³/6`
(`etaMix_n1`), it evaluates to the scalar PY DCF `c_HS`; its `q0_poly` kernel is
`ρ₀·q0MixEntry(physMixN) 0 0` on the core (`q0MixEntry_physMixN_fin1_core`).  The physical mixture
kernel therefore reproduces `c_HS` at one component — through the derivative form. -/
theorem rcHS_physMixN_fin1 (rho sigma : Fin 1 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (heta0 : 0 ≤ etaMix rho sigma) (heta1 : etaMix rho sigma < 1) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (sigma 0)) :
    2 * Real.pi * rho 0 * r * c_HS (etaMix rho sigma) (sigma 0) r
      = (∫ r' in r..(sigma 0), q0_poly (etaMix rho sigma) (sigma 0) (rho 0) (r' - r)
            * (rho 0 * q_prime_py (etaMix rho sigma) (sigma 0)
                + rho 0 * q_doubleprime_py (etaMix rho sigma) * (r' - sigma 0)))
        - (rho 0 * q_prime_py (etaMix rho sigma) (sigma 0)
            + rho 0 * q_doubleprime_py (etaMix rho sigma) * (r - sigma 0)) :=
  baxter_factorization_inner (hsig 0) heta0 heta1 (etaMix_n1 rho sigma) r hr

/-! ### Core derivative of the Baxter kernel (building block for the derivative form) -/

/-- **Core derivative of the Baxter kernel** `q0MixDeriv X i j r = Q0ᵢⱼ + Qppⱼ·(r − Rᵢⱼ)` — the
`r`-derivative of `q0MixEntry`'s quadratic on the open core `(λᵢⱼ, Rᵢⱼ)`.  It is the mixture analog
of the scalar `q0_poly'` that `baxter_factorization_inner` carries. -/
noncomputable def q0MixDeriv {N M : ℕ} (X : Mix N M) (i j : Fin N) (r : ℝ) : ℝ :=
  X.Q0 i j + X.Qpp j * (r - X.R i j)

/-- **FTC building block** — on the open core `(λᵢⱼ, Rᵢⱼ)`, `q0MixEntry` is differentiable with
derivative `q0MixDeriv` (the indicator is `= 1` on the open core, so the derivative is the
quadratic's derivative `Q0ᵢⱼ + Qppⱼ·(r − Rᵢⱼ)`). -/
theorem hasDerivAt_q0MixEntry {N M : ℕ} (X : Mix N M) (i j : Fin N) {r : ℝ}
    (hr : r ∈ Set.Ioo (X.lam i j) (X.R i j)) :
    HasDerivAt (q0MixEntry X i j) (q0MixDeriv X i j r) r := by
  have hsub : HasDerivAt (fun s => s - X.R i j) (1 : ℝ) r := (hasDerivAt_id r).sub_const _
  have h1 : HasDerivAt (fun s => X.Q0 i j * (s - X.R i j)) (X.Q0 i j * 1) r :=
    hsub.const_mul (X.Q0 i j)
  have hsq : HasDerivAt (fun s => (s - X.R i j) ^ 2) (2 * (r - X.R i j) ^ 1 * 1) r := hsub.pow 2
  have h2 : HasDerivAt (fun s => X.Qpp j * (s - X.R i j) ^ 2 / 2)
      (X.Qpp j * (2 * (r - X.R i j) ^ 1 * 1) / 2) r := (hsq.const_mul (X.Qpp j)).div_const 2
  have hpoly : HasDerivAt (fun s => X.Q0 i j * (s - X.R i j) + X.Qpp j * (s - X.R i j) ^ 2 / 2)
      (q0MixDeriv X i j r) r := by
    have hd := h1.add h2
    have heq : X.Q0 i j * 1 + X.Qpp j * (2 * (r - X.R i j) ^ 1 * 1) / 2 = q0MixDeriv X i j r := by
      simp only [q0MixDeriv]; ring
    rwa [heq] at hd
  refine hpoly.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
  unfold q0MixEntry
  rw [Set.indicator_of_mem (Set.Ioo_subset_Icc_self hs)]

/-! ### Unequal diameters — the correct SYMMETRIC `matDCFreCore`-derivative IS the physical DCF

⚠ **CORRECTED 2026-08-13** (`mixdcf_unequal_value_check.py`).  An earlier note here claimed the
`q0`-only Baxter-derivative form is "5–13% off, needs the renewal `Ψ`".  That was an artifact of an
**asymmetric** naive formula (`2π r c_ij = −q0MixDeriv_ij + ∑ₗ ρₗ ∫ q0MixEntry_il(r'−r)·q0MixDeriv_lj`)
which drops the **reflected** linear term `q0(j,i)(−v)` and mis-weights — it fails `c_ij = c_ji`.

The CORRECT object is the full **symmetric** fold kernel `matDCFreCore = Re matDCFfull`
(a.e.-symmetric, `matDCFreCore_ae_symm`):
`matDCFreCore_ij(v) = rg_ij q0(i,j)(v) + rg_ji q0(j,i)(−v) − ∑ₘ rg_im rg_jm ∫ q0(i,m)(t) q0(j,m)(t−v)`
(BOTH linear terms).  Its shell-inverse / derivative form `c_ij = −matDCFreCore_ij'/(2π rg_ij v)` IS
the true PY-HS mixture DCF at **unequal** diameters — verified decisively: (i) equal-σ control
reproduces the analytic scalar `c_HS(η_tot)`; (ii) the **hard-core test** `g_ij(r<σ_ij)=0` (defining
property of the true DCF) passes to `<1.2%` (= the equal-σ transform-noise baseline), while a
sensitivity sweep shows a mere 5%-scaled `c` already gives `g ~ 0.03–0.05`.  So **no renewal `Ψ` is
needed** — the equal-σ value proof (`MixtureBaxterODEEqualDiam.shellForcing_eq_cHS_equalDiam`)
generalizes to unequal σ via `matDCFreCore`.

Concretely, the **mixture Baxter ODE** `matDCFreCore_ij'(s) = −2π rg_ij s c_ij(s)` holds at unequal
σ with the physical **two-piece** Lebowitz `c_ij` (a knot at `λ_ij`: reflected quadratic on `(0,λ_ij)`,
forward on `(λ_ij, R_ij)`, correlation throughout).  The Lean value capstone at unequal σ is therefore
the two-piece analog of `baxterODE_n1` (this file's `q0MixDeriv` / `hasDerivAt_q0MixEntry` and
`MixtureHSDCF.qpConv_contDiffOn_upper`/`_lower` are the FTC building blocks). -/

/-! ### N=1 physical reduction of the renewal-seed mixture DCF `cHSmixRenewal` -/

/-- **⭐ N=1 physical reduction of the renewal-seed mixture DCF.**  For the physical one-component
mixture `physMixN` (Baxter factor `Q i j = ρ₀·q0MixEntry(physMixN) 0 0`, whose row-sum is the scalar
PY `q0_poly` on the core, `q0MixEntry_physMixN_fin1_core`) and ANY renewal solution `Psi` satisfying
the standard outer/core hypotheses, `cHSmixRenewal` collapses to the scalar `c_HS`.  The Q-side
hypotheses of `cHSmixRenewal_eq_cHS_of_equalDiam` (support, symmetry, row-sum, integrability) are
all discharged from the physical `q0MixEntry`; only the renewal `Psi` conditions remain (the OZ
solution, which the project builds via `matBaxterPsi` and routes around via `matOzStar_unique`). -/
theorem cHSmixRenewal_physMixN_fin1 (rho sigma : Fin 1 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (heta1 : etaMix rho sigma < 1)
    (Psi : Matrix (Fin 1) (Fin 1) (ℝ → ℝ))
    (hUouter : ∀ i j r, sigma 0 ≤ r →
      matBaxterU Psi (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u)
        (sigma 0) i j r = 0)
    (hint : ∀ (i j k : Fin 1) (r : ℝ), IntervalIntegrable
      (fun t => (rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 t)
        * matBaxterU Psi (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u)
            (sigma 0) k j (r + t)) volume 0 (sigma 0))
    (hcore : ∀ (k j : Fin 1) (v : ℝ), v ∈ Set.Ioo (-(sigma 0)) (sigma 0) → Psi k j v = -v)
    {r : ℝ} (hr : 0 < r) (i j : Fin 1) :
    cHSmixRenewal Psi (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u) i j r
      = c_HS (etaMix rho sigma) (sigma 0) r := by
  set X := physMixN rho sigma hsig with hX
  set Q : Matrix (Fin 1) (Fin 1) (ℝ → ℝ) :=
    fun _ _ u => rho 0 * q0MixEntry X 0 0 u with hQ
  have heta_ne : etaMix rho sigma ≠ 1 := ne_of_lt heta1
  have hlam : X.lam 0 0 = 0 := by simp only [hX, physMixN, Mix.lam]; ring
  have hR : X.R 0 0 = sigma 0 := by simp only [hX, physMixN, Mix.R]; ring
  refine cHSmixRenewal_eq_cHS_of_equalDiam Psi Q (eta := etaMix rho sigma) (sigma := sigma 0)
    (rho := rho 0) (hsig 0) heta1 (etaMix_n1 rho sigma) ?_ ?_ hUouter hint ?_ ?_ ?_ hcore hr i j
  · intro a k t ht
    simp only [hQ]
    have hnm : t ∉ Set.Icc (X.lam 0 0) (X.R 0 0) := by
      rw [hlam, hR]
      intro hc
      rw [Set.mem_Icc] at hc
      rcases ht with h | h
      · exact absurd hc.1 (not_le.mpr h)
      · exact absurd hc.2 (not_le.mpr h)
    rw [Function.notMem_support.mp (fun hs => hnm (q0MixEntry_support_subset X 0 0 hs)),
      mul_zero]
  · intro a b; rfl
  · intro a u hu
    simp only [hQ, Fin.sum_univ_one]
    exact q0MixEntry_physMixN_fin1_core rho sigma hsig heta_ne hu
  · intro a k
    exact (q0MixEntry_intervalIntegrable X 0 0 0 (sigma 0)).const_mul (rho 0)
  · intro a k
    refine ((q0MixEntry_mul_id_intervalIntegrable X 0 0 0 (sigma 0)).const_mul (rho 0)).congr ?_
    intro x _
    simp only [hQ]; ring

/-- **N=1 physical reduction with `hcore` CONSTRUCTED.**  Instantiating the renewal solution as the
glued `matBaxterPsi Ψouter (−v) σ₀` (physical core `Ψcore = −v`), the `hcore` hypothesis of
`cHSmixRenewal_physMixN_fin1` is discharged outright by `matBaxterPsi_core` (definitional core
branch).  So the physical N=1 reduction now needs ONLY the two renewal-equation conditions on the
outer solution `Ψouter` (`hUouter`, `hint`) — the core is no longer a free assumption. -/
theorem cHSmixRenewal_physMixN_fin1_ofOuter (rho sigma : Fin 1 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (heta1 : etaMix rho sigma < 1)
    (Psiouter : Matrix (Fin 1) (Fin 1) (ℝ → ℝ))
    (hUouter : ∀ i j r, sigma 0 ≤ r →
      matBaxterU (matBaxterPsi Psiouter (fun _ _ v => -v) (sigma 0))
        (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u) (sigma 0) i j r = 0)
    (hint : ∀ (i j k : Fin 1) (r : ℝ), IntervalIntegrable
      (fun t => (rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 t)
        * matBaxterU (matBaxterPsi Psiouter (fun _ _ v => -v) (sigma 0))
            (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u)
            (sigma 0) k j (r + t)) volume 0 (sigma 0))
    {r : ℝ} (hr : 0 < r) (i j : Fin 1) :
    cHSmixRenewal (matBaxterPsi Psiouter (fun _ _ v => -v) (sigma 0))
        (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u) i j r
      = c_HS (etaMix rho sigma) (sigma 0) r := by
  refine cHSmixRenewal_physMixN_fin1 rho sigma hsig heta1
    (matBaxterPsi Psiouter (fun _ _ v => -v) (sigma 0)) hUouter hint ?_ hr i j
  intro k j' v hv
  exact matBaxterPsi_core Psiouter (fun _ _ w => -w) k j' hv

/-! ### Constructing `Ψouter` for `hUouter` — the Banach–Volterra renewal solution -/

/-- Physical N=1 continuous Baxter kernel matrix: the `1×1` `q0_poly` (the renewal is built from the
CONTINUOUS `q0_poly`, which agrees with the truncated `q0MixEntry` on `[0,σ]`). -/
noncomputable def physN1Qm (rho sigma : Fin 1 → ℝ) : ℝ → Matrix (Fin 1) (Fin 1) ℝ :=
  fun r => Matrix.of (fun _ _ => q0_poly (etaMix rho sigma) (sigma 0) (rho 0) r)

/-- Physical N=1 core-convolution forcing matrix: the `1×1` `baxterForcing`. -/
noncomputable def physN1Fm (rho sigma : Fin 1 → ℝ) : ℝ → Matrix (Fin 1) (Fin 1) ℝ :=
  fun r => Matrix.of (fun _ _ => baxterForcing (etaMix rho sigma) (sigma 0) (rho 0) r)

theorem physN1Qm_continuous (rho sigma : Fin 1 → ℝ) : Continuous (physN1Qm rho sigma) :=
  continuous_matrix (fun _ _ => by
    simp only [physN1Qm, Matrix.of_apply]
    exact q0_poly_continuous (etaMix rho sigma) (sigma 0) (rho 0))

theorem physN1Fm_continuous (rho sigma : Fin 1 → ℝ) : Continuous (physN1Fm rho sigma) :=
  continuous_matrix (fun _ _ => by
    simp only [physN1Fm, Matrix.of_apply]
    exact baxterForcing_continuous (etaMix rho sigma) (sigma 0) (rho 0))

/-- **⭐ `hUouter` for the CONSTRUCTED renewal `Ψouter`.**  Instantiating `Ψouter` as the
Banach–Volterra solution `matBaxterPsiOuterFun σ₀ (q0_poly-matrix) (baxterForcing-matrix)`, the
outer-vanishing `matBaxterU = 0` on `[σ₀,∞)` holds for the physical truncated Baxter factor.
`matBaxterPsi_hUouter` gives it for the continuous `q0_poly` kernel (`hQsupp` =
`q0_poly_eq_zero_of_ge`, `hforcing` = `baxterForcing` def); a kernel bridge carries it to the
truncated `ρ₀·q0MixEntry`, which equals `q0_poly` on `[0,σ₀]`
(`q0MixEntry_physMixN_fin1_core`) — all `matBaxterU` samples. -/
theorem physN1_hUouter (rho sigma : Fin 1 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (heta1 : etaMix rho sigma < 1) (i j : Fin 1) {r : ℝ} (hr : sigma 0 ≤ r) :
    matBaxterU
      (matBaxterPsi (fun a b r => (matBaxterPsiOuterFun (sigma 0) (physN1Qm rho sigma)
          (physN1Fm rho sigma) (physN1Qm_continuous rho sigma)
          (physN1Fm_continuous rho sigma) r) a b)
        (fun _ _ v => -v) (sigma 0))
      (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u) (sigma 0) i j r = 0 := by
  have heta_ne : etaMix rho sigma ≠ 1 := ne_of_lt heta1
  have hkey := matBaxterPsi_hUouter (sigma 0) (hsig 0) (physN1Qm rho sigma) (physN1Fm rho sigma)
    (physN1Qm_continuous rho sigma) (physN1Fm_continuous rho sigma)
    (fun v hv a b => by simp only [physN1Qm, Matrix.of_apply]; exact q0_poly_eq_zero_of_ge hv)
    (fun a b r' hr' => by
      simp only [physN1Fm, physN1Qm, Matrix.of_apply, Fin.sum_univ_one, baxterForcing])
    i j hr
  rw [← hkey]
  unfold matBaxterU
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le (le_of_lt (hsig 0))] at ht
  congr 1
  simp only [physN1Qm, Matrix.of_apply]
  exact q0MixEntry_physMixN_fin1_core rho sigma hsig heta_ne ht

/-- **Kernel bridge for `matBaxterU`.**  `matBaxterU` only samples its kernel via `∫₀^σ`, so two
kernels agreeing on `[0,σ]` give the same `matBaxterU`. -/
theorem matBaxterU_kernel_congr {N : ℕ} (Psi Q1 Q2 : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (h : ∀ a b t, t ∈ Set.uIcc (0:ℝ) sigma → Q1 a b t = Q2 a b t) (i j : Fin N) (r : ℝ) :
    matBaxterU Psi Q1 sigma i j r = matBaxterU Psi Q2 sigma i j r := by
  unfold matBaxterU
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [h i k t ht]

/-- **⭐ `hint` for the CONSTRUCTED renewal `Ψouter`.**  Interval-integrability of the seed integrand
for the physical truncated Baxter factor, with `Ψ = matBaxterPsi (Banach–Volterra Ψouter) (−v) σ₀`.
`matBaxterPsi_hint` gives it for the continuous `q0_poly` kernel; the kernel bridge + `q0MixEntry =
q0_poly` on `[0,σ₀]` carries it to the truncated `ρ₀·q0MixEntry`. -/
theorem physN1_hint (rho sigma : Fin 1 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (heta1 : etaMix rho sigma < 1) (i k j : Fin 1) (r : ℝ) :
    IntervalIntegrable
      (fun t => (rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 t)
        * matBaxterU (matBaxterPsi (fun a b r => (matBaxterPsiOuterFun (sigma 0)
              (physN1Qm rho sigma) (physN1Fm rho sigma) (physN1Qm_continuous rho sigma)
              (physN1Fm_continuous rho sigma) r) a b)
            (fun _ _ v => -v) (sigma 0))
          (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u)
          (sigma 0) k j (r + t)) volume 0 (sigma 0) := by
  have heta_ne : etaMix rho sigma ≠ 1 := ne_of_lt heta1
  have hbridge : ∀ (a b : Fin 1) (t : ℝ), t ∈ Set.uIcc (0:ℝ) (sigma 0) →
      (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u : Matrix _ _ _) a b t
        = (fun a b s => (physN1Qm rho sigma s) a b : Matrix _ _ _) a b t := by
    intro a b t ht
    rw [Set.uIcc_of_le (le_of_lt (hsig 0))] at ht
    simp only [physN1Qm, Matrix.of_apply]
    exact q0MixEntry_physMixN_fin1_core rho sigma hsig heta_ne ht
  have hkey := matBaxterPsi_hint (sigma 0) (le_of_lt (hsig 0)) (physN1Qm rho sigma)
    (physN1Fm rho sigma) (physN1Qm_continuous rho sigma) (physN1Fm_continuous rho sigma) i k j r
  refine hkey.congr (fun t ht => ?_)
  congr 1
  · exact (hbridge i k t (Set.uIoc_subset_uIcc ht)).symm
  · exact (matBaxterU_kernel_congr _ _ _ (sigma 0) hbridge k j (r + t)).symm

/-- **⭐⭐ UNCONDITIONAL N=1 physical reduction.**  With `Ψ` the fully-constructed glued renewal
solution `matBaxterPsi (Banach–Volterra Ψouter) (−v) σ₀`, ALL three renewal hypotheses are
discharged (`hcore` = `matBaxterPsi_core`, `hUouter` = `physN1_hUouter`, `hint` = `physN1_hint`), so
the physical one-component renewal-seed mixture DCF equals the scalar `c_HS` with NO remaining
assumptions on `Ψ`. -/
theorem cHSmixRenewal_physMixN_fin1_uncond (rho sigma : Fin 1 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (heta1 : etaMix rho sigma < 1) {r : ℝ} (hr : 0 < r) (i j : Fin 1) :
    cHSmixRenewal
        (matBaxterPsi (fun a b r => (matBaxterPsiOuterFun (sigma 0) (physN1Qm rho sigma)
            (physN1Fm rho sigma) (physN1Qm_continuous rho sigma)
            (physN1Fm_continuous rho sigma) r) a b)
          (fun _ _ v => -v) (sigma 0))
        (fun _ _ u => rho 0 * q0MixEntry (physMixN rho sigma hsig) 0 0 u) i j r
      = c_HS (etaMix rho sigma) (sigma 0) r :=
  cHSmixRenewal_physMixN_fin1_ofOuter rho sigma hsig heta1
    (fun a b r => (matBaxterPsiOuterFun (sigma 0) (physN1Qm rho sigma) (physN1Fm rho sigma)
      (physN1Qm_continuous rho sigma) (physN1Fm_continuous rho sigma) r) a b)
    (fun i' j' r' hr' => physN1_hUouter rho sigma hsig heta1 i' j' hr')
    (fun i' j' k' r' => physN1_hint rho sigma hsig heta1 i' k' j' r')
    hr i j

/-! ### N=2 unequal diameters — `hUouter`/`hint` for the constructed renewal (continuous kernel) -/

/-- **Continuous mixture Baxter polynomial** — the `q0MixEntry` quadratic clamped by `min r Rᵢⱼ`
(continuous everywhere: at `Rᵢⱼ` the quadratic vanishes; agrees with `q0MixEntry` on `[λᵢⱼ,Rᵢⱼ]`,
and extends the polynomial continuously below `λᵢⱼ` — the continuous kernel Banach–Volterra
needs). -/
noncomputable def q0MixPoly {N M : ℕ} (X : Mix N M) (i j : Fin N) (r : ℝ) : ℝ :=
  X.Q0 i j * (min r (X.R i j) - X.R i j)
    + X.Qpp j * (min r (X.R i j) - X.R i j) ^ 2 / 2

theorem q0MixPoly_continuous {N M : ℕ} (X : Mix N M) (i j : Fin N) :
    Continuous (q0MixPoly X i j) := by
  unfold q0MixPoly; fun_prop

/-- `q0MixPoly X i j r = 0` for `r ≥ Rᵢⱼ` (the clamp freezes at `Rᵢⱼ`, quadratic `= 0` there). -/
theorem q0MixPoly_eq_zero_of_ge {N M : ℕ} (X : Mix N M) (i j : Fin N) {r : ℝ} (hr : X.R i j ≤ r) :
    q0MixPoly X i j r = 0 := by
  simp only [q0MixPoly, min_eq_right hr, sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, add_zero]

/-- The `q0MixPoly` matrix kernel `Qm r := (q0MixPoly X i j r)ᵢⱼ`. -/
noncomputable def q0MixPolyMat {N M : ℕ} (X : Mix N M) : ℝ → Matrix (Fin N) (Fin N) ℝ :=
  fun r => Matrix.of (fun i j => q0MixPoly X i j r)

theorem q0MixPolyMat_continuous {N M : ℕ} (X : Mix N M) : Continuous (q0MixPolyMat X) :=
  continuous_matrix (fun i j => by
    simp only [q0MixPolyMat, Matrix.of_apply]; exact q0MixPoly_continuous X i j)

-- `matForcingCore` / `matForcingCore_continuous` are generic Matrix machinery; moved to the
-- HSMixture layer (`HSMixture/MixtureSeedExtended.lean`, same `FMSA.MixtureOzStar` namespace),
-- re-used here by import.

/-- **⭐ `hUouter` for the constructed renewal at ANY `Mix` (incl. N=2 unequal diameters).**  With
`Ψouter` the Banach–Volterra solution for the continuous `q0MixPoly` kernel and its core-convolution
forcing, `matBaxterU = 0` on `[σ,∞)`, provided `σ` bounds every support edge `Rᵢⱼ`.  Direct
`matBaxterPsi_hUouter` (`hQsupp` = `q0MixPoly_eq_zero_of_ge`, `hforcing` = `matForcingCore` def). -/
theorem q0MixPoly_hUouter {N M : ℕ} (X : Mix N M) (sigma : ℝ) (hsigma : 0 < sigma)
    (hRle : ∀ i j, X.R i j ≤ sigma) (i j : Fin N) {r : ℝ} (hr : sigma ≤ r) :
    matBaxterU
      (matBaxterPsi (fun a b r => (matBaxterPsiOuterFun sigma (q0MixPolyMat X)
          (matForcingCore (q0MixPolyMat X) sigma) (q0MixPolyMat_continuous X)
          (matForcingCore_continuous (q0MixPolyMat X) sigma (q0MixPolyMat_continuous X)) r) a b)
        (fun _ _ v => -v) sigma)
      (fun a b s => (q0MixPolyMat X s) a b) sigma i j r = 0 := by
  refine matBaxterPsi_hUouter sigma hsigma (q0MixPolyMat X)
    (matForcingCore (q0MixPolyMat X) sigma) (q0MixPolyMat_continuous X)
    (matForcingCore_continuous (q0MixPolyMat X) sigma (q0MixPolyMat_continuous X)) ?_ ?_ i j hr
  · intro v hv a b
    simp only [q0MixPolyMat, Matrix.of_apply]
    exact q0MixPoly_eq_zero_of_ge X a b (le_trans (hRle a b) hv)
  · intro a b r' _
    simp only [matForcingCore, Matrix.of_apply]

/-- **⭐ `hint` for the constructed renewal at ANY `Mix` (incl. N=2 unequal diameters).**  Direct
`matBaxterPsi_hint` for the continuous `q0MixPoly` kernel + its `matForcingCore` forcing. -/
theorem q0MixPoly_hint {N M : ℕ} (X : Mix N M) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (i k j : Fin N) (r : ℝ) :
    IntervalIntegrable
      (fun t => (q0MixPolyMat X t) i k *
        matBaxterU (matBaxterPsi (fun a b r => (matBaxterPsiOuterFun sigma (q0MixPolyMat X)
            (matForcingCore (q0MixPolyMat X) sigma) (q0MixPolyMat_continuous X)
            (matForcingCore_continuous (q0MixPolyMat X) sigma (q0MixPolyMat_continuous X)) r) a b)
          (fun _ _ v => -v) sigma)
          (fun a b s => (q0MixPolyMat X s) a b) sigma k j (r + t)) volume 0 sigma :=
  matBaxterPsi_hint sigma hsigma (q0MixPolyMat X) (matForcingCore (q0MixPolyMat X) sigma)
    (q0MixPolyMat_continuous X)
    (matForcingCore_continuous (q0MixPolyMat X) sigma (q0MixPolyMat_continuous X)) i k j r

/-- **⭐⭐ N=2 unequal-diameter `hUouter`** for the physical binary mixture `physMix`, with the seed
scale `σ = max(σ₀,σ₁)` bounding both support edges. -/
theorem physMix_hUouter (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) {r : ℝ} (hr : max (sigma 0) (sigma 1) ≤ r) :
    matBaxterU
      (matBaxterPsi (fun a b r => (matBaxterPsiOuterFun (max (sigma 0) (sigma 1))
          (q0MixPolyMat (physMix rho sigma hsig))
          (matForcingCore (q0MixPolyMat (physMix rho sigma hsig)) (max (sigma 0) (sigma 1)))
          (q0MixPolyMat_continuous (physMix rho sigma hsig))
          (matForcingCore_continuous (q0MixPolyMat (physMix rho sigma hsig))
            (max (sigma 0) (sigma 1)) (q0MixPolyMat_continuous (physMix rho sigma hsig))) r) a b)
        (fun _ _ v => -v) (max (sigma 0) (sigma 1)))
      (fun a b s => (q0MixPolyMat (physMix rho sigma hsig) s) a b)
      (max (sigma 0) (sigma 1)) i j r = 0 := by
  refine q0MixPoly_hUouter (physMix rho sigma hsig) (max (sigma 0) (sigma 1))
    (lt_of_lt_of_le (hsig 0) (le_max_left _ _)) ?_ i j hr
  intro a b
  simp only [physMix, Mix.R]
  have ha : sigma a ≤ max (sigma 0) (sigma 1) := by
    fin_cases a <;> simp [le_max_left, le_max_right]
  have hb : sigma b ≤ max (sigma 0) (sigma 1) := by
    fin_cases b <;> simp [le_max_left, le_max_right]
  linarith

/-- **⭐⭐ N=2 unequal-diameter `hint`** for the physical binary mixture `physMix`. -/
theorem physMix_hint (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k j : Fin 2) (r : ℝ) :
    IntervalIntegrable
      (fun t => (q0MixPolyMat (physMix rho sigma hsig) t) i k *
        matBaxterU (matBaxterPsi (fun a b r => (matBaxterPsiOuterFun (max (sigma 0) (sigma 1))
            (q0MixPolyMat (physMix rho sigma hsig))
            (matForcingCore (q0MixPolyMat (physMix rho sigma hsig)) (max (sigma 0) (sigma 1)))
            (q0MixPolyMat_continuous (physMix rho sigma hsig))
            (matForcingCore_continuous (q0MixPolyMat (physMix rho sigma hsig))
              (max (sigma 0) (sigma 1)) (q0MixPolyMat_continuous (physMix rho sigma hsig))) r) a b)
          (fun _ _ v => -v) (max (sigma 0) (sigma 1)))
          (fun a b s => (q0MixPolyMat (physMix rho sigma hsig) s) a b)
          (max (sigma 0) (sigma 1)) k j (r + t)) volume 0 (max (sigma 0) (sigma 1)) :=
  q0MixPoly_hint (physMix rho sigma hsig) (max (sigma 0) (sigma 1))
    (le_of_lt (lt_of_lt_of_le (hsig 0) (le_max_left _ _))) i k j r

/-! ### The windowing-loss bridge — extended (`∫_ℝ`) vs windowed (`∫₀^σ`) for unequal diameters -/

/-- **Windowing loss vanishes for `λᵢₖ ≥ 0`.**  `q0MixEntry X i k` is supported in `[λᵢₖ, Rᵢₖ]`, so
for `λᵢₖ ≥ 0` it vanishes at `t < 0`; the sub-zero tail `∫_{≤0} q0MixEntry·f = 0` (`{0}` null). -/
theorem q0MixEntry_subZeroTail_zero {N M : ℕ} (X : Mix N M) (i k : Fin N) (f : ℝ → ℝ)
    (hlam : 0 ≤ X.lam i k) :
    (∫ t in Set.Iic (0:ℝ), q0MixEntry X i k t * f t) = 0 :=
  FMSA.HSMix.q0MixEntry_subZeroTail_zero X.toHSMix i k f hlam

/-- **Full-line ⇄ windowed split for the compactly-supported `q0MixEntry`.**  `∫_ℝ q0MixEntry·g =
∫₀^σ + ∫_{≤0}` — the `(σ,∞)` piece vanishes (`q0MixEntry = 0` past `Rᵢₖ ≤ σ`). -/
theorem q0MixEntry_intSplit {N M : ℕ} (X : Mix N M) (i k : Fin N) (g : ℝ → ℝ) (sigma : ℝ)
    (hsig0 : 0 ≤ sigma) (hRsigC : X.R i k ≤ sigma)
    (hint : Integrable (fun t => q0MixEntry X i k t * g t)) :
    (∫ t, q0MixEntry X i k t * g t)
      = (∫ t in (0:ℝ)..sigma, q0MixEntry X i k t * g t)
        + ∫ t in Set.Iic (0:ℝ), q0MixEntry X i k t * g t :=
  FMSA.HSMix.q0MixEntry_intSplit X.toHSMix i k g sigma hsig0 hRsigC hint

/-- **⭐ Windowing-loss bridge — extended = windowed for the smallest species.**  On a row `i` whose
species is smallest (`λᵢₖ ≥ 0` for all `k`, i.e. `σᵢ ≤ σₖ`), every sub-zero tail vanishes, so the
extended (`∫_ℝ`) and windowed (`∫₀^σ`) first Baxter convolutions COINCIDE — NO windowing loss.  (For
larger species some `λᵢₖ < 0` and the sub-zero tail is a genuine `[λᵢₖ,0)` term — the extended
seed's raison d'être.)  Rests only on interval-integrability of each `q0MixEntry·Ψ`. -/
theorem matBaxterUExt_eq_matBaxterU_of_row_lam_nonneg {N M : ℕ} (X : Mix N M)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, 0 ≤ X.lam i k) (hRsigC : ∀ k, X.R i k ≤ sigma)
    (hint : ∀ k, Integrable (fun t => q0MixEntry X i k t * Psi k j (r - t))) :
    matBaxterUExt Psi (fun a b => q0MixEntry X a b) i j r
      = matBaxterU Psi (fun a b => q0MixEntry X a b) sigma i j r :=
  FMSA.HSMix.matBaxterUExt_eq_matBaxterU_of_row_lam_nonneg X.toHSMix Psi sigma hsig0 i j r
    hlam hRsigC hint

/-- `q0MixEntry X i k` integrates to `0` over `(-∞, λᵢₖ]` (below its support; `{λᵢₖ}` is null). -/
theorem q0MixEntry_intIic_lam_eq_zero {N M : ℕ} (X : Mix N M) (i k : Fin N) (g : ℝ → ℝ) :
    (∫ t in Set.Iic (X.lam i k), q0MixEntry X i k t * g t) = 0 :=
  FMSA.HSMix.q0MixEntry_intIic_lam_eq_zero X.toHSMix i k g

/-- **⭐ Larger-species sub-zero tail, compact form.**  For `λᵢₖ ≤ 0` (species `i` bigger than `k`,
`σᵢ > σₖ`) the windowing-loss tail collapses to the COMPACT interval integral over `[λᵢₖ, 0]` — the
`(-∞,λᵢₖ]` piece is below the support and vanishes (`q0MixEntry_intIic_lam_eq_zero`). -/
theorem q0MixEntry_subZeroTail_compact {N M : ℕ} (X : Mix N M) (i k : Fin N) (g : ℝ → ℝ)
    (hlam : X.lam i k ≤ 0) (hint : Integrable (fun t => q0MixEntry X i k t * g t)) :
    (∫ t in Set.Iic (0:ℝ), q0MixEntry X i k t * g t)
      = ∫ t in (X.lam i k)..(0:ℝ), q0MixEntry X i k t * g t :=
  FMSA.HSMix.q0MixEntry_subZeroTail_compact X.toHSMix i k g hlam hint

/-- `q0MixEntry` on its support `[λᵢₖ, Rᵢₖ]` is the explicit Lebowitz quadratic. -/
theorem q0MixEntry_inner_expand {N M : ℕ} (X : Mix N M) (i k : Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (X.lam i k) (X.R i k)) :
    q0MixEntry X i k t
      = X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2 :=
  FMSA.HSMix.q0MixEntry_inner_expand X.toHSMix i k ht

/-- **⭐ Larger-species windowing loss made EXPLICIT.**  For `λᵢₖ ≤ 0`, the sub-zero tail equals the
concrete polynomial moment `∫_{λᵢₖ}^0 (Q0ᵢₖ·(t−Rᵢₖ) + Qppₖ·(t−Rᵢₖ)²/2)·g(t) dt` — the Lebowitz
Baxter quadratic against `g` over `[λᵢₖ, 0]` (there the kernel is the bare polynomial). -/
theorem q0MixEntry_subZeroTail_poly {N M : ℕ} (X : Mix N M) (i k : Fin N) (g : ℝ → ℝ)
    (hlam : X.lam i k ≤ 0) (hint : Integrable (fun t => q0MixEntry X i k t * g t)) :
    (∫ t in Set.Iic (0:ℝ), q0MixEntry X i k t * g t)
      = ∫ t in (X.lam i k)..(0:ℝ),
          (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) * g t :=
  FMSA.HSMix.q0MixEntry_subZeroTail_poly X.toHSMix i k g hlam hint

/-- **⭐⭐ Windowing loss for the LARGEST species, made EXPLICIT.**  Dual to the smallest-species
bridge: on a row `i` whose species is largest (`λᵢₖ ≤ 0` ∀k, i.e. `σᵢ ≥ σₖ`), the extended and
windowed convolutions differ by the concrete sum of Lebowitz polynomial moments `∑ₖ ∫_{λᵢₖ}^0
(Q0ᵢₖ·(t−Rᵢₖ) + Qppₖ·(t−Rᵢₖ)²/2)·Ψₖⱼ(r−t) dt` — the exact windowing loss, NOT fabricated away.
(Diagonal `k=i` has `λᵢᵢ=0` ⇒ empty integral; only smaller partners `σₖ<σᵢ` contribute.) -/
theorem matBaxterUExt_eq_matBaxterU_sub_polyTail {N M : ℕ} (X : Mix N M)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, X.lam i k ≤ 0) (hRsigC : ∀ k, X.R i k ≤ sigma)
    (hint : ∀ k, Integrable (fun t => q0MixEntry X i k t * Psi k j (r - t))) :
    matBaxterUExt Psi (fun a b => q0MixEntry X a b) i j r
      = matBaxterU Psi (fun a b => q0MixEntry X a b) sigma i j r
        - ∑ k, ∫ t in (X.lam i k)..(0:ℝ),
            (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) * Psi k j (r - t) :=
  FMSA.HSMix.matBaxterUExt_eq_matBaxterU_sub_polyTail X.toHSMix Psi sigma hsig0 i j r
    hlam hRsigC hint

/-! ### Physical integrability discharge for the windowing-loss `hint` -/

/-- **Full-line integrability of `q0MixEntry·g`.**  `q0MixEntry X i k` has compact support
`[λᵢₖ,Rᵢₖ]` and is bounded (`q0MixEntry_abs_le`), so its product with any measurable `g` bounded on
that support is integrable over `ℝ` (bounded × finite-measure support). -/
theorem q0MixEntry_mul_integrable {N M : ℕ} (X : Mix N M) (i k : Fin N) (g : ℝ → ℝ)
    (hg : Measurable g) {D : ℝ} (hgbdd : ∀ t ∈ Set.Icc (X.lam i k) (X.R i k), |g t| ≤ D) :
    Integrable (fun t => q0MixEntry X i k t * g t) := by
  obtain ⟨C, hC0, hC⟩ := q0MixEntry_abs_le X i k
  have hsupp : Function.support (fun t => q0MixEntry X i k t * g t)
      ⊆ Set.Icc (X.lam i k) (X.R i k) := fun t ht =>
    q0MixEntry_support_subset X i k
      (Function.mem_support.mpr (left_ne_zero_of_mul (Function.mem_support.mp ht)))
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine Measure.integrableOn_of_bounded (M := C * max D 0) measure_Icc_lt_top.ne
    ((q0MixEntry_measurable X i k).mul hg).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC t) (le_trans (hgbdd t ht) (le_max_left _ _)) (abs_nonneg _) hC0

/-- **⭐ `hint` DISCHARGED for the constructed renewal `matBaxterPsi`.**  For continuous outer/core
data `Po,Pc`, the seed integrand `q0MixEntry X i k · matBaxterPsi Po Pc σ k j (r−·)` is integrable
over `ℝ` — `matBaxterPsi` is measurable (`matBaxterPsi_entry_measurable`) and bounded on the compact
`r − [λᵢₖ,Rᵢₖ]` (`matBaxterPsi_entry_bddOn`), and `q0MixEntry` supplies the compact support. -/
theorem q0MixEntry_matBaxterPsi_integrable {N M : ℕ} (X : Mix N M)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i k j : Fin N) (r : ℝ) :
    Integrable (fun t => q0MixEntry X i k t * matBaxterPsi Po Pc sigma k j (r - t)) :=
  FMSA.HSMix.q0MixEntry_matBaxterPsi_integrable X.toHSMix Po Pc sigma hPo hPc i k j r

/-- **⭐⭐ Windowing-loss bridge, hint-free (smallest species, constructed renewal).**  With `Ψ =
matBaxterPsi Po Pc σ` for CONTINUOUS `Po,Pc` (the constructed renewal), the smallest-species bridge
holds with the integrability side-condition DISCHARGED (`q0MixEntry_matBaxterPsi_integrable`): no
windowing loss. -/
theorem matBaxterUExt_eq_matBaxterU_smallest_of_cont {N M : ℕ} (X : Mix N M)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, 0 ≤ X.lam i k) (hRsigC : ∀ k, X.R i k ≤ sigma) :
    matBaxterUExt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) i j r
      = matBaxterU (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) sigma i j r :=
  FMSA.HSMix.matBaxterUExt_eq_matBaxterU_smallest_of_cont X.toHSMix Po Pc sigma hsig0 hPo hPc
    i j r hlam hRsigC

/-- **⭐⭐ Windowing-loss bridge, hint-free (largest species, constructed renewal).**  Dual of the
above with the integrability DISCHARGED: the extended seed differs from the windowed by the explicit
sum of Lebowitz polynomial moments. -/
theorem matBaxterUExt_sub_polyTail_of_cont {N M : ℕ} (X : Mix N M)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, X.lam i k ≤ 0) (hRsigC : ∀ k, X.R i k ≤ sigma) :
    matBaxterUExt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) i j r
      = matBaxterU (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) sigma i j r
        - ∑ k, ∫ t in (X.lam i k)..(0:ℝ),
            (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2)
              * matBaxterPsi Po Pc sigma k j (r - t) :=
  FMSA.HSMix.matBaxterUExt_sub_polyTail_of_cont X.toHSMix Po Pc sigma hsig0 hPo hPc
    i j r hlam hRsigC

/-! ### N=2 physical instantiation at `σ = max diameter` — the binary-mixture windowing loss -/

/-- The constructed Banach–Volterra outer renewal solution for the physical binary mixture at the
seed scale `σ = max(σ₀,σ₁)` (from the continuous `q0MixPoly` kernel + `matForcingCore`). -/
noncomputable def physMixPsiouter (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) :
    Matrix (Fin 2) (Fin 2) (ℝ → ℝ) :=
  fun a b r => (matBaxterPsiOuterFun (max (sigma 0) (sigma 1))
    (q0MixPolyMat (physMix rho sigma hsig))
    (matForcingCore (q0MixPolyMat (physMix rho sigma hsig)) (max (sigma 0) (sigma 1)))
    (q0MixPolyMat_continuous (physMix rho sigma hsig))
    (matForcingCore_continuous (q0MixPolyMat (physMix rho sigma hsig)) (max (sigma 0) (sigma 1))
      (q0MixPolyMat_continuous (physMix rho sigma hsig))) r) a b

theorem physMixPsiouter_continuous (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (a b : Fin 2) :
    Continuous (physMixPsiouter rho sigma hsig a b) :=
  FMSA.HSMix.physHSMixPsiouter_continuous rho sigma hsig a b

theorem physMix_R_le_max (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) :
    (physMix rho sigma hsig).R i k ≤ max (sigma 0) (sigma 1) :=
  FMSA.HSMix.physHSMix_R_le_max rho sigma hsig i k

/-- **⭐⭐⭐ Physical binary grand assembly — `matBaxterUQm[physMix] = r · c_ij`.**  The
unequal-diameter binary-mixture instantiation of `matBaxterUQm_eq_rcMixMomentDCF`: for the physical
`physMix` with the constructed Banach–Volterra renewal (`physMixPsiouter`) and the `q0MixPolyMat`
kernel at the seed scale `σ = max(σ₀,σ₁)`, the windowed second Baxter convolution equals `r` times
the explicit mixture DCF `cMixMomentDCF` — the general-`N` grand assembly landed at a physical
unequal-diameter mixture.  Discharges `hUouter`=`physMix_hUouter`, `hint`=`physMix_hint`,
`hQ0`/`hQ1` (kernel continuity), `hcore`=`matBaxterPsi_core`.  (The windowed-seed DCF; the loss-free
object is `matBaxterUQmSymFullExt` / `cHSmixRenewal`.) -/
theorem matBaxterUQm_physMix_eq_rc (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {r : ℝ} (hr : 0 < r) (i j : Fin 2) :
    matBaxterUQm (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b s => (q0MixPolyMat (physMix rho sigma hsig) s) a b)
        (max (sigma 0) (sigma 1)) i j r
      = r * cMixMomentDCF (fun a b s => (q0MixPolyMat (physMix rho sigma hsig) s) a b)
          (max (sigma 0) (sigma 1)) i j r :=
  matBaxterUQm_eq_rcMixMomentDCF _ _ (max (sigma 0) (sigma 1))
    (lt_of_lt_of_le (hsig 0) (le_max_left _ _))
    (fun i j r hr => physMix_hUouter rho sigma hsig i j hr)
    (fun i j k r => physMix_hint rho sigma hsig i k j r)
    (fun i k => (((q0MixPolyMat_continuous (physMix rho sigma hsig)).matrix_elem i k
      ).intervalIntegrable 0 _))
    (fun i k => (continuous_id.mul
      ((q0MixPolyMat_continuous (physMix rho sigma hsig)).matrix_elem i k)).intervalIntegrable 0 _)
    (fun k j v hv => matBaxterPsi_core _ _ k j hv) hr i j

/-- **⭐⭐⭐ N=2 physical windowing-loss — smallest species (σ = max diameter).**  For the physical
binary mixture, on the row `i` of the SMALLEST species (`σᵢ ≤ σₖ ∀k`), the extended and windowed
Baxter convolutions coincide: NO windowing loss.  Fully instantiated — the constructed renewal
supplies continuity, `σ = max(σ₀,σ₁)` bounds the support edges, and integrability is discharged. -/
theorem physMix_windowing_smallest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hsmall : ∀ k, sigma i ≤ sigma k) :
    matBaxterUExt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) i j r
      = matBaxterU (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) (max (sigma 0) (sigma 1)) i j r := by
  exact FMSA.HSMix.physHSMix_windowing_smallest rho sigma hsig i j r hsmall

/-- **⭐⭐⭐ N=2 physical windowing-loss — largest species (σ = max diameter).**  On the row `i` of
the LARGEST species (`σₖ ≤ σᵢ ∀k`), the extended seed differs from the windowed by the EXPLICIT sum
of Lebowitz polynomial moments over `[λᵢₖ, 0]` — the exact unequal-diameter windowing loss. -/
theorem physMix_windowing_largest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hlarge : ∀ k, sigma k ≤ sigma i) :
    matBaxterUExt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) i j r
      = matBaxterU (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) (max (sigma 0) (sigma 1)) i j r
        - ∑ k, ∫ t in ((physMix rho sigma hsig).lam i k)..(0:ℝ),
            ((physMix rho sigma hsig).Q0 i k * (t - (physMix rho sigma hsig).R i k)
              + (physMix rho sigma hsig).Qpp k * (t - (physMix rho sigma hsig).R i k) ^ 2 / 2)
              * matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
                  (max (sigma 0) (sigma 1)) k j (r - t) := by
  exact FMSA.HSMix.physHSMix_windowing_largest rho sigma hsig i j r hlarge

/-! ### Transposed seed arm `matBaxterUtExt` — windowing loss (dual of the un-transposed arm) -/

/-- **⭐ Transposed-arm windowing loss vanishes — `matBaxterUtExt = matBaxterUt` when `λₖᵢ ≥ 0`.**
The transposed seed arm `matBaxterUtExt` convolves the kernel `Qₖᵢ = q0MixEntry X k i`, so its
sub-zero tail is governed by `λₖᵢ = (σᵢ−σₖ)/2`.  DUAL to the un-transposed arm: it VANISHES on the
LARGEST-species row `i` (`σᵢ ≥ σₖ ∀k ⟺ λₖᵢ ≥ 0`).  Via `matBaxterUt/UtExt_eq_transpose` (both `rfl`)
this is the un-transposed bridge at the transposed kernel `Qᵀ`. -/
theorem matBaxterUtExt_eq_matBaxterUt_of_row {N M : ℕ} (X : Mix N M)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, 0 ≤ X.lam k i) (hRsigC : ∀ k, X.R k i ≤ sigma)
    (hint : ∀ k, Integrable (fun t => q0MixEntry X k i t * Psi k j (r - t))) :
    matBaxterUtExt Psi (fun a b => q0MixEntry X a b) i j r
      = matBaxterUt Psi (fun a b => q0MixEntry X a b) sigma i j r :=
  FMSA.HSMix.matBaxterUtExt_eq_matBaxterUt_of_row X.toHSMix Psi sigma hsig0 i j r
    hlam hRsigC hint

/-- **⭐⭐ Transposed-arm windowing loss, EXPLICIT — smallest species (`λₖᵢ ≤ 0`).**  On the
SMALLEST-species row `i` (`σᵢ ≤ σₖ ∀k`), the transposed extended arm differs from the windowed by
the explicit sum of Lebowitz polynomial moments `∑ₖ ∫_{λₖᵢ}^0 (Q0ₖᵢ(t−Rₖᵢ)+Qppᵢ(t−Rₖᵢ)²/2)·Ψₖⱼ(r−t)`
— the DUAL of the un-transposed largest-species loss.  (The seed's leading arm; the numerically-
verified value object.) -/
theorem matBaxterUtExt_eq_matBaxterUt_sub_polyTail {N M : ℕ} (X : Mix N M)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, X.lam k i ≤ 0) (hRsigC : ∀ k, X.R k i ≤ sigma)
    (hint : ∀ k, Integrable (fun t => q0MixEntry X k i t * Psi k j (r - t))) :
    matBaxterUtExt Psi (fun a b => q0MixEntry X a b) i j r
      = matBaxterUt Psi (fun a b => q0MixEntry X a b) sigma i j r
        - ∑ k, ∫ t in (X.lam k i)..(0:ℝ),
            (X.Q0 k i * (t - X.R k i) + X.Qpp i * (t - X.R k i) ^ 2 / 2) * Psi k j (r - t) :=
  FMSA.HSMix.matBaxterUtExt_eq_matBaxterUt_sub_polyTail X.toHSMix Psi sigma hsig0 i j r
    hlam hRsigC hint


/-- Decoupled integrability: `q0MixEntry X a b · matBaxterPsi Po Pc σ p q (r−·)` with the kernel
indices `(a,b)` INDEPENDENT of the `Ψ` indices `(p,q)` — needed for the transposed arm where the
`q0MixEntry` second index and the `matBaxterPsi` first index differ. -/
theorem q0MixEntry_matBaxterPsi_integrable_gen {N M : ℕ} (X : Mix N M)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (a b p q : Fin N) (r : ℝ) :
    Integrable (fun t => q0MixEntry X a b t * matBaxterPsi Po Pc sigma p q (r - t)) :=
  FMSA.HSMix.q0MixEntry_matBaxterPsi_integrable_gen X.toHSMix Po Pc sigma hPo hPc a b p q r

/-- **⭐⭐ Transposed arm, hint-free (largest species, constructed renewal): NO loss.** -/
theorem matBaxterUtExt_eq_matBaxterUt_of_cont {N M : ℕ} (X : Mix N M)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, 0 ≤ X.lam k i) (hRsigC : ∀ k, X.R k i ≤ sigma) :
    matBaxterUtExt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) i j r
      = matBaxterUt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) sigma i j r :=
  FMSA.HSMix.matBaxterUtExt_eq_matBaxterUt_of_cont X.toHSMix Po Pc sigma hsig0 hPo hPc
    i j r hlam hRsigC

/-- **⭐⭐ Transposed arm, hint-free (smallest species, constructed renewal): EXPLICIT loss.** -/
theorem matBaxterUtExt_sub_polyTail_of_cont {N M : ℕ} (X : Mix N M)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, X.lam k i ≤ 0) (hRsigC : ∀ k, X.R k i ≤ sigma) :
    matBaxterUtExt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) i j r
      = matBaxterUt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) sigma i j r
        - ∑ k, ∫ t in (X.lam k i)..(0:ℝ),
            (X.Q0 k i * (t - X.R k i) + X.Qpp i * (t - X.R k i) ^ 2 / 2)
              * matBaxterPsi Po Pc sigma k j (r - t) :=
  FMSA.HSMix.matBaxterUtExt_sub_polyTail_of_cont X.toHSMix Po Pc sigma hsig0 hPo hPc
    i j r hlam hRsigC



/-- **⭐⭐⭐ N=2 physical transposed arm — largest species (σ = max diameter): NO loss.**  DUAL to
`physMix_windowing_largest`: the transposed seed arm on the largest-species row has no loss. -/
theorem physMix_windowing_t_largest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hlarge : ∀ k, sigma k ≤ sigma i) :
    matBaxterUtExt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) i j r
      = matBaxterUt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) (max (sigma 0) (sigma 1)) i j r := by
  exact FMSA.HSMix.physHSMix_windowing_t_largest rho sigma hsig i j r hlarge

/-- **⭐⭐⭐ N=2 physical transposed-arm windowing loss — smallest species: EXPLICIT loss.**  DUAL to
`physMix_windowing_smallest`: the transposed arm on the smallest-species row carries the explicit
Lebowitz polynomial-moment loss (the numerically-verified value arm). -/
theorem physMix_windowing_t_smallest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hsmall : ∀ k, sigma i ≤ sigma k) :
    matBaxterUtExt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) i j r
      = matBaxterUt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => q0MixEntry (physMix rho sigma hsig) a b) (max (sigma 0) (sigma 1)) i j r
        - ∑ k, ∫ t in ((physMix rho sigma hsig).lam k i)..(0:ℝ),
            ((physMix rho sigma hsig).Q0 k i * (t - (physMix rho sigma hsig).R k i)
              + (physMix rho sigma hsig).Qpp i * (t - (physMix rho sigma hsig).R k i) ^ 2 / 2)
              * matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
                  (max (sigma 0) (sigma 1)) k j (r - t) := by
  exact FMSA.HSMix.physHSMix_windowing_t_smallest rho sigma hsig i j r hsmall

/-! ### Sum of both arms' windowing losses = the symmetrized fold-kernel `Ĉ₀` sub-zero tail -/

/-- **⭐⭐ Sum of the two seed arms' windowing losses = the SYMMETRIZED-kernel sub-zero tail.**  The
un-transposed arm loss `matBaxterU − matBaxterUExt = ∑ₖ ∫_{≤0} q0MixEntry X i k·Ψ` and the
transposed arm loss `matBaxterUt − matBaxterUtExt = ∑ₖ ∫_{≤0} q0MixEntry X k i·Ψ` ADD, by linearity,
to the
sub-zero tail of the SYMMETRIZED Baxter kernel `q0MixEntry X i k + q0MixEntry X k i` — the
un-reflected part of the DCF fold kernel `Ĉ₀` the symmetric mixture DCF `r·c` is built from.  Holds
on ANY row (no species condition): the un-transposed contributes on the larger partners, the
transposed on the smaller, together covering every `k`. -/
theorem windowing_loss_sum_eq_symTail {N M : ℕ} (X : Mix N M)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hRun : ∀ k, X.R i k ≤ sigma) (hRt : ∀ k, X.R k i ≤ sigma)
    (hint_un : ∀ k, Integrable (fun t => q0MixEntry X i k t * Psi k j (r - t)))
    (hint_t : ∀ k, Integrable (fun t => q0MixEntry X k i t * Psi k j (r - t))) :
    (matBaxterU Psi (fun a b => q0MixEntry X a b) sigma i j r
       - matBaxterUExt Psi (fun a b => q0MixEntry X a b) i j r)
    + (matBaxterUt Psi (fun a b => q0MixEntry X a b) sigma i j r
       - matBaxterUtExt Psi (fun a b => q0MixEntry X a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        (q0MixEntry X i k t + q0MixEntry X k i t) * Psi k j (r - t) :=
  FMSA.HSMix.windowing_loss_sum_eq_symTail X.toHSMix Psi sigma hsig0 i j r hRun hRt hint_un hint_t


/-- **⭐⭐ Symmetric-kernel windowing loss, hint-free (constructed renewal).**  Same, for `Ψ =
matBaxterPsi Po Pc σ` with continuous `Po,Pc`, integrability discharged. -/
theorem windowing_loss_sum_eq_symTail_of_cont {N M : ℕ} (X : Mix N M)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hRun : ∀ k, X.R i k ≤ sigma) (hRt : ∀ k, X.R k i ≤ sigma) :
    (matBaxterU (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) sigma i j r
       - matBaxterUExt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) i j r)
    + (matBaxterUt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) sigma i j r
       - matBaxterUtExt (matBaxterPsi Po Pc sigma) (fun a b => q0MixEntry X a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        (q0MixEntry X i k t + q0MixEntry X k i t) * matBaxterPsi Po Pc sigma k j (r - t) :=
  FMSA.HSMix.windowing_loss_sum_eq_symTail_of_cont X.toHSMix Po Pc sigma hsig0 hPo hPc
    i j r hRun hRt

/-- **⭐⭐⭐ N=2 physical symmetric-kernel windowing loss (σ = max diameter).**  For the binary
mixture on ANY row `i`, the two arms' losses sum to the symmetrized `q0MixEntry` sub-zero tail — the
fold-kernel `Ĉ₀` windowing loss the symmetric Lebowitz DCF is built from. -/
theorem physMix_windowing_sum (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin 2)
    (r : ℝ) :
    (matBaxterU (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => q0MixEntry (physMix rho sigma hsig) a b)
        (max (sigma 0) (sigma 1)) i j r
       - matBaxterUExt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => q0MixEntry (physMix rho sigma hsig) a b) i j r)
    + (matBaxterUt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => q0MixEntry (physMix rho sigma hsig) a b)
        (max (sigma 0) (sigma 1)) i j r
       - matBaxterUtExt (matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => q0MixEntry (physMix rho sigma hsig) a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        (q0MixEntry (physMix rho sigma hsig) i k t + q0MixEntry (physMix rho sigma hsig) k i t)
          * matBaxterPsi (physMixPsiouter rho sigma hsig) (fun _ _ v => -v)
              (max (sigma 0) (sigma 1)) k j (r - t) :=
  FMSA.HSMix.physHSMix_windowing_sum rho sigma hsig i j r

/-! ### General-N (N≥3) physical symmetric-kernel windowing loss -/

/-- The constructed Banach–Volterra outer renewal for the GENERAL-N physical mixture `physMixN`, at
a seed scale `sigmax` bounding every diameter (continuous `q0MixPoly` kernel + `matForcingCore`). -/
noncomputable def physMixNPsiouter {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (sigmax : ℝ) : Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  fun a b r => (matBaxterPsiOuterFun sigmax (q0MixPolyMat (physMixN rho sigma hsig))
    (matForcingCore (q0MixPolyMat (physMixN rho sigma hsig)) sigmax)
    (q0MixPolyMat_continuous (physMixN rho sigma hsig))
    (matForcingCore_continuous (q0MixPolyMat (physMixN rho sigma hsig)) sigmax
      (q0MixPolyMat_continuous (physMixN rho sigma hsig))) r) a b

theorem physMixNPsiouter_continuous {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (sigmax : ℝ) (a b : Fin N) : Continuous (physMixNPsiouter rho sigma hsig sigmax a b) :=
  FMSA.HSMix.physHSMixNPsiouter_continuous rho sigma hsig sigmax a b

theorem physMixN_R_le {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (sigmax : ℝ)
    (hsigmax : ∀ k, sigma k ≤ sigmax) (i k : Fin N) :
    (physMixN rho sigma hsig).R i k ≤ sigmax :=
  FMSA.HSMix.physHSMixN_R_le rho sigma hsig sigmax hsigmax i k

/-- **⭐⭐⭐ General-N (N≥3) physical symmetric-kernel windowing loss.**  For the general-N physical
mixture `physMixN` (any `N`) with the constructed renewal at a seed scale `sigmax` bounding every
diameter, on ANY row `i` the two seed arms' windowing losses SUM to the symmetrized `q0MixEntry`
sub-zero tail — the fold-kernel `Ĉ₀` windowing loss.  General-N form of `physMix_windowing_sum`. -/
theorem physMixN_windowing_sum {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (sigmax : ℝ) (hpos : 0 ≤ sigmax) (hsigmax : ∀ k, sigma k ≤ sigmax) (i j : Fin N) (r : ℝ) :
    (matBaxterU (matBaxterPsi (physMixNPsiouter rho sigma hsig sigmax) (fun _ _ v => -v) sigmax)
        (fun a b => q0MixEntry (physMixN rho sigma hsig) a b) sigmax i j r
       - matBaxterUExt (matBaxterPsi (physMixNPsiouter rho sigma hsig sigmax)
        (fun _ _ v => -v) sigmax)
        (fun a b => q0MixEntry (physMixN rho sigma hsig) a b) i j r)
    + (matBaxterUt (matBaxterPsi (physMixNPsiouter rho sigma hsig sigmax) (fun _ _ v => -v) sigmax)
        (fun a b => q0MixEntry (physMixN rho sigma hsig) a b) sigmax i j r
       - matBaxterUtExt (matBaxterPsi (physMixNPsiouter rho sigma hsig sigmax)
        (fun _ _ v => -v) sigmax)
        (fun a b => q0MixEntry (physMixN rho sigma hsig) a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        (q0MixEntry (physMixN rho sigma hsig) i k t + q0MixEntry (physMixN rho sigma hsig) k i t)
          * matBaxterPsi (physMixNPsiouter rho sigma hsig sigmax) (fun _ _ v => -v) sigmax
              k j (r - t) :=
  FMSA.HSMix.physHSMixN_windowing_sum rho sigma hsig sigmax hpos hsigmax i j r

end FMSA.MixtureHSDCFFin1
