/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureBaxterSeed
import LeanCode.YukawaOZMix.WHSupports
import LeanCode.HSMixture.HSMixBaxterFactor
import LeanCode.HSMixture.MixtureSeedExtended

/-!
# `hrow` for the concrete `q0MixEntry` — the equal-diameter row-sum collapse

`matBaxterUQm_momentSeed_of_rowSum` (`MixtureBaxterSeed`) reduces the matrix Wertheim–Thiele seed to
the scalar `baxter_core_seed` **given** the row-sum collapse

  `hrow : ∀ i, ∀ u ∈ [0,σ],  ∑ₖ Qᵢₖ(u) = q0_poly η σ ρ(u)`      (`ρ = ∑ₖ ρₖ`, `η = πρσ³/6`).

This file discharges `hrow` for the **concrete** real-space Baxter factor `WHSupports.q0MixEntry`, in
the physically-rigorous **equal-diameter** regime.

For a common diameter `σᵢ = σ` the size asymmetry `λᵢₖ = 0` vanishes (delta-free, single core `[0,σ]`)
and the contact distance `Rᵢₖ = σ` is constant, so on `[0,σ]`

  `q0MixEntryᵢₖ(u) = Q₀ᵢₖ·(u−σ) + Q''ₖ·(u−σ)²/2`.

The **non-symmetric** Baxter convention that matches the seed's bare core value `Ψₖⱼ = −v` carries the
column density `ρₖ` in the factor coefficients — `Q₀ᵢₖ = ρₖ·q'_py(η,σ)`, `Q''ₖ = ρₖ·q''_py(η)` — the
density-weighted form of the one-component PY coefficients (note `Q0phys` at a single equal-diameter
species reduces to exactly `q_prime_py`).  Then every row collapses:

  `∑ₖ q0MixEntryᵢₖ(u) = (∑ₖρₖ)·(q'_py·(u−σ) + q''_py·(u−σ)²/2) = ρ·(…) = q0_poly η σ ρ(u)`,

the one-component scalar Baxter factor at the total density (`q0_poly_inner`) — colour-blindness of the
equal-diameter mixture.  This is exactly `hrow`; fed to `matBaxterUQm_momentSeed_of_rowSum` it discharges
the matrix core seed for the concrete kernel.

Status: ✓ axiom-clean.
-/

open MeasureTheory Set
namespace FMSA.MixtureBaxter
open FMSA.MixtureOzStar
open FMSA.InnerDecomp FMSA.WHSupports FMSA.HardSphere

noncomputable section

/-- **Concrete `hrow` — the equal-diameter row-sum of `q0MixEntry` is the scalar `q0_poly`.**

For an equal-diameter mixture (`X.σ k = σ` for every `k`) whose Baxter coefficients are the
density-weighted one-component PY values (`X.Q0 i k = ρₖ·q'_py(η,σ)`, `X.Qpp k = ρₖ·q''_py(η)`, the
non-symmetric convention matching the bare core value `Ψₖⱼ = −v`), the row-sum of the concrete
`WHSupports.q0MixEntry` over the intermediate species `k` equals the one-component scalar Baxter factor
`q0_poly η σ ρ` at the total density `ρ = ∑ₖ ρₖ` — on the full core `[0,σ]`.

This **discharges** the `hrow` hypothesis of `matBaxterUQm_momentSeed_of_rowSum` /
`matBaxterUQm_eq_rcHS_of_rowSum` for the concrete kernel, closing the equal-diameter matrix seed. -/
theorem q0MixEntry_rowSum_eq_q0_poly {N M : ℕ} (X : Mix N M) {sigma eta rho : ℝ}
    (hsig : ∀ k, X.σ k = sigma)
    (hrho : rho = ∑ k, X.ρ k)
    (hQ0 : ∀ i k, X.Q0 i k = X.ρ k * q_prime_py eta sigma)
    (hQpp : ∀ k, X.Qpp k = X.ρ k * q_doubleprime_py eta)
    (i : Fin N) (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) sigma) :
    ∑ k, q0MixEntry X i k u = q0_poly eta sigma rho u := by
  obtain ⟨hu0, huσ⟩ := hu
  -- each entry collapses to `ρₖ·(per-density quadratic)` on the equal-diameter core `[0,σ]`
  have hentry : ∀ k : Fin N, q0MixEntry X i k u
      = X.ρ k * (q_prime_py eta sigma * (u - sigma)
                  + q_doubleprime_py eta * (u - sigma) ^ 2 / 2) := by
    intro k
    have hlam : X.lam i k = 0 := by simp only [Mix.lam, hsig]; ring
    have hR : X.R i k = sigma := by simp only [Mix.R, hsig]; ring
    have hmem : u ∈ Set.Icc (X.lam i k) (X.R i k) := by
      rw [hlam, hR]; exact Set.mem_Icc.mpr ⟨hu0, huσ⟩
    unfold q0MixEntry
    rw [Set.indicator_of_mem hmem]
    simp only [hR, hQ0 i k, hQpp k]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hentry k), ← Finset.sum_mul, ← hrho, q0_poly_inner huσ]
  ring

/-! ### Integrability of the concrete kernel — the seed's remaining side-conditions -/

/-- **`q0MixEntry X i k` is interval-integrable on any `[a,b]`.**  Discharges the `hQ0`
side-condition of `matBaxterUQm_momentSeed_of_rowSum`.  Delegates to the pure-HS-layer
`FMSA.HSMix.q0MixEntry_intervalIntegrable` through the `toHSMix` bridge (functions `rfl`-equal). -/
theorem q0MixEntry_intervalIntegrable {N M : ℕ} (X : Mix N M) (i k : Fin N) (a b : ℝ) :
    IntervalIntegrable (q0MixEntry X i k) volume a b :=
  FMSA.HSMix.q0MixEntry_intervalIntegrable X.toHSMix i k a b

/-- **`t ↦ t · q0MixEntry X i k t` is interval-integrable on any `[a,b]`.**  Discharges the `hQ1`
side-condition.  Delegates to the pure-HS layer through the `toHSMix` bridge. -/
theorem q0MixEntry_mul_id_intervalIntegrable {N M : ℕ} (X : Mix N M) (i k : Fin N) (a b : ℝ) :
    IntervalIntegrable (fun t => t * q0MixEntry X i k t) volume a b :=
  FMSA.HSMix.q0MixEntry_mul_id_intervalIntegrable X.toHSMix i k a b

/-- **UNCONDITIONAL concrete matrix core seed — the equal-diameter `q0MixEntry` moment identity.**
Combining the concrete row-sum (`q0MixEntry_rowSum_eq_q0_poly`) with the `q0MixEntry` interval
integrability, the matrix Wertheim–Thiele moment identity holds for the concrete Baxter factor
`Q = q0MixEntry` with **no integrability side-condition left** — the full `matBaxterUQm_momentSeed_of_rowSum`
discharged for the physical kernel at equal diameters.  This is exactly the `hMomentSeed` that
`matBaxterUQm_eq_rPhi_of_momentSeed` needs, now unconditional in the kernel. -/
theorem matBaxterUQm_momentSeed_q0MixEntry {N M : ℕ} (X : Mix N M) {sigma eta rho : ℝ}
    (hsigma : 0 < sigma) (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hsig : ∀ k, X.σ k = sigma) (hrho : rho = ∑ k, X.ρ k)
    (hQ0 : ∀ i k, X.Q0 i k = X.ρ k * q_prime_py eta sigma)
    (hQpp : ∀ k, X.Qpp k = X.ρ k * q_doubleprime_py eta) :
    ∀ (i _j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      (r * ((∑ k, ∫ t in (0:ℝ)..sigma, q0MixEntry X i k t) - 1)
          - ∑ k, ∫ t in (0:ℝ)..sigma, t * q0MixEntry X i k t)
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), q0MixEntry X i k t
            * ((r + t) * ((∑ l, ∫ s in (0:ℝ)..sigma, q0MixEntry X k l s) - 1)
               - ∑ l, ∫ s in (0:ℝ)..sigma, s * q0MixEntry X k l s)
      = r * c_HS eta sigma r :=
  matBaxterUQm_momentSeed_of_rowSum (fun i k => q0MixEntry X i k) hsigma heta heta_def
    (fun i u hu => q0MixEntry_rowSum_eq_q0_poly X hsig hrho hQ0 hQpp i u hu)
    (fun i k => q0MixEntry_intervalIntegrable X i k 0 sigma)
    (fun i k => q0MixEntry_mul_id_intervalIntegrable X i k 0 sigma)

/-! ### The Ψ-side: the concrete `matBaxterPsi` carries the hard-core value (`hcore`) -/

/-- **`hcore` for the concrete `matBaxterPsi`.**  The concrete glued matrix solution takes
`Ψcore = fun _ _ v => −v` (the multicomponent `h = −1` hard-core value, exactly the core matrix used by
`matBaxterPsi_fin_one_of_scalar`), so on the open core `(−σ,σ)` the core branch of `matBaxterPsi` is,
**definitionally**, `−v`:

  `matBaxterPsi Ψouter (fun _ _ v => −v) σ k j v = −v`   for `v ∈ (−σ,σ)`.

This discharges the `hcore` hypothesis of `matBaxterU_core` / `matBaxterUQm_eq_rcHS_of_rowSum` for the
constructed `Ψ`, for **any** outer solution `Ψouter` (the seed-side analog of the scalar
`baxterPsi_core`). -/
theorem matBaxterPsi_hcore {N : ℕ} (Psiouter : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {sigma : ℝ}
    (k j : Fin N) (v : ℝ) (hv : v ∈ Set.Ioo (-sigma) sigma) :
    matBaxterPsi Psiouter (fun _ _ v => -v) sigma k j v = -v :=
  matBaxterPsi_core Psiouter (fun _ _ v => -v) k j hv

/-- **`hUouter` (claim A) for the constructed `matBaxterPsi`.**  For **continuous** matrix Baxter data
`Qm, Fm : ℝ → Matrix` with `Qm` vanishing above `σ` and `Fm` the core-convolution forcing, the glued
solution `Ψ = matBaxterPsi (matBaxterPsiOuterFun σ Qm Fm) (fun _ _ v => −v) σ` satisfies the first
Baxter convolution outer-vanishing `matBaxterUᵢⱼ(r) = 0` on `[σ,∞)`.

This wires the constructed outer solution into the abstract `matBaxterU_outer`: `hQcont`/`hQsupp` from
`Qm` (entrywise, `fun_prop`), `hcore` from `matBaxterPsi_core` (the definitional `−v`), `houter_cont`
from `matBaxterPsiOuterFun_continuous` + `matBaxterPsi_outer` (glued `= Ψouter` on `[σ,b]`), and the
coupled `hrenewal` from `matBaxterPsiOuter_matRenewalEq` (Banach global Volterra) rewritten from `Ψouter`
to `Ψ` via `matBaxterPsi_outer` on `[σ,r]`.  The continuity of `Qm` is intrinsic — the renewal is built
by Banach Volterra, which needs it (so the seed kernel is the *continuous* `q0_poly`-matrix, not the
truncated `q0MixEntry`; the two agree on `[0,σ]`, which is all `matBaxterU`/`matBaxterUQm` sample). -/
theorem matBaxterPsi_hUouter {N : ℕ} (sigma : ℝ) (hsigma : 0 < sigma)
    (Qm Fm : ℝ → Matrix (Fin N) (Fin N) ℝ) (hQ : Continuous Qm) (hF : Continuous Fm)
    (hQsupp : ∀ (v : ℝ), sigma ≤ v → ∀ i k, (Qm v) i k = 0)
    (hforcing : ∀ i j r, sigma ≤ r →
      (Fm r) i j = ∑ k, ∫ s in (0:ℝ)..sigma, (Qm (r - s)) i k * (-s))
    (i j : Fin N) {r : ℝ} (hr : sigma ≤ r) :
    matBaxterU (matBaxterPsi (fun i j r => (matBaxterPsiOuterFun sigma Qm Fm hQ hF r) i j)
        (fun _ _ v => -v) sigma) (fun i k s => (Qm s) i k) sigma i j r = 0 := by
  set Po : Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
    (fun i j r => (matBaxterPsiOuterFun sigma Qm Fm hQ hF r) i j) with hPo
  set Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ) := (fun _ _ v => -v) with hPc
  set Qe : Matrix (Fin N) (Fin N) (ℝ → ℝ) := (fun i k s => (Qm s) i k) with hQe
  set Fe : Matrix (Fin N) (Fin N) (ℝ → ℝ) := (fun i j r => (Fm r) i j) with hFe
  have hcontOuter : Continuous (matBaxterPsiOuterFun sigma Qm Fm hQ hF) :=
    matBaxterPsiOuterFun_continuous sigma Qm Fm hQ hF
  have hRen : MatRenewalEq Po Fe Qe sigma :=
    matBaxterPsiOuter_matRenewalEq sigma Qm Fm hQ hF
  refine matBaxterU_outer sigma hsigma (matBaxterPsi Po Pc sigma) Pc Qe Fe
    (fun i k => by simp only [hQe]; fun_prop)
    (fun i k v hv => by simp only [hQe]; exact hQsupp v hv i k)
    (fun k j => by simp only [hPc]; fun_prop)
    (fun k j s hs => matBaxterPsi_core Po Pc k j
      (Set.mem_Ioo.mpr ⟨by linarith [hs.1, hsigma], hs.2⟩))
    (fun k j b => ?_)
    (fun i j r hr => by simp only [hFe, hQe, hPc]; exact hforcing i j r hr)
    (fun i j r hr => ?_) hr i j
  · have hce : Continuous (fun v => (matBaxterPsiOuterFun sigma Qm Fm hQ hF v) k j) := by fun_prop
    refine (hce.continuousOn).congr (fun v hv => ?_)
    exact matBaxterPsi_outer Po Pc k j (Set.mem_Icc.mp hv).1
  · rw [matBaxterPsi_outer Po Pc i j hr, hRen i j r hr]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hr] at ht
    rw [matBaxterPsi_outer Po Pc k j ht.1]

/-! ### The Ψ-side: `hint` (integrability of `Q · matBaxterU`) for the constructed `matBaxterPsi` -/

/-- The convolution window `x ↦ ∫₀^σ Q(t)·Psi(x−t) dt` is measurable (for measurable `Q, Psi`) — via
`StronglyMeasurable.integral_prod_right` after rewriting the interval integral as an `Ioc`-indicator. -/
theorem convWindow_measurable {Q Psi : ℝ → ℝ} (hQ : Measurable Q) (hPsi : Measurable Psi)
    {sigma : ℝ} (hσ : 0 ≤ sigma) :
    Measurable (fun x => ∫ t in (0:ℝ)..sigma, Q t * Psi (x - t)) := by
  have hrw : (fun x => ∫ t in (0:ℝ)..sigma, Q t * Psi (x - t))
      = fun x => ∫ t, (Set.Ioc (0:ℝ) sigma).indicator (fun t => Q t * Psi (x - t)) t := by
    funext x
    rw [intervalIntegral.integral_of_le hσ, ← MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [hrw]
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
    (f := fun x t => (Set.Ioc (0:ℝ) sigma).indicator (fun t => Q t * Psi (x - t)) t)
  exact (Measurable.indicator (by fun_prop)
    (measurableSet_Ioc.preimage (by fun_prop))).stronglyMeasurable

/-- `matBaxterU Psi Q σ k j` is measurable (continuous `Q`, measurable `Psi` entries). -/
theorem matBaxterU_measurable {N : ℕ} (sigma : ℝ) (hσ : 0 ≤ sigma)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQcont : ∀ i k, Continuous (Q i k)) (hPsiMeas : ∀ l j, Measurable (Psi l j)) (k j : Fin N) :
    Measurable (matBaxterU Psi Q sigma k j) := by
  unfold matBaxterU
  refine (hPsiMeas k j).sub (Finset.measurable_sum _ (fun l _ => ?_))
  exact convWindow_measurable (hQcont k l).measurable (hPsiMeas l j) hσ

/-- `matBaxterU Psi Q σ k j` is bounded on every `Icc a b` (`a ≤ b`) — continuous `Q`, locally
bounded `Psi`. -/
theorem matBaxterU_bddOn {N : ℕ} (sigma : ℝ) (hσ : 0 ≤ sigma)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQcont : ∀ i k, Continuous (Q i k))
    (hPsiBdd : ∀ l j a b, ∃ C, ∀ x ∈ Set.uIcc a b, |Psi l j x| ≤ C)
    (k j : Fin N) (a b : ℝ) (hab : a ≤ b) :
    ∃ C, ∀ x ∈ Set.Icc a b, |matBaxterU Psi Q sigma k j x| ≤ C := by
  obtain ⟨C0, hC0⟩ := hPsiBdd k j a b
  have hconv : ∀ l : Fin N, ∃ Cl, ∀ x ∈ Set.Icc a b,
      |∫ t in (0:ℝ)..sigma, Q k l t * Psi l j (x - t)| ≤ Cl := by
    intro l
    obtain ⟨Cq, hCq⟩ := (isCompact_uIcc (a := (0:ℝ)) (b := sigma)).exists_bound_of_continuousOn
      (hQcont k l).continuousOn
    obtain ⟨Cp, hCp⟩ := hPsiBdd l j (a - sigma) b
    refine ⟨(max Cq 0) * (max Cp 0) * sigma, fun x hx => ?_⟩
    have hbd : ∀ t ∈ Set.Ioc (min (0:ℝ) sigma) (max 0 sigma),
        ‖Q k l t * Psi l j (x - t)‖ ≤ (max Cq 0) * (max Cp 0) := by
      intro t ht
      rw [min_eq_left hσ, max_eq_right hσ] at ht
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Q k l t| ≤ max Cq 0 := by
        have := hCq t (Set.Ioc_subset_Icc_self.trans (le_of_eq (Set.uIcc_of_le hσ).symm) ht)
        rw [Real.norm_eq_abs] at this; exact le_trans this (le_max_left _ _)
      have h2 : |Psi l j (x - t)| ≤ max Cp 0 := by
        have hmem : x - t ∈ Set.uIcc (a - sigma) b := by
          rw [Set.uIcc_of_le (by linarith [hx.1, hx.2] : a - sigma ≤ b), Set.mem_Icc]
          exact ⟨by linarith [hx.1, ht.2], by linarith [hx.2, ht.1]⟩
        exact le_trans (hCp _ hmem) (le_max_left _ _)
      exact mul_le_mul h1 h2 (abs_nonneg _) (le_max_right _ _)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hσ] at this
    exact this
  choose Cl hCl using hconv
  refine ⟨C0 + ∑ l, Cl l, fun x hx => ?_⟩
  have hx' : x ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hx
  calc |matBaxterU Psi Q sigma k j x|
      = |Psi k j x - ∑ l, ∫ t in (0:ℝ)..sigma, Q k l t * Psi l j (x - t)| := rfl
    _ ≤ |Psi k j x| + |∑ l, ∫ t in (0:ℝ)..sigma, Q k l t * Psi l j (x - t)| := abs_sub _ _
    _ ≤ |Psi k j x| + ∑ l, |∫ t in (0:ℝ)..sigma, Q k l t * Psi l j (x - t)| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ C0 + ∑ l, Cl l := by
        gcongr with l _
        · exact hC0 x hx'
        · exact hCl l x hx

/-- **`hint` from regularity** — interval-integrability of `Qᵢₖ · matBaxterU Ψ Q σ ₖⱼ(r+·)` on `[0,σ]`,
from `Q` continuous and `Ψ` measurable + locally bounded.  Reduces (via `matBaxterU_measurable` +
`matBaxterU_bddOn`) to a bounded-measurable interval integrand times the continuous `Q`. -/
theorem matBaxterU_hint_of_regular {N : ℕ} (sigma : ℝ) (hσ : 0 ≤ sigma)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQcont : ∀ i k, Continuous (Q i k)) (hPsiMeas : ∀ l j, Measurable (Psi l j))
    (hPsiBdd : ∀ l j a b, ∃ C, ∀ x ∈ Set.uIcc a b, |Psi l j x| ≤ C)
    (i k j : Fin N) (r : ℝ) :
    IntervalIntegrable (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma := by
  have hMUmeas := matBaxterU_measurable sigma hσ Psi Q hQcont hPsiMeas k j
  obtain ⟨C, hC⟩ := matBaxterU_bddOn sigma hσ Psi Q hQcont hPsiBdd k j r (r + sigma) (by linarith)
  have hcompInt : IntervalIntegrable (fun t => matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma := by
    rw [intervalIntegrable_iff]
    have hfin : volume (Set.uIoc (0:ℝ) sigma) ≠ ⊤ :=
      ne_top_of_le_ne_top isCompact_uIcc.measure_ne_top (measure_mono Set.uIoc_subset_uIcc)
    refine Measure.integrableOn_of_bounded (M := C) hfin
      (hMUmeas.comp (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hσ] at ht
    rw [Real.norm_eq_abs]
    exact hC (r + t) (Set.mem_Icc.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  exact hcompInt.continuousOn_mul (hQcont i k).continuousOn

-- `matBaxterPsi_entry_measurable` / `matBaxterPsi_entry_bddOn` are generic Matrix machinery about the
-- glued `matBaxterPsi`; moved to the HSMixture layer (`HSMixture/MixtureSeedExtended.lean`, same
-- `FMSA.MixtureOzStar` namespace), re-used here by import.

/-- **`hint` for the constructed `matBaxterPsi`.**  Interval-integrability of
`(Qm t)ᵢₖ · matBaxterU Ψ Qₑ σ ₖⱼ(r+t)` on `[0,σ]`, for continuous matrix Baxter data `Qm, Fm` and the
glued `Ψ = matBaxterPsi (matBaxterPsiOuterFun σ Qm Fm) (fun _ _ v => −v) σ`.  Discharges the `hint`
side-condition of `matBaxterUQm_core_reduce` / `matBaxterUQm_eq_rPhi_of_momentSeed` for the constructed
solution: the glued `Ψ` is measurable + locally bounded (`matBaxterPsi_entry_measurable`/`_bddOn`), so
`matBaxterU_hint_of_regular` applies. -/
theorem matBaxterPsi_hint {N : ℕ} (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (Qm Fm : ℝ → Matrix (Fin N) (Fin N) ℝ) (hQ : Continuous Qm) (hF : Continuous Fm)
    (i k j : Fin N) (r : ℝ) :
    IntervalIntegrable (fun t => (Qm t) i k *
      matBaxterU (matBaxterPsi (fun i j r => (matBaxterPsiOuterFun sigma Qm Fm hQ hF r) i j)
        (fun _ _ v => -v) sigma) (fun i k s => (Qm s) i k) sigma k j (r + t)) volume 0 sigma := by
  have hcontOuter : Continuous (matBaxterPsiOuterFun sigma Qm Fm hQ hF) :=
    matBaxterPsiOuterFun_continuous sigma Qm Fm hQ hF
  exact matBaxterU_hint_of_regular sigma hsigma
    (matBaxterPsi (fun i j r => (matBaxterPsiOuterFun sigma Qm Fm hQ hF r) i j)
      (fun _ _ v => -v) sigma)
    (fun i k s => (Qm s) i k)
    (fun i k => by fun_prop)
    (fun l j => matBaxterPsi_entry_measurable _ _ sigma (fun k j => by fun_prop)
      (fun k j => by fun_prop) l j)
    (fun l j a b => matBaxterPsi_entry_bddOn _ _ sigma (fun k j => by fun_prop)
      (fun k j => by fun_prop) l j a b)
    i k j r

/-! ### The KDEF `hfact` — the real-space Baxter factorization at equal diameters -/

/-- **KDEF for an idempotent weight `W`** — with `Qᵢₖ = wᵢₖ·q0_poly` and `Kᵢⱼ = wᵢⱼ·baxterK`, the
matrix factorization `ρKᵢⱼ = Qᵢⱼ − matSelfConvᵢⱼ` reduces to the scalar `rho_baxterK_eq_q0_self_conv`,
because `matSelfConvᵢⱼ = (∑ₖ wᵢₖwⱼₖ)·(q0⋆q0) = wᵢⱼ·(q0⋆q0)` under the idempotency `W·Wᵀ = W`
(`∑ₖ wᵢₖwⱼₖ = wᵢⱼ`).  This is the algebraic heart of the equal-diameter matrix KDEF. -/
theorem matBaxterFactorization_of_idempotent {N : ℕ} (w : Matrix (Fin N) (Fin N) ℝ)
    (hidem : ∀ i j, ∑ k, w i k * w j k = w i j)
    {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    MatBaxterFactorization (fun i j v => w i j * baxterK eta sigma v)
      (fun i j u => w i j * q0_poly eta sigma rho u) rho sigma := by
  intro i j v hv
  have hscalar := rho_baxterK_eq_q0_self_conv hsigma heta heta_def hv
  have hself : matSelfConv (fun i j u => w i j * q0_poly eta sigma rho u) sigma v i j
      = w i j * ∫ t in v..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - v) := by
    rw [matSelfConv_apply]
    have hk : ∀ k : Fin N,
        (∫ t in v..sigma, (w i k * q0_poly eta sigma rho t) * (w j k * q0_poly eta sigma rho (t - v)))
        = (w i k * w j k) *
            ∫ t in v..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - v) := by
      intro k
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      ring
    simp_rw [hk]
    rw [← Finset.sum_mul, hidem i j]
  show rho * (w i j * baxterK eta sigma v)
    = w i j * q0_poly eta sigma rho v
      - matSelfConv (fun i j u => w i j * q0_poly eta sigma rho u) sigma v i j
  rw [hself]
  have hr : rho * (w i j * baxterK eta sigma v) = w i j * (rho * baxterK eta sigma v) := by ring
  rw [hr, hscalar]; ring

/-- The physical equal-diameter symmetric weight `wᵢⱼ = √(ρᵢρⱼ)/ρ` is idempotent (`ρ = ∑ₖρₖ`,
`ρₖ ≥ 0`): `∑ₖ wᵢₖwⱼₖ = √(ρᵢρⱼ)/ρ² · ∑ₖρₖ = √(ρᵢρⱼ)/ρ`. -/
theorem physWeight_idempotent {N : ℕ} (rhof : Fin N → ℝ) (hnonneg : ∀ k, 0 ≤ rhof k)
    {rho : ℝ} (hrho : rho = ∑ k, rhof k) (hpos : 0 < rho) (i j : Fin N) :
    ∑ k, (Real.sqrt (rhof i * rhof k) / rho) * (Real.sqrt (rhof j * rhof k) / rho)
      = Real.sqrt (rhof i * rhof j) / rho := by
  have hsplit : ∀ k, (Real.sqrt (rhof i * rhof k) / rho) * (Real.sqrt (rhof j * rhof k) / rho)
      = (Real.sqrt (rhof i * rhof j) / (rho * rho)) * rhof k := by
    intro k
    have hk2 : Real.sqrt (rhof k) * Real.sqrt (rhof k) = rhof k := Real.mul_self_sqrt (hnonneg k)
    rw [Real.sqrt_mul (hnonneg i) (rhof k), Real.sqrt_mul (hnonneg j) (rhof k),
      Real.sqrt_mul (hnonneg i) (rhof j)]
    field_simp
    linear_combination (Real.sqrt (rhof i) * Real.sqrt (rhof j)) * hk2
  simp_rw [hsplit]
  rw [← Finset.mul_sum, ← hrho]
  field_simp

/-- **Concrete equal-diameter KDEF `hfact`.**  With the physical symmetric Baxter factor
`Qᵢⱼ = √(ρᵢρⱼ)/ρ · q0_poly` and `Kᵢⱼ = √(ρᵢρⱼ)/ρ · baxterK` (`ρ = ∑ₖρₖ`), the matrix factorization
holds, reducing to the scalar `rho_baxterK_eq_q0_self_conv` via the idempotency of `√(ρᵢρⱼ)/ρ`.  This
discharges the `hfact` hypothesis of `matOzStar_of_shellClaims` / `matOzStar_of_regular` for the
concrete equal-diameter kernel. -/
theorem matBaxterFactorization_equalDiam {N : ℕ} (rhof : Fin N → ℝ) (hnonneg : ∀ k, 0 ≤ rhof k)
    {sigma eta rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (hrho : rho = ∑ k, rhof k) (hpos : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    MatBaxterFactorization
      (fun i j v => (Real.sqrt (rhof i * rhof j) / rho) * baxterK eta sigma v)
      (fun i j u => (Real.sqrt (rhof i * rhof j) / rho) * q0_poly eta sigma rho u) rho sigma :=
  matBaxterFactorization_of_idempotent (fun i j => Real.sqrt (rhof i * rhof j) / rho)
    (physWeight_idempotent rhof hnonneg hrho hpos) hsigma heta heta_def

/-! ### The shell bridge `hbridge` — the matrix OZFIX.19 for the weighted `c_HS`/`baxterK` pair -/

/-- `radial3d_conv` is linear in its first argument — the constant pulls through both nested
integrals (and through the `r ≤ 0` branch trivially). -/
theorem radial3d_conv_const_mul (c : ℝ) (f g : ℝ → ℝ) (r : ℝ) :
    radial3d_conv (fun t => c * f t) g r = c * radial3d_conv f g r := by
  unfold radial3d_conv
  by_cases hr : r ≤ 0
  · rw [if_pos hr, if_pos hr, mul_zero]
  · rw [if_neg hr, if_neg hr]
    have hstep : (∫ t in Set.Ioi (0:ℝ), t * (c * f t) * ∫ s in Set.Icc (|r - t|) (r + t), s * g s)
        = c * ∫ t in Set.Ioi (0:ℝ), t * f t * ∫ s in Set.Icc (|r - t|) (r + t), s * g s := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      ring
    rw [hstep]; ring

/-- **`hbridge` — the matrix OZFIX.19 for a weighted `c_HS`/`baxterK` pair.**  With `Φᵢₖ = wᵢₖ·c_HS`
and `Kᵢₖ = wᵢₖ·baxterK` (matching the KDEF weight of `matBaxterFactorization_of_idempotent`), the matrix
shell bridge `r·matRadialConv Φ G = matShellConv K G` holds: the weight `wᵢₖ` pulls out of both
`radial3d_conv` and the shell integral (`radial3d_conv_const_mul` + `integral_const_mul`), and each
per-entry identity is the scalar `radial3d_conv_eq_baxterK_shell` (with its per-entry integrability
`hshell`/`hjoint`, exactly as in `matShellBridge_fin_one_of_scalar`).  This discharges the `hbridge`
hypothesis of `matOzStar_of_shellClaims` / `matOzStar_of_regular` for the weighted kernel. -/
theorem matBridge_weighted {N : ℕ} (w : Matrix (Fin N) (Fin N) ℝ) {eta sigma : ℝ} (hsigma : 0 < sigma)
    (G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {r : ℝ} (hr : 0 < r) (i j : Fin N)
    (hshell : ∀ k, ∀ t ∈ Set.Ioi (0:ℝ),
      IntervalIntegrable (oddExt (G k j)) volume (r - t) (r + t))
    (hjoint : ∀ k, Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * c_HS eta sigma s) s
        * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)))
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma)))) :
    r * matRadialConv (fun i j v => w i j * c_HS eta sigma v) G r i j
      = matShellConv (fun i j v => w i j * baxterK eta sigma v) G sigma r i j := by
  apply matRadialConv_eq_matShellConv
  intro k
  have hsc := radial3d_conv_eq_baxterK_shell hsigma hr (hshell k) (hjoint k)
  rw [radial3d_conv_const_mul,
    show r * (w i k * radial3d_conv (c_HS eta sigma) (G k j) r)
      = w i k * (r * radial3d_conv (c_HS eta sigma) (G k j) r) from by ring, hsc,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  ring

/-! ### The equal-diameter matrix OZ★ — direct reduction to the scalar `baxterPsi_ozstar`

For the physical **symmetric** weight `wᵢⱼ = √(ρᵢρⱼ)/ρ` (chained-idempotent, `∑ₖ wᵢₖwₖⱼ = wᵢⱼ`), the whole
solution is `wᵢⱼ·(scalar)`: `Ψᵢⱼ = wᵢⱼ·baxterPsi`, `Φᵢⱼ = wᵢⱼ·c_HS`.  Then `MatOZStar` reduces
**directly** to the proved scalar `baxterPsi_ozstar` — the species sum in `matRadialConv` collapses via
`W·W = W`.  This closes the equal-diameter matrix OZ★ for **any densities**, bypassing the
seed/`hclaimA`/KDEF/bridge route (which those pieces build for the general-`N`, unequal-diameter case). -/

/-- `radial3d_conv` is linear in its **second** argument (the constant pulls through the inner shell
integral, then the outer). -/
theorem radial3d_conv_const_mul_right (c : ℝ) (f g : ℝ → ℝ) (r : ℝ) :
    radial3d_conv f (fun s => c * g s) r = c * radial3d_conv f g r := by
  unfold radial3d_conv
  by_cases hr : r ≤ 0
  · rw [if_pos hr, if_pos hr, mul_zero]
  · rw [if_neg hr, if_neg hr]
    have hinner : ∀ t : ℝ, (∫ s in Set.Icc (|r - t|) (r + t), s * (c * g s))
        = c * ∫ s in Set.Icc (|r - t|) (r + t), s * g s := by
      intro t
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
      ring
    have hstep : (∫ t in Set.Ioi (0:ℝ), t * f t * ∫ s in Set.Icc (|r - t|) (r + t), s * (c * g s))
        = c * ∫ t in Set.Ioi (0:ℝ), t * f t * ∫ s in Set.Icc (|r - t|) (r + t), s * g s := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      show t * f t * (∫ s in Set.Icc (|r - t|) (r + t), s * (c * g s))
        = c * (t * f t * ∫ s in Set.Icc (|r - t|) (r + t), s * g s)
      rw [hinner t]; ring
    rw [hstep]; ring

/-- **Equal-diameter matrix OZ★ — direct reduction to the scalar `baxterPsi_ozstar`.**  For a
chained-idempotent weight `W` (`∑ₖ wᵢₖwₖⱼ = wᵢⱼ`), the weighted solution `Ψᵢⱼ = wᵢⱼ·baxterPsi`,
`Φᵢⱼ = wᵢⱼ·c_HS` satisfies `MatOZStar Ψ Φ ρ`: the `matRadialConv` species sum collapses (`wᵢₖwₖⱼ` pulls
out of `radial3d_conv` in both arguments, then `W·W = W`), and each entry is `wᵢⱼ·baxterPsi_ozstar`. -/
theorem matOzStar_equalDiam {N : ℕ} (w : Matrix (Fin N) (Fin N) ℝ)
    (hidem : ∀ i j, ∑ k, w i k * w k j = w i j)
    {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    MatOZStar (fun i j r => w i j * baxterPsi eta sigma rho r)
      (fun i j r => w i j * c_HS eta sigma r) rho := by
  intro i j r hr
  have hscalar := baxterPsi_ozstar hsigma heta heta_def r hr
  have hsum : matRadialConv (fun i j r => w i j * c_HS eta sigma r)
      (fun k l x => (fun i j r => w i j * baxterPsi eta sigma rho r) k l x / x) r i j
      = w i j * radial3d_conv (c_HS eta sigma) (fun x => baxterPsi eta sigma rho x / x) r := by
    rw [matRadialConv_apply]
    have hk : ∀ k : Fin N, radial3d_conv (fun r => w i k * c_HS eta sigma r)
        (fun x => w k j * baxterPsi eta sigma rho x / x) r
        = (w i k * w k j)
          * radial3d_conv (c_HS eta sigma) (fun x => baxterPsi eta sigma rho x / x) r := by
      intro k
      rw [radial3d_conv_const_mul,
        show (fun x => w k j * baxterPsi eta sigma rho x / x)
          = (fun x => w k j * (baxterPsi eta sigma rho x / x)) from by funext x; rw [mul_div_assoc],
        radial3d_conv_const_mul_right]
      ring
    simp_rw [hk]
    rw [← Finset.sum_mul, hidem i j]
  show w i j * baxterPsi eta sigma rho r
    = r * (w i j * c_HS eta sigma r)
      + rho * (r * matRadialConv (fun i j r => w i j * c_HS eta sigma r)
        (fun k l x => (fun i j r => w i j * baxterPsi eta sigma rho r) k l x / x) r i j)
  rw [hsum, hscalar]; ring

/-- The physical symmetric weight `√(ρᵢρⱼ)/ρ` is chained-idempotent (`physWeight_idempotent` +
`mul_comm` inside the `√`). -/
theorem physWeight_idempotent_chained {N : ℕ} (rhof : Fin N → ℝ) (hnonneg : ∀ k, 0 ≤ rhof k)
    {rho : ℝ} (hrho : rho = ∑ k, rhof k) (hpos : 0 < rho) (i j : Fin N) :
    ∑ k, (Real.sqrt (rhof i * rhof k) / rho) * (Real.sqrt (rhof k * rhof j) / rho)
      = Real.sqrt (rhof i * rhof j) / rho := by
  have hcongr : (∑ k, (Real.sqrt (rhof i * rhof k) / rho) * (Real.sqrt (rhof k * rhof j) / rho))
      = ∑ k, (Real.sqrt (rhof i * rhof k) / rho) * (Real.sqrt (rhof j * rhof k) / rho) :=
    Finset.sum_congr rfl (fun k _ => by rw [mul_comm (rhof k) (rhof j)])
  rw [hcongr]
  exact physWeight_idempotent rhof hnonneg hrho hpos i j

/-- **Concrete equal-diameter matrix OZ★.**  With the physical symmetric normalization
`Ψᵢⱼ = √(ρᵢρⱼ)/ρ·baxterPsi`, `Φᵢⱼ = √(ρᵢρⱼ)/ρ·c_HS` (`ρ = ∑ₖρₖ`), `MatOZStar` holds — the mixture OZ★
solution for equal diameters, at **any** densities.  This is the equal-diameter payoff: the matrix
mixture Ornstein–Zernike identity, reduced entirely to the (axiom-free) scalar `baxterPsi_ozstar`. -/
theorem matOzStar_equalDiam_phys {N : ℕ} (rhof : Fin N → ℝ) (hnonneg : ∀ k, 0 ≤ rhof k)
    {sigma eta rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (hrho : rho = ∑ k, rhof k) (hpos : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    MatOZStar (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * baxterPsi eta sigma rho r)
      (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) rho :=
  matOzStar_equalDiam (fun i j => Real.sqrt (rhof i * rhof j) / rho)
    (physWeight_idempotent_chained rhof hnonneg hrho hpos) hsigma heta heta_def

/-! ### Unequal-diameter direction — the odd structure and the shell → flat conversion

For **unequal diameters** the `wᵢⱼ·scalar` factorization fails (each pair `(i,j)` has its own `σ_ij`,
`λ_ij`, and DCF shape), so the direct reduction above does not apply — the coupled seed route is genuinely
needed.  These lemmas are the *diameter-agnostic* structural building blocks of the shell form: the
constructed `matBaxterPsi` is **odd**, hence `oddExt(Ψ/·) = Ψ`, which collapses the OZ★/`hclaimA` shell
integrands to the flat renewal form.  (What remains genuinely open for unequal diameters: the flat
matrix Wertheim–Thiele seed `matBaxterUQm = r·c_HS,ij` with per-pair DCF, and — for the `matSelfConv`
reindex in `hclaimA` — the fact that the unequal-diameter Baxter factor `Q` is **not symmetric**
(`Qᵢⱼ` and `Qⱼᵢ` have opposite `λ`-shift), which the equal-diameter symmetric weight sidesteps.) -/

/-- **The glued `matBaxterPsi` is odd** — `Ψᵢⱼ(−v) = −Ψᵢⱼ(v)` — whenever the core `Ψcore` is odd (the
reflection branch `−Ψouter(−v)` is exactly what makes it odd across `±σ`).  Holds for any diameters. -/
theorem matBaxterPsi_odd {N : ℕ} (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {sigma : ℝ}
    (hsigma : 0 < sigma) (hPc : ∀ i j v, Pc i j (-v) = -Pc i j v) (i j : Fin N) (v : ℝ) :
    matBaxterPsi Po Pc sigma i j (-v) = -matBaxterPsi Po Pc sigma i j v := by
  unfold matBaxterPsi
  by_cases h1 : sigma ≤ v
  · have hn1 : ¬ sigma ≤ -v := by intro h; linarith
    have hn2 : -v ≤ -sigma := by linarith
    rw [if_pos h1, if_neg hn1, if_pos hn2, neg_neg]
  · by_cases h2 : v ≤ -sigma
    · have hp1 : sigma ≤ -v := by linarith
      rw [if_neg h1, if_pos h2, if_pos hp1, neg_neg]
    · have hn1 : ¬ sigma ≤ -v := fun h => h2 (by linarith)
      have hn2 : ¬ -v ≤ -sigma := fun h => h1 (by linarith)
      rw [if_neg h1, if_neg h2, if_neg hn1, if_neg hn2, hPc]

/-- **`oddExt(ψ/·) = ψ` for odd `ψ` (`v ≠ 0`)** — the shell weight `oddExt(fun x => ψ x/x)(v)` collapses
to `ψ(v)` when `ψ` is odd (`v/|v|·ψ(|v|) = ψ(v)`), so the OZ★/`hclaimA` shell terms `oddExt(Ψₖⱼ/·)(r±u)`
are just `Ψₖⱼ(r±u)`.  Holds for any diameters. -/
theorem oddExt_div_self_of_odd {ψ : ℝ → ℝ} (hodd : ∀ x, ψ (-x) = -ψ x) {v : ℝ} (hv : v ≠ 0) :
    oddExt (fun x => ψ x / x) v = ψ v := by
  unfold oddExt
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · show v * (ψ |v| / |v|) = ψ v
    rw [abs_of_neg hneg, hodd v]; field_simp
  · show v * (ψ |v| / |v|) = ψ v
    rw [abs_of_pos hpos]; field_simp

/-- **Shell → flat, for odd `Ψ`.**  The OZ★/`hclaimA` shell integrand
`Qᵢₖ(u)·(oddExt(Ψₖⱼ/·)(r−u) + oddExt(Ψₖⱼ/·)(r+u))` equals the flat form `Qᵢₖ(u)·(Ψₖⱼ(r−u) + Ψₖⱼ(r+u))`
(a.e. `u`, the exceptions `u = ±r` being null) whenever every `Ψₖⱼ` is odd — via `oddExt_div_self_of_odd`.
This converts the shell-form `hclaimA` to the flat renewal form, for **any** diameters. -/
theorem shell_eq_flat_of_odd {N : ℕ} (Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hodd : ∀ k j x, Psi k j (-x) = -Psi k j x) (sigma : ℝ) (i k j : Fin N) (r : ℝ) :
    (∫ u in (0:ℝ)..sigma, Q i k u
        * (oddExt (fun x => Psi k j x / x) (r - u) + oddExt (fun x => Psi k j x / x) (r + u)))
      = ∫ u in (0:ℝ)..sigma, Q i k u * (Psi k j (r - u) + Psi k j (r + u)) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hr' : ∀ᵐ u : ℝ, u ≠ r := by rw [MeasureTheory.ae_iff]; simp
  have hr'' : ∀ᵐ u : ℝ, u ≠ -r := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hr', hr''] with u hu1 hu2 _
  rw [oddExt_div_self_of_odd (hodd k j) (sub_ne_zero.mpr (Ne.symm hu1)),
    oddExt_div_self_of_odd (hodd k j) (fun h => hu2 (by linarith))]

/-- **`matSelfConv` in shifted form (obstruction (b), made precise).**  Substituting `τ = t − u`,
`matSelfConvᵢⱼ(u) = ∑ₖ ∫₀^{σ−u} Qᵢₖ(τ+u)·Qⱼₖ(τ) dτ` — the `+u` shift lands on the **i**-factor only.
Hence `matSelfConvⱼᵢ(u) = ∑ₖ ∫₀^{σ−u} Qⱼₖ(τ+u)·Qᵢₖ(τ) dτ` shifts the **j**-factor instead: the two are
**not** equal for a non-symmetric `Q` (the transpose swaps which factor carries the `+u`).  This pins
the unequal-diameter obstruction (b): the shell-form `hclaimA` weights both `r±u` terms by
`matSelfConvᵢₖ`, but the seed's reindex (`matDblConv_reindex`) supplies `matSelfConvᵢₖ` for `r+u` and
`matSelfConvₖᵢ` for `r−u` — so discharging `hclaimA` from the seed requires `matSelfConv` symmetric,
which holds for the equal-diameter symmetric factor but fails for the unequal-diameter one
(`λ_ij = −λ_ji`).  Resolving it needs either a symmetrised matrix seed (transpose in the second Baxter
convolution) or a genuinely new reindex — research-scale. -/
theorem matSelfConv_shift {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma u : ℝ) (i j : Fin N) :
    matSelfConv Q sigma u i j = ∑ k, ∫ τ in (0:ℝ)..(sigma - u), Q i k (τ + u) * Q j k τ := by
  rw [matSelfConv_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := sigma - u)
    (fun t => Q i k t * Q j k (t - u)) u
  have he : sigma - u + u = sigma := by ring
  rw [zero_add, he] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  show Q i k (x + u) * Q j k (x + u - u) = Q i k (x + u) * Q j k x
  rw [add_sub_cancel_right]

/-! ### Prototype: the symmetrised matrix seed (the constructive fix for obstruction (b))

The current `matBaxterUQm` uses `Q i k` in its second convolution, giving a *chained* double term
`Q·Q·Ψ` that only matches `matSelfConv` (`Q⋆Qᵀ`) when `Q` is symmetric.  The fix is to transpose the
inner factor of the second convolution — `matBaxterUt` below uses `Qₘᵢ` — so the two `Q`-factors share
their **second** index, landing on the correlation `matSelfConv` structure for *any* `Q`.  These
lemmas prototype the corrected seed and prove it is a faithful generalization (it coincides with the
current seed exactly on symmetric `Q`, hence at `N = 1` and for the equal-diameter factor). -/

-- `matBaxterUt` (the transposed first Baxter convolution `Ψ ⋆ Qᵀ`) is generic Matrix machinery;
-- it has been moved to the HSMixture layer (`HSMixture/MixtureSeedExtended.lean`, same
-- `FMSA.MixtureOzStar` namespace) and is re-used here by import.

/-- **Symmetrised matrix second Baxter convolution** — `matBaxterU` with the transposed `matBaxterUt`
as the inner second factor. -/
def matBaxterUQmSym {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (i j : Fin N)
    (r : ℝ) : ℝ :=
  matBaxterU Psi Q sigma i j r
    - ∑ k, ∫ t in (0:ℝ)..sigma, Q i k t * matBaxterUt Psi Q sigma k j (r + t)

/-- **The double term is the correlation `Q⋆Qᵀ`.**  Unfolding the symmetrised seed, the second-order
term is `∑ₖ ∫ Qᵢₖ(t)·(Ψₖⱼ(r+t) − ∑ₘ ∫ Qₘₖ(s)·Ψₘⱼ(r+t−s))` — both `Qᵢₖ` and `Qₘₖ` carry the **second**
index `k`, exactly the `matSelfConvᵢₘ(u) = ∑ₖ ∫ Qᵢₖ(t)Qₘₖ(t−u)` shape (contrast the current
`matBaxterUQm`, whose inner factor `Qₖₘ` carries index `m`, giving the chained `Q·Q·Ψ`). -/
theorem matBaxterUQmSym_unfold {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (i j : Fin N) (r : ℝ) :
    matBaxterUQmSym Psi Q sigma i j r
      = matBaxterU Psi Q sigma i j r
        - ∑ k, ∫ t in (0:ℝ)..sigma, Q i k t
            * (Psi k j (r + t) - ∑ m, ∫ s in (0:ℝ)..sigma, Q m k s * Psi m j (r + t - s)) :=
  rfl

/-- **`matBaxterUt = matBaxterU` for symmetric `Q`** — the transpose is invisible when `Qᵢⱼ = Qⱼᵢ`. -/
theorem matBaxterUt_of_symm {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsym : ∀ i j, Q i j = Q j i) (i j : Fin N) (r : ℝ) :
    matBaxterUt Psi Q sigma i j r = matBaxterU Psi Q sigma i j r := by
  unfold matBaxterUt matBaxterU
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [hsym m i]

/-- **`matBaxterUQmSym = matBaxterUQm` for symmetric `Q`** — the symmetrised seed is a *faithful*
generalization: it coincides with the current seed exactly when `Q` is symmetric (the equal-diameter
factor, and `N = 1`, where `Q` at `Fin 1` is trivially symmetric), and differs — correctly landing on
`matSelfConv` — only when `Q` is asymmetric (unequal diameters), which is precisely obstruction (b). -/
theorem matBaxterUQmSym_of_symm {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsym : ∀ i j, Q i j = Q j i) (i j : Fin N) (r : ℝ) :
    matBaxterUQmSym Psi Q sigma i j r = matBaxterUQm Psi Q sigma i j r := by
  unfold matBaxterUQmSym matBaxterUQm
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [matBaxterUt_of_symm Psi Q sigma hsym k j (r + t)]

/-! ### Refactor: the asymmetric-`matSelfConv` shell assembly (consumes the corrected seed)

The corrected seed produces `matSelfConvᵢₖ` on the `r+u` arm and its transpose `matSelfConvₖᵢ` on the
`r−u` arm.  `matShellConvAsym` (two kernels) captures that, with an asymmetric KDEF split.  The whole
detour collapses back to the *current* symmetric assembly once `matSelfConv` symmetry
(`matSelfConvᵢₖ = matSelfConvₖᵢ`) is available — which is a **physical** property of the Baxter factor
(`Q̂(k)·Q̂ᵀ(−k) = I − Ĉ`, symmetric because the DCF `Ĉ` is), holding for **any** diameters, not just
the equal-diameter symmetric one.  So the unequal-diameter route is: corrected seed
(`matBaxterUQmSym`) + `matSelfConv` symmetry ⇒ symmetric `hclaimA` ⇒ existing `matOzStar_of_shellClaims`. -/

/-- **Asymmetric matrix shell convolution** — `Kp` weights `oddExt(Gₖⱼ)(r+u)`, `Km` weights
`oddExt(Gₖⱼ)(r−u)` (the current `matShellConv` is the diagonal `Kp = Km`). -/
def matShellConvAsym {N : ℕ} (Kp Km G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ k, ∫ u in (0:ℝ)..sigma,
    (Kp i k u * oddExt (G k j) (r + u) + Km i k u * oddExt (G k j) (r - u))

/-- **Asymmetric KDEF split.**  With `ρKp = Q − matSelfConv` (for `r+u`) and `ρKm = Q − matSelfConvᵀ`
(for `r−u`), `ρ·matShellConvAsym Kp Km` splits into the linear `Q`-shell minus the asymmetric
self-convolution shell — exactly the form the corrected seed supplies. -/
theorem matShellConvAsym_kdef_split {N : ℕ} (Kp Km Q G : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {rho sigma r : ℝ} (hsigma : 0 < sigma) (i j : Fin N)
    (hfactP : ∀ k v, v ∈ Set.Ioo (0:ℝ) sigma → rho * Kp i k v = Q i k v - matSelfConv Q sigma v i k)
    (hfactM : ∀ k v, v ∈ Set.Ioo (0:ℝ) sigma → rho * Km i k v = Q i k v - matSelfConv Q sigma v k i)
    (hAint : ∀ k, IntervalIntegrable
      (fun u => Q i k u * oddExt (G k j) (r + u) + Q i k u * oddExt (G k j) (r - u))
      MeasureTheory.volume 0 sigma)
    (hBint : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u i k * oddExt (G k j) (r + u)
        + matSelfConv Q sigma u k i * oddExt (G k j) (r - u)) MeasureTheory.volume 0 sigma) :
    rho * matShellConvAsym Kp Km G sigma r i j
      = (∑ k, ∫ u in (0:ℝ)..sigma,
            (Q i k u * oddExt (G k j) (r + u) + Q i k u * oddExt (G k j) (r - u)))
        - ∑ k, ∫ u in (0:ℝ)..sigma,
            (matSelfConv Q sigma u i k * oddExt (G k j) (r + u)
              + matSelfConv Q sigma u k i * oddExt (G k j) (r - u)) := by
  rw [matShellConvAsym, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hAint k) (hBint k)]
  have hne : ∀ᵐ (x : ℝ), x ≠ sigma := by
    rw [MeasureTheory.ae_iff]; simp [MeasureTheory.measure_singleton]
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hsigma.le]
  filter_upwards [hne] with u hune hmem
  have hu : u ∈ Set.Ioo (0:ℝ) sigma := ⟨hmem.1, lt_of_le_of_ne hmem.2 hune⟩
  show rho * (Kp i k u * oddExt (G k j) (r + u) + Km i k u * oddExt (G k j) (r - u))
      = (Q i k u * oddExt (G k j) (r + u) + Q i k u * oddExt (G k j) (r - u))
        - (matSelfConv Q sigma u i k * oddExt (G k j) (r + u)
            + matSelfConv Q sigma u k i * oddExt (G k j) (r - u))
  rw [show rho * (Kp i k u * oddExt (G k j) (r + u) + Km i k u * oddExt (G k j) (r - u))
        = (rho * Kp i k u) * oddExt (G k j) (r + u) + (rho * Km i k u) * oddExt (G k j) (r - u)
      from by ring, hfactP k u hu, hfactM k u hu]
  ring

/-- **The asymmetric shell collapses to the symmetric one when the kernels agree** (`Kp = Km`).  So
`matShellConvAsym` generalizes `matShellConv`; the asymmetric `matSelfConv` term equals the symmetric
one exactly under `matSelfConv` symmetry — the physical Baxter-factor property. -/
theorem matShellConvAsym_diag {N : ℕ} (K G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ)
    (i j : Fin N) :
    matShellConvAsym K K G sigma r i j = matShellConv K G sigma r i j := by
  unfold matShellConvAsym matShellConv
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  ring

/-- **The corrected seed's asymmetric `matSelfConv` shell term = the symmetric one, under `matSelfConv`
symmetry.**  When `matSelfConvᵢₖ = matSelfConvₖᵢ` (the physical Baxter-factor property — `Q̂Q̂ᵀ(−k) = I−Ĉ`
symmetric since the DCF is), the corrected seed's asymmetric shell term coincides with the symmetric
term that `matOzStar_of_shellClaims`/`matShellConv_kdef_split` consume.  Hence **corrected seed +
`matSelfConv` symmetry ⇒ the existing symmetric assembly applies verbatim, for any diameters.** -/
theorem matSelfConv_shell_symm {N : ℕ} (Q G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ)
    (hsym : ∀ i k u, matSelfConv Q sigma u i k = matSelfConv Q sigma u k i) (i j : Fin N) :
    (∑ k, ∫ u in (0:ℝ)..sigma, (matSelfConv Q sigma u i k * oddExt (G k j) (r + u)
        + matSelfConv Q sigma u k i * oddExt (G k j) (r - u)))
      = ∑ k, ∫ u in (0:ℝ)..sigma,
          matSelfConv Q sigma u i k * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)) := by
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [hsym k i u]
  ring

/-! ### `matSelfConv` symmetry from a DCF-symmetry hypothesis — closing obstruction (b) -/

/-- **`matSelfConv` symmetry from the DCF-symmetry hypothesis.**  The physical Baxter factor satisfies
`Q̂(k)·Q̂ᵀ(−k) = I − Ĉ`, symmetric because the DCF `Ĉ` is (`cᵢⱼ = cⱼᵢ`).  In real space this is exactly
`hMsym`: the two-time self-correlation kernel `∑ₗ Qᵢₗ(t)·Qₖₗ(s)` is symmetric in its time arguments
`(t, s)` (not algebraic — `matSelfConv_shift` shows it fails for arbitrary `Q`).  From it,
`matSelfConvᵢₖ = matSelfConvₖᵢ`: move the species sum inside (`integral_finsetSum`), swap `(t, t−u)` via
`hMsym`, `mul_comm` back to the transpose. -/
theorem matSelfConv_symm_of_corrSymm {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma u : ℝ)
    (hMsym : ∀ (i k : Fin N) (t s : ℝ), ∑ l, Q i l t * Q k l s = ∑ l, Q i l s * Q k l t)
    (hint : ∀ (a b l : Fin N),
      IntervalIntegrable (fun t => Q a l t * Q b l (t - u)) MeasureTheory.volume u sigma)
    (i k : Fin N) :
    matSelfConv Q sigma u i k = matSelfConv Q sigma u k i := by
  rw [matSelfConv_apply, matSelfConv_apply,
    ← intervalIntegral.integral_finsetSum (fun l _ => hint i k l),
    ← intervalIntegral.integral_finsetSum (fun l _ => hint k i l)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hMsym i k t (t - u)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- **The unequal-diameter route, reduced to one physical hypothesis.**  From the DCF-symmetry
hypothesis `hMsym` (+ integrability), the corrected seed's *asymmetric* `matSelfConv` shell term equals
the *symmetric* term that the existing `matOzStar_of_shellClaims`/`matShellConv_kdef_split` consume.
So: corrected seed (`matBaxterUQmSym`) + `hMsym` ⇒ symmetric `hclaimA` ⇒ the existing assembly, for
**any** diameters — the whole unequal-diameter obstruction (b) collapses to the single physical
hypothesis `hMsym` (the real-space DCF symmetry `Q̂Q̂ᵀ(−k) = I − Ĉ`). -/
theorem matSelfConv_shell_symm_of_corrSymm {N : ℕ} (Q G : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma r : ℝ)
    (hMsym : ∀ (i k : Fin N) (t s : ℝ), ∑ l, Q i l t * Q k l s = ∑ l, Q i l s * Q k l t)
    (hint : ∀ (u : ℝ) (a b l : Fin N),
      IntervalIntegrable (fun t => Q a l t * Q b l (t - u)) MeasureTheory.volume u sigma)
    (i j : Fin N) :
    (∑ k, ∫ u in (0:ℝ)..sigma, (matSelfConv Q sigma u i k * oddExt (G k j) (r + u)
        + matSelfConv Q sigma u k i * oddExt (G k j) (r - u)))
      = ∑ k, ∫ u in (0:ℝ)..sigma,
          matSelfConv Q sigma u i k * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)) :=
  matSelfConv_shell_symm Q G sigma r
    (fun i k u => matSelfConv_symm_of_corrSymm Q sigma u hMsym (hint u) i k) i j

/-- **`hMsym` for a separable Baxter factor `Qᵢₗ = wᵢₗ·q̂`.**  When every entry is one common profile
`q̂` scaled by a weight, the two-time self-correlation `∑ₗ Qᵢₗ(t)Qₖₗ(s)` is symmetric in `(t, s)` term
by term (`wᵢₗwₖₗ·q̂(t)q̂(s)` commutes) — so `hMsym` holds with no factorization input.  This is exactly
the equal-diameter case: all pairs share one profile. -/
theorem hMsym_of_separable {N : ℕ} (w : Matrix (Fin N) (Fin N) ℝ) (qhat : ℝ → ℝ) (i k : Fin N)
    (t s : ℝ) :
    ∑ l, (w i l * qhat t) * (w k l * qhat s) = ∑ l, (w i l * qhat s) * (w k l * qhat t) := by
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- **`hMsym` for the concrete `q0MixEntry`, equal diameters.**  With a common diameter and the
column-weighted PY coefficients (`X.Q0 i l = ρₗ·a`, `X.Qpp l = ρₗ·b`, as in `q0MixEntry_rowSum_eq_q0_poly`),
every entry is `q0MixEntryᵢₗ = ρₗ·(indicator quadratic)` — separable — so the DCF-symmetry hypothesis
`hMsym` holds for the concrete kernel.  This discharges `matSelfConv_symm_of_corrSymm`'s hypothesis,
closing obstruction (b) for the concrete equal-diameter factor.  (For *unequal* diameters the factor is
not separable — each pair has its own `σ_il`, `λ_il` profile — so `hMsym` there genuinely needs the WH
factorization of the symmetric PY DCF.) -/
theorem q0MixEntry_hMsym_equalDiam {N M : ℕ} (X : Mix N M) {sigma : ℝ} (hsig : ∀ k, X.σ k = sigma)
    {a b : ℝ} (hQ0 : ∀ i l, X.Q0 i l = X.ρ l * a) (hQpp : ∀ l, X.Qpp l = X.ρ l * b)
    (i k : Fin N) (t s : ℝ) :
    ∑ l, q0MixEntry X i l t * q0MixEntry X k l s
      = ∑ l, q0MixEntry X i l s * q0MixEntry X k l t := by
  have hsep : ∀ (m l : Fin N) (u : ℝ), q0MixEntry X m l u
      = X.ρ l * Set.indicator (Set.Icc (0:ℝ) sigma)
          (fun u => a * (u - sigma) + b * (u - sigma) ^ 2 / 2) u := by
    intro m l u
    have hlam : X.lam m l = 0 := by simp only [Mix.lam, hsig]; ring
    have hR : X.R m l = sigma := by simp only [Mix.R, hsig]; ring
    unfold q0MixEntry
    simp only [hlam, hR, hQ0, hQpp]
    by_cases h : u ∈ Set.Icc (0:ℝ) sigma
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
  simp_rw [hsep]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-! ### `matSelfConv` symmetry from the WH factorization (the non-separable / unequal-diameter route)

`hMsym` (the two-variable `∑ₗ Qᵢₗ(t)Qₖₗ(s)` symmetry) turned out to be **stronger** than the WH
factorization supplies: its Fourier content is `∑ₗ Q̂ᵢₗ(ω)Q̂ₖₗ(ν)` symmetric in `ω ↔ ν`, whereas the WH
factorization only gives the *single-variable* `Q̂(k)·Q̂ᵀ(−k) = I − Ĉ` symmetric.  So for a non-separable
`Q`, `hMsym` need not hold — but the object actually needed, `matSelfConv` symmetry, still does, and
follows from the factorization directly.  These lemmas take that route: the WH factorization (`hfact`:
on the core `matSelfConv` *is* the DCF matrix `C`) plus DCF symmetry (`hCsym`) give `matSelfConv`
symmetry, for **any** diameters. -/

/-- **`matSelfConv` symmetry from the WH factorization + DCF symmetry.**  On the core, `matSelfConv` is
the DCF matrix `C` (the real-space content of `Cmix0 = I − Q̂₀Q̂₀ᵀ(−k)`, MRS.6); the DCF is symmetric
(`Cᵢₖ = Cₖᵢ`, physically `cᵢⱼ = cⱼᵢ`), so `matSelfConv` inherits the symmetry — the single-variable route
that works for the *unequal-diameter* (non-separable) factor, unlike `hMsym`. -/
theorem matSelfConv_symm_of_dcf {N : ℕ} (Q C : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hCsym : ∀ i k u, C i k u = C k i u)
    (hfact : ∀ i k u, u ∈ Set.Ioo (0:ℝ) sigma → matSelfConv Q sigma u i k = C i k u)
    (i k : Fin N) (u : ℝ) (hu : u ∈ Set.Ioo (0:ℝ) sigma) :
    matSelfConv Q sigma u i k = matSelfConv Q sigma u k i := by
  rw [hfact i k u hu, hfact k i u hu, hCsym i k u]

/-- **The unequal-diameter route via the factorization.**  On the core the corrected seed's asymmetric
`matSelfConv` shell term equals the symmetric term the existing assembly consumes — from the WH
factorization (`hfact`) + DCF symmetry (`hCsym`), with **no** separability assumption.  So obstruction
(b) is discharged for *any* diameters, modulo the (existing, Fourier-space) `Cmix0_factorization` cast to
its real-space core form. -/
theorem matSelfConv_shell_symm_of_dcf {N : ℕ} (Q C G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {sigma : ℝ}
    (r : ℝ) (hsigma : 0 < sigma)
    (hCsym : ∀ i k u, C i k u = C k i u)
    (hfact : ∀ i k u, u ∈ Set.Ioo (0:ℝ) sigma → matSelfConv Q sigma u i k = C i k u)
    (i j : Fin N) :
    (∑ k, ∫ u in (0:ℝ)..sigma, (matSelfConv Q sigma u i k * oddExt (G k j) (r + u)
        + matSelfConv Q sigma u k i * oddExt (G k j) (r - u)))
      = ∑ k, ∫ u in (0:ℝ)..sigma,
          matSelfConv Q sigma u i k * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u)) := by
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ u : ℝ, u ≠ sigma := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with u hune hmem
  rw [Set.uIoc_of_le hsigma.le] at hmem
  have hu : u ∈ Set.Ioo (0:ℝ) sigma := ⟨hmem.1, lt_of_le_of_ne hmem.2 hune⟩
  rw [matSelfConv_symm_of_dcf Q C sigma hCsym hfact k i u hu]
  ring

/-- **Scoping the `Cmix0_factorization → matSelfConv` cast (VALID implication, but see the ⚠ below).**
`matSelfConv` symmetry would factor into:

* `hTsym` — the **momentum** symmetry of `Tfun z = Q̂₀(z)·Q̂₀ᵀ(−z)`: `(Tfun z)ᵢₖ = (Tfun z)ₖᵢ`.  Proved
  for the physical factor: `MixtureRealSpace.Qphys_T0_isSymm` / the entrywise `Qphys_Cmix0_entry_symm`,
  both from `swap_offdiag_of_keys` (MRS.7).  **This is the momentum-space discharge of obstruction (b).**

* `hbridge` — the **transform bridge**: `matSelfConvᵢₖ(·)` is the inverse transform of `z ↦ (Tfun z)ᵢₖ`.

⚠ **These two hypotheses cannot BOTH hold for the function-part `Q = q0MixEntry`** (2026-08-03, settled).
`swap`/`hTsym` is about the FULL momentum product `Q̂₀ = I − ρ_geo·q̂` (identity `δ` + `ρ_geo` weights); but
`matSelfConv`'s transform is the *unweighted function-part* product `∑ₗ q̂ᵢₗ(z)q̂ₖₗ(−z)`, which is NOT
symmetric (numerically ~0.02; identity `δ` terms essential).  So with `Tfun` = full product `hbridge`
fails, and with `Tfun` = function-part product `hTsym` fails — the reduction is unsatisfiable for the
bare `Q`.  **The CORRECT symmetric object is the DCF `Cmix0` itself** (its off-diagonal is a genuine
function — the `δ` sits only on the diagonal), symmetric via `Qphys_Cmix0_entry_symm`.  The Baxter
relation is `Ĉ₀ᵢₖ = q̂ᵢₖ(z) + q̂ₖᵢ(−z) − matCorrᵢₖ(z)` (i≠k): the seed must produce `Ĉ₀` (the linear `q̂`
terms INCLUDED), not `matSelfConv` alone; then `Qphys_Cmix0_entry_symm` closes it.  So the momentum side
is done; the remaining real-space work is the corrected `hfact` (`seed-output = Ĉ₀`, with the linear
terms), NOT the false `matSelfConv = Ĉ₀`. -/
theorem matSelfConv_symm_of_transform {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (Tfun : ℂ → Matrix (Fin N) (Fin N) ℂ) (InvT : (ℂ → ℂ) → (ℝ → ℝ))
    (hbridge : ∀ i k, (fun u => matSelfConv Q sigma u i k) = InvT (fun z => Tfun z i k))
    (hTsym : ∀ z i k, Tfun z i k = Tfun z k i)
    (i k : Fin N) (u : ℝ) :
    matSelfConv Q sigma u i k = matSelfConv Q sigma u k i := by
  have h1 : (fun u => matSelfConv Q sigma u i k) = (fun u => matSelfConv Q sigma u k i) := by
    rw [hbridge i k, hbridge k i]
    congr 1
    funext z
    exact hTsym z i k
  exact congrFun h1 u

/-! ### The `K`-shell assembly — VALID implications, but ⚠ `K` symmetry is ALSO FALSE (2026-08-04)

The lemmas below (`matOzStar_of_shellClaims_K`, `matBaxterK_symm_of_dcf`, `matShellConvAsym_symm_of_K`,
`matOzStar_of_asymK`) are correct implications, but their `K`-symmetry hypothesis (`hCsym`/`hKsym`) is
**numerically FALSE** for unequal diameters — the same trap as `matSelfConv` symmetry and `hmom`.
`K = (Q − matSelfConv)/ρ` carries only ONE linear term `Q` and the WINDOWED `matSelfConv` `[v,σ]`, and
`Q(i,k)−matSelfConv(i,k) ≠ Q(k,i)−matSelfConv(k,i)` (`scratchpad/k_symm_test.py`: diff ~3e-3).  The
genuinely symmetric object is the FULL-LINE DCF `Ĉ₀ᵢₖ(v) = q0(i,k)(v) + q0(k,i)(−v) − matCorrᵢₖ(v)` (TWO
linear terms + full-line `matCorr`, NOT windowed), which is symmetric to machine precision A.E. — but
DISCONTINUOUS at `v = λ` (the `q0` jumps; numerically the symmetry diff is 1e-11..1e-15 away from `v=λ`
and jumps to ~0.19 AT `v=λ`).  So: no windowed / single-linear-term object (`matSelfConv`, `K`) is
symmetric; only the full-line `matDCF`/`Cmix0` is, and only a.e.  Closing the assembly needs the a.e.
Fourier-inversion framework on the discontinuous `matDCF`, NOT the (false) `K` symmetry below. -/

/-- **Matrix OZ★ from the UNSPLIT `K`-shell claim (consumes `Ĉ₀`, not `matSelfConv`).**  If the seed
supplies `Ψ = r·Φ + ρ·matShellConv K` directly — with the symmetric DCF kernel `K` (`ρK = Ĉ₀`, the
inverse transform of `Cmix0`), rather than the `Q − matSelfConv` split — then `MatOZStar` follows from
just the shell-conv bridge.  No `matSelfConv` symmetry, no KDEF split, no integrability side-conditions:
the asymmetric function-part self-conv never appears, since the linear `q̂` terms live inside `K`. -/
theorem matOzStar_of_shellClaims_K {N : ℕ} (Psi Phi Kmat : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {rho sigma : ℝ}
    (hbridge : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
        = matShellConv Kmat (fun k l => fun x => Psi k l x / x) sigma r i j)
    (hclaimA : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      Psi i j r = r * Phi i j r
        + rho * matShellConv Kmat (fun k l => fun x => Psi k l x / x) sigma r i j) :
    MatOZStar Psi Phi rho := by
  intro i j r hr
  rw [hclaimA i j r hr, ← hbridge i j r hr]

/-- **The DCF kernel `K = (Q − matSelfConv)/ρ` is symmetric ⟺ the DCF is symmetric.**  `K` carries the
linear `Q` term, so `Kᵢₖ = Kₖᵢ` follows from the DCF symmetry `hCsym`
(`Qᵢₖ − matSelfConvᵢₖ = Qₖᵢ − matSelfConvₖᵢ`, the real-space content of `Cmix0` symmetric,
`Qphys_Cmix0_entry_symm`) — even though `matSelfConv` alone is NOT symmetric.  This is the correct
symmetry input for `matOzStar_of_shellClaims_K` (its `Kmat`), replacing the false `matSelfConv`
symmetry. -/
theorem matBaxterK_symm_of_dcf {N : ℕ} (Kmat Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {rho sigma : ℝ}
    (hfact : MatBaxterFactorization Kmat Q rho sigma)
    (hCsym : ∀ i k u, u ∈ Set.Ioo (0 : ℝ) sigma →
      Q i k u - matSelfConv Q sigma u i k = Q k i u - matSelfConv Q sigma u k i)
    (i k : Fin N) (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) sigma) (hrho : rho ≠ 0) :
    Kmat i k u = Kmat k i u := by
  refine mul_left_cancel₀ hrho ?_
  rw [hfact i k u hu, hfact k i u hu]
  exact hCsym i k u hu

/-- **The seed's asymmetric `K`-shell collapses to the symmetric `matShellConv K`, via `K` symmetry.**
The corrected seed produces `matShellConvAsym K Kᵀ` — `K(i,k)` on `r+u` (linear `q̂ᵢₖ`) and the reflected
`K(k,i)` on `r−u` (linear `q̂ₖᵢ(−z)`), matching the two linear `q̂` terms of `Ĉ₀`.  When `K` is symmetric
(`matBaxterK_symm_of_dcf`, from the DCF / `Cmix0`), `Kᵀ = K` and it equals the symmetric `matShellConv K`
that `matOzStar_of_shellClaims_K` consumes — with NO `matSelfConv` symmetry. -/
theorem matShellConvAsym_symm_of_K {N : ℕ} (K G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ)
    (hKsym : ∀ i k u, K i k u = K k i u) (i j : Fin N) :
    matShellConvAsym K (fun a b => fun u => K b a u) G sigma r i j
      = matShellConv K G sigma r i j := by
  unfold matShellConvAsym matShellConv
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  show K i k u * oddExt (G k j) (r + u) + K k i u * oddExt (G k j) (r - u)
      = K i k u * (oddExt (G k j) (r - u) + oddExt (G k j) (r + u))
  rw [hKsym k i u]
  ring

/-- **Matrix OZ★ from the corrected seed's asymmetric `K`-renewal — CLOSES obstruction (b), any diameters.**
Given the seed's renewal in asymmetric-`K` form (`hclaimA`: `Ψ = r·Φ + ρ·matShellConvAsym K Kᵀ`), `K`
symmetry (`hKsym`, from `matBaxterK_symm_of_dcf`, i.e. the DCF `Cmix0` symmetric via `swap_offdiag`), and
the shell-conv bridge (`hbridge`), `MatOZStar` holds — using only the proven momentum-space DCF symmetry,
NOT the false `matSelfConv` symmetry.  The seed's two linear terms `Q(i,k)` (`r+u`) and `Q(k,i)` (`r−u`)
supply `Ĉ₀`'s `q̂ᵢₖ(z) + q̂ₖᵢ(−z)`; the self-conv folds into `K`. -/
theorem matOzStar_of_asymK {N : ℕ} (Psi Phi Kmat : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {rho sigma : ℝ}
    (hKsym : ∀ i k u, Kmat i k u = Kmat k i u)
    (hbridge : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
        = matShellConv Kmat (fun k l => fun x => Psi k l x / x) sigma r i j)
    (hclaimA : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      Psi i j r = r * Phi i j r
        + rho * matShellConvAsym Kmat (fun a b => fun u => Kmat b a u)
            (fun k l => fun x => Psi k l x / x) sigma r i j) :
    MatOZStar Psi Phi rho := by
  refine matOzStar_of_shellClaims_K Psi Phi Kmat hbridge (fun i j r hr => ?_)
  rw [hclaimA i j r hr,
    matShellConvAsym_symm_of_K Kmat (fun k l => fun x => Psi k l x / x) sigma r hKsym i j]

/-- **⚠ The current seed matches the `K Kᵀ` target ONLY for equal diameters.**  `matBaxterUQmSym` puts the
UN-reflected linear `Qᵢₖ` on BOTH arms (`matBaxterUQmSym_unfold`: `matBaxterU` gives `Qᵢₖ` on `r−t`, the
second convolution gives `Qᵢₖ` on `r+t`), so after the KDEF its `r−u` coefficient is `Qᵢₖ − matSelfConvₖᵢ`.
`matOzStar_of_asymK`'s `matShellConvAsym K Kᵀ` needs the REFLECTED `Qₖᵢ − matSelfConvₖᵢ = ρKᵀ` on `r−u`.
These coincide **iff `Qᵢₖ = Qₖᵢ`** — equal diameters only.  For unequal diameters (`Q` asymmetric) the
current seed does NOT output `ρ·matShellConvAsym K Kᵀ`: its self-conv IS correctly reflected
(`matDblConv_reindex`: `matSelfConvᵢₖ` on `r+u`, `matSelfConvₖᵢ` on `r−u`), but its linear term is not, so
an uncompensated `(Qᵢₖ−Qₖᵢ)·Ψₖⱼ(r−u)` term remains.  Supplying the reflected linear needs the transposed
FIRST convolution (`Qₖᵢ` on `r−t`), which changes the renewal (`matBaxterU_outer` fixes `Qᵢₖ`) — the
genuine remaining seed-level obstacle. -/
theorem seed_rMinus_eq_KKt_iff {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma u : ℝ)
    (i k : Fin N) :
    Q i k u - matSelfConv Q sigma u k i = Q k i u - matSelfConv Q sigma u k i
      ↔ Q i k u = Q k i u :=
  sub_left_inj

/-! ### B1 of the transform bridge — the Laplace transform of `q0MixEntry` -/

/-- **B1 (closed form) — the Laplace transform of the Baxter quadratic.**
`∫_λ^{λ+σ} e^{−zr}·(Q0(r−R) + Q''(r−R)²/2) dr = e^{−zλ}·(Q0·p₁(σ,z) + Q''·p₂(σ,z))`, with
`p₁ = (1−zσ−e^{−zσ})/z²`, `p₂ = (1−zσ+(zσ)²/2−e^{−zσ})/z³` — exactly the (non-delta) function part of the
momentum `q0_entry`.  Proved by FTC against the explicit antiderivative
`e^{−zr}·((−Q0/z−Q''/z²)(r−R) + (−Q''/2z)(r−R)² + (−Q0/z²−Q''/z³))`. -/
theorem laplace_baxter_quad (z lam sigma Q0 Qpp : ℝ) (hz : z ≠ 0) :
    (∫ r in lam..(lam + sigma), Real.exp (-(z * r))
        * (Q0 * (r - (lam + sigma)) + Qpp * (r - (lam + sigma)) ^ 2 / 2))
      = Real.exp (-(z * lam))
        * (Q0 * ((1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2)
          + Qpp * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3)) := by
  have hF : ∀ r, HasDerivAt (fun r => Real.exp (-(z * r))
        * ((-Q0 / z - Qpp / z ^ 2) * (r - (lam + sigma)) + (-Qpp / (2 * z)) * (r - (lam + sigma)) ^ 2
            + (-Q0 / z ^ 2 - Qpp / z ^ 3)))
      (Real.exp (-(z * r)) * (Q0 * (r - (lam + sigma)) + Qpp * (r - (lam + sigma)) ^ 2 / 2)) r := by
    intro r
    have he : HasDerivAt (fun r => Real.exp (-(z * r))) (Real.exp (-(z * r)) * (-z)) r := by
      have hlin : HasDerivAt (fun r => -(z * r)) (-z) r := by
        simpa [neg_mul] using (hasDerivAt_id r).const_mul (-z)
      exact hlin.exp
    have hg : HasDerivAt (fun r => (-Q0 / z - Qpp / z ^ 2) * (r - (lam + sigma))
          + (-Qpp / (2 * z)) * (r - (lam + sigma)) ^ 2 + (-Q0 / z ^ 2 - Qpp / z ^ 3))
        ((-Q0 / z - Qpp / z ^ 2) * 1 + (-Qpp / (2 * z)) * (2 * (r - (lam + sigma)) ^ 1 * 1)) r := by
      have h1 : HasDerivAt (fun r : ℝ => r - (lam + sigma)) 1 r := (hasDerivAt_id r).sub_const _
      have h2 : HasDerivAt (fun r : ℝ => (r - (lam + sigma)) ^ 2) (2 * (r - (lam + sigma)) ^ 1 * 1) r :=
        h1.pow 2
      exact (((h1.const_mul _).add (h2.const_mul _)).add_const _)
    refine (he.mul hg).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hF r)
      ((by fun_prop : Continuous (fun r => Real.exp (-(z * r))
        * (Q0 * (r - (lam + sigma)) + Qpp * (r - (lam + sigma)) ^ 2 / 2))).intervalIntegrable _ _)]
  have hexp : Real.exp (-(z * (lam + sigma))) = Real.exp (-(z * lam)) * Real.exp (-(z * sigma)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  field_simp
  ring

/-- **B1 — the Laplace transform of the concrete `q0MixEntry`.**  Over its causal window `[λᵢⱼ, Rᵢⱼ]`,
`q0MixEntry` collapses to its quadratic (indicator), `Rᵢⱼ = λᵢⱼ + σᵢ`, and the closed form is
`e^{−zλᵢⱼ}·(Q0ᵢⱼ·p₁(σᵢ,z) + Q''ⱼ·p₂(σᵢ,z))` — precisely the (non-delta) function part of the momentum
`q0_entry`.  This is B1 of the transform bridge; B2 (`q̂ᵢₗ(z)·q̂ₖₗ(−z) = Laplace of the correlation`) and
B4 (injectivity) remain to complete `hbridge`. -/
theorem q0MixEntry_laplace {N M : ℕ} (X : Mix N M) (i j : Fin N) (z : ℝ) (hz : z ≠ 0) :
    (∫ t in (X.lam i j)..(X.R i j), Real.exp (-(z * t)) * q0MixEntry X i j t)
      = Real.exp (-(z * X.lam i j))
        * (X.Q0 i j * ((1 - z * X.σ i - Real.exp (-(z * X.σ i))) / z ^ 2)
          + X.Qpp j * ((1 - z * X.σ i + (z * X.σ i) ^ 2 / 2 - Real.exp (-(z * X.σ i))) / z ^ 3)) := by
  have hRlam : X.R i j = X.lam i j + X.σ i := by simp only [Mix.R, Mix.lam]; ring
  have hle : X.lam i j ≤ X.R i j := by rw [hRlam]; linarith [X.hσ i]
  have hcongr : (∫ t in (X.lam i j)..(X.R i j), Real.exp (-(z * t)) * q0MixEntry X i j t)
      = ∫ t in (X.lam i j)..(X.R i j), Real.exp (-(z * t))
          * (X.Q0 i j * (t - X.R i j) + X.Qpp j * (t - X.R i j) ^ 2 / 2) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hle] at ht
    unfold q0MixEntry
    rw [Set.indicator_of_mem ht]
  rw [hcongr, hRlam]
  exact laplace_baxter_quad z (X.lam i j) (X.σ i) (X.Q0 i j) (X.Qpp j) hz

/-! ### B2 of the transform bridge — the Laplace product↔correlation theorem -/

/-- Full-line reflection: `∫ s, H(t − s) = ∫ s, H s` (measure-preserving affine reflection). -/
theorem integral_reflect_sub (H : ℝ → ℝ) (t : ℝ) : (∫ s, H (t - s)) = ∫ s, H s := by
  have h1 : (∫ s, H (t - s)) = ∫ s, H (t + s) := by
    rw [show (fun s => H (t - s)) = (fun s => (fun s => H (t + s)) (-s)) from by
      funext s; simp [sub_eq_add_neg]]
    exact integral_neg_eq_self (fun s => H (t + s)) volume
  rw [h1, show (fun s => H (t + s)) = (fun s => (fun s => H s) (s + t)) from by
    funext s; rw [add_comm]]
  exact integral_add_right_eq_self H t

/-- **B2 — the Laplace product↔correlation theorem.**
`(∫ f(t)e^{−zt} dt)·(∫ g(s)e^{zs} ds) = ∫ (∫ f(t)g(t−u) dt)·e^{−zu} du` — the product of the two one-sided
Laplace transforms `q̂ᵢₗ(z)`, `q̂ₖₗ(−z)` is the Laplace transform of the cross-correlation
`(f ⋆̃ g)(u) = ∫ f(t)g(t−u) dt` (the `matSelfConv` summand).  Proof: product → double integral
(`integral_prod_mul`), inner reflection `s = t−u` (`integral_reflect_sub`, turning `e^{−z(t−s)}` into
`e^{−zu}`), Fubini swap (`integral_integral_swap`), pull out `e^{−zu}`.  With B1 this gives
`q̂ᵢₗ(z)·q̂ₖₗ(−z) = Laplace((Qᵢₗ ⋆̃ Qₖₗ))`; summed over `l` (B3) it is `[Q̂Q̂ᵀ(−z)]ᵢₖ = Laplace(matSelfConvᵢₖ)`,
which with the momentum symmetry and injectivity (B4) closes `hbridge`. -/
theorem laplace_product_eq_corr (f g : ℝ → ℝ) (z : ℝ)
    (hjoint1 : Integrable
      (fun p : ℝ × ℝ => (f p.1 * Real.exp (-(z * p.1))) * (g p.2 * Real.exp (z * p.2)))
      (volume.prod volume))
    (hjoint2 : Integrable
      (Function.uncurry fun t u => f t * g (t - u) * Real.exp (-(z * u)))
      (volume.prod volume)) :
    (∫ t, f t * Real.exp (-(z * t))) * (∫ s, g s * Real.exp (z * s))
      = ∫ u, (∫ t, f t * g (t - u)) * Real.exp (-(z * u)) := by
  have hinner : ∀ t, (∫ s, (f t * Real.exp (-(z * t))) * (g s * Real.exp (z * s)))
      = ∫ u, f t * g (t - u) * Real.exp (-(z * u)) := by
    intro t
    have hrw : (fun s => (f t * Real.exp (-(z * t))) * (g s * Real.exp (z * s)))
        = (fun s => (fun u => f t * g (t - u) * Real.exp (-(z * u))) (t - s)) := by
      funext s
      simp only []
      rw [show t - (t - s) = s from by ring,
        show -(z * (t - s)) = -(z * t) + z * s from by ring, Real.exp_add]
      ring
    rw [hrw]
    exact integral_reflect_sub (fun u => f t * g (t - u) * Real.exp (-(z * u))) t
  rw [← integral_prod_mul (fun t => f t * Real.exp (-(z * t))) (fun s => g s * Real.exp (z * s)),
    integral_prod _ hjoint1]
  rw [show (fun t => ∫ s, (f t * Real.exp (-(z * t))) * (g s * Real.exp (z * s)))
      = (fun t => ∫ u, f t * g (t - u) * Real.exp (-(z * u))) from funext hinner]
  rw [integral_integral_swap hjoint2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  exact integral_mul_const _ _

/-! ### B1/B2 in the complex (Fourier) convention

The real-variable `laplace_baxter_quad`/`q0MixEntry_laplace`/`laplace_product_eq_corr` above establish the
algebra; but the momentum symmetry `swap_offdiag_of_keys` (MRS.7) lives on the imaginary axis and the
closure step is Mathlib's Fourier inversion (`Continuous.fourierInv_fourier_eq`).  These `_c` variants
carry a complex transform variable `z : ℂ`, so evaluating at `z = 2πi·w` gives the genuine Fourier
transform.  The proofs are character-agnostic — identical structure, `Complex.exp` for `Real.exp`, with
`ofReal` casts. -/

/-- **B1 (complex).**  The two-sided-Laplace / Fourier transform of the Baxter quadratic, `z : ℂ`,
`z ≠ 0`.  Specializes to the Fourier transform at `z = 2πi·w`. -/
theorem laplace_baxter_quad_c (z : ℂ) (lam sigma Q0 Qpp : ℝ) (hz : z ≠ 0) :
    (∫ r in lam..(lam + sigma), Complex.exp (-(z * r))
        * ((Q0 : ℂ) * ((r : ℂ) - ((lam + sigma : ℝ) : ℂ))
          + (Qpp : ℂ) * ((r : ℂ) - ((lam + sigma : ℝ) : ℂ)) ^ 2 / 2))
      = Complex.exp (-(z * lam))
        * ((Q0 : ℂ) * ((1 - z * sigma - Complex.exp (-(z * sigma))) / z ^ 2)
          + (Qpp : ℂ) * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - Complex.exp (-(z * sigma))) / z ^ 3)) := by
  set R : ℂ := ((lam + sigma : ℝ) : ℂ) with hR
  have hF : ∀ r : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(z * r))
        * ((-Q0 / z - Qpp / z ^ 2) * ((r : ℂ) - R) + (-Qpp / (2 * z)) * ((r : ℂ) - R) ^ 2
            + (-Q0 / z ^ 2 - Qpp / z ^ 3)))
      (Complex.exp (-(z * r)) * ((Q0 : ℂ) * ((r : ℂ) - R) + (Qpp : ℂ) * ((r : ℂ) - R) ^ 2 / 2)) r := by
    intro r
    have h0 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := Complex.ofRealCLM.hasDerivAt
    have he : HasDerivAt (fun r : ℝ => Complex.exp (-(z * (r : ℂ))))
        (Complex.exp (-(z * r)) * (-z)) r := by
      have hlin : HasDerivAt (fun r : ℝ => -(z * (r : ℂ))) (-z) r := by
        simpa [neg_mul] using (h0.const_mul (-z))
      exact hlin.cexp
    have hg : HasDerivAt (fun r : ℝ => (-Q0 / z - Qpp / z ^ 2) * ((r : ℂ) - R)
          + (-Qpp / (2 * z)) * ((r : ℂ) - R) ^ 2 + (-Q0 / z ^ 2 - Qpp / z ^ 3))
        ((-Q0 / z - Qpp / z ^ 2) * 1 + (-Qpp / (2 * z)) * (2 * ((r : ℂ) - R) ^ 1 * 1)) r := by
      have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) - R) 1 r := h0.sub_const _
      have h2 : HasDerivAt (fun r : ℝ => ((r : ℂ) - R) ^ 2) (2 * ((r : ℂ) - R) ^ 1 * 1) r := h1.pow 2
      exact (((h1.const_mul _).add (h2.const_mul _)).add_const _)
    refine (he.mul hg).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hF r)
      ((by fun_prop : Continuous (fun r : ℝ => Complex.exp (-(z * (r : ℂ)))
        * ((Q0 : ℂ) * ((r : ℂ) - R) + (Qpp : ℂ) * ((r : ℂ) - R) ^ 2 / 2))).intervalIntegrable _ _)]
  have hexp : Complex.exp (-(z * ((lam + sigma : ℝ) : ℂ)))
      = Complex.exp (-(z * lam)) * Complex.exp (-(z * sigma)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [hR, hexp]
  push_cast
  field_simp
  ring

/-- Full-line reflection (ℂ-valued): `∫ s, H(t − s) = ∫ s, H s`. -/
theorem integral_reflect_sub_c (H : ℝ → ℂ) (t : ℝ) : (∫ s, H (t - s)) = ∫ s, H s := by
  have h1 : (∫ s, H (t - s)) = ∫ s, H (t + s) := by
    rw [show (fun s => H (t - s)) = (fun s => (fun s => H (t + s)) (-s)) from by
      funext s; simp [sub_eq_add_neg]]
    exact integral_neg_eq_self (fun s => H (t + s)) volume
  rw [h1, show (fun s => H (t + s)) = (fun s => (fun s => H s) (s + t)) from by
    funext s; rw [add_comm]]
  exact integral_add_right_eq_self H t

/-- **B2 (complex) — the Fourier product↔correlation theorem.**
`(∫ f(t)e^{−zt} dt)·(∫ g(s)e^{zs} ds) = ∫ (∫ f(t)g(t−u) dt)·e^{−zu} du` for `z : ℂ`, `f g : ℝ → ℂ`.
At `z = 2πi·w` this is `f̂(w)·ĝ(−w) = 𝓕(f ⋆̃ g)(w)`; summed over `l` and combined with the momentum
symmetry it makes the FULL-LINE correlation `R` symmetric (which then feeds Fourier inversion, B4). -/
theorem laplace_product_eq_corr_c (f g : ℝ → ℂ) (z : ℂ)
    (hjoint1 : Integrable
      (fun p : ℝ × ℝ => (f p.1 * Complex.exp (-(z * p.1))) * (g p.2 * Complex.exp (z * p.2)))
      (volume.prod volume))
    (hjoint2 : Integrable
      (Function.uncurry fun t u => f t * g (t - u) * Complex.exp (-(z * u)))
      (volume.prod volume)) :
    (∫ t, f t * Complex.exp (-(z * t))) * (∫ s, g s * Complex.exp (z * s))
      = ∫ u, (∫ t, f t * g (t - u)) * Complex.exp (-(z * u)) := by
  have hinner : ∀ t, (∫ s, (f t * Complex.exp (-(z * t))) * (g s * Complex.exp (z * s)))
      = ∫ u, f t * g (t - u) * Complex.exp (-(z * u)) := by
    intro t
    have hrw : (fun s => (f t * Complex.exp (-(z * (t : ℂ)))) * (g s * Complex.exp (z * (s : ℂ))))
        = (fun s => (fun u => f t * g (t - u) * Complex.exp (-(z * (u : ℂ)))) (t - s)) := by
      funext s
      simp only []
      rw [show t - (t - s) = s from by ring,
        show Complex.exp (-(z * (((t - s : ℝ)) : ℂ)))
            = Complex.exp (-(z * (t : ℂ))) * Complex.exp (z * (s : ℂ)) from by
          rw [← Complex.exp_add]; push_cast; ring_nf]
      ring
    rw [hrw]
    exact integral_reflect_sub_c (fun u => f t * g (t - u) * Complex.exp (-(z * (u : ℂ)))) t
  rw [← integral_prod_mul (fun t => f t * Complex.exp (-(z * t)))
      (fun s => g s * Complex.exp (z * s)), integral_prod _ hjoint1]
  rw [show (fun t => ∫ s, (f t * Complex.exp (-(z * t))) * (g s * Complex.exp (z * s)))
      = (fun t => ∫ u, f t * g (t - u) * Complex.exp (-(z * u))) from funext hinner]
  rw [integral_integral_swap hjoint2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  exact integral_mul_const _ _

/-- **B1 (complex, concrete) — the Fourier/two-sided-Laplace transform of `q0MixEntry`.**  Over
`[λᵢⱼ, Rᵢⱼ]` (with `Rᵢⱼ = λᵢⱼ + σᵢ`) the entry collapses to its quadratic and transforms to
`e^{−zλᵢⱼ}(Q0ᵢⱼ·p₁(σᵢ,z) + Q''ⱼ·p₂(σᵢ,z))`.  At `z = 2πi·w` this is the Fourier-side momentum entry
`Q̂ᵢⱼ(w)` — the object entering `swap_offdiag_of_keys`. -/
theorem q0MixEntry_laplace_c {M : ℕ} (X : Mix N M) (i j : Fin N) (z : ℂ) (hz : z ≠ 0) :
    (∫ t in (X.lam i j)..(X.R i j), Complex.exp (-(z * (t : ℂ))) * ((q0MixEntry X i j t : ℝ) : ℂ))
      = Complex.exp (-(z * (X.lam i j : ℂ)))
        * ((X.Q0 i j : ℂ) * ((1 - z * X.σ i - Complex.exp (-(z * X.σ i))) / z ^ 2)
          + (X.Qpp j : ℂ)
            * ((1 - z * X.σ i + (z * X.σ i) ^ 2 / 2 - Complex.exp (-(z * X.σ i))) / z ^ 3)) := by
  have hRlam : X.R i j = X.lam i j + X.σ i := by simp only [Mix.R, Mix.lam]; ring
  have hle : X.lam i j ≤ X.R i j := by rw [hRlam]; linarith [X.hσ i]
  have hcongr :
      (∫ t in (X.lam i j)..(X.R i j), Complex.exp (-(z * (t : ℂ))) * ((q0MixEntry X i j t : ℝ) : ℂ))
      = ∫ t in (X.lam i j)..(X.R i j), Complex.exp (-(z * (t : ℂ)))
          * ((X.Q0 i j : ℂ) * ((t : ℂ) - ((X.R i j : ℝ) : ℂ))
            + (X.Qpp j : ℂ) * ((t : ℂ) - ((X.R i j : ℝ) : ℂ)) ^ 2 / 2) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hle] at ht
    unfold q0MixEntry
    rw [Set.indicator_of_mem ht]
    push_cast
    ring
  rw [hcongr, hRlam]
  exact laplace_baxter_quad_c z (X.lam i j) (X.σ i) (X.Q0 i j) (X.Qpp j) hz

/-! ### B3 — `∑ₗ` into the full-line correlation `R`

Summing the complex product↔correlation theorem over the species index `l` and identifying the result
with the transform of the FULL-LINE correlation `matCorr` (the symmetric object, unlike the windowed
`matSelfConv`).  The three integrability side-conditions are discharged from the compact support of
`q0MixEntry`. -/

/-- **B3 (algebra) — `∑ₗ` of `laplace_product_eq_corr_c`.**  Pure `∑`/`∫` bookkeeping (per-index B2 +
`integral_finsetSum` swap + `Finset.sum_mul`): the sum of transform products is the transform of the
summed correlation `∑ₗ (Fₗ ⋆̃ Gₗ)`. -/
theorem laplace_sum_eq_corr_c {ι : Type*} (s : Finset ι) (F G : ι → ℝ → ℂ) (z : ℂ)
    (h1 : ∀ l ∈ s, Integrable
      (fun p : ℝ × ℝ => (F l p.1 * Complex.exp (-(z * p.1))) * (G l p.2 * Complex.exp (z * p.2)))
      (volume.prod volume))
    (h2 : ∀ l ∈ s, Integrable
      (Function.uncurry fun t u => F l t * G l (t - u) * Complex.exp (-(z * u)))
      (volume.prod volume))
    (h3 : ∀ l ∈ s, Integrable
      (fun v => (∫ t, F l t * G l (t - v)) * Complex.exp (-(z * v)))) :
    (∑ l ∈ s, (∫ t, F l t * Complex.exp (-(z * t))) * (∫ s, G l s * Complex.exp (z * s)))
      = ∫ v, (∑ l ∈ s, ∫ t, F l t * G l (t - v)) * Complex.exp (-(z * v)) := by
  rw [Finset.sum_congr rfl (fun l hl => laplace_product_eq_corr_c (F l) (G l) z (h1 l hl) (h2 l hl))]
  rw [← integral_finsetSum s h3]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [Finset.sum_mul]

/-- Global measurability of the mixture Baxter entry (indicator of a continuous quadratic).
Delegates to the pure-HS layer through the `toHSMix` bridge. -/
theorem q0MixEntry_measurable {N M : ℕ} (X : Mix N M) (i k : Fin N) :
    Measurable (q0MixEntry X i k) :=
  FMSA.HSMix.q0MixEntry_measurable X.toHSMix i k

/-- **Full-line integrability of `(q0MixEntry)·exp(w·t)` for any `w : ℂ`.**  Compactly supported on
`[λᵢₖ,Rᵢₖ]`, bounded there.  Delegates to the pure-HS layer through the `toHSMix` bridge. -/
theorem q0MixEntry_mul_exp_integrable {N M : ℕ} (X : Mix N M) (i k : Fin N) (w : ℂ) :
    Integrable (fun t => (q0MixEntry X i k t : ℂ) * Complex.exp (w * t)) :=
  FMSA.HSMix.q0MixEntry_mul_exp_integrable X.toHSMix i k w

/-- Global bound on `|q0MixEntry|` (bounded on the compact core, zero elsewhere).
Delegates to the pure-HS layer through the `toHSMix` bridge. -/
theorem q0MixEntry_abs_le {N M : ℕ} (X : Mix N M) (i k : Fin N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |q0MixEntry X i k t| ≤ C :=
  FMSA.HSMix.q0MixEntry_abs_le X.toHSMix i k

/-- **h2 — joint integrability of `Qᵢₗ(t)·Qⱼₗ(t−u)·e^{−zu}` on `ℝ²`.**  Compactly supported on a box
(both entries have compact core support), bounded there (global entry bounds × `e^{−zu}` bounded on the
compact `u`-range); integrable via `integrableOn_of_bounded`. -/
theorem q0MixEntry_corr_exp_prod_integrable {N M : ℕ} (X : Mix N M) (i j l : Fin N) (z : ℂ) :
    Integrable (Function.uncurry fun t u =>
      (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - u) : ℂ) * Complex.exp (-(z * u)))
      (volume.prod volume) := by
  set Bt := Set.Icc (X.lam i l) (X.R i l) with hBt
  set Bu := Set.Icc (X.lam i l - X.R j l) (X.R i l - X.lam j l) with hBu
  have hmeas : Measurable (Function.uncurry fun t u =>
      (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - u) : ℂ) * Complex.exp (-(z * u))) := by
    change Measurable (fun p : ℝ × ℝ => (q0MixEntry X i l p.1 : ℂ)
      * (q0MixEntry X j l (p.1 - p.2) : ℂ) * Complex.exp (-(z * p.2)))
    refine (Measurable.mul (Measurable.mul ?_ ?_) ?_)
    · exact (Complex.measurable_ofReal.comp (q0MixEntry_measurable X i l)).comp measurable_fst
    · exact Complex.measurable_ofReal.comp
        ((q0MixEntry_measurable X j l).comp (measurable_fst.sub measurable_snd))
    · exact (by fun_prop : Measurable (fun p : ℝ × ℝ => Complex.exp (-(z * p.2))))
  have hsupp : Function.support (Function.uncurry fun t u =>
      (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - u) : ℂ) * Complex.exp (-(z * u)))
      ⊆ Bt ×ˢ Bu := by
    intro p hp
    rw [Function.mem_support] at hp
    simp only [Function.uncurry] at hp
    have hi : q0MixEntry X i l p.1 ≠ 0 := by
      rintro h; exact hp (by rw [h]; push_cast; ring)
    have hj : q0MixEntry X j l (p.1 - p.2) ≠ 0 := by
      rintro h; exact hp (by rw [h]; push_cast; ring)
    have hmemi := q0MixEntry_support_subset X i l (Function.mem_support.mpr hi)
    have hmemj := q0MixEntry_support_subset X j l (Function.mem_support.mpr hj)
    rw [Set.mem_Icc] at hmemi hmemj
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr hmemi, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · linarith [hmemi.1, hmemj.2]
    · linarith [hmemi.2, hmemj.1]
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  obtain ⟨Ci, _, hCi⟩ := q0MixEntry_abs_le X i l
  obtain ⟨Cj, _, hCj⟩ := q0MixEntry_abs_le X j l
  obtain ⟨E, hE⟩ := (isCompact_Icc (a := X.lam i l - X.R j l) (b := X.R i l - X.lam j l)
    ).exists_bound_of_continuousOn (f := fun u => Complex.exp (-(z * u)))
    (Continuous.continuousOn (by fun_prop))
  have hfin : (volume.prod volume) (Bt ×ˢ Bu) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
  refine Measure.integrableOn_of_bounded (M := Ci * Cj * E) hfin hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  rw [Set.mem_prod] at hp
  simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul (mul_le_mul (hCi p.1) (hCj (p.1 - p.2)) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hCi p.1))) (hE p.2 hp.2) (norm_nonneg _)
    (mul_nonneg (le_trans (abs_nonneg _) (hCi p.1)) (le_trans (abs_nonneg _) (hCj (p.1 - p.2))))

/-- **The full-line matrix correlation `Rᵢⱼ(v) = ∑ₗ ∫_ℝ Qᵢₗ(t)·Qⱼₗ(t−v) dt`** — the SYMMETRIC object
(unlike the windowed `matSelfConv`, which drops a causal tail when `λ<0`). -/
def matCorr {N M : ℕ} (X : Mix N M) (i j : Fin N) (v : ℝ) : ℂ :=
  ∑ l, ∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ)

/-- **B3 (concrete) — `∑ₗ Q̂ᵢₗ(z)·Q̂ⱼₗ(−z) = Laplace(Rᵢⱼ)`.**  The row-summed product of the complex
transforms equals the transform of the full-line correlation `matCorr`.  All three integrability side
conditions discharged from the compact support of `q0MixEntry` (h1 = `mul_prod` of the 1-D primitive,
h2 = the 2-D box bound, h3 = `integral_prod_right` of h2 with `e^{−zv}` pulled out). -/
theorem matCorr_laplace {N M : ℕ} (X : Mix N M) (i j : Fin N) (z : ℂ) :
    (∑ l, (∫ t, (q0MixEntry X i l t : ℂ) * Complex.exp (-(z * t)))
        * (∫ s, (q0MixEntry X j l s : ℂ) * Complex.exp (z * s)))
      = ∫ v, matCorr X i j v * Complex.exp (-(z * v)) := by
  have key := laplace_sum_eq_corr_c (ι := Fin N) Finset.univ
    (fun l => fun t => (q0MixEntry X i l t : ℂ)) (fun l => fun t => (q0MixEntry X j l t : ℂ)) z
    (fun l _ => by
      simpa only [neg_mul] using
        (q0MixEntry_mul_exp_integrable X i l (-z)).mul_prod (q0MixEntry_mul_exp_integrable X j l z))
    (fun l _ => q0MixEntry_corr_exp_prod_integrable X i j l z)
    (fun l _ => by
      refine (q0MixEntry_corr_exp_prod_integrable X i j l z).integral_prod_right.congr
        (Filter.Eventually.of_forall (fun v => ?_))
      simp only [Function.uncurry]
      exact MeasureTheory.integral_mul_const (Complex.exp (-(z * (v : ℂ)))) _)
  simpa only [matCorr] using key

/-! ### B4 — Fourier inversion machinery (and a CORRECTED structural finding)

Fourier inversion transports a momentum-space transform equality to a real-space function equality.  The
key economy: `eq_zero_of_fourier_eq_zero` needs `Integrable (𝓕 diff)`, which is FREE when `𝓕 diff = 0`
(the integrable zero function), so no decay estimate is needed — only continuity + integrability.

⚠ **CORRECTION (2026-08-03, numerically settled).**  The reduction `matCorr_symm` below is a *valid*
implication, but its hypothesis `hmom` is **FALSE**, so it does NOT close obstruction (b).  `swap_offdiag_of_keys`/MRS.7
proves the FULL momentum product `[Q̂₀(k)·Q̂₀(−k)ᵀ]` symmetric — but `Q̂₀ᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ·Q̂ᵢⱼ` carries the
identity `δ` and the `ρ_geo` weights, whereas `matCorr`'s transform is the *unweighted function-part* product
`∑ₗ Q̂ᵢₗ(z)Q̂ⱼₗ(−z)` (no identity, no weights).  Numerically, the full product is symmetric to 3e-16 while the
unweighted product differs by ~0.02 (and the ρ_geo-weighted-but-no-identity product still differs by ~1.6e-3),
so the identity `δ` terms are essential.  Equivalently `matCorr(j,i)(v) = matCorr(i,j)(−v)` (algebraic), so
`matCorr` symmetric ⟺ each entry EVEN; the off-diagonal `matCorr(0,1)` is a cross-correlation of *different*
functions and is NOT even (`matCorr(0,1)(±0.3)` = 0.285 vs 0.400).  **So the physical symmetry is the full
`Q̂₀` self-product (its real-space form is distributional — carries `δ(v)`), NOT the function-part `matCorr`;
obstruction (b) must use the full Baxter factor (with identity) or be discharged in momentum space via
`swap_offdiag_of_keys` directly.**  The B1–B4 machinery (`matCorr_fourier_eq`, the injectivity lemmas,
`matCorr_continuous`, `matCorr_integrable`) is all correct and reusable; only the target object was wrong. -/

open scoped FourierTransform RealInnerProductSpace

/-- `𝓕⁻` of the zero function is zero. -/
theorem fourierInv_zero_real : (𝓕⁻ (0 : ℝ → ℂ)) = 0 := by
  funext w; rw [Real.fourierInv_eq]; simp

/-- The (real) Fourier transform is subtractive on integrable functions (`integral_sub` after unfolding
to the inner-product form, integrand integrability from `fourierIntegral_convergent_iff`). -/
theorem fourier_sub_real {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  funext w
  have h1 : Integrable (fun v : ℝ => 𝐞 (-⟪v, w⟫) • f v) :=
    (Real.fourierIntegral_convergent_iff w).mpr hf
  have h2 : Integrable (fun v : ℝ => 𝐞 (-⟪v, w⟫) • g v) :=
    (Real.fourierIntegral_convergent_iff w).mpr hg
  rw [Pi.sub_apply, Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  simp only [Pi.sub_apply, smul_sub]
  exact integral_sub h1 h2

/-- **Fourier injectivity via inversion (zero-transform form).**  A continuous integrable function whose
Fourier transform vanishes identically is zero.  `Integrable (𝓕 f)` is free here because `𝓕 f = 0`. -/
theorem eq_zero_of_fourier_eq_zero {f : ℝ → ℂ} (hcont : Continuous f) (hInt : Integrable f)
    (hF : 𝓕 f = 0) : f = 0 := by
  have hF0 : Integrable (𝓕 f) := by rw [hF]; exact integrable_zero _ _ _
  have hinv := hcont.fourierInv_fourier_eq hInt hF0
  rw [hF, fourierInv_zero_real] at hinv
  exact hinv.symm

/-- **Fourier injectivity (equal-transform form).**  Continuous integrable functions with equal Fourier
transforms are equal. -/
theorem eq_of_fourier_eq {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfI : Integrable f) (hgI : Integrable g) (hF : 𝓕 f = 𝓕 g) : f = g := by
  refine sub_eq_zero.mp (eq_zero_of_fourier_eq_zero (hf.sub hg) (hfI.sub hgI) ?_)
  rw [fourier_sub_real hfI hgI, hF, sub_self]

/-- `matCorr` is integrable (finite sum of compactly-supported correlations; `z=0` case of h2 followed
by `integral_prod_right`). -/
theorem matCorr_integrable {N M : ℕ} (X : Mix N M) (i j : Fin N) : Integrable (matCorr X i j) := by
  unfold matCorr
  refine integrable_finsetSum Finset.univ (fun l _ => ?_)
  refine (q0MixEntry_corr_exp_prod_integrable X i j l 0).integral_prod_right.congr
    (Filter.Eventually.of_forall (fun v => ?_))
  simp only [Function.uncurry, zero_mul, neg_zero, Complex.exp_zero, mul_one]

/-- The complex transform variable on the imaginary axis: `zOfW w = 2πi·w`. -/
def zOfW (w : ℝ) : ℂ := 2 * (Real.pi : ℂ) * (w : ℂ) * Complex.I

/-- **The Mathlib Fourier transform in the `zOfW` convention:** `𝓕 g w = ∫ g(v)·e^{−(2πi w)v} dv`.  The
reusable bridge between Mathlib's `𝓕` and this file's `∫ ·e^{−zt}` transforms (at `z = zOfW w`). -/
theorem fourier_eq_zOfW (g : ℝ → ℂ) (w : ℝ) :
    𝓕 g w = ∫ v, g v * Complex.exp (-(zOfW w * v)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  change 𝐞 (-⟪v, w⟫) • g v = g v * Complex.exp (-(zOfW w * (v : ℂ)))
  rw [Circle.smul_def, mul_comm]
  congr 1
  rw [Real.fourierChar_apply, zOfW, Real.inner_apply]
  push_cast
  ring_nf

/-- **Convention bridge — `𝓕(matCorr) = ∑ₗ Q̂ᵢₗ(z)·Q̂ⱼₗ(−z)` at `z = 2πi·w`.**  Identifies the Mathlib
Fourier transform of `matCorr` (B3) with the row-summed transform product. -/
theorem matCorr_fourier_eq {N M : ℕ} (X : Mix N M) (i j : Fin N) (w : ℝ) :
    𝓕 (matCorr X i j) w
      = ∑ l, (∫ t, (q0MixEntry X i l t : ℂ) * Complex.exp (-(zOfW w * t)))
          * (∫ s, (q0MixEntry X j l s : ℂ) * Complex.exp (zOfW w * s)) := by
  rw [fourier_eq_zOfW, matCorr_laplace X i j (zOfW w)]

/-- **Transform of a single (cast) `q0MixEntry`:** `𝓕 (q0MixEntry i j) w = Q̂ᵢⱼ(z)`, `z = zOfW w` — the
linear `q̂` term of the corrected DCF `Ĉ₀ᵢⱼ = q̂ᵢⱼ(z) + q̂ⱼᵢ(−z) − matCorrᵢⱼ(z)`. -/
theorem q0MixEntry_fourier_eq {N M : ℕ} (X : Mix N M) (i j : Fin N) (w : ℝ) :
    𝓕 (fun t => (q0MixEntry X i j t : ℂ)) w
      = ∫ t, (q0MixEntry X i j t : ℂ) * Complex.exp (-(zOfW w * t)) :=
  fourier_eq_zOfW _ w

/-- **Transform of the reflected `q0MixEntry`:** `𝓕 (v ↦ q0MixEntry j i (−v)) w = Q̂ⱼᵢ(−z)` — the second
linear `q̂` term of `Ĉ₀`. -/
theorem q0MixEntry_refl_fourier_eq {N M : ℕ} (X : Mix N M) (i j : Fin N) (w : ℝ) :
    𝓕 (fun v => (q0MixEntry X j i (-v) : ℂ)) w
      = ∫ s, (q0MixEntry X j i s : ℂ) * Complex.exp (zOfW w * s) := by
  rw [fourier_eq_zOfW]
  rw [show (fun v => (q0MixEntry X j i (-v) : ℂ) * Complex.exp (-(zOfW w * (v : ℂ))))
      = (fun v => (fun s => (q0MixEntry X j i s : ℂ) * Complex.exp (zOfW w * (s : ℂ))) (-v)) from by
        funext v
        congr 1
        rw [show -(zOfW w * (v : ℂ)) = zOfW w * ((-v : ℝ) : ℂ) from by push_cast; ring]]
  exact integral_neg_eq_self
    (fun s => (q0MixEntry X j i s : ℂ) * Complex.exp (zOfW w * (s : ℂ))) volume

/-- `q0MixEntry` (cast to `ℂ`) is in every `Lᵖ` (bounded on the compact core, zero elsewhere). -/
theorem q0MixEntry_memLp {N M : ℕ} (X : Mix N M) (i k : Fin N) (p : ENNReal) :
    MemLp (fun t => (q0MixEntry X i k t : ℂ)) p volume := by
  obtain ⟨C, hC0, hC⟩ := q0MixEntry_abs_le X i k
  have hmeas : AEStronglyMeasurable (fun t => (q0MixEntry X i k t : ℂ)) volume :=
    (Complex.measurable_ofReal.comp (q0MixEntry_measurable X i k)).aestronglyMeasurable
  have hg : MemLp (Set.indicator (Set.Icc (X.lam i k) (X.R i k)) (fun _ => C)) p volume :=
    memLp_indicator_const p measurableSet_Icc C (Or.inr measure_Icc_lt_top.ne)
  refine hg.mono' hmeas (Filter.Eventually.of_forall (fun t => ?_))
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases h : t ∈ Set.Icc (X.lam i k) (X.R i k)
  · rw [Set.indicator_of_mem h]; exact hC t
  · rw [Set.indicator_of_notMem h]
    have hz : q0MixEntry X i k t = 0 := by
      by_contra hq; exact h (q0MixEntry_support_subset X i k (Function.mem_support.mpr hq))
    rw [hz]; simp

/-- Continuity of one correlation summand `v ↦ ∫ Qᵢₗ(t)·Qⱼₗ(t−v) dt` via the **L² route** (translation
is strongly continuous on `L²`): `cₗ(v) = ⟪(Qᵢₗ)_L², τᵥ(Qⱼₗ)_L²⟫`, with `v ↦ τᵥ g` continuous by
`Lp.compMeasurePreserving_continuous` and the inner product continuous.  Dominated convergence does NOT
apply — the integrand `v ↦ Qⱼₗ(t−v)` jumps at `λ`; the continuity comes from L² smoothing. -/
theorem q0MixEntry_corr_continuous {N M : ℕ} (X : Mix N M) (i j l : Fin N) :
    Continuous (fun v => ∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ)) := by
  have hfmem := q0MixEntry_memLp X i l 2
  have hgmem := q0MixEntry_memLp X j l 2
  set fLp := hfmem.toLp with hfLp
  set gLp := hgmem.toLp with hgLp
  set T : ℝ → C(ℝ, ℝ) := fun v => ⟨fun x => x - v, by fun_prop⟩ with hT
  have hTcont : Continuous T := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × ℝ => p.2 - p.1)
    fun_prop
  have hMP : ∀ v, MeasurePreserving (⇑(T v)) volume volume := fun v =>
    measurePreserving_sub_right volume v
  set gv : ℝ → Lp ℂ 2 volume := fun v => Lp.compMeasurePreserving (⇑(T v)) (hMP v) gLp with hgv
  have hgvcont : Continuous gv := by
    have hpair : Continuous (fun v : ℝ =>
        (gLp, (⟨T v, hMP v⟩ : {f : C(ℝ, ℝ) // MeasurePreserving (⇑f) volume volume}))) :=
      continuous_const.prodMk (hTcont.subtype_mk _)
    exact (Lp.compMeasurePreserving_continuous volume volume ℂ (by norm_num)).comp hpair
  have hcont : Continuous (fun v => (inner ℂ fLp (gv v) : ℂ)) :=
    (continuous_const.inner continuous_id).comp hgvcont
  refine hcont.congr (fun v => ?_)
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  have hf_ae : fLp =ᵐ[volume] (fun t => (q0MixEntry X i l t : ℂ)) := hfmem.coeFn_toLp
  have hgv_ae : gv v =ᵐ[volume] (fun x => (q0MixEntry X j l (x - v) : ℂ)) := by
    have h1 : gv v =ᵐ[volume] (gLp ∘ ⇑(T v)) := Lp.coeFn_compMeasurePreserving gLp (hMP v)
    have h2 : (gLp : ℝ → ℂ) =ᵐ[volume] (fun t => (q0MixEntry X j l t : ℂ)) := hgmem.coeFn_toLp
    exact h1.trans ((hMP v).quasiMeasurePreserving.ae_eq_comp h2)
  filter_upwards [hf_ae, hgv_ae] with t ht1 ht2
  rw [ht1, ht2, RCLike.inner_apply, Complex.conj_ofReal]; ring

/-- **B4 remaining input (1) DISCHARGED — `matCorr` entries are continuous** (finite sum of the
single-summand correlation continuities). -/
theorem matCorr_continuous {N M : ℕ} (X : Mix N M) (i j : Fin N) : Continuous (matCorr X i j) := by
  unfold matCorr
  exact continuous_finsetSum Finset.univ (fun l _ => q0MixEntry_corr_continuous X i j l)

/-- **B4 (valid implication, but the hypothesis `hmom` is FALSE — see the section note).**  Via Fourier
inversion (`eq_of_fourier_eq` + `matCorr_integrable` + `matCorr_continuous` + `matCorr_fourier_eq`), IF the
unweighted function-part product `∑ₗ Q̂ᵢₗ(z)Q̂ⱼₗ(−z)` were symmetric THEN `matCorr` would be symmetric.  But
`hmom` does NOT follow from `swap_offdiag_of_keys` (which is the FULL `Q̂₀` product, with identity + `ρ_geo`
weights) and is numerically false (~0.02).  Kept only to record the reduction; it does NOT discharge
obstruction (b).  The symmetric object is the full `Q̂₀` self-product (distributional in real space). -/
theorem matCorr_symm {N M : ℕ} (X : Mix N M) (i j : Fin N)
    (hmom : ∀ w : ℝ,
      (∑ l, (∫ t, (q0MixEntry X i l t : ℂ) * Complex.exp (-(zOfW w * t)))
          * (∫ s, (q0MixEntry X j l s : ℂ) * Complex.exp (zOfW w * s)))
        = ∑ l, (∫ t, (q0MixEntry X j l t : ℂ) * Complex.exp (-(zOfW w * t)))
          * (∫ s, (q0MixEntry X i l s : ℂ) * Complex.exp (zOfW w * s))) :
    matCorr X i j = matCorr X j i := by
  refine eq_of_fourier_eq (matCorr_continuous X i j) (matCorr_continuous X j i)
    (matCorr_integrable X i j) (matCorr_integrable X j i) ?_
  funext w
  rw [matCorr_fourier_eq, matCorr_fourier_eq, hmom w]

end
end FMSA.MixtureBaxter
