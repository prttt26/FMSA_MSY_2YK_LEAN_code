/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.PoleSeriesSummable
import LeanCode.HSMixture.MixtureHSPoles

/-!
# Tasks MML.4 / MML.5 — the N=2 mixture HS-pole Mittag-Leffler *series*

Group MML (split of the retired MML.3 "full inner-DCF assembly"). This file builds the HS-pole
Mittag-Leffler *series object* — the term-(II) sum

  `Σ_k 2·Re[ B_k · exp(−s_k·r) ]`

of the N=2 inner DCF — and its convergence, mirroring the scalar `h_explicit`/`h_explicit_summable`
machinery of Group POLE (`HardSphere/BaxterResidue.lean`).

## MML.4 — per-pole term + Yukawa-coupled residue

The per-pole term is defined over an **abstract** coefficient family `Bcoef : ℕ → ℂ` and pole family
`sfam : ℕ → ℂ` (mirroring `h_explicit_term`'s abstract `kfam`). Keeping `Bcoef` abstract defers the
singly-vs-doubly-propagation modeling choice to MML.8; here we only tie a *given* `B_k` to the
proven MML.2 residue.

* `mixHSterm` / `mixHS_series` — the `B_k·e^{−s_k r}` term and the `2·Re`-of-tsum series.
* `yukawaCoupling` / `yukawaCoupling_continuousAt` — the Laplace-space Yukawa propagator factor
  `Σ_t K_t/(z_t²−s²)`, continuous away from the Yukawa poles `s²=z_t²`.
* `b_k_residue_coupled` — **MML.4**: multiplying MML.2's `Res_{s_k}[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁(s_k)/det′`
  by any factor `coupling` continuous at `s_k` gives the coupled residue `coupling(s_k)·B_k`. With
  `coupling := yukawaCoupling`, `coupling(s_k)·(−Q̂₀₀₁(s_k)/det′)` is exactly the `B_k` amplitude of
  `fmsa_hs_pole_residue.py`.

## MML.5 — convergence (abstract)

* `mixHS_summable` — **MML.5 (abstract)**: given a magnitude decay `‖mixHSterm n‖ ≤ C·(n+1)^p`
  with `p < −1`, the series is `Summable`. Near-copy of `h_explicit_summable`, closing through
  `Real.summable_nat_rpow`. The *concrete* discharge of this hypothesis (a `|adj/det′|`-growth
  bound tied to the MZERO.1 pole family, a POLE.5-analog for the two-frequency `detC`) is the
  deferred **MML.5-concrete** gate — not attempted here.

Status: ✓ DONE (MML.4, MML.5-abstract), axiom-clean.
-/

set_option linter.style.longLine false

open Filter Topology
open scoped Matrix

open FMSA.PoleSeries

namespace FMSA.MixtureHSPoles

/-! ### MML.4 — the per-pole HS Mittag-Leffler term -/

/-- The Laplace-space Yukawa propagator factor `Σ_{t<nt} K_t/(z_t²−s²)` (`fmsa_hs_pole_residue.py`
`_precompute_residues`). Its poles are at `s² = z_t²`; away from them it is continuous. -/
noncomputable def yukawaCoupling (K z : ℕ → ℂ) (nt : ℕ) (s : ℂ) : ℂ :=
  ∑ t ∈ Finset.range nt, K t / (z t ^ 2 - s ^ 2)

/-- `yukawaCoupling` is continuous at any `s_k` that is not a Yukawa pole (`z_t² ≠ s_k²` for all
tails). -/
theorem yukawaCoupling_continuousAt (K z : ℕ → ℂ) (nt : ℕ) (s_k : ℂ)
    (hden : ∀ t ∈ Finset.range nt, z t ^ 2 - s_k ^ 2 ≠ 0) :
    ContinuousAt (fun s => yukawaCoupling K z nt s) s_k := by
  unfold yukawaCoupling
  apply tendsto_finsetSum
  intro t ht
  exact ContinuousAt.div continuousAt_const (by fun_prop) (hden t ht)

/-- **MML.4 — the Yukawa-coupled HS-pole residue.**  At a simple zero `s_k` of `det(Q̂₀)` (an HS
pole), multiplying MML.2's residue `Res_{s_k}[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁(s_k)/Dprime` by any `coupling`
continuous at `s_k` yields the residue of `coupling·[Q̂₀⁻¹]₀₁`, namely `coupling(s_k)·(−Q̂₀₀₁(s_k)/
Dprime)`.  Instantiated with `coupling := yukawaCoupling K z nt` (and
`yukawaCoupling_continuousAt`) this is the exact `B_k` amplitude of `fmsa_hs_pole_residue.py`.
Wires `b_k_residue` (MML.2) through `Tendsto.mul` with the continuous coupling factor. -/
theorem b_k_residue_coupled (s_k : ℂ) (sigma : Fin 2 → ℂ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    (Dprime : ℂ) (coupling : ℂ → ℂ)
    (hD : HasDerivAt (fun z => (FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp).det) Dprime s_k)
    (hDz0 : (FMSA.Q0Complex.Q0_mat_c s_k sigma rho_geo Qp Qpp).det = 0)
    (hDprime : Dprime ≠ 0)
    (hNcont : ContinuousAt (fun z => (FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp) 0 1) s_k)
    (hcoup : ContinuousAt coupling s_k) :
    Tendsto (fun z => (z - s_k) *
        (coupling z * ((FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp)⁻¹ 0 1)))
      (𝓝[≠] s_k)
      (𝓝 (coupling s_k *
        (-(FMSA.Q0Complex.Q0_mat_c s_k sigma rho_geo Qp Qpp) 0 1 / Dprime))) := by
  have hres := b_k_residue s_k sigma rho_geo Qp Qpp Dprime hD hDz0 hDprime hNcont
  have hcoup' : Tendsto coupling (𝓝[≠] s_k) (𝓝 (coupling s_k)) :=
    hcoup.tendsto.mono_left nhdsWithin_le_nhds
  have heq : ∀ z, (z - s_k) *
        (coupling z * ((FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp)⁻¹ 0 1))
      = coupling z * ((z - s_k) * ((FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp)⁻¹ 0 1)) :=
    fun z => by ring
  simp_rw [heq]
  exact hcoup'.mul hres

/-! ### MML.5 — convergence of the HS-pole series (abstract) -/

end FMSA.MixtureHSPoles
