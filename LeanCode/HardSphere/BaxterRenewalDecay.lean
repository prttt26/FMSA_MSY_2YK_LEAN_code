/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.WienerRenewal
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.HardSphere.BaxterDiluteDecay

/-!
# MA.13 wiring — the concrete FMSA renewal decay `baxterPsiOuter → 0`

Task `MA.13` (`MATH_AXIOMS.md`) supplies the abstract Paley–Wiener / Wiener-algebra renewal-decay
**axiom** `volterra_renewal_tendsto_zero` (`Analysis/WienerRenewal.lean`): a right-compactly-
supported
kernel whose Laplace symbol is nonvanishing on the closed right half-plane yields a decaying
renewal/Volterra solution. That axiom is genuinely axiom-worthy — reconnaissance (2026-07-18)
confirmed Mathlib has **no** Wiener `1/f` / Wiener-algebra inversion, no L¹ convolution Banach
algebra, no Laplace transform, no Paley–Wiener or renewal theory, and (unlike `MA.12`'s
positive-symbol case, which had a Plancherel-coercivity shortcut) there is **no elementary route** —
the classical proof needs the Gelfand-spectrum identification of the Wiener algebra with the
compactified half-plane, a hard from-scratch development.

This file is the **"processing" (wiring) half** of MA.13: it instantiates that abstract axiom at the
concrete FMSA Volterra data — kernel `q0_poly`, forcing `baxterForcing`, solution `baxterPsiOuter`,
after the `[σ,∞) → [0,∞)` shift — producing `baxterPsiOuter → 0` from the concrete Laplace-symbol
nonvanishing hypothesis. That hypothesis (`1 − ∫₀^σ q0_poly(t) e^{−zt} dt ≠ 0` on `{Re z ≥ 0}`, i.e.
`Q̂ ≠ 1` on the closed lower half-plane under `z = ik`) is the **Hermite–Biehler root-location fact
`MA.14`** (`HardSphere/BaxterHermiteBiehler.lean`); left here as an explicit hypothesis so this file
is independent of MA.14's in-progress work. `baxterPsiOuter → 0` in turn discharges the
hypothesis of
`baxterPsi_bounded_Ici_of_tendsto_zero` / `r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero`
(`BaxterExteriorDecayReduction.lean`) ⇒ the general-`η` exterior-decay clauses of the theorem
`baxter_exterior_regularity`.

## Statement-fix note (caught while wiring)

The axiom originally carried a `∀ t, t < 0 ∨ S < t → q t = 0` support clause. The `t < 0`
disjunct is
**unsatisfiable by `q0_poly`** (a nonzero polynomial for `t < 0`, only vanishing for `t > σ`),
and is
mathematically inert (the equation evaluates `q` only at `r − t ≥ 0` and the symbol integrates only
`[0, σ]`). It was weakened to `∀ t, S < t → q t = 0`, discharged here by `q0_poly_outer`.

## Results

* `baxterPsiOuter_continuousOn_Ici` — `baxterPsiOuter` continuous on all of `[σ, ∞)` (axiom-clean).
* `baxterPsiOuter_tendsto_zero_of_symbol` — the wiring: concrete-symbol nonvanishing ⇒
  `baxterPsiOuter → 0`. Depends on exactly `volterra_renewal_tendsto_zero` + the standard three.
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

variable {eta sigma rho : ℝ}

/-- `baxterPsiOuter` is continuous on the whole ray `[σ, ∞)`. -/
theorem baxterPsiOuter_continuousOn_Ici :
    ContinuousOn (baxterPsiOuter eta sigma rho) (Ici sigma) := by
  intro x hx
  have hx' : sigma ≤ x := hx
  have hcont := baxterPsiOuter_continuousOn (eta := eta) (sigma := sigma) (rho := rho)
    (b := x + 1) (le_trans hx' (by linarith))
  have hmem : Icc sigma (x + 1) ∈ 𝓝[Ici sigma] x :=
    mem_nhdsWithin.mpr ⟨Iio (x + 1), isOpen_Iio, mem_Iio.mpr (lt_add_one x),
      fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
  exact (hcont x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- **MA.13 wiring (shifted core).** Instantiating the abstract Paley–Wiener renewal axiom
`volterra_renewal_tendsto_zero` at the concrete FMSA Volterra data (`q := q0_poly`,
`g := baxterForcing`, `ψ := baxterPsiOuter`, after the `[σ,∞) → [0,∞)` shift): if the concrete
Laplace symbol `1 − ∫₀^σ q0_poly(t) e^{−z t} dt` is nonvanishing on the closed right half-plane,
then the shifted outer solution both `→ 0` and is `L¹` on `(0,∞)`. -/
theorem baxterPsiOuter_shift_symbol_pair (hsigma : 0 < sigma)
    (hsym : ∀ z : ℂ, 0 ≤ z.re →
      1 - (∫ t in (0:ℝ)..sigma, (q0_poly eta sigma rho t : ℂ) * Complex.exp (-z * (t : ℂ))) ≠ 0) :
    Tendsto (fun s => baxterPsiOuter eta sigma rho (s + sigma)) atTop (𝓝 0)
      ∧ IntegrableOn (fun s => baxterPsiOuter eta sigma rho (s + sigma)) (Ioi 0) := by
  have hadd : Continuous (fun s : ℝ => s + sigma) := by fun_prop
  apply volterra_renewal_tendsto_zero (q := q0_poly eta sigma rho)
    (g := fun s => baxterForcing eta sigma rho (s + sigma))
    (ψ := fun s => baxterPsiOuter eta sigma rho (s + sigma)) (S := sigma) hsigma
  · exact q0_poly_continuous eta sigma rho
  · exact (baxterForcing_continuous eta sigma rho).comp hadd
  · intro t ht; exact q0_poly_outer ht
  · exact ⟨sigma, fun s hs => baxterForcing_eq_zero_of_two_sigma_le hsigma (by linarith)⟩
  · exact (baxterPsiOuter_continuousOn_Ici).comp hadd.continuousOn
      (fun s hs => by simp only [mem_Ici] at hs ⊢; linarith)
  · exact hsym
  · intro s hs
    have hspec := baxterPsiOuter_spec (eta := eta) (sigma := sigma) (rho := rho)
      (r := s + sigma) (by linarith)
    have hint : (∫ t in sigma..s + sigma,
          q0_poly eta sigma rho (s + sigma - t) * baxterPsiOuter eta sigma rho t)
        = ∫ t in (0:ℝ)..s,
          q0_poly eta sigma rho (s - t) * baxterPsiOuter eta sigma rho (t + sigma) := by
      have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := s)
        (f := fun t =>
          q0_poly eta sigma rho (s + sigma - t) * baxterPsiOuter eta sigma rho t) sigma
      rw [zero_add] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro u _
      change q0_poly eta sigma rho (s + sigma - (u + sigma))
          * baxterPsiOuter eta sigma rho (u + sigma)
        = q0_poly eta sigma rho (s - u) * baxterPsiOuter eta sigma rho (u + sigma)
      rw [show s + sigma - (u + sigma) = s - u from by ring]
    change baxterPsiOuter eta sigma rho (s + sigma)
        = baxterForcing eta sigma rho (s + sigma)
          + ∫ t in (0:ℝ)..s,
            q0_poly eta sigma rho (s - t) * baxterPsiOuter eta sigma rho (t + sigma)
    rw [hspec, hint]

/-- **MA.13 wiring — decay.**  General-`η` exterior decay `baxterPsiOuter → 0` from the shifted
core (`.1` composed with the reverse shift `r ↦ (r − σ) + σ`). -/
theorem baxterPsiOuter_tendsto_zero_of_symbol (hsigma : 0 < sigma)
    (hsym : ∀ z : ℂ, 0 ≤ z.re →
      1 - (∫ t in (0:ℝ)..sigma, (q0_poly eta sigma rho t : ℂ) * Complex.exp (-z * (t : ℂ))) ≠ 0) :
    Tendsto (baxterPsiOuter eta sigma rho) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun r => baxterPsiOuter eta sigma rho ((r - sigma) + sigma)) atTop (𝓝 0) :=
    (baxterPsiOuter_shift_symbol_pair hsigma hsym).1.comp
      (tendsto_atTop_add_const_right atTop (-sigma) tendsto_id)
  have heq : (fun r => baxterPsiOuter eta sigma rho ((r - sigma) + sigma))
      = baxterPsiOuter eta sigma rho := by funext r; rw [sub_add_cancel]
  rwa [heq] at hcomp

/-- **MA.13 wiring — `L¹` integrability.**  `baxterPsiOuter` is integrable on `(σ,∞)`, from the
shifted core (`.2`) transported by the volume-preserving translation `s ↦ s + σ`
(`(· + σ) '' Ioi 0 = Ioi σ`). -/
theorem baxterPsiOuter_integrableOn_Ioi_of_symbol (hsigma : 0 < sigma)
    (hsym : ∀ z : ℂ, 0 ≤ z.re →
      1 - (∫ t in (0:ℝ)..sigma, (q0_poly eta sigma rho t : ℂ) * Complex.exp (-z * (t : ℂ))) ≠ 0) :
    IntegrableOn (baxterPsiOuter eta sigma rho) (Ioi sigma) := by
  have hshift := (baxterPsiOuter_shift_symbol_pair hsigma hsym).2
  have hmp : MeasurePreserving (fun s : ℝ => s + sigma) volume volume :=
    measurePreserving_add_right volume sigma
  have hme : MeasurableEmbedding (fun s : ℝ => s + sigma) :=
    (MeasurableEquiv.addRight sigma).measurableEmbedding
  have himg : (fun s : ℝ => s + sigma) '' Ioi 0 = Ioi sigma := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨s, hs, rfl⟩; linarith
    · intro hx; exact ⟨x - sigma, by linarith, by ring⟩
  rw [← himg, hmp.integrableOn_image hme]
  exact hshift

end

end FMSA.HardSphere
