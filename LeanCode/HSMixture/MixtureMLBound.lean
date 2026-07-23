/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MixtureChordFamily
import LeanCode.Analysis.PoleSeriesSummable

/-!
# Task MML.5-concrete — end-to-end summability of the HS-pole series

This file wires `MixtureChordFamily.lean`'s per-pole magnitude gate
(`detF_family_magnitude_bound`) into `MixtureMLSeries.lean`'s summability reduction
(`mixHS_summable_of_growth`), closing the last analytic obligation of MML.5-concrete: the
HS-pole Mittag–Leffler series `Σ_k B_k · e^{−s_k r}` is `Summable`.

## Reflection convention (the "leftover hypothesis")

`detF_family_magnitude_bound` produces `detC`-zeros `g n` with `Re (g n) < 0`. The physical HS
poles carry `Re s_k > 0`, so the series is enumerated with the **reflected** family
`s_k := −(g n)` and residues `B_k := −q01(g n) / det′(g n)` (`= b_k_residue` at the zero `g n`,
`MixtureHSPoles.lean`). Under this reflection `mixHSterm`'s decaying kernel `e^{−s_k r} =
e^{(g n) r}` decays (`Re (g n) < 0`), and its magnitude is *exactly* the gate's LHS
`‖q01(g n)‖ · e^{r·Re(g n)} / ‖det′(g n)‖`. `mixHS_summable_of_growth` takes `Bcoef`, `sfam`
as free functions, so no `b_k_residue` analytic hypotheses are needed here — the wiring is
purely the reflection + a norm computation.

## Result

* `detF_mixHS_summable` — for physical `N=2` data and `rdist > max(σ₀/2, (σ₁−σ₀)/2)`, there is
  an injective family `g` of `detC`-zeros on which the reflected HS-pole series is `Summable`.

**Status:** ✓ DONE, axiom-clean. This discharges the `Summable` step left open when the gate
was proved. Identifying `Bcoef n` with `b_k_residue`'s abstract `B_k` (the same value, modulo
the residue-formula packaging) remains a cosmetic bookkeeping step for the mixture DCF assembly.
-/

open FMSA.PoleSeries

namespace FMSA.MixtureHSPoles

noncomputable section

/-- **MML.5-concrete, end-to-end.** The reflected HS-pole Mittag–Leffler series is `Summable`:
its residues `−q01(g n)/det′(g n)` and reflected poles `−(g n)` (`Re > 0`) satisfy the
`mixHS_summable_of_growth` reduction via the `detF_family_magnitude_bound` gate. -/
theorem detF_mixHS_summable (P : MixParams) (hP : P.Phys) {rdist : ℝ}
    (hrd : max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2) < rdist) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧ (∀ n, P.detF (g n) = 0) ∧
      Summable (mixHSterm (fun n => -(q01 P (g n)) / derivF P (g n))
        (fun n => -(g n)) rdist) := by
  obtain ⟨g, C, p, hp, hC, hinj, hzero, ⟨c, d, hc, hd, hgrow⟩, hbd⟩ :=
    detF_family_magnitude_bound P hP hrd
  refine ⟨g, hinj, hzero, ?_⟩
  refine mixHS_summable_of_growth (r := rdist) (C := C) (c := c) (d := d)
    hp hC.le hc hd (fun n => ?_) (fun n => ?_)
  · -- linear growth transfers through ‖−(g n)‖ = ‖g n‖
    rw [norm_neg]; exact hgrow n
  · -- the term norm equals the gate's LHS
    have hterm : ‖mixHSterm (fun n => -(q01 P (g n)) / derivF P (g n))
        (fun n => -(g n)) rdist n‖ =
        ‖q01 P (g n)‖ * Real.exp (rdist * (g n).re) / ‖derivF P (g n)‖ := by
      unfold mixHSterm
      rw [norm_mul, norm_div, norm_neg]
      have harg : -(-(g n)) * (rdist : ℂ) = g n * (rdist : ℂ) := by ring
      rw [harg, Complex.norm_exp]
      have hre : (g n * (rdist : ℂ)).re = rdist * (g n).re := by
        simp [Complex.mul_re]; ring
      rw [hre]; ring
    rw [hterm, norm_neg]
    exact hbd n

end

end FMSA.MixtureHSPoles
