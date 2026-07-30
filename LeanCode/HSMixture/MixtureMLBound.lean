/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MixtureChordFamily
import LeanCode.HSMixture.MixtureHSPoles
import LeanCode.Analysis.PoleSeriesSummable

/-!
# Task MML.5-concrete — end-to-end summability of the HS-pole series

This file wires `MixtureChordFamily.lean`'s per-pole magnitude gate
(`detF_family_magnitude_bound`) into `MixtureMLSeries.lean`'s summability reduction
(`poleExpTerm_summable_of_growth`), closing the last analytic obligation of MML.5-concrete: the
HS-pole Mittag–Leffler series `Σ_k B_k · e^{−s_k r}` is `Summable`.

## Reflection convention (the "leftover hypothesis")

`detF_family_magnitude_bound` produces `detC`-zeros `g n` with `Re (g n) < 0`. The physical HS
poles carry `Re s_k > 0`, so the series is enumerated with the **reflected** family
`s_k := −(g n)` and residues `B_k := −q01(g n) / det′(g n)` (`= b_k_residue` at the zero `g n`,
`MixtureHSPoles.lean`). Under this reflection `poleExpTerm`'s decaying kernel `e^{−s_k r} =
e^{(g n) r}` decays (`Re (g n) < 0`), and its magnitude is *exactly* the gate's LHS
`‖q01(g n)‖ · e^{r·Re(g n)} / ‖det′(g n)‖`. `poleExpTerm_summable_of_growth` takes `Bcoef`, `sfam`
as free functions, so no `b_k_residue` analytic hypotheses are needed there — that wiring is
purely the reflection + a norm computation.

## The residue identification (MML.5's last bookkeeping item, closed 2026-07-24)

The wiring above leaves `Bcoef n = −q01(g n)/det′(g n)` as a *formula*, resembling MML.2's
residue `B_k` but not proved to be it. `detF_Bcoef_eq_b_k_residue` supplies the missing step: at
any `s_k ≠ 0` with `detF s_k = 0` and `det′(s_k) ≠ 0`, that formula **is** the residue of
`[Q̂₀(z)⁻¹]₀₁` at `s_k` (`b_k_residue`, MML.2). The two simple-zero hypotheses are discharged for
the constructed family by the non-vanishing clause that `detF_family_magnitude_bound` now exports
(`g n ≠ 0`, `det′(g n) ≠ 0` — strict consequences of the `disk_facts` it already used). So
`detF_mixHS_summable` below now certifies **both** that the series converges and that what is being
summed are the genuine HS-pole residues.

## Results

* `detF_eq_det_Q0` — the parameter pack's `detF` is literally `det Q̂₀` of the cast Baxter matrix.
* `detF_Bcoef_eq_b_k_residue` — `−q01(s_k)/det′(s_k)` is the `B_k` residue (MML.2) at a simple zero.
* `detF_mixHS_summable` — for physical `N=2` data and `rdist > max(σ₀/2, (σ₁−σ₀)/2)`, there is
  an injective family `g` of **simple** `detC`-zeros (`detF = 0`, `g n ≠ 0`, `det′ ≠ 0`) on which
  the reflected HS-pole series is `Summable` **and** each coefficient is the residue.  The
  simple-zero clause is what lets the RDF's *order-2* pole data be built on the same family
  (`detF_rdf_pole_family`, `YukawaDCF/MixtureRDFPoleData.lean`, MML.11).

**Status:** ✓ DONE, axiom-clean. MML.5 is now closed with no bookkeeping remainder.
-/

open FMSA.PoleSeries

namespace FMSA.MixtureHSPoles

noncomputable section

/-! ### The `Bcoef = B_k` identification -/

/-- The parameter pack's determinant is literally `det Q̂₀` of the cast physical Baxter matrix —
the bridge that lets `MixParams`-level facts (`detF_hasDerivAt`, `derivF`) meet the `Q0_mat_c`-level
residue lemma `b_k_residue`. -/
theorem detF_eq_det_Q0 (P : MixParams) (s : ℂ) :
    P.detF s = (FMSA.Q0Complex.Q0_mat_c s (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ))
      (fun i j => ((P.rr i j : ℝ) : ℂ)) (fun i j => ((P.Qp i j : ℝ) : ℂ))
      (fun i j => ((P.Qpp i j : ℝ) : ℂ))).det := rfl

/-- **MML.5 — the summed coefficient *is* the `B_k` residue.**  At a simple zero `s_k ≠ 0` of
`detF` (`detF s_k = 0`, `det′(s_k) ≠ 0`), the coefficient `−q01(s_k)/det′(s_k)` that
`detF_mixHS_summable` feeds to `poleExpTerm` is exactly the residue of the off-diagonal inverse entry
`[Q̂₀(z)⁻¹]₀₁` at `s_k`, i.e. MML.2's `b_k_residue`.  This closes MML.5's last item — the series was
already known to converge; now what it sums is certified to be the HS-pole residues rather than a
look-alike formula.

The three `b_k_residue` inputs are discharged from the `MixParams` layer: the derivative from
`detF_hasDerivAt` (`s_k ≠ 0`), the vanishing from `hzero`, and the entry's continuity from
`q0_entry_c_differentiableAt`. -/
theorem detF_Bcoef_eq_b_k_residue (P : MixParams) {s_k : ℂ} (hs : s_k ≠ 0)
    (hzero : P.detF s_k = 0) (hDp : derivF P s_k ≠ 0) :
    Filter.Tendsto (fun z => (z - s_k) *
        ((FMSA.Q0Complex.Q0_mat_c z (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ))
          (fun i j => ((P.rr i j : ℝ) : ℂ)) (fun i j => ((P.Qp i j : ℝ) : ℂ))
          (fun i j => ((P.Qpp i j : ℝ) : ℂ)))⁻¹ 0 1))
      (nhdsWithin s_k {s_k}ᶜ) (nhds (-(q01 P s_k) / derivF P s_k)) := by
  have hD : HasDerivAt (fun z => (FMSA.Q0Complex.Q0_mat_c z
      (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ)) (fun i j => ((P.rr i j : ℝ) : ℂ))
      (fun i j => ((P.Qp i j : ℝ) : ℂ)) (fun i j => ((P.Qpp i j : ℝ) : ℂ))).det)
      (derivF P s_k) s_k := detF_hasDerivAt P hs
  have hD0 : (FMSA.Q0Complex.Q0_mat_c s_k (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ))
      (fun i j => ((P.rr i j : ℝ) : ℂ)) (fun i j => ((P.Qp i j : ℝ) : ℂ))
      (fun i j => ((P.Qpp i j : ℝ) : ℂ))).det = 0 := hzero
  have hcont : ContinuousAt (fun z => FMSA.Q0Complex.Q0_mat_c z
      (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ)) (fun i j => ((P.rr i j : ℝ) : ℂ))
      (fun i j => ((P.Qp i j : ℝ) : ℂ)) (fun i j => ((P.Qpp i j : ℝ) : ℂ)) 0 1) s_k :=
    (q0_entry_c_differentiableAt _ _ _ _ _ _ hs).continuousAt
  have h := b_k_residue s_k (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ))
    (fun i j => ((P.rr i j : ℝ) : ℂ)) (fun i j => ((P.Qp i j : ℝ) : ℂ))
    (fun i j => ((P.Qpp i j : ℝ) : ℂ)) (derivF P s_k) hD hD0 hDp hcont
  rwa [← q01_eq P s_k] at h

/-! ### MML.5-concrete, end to end -/

/-- **MML.5-concrete, end-to-end.** The reflected HS-pole Mittag–Leffler series is `Summable`:
its residues `−q01(g n)/det′(g n)` and reflected poles `−(g n)` (`Re > 0`) satisfy the
`poleExpTerm_summable_of_growth` reduction via the `detF_family_magnitude_bound` gate.  The third clause
certifies (via `detF_Bcoef_eq_b_k_residue`) that those coefficients **are** MML.2's `B_k` residues,
so no bookkeeping gap is left between "the series converges" and "the series is the HS-pole
Mittag–Leffler series". -/
theorem detF_mixHS_summable (P : MixParams) (hP : P.Phys) {rdist : ℝ}
    (hrd : max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2) < rdist) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧
      (∀ n, P.detF (g n) = 0 ∧ g n ≠ 0 ∧ derivF P (g n) ≠ 0) ∧
      (∀ n, Filter.Tendsto (fun z => (z - g n) *
        ((FMSA.Q0Complex.Q0_mat_c z (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ))
          (fun i j => ((P.rr i j : ℝ) : ℂ)) (fun i j => ((P.Qp i j : ℝ) : ℂ))
          (fun i j => ((P.Qpp i j : ℝ) : ℂ)))⁻¹ 0 1))
        (nhdsWithin (g n) {g n}ᶜ) (nhds (-(q01 P (g n)) / derivF P (g n)))) ∧
      Summable (poleExpTerm (fun n => -(q01 P (g n)) / derivF P (g n))
        (fun n => -(g n)) rdist) := by
  obtain ⟨g, C, p, hp, hC, hinj, hzero, ⟨c, d, hc, hd, hgrow⟩, hne, hbd⟩ :=
    detF_family_magnitude_bound P hP hrd
  refine ⟨g, hinj, fun n => ⟨hzero n, (hne n).1, (hne n).2⟩, ?_, ?_⟩
  · -- each coefficient is the `B_k` residue: the two simple-zero hypotheses come from `hne`
    intro n
    exact detF_Bcoef_eq_b_k_residue P (hne n).1 (hzero n) (hne n).2
  refine poleExpTerm_summable_of_growth (r := rdist) (C := C) (c := c) (d := d)
    hp hC.le hc hd (fun n => ?_) (fun n => ?_)
  · -- linear growth transfers through ‖−(g n)‖ = ‖g n‖
    rw [norm_neg]; exact hgrow n
  · -- the term norm equals the gate's LHS
    have hterm : ‖poleExpTerm (fun n => -(q01 P (g n)) / derivF P (g n))
        (fun n => -(g n)) rdist n‖ =
        ‖q01 P (g n)‖ * Real.exp (rdist * (g n).re) / ‖derivF P (g n)‖ := by
      unfold poleExpTerm
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
