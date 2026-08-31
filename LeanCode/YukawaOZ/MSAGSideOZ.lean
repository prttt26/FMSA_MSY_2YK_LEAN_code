/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSABlumHoyeDerivation

/-!
# The g-side Yukawa OZ equation (Blum–Høye Eq. 9) — discharging `hoz` (leg-3, `N = 1`)

**Goal.**  `MSABlumHoyeDerivation.h33_of_gside_oz` reduced the exact-MSA constraint `h33`
(`2πG·bhF = bhP`) to a single hypothesis `hoz` — the g-side Ornstein–Zernike relation (Blum–Høye
Eq. 9) Laplace-transformed at `s = z`:

    hoz :  2π·G·bhF  =  ∫₀^∞ [(u·msaA + msaQp) + z·γ·Dt·e^{−zu}] · e^{−zu} du     (the σ-shifted
                                                                                  g-source Laplace)

This file builds the machinery to **discharge `hoz`** from Baxter's real-space g-side equation (BH
Eq. 32) via the Laplace convolution theorem — the last leg of the `N = 1` Blum–Høye derivation.

**The plan (BH Eqs. 30–33).**  Eq. (32) is the real-space g-side OZ equation, at `r > σ`:

    2πr·g(r) = (r−σ)q'' + q' − zC·e^{−z(r−σ)}  +  2πρ ∫_λ^r (r−t)·g(|r−t|)·Q(t) dt        (BH 32)

Laplace-transforming at `s = z` and using the **convolution theorem** on the last (OZ-convolution)
term folds it onto the left side:

    L_z[∫ (r−t)g(|r−t|)Q(t) dt]  =  ĝ(z) · Q̂(z)                                     (conv. theorem)

giving `2πĝ(z)·(1 − ρQ̂(z)) = L_z[g-source]`.  With the repo identifications `ĝ(z) = G·e^{−z}`,
`1 − ρQ̂(z) = bhF`, and the σ-shift `L_z[·over [σ,∞)] = e^{−z}·L_z[·shifted over [0,∞)]`, the `e^{−z}`
factors cancel consistently and this is exactly `hoz`.

**⭐ Normalization resolution (see `bhP_eq_gsource_moment`).**  The `C`-exp in the g-source is
σ-ANCHORED `e^{−z(r−σ)}` (Blum–Høye printed `e^{−zr}`, the source of the spurious `e^{−z}`); the
σ-anchored form makes `L_z[g-source] = bhP` exactly, and `bhP_eq_gsource_moment` already proves it.
So the **only** remaining content is the convolution theorem.

**The convolution theorem, via `Mathlib.Analysis.Convolution`.**  Weight both factors by `e^{−zr}`:
with `f_z(r) = e^{−zr}·r·g(r)` and `Q_z(t) = e^{−zt}·Q(t)`, the pointwise identity
`(f_z ⋆ Q_z)(r) = e^{−zr}·(⟨r·g⟩ ⋆ Q)(r)` (the core `laplace_conv_weight` below) turns
`∫₀^∞ e^{−zr}·(conv)(r) dr` into `∫ (f_z ⋆ Q_z)`, and `MeasureTheory.integral_convolution`
(`∫ f⋆g = (∫f)(∫g)`) delivers `= (∫ f_z)(∫ Q_z) = ĝ(z)·Q̂(z)`.  For `[0,∞)`-supported `g`, `Q` the
whole-line convolution agrees with the one-sided `∫_0^r`.

**Status.**  This file currently provides the abstract RDF Laplace moment `rdfLaplaceMoment` (BH
Eq. 28) and the core weighting identity `laplace_conv_weight`.  TODO (the substantial analysis): the
full `laplace_conv_eq_rdf_mul_qhat` (Fubini/`integral_convolution` + support + integrability), then
the assembly `hoz` from `bhP_eq_gsource_moment` + the transformed BH Eq. (32).
-/

open MeasureTheory Set Real

namespace FMSA.ExactMSA.GSide

/-- **The RDF Laplace moment** (Blum–Høye Eq. 28): `ĝ(s) = ∫₀^∞ e^{−sr}·r·g(r) dr`, for an abstract
radial distribution function `g` (the OZ solution; no closed form, so kept abstract). -/
noncomputable def rdfLaplaceMoment (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0:ℝ), Real.exp (-s * r) * (r * g r)

/-- **The Laplace weighting identity** — the algebraic core of the Laplace convolution theorem.
Weighting each factor of a convolution integrand by `e^{−z·}` pulls a single `e^{−zr}` out of the
convolution: `∫ₛ (e^{−z(r−t)}·f(r−t))·(e^{−zt}·h(t)) dt = e^{−zr}·∫ₛ f(r−t)·h(t) dt`.  This is why
`L_z[f ⋆ h] = f̂(z)·ĥ(z)`: the `e^{−zr}` factors out of the convolution and the weighted factors
integrate to the individual transforms.  Convention-independent (`exp_add` + `integral_const_mul`),
so it holds for any `f`, `h` and any set `s`. -/
theorem laplace_conv_weight (f h : ℝ → ℝ) (z r : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ t in s, (Real.exp (-z * (r - t)) * f (r - t)) * (Real.exp (-z * t) * h t)
      = Real.exp (-z * r) * ∫ t in s, f (r - t) * h t := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun hs
  intro t _
  show (Real.exp (-z * (r - t)) * f (r - t)) * (Real.exp (-z * t) * h t)
      = Real.exp (-z * r) * (f (r - t) * h t)
  rw [show (Real.exp (-z * (r - t)) * f (r - t)) * (Real.exp (-z * t) * h t)
        = (Real.exp (-z * (r - t)) * Real.exp (-z * t)) * (f (r - t) * h t) from by ring,
      show Real.exp (-z * (r - t)) * Real.exp (-z * t) = Real.exp (-z * r) from by
        rw [← Real.exp_add]; congr 1; ring]

/-- **`Ioi`-translation of a set integral.**  `∫_{u > 0} F(u+t) du = ∫_{r > t} F(r) dr`, from the
measure-preserving right-translation `u ↦ u + t` (which maps `Ioi 0` onto `Ioi t`).  The change of
variables underlying the convolution theorem's shift step. -/
theorem integral_Ioi_shift (F : ℝ → ℝ) (t : ℝ) :
    ∫ u in Set.Ioi (0:ℝ), F (u + t) = ∫ r in Set.Ioi t, F r := by
  have hmp : MeasureTheory.MeasurePreserving (· + t) (volume : Measure ℝ) volume :=
    measurePreserving_add_right volume t
  have hme : MeasurableEmbedding (· + t) :=
    (Homeomorph.addRight t).isClosedEmbedding.measurableEmbedding
  have hpre : (· + t) ⁻¹' Set.Ioi t = Set.Ioi (0:ℝ) := by
    ext u; simp only [Set.mem_preimage, Set.mem_Ioi]; constructor <;> intro h <;> linarith
  rw [← hpre, hmp.setIntegral_preimage_emb hme]

/-- **The shift step of the convolution theorem** — the inner (over-`r`) integral of the g-side
OZ convolution.  `∫_{r > t} e^{−zr}·(r−t)·g(r−t) dr = e^{−zt}·ĝ(z)`: substituting `u = r − t`
(`integral_Ioi_shift`) and factoring `e^{−z(u+t)} = e^{−zt}·e^{−zu}` gives the RDF moment `ĝ(z)`
times the `e^{−zt}` that combines with the `Q(t)` factor to reconstruct `Q̂(z)` after the `t`-integral.
-/
theorem rdfLaplaceMoment_shift (g : ℝ → ℝ) (z t : ℝ) :
    ∫ r in Set.Ioi t, Real.exp (-z * r) * ((r - t) * g (r - t))
      = Real.exp (-z * t) * rdfLaplaceMoment g z := by
  rw [← integral_Ioi_shift (fun r => Real.exp (-z * r) * ((r - t) * g (r - t))) t, rdfLaplaceMoment,
      ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  show Real.exp (-z * (u + t)) * ((u + t - t) * g (u + t - t))
      = Real.exp (-z * t) * (Real.exp (-z * u) * (u * g u))
  rw [show u + t - t = u from by ring,
      show Real.exp (-z * (u + t)) = Real.exp (-z * t) * Real.exp (-z * u) from by
        rw [← Real.exp_add]; congr 1; ring]
  ring

/-- **The post-Fubini assembly of the convolution theorem.**  After swapping the `r`- and
`t`-integrals (Fubini), the `t`-outer form of `L_z[(rg) ⋆ Q]` collapses via the shift step: the inner
`r`-integral is `e^{−zt}·ĝ(z)` (`rdfLaplaceMoment_shift`), so
`∫_{t>0} Q(t)·(∫_{r>t} e^{−zr}(r−t)g(r−t) dr) dt = ĝ(z)·∫_{t>0} e^{−zt}Q(t) dt = ĝ(z)·Q̂(z)`.
This isolates the remaining analytic input to the single Fubini swap (`integral_integral_swap` +
the 2D integrability of the OZ-convolution integrand). -/
theorem laplace_conv_post_fubini (g Q : ℝ → ℝ) (z : ℝ) :
    (∫ t in Set.Ioi (0:ℝ),
        Q t * ∫ r in Set.Ioi t, Real.exp (-z * r) * ((r - t) * g (r - t)))
      = rdfLaplaceMoment g z * ∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q t := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  show Q t * (∫ r in Set.Ioi t, Real.exp (-z * r) * ((r - t) * g (r - t)))
      = rdfLaplaceMoment g z * (Real.exp (-z * t) * Q t)
  rw [rdfLaplaceMoment_shift g z t]
  ring

end FMSA.ExactMSA.GSide
