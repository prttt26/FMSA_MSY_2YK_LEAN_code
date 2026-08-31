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

end FMSA.ExactMSA.GSide
