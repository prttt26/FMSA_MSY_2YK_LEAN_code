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

**Status.**  The convolution theorem is **fully PROVED, axiom-clean, with no Fubini hypothesis**:
`laplace_conv_eq_rdf_mul_qhat_of_integrable` gives `L_z[(rg) ⋆ Q] = ĝ(z)·Q̂(z)` from just the physical
integrability of the Laplace-weighted moments `r·g(r)`, `Q(t)` (`F₁, F₂ ∈ L¹`) plus `g`'s `[0,∞)`
support.  The Fubini swap `hfub` (`laplace_conv_eq_rdf_mul_qhat`'s hypothesis) is discharged by
`laplace_conv_fubini_swap`: the OZ integrand `e^{−zr}(r−t)g(r−t)Q(t)` is a convolution kernel
`F₁(r−t)·F₂(t)`, so `Integrable.convolution_integrand` (full plane) + `Measure.prod_restrict` +
`integral_integral_swap` give the swap.  The algebra is assembled from `rdfLaplaceMoment` (BH Eq. 28),
`laplace_conv_weight`, `laplace_conv_pull_in`,
`integral_Ioi_shift`/`rdfLaplaceMoment_shift`/`rdfLaplaceMoment_shift_from_zero`, and
`laplace_conv_post_fubini`.  **The g-side leg is ASSEMBLED:** `hoz_of_gside` derives `hoz` from the
g-side OZ equation Laplace-transformed at `s = z` (`hgside`, the OZ primitive) by folding its
convolution term with `laplace_conv_eq_rdf_mul_qhat_of_integrable` and substituting `ĝ(z) = G`,
`Q̂(z) = 1 − bhF`; `h33_of_gside` chains it into `MSABlumHoyeDerivation.h33_of_gside_oz` for the full
**`2πG·bhF = bhP`**.  So `h33` now stands on exactly the recognised inputs `hgside` (Eq. 32 Laplace-
transformed) + `ĝ(z)=G` + `Q̂(z)=1−bhF` — parallel to how `h29` stands on `hbax` — with the convolution
folding (the mathematical crux) fully discharged, axiom-clean.
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

/-- **The "pull-in" step** — moves the exterior Laplace weight `e^{−zr}` inside the (`t`-)convolution
integral, turning `L_z[conv]` into the double integral `∫_r ∫_t e^{−zr}·F(r,t)` that Fubini can swap.
`e^{−zr}` is constant in `t`, so this is `integral_const_mul` under the `r`-integral.  Together with
`laplace_conv_post_fubini`, this brackets the only remaining analytic input — the bare Fubini swap
(`integral_integral_swap` + the OZ integrand's 2D integrability on `{0 < t < r}`). -/
theorem laplace_conv_pull_in (F : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ∫ t in Set.Ioi (0:ℝ), F r t)
      = ∫ r in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ), Real.exp (-z * r) * F r t := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro r _
  show Real.exp (-z * r) * (∫ t in Set.Ioi (0:ℝ), F r t)
      = ∫ t in Set.Ioi (0:ℝ), Real.exp (-z * r) * F r t
  rw [MeasureTheory.integral_const_mul]

/-- **The shift step over the physical half-line** `[0, ∞)`.  For an RDF `g` supported on `[0, ∞)`
(`g u = 0` for `u < 0`) and `t > 0`,
`∫_{r > 0} e^{−zr}·(r−t)·g(r−t) dr = e^{−zt}·ĝ(z)`.  The inner `r`-integral of the OZ convolution
naturally runs over `r > 0` (the physical domain), but `g(r−t) = 0` for `r < t` (support) *and* the
`(r−t)` factor vanishes at the boundary `r = t`, so the integrand is **pointwise zero** on all of
`(0, t]` — no measure-zero subtlety.  Hence `∫_{r>0} = ∫_{r>t}` by
`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero` (no integrability needed), and the latter is
`rdfLaplaceMoment_shift`.  This is what lets the `t`-outer form assemble to `ĝ(z)·Q̂(z)` directly from
the physical `r > 0` domain. -/
theorem rdfLaplaceMoment_shift_from_zero (g : ℝ → ℝ) (z t : ℝ) (ht : 0 < t)
    (hgsupp : ∀ u, u < 0 → g u = 0) :
    ∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t))
      = Real.exp (-z * t) * rdfLaplaceMoment g z := by
  rw [← rdfLaplaceMoment_shift g z t]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ioi_subset_Ioi (le_of_lt ht))
  intro r hr
  simp only [Set.mem_diff, Set.mem_Ioi, not_lt] at hr
  have hz : (r - t) * g (r - t) = 0 := by
    rcases lt_or_eq_of_le hr.2 with h | h
    · rw [hgsupp (r - t) (by linarith)]; ring
    · rw [h]; ring
  show Real.exp (-z * r) * ((r - t) * g (r - t)) = 0
  rw [hz]; ring

/-- **The Laplace convolution theorem for the g-side OZ equation** (Blum–Høye, the `L_z` of Eq. 32's
convolution term).  For an RDF `g` and Baxter function `Q` supported on `[0, ∞)`, the Laplace
transform at `s = z` of the OZ convolution `∫₀^∞ (r−t)·g(r−t)·Q(t) dt` factors into the product of the
individual transforms:

    ∫_{r>0} e^{−zr}·(∫_{t>0} (r−t)·g(r−t)·Q(t) dt) dr  =  ĝ(z)·Q̂(z)

where `ĝ(z) = rdfLaplaceMoment g z` and `Q̂(z) = ∫_{t>0} e^{−zt}·Q(t) dt`.  Assembled from the four
algebraic pieces — `laplace_conv_pull_in` (move `e^{−zr}` inside), the Fubini swap (`hfub`), the
per-`t` collapse (`rdfLaplaceMoment_shift_from_zero`, using `g`'s support), and
`laplace_conv_post_fubini`.  The **only** analytic hypothesis is `hfub`, the Fubini swap of the OZ
integrand — i.e. `MeasureTheory.integral_integral_swap` applied to the 2D integrability of
`e^{−zr}·(r−t)·g(r−t)·Q(t)` on the region `{0 < t < r}` (discharged from `g`, `Q` integrability +
exponential decay). -/
theorem laplace_conv_eq_rdf_mul_qhat (g Q : ℝ → ℝ) (z : ℝ)
    (hgsupp : ∀ u, u < 0 → g u = 0)
    (hfub : (∫ r in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
                Real.exp (-z * r) * ((r - t) * g (r - t) * Q t))
          = ∫ t in Set.Ioi (0:ℝ), ∫ r in Set.Ioi (0:ℝ),
                Real.exp (-z * r) * ((r - t) * g (r - t) * Q t)) :
    (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
        * ∫ t in Set.Ioi (0:ℝ), (r - t) * g (r - t) * Q t)
      = rdfLaplaceMoment g z * ∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q t := by
  calc (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
            * ∫ t in Set.Ioi (0:ℝ), (r - t) * g (r - t) * Q t)
      = ∫ r in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            Real.exp (-z * r) * ((r - t) * g (r - t) * Q t) :=
        laplace_conv_pull_in (fun r t => (r - t) * g (r - t) * Q t) z
    _ = ∫ t in Set.Ioi (0:ℝ), ∫ r in Set.Ioi (0:ℝ),
            Real.exp (-z * r) * ((r - t) * g (r - t) * Q t) := hfub
    _ = ∫ t in Set.Ioi (0:ℝ),
            Q t * ∫ r in Set.Ioi t, Real.exp (-z * r) * ((r - t) * g (r - t)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        show (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t) * Q t))
            = Q t * ∫ r in Set.Ioi t, Real.exp (-z * r) * ((r - t) * g (r - t))
        rw [rdfLaplaceMoment_shift g z t,
            ← rdfLaplaceMoment_shift_from_zero g z t ht hgsupp,
            ← MeasureTheory.integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        show Real.exp (-z * r) * ((r - t) * g (r - t) * Q t)
            = Q t * (Real.exp (-z * r) * ((r - t) * g (r - t)))
        ring
    _ = rdfLaplaceMoment g z * ∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q t :=
        laplace_conv_post_fubini g Q z

/-- **The Fubini swap of the OZ-convolution integrand** — discharges the `hfub` hypothesis of
`laplace_conv_eq_rdf_mul_qhat`.  The 2D integrand factors as a *convolution kernel*
`e^{−zr}·(r−t)·g(r−t)·Q(t) = F₁(r−t)·F₂(t)` with `F₁(u) = e^{−zu}·u·g(u)` and `F₂(t) = e^{−zt}·Q(t)`
(since `e^{−z(r−t)}·e^{−zt} = e^{−zr}`).  So its 2D integrability follows from `F₁, F₂ ∈ L¹(ℝ)`:
`Integrable.convolution_integrand` gives full-plane integrability on `volume.prod volume`, and
restricting to `Ioi 0 ×ˢ Ioi 0` (`Integrable.integrableOn` + `Measure.prod_restrict`) yields
integrability on `(volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))` — exactly the hypothesis
`integral_integral_swap` needs (no translation-invariance required at the swap step).  The physical
integrability inputs are `F₁, F₂ ∈ L¹`, i.e. `r·g(r)` and `Q(t)` weighted by the `e^{−z·}` Laplace
kernel decay — precisely the finiteness of the RDF moment `ĝ(z)` and Baxter moment `Q̂(z)`. -/
theorem laplace_conv_fubini_swap (g Q : ℝ → ℝ) (z : ℝ)
    (hF1 : Integrable (fun u => Real.exp (-z * u) * (u * g u)))
    (hF2 : Integrable (fun t => Real.exp (-z * t) * Q t)) :
    (∫ r in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
        Real.exp (-z * r) * ((r - t) * g (r - t) * Q t))
      = ∫ t in Set.Ioi (0:ℝ), ∫ r in Set.Ioi (0:ℝ),
        Real.exp (-z * r) * ((r - t) * g (r - t) * Q t) := by
  have hconv : Integrable
      (fun p : ℝ × ℝ => Real.exp (-z * p.1) * ((p.1 - p.2) * g (p.1 - p.2) * Q p.2))
      (volume.prod volume) := by
    refine (hF2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hF1).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [ContinuousLinearMap.mul_apply']
    have hac : Real.exp (-z * p.2) * Real.exp (-z * (p.1 - p.2)) = Real.exp (-z * p.1) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination (Q p.2 * ((p.1 - p.2) * g (p.1 - p.2))) * hac
  have hrestr : Integrable
      (fun p : ℝ × ℝ => Real.exp (-z * p.1) * ((p.1 - p.2) * g (p.1 - p.2) * Q p.2))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hconv.integrableOn
  exact integral_integral_swap
    (f := fun r t => Real.exp (-z * r) * ((r - t) * g (r - t) * Q t)) hrestr

/-- **The g-side Laplace convolution theorem, fully discharged** (no Fubini hypothesis).  Combines
`laplace_conv_eq_rdf_mul_qhat` with `laplace_conv_fubini_swap`: for an RDF `g` supported on `[0, ∞)`
and with the Laplace-weighted moments `r·g(r)` and `Q(t)` integrable,

    ∫_{r>0} e^{−zr}·(∫_{t>0} (r−t)·g(r−t)·Q(t) dt) dr  =  ĝ(z)·Q̂(z).

This is the form the g-side OZ assembly (`hoz`) consumes: only the physical integrability of the RDF
and Baxter moments is assumed — the Fubini swap is now internal. -/
theorem laplace_conv_eq_rdf_mul_qhat_of_integrable (g Q : ℝ → ℝ) (z : ℝ)
    (hgsupp : ∀ u, u < 0 → g u = 0)
    (hF1 : Integrable (fun u => Real.exp (-z * u) * (u * g u)))
    (hF2 : Integrable (fun t => Real.exp (-z * t) * Q t)) :
    (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
        * ∫ t in Set.Ioi (0:ℝ), (r - t) * g (r - t) * Q t)
      = rdfLaplaceMoment g z * ∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q t :=
  laplace_conv_eq_rdf_mul_qhat g Q z hgsupp (laplace_conv_fubini_swap g Q z hF1 hF2)

/-! ### The g-side OZ assembly — `hoz` from the convolution theorem (Blum–Høye Eq. 32 → 33) -/

/-- **`hoz`, derived from the g-side OZ equation** — the g-side analog of `bh_exterior_baxter_relation`
feeding `h29_of_baxter_exterior`.  Given Blum–Høye's real-space g-side OZ equation (Eq. 32),
**Laplace-transformed at `s = z`** (`hgside`, the recognised OZ primitive — the moment/integral match,
not a single-point coefficient match as on the c-side):

    2π·ĝ(z)  =  ∫₀^∞ (g-source)·e^{−zu} du  +  2π·∫₀^∞ e^{−zr}(∫₀^∞ (r−t)g(r−t)Q(t) dt) dr,

the last (OZ-convolution) term **folds** onto the left via `laplace_conv_eq_rdf_mul_qhat_of_integrable`
into `ĝ(z)·Q̂(z)`.  With the physical identifications `ĝ(z) = G` (`hgmoment`, the RDF Laplace moment =
the repo contact amplitude) and `Q̂(z) = 1 − bhF` (`hQtransform`, i.e. `1 − ρQ̂ = bhF` with `ρ` carried
by `Q`; this is `MSABlumHoyeDerivation.bhBaxter_transform_at_z` for the `[0,∞)`-supported Baxter
function), the `2π·ĝ(z)·(1 − ρQ̂)` regroups to `2π·G·bhF`, giving exactly the `hoz` consumed by
`h33_of_gside_oz`.  The `Q`-support that `Q̂` needs is implicit in `hF2` (`e^{−z·}·Q ∈ L¹` forces
`Q = 0` on `(−∞,0)` since `e^{−z·}` blows up there); the conv theorem itself never evaluates `Q` at
negative arguments. -/
theorem hoz_of_gside (xi z Dt G : ℝ) (g Q : ℝ → ℝ)
    (hgsupp : ∀ u, u < 0 → g u = 0)
    (hF1 : Integrable (fun u => Real.exp (-z * u) * (u * g u)))
    (hF2 : Integrable (fun t => Real.exp (-z * t) * Q t))
    (hgmoment : rdfLaplaceMoment g z = G)
    (hQtransform : (∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q t)
      = 1 - bhF xi z (Dt, G))
    (hgside : 2 * Real.pi * rdfLaplaceMoment g z
      = (∫ u in Set.Ioi (0:ℝ),
            (u * msaA xi z Dt G + msaQp xi z Dt G + z * gam xi z G * Dt * Real.exp (-z * u))
              * Real.exp (-z * u))
        + 2 * Real.pi * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
            * ∫ t in Set.Ioi (0:ℝ), (r - t) * g (r - t) * Q t)) :
    2 * Real.pi * (G * bhF xi z (Dt, G))
      = ∫ u in Set.Ioi (0:ℝ),
          (u * msaA xi z Dt G + msaQp xi z Dt G + z * gam xi z G * Dt * Real.exp (-z * u))
            * Real.exp (-z * u) := by
  rw [laplace_conv_eq_rdf_mul_qhat_of_integrable g Q z hgsupp hF1 hF2, hgmoment,
      hQtransform] at hgside
  linear_combination hgside

/-- **Blum–Høye Eq. (33), fully assembled** — `2πG·bhF = bhP` from the g-side OZ equation
(`hgside`) via the convolution theorem, chaining `hoz_of_gside` into
`MSABlumHoyeDerivation.h33_of_gside_oz`.  This closes the g-side leg of the `N = 1` Blum–Høye
derivation: `h33` is now reduced to the single recognised OZ primitive `hgside` (Eq. 32 Laplace-
transformed) plus the two physical identifications `ĝ(z) = G`, `Q̂(z) = 1 − bhF` — the convolution
folding that was the mathematical crux is discharged (axiom-clean). -/
theorem h33_of_gside (xi z Dt G : ℝ) (hz : 0 < z) (g Q : ℝ → ℝ)
    (hgsupp : ∀ u, u < 0 → g u = 0)
    (hF1 : Integrable (fun u => Real.exp (-z * u) * (u * g u)))
    (hF2 : Integrable (fun t => Real.exp (-z * t) * Q t))
    (hgmoment : rdfLaplaceMoment g z = G)
    (hQtransform : (∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q t)
      = 1 - bhF xi z (Dt, G))
    (hgside : 2 * Real.pi * rdfLaplaceMoment g z
      = (∫ u in Set.Ioi (0:ℝ),
            (u * msaA xi z Dt G + msaQp xi z Dt G + z * gam xi z G * Dt * Real.exp (-z * u))
              * Real.exp (-z * u))
        + 2 * Real.pi * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
            * ∫ t in Set.Ioi (0:ℝ), (r - t) * g (r - t) * Q t)) :
    2 * Real.pi * (G * bhF xi z (Dt, G)) - bhP xi z (Dt, G) = 0 :=
  h33_of_gside_oz xi z Dt G hz
    (hoz_of_gside xi z Dt G g Q hgsupp hF1 hF2 hgmoment hQtransform hgside)

end FMSA.ExactMSA.GSide
