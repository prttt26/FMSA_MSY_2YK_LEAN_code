/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterForcingDeriv

/-!
# (★DIFF): the differentiated renewal equation — steps 3–5 of `OZFIX.25`

`baxterPsiOuter` (`ψ`) solves the renewal equation on `[σ,∞)` (`baxterPsiOuter_spec`)

  `ψ(r) = baxterForcing(r) + ∫_σ^r q0_poly(r−t)·ψ(t) dt`.

Differentiating (Leibniz: variable upper limit **and** `r`-dependent integrand = `MA.16`) gives

  `Ψ'(r) = baxterForcing'(r) + q0_poly(0)·ψ̃(r) + ∫_σ^r q0PolyDeriv(r−t)·ψ̃(t) dt`.   **(★DIFF)**

## Two design choices that make this clean

* **`ψ̃ := ψ ∘ (max · σ)`** — `MA.16` wants a *globally* continuous `φ`, but `ψ = baxterPsiOuter`
  jumps at `σ` (it is `0` below).  Composing with `max · σ` freezes it at `ψ(σ)` below `σ` and is
  continuous because `ψ` is `ContinuousOn (Ici σ)` and `max · σ` lands in `Ici σ`.  On `[σ,∞)`,
  `ψ̃ = ψ`, so the renewal integral is unchanged.
* **`baxterPsiSmooth := baxterForcing + Φ`** is the *natural* smooth representative: it is
  differentiable on **all** of `ℝ` (both summands are), and equals `ψ` on `[σ,∞)` by the renewal
  equation.  `ψ` itself is *not* two-sidedly differentiable at `σ` (it is `0` below), which is exactly
  why clause 6a of the old axiom was false — but `baxterPsiSmooth` repairs it with **no linear
  extension needed**, and `baxterPsiSmooth/·` is then the `C¹` representative asked for by
  `ozExterior_smooth_repr` (7a).
-/

open MeasureTheory Set Filter Topology

namespace FMSA.HardSphere

noncomputable section

variable {eta sigma rho : ℝ}

/-- The continuous extension of `baxterPsiOuter` below `σ`, frozen at its value at `σ`.
Equal to `baxterPsiOuter` on `[σ,∞)`. -/
def baxterPsiExt (eta sigma rho : ℝ) : ℝ → ℝ :=
  fun t => baxterPsiOuter eta sigma rho (max t sigma)

theorem baxterPsiExt_eq_of_ge {t : ℝ} (ht : sigma ≤ t) :
    baxterPsiExt eta sigma rho t = baxterPsiOuter eta sigma rho t := by
  simp only [baxterPsiExt, max_eq_left ht]

/-- `baxterPsiOuter` is continuous on all of `[σ,∞)`, from the compact-interval version.  Proved
locally here (rather than imported) so that this file stays **upstream** of `OzExteriorSmooth.lean`,
which must import it to retire axiom 7a — importing `BaxterRenewalDecay` would close a cycle
`… → OzCoreClosure → OzExteriorSmooth`. -/
theorem baxterPsiOuter_continuousOn_Ici_local (hsigma : 0 < sigma) :
    ContinuousOn (baxterPsiOuter eta sigma rho) (Ici sigma) := by
  intro x hx
  have hx' : sigma ≤ x := hx
  have hcont := baxterPsiOuter_continuousOn (eta := eta) (sigma := sigma) (rho := rho)
    (b := x + 1) (by linarith)
  refine (hcont x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.mpr ⟨Iio (x + 1), isOpen_Iio, by simp, ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact ⟨hy2, le_of_lt hy1⟩

/-- `baxterPsiExt` is globally continuous — `MA.16`'s `hφ`. -/
theorem baxterPsiExt_continuous (hsigma : 0 < sigma) :
    Continuous (baxterPsiExt eta sigma rho) :=
  (baxterPsiOuter_continuousOn_Ici_local hsigma).comp_continuous
    (continuous_id.max continuous_const) (fun t => le_max_right t sigma)

/-- The renewal convolution term, as a function of the upper limit. -/
def baxterRenewalConv (eta sigma rho : ℝ) : ℝ → ℝ :=
  fun x => ∫ t in sigma..x, q0_poly eta sigma rho (x - t) * baxterPsiExt eta sigma rho t

/-- **The smooth representative** `Ψ := baxterForcing + Φ`.  Differentiable on all of `ℝ`, and equal
to `baxterPsiOuter` on `[σ,∞)` (`baxterPsiSmooth_eq_of_ge`). -/
def baxterPsiSmooth (eta sigma rho : ℝ) : ℝ → ℝ :=
  fun r => baxterForcing eta sigma rho r + baxterRenewalConv eta sigma rho r

/-- `Ψ = ψ` on the exterior — this is exactly the renewal equation `baxterPsiOuter_spec`, with the
integrand's `ψ` replaced by `ψ̃` (legitimate: they agree on the integration range `[σ,r]`). -/
theorem baxterPsiSmooth_eq_of_ge (hsigma : 0 < sigma) {r : ℝ} (hr : sigma ≤ r) :
    baxterPsiSmooth eta sigma rho r = baxterPsiOuter eta sigma rho r := by
  have hcongr : baxterRenewalConv eta sigma rho r
      = ∫ t in sigma..r, q0_poly eta sigma rho (r - t) * baxterPsiOuter eta sigma rho t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hr] at ht
    show q0_poly eta sigma rho (r - t) * baxterPsiExt eta sigma rho t
      = q0_poly eta sigma rho (r - t) * baxterPsiOuter eta sigma rho t
    rw [baxterPsiExt_eq_of_ge (mem_Icc.mp ht).1]
  rw [baxterPsiSmooth, hcongr]
  exact (baxterPsiOuter_spec hr).symm

/-- **(★DIFF), convolution half.**  `MA.16`'s variable-limit Leibniz applied to the renewal
convolution, with the kernel hypotheses from `BaxterKernelDeriv.lean`. -/
theorem hasDerivAt_baxterRenewalConv (hsigma : 0 < sigma) {r : ℝ} (hr : sigma ≤ r) :
    HasDerivAt (baxterRenewalConv eta sigma rho)
      (q0_poly eta sigma rho 0 * baxterPsiExt eta sigma rho r
        + ∫ t in sigma..r, q0PolyDeriv eta sigma rho (r - t) * baxterPsiExt eta sigma rho t) r := by
  have hlip := q0_poly_lipschitzOnWith_Icc eta sigma rho (-1) (r + 1 - sigma)
    (by linarith)
  exact FMSA.Analysis.hasDerivAt_intervalIntegral_convolution
    (K := q0_poly eta sigma rho) (K' := q0PolyDeriv eta sigma rho)
    (φ := baxterPsiExt eta sigma rho)
    (by norm_num) hr
    (q0_poly_continuous eta sigma rho) (baxterPsiExt_continuous hsigma)
    (hasDerivAt_q0_poly_ae eta sigma rho) (q0PolyDeriv_measurable eta sigma rho)
    hlip

/-- The derivative appearing in (★DIFF). -/
def baxterPsiSmoothDeriv (eta sigma rho : ℝ) : ℝ → ℝ :=
  fun r => (∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s))
    + (q0_poly eta sigma rho 0 * baxterPsiExt eta sigma rho r
      + ∫ t in sigma..r, q0PolyDeriv eta sigma rho (r - t) * baxterPsiExt eta sigma rho t)

/-- **(★DIFF).**  The smooth representative `Ψ` of the renewal solution is differentiable on the
exterior, with derivative `baxterForcing' + q0(0)·ψ̃ + ∫_σ^r q0'·ψ̃`.

Note this is a genuine `HasDerivAt` (two-sided) **including at `r = σ`** — possible precisely because
it is stated for `Ψ`, not for `ψ` (which is `0` below `σ` and so jumps there). -/
theorem hasDerivAt_baxterPsiSmooth (hsigma : 0 < sigma) {r : ℝ} (hr : sigma ≤ r) :
    HasDerivAt (baxterPsiSmooth eta sigma rho) (baxterPsiSmoothDeriv eta sigma rho r) r :=
  (hasDerivAt_baxterForcing eta sigma rho hsigma.le r).add
    (hasDerivAt_baxterRenewalConv hsigma hr)

/-- **Axiom 7a PROVED** (`OZFIX.25` step 5) — `baxterPsiOuter/·` admits a `C¹` representative across
`σ`.  Take `g := Ψ/·` with `Ψ = baxterPsiSmooth`: `Ψ` is differentiable on all of `ℝ` and equals `ψ`
on `[σ,∞)`, and dividing by `r ≥ σ > 0` is harmless.  **No linear extension is needed** — the
renewal equation itself hands us the smooth representative. -/
theorem ozExterior_smooth_repr_proved (hsigma : 0 < sigma) :
    ∃ g g' : ℝ → ℝ,
      (∀ r ∈ Set.Ici sigma, HasDerivAt g (g' r) r) ∧
      (∀ r, sigma ≤ r → g r = baxterPsiOuter eta sigma rho r / r) := by
  refine ⟨fun r => baxterPsiSmooth eta sigma rho r / r,
    fun r => (baxterPsiSmoothDeriv eta sigma rho r * r
      - baxterPsiSmooth eta sigma rho r * 1) / r ^ 2, fun r hr => ?_, fun r hr => ?_⟩
  · have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hsigma hr)
    have hdiv : HasDerivAt (fun y : ℝ => baxterPsiSmooth eta sigma rho y / y)
        ((baxterPsiSmoothDeriv eta sigma rho r * r
          - baxterPsiSmooth eta sigma rho r * 1) / r ^ 2) r :=
      (hasDerivAt_baxterPsiSmooth hsigma hr).div (hasDerivAt_id r) hr0
    exact hdiv
  · show baxterPsiSmooth eta sigma rho r / r = baxterPsiOuter eta sigma rho r / r
    rw [baxterPsiSmooth_eq_of_ge hsigma hr]

end

end FMSA.HardSphere
