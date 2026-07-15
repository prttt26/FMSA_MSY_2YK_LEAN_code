/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.RadialFourierCHS
import LeanCode.HardSphere.OZFourierBridge
import LeanCode.HardSphere.PYOZ_GHS

/-!
# Tasks BAXTER.6/BAXTER.8 — general jump-asymptotic lemma and assembly
*(formerly Tasks OZ.15/OZ.17; see `proof_notes_baxter.md`, Group BAXTER)*

`radial_fourier_c_HS_remainder_le`/`Hhat_closed_asymptotic` (Task `BAXTER.7`,
`RadialFourierCHS.lean`) give the large-`k` asymptotic of the *closed-form*
`Ĥ(k) = Ĉ(k)/(1-ρĈ(k))`. This file supplies the missing link back to `g0_HS_contact_value`: a
genuine, from-scratch real-analysis jump-asymptotic lemma (Task `BAXTER.6`, via integration by
parts on `(σ,∞)` and the Riemann-Lebesgue lemma — already in Mathlib,
`Analysis/Fourier/RiemannLebesgueLemma.lean`), applied to `oz_h` (Task `BAXTER.8`) and matched
against `BAXTER.7`'s closed-form asymptotic via the algebraic identity
`oz_fourier_oz_eq_of_PY_core` (Task OZ.9b).

**Honest scope:** the exterior branch of `oz_h` (`r ≥ σ`) is currently only known to be bounded
and continuous (`oz_fixed_pt_unique`) — not differentiable, not decaying. The jump-asymptotic
lemma genuinely needs differentiability and a `(σ,∞)`-decay/integrability condition to run its
integration-by-parts argument (this is the "main open risk" flagged in `proof_notes_baxter.md`
Task `BAXTER.6`). Rather than assume this away, Task `BAXTER.8`'s final theorem carries it as an
explicit, clearly-labeled hypothesis on `oz_h` — matching this codebase's established practice of
threading genuinely open regularity/integrability conditions explicitly (e.g.
`oz_fourier_oz_eq_of_PY_core` already carries a long list of "routine integrability" hypotheses
the same way).
-/

open MeasureTheory Filter Real Set intervalIntegral
open scoped FourierTransform Topology

noncomputable section

namespace FMSA.HardSphere

/-! ### Piece 0 — Riemann-Lebesgue for real `cos`/`sin`, reusable building block -/

/-- **Riemann-Lebesgue lemma, real `cos`/`sin` form, `k → ∞`.** For `h ∈ L¹(ℝ)`,
`∫ h(v) cos(kv) dv → 0` and `∫ h(v) sin(kv) dv → 0` as `k → ∞`. Derived from Mathlib's general
`Real.tendsto_integral_exp_smul_cocompact` (`Analysis/Fourier/RiemannLebesgueLemma.lean`) by
unpacking the circle-valued Fourier character into real `cos`/`sin`, restricting the `cocompact`
filter to `atTop`, and reparametrizing `w ↦ k = 2πw`. -/
theorem tendsto_integral_mul_cos_sin_atTop {h : ℝ → ℝ} (hh : Integrable h) :
    Tendsto (fun k : ℝ => ∫ v : ℝ, h v * Real.cos (k * v)) atTop (𝓝 0) ∧
    Tendsto (fun k : ℝ => ∫ v : ℝ, h v * Real.sin (k * v)) atTop (𝓝 0) := by
  have hRL : Tendsto (fun w : ℝ => ∫ v : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ)) atTop (𝓝 0) :=
    (Real.tendsto_integral_exp_smul_cocompact (fun v : ℝ => (h v : ℂ))).mono_left atTop_le_cocompact
  have hint : Integrable (fun v : ℝ => (h v : ℂ)) := hh.ofReal
  have hcplx : ∀ w : ℝ, Integrable (fun v : ℝ => (Real.fourierChar (-(v*w))) • (h v : ℂ)) := by
    intro w
    simp_rw [Circle.smul_def]
    apply Integrable.bdd_mul hint (c := 1)
    · fun_prop
    · filter_upwards with v using (Circle.norm_coe _).le
  have hpt : ∀ v w : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ) =
      (h v : ℂ) *
        ((Real.cos (2 * π * v * w) : ℂ) - (Real.sin (2 * π * v * w) : ℂ) * Complex.I) := by
    intro v w
    rw [Circle.smul_def, Real.fourierChar_apply,
      show (2 * π * (-(v * w)) : ℝ) = -(2 * π * v * w) from by ring,
      Complex.exp_ofReal_mul_I (-(2 * π * v * w)), Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hre : ∀ w : ℝ, (∫ v : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ)).re =
      ∫ v : ℝ, h v * Real.cos (2 * π * v * w) := by
    intro w
    calc (∫ v : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ)).re
        = RCLike.re (∫ v : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ)) := rfl
      _ = ∫ v : ℝ, RCLike.re ((Real.fourierChar (-(v*w))) • (h v : ℂ)) :=
            (integral_re (hcplx w)).symm
      _ = ∫ v : ℝ, h v * Real.cos (2 * π * v * w) := by
          congr 1; ext v
          rw [hpt v w]
          have hgoal : ((h v : ℂ) *
              ((Real.cos (2 * π * v * w) : ℂ) - (Real.sin (2 * π * v * w) : ℂ) * Complex.I)).re =
              h v * Real.cos (2 * π * v * w) := by
            simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im]
            ring
          exact hgoal
  have him : ∀ w : ℝ, (∫ v : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ)).im =
      -∫ v : ℝ, h v * Real.sin (2 * π * v * w) := by
    intro w
    calc (∫ v : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ)).im
        = RCLike.im (∫ v : ℝ, (Real.fourierChar (-(v*w))) • (h v : ℂ)) := rfl
      _ = ∫ v : ℝ, RCLike.im ((Real.fourierChar (-(v*w))) • (h v : ℂ)) :=
            (integral_im (hcplx w)).symm
      _ = -∫ v : ℝ, h v * Real.sin (2 * π * v * w) := by
          rw [← MeasureTheory.integral_neg]
          congr 1; ext v
          rw [hpt v w]
          have hgoal : ((h v : ℂ) *
              ((Real.cos (2 * π * v * w) : ℂ) - (Real.sin (2 * π * v * w) : ℂ) * Complex.I)).im =
              -(h v * Real.sin (2 * π * v * w)) := by
            simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im]
            ring
          exact hgoal
  have hRLre : Tendsto (fun w : ℝ => ∫ v : ℝ, h v * Real.cos (2 * π * v * w)) atTop (𝓝 0) := by
    have hcomp := (Complex.continuous_re.tendsto 0).comp hRL
    simp only [Complex.zero_re] at hcomp
    exact hcomp.congr hre
  have hRLim : Tendsto (fun w : ℝ => ∫ v : ℝ, h v * Real.sin (2 * π * v * w)) atTop (𝓝 0) := by
    have hcomp := (Complex.continuous_im.tendsto 0).comp hRL
    simp only [Complex.zero_im] at hcomp
    have hcomp2 : Tendsto (fun w : ℝ => -∫ v : ℝ, h v * Real.sin (2 * π * v * w)) atTop (𝓝 0) :=
      hcomp.congr him
    simpa using hcomp2.neg
  have hdiv : Tendsto (fun k : ℝ => k / (2*π)) atTop atTop :=
    Filter.tendsto_id.atTop_div_const (by positivity)
  have hkey : ∀ k v : ℝ, 2*π*v*(k/(2*π)) = k*v := by
    intro k v; field_simp
  refine ⟨?_, ?_⟩
  · have hc : Tendsto (fun k : ℝ => ∫ v : ℝ, h v * Real.cos (2*π*v*(k/(2*π)))) atTop (𝓝 0) :=
      hRLre.comp hdiv
    simpa only [hkey] using hc
  · have hc : Tendsto (fun k : ℝ => ∫ v : ℝ, h v * Real.sin (2*π*v*(k/(2*π)))) atTop (𝓝 0) :=
      hRLim.comp hdiv
    simpa only [hkey] using hc

/-! ### Piece 1 — exact integration-by-parts identity on `(a,∞)` -/

/-- **Exact IBP identity on `(a,∞)`, for a fixed `k ≠ 0`.** Splits `∫ r g(r) sin(kr) dr` into a
boundary term at `r=a` plus a `(1/k)`-scaled remainder integral, via `HasDerivAt`+FTC on
`F(r) := -(r·g(r)·cos(kr))/k` and Mathlib's improper-integral FTC on `Ioi`
(`integral_Ioi_of_hasDerivAt_of_tendsto'`, `MeasureTheory/Integral/IntegralEqImproper.lean`). -/
theorem ibp_ioi_identity (a k : ℝ) (hk : k ≠ 0) (g g' : ℝ → ℝ)
    (hderiv : ∀ r ∈ Ici a, HasDerivAt g (g' r) r)
    (htendsto : Tendsto (fun r => r * g r) atTop (𝓝 0))
    (hg_int : IntegrableOn (fun r => r * g r * Real.sin (k * r)) (Ioi a))
    (hg'_int : IntegrableOn (fun r => (g r + r * g' r) * Real.cos (k * r)) (Ioi a)) :
    (∫ r in Ioi a, r * g r * Real.sin (k * r)) =
      a * g a * Real.cos (k * a) / k +
        (1/k) * ∫ r in Ioi a, (g r + r * g' r) * Real.cos (k * r) := by
  set F : ℝ → ℝ := fun r => -(r * g r * Real.cos (k * r)) / k with hFdef
  set F' : ℝ → ℝ := fun r => r * g r * Real.sin (k * r) - (g r + r * g' r) * Real.cos (k * r) / k
    with hF'def
  have hFderiv : ∀ r ∈ Ici a, HasDerivAt F (F' r) r := by
    intro r hr
    have h1 : HasDerivAt (fun r => r * g r) (g r + r * g' r) r := by
      have h := (hasDerivAt_id r).mul (hderiv r hr)
      simp only [id_eq, one_mul] at h
      exact h
    have h2 : HasDerivAt (fun x => Real.cos (k * x)) (-Real.sin (k * r) * k) r := by
      have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
      exact h.cos
    have h3 : HasDerivAt (fun r => r * g r * Real.cos (k * r))
        ((g r + r * g' r) * Real.cos (k * r) + r * g r * (-Real.sin (k * r) * k)) r := h1.mul h2
    have h4 : HasDerivAt F
        (-((g r + r * g' r) * Real.cos (k * r) + r * g r * (-Real.sin (k * r) * k)) / k) r :=
      (h3.neg).div_const k
    refine h4.congr_deriv ?_
    rw [hF'def]
    field_simp
    ring
  have hFtendsto : Tendsto F atTop (𝓝 0) := by
    have hb1 : Tendsto (fun r : ℝ => (r * g r) * Real.cos (k * r)) atTop (𝓝 0) := by
      have hbdd : ∀ᶠ r in atTop, ‖(r * g r) * Real.cos (k * r)‖ ≤ ‖r * g r‖ * 1 := by
        filter_upwards with r
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (norm_nonneg _)
      have := squeeze_zero_norm' hbdd (by simpa using htendsto.norm)
      simpa using this
    have := hb1.div_const k
    rw [hFdef]
    simpa [neg_div] using this.neg
  have hF'int : IntegrableOn F' (Ioi a) := by
    rw [hF'def]
    apply Integrable.sub hg_int
    exact hg'_int.div_const k
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hFderiv hF'int hFtendsto
  rw [zero_sub] at key
  rw [hF'def] at key
  rw [integral_sub hg_int (hg'_int.div_const k)] at key
  rw [MeasureTheory.integral_div] at key
  rw [hFdef] at key
  field_simp at key ⊢
  simp only [mul_comm _ k] at key ⊢
  linarith [key]

/-! ### Piece 2 — exterior (`(σ,∞)`) jump-asymptotic via IBP + Riemann-Lebesgue -/

/-- **Task BAXTER.6's "hard half": the exterior `(a,∞)` piece.** For `g` differentiable on `Ici a`
with `r·g(r) → 0` and both `r·g(r)` and `g(r)+r·g'(r)` absolutely integrable on `(a,∞)`,
`k·∫_{(a,∞)} r·g(r)·sin(kr) dr - a·g(a)·cos(ka) → 0` as `k → ∞` — i.e. the sine-moment integral
over `(a,∞)` is `a·g(a)·cos(ka)/k + o(1/k)`, genuinely (not just `O(1/k)`) faster than its own
leading `1/k` order, via Riemann-Lebesgue applied to the IBP remainder `g+r·g'`. -/
theorem right_piece_asymptotic (a : ℝ) (g g' : ℝ → ℝ)
    (hderiv : ∀ r ∈ Ici a, HasDerivAt g (g' r) r)
    (htendsto : Tendsto (fun r => r * g r) atTop (𝓝 0))
    (hg_int : IntegrableOn (fun r => r * g r) (Ioi a))
    (hg'_int : IntegrableOn (fun r => g r + r * g' r) (Ioi a)) :
    Tendsto (fun k : ℝ => k * (∫ r in Ioi a, r * g r * Real.sin (k * r)) -
        a * g a * Real.cos (k * a)) atTop (𝓝 0) := by
  have hRLcs := tendsto_integral_mul_cos_sin_atTop
    (h := (Ioi a).indicator (fun r => g r + r * g' r))
    ((integrable_indicator_iff measurableSet_Ioi).2 hg'_int)
  have hRLcos := hRLcs.1
  have heq : ∀ k : ℝ, (∫ v : ℝ, (Ioi a).indicator (fun r => g r + r * g' r) v * Real.cos (k * v)) =
      ∫ r in Ioi a, (g r + r * g' r) * Real.cos (k * r) := by
    intro k
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1
    ext v
    by_cases hv : v ∈ Ioi a
    · simp [Set.indicator_of_mem hv]
    · simp [Set.indicator_of_notMem hv]
  have hRLcos' : Tendsto (fun k : ℝ => ∫ r in Ioi a, (g r + r * g' r) * Real.cos (k * r))
      atTop (𝓝 0) := hRLcos.congr heq
  have hgk_int : ∀ k : ℝ, IntegrableOn (fun r => r * g r * Real.sin (k * r)) (Ioi a) := by
    intro k
    apply hg_int.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with r using Real.abs_sin_le_one _
  have hg'k_int : ∀ k : ℝ, IntegrableOn (fun r => (g r + r * g' r) * Real.cos (k * r)) (Ioi a) := by
    intro k
    apply hg'_int.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with r using Real.abs_cos_le_one _
  have hpointwise : ∀ᶠ k in atTop, k * (∫ r in Ioi a, r * g r * Real.sin (k * r)) -
      a * g a * Real.cos (k * a) = ∫ r in Ioi a, (g r + r * g' r) * Real.cos (k * r) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with k hk
    have hid := ibp_ioi_identity a k hk g g' hderiv htendsto (hgk_int k) (hg'k_int k)
    field_simp at hid
    simp only [mul_comm _ k] at hid
    linarith [hid]
  exact Tendsto.congr' (Filter.EventuallyEq.symm hpointwise) hRLcos'

/-! ### Piece 3 — domain splitting and the interior (`(0,σ)`) piece -/

/-- **`radial_fourier`'s defining `Ioi 0` integral splits exactly at `σ`.** Only needs `{σ}` to
be a null set (automatic for Lebesgue measure), no regularity on `F`. -/
theorem radial_fourier_split (sigma : ℝ) (hsigma : 0 < sigma) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ioi (0 : ℝ))) :
    (∫ r in Ioi (0 : ℝ), F r) = (∫ r in Ioo (0 : ℝ) sigma, F r) + ∫ r in Ioi sigma, F r := by
  have hdisj : Disjoint (Ioo (0 : ℝ) sigma) (Ici sigma) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_lt.mpr hx2))
  have hF1 : IntegrableOn F (Ioo (0 : ℝ) sigma) := hF.mono_set Ioo_subset_Ioi_self
  have hF2 : IntegrableOn F (Ici sigma) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hF.mono_set (Ioi_subset_Ioi hsigma.le)
  have heq := setIntegral_union hdisj measurableSet_Ici hF1 hF2
  rw [Ioo_union_Ici_eq_Ioi hsigma] at heq
  rw [heq, integral_Ici_eq_integral_Ioi (x := sigma) (f := F) (μ := volume)]

/-- **The interior `(0,σ)` piece, exactly, for `f ≡ c` constant there.** Elementary closed form
via `psi1_formula` (Task OZ.8, `RadialFourierCHS.lean`) — the same `∫ r sin(kr) dr` moment
integral already used for `c_HS`'s own closed form. -/
theorem left_piece_const (sigma k c : ℝ) (hsigma : 0 < sigma) (hk : k ≠ 0) :
    (∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r)) =
      -sigma * c * Real.cos (k * sigma) / k + c * Real.sin (k * sigma) / k ^ 2 := by
  have hconv : (∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r)) =
      ∫ r in (0 : ℝ)..sigma, r * c * Real.sin (k * r) := by
    rw [integral_of_le hsigma.le, integral_Ioc_eq_integral_Ioo]
  rw [hconv]
  have hpull : (∫ r in (0 : ℝ)..sigma, r * c * Real.sin (k * r)) =
      c * ∫ r in (0 : ℝ)..sigma, r * Real.sin (k * r) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext r; ring
  rw [hpull, psi1_formula hk sigma]
  field_simp
  ring

/-! ### Piece 4 (Task BAXTER.6) — assembly: the general jump-asymptotic lemma -/

/-- **Task BAXTER.6 (main theorem).** For `f` equal to the constant `c` on `(0,σ)` and equal to `g`
on `(σ,∞)`, with `g` satisfying the exterior regularity/decay hypotheses of
`right_piece_asymptotic`, `radial_fourier f k`'s deviation from its `cos(kσ)/k²` leading term —
coefficient `4πσ·(g(σ)-c)`, i.e. `4πσ` times the jump `f(σ⁺)-f(σ⁻)` — is `o(1/k²)`:
`k² · (radial_fourier f k - 4πσ(g(σ)-c)·cos(kσ)/k²) → 0` as `k → ∞`. -/
theorem radial_fourier_jump_asymptotic (sigma c : ℝ) (hsigma : 0 < sigma)
    (g g' : ℝ → ℝ) (hderiv : ∀ r ∈ Ici sigma, HasDerivAt g (g' r) r)
    (htendsto : Tendsto (fun r => r * g r) atTop (𝓝 0))
    (hg_int : IntegrableOn (fun r => r * g r) (Ioi sigma))
    (hg'_int : IntegrableOn (fun r => g r + r * g' r) (Ioi sigma))
    (f : ℝ → ℝ) (hf_left : ∀ r ∈ Ioo (0 : ℝ) sigma, f r = c)
    (hf_right : ∀ r ∈ Ioi sigma, f r = g r) :
    Tendsto (fun k : ℝ => k ^ 2 * (radial_fourier f k -
        4 * Real.pi * sigma * (g sigma - c) * Real.cos (k * sigma) / k ^ 2)) atTop (𝓝 0) := by
  have hgk_int : ∀ k : ℝ, IntegrableOn (fun r => r * g r * Real.sin (k * r)) (Ioi sigma) := by
    intro k
    apply hg_int.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with r using Real.abs_sin_le_one _
  have hleft_eq : ∀ k : ℝ, (∫ r in Ioo (0 : ℝ) sigma, r * f r * Real.sin (k * r)) =
      ∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r) := by
    intro k
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    simp only [hf_left r hr]
  have hright_eq : ∀ k : ℝ, (∫ r in Ioi sigma, r * f r * Real.sin (k * r)) =
      ∫ r in Ioi sigma, r * g r * Real.sin (k * r) := by
    intro k
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [hf_right r hr]
  have hfk_int : ∀ k : ℝ, IntegrableOn (fun r => r * f r * Real.sin (k * r)) (Ioi (0 : ℝ)) := by
    intro k
    have hL : IntegrableOn (fun r => r * f r * Real.sin (k * r)) (Ioo (0 : ℝ) sigma) := by
      have hcont : IntegrableOn (fun r => r * c * Real.sin (k * r)) (Ioo (0 : ℝ) sigma) :=
        (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
      exact hcont.congr_fun (fun r hr => by simp only [hf_left r hr]) measurableSet_Ioo
    have hR : IntegrableOn (fun r => r * f r * Real.sin (k * r)) (Ici sigma) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact (hgk_int k).congr_fun (fun r hr => by simp only [hf_right r hr]) measurableSet_Ioi
    have hunion := hL.union hR
    rw [Ioo_union_Ici_eq_Ioi hsigma] at hunion
    exact hunion
  have hsplit_k : ∀ k : ℝ, (∫ r in Ioi (0 : ℝ), r * f r * Real.sin (k * r)) =
      (∫ r in Ioo (0 : ℝ) sigma, r * f r * Real.sin (k * r)) +
        ∫ r in Ioi sigma, r * f r * Real.sin (k * r) :=
    fun k => radial_fourier_split sigma hsigma (fun r => r * f r * Real.sin (k * r)) (hfk_int k)
  have hradial_eq : ∀ k : ℝ, radial_fourier f k =
      (4 * Real.pi / k) * ((∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r)) +
        ∫ r in Ioi sigma, r * g r * Real.sin (k * r)) := by
    intro k
    unfold radial_fourier
    rw [hsplit_k k, hleft_eq k, hright_eq k]
  have hright := right_piece_asymptotic sigma g g' hderiv htendsto hg_int hg'_int
  have hpointwise : ∀ᶠ k in atTop, k ^ 2 * (radial_fourier f k -
      4 * Real.pi * sigma * (g sigma - c) * Real.cos (k * sigma) / k ^ 2) =
      4 * Real.pi * ((k * (∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r)) +
          sigma * c * Real.cos (k * sigma)) +
        (k * (∫ r in Ioi sigma, r * g r * Real.sin (k * r)) -
          sigma * g sigma * Real.cos (k * sigma))) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with k hk
    rw [hradial_eq k, left_piece_const sigma k c hsigma hk]
    field_simp
    ring
  have hleftlim : Tendsto (fun k : ℝ => k * (∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r)) +
      sigma * c * Real.cos (k * sigma)) atTop (𝓝 0) := by
    have heq2 : ∀ᶠ k : ℝ in atTop, k * (∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r)) +
        sigma * c * Real.cos (k * sigma) = c * Real.sin (k * sigma) / k := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with k hk
      rw [left_piece_const sigma k c hsigma hk]
      field_simp
      ring
    have hb : Tendsto (fun k : ℝ => c * Real.sin (k * sigma) / k) atTop (𝓝 0) := by
      have hbdd : ∀ᶠ k in atTop, ‖c * Real.sin (k * sigma) / k‖ ≤ ‖c‖ / k := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
        rw [norm_div, norm_mul, norm_of_nonneg hk.le]
        simp only [Real.norm_eq_abs]
        apply div_le_div_of_nonneg_right _ hk.le
        exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_sin_le_one _)
      have hcinv : Tendsto (fun k : ℝ => ‖c‖ / k) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := ‖c‖)).div_atTop tendsto_id
      exact squeeze_zero_norm' hbdd hcinv
    exact Tendsto.congr' (Filter.EventuallyEq.symm heq2) hb
  have hfinal := hleftlim.add hright
  simp only [add_zero] at hfinal
  have hfinal2 : Tendsto (fun k : ℝ => 4 * Real.pi *
      ((k * (∫ r in Ioo (0 : ℝ) sigma, r * c * Real.sin (k * r)) +
          sigma * c * Real.cos (k * sigma)) +
        (k * (∫ r in Ioi sigma, r * g r * Real.sin (k * r)) -
          sigma * g sigma * Real.cos (k * sigma)))) atTop (𝓝 0) := by
    have := hfinal.const_mul (4 * Real.pi)
    simpa using this
  exact Tendsto.congr' (Filter.EventuallyEq.symm hpointwise) hfinal2

/-! ### Piece 5 (Task BAXTER.8) — assembly: closing `g0_HS_contact_value` -/

/-- **`Hhat_closed_asymptotic`'s explicit `O(1/k³)` bound, repackaged as a `Tendsto` statement.**
Pure squeeze argument: the bound's numerator is `k`-independent, so
`k²·(remainder) = O(1/k) → 0`. -/
theorem Hhat_closed_asymptotic_tendsto (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    Tendsto (fun k : ℝ => k ^ 2 * (Hhat_closed eta sigma rho k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2))
      atTop (𝓝 0) := by
  set C := 2 * |rho| * cHS_bound eta sigma ^ 2 + 4 * Real.pi * cHS_remainder_bound eta sigma
  have hbdd : ∀ᶠ k in atTop, ‖k ^ 2 * (Hhat_closed eta sigma rho k -
      4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2)‖ ≤ C / k := by
    filter_upwards [eventually_ge_atTop (1 + 2 * |rho| * cHS_bound eta sigma)] with k hk
    have hk1 : (1 : ℝ) ≤ k := by
      nlinarith [mul_nonneg (abs_nonneg rho) (cHS_bound_nonneg eta sigma hsigma)]
    have hbound := Hhat_closed_asymptotic eta sigma rho k hsigma hk
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < k ^ 2)]
    rw [show C / k = k ^ 2 * (C / k ^ 3) from by field_simp]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  have hCtoZero : Tendsto (fun k : ℝ => C / k) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).div_atTop tendsto_id
  exact squeeze_zero_norm' hbdd hCtoZero

/-- **A constant `A` with `A·cos(kσ) → 0` as `k → ∞` must be `0`.** Evaluated along the explicit
subsequence `k_n = 2πn/σ`, on which `cos(k_nσ) = cos(2πn) = 1` identically — avoids needing a
general "`cos` doesn't tend to `0`" density/equidistribution lemma. -/
theorem eq_zero_of_tendsto_mul_cos (A sigma : ℝ) (hsigma : 0 < sigma)
    (h : Tendsto (fun k : ℝ => A * Real.cos (k * sigma)) atTop (𝓝 0)) : A = 0 := by
  have hseq : Tendsto (fun n : ℕ => (2 * π * n / sigma : ℝ)) atTop atTop := by
    apply Tendsto.atTop_div_const hsigma
    apply Tendsto.const_mul_atTop (by positivity : (0:ℝ) < 2 * π)
    exact tendsto_natCast_atTop_atTop
  have hcomp : Tendsto (fun n : ℕ => A * Real.cos ((2 * π * n / sigma : ℝ) * sigma))
      atTop (𝓝 0) := h.comp hseq
  have heq : ∀ n : ℕ, A * Real.cos ((2 * π * n / sigma : ℝ) * sigma) = A := by
    intro n
    rw [show (2 * π * (n:ℝ) / sigma) * sigma = 2 * π * n from by field_simp]
    rw [show (2 * π * (n:ℝ)) = (n:ℝ) * (2 * π) from by ring, Real.cos_nat_mul_two_pi]
    ring
  simp only [heq] at hcomp
  exact tendsto_nhds_unique tendsto_const_nhds hcomp

/-- **Task BAXTER.8 (main theorem): `g0_HS_contact_value` from BAXTER.6+BAXTER.7+OZ.9b.**

Closes the `g0_HS_contact_value` axiom *conditionally* on `oz_h`'s exterior branch (`r ≥ σ`)
being differentiable with derivative `g'`, `r·oz_h(r) → 0`, and `r·oz_h(r)`/`oz_h(r)+r·g'(r)`
absolutely integrable on `(σ,∞)` — genuinely open regularity/decay facts about `oz_h` not yet
established elsewhere in this codebase (see `proof_notes_baxter.md` Task BAXTER.6's "main open
risk"), carried here as explicit hypotheses exactly as `oz_fourier_oz_eq_of_PY_core`'s own "routine
integrability" hypotheses already are. Given those, the proof itself is unconditional: apply
`radial_fourier_jump_asymptotic` (Task BAXTER.6) to `f = oz_h`, `c = -1` (`oz_h_core`); separately
identify `radial_fourier(oz_h)(k) = Hhat_closed(k)` via `oz_fourier_oz_eq_of_PY_core` (Task OZ.9b)
and `one_sub_rho_mul_radial_fourier_c_HS_ne_zero`, then transfer BAXTER.7's asymptotic
(`Hhat_closed_asymptotic_tendsto`) across that identification; the two resulting asymptotic
expansions of the *same* function `radial_fourier(oz_h)(k)` must have the same leading
coefficient (`eq_zero_of_tendsto_mul_cos`), forcing `g0_HS(σ) = (1+η/2)/(1-η)²`. -/
theorem g0_HS_contact_value_of_oz_h_regularity {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1)
    (g' : ℝ → ℝ)
    (hderiv : ∀ r ∈ Ici sigma, HasDerivAt (oz_h eta sigma rho) (g' r) r)
    (htendsto : Tendsto (fun r => r * oz_h eta sigma rho r) atTop (𝓝 0))
    (hg_int : IntegrableOn (fun r => r * oz_h eta sigma rho r) (Ioi sigma))
    (hg'_int : IntegrableOn (fun r => oz_h eta sigma rho r + r * g' r) (Ioi sigma))
    (hintA1 : ∀ k : ℝ, 0 < k → ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma)
    (hintA2 : ∀ k : ℝ, 0 < k → ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s' in (max (r - t) sigma)..(r + t), s' * oz_h eta sigma rho s')
      MeasureTheory.volume 0 sigma)
    (htsIntC : ∀ k : ℝ, 0 < k → ∀ r ∈ Ioi (0 : ℝ), Integrable
      (fun p : ℝ × ℝ =>
        p.1 * c_HS eta sigma p.1 *
          (Icc |r - p.1| (r + p.1)).indicator (fun s => s * oz_h eta sigma rho s) p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
    (hjointC : ∀ k, 0 < k → Integrable
      (fun p : ℝ × ℝ × ℝ =>
        (p.2.1 * c_HS eta sigma p.2.1) *
          (Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
            (fun s => s * oz_h eta sigma rho s) p.2.2 *
          Real.sin (k * p.1))
      ((volume.restrict (Ioi 0)).prod
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))))
    (hintB1 : ∀ k, 0 < k → Integrable (fun r => r * c_HS eta sigma r * Real.sin (k * r))
      (volume.restrict (Ioi 0)))
    (hintConv : ∀ k, 0 < k → Integrable
      (fun r => r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.sin (k * r))
      (volume.restrict (Ioi 0))) :
    g0_HS eta sigma rho sigma = (1 + eta / 2) / (1 - eta) ^ 2 := by
  -- Fact A: via the algebraic identity (OZ.9b) + BAXTER.7's asymptotic, transferred across it.
  have hFactA : Tendsto (fun k : ℝ => k ^ 2 * (radial_fourier (oz_h eta sigma rho) k -
      4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2))
      atTop (𝓝 0) := by
    have hpointwise : ∀ᶠ k in atTop, radial_fourier (oz_h eta sigma rho) k =
        Hhat_closed eta sigma rho k := by
      filter_upwards [eventually_ge_atTop (1 + 2 * |rho| * cHS_bound eta sigma),
        eventually_gt_atTop (0:ℝ)] with k hk hk0
      have hne := one_sub_rho_mul_radial_fourier_c_HS_ne_zero eta sigma rho k hsigma hk
      have heq := oz_fourier_oz_eq_of_PY_core hsigma hk0 heta_def heta_lt
        (hintA1 k hk0) (hintA2 k hk0) (htsIntC k hk0) (hjointC k hk0) (hintB1 k hk0)
        (hintConv k hk0)
      unfold Hhat_closed
      rw [eq_div_iff hne]
      exact heq
    have hB := Hhat_closed_asymptotic_tendsto eta sigma rho hsigma
    have hAeq : (fun k : ℝ => k ^ 2 * (Hhat_closed eta sigma rho k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2)) =ᶠ[atTop]
        (fun k : ℝ => k ^ 2 * (radial_fourier (oz_h eta sigma rho) k -
          4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2)) := by
      filter_upwards [hpointwise] with k hk
      rw [hk]
    exact Tendsto.congr' hAeq hB
  -- Fact B: BAXTER.6 applied directly to `f := oz_h`, `c := -1`.
  have hFactB : Tendsto (fun k : ℝ => k ^ 2 * (radial_fourier (oz_h eta sigma rho) k -
      4 * Real.pi * sigma * (oz_h eta sigma rho sigma - (-1)) * Real.cos (k * sigma) / k ^ 2))
      atTop (𝓝 0) :=
    radial_fourier_jump_asymptotic sigma (-1) hsigma (oz_h eta sigma rho) g' hderiv htendsto
      hg_int hg'_int (oz_h eta sigma rho)
      (fun r hr => oz_h_core hsigma hr.2) (fun _ _ => rfl)
  -- Difference of the two leading coefficients, matched via `eq_zero_of_tendsto_mul_cos`.
  have hdiff : Tendsto (fun k : ℝ =>
      4 * Real.pi * sigma * (cHS_leading_coeff eta - (oz_h eta sigma rho sigma + 1)) *
        Real.cos (k * sigma)) atTop (𝓝 0) := by
    have hsub := hFactB.sub hFactA
    rw [sub_self] at hsub
    have heq2 : ∀ k : ℝ, k ≠ 0 →
        k ^ 2 * (radial_fourier (oz_h eta sigma rho) k -
            4 * Real.pi * sigma * (oz_h eta sigma rho sigma - (-1)) * Real.cos (k * sigma) /
              k ^ 2) -
          k ^ 2 * (radial_fourier (oz_h eta sigma rho) k -
            4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2) =
          4 * Real.pi * sigma * (cHS_leading_coeff eta - (oz_h eta sigma rho sigma + 1)) *
            Real.cos (k * sigma) := by
      intro k hk
      field_simp
      ring
    have hcongr : ∀ᶠ k in atTop,
        k ^ 2 * (radial_fourier (oz_h eta sigma rho) k -
            4 * Real.pi * sigma * (oz_h eta sigma rho sigma - (-1)) * Real.cos (k * sigma) /
              k ^ 2) -
          k ^ 2 * (radial_fourier (oz_h eta sigma rho) k -
            4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2) =
          4 * Real.pi * sigma * (cHS_leading_coeff eta - (oz_h eta sigma rho sigma + 1)) *
            Real.cos (k * sigma) := by
      filter_upwards [eventually_ne_atTop (0:ℝ)] with k hk using heq2 k hk
    exact Tendsto.congr' hcongr hsub
  have hzero : 4 * Real.pi * sigma *
      (cHS_leading_coeff eta - (oz_h eta sigma rho sigma + 1)) = 0 :=
    eq_zero_of_tendsto_mul_cos _ sigma hsigma hdiff
  have hJ : oz_h eta sigma rho sigma + 1 = cHS_leading_coeff eta := by
    have h4πσ : (4 : ℝ) * Real.pi * sigma ≠ 0 := by positivity
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h h4πσ
    · linarith
  have hJ0 : cHS_leading_coeff eta = (1 + eta / 2) / (1 - eta) ^ 2 := by
    unfold cHS_leading_coeff
    exact py_f1_eq heta_lt
  have hg0 : g0_HS eta sigma rho sigma = 1 + oz_h eta sigma rho sigma := by
    unfold g0_HS
    rw [if_neg (lt_irrefl sigma)]
    rfl
  rw [hg0, ← hJ0, ← hJ]
  ring

/-! ### Task OZ.3 — retiring the bare `g0_HS_contact_value` axiom

BAXTER.8 (`g0_HS_contact_value_of_oz_h_regularity`) reduces the PY contact value to a bundle of
exterior regularity/decay/integrability facts about `oz_h`. Those facts are genuinely open in this
codebase (`oz_h` is only known bounded/continuous via `oz_fixed_pt_unique`), but they are standard
analytic properties of the PY hard-sphere OZ solution in the exterior region (Wertheim 1963), not
physics input. We package exactly BAXTER.8's extra hypotheses as one named axiom and derive the
contact value as an unconditional theorem — replacing the old *physical-number* axiom
(`g0_HS_contact_value`, formerly in `PYOZ_GHS.lean`) with an *analytic-regularity* axiom of strictly
weaker epistemic content: the specific value `(1+η/2)/(1-η)²` is now proved, not assumed. -/

/-- **`oz_h` exterior regularity/decay/integrability (named axiom, Task OZ.3).**

Exactly the extra hypotheses `g0_HS_contact_value_of_oz_h_regularity` (Task BAXTER.8) consumes,
bundled as an existential over the exterior derivative `g'`: on `[σ,∞)` the OZ solution `oz_h` is
differentiable with derivative `g'`, its first moment `r·oz_h(r)` decays to `0` and is integrable,
`oz_h + r·g'` is integrable, and the OZ-convolution/sine-transform integrands are integrable for
every `k > 0`. These are standard regularity/decay properties of the PY hard-sphere OZ solution in
the exterior (`c_HS` has compact support, so the convolution integrals converge), established in the
literature but not yet formalized from Mathlib real-analysis for the opaque `Classical.choose`-built
`oz_h`. This is the *only* remaining assumption behind the PY contact value; everything else
(BAXTER.6/7 + OZ.9b) is proved. -/
axiom oz_h_exterior_regularity {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∃ g' : ℝ → ℝ,
      (∀ r ∈ Ici sigma, HasDerivAt (oz_h eta sigma rho) (g' r) r) ∧
      Tendsto (fun r => r * oz_h eta sigma rho r) atTop (𝓝 0) ∧
      IntegrableOn (fun r => r * oz_h eta sigma rho r) (Ioi sigma) ∧
      IntegrableOn (fun r => oz_h eta sigma rho r + r * g' r) (Ioi sigma) ∧
      (∀ k : ℝ, 0 < k → ∀ r, sigma ≤ r → IntervalIntegrable
        (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
          if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma) ∧
      (∀ k : ℝ, 0 < k → ∀ r, sigma ≤ r → IntervalIntegrable
        (fun t => t * c_HS eta sigma t *
          ∫ s' in (max (r - t) sigma)..(r + t), s' * oz_h eta sigma rho s')
        MeasureTheory.volume 0 sigma) ∧
      (∀ k : ℝ, 0 < k → ∀ r ∈ Ioi (0 : ℝ), Integrable
        (fun p : ℝ × ℝ =>
          p.1 * c_HS eta sigma p.1 *
            (Icc |r - p.1| (r + p.1)).indicator (fun s => s * oz_h eta sigma rho s) p.2)
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) ∧
      (∀ k, 0 < k → Integrable
        (fun p : ℝ × ℝ × ℝ =>
          (p.2.1 * c_HS eta sigma p.2.1) *
            (Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
              (fun s => s * oz_h eta sigma rho s) p.2.2 *
            Real.sin (k * p.1))
        ((volume.restrict (Ioi 0)).prod
          ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))) ∧
      (∀ k, 0 < k → Integrable (fun r => r * c_HS eta sigma r * Real.sin (k * r))
        (volume.restrict (Ioi 0))) ∧
      (∀ k, 0 < k → Integrable
        (fun r => r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.sin (k * r))
        (volume.restrict (Ioi 0)))

/-- **Exact PY contact value (Task OZ.3), now a theorem.**

    g0_HS(σ) = (1 + η/2) / (1 - η)²

Same statement as the retired bare axiom (formerly in `PYOZ_GHS.lean`); proved by feeding the
`oz_h_exterior_regularity` witnesses into BAXTER.8 (`g0_HS_contact_value_of_oz_h_regularity`).
The physical contact value is thus *derived* from Fourier analysis (BAXTER.6/7 + OZ.9b), assuming
only the analytic regularity of the OZ exterior solution. Still in namespace `FMSA.HardSphere`, so
the fully-qualified name `FMSA.HardSphere.g0_HS_contact_value` is unchanged. -/
theorem g0_HS_contact_value {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    g0_HS eta sigma rho sigma = (1 + eta / 2) / (1 - eta) ^ 2 := by
  obtain ⟨g', hderiv, htendsto, hg_int, hg'_int,
      hintA1, hintA2, htsIntC, hjointC, hintB1, hintConv⟩ :=
    oz_h_exterior_regularity hsigma heta_def heta_lt
  exact g0_HS_contact_value_of_oz_h_regularity hsigma heta_def heta_lt g' hderiv htendsto
    hg_int hg'_int hintA1 hintA2 htsIntC hjointC hintB1 hintConv

end FMSA.HardSphere
