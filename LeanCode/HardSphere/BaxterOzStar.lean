/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.HardSphere.BaxterRenewalDecay

/-!
# `baxterPsi_ozstar` — the unconditional OZ★ renewal identity

`baxterPsi_eq_phi_add_rho_conv` (in `BaxterRenewal.lean`) is the OZ★ real-space renewal identity
for the constructed Baxter solution `baxterPsi`, carrying fourteen integrability side-conditions
(`hAminus … haddI2`).  This file discharges every one of them as a *theorem* (no axiom, no decay
hypothesis), producing the fully unconditional `baxterPsi_ozstar`.

All fourteen are pure integrability facts: the integrands are products of the globally continuous
`q0_poly`/`c_HS` factors and the globally *measurable* (piecewise-continuous) `baxterPsi`, over
finite intervals or a finite product measure.  The reusable toolkit:

* `baxterPsi_measurable` — `baxterPsi` is measurable (piecewise via a globally continuous clamp).
* `baxterPsiDom` / `baxterPsi_abs_le_dom` — a globally continuous dominator for `|baxterPsi|`.
* `baxterPsi_comp_bddOn_uIcc` — `|baxterPsi ∘ h|` is bounded on any `uIcc` for continuous `h`.
* `intervalIntegrable_of_aesm_bddOn` — a.e.-measurable + bounded ⟹ interval integrable.
* `measurable_intervalIntegral_param` — measurability of a parametric interval integral with
  measurable endpoints and integrand (handles the moving-endpoint inner integrals).
* `integrable_prod_restrict_of_measurable_bddOn` — measurable + bounded ⟹ integrable on the finite
  product measure `(volume.restrict (Ioc 0 σ)).prod (volume.restrict (Ioc 0 σ))`.
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-! ### Base integrability helpers -/

/-- A bounded, a.e.-strongly-measurable function is interval integrable on a finite interval. -/
theorem intervalIntegrable_of_aesm_bddOn {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    {a b C : ℝ} (hbdd : ∀ x ∈ Set.uIcc a b, |f x| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  have hfin : volume (Set.uIoc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top isCompact_uIcc.measure_ne_top (measure_mono Set.uIoc_subset_uIcc)
  refine Measure.integrableOn_of_bounded (M := C) hfin hf ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [Real.norm_eq_abs]
  exact hbdd x (Set.uIoc_subset_uIcc hx)

/-- A bounded, measurable function on `ℝ × ℝ` is integrable for the finite product measure
`(volume.restrict (Ioc 0 σ)).prod (volume.restrict (Ioc 0 σ))`. -/
theorem integrable_prod_restrict_of_measurable_bddOn {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {sigma C : ℝ}
    (hbdd : ∀ p ∈ (Set.Ioc (0 : ℝ) sigma) ×ˢ (Set.Ioc (0 : ℝ) sigma), |f p| ≤ C) :
    Integrable f
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma))) := by
  have hνfin : (volume.restrict (Set.Ioc (0 : ℝ) sigma)) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top.ne
  rw [← integrableOn_univ]
  refine Measure.integrableOn_of_bounded (M := C) ?_ hf.aestronglyMeasurable ?_
  · rw [← Set.univ_prod_univ, Measure.prod_prod]
    exact ENNReal.mul_ne_top hνfin hνfin
  · rw [Measure.restrict_univ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    rw [Real.norm_eq_abs]; exact hbdd p hp

/-! ### Measurability and continuous dominator for `baxterPsi` -/

/-- `baxterPsi` written with a globally continuous outer clamp `baxterPsiOuter (max · σ)`, so that
its measurability is manifest.  On `{σ ≤ v}`, `max v σ = v`; on `{v ≤ -σ}`, `max (-v) σ = -v`. -/
theorem baxterPsi_eq_clamp {eta sigma rho : ℝ} :
    baxterPsi eta sigma rho = fun v =>
      if sigma ≤ v then baxterPsiOuter eta sigma rho (max v sigma)
      else if v ≤ -sigma then -baxterPsiOuter eta sigma rho (max (-v) sigma)
      else -v := by
  funext v
  unfold baxterPsi
  split_ifs with h1 h2
  · rw [max_eq_left h1]
  · rw [max_eq_left (by linarith : sigma ≤ -v)]
  · rfl

/-- `baxterPsi` is measurable. -/
theorem baxterPsi_measurable {eta sigma rho : ℝ} : Measurable (baxterPsi eta sigma rho) := by
  rw [baxterPsi_eq_clamp]
  have hf1 : Continuous (fun v : ℝ => baxterPsiOuter eta sigma rho (max v sigma)) :=
    baxterPsiOuter_continuousOn_Ici.comp_continuous (by fun_prop) (fun x => le_max_right x sigma)
  have hf2 : Continuous (fun v : ℝ => baxterPsiOuter eta sigma rho (max (-v) sigma)) :=
    baxterPsiOuter_continuousOn_Ici.comp_continuous (by fun_prop) (fun x => le_max_right (-x) sigma)
  refine Measurable.ite measurableSet_Ici hf1.measurable ?_
  exact Measurable.ite measurableSet_Iic hf2.measurable.neg measurable_id.neg

/-- A globally continuous dominator for `|baxterPsi|`. -/
def baxterPsiDom (eta sigma rho : ℝ) (v : ℝ) : ℝ :=
  |baxterPsiOuter eta sigma rho (max v sigma)|
    + |baxterPsiOuter eta sigma rho (max (-v) sigma)| + |v|

theorem baxterPsiDom_nonneg {eta sigma rho : ℝ} (v : ℝ) : 0 ≤ baxterPsiDom eta sigma rho v := by
  unfold baxterPsiDom; positivity

theorem baxterPsiDom_continuous {eta sigma rho : ℝ} :
    Continuous (baxterPsiDom eta sigma rho) := by
  unfold baxterPsiDom
  have hf1 : Continuous (fun v : ℝ => baxterPsiOuter eta sigma rho (max v sigma)) :=
    baxterPsiOuter_continuousOn_Ici.comp_continuous (by fun_prop) (fun x => le_max_right x sigma)
  have hf2 : Continuous (fun v : ℝ => baxterPsiOuter eta sigma rho (max (-v) sigma)) :=
    baxterPsiOuter_continuousOn_Ici.comp_continuous (by fun_prop) (fun x => le_max_right (-x) sigma)
  exact ((hf1.abs).add (hf2.abs)).add continuous_abs

theorem baxterPsi_abs_le_dom {eta sigma rho : ℝ} (v : ℝ) :
    |baxterPsi eta sigma rho v| ≤ baxterPsiDom eta sigma rho v := by
  unfold baxterPsi baxterPsiDom
  split_ifs with h1 h2
  · rw [max_eq_left h1]
    have := abs_nonneg (baxterPsiOuter eta sigma rho (max (-v) sigma))
    have := abs_nonneg v
    linarith
  · rw [max_eq_left (by linarith : sigma ≤ -v), abs_neg]
    have := abs_nonneg (baxterPsiOuter eta sigma rho (max v sigma))
    have := abs_nonneg v
    linarith
  · rw [abs_neg]
    have := abs_nonneg (baxterPsiOuter eta sigma rho (max v sigma))
    have := abs_nonneg (baxterPsiOuter eta sigma rho (max (-v) sigma))
    linarith

/-- `|baxterPsi ∘ h|` is bounded on any `uIcc a b`, for continuous `h`. -/
theorem baxterPsi_comp_bddOn_uIcc {eta sigma rho : ℝ} {h : ℝ → ℝ} (hh : Continuous h) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |baxterPsi eta sigma rho (h s)| ≤ C := by
  have hcont : Continuous (fun s => baxterPsiDom eta sigma rho (h s)) :=
    baxterPsiDom_continuous.comp hh
  obtain ⟨x0, _, hx0⟩ := isCompact_uIcc.exists_isMaxOn Set.nonempty_uIcc hcont.continuousOn
  refine ⟨baxterPsiDom eta sigma rho (h x0), baxterPsiDom_nonneg _, fun s hs => ?_⟩
  exact le_trans (baxterPsi_abs_le_dom (h s)) (isMaxOn_iff.mp hx0 s hs)

/-- `|baxterPsi|` is bounded on any `uIcc a b`. -/
theorem baxterPsi_bddOn_uIcc {eta sigma rho : ℝ} (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |baxterPsi eta sigma rho s| ≤ C :=
  baxterPsi_comp_bddOn_uIcc continuous_id a b

/-- `|q0_poly|` is bounded on any `uIcc a b`. -/
theorem q0_poly_bddOn_uIcc {eta sigma rho : ℝ} (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |q0_poly eta sigma rho s| ≤ C := by
  have hcont := (q0_poly_continuous eta sigma rho).abs.continuousOn (s := Set.uIcc a b)
  obtain ⟨x0, _, hx0⟩ := isCompact_uIcc.exists_isMaxOn Set.nonempty_uIcc hcont
  exact ⟨|q0_poly eta sigma rho x0|, abs_nonneg _, fun s hs => isMaxOn_iff.mp hx0 s hs⟩

/-- `|c_HS|` is bounded on `Icc 0 σ` (via the continuous polynomial it agrees with there). -/
theorem c_HS_bddOn {eta sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0:ℝ) sigma, |c_HS eta sigma s| ≤ C := by
  have hgcont : Continuous
      (fun r => -(py_a0 eta + py_a1 eta * (r / sigma) + py_a3 eta * (r / sigma) ^ 3)) := by
    fun_prop
  obtain ⟨x0, _, hx0⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, ⟨le_rfl, hsigma.le⟩⟩ : (Set.Icc (0:ℝ) sigma).Nonempty) hgcont.abs.continuousOn
  refine ⟨|-(py_a0 eta + py_a1 eta * (x0 / sigma) + py_a3 eta * (x0 / sigma) ^ 3)|,
    abs_nonneg _, fun s hs => ?_⟩
  have hmax := isMaxOn_iff.mp hx0 s hs
  rcases lt_or_ge s sigma with h | h
  · rw [c_HS_inner h]; exact hmax
  · rw [c_HS_outer h, abs_zero]; exact abs_nonneg _

/-- Membership in `uIcc (-σ) σ` (the interval that carries every `q0_poly` argument). -/
theorem mem_uIcc_q0 {sigma x : ℝ} (hsigma : 0 < sigma) (h1 : -sigma ≤ x) (h2 : x ≤ sigma) :
    x ∈ Set.uIcc (-sigma) sigma := by
  rw [Set.uIcc_of_le (by linarith)]; exact ⟨h1, h2⟩

/-- Membership in `uIcc (r-σ) (r+σ)` (the interval that carries every `baxterPsi` argument). -/
theorem mem_uIcc_psi {sigma r x : ℝ} (hsigma : 0 < sigma) (h1 : r - sigma ≤ x)
    (h2 : x ≤ r + sigma) : x ∈ Set.uIcc (r - sigma) (r + sigma) := by
  rw [Set.uIcc_of_le (by linarith)]; exact ⟨h1, h2⟩

/-! ### Measurability of a parametric interval integral -/

/-- The parametric interval integral `t ↦ ∫ s in α t..β t, Φ t s` is measurable, provided the
uncurried integrand `(t, s) ↦ Φ t s` and the endpoints `α, β` are measurable.  Handles the
moving-endpoint inner integrals whose integrand (`baxterPsi`-composition) is only measurable. -/
theorem measurable_intervalIntegral_param {Φ : ℝ → ℝ → ℝ}
    (hΦ : Measurable (fun p : ℝ × ℝ => Φ p.1 p.2)) {α β : ℝ → ℝ}
    (hα : Measurable α) (hβ : Measurable β) :
    Measurable (fun t => ∫ s in α t..β t, Φ t s) := by
  have key : ∀ (a b : ℝ → ℝ), Measurable a → Measurable b →
      Measurable (fun t => ∫ s in Set.Ioc (a t) (b t), Φ t s ∂volume) := by
    intro a b ha hb
    have hset : MeasurableSet {p : ℝ × ℝ | a p.1 < p.2 ∧ p.2 ≤ b p.1} :=
      (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hb.comp measurable_fst))
    have hstep : Measurable (fun t => ∫ s,
        ({p : ℝ × ℝ | a p.1 < p.2 ∧ p.2 ≤ b p.1}).indicator (fun p => Φ p.1 p.2) (t, s) ∂volume) :=
      ((hΦ.indicator hset).stronglyMeasurable).integral_prod_right'.measurable
    have hconv : (fun t => ∫ s,
          ({p : ℝ × ℝ | a p.1 < p.2 ∧ p.2 ≤ b p.1}).indicator (fun p => Φ p.1 p.2) (t, s) ∂volume)
        = (fun t => ∫ s in Set.Ioc (a t) (b t), Φ t s ∂volume) := by
      funext t
      rw [← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioc]
    rwa [hconv] at hstep
  have hdef : (fun t => ∫ s in α t..β t, Φ t s)
      = (fun t => (∫ s in Set.Ioc (α t) (β t), Φ t s ∂volume)
          - ∫ s in Set.Ioc (β t) (α t), Φ t s ∂volume) := by
    funext t; rfl
  rw [hdef]
  exact (key α β hα hβ).sub (key β α hβ hα)

/-! ### Discharges — single-factor / product integrands (`hAminus`, `hAplus`, `hshell`, slices) -/

/-- `hAminus`: `q0_poly(u)·ψ(r-u)` is interval integrable on `[0,σ]`. -/
theorem ozstar_hAminus {eta sigma rho r : ℝ} :
    IntervalIntegrable
      (fun u => q0_poly eta sigma rho u * baxterPsi eta sigma rho (r - u)) volume 0 sigma := by
  obtain ⟨Cq, hCq0, hCq⟩ := q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) 0 sigma
  obtain ⟨Cp, hCp0, hCp⟩ := baxterPsi_comp_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho)
    (h := fun u => r - u) (by fun_prop) 0 sigma
  refine intervalIntegrable_of_aesm_bddOn (C := Cq * Cp) ?_ ?_
  · exact ((q0_poly_continuous eta sigma rho).measurable.mul
      (baxterPsi_measurable.comp (by fun_prop))).aestronglyMeasurable
  · intro x hx
    rw [abs_mul]
    exact mul_le_mul (hCq x hx) (hCp x hx) (abs_nonneg _) hCq0

/-- `hAplus`: `q0_poly(t)·ψ(r+t)` is interval integrable on `[0,σ]`. -/
theorem ozstar_hAplus {eta sigma rho r : ℝ} :
    IntervalIntegrable
      (fun t => q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + t)) volume 0 sigma := by
  obtain ⟨Cq, hCq0, hCq⟩ := q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) 0 sigma
  obtain ⟨Cp, hCp0, hCp⟩ := baxterPsi_comp_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho)
    (h := fun t => r + t) (by fun_prop) 0 sigma
  refine intervalIntegrable_of_aesm_bddOn (C := Cq * Cp) ?_ ?_
  · exact ((q0_poly_continuous eta sigma rho).measurable.mul
      (baxterPsi_measurable.comp (by fun_prop))).aestronglyMeasurable
  · intro x hx
    rw [abs_mul]
    exact mul_le_mul (hCq x hx) (hCp x hx) (abs_nonneg _) hCq0

/-- `hshell`: `ψ` is interval integrable on `[r-t, r+t]`. -/
theorem ozstar_hshell {eta sigma rho r t : ℝ} :
    IntervalIntegrable (baxterPsi eta sigma rho) volume (r - t) (r + t) := by
  obtain ⟨C, hC0, hC⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - t) (r + t)
  exact intervalIntegrable_of_aesm_bddOn baxterPsi_measurable.aestronglyMeasurable (C := C) hC

/-- Interval integrability of `c·q0_poly(s)·ψ(affine s)` on `[a,b]`, for a constant `c` and a
continuous affine argument `h`; the shared engine for the three slice hypotheses. -/
theorem ozstar_const_q0_psi {eta sigma rho : ℝ} (c : ℝ) {h : ℝ → ℝ} (hh : Continuous h)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s => c * q0_poly eta sigma rho s * baxterPsi eta sigma rho (h s)) volume a b := by
  obtain ⟨Cq, hCq0, hCq⟩ := q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) a b
  obtain ⟨Cp, hCp0, hCp⟩ :=
    baxterPsi_comp_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) hh a b
  refine intervalIntegrable_of_aesm_bddOn (C := |c| * Cq * Cp) ?_ ?_
  · exact (((measurable_const.mul (q0_poly_continuous eta sigma rho).measurable).mul
      (baxterPsi_measurable.comp hh.measurable))).aestronglyMeasurable
  · intro x hx
    rw [abs_mul, abs_mul]
    have hc : (0 : ℝ) ≤ |c| := abs_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hCq x hx) hc) (hCp x hx) (abs_nonneg _)
      (mul_nonneg hc hCq0)

/-- `hsliceL`: `q0_poly(t)·q0_poly(s)·ψ(r+t-s)` interval integrable on `[0,t]`. -/
theorem ozstar_hsliceL {eta sigma rho r : ℝ} (t : ℝ) :
    IntervalIntegrable
      (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) volume 0 t :=
  ozstar_const_q0_psi (q0_poly eta sigma rho t) (by fun_prop : Continuous (fun s => r + t - s)) 0 t

/-- `hsliceR`: `q0_poly(t)·q0_poly(s)·ψ(r+t-s)` interval integrable on `[t,σ]`. -/
theorem ozstar_hsliceR {eta sigma rho r : ℝ} (t : ℝ) :
    IntervalIntegrable
      (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) volume t sigma :=
  ozstar_const_q0_psi (q0_poly eta sigma rho t)
    (by fun_prop : Continuous (fun s => r + t - s)) t sigma

/-- `hsliceL2`: `q0_poly(s)·q0_poly(t)·ψ(r+s-t)` interval integrable on `[0,t]`. -/
theorem ozstar_hsliceL2 {eta sigma rho r : ℝ} (t : ℝ) :
    IntervalIntegrable
      (fun s => q0_poly eta sigma rho s * q0_poly eta sigma rho t
        * baxterPsi eta sigma rho (r + s - t)) volume 0 t := by
  have heq : (fun s => q0_poly eta sigma rho s * q0_poly eta sigma rho t
        * baxterPsi eta sigma rho (r + s - t))
      = (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + s - t)) := by
    funext s; ring
  rw [heq]
  exact ozstar_const_q0_psi (q0_poly eta sigma rho t)
    (by fun_prop : Continuous (fun s => r + s - t)) 0 t

/-! ### Discharges — parametric inner-integral integrands (`hAdbl`, `hKdblH`, `haddI/II/I2`) -/

/-- `hAdbl`: `q0_poly(t)·(∫₀^σ q0_poly(s)·ψ(r+t-s) ds)` is interval integrable on `[0,σ]`. -/
theorem ozstar_hAdbl {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable
      (fun t => q0_poly eta sigma rho t
        * ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s))
      volume 0 sigma := by
  obtain ⟨Cq, hCq0, hCq⟩ :=
    q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (-sigma) sigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hGmeas : Measurable (fun t => ∫ s in (0:ℝ)..sigma,
      q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s)) := by
    refine measurable_intervalIntegral_param
      (Φ := fun t s => q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s))
      (α := fun _ => 0) (β := fun _ => sigma) ?_ measurable_const measurable_const
    exact ((q0_poly_continuous eta sigma rho).measurable.comp measurable_snd).mul
      (baxterPsi_measurable.comp (by fun_prop))
  refine intervalIntegrable_of_aesm_bddOn (C := Cq * (Cq * Cψ * |sigma - 0|)) ?_ ?_
  · exact ((q0_poly_continuous eta sigma rho).measurable.mul hGmeas).aestronglyMeasurable
  · intro t ht
    rw [Set.uIcc_of_le hsigma.le] at ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [abs_mul]
    have hGb : |∫ s in (0:ℝ)..sigma,
          q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s)|
          ≤ Cq * Cψ * |sigma - 0| := by
      rw [← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
      rw [Set.uIoc_of_le hsigma.le] at hs
      obtain ⟨hs0, hs1⟩ := hs
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hCq s (mem_uIcc_q0 hsigma (by linarith) hs1))
        (hCψ (r + t - s) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
        (abs_nonneg _) hCq0
    exact mul_le_mul (hCq t (mem_uIcc_q0 hsigma (by linarith) ht1)) hGb (abs_nonneg _) hCq0

/-- `hKdblH`: `(∫_u^σ q0(t)·q0(t-u) dt)·(ψ(r-u)+ψ(r+u))` is interval integrable on `[0,σ]`. -/
theorem ozstar_hKdblH {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable
      (fun u => (∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      volume 0 sigma := by
  obtain ⟨Cq, hCq0, hCq⟩ :=
    q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (-sigma) sigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hKmeas : Measurable (fun u => ∫ t in u..sigma,
      q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)) := by
    refine measurable_intervalIntegral_param
      (Φ := fun u t => q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
      (α := fun u => u) (β := fun _ => sigma) ?_ measurable_id measurable_const
    exact ((q0_poly_continuous eta sigma rho).measurable.comp measurable_snd).mul
      ((q0_poly_continuous eta sigma rho).measurable.comp
        (measurable_snd.sub measurable_fst))
  have hBmeas : Measurable (fun u => baxterPsi eta sigma rho (r - u)
      + baxterPsi eta sigma rho (r + u)) :=
    (baxterPsi_measurable.comp (by fun_prop)).add (baxterPsi_measurable.comp (by fun_prop))
  refine intervalIntegrable_of_aesm_bddOn (C := Cq * Cq * sigma * (2 * Cψ)) ?_ ?_
  · exact (hKmeas.mul hBmeas).aestronglyMeasurable
  · intro u hu
    rw [Set.uIcc_of_le hsigma.le] at hu
    obtain ⟨hu0, hu1⟩ := hu
    rw [abs_mul]
    have hKb : |∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)|
        ≤ Cq * Cq * sigma := by
      have h1 : |∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)|
          ≤ Cq * Cq * |sigma - u| := by
        rw [← Real.norm_eq_abs]
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
        rw [Set.uIoc_of_le hu1] at ht
        obtain ⟨ht0, ht1⟩ := ht
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCq t (mem_uIcc_q0 hsigma (by linarith) ht1))
          (hCq (t - u) (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hCq0
      have h2 : |sigma - u| ≤ sigma := by rw [abs_of_nonneg (by linarith)]; linarith
      calc |∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)|
          ≤ Cq * Cq * |sigma - u| := h1
        _ ≤ Cq * Cq * sigma := by
            exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hCq0 hCq0)
    have hBb : |baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)| ≤ 2 * Cψ := by
      calc |baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)|
          ≤ |baxterPsi eta sigma rho (r - u)| + |baxterPsi eta sigma rho (r + u)| := abs_add_le _ _
        _ ≤ Cψ + Cψ := add_le_add (hCψ (r - u) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
            (hCψ (r + u) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
        _ = 2 * Cψ := by ring
    exact mul_le_mul hKb hBb (abs_nonneg _) (by positivity)

/-- `haddI`: `∫₀^t q0(t)·q0(s)·ψ(r+t-s) ds` is interval integrable in `t` on `[0,σ]`. -/
theorem ozstar_haddI {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..t, q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) volume 0 sigma := by
  obtain ⟨Cq, hCq0, hCq⟩ :=
    q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (-sigma) sigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hFmeas : Measurable (fun t => ∫ s in (0:ℝ)..t, q0_poly eta sigma rho t
      * q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s)) := by
    refine measurable_intervalIntegral_param
      (Φ := fun t s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s))
      (α := fun _ => 0) (β := fun t => t) ?_ measurable_const measurable_id
    exact (((q0_poly_continuous eta sigma rho).measurable.comp measurable_fst).mul
      ((q0_poly_continuous eta sigma rho).measurable.comp measurable_snd)).mul
      (baxterPsi_measurable.comp (by fun_prop))
  refine intervalIntegrable_of_aesm_bddOn (C := Cq * Cq * Cψ * sigma)
    hFmeas.aestronglyMeasurable ?_
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hb : |∫ s in (0:ℝ)..t, q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)| ≤ Cq * Cq * Cψ * |t - 0| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
    rw [Set.uIoc_of_le ht0] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hCq t (mem_uIcc_q0 hsigma (by linarith) ht1))
      (hCq s (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hCq0)
      (hCψ (r + t - s) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      (abs_nonneg _) (mul_nonneg hCq0 hCq0)
  have hlen : |t - 0| ≤ sigma := by rw [abs_of_nonneg (by linarith)]; linarith
  exact le_trans hb (mul_le_mul_of_nonneg_left hlen (mul_nonneg (mul_nonneg hCq0 hCq0) hCψ0))

/-- `haddII`: `∫_t^σ q0(t)·q0(s)·ψ(r+t-s) ds` is interval integrable in `t` on `[0,σ]`. -/
theorem ozstar_haddII {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable
      (fun t => ∫ s in t..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) volume 0 sigma := by
  obtain ⟨Cq, hCq0, hCq⟩ :=
    q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (-sigma) sigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hFmeas : Measurable (fun t => ∫ s in t..sigma, q0_poly eta sigma rho t
      * q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s)) := by
    refine measurable_intervalIntegral_param
      (Φ := fun t s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s))
      (α := fun t => t) (β := fun _ => sigma) ?_ measurable_id measurable_const
    exact (((q0_poly_continuous eta sigma rho).measurable.comp measurable_fst).mul
      ((q0_poly_continuous eta sigma rho).measurable.comp measurable_snd)).mul
      (baxterPsi_measurable.comp (by fun_prop))
  refine intervalIntegrable_of_aesm_bddOn (C := Cq * Cq * Cψ * sigma)
    hFmeas.aestronglyMeasurable ?_
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hb : |∫ s in t..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)| ≤ Cq * Cq * Cψ * |sigma - t| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
    rw [Set.uIoc_of_le ht1] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hCq t (mem_uIcc_q0 hsigma (by linarith) ht1))
      (hCq s (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hCq0)
      (hCψ (r + t - s) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      (abs_nonneg _) (mul_nonneg hCq0 hCq0)
  have hlen : |sigma - t| ≤ sigma := by rw [abs_of_nonneg (by linarith)]; linarith
  exact le_trans hb (mul_le_mul_of_nonneg_left hlen (mul_nonneg (mul_nonneg hCq0 hCq0) hCψ0))

/-- `haddI2`: `∫₀^t q0(s)·q0(t)·ψ(r+s-t) ds` is interval integrable in `t` on `[0,σ]`. -/
theorem ozstar_haddI2 {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..t, q0_poly eta sigma rho s * q0_poly eta sigma rho t
        * baxterPsi eta sigma rho (r + s - t)) volume 0 sigma := by
  obtain ⟨Cq, hCq0, hCq⟩ :=
    q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (-sigma) sigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hFmeas : Measurable (fun t => ∫ s in (0:ℝ)..t, q0_poly eta sigma rho s
      * q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + s - t)) := by
    refine measurable_intervalIntegral_param
      (Φ := fun t s => q0_poly eta sigma rho s * q0_poly eta sigma rho t
        * baxterPsi eta sigma rho (r + s - t))
      (α := fun _ => 0) (β := fun t => t) ?_ measurable_const measurable_id
    exact (((q0_poly_continuous eta sigma rho).measurable.comp measurable_snd).mul
      ((q0_poly_continuous eta sigma rho).measurable.comp measurable_fst)).mul
      (baxterPsi_measurable.comp (by fun_prop))
  refine intervalIntegrable_of_aesm_bddOn (C := Cq * Cq * Cψ * sigma)
    hFmeas.aestronglyMeasurable ?_
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hb : |∫ s in (0:ℝ)..t, q0_poly eta sigma rho s * q0_poly eta sigma rho t
        * baxterPsi eta sigma rho (r + s - t)| ≤ Cq * Cq * Cψ * |t - 0| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
    rw [Set.uIoc_of_le ht0] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hCq s (mem_uIcc_q0 hsigma (by linarith) (by linarith)))
      (hCq t (mem_uIcc_q0 hsigma (by linarith) ht1)) (abs_nonneg _) hCq0)
      (hCψ (r + s - t) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      (abs_nonneg _) (mul_nonneg hCq0 hCq0)
  have hlen : |t - 0| ≤ sigma := by rw [abs_of_nonneg (by linarith)]; linarith
  exact le_trans hb (mul_le_mul_of_nonneg_left hlen (mul_nonneg (mul_nonneg hCq0 hCq0) hCψ0))

/-! ### Discharges — product-measure integrands (`hjoint`, `hswapD`, `hswapA`) -/

/-- `hjoint`: the Fubini integrand for the forcing term is integrable on the finite product. -/
theorem ozstar_hjoint {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * c_HS eta sigma s) s
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma))) := by
  obtain ⟨Cc, hCc0, hCc⟩ := c_HS_bddOn (eta := eta) (sigma := sigma) hsigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hAind : Measurable
      (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (fun s => s * c_HS eta sigma s) p.2) := by
    have heq : (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (fun s => s * c_HS eta sigma s) p.2)
        = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => p.2 * c_HS eta sigma p.2) := by
      funext p; simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_setOf_eq]
    rw [heq]
    exact (measurable_snd.mul ((c_HS_measurable eta sigma).comp measurable_snd)).indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have hBind : Measurable (fun p : ℝ × ℝ =>
      baxterPsi eta sigma rho (r - p.1) + baxterPsi eta sigma rho (r + p.1)) :=
    (baxterPsi_measurable.comp (by fun_prop)).add (baxterPsi_measurable.comp (by fun_prop))
  refine integrable_prod_restrict_of_measurable_bddOn (C := sigma * Cc * (2 * Cψ))
    (hAind.mul hBind) ?_
  intro p hp
  have hp1 := hp.1
  have hp2 := hp.2
  rw [Set.mem_Ioc] at hp1 hp2
  have hAb : |(Set.Ioi p.1).indicator (fun s => s * c_HS eta sigma s) p.2| ≤ sigma * Cc := by
    rw [Set.indicator_apply]
    split_ifs with h
    · rw [abs_mul]
      exact mul_le_mul (by rw [abs_of_pos hp2.1]; exact hp2.2) (hCc p.2 ⟨hp2.1.le, hp2.2⟩)
        (abs_nonneg _) hsigma.le
    · rw [abs_zero]; exact mul_nonneg hsigma.le hCc0
  have hBb : |baxterPsi eta sigma rho (r - p.1)
      + baxterPsi eta sigma rho (r + p.1)| ≤ 2 * Cψ := by
    calc |baxterPsi eta sigma rho (r - p.1) + baxterPsi eta sigma rho (r + p.1)|
        ≤ |baxterPsi eta sigma rho (r - p.1)| + |baxterPsi eta sigma rho (r + p.1)| :=
          abs_add_le _ _
      _ ≤ Cψ + Cψ := add_le_add (hCψ (r - p.1) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
          (hCψ (r + p.1) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      _ = 2 * Cψ := by ring
  change |(Set.Ioi p.1).indicator (fun s => s * c_HS eta sigma s) p.2
      * (baxterPsi eta sigma rho (r - p.1) + baxterPsi eta sigma rho (r + p.1))| ≤ _
  rw [abs_mul]
  exact mul_le_mul hAb hBb (abs_nonneg _) (mul_nonneg hsigma.le hCc0)

/-- `hswapD`: the Fubini integrand for the double kernel is integrable on the finite product. -/
theorem ozstar_hswapD {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    Integrable
      (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))) t)
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma))) := by
  obtain ⟨Cq, hCq0, hCq⟩ :=
    q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (-sigma) sigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hmeas : Measurable (Function.uncurry fun u t => (Set.Ioi u).indicator
      (fun t => q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))) t) := by
    have heq : (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))) t)
        = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => q0_poly eta sigma rho p.2
            * q0_poly eta sigma rho (p.2 - p.1)
            * (baxterPsi eta sigma rho (r - p.1) + baxterPsi eta sigma rho (r + p.1))) := by
      funext p; simp only [Function.uncurry, Set.indicator_apply, Set.mem_Ioi, Set.mem_setOf_eq]
    rw [heq]
    refine Measurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
    exact (((q0_poly_continuous eta sigma rho).measurable.comp measurable_snd).mul
      ((q0_poly_continuous eta sigma rho).measurable.comp
        (measurable_snd.sub measurable_fst))).mul
      ((baxterPsi_measurable.comp (by fun_prop)).add (baxterPsi_measurable.comp (by fun_prop)))
  refine integrable_prod_restrict_of_measurable_bddOn (C := Cq * Cq * (2 * Cψ)) hmeas ?_
  intro p hp
  have hp1 := hp.1
  have hp2 := hp.2
  rw [Set.mem_Ioc] at hp1 hp2
  change |(Set.Ioi p.1).indicator
      (fun t => q0_poly eta sigma rho t * q0_poly eta sigma rho (t - p.1)
        * (baxterPsi eta sigma rho (r - p.1) + baxterPsi eta sigma rho (r + p.1))) p.2| ≤ _
  rw [Set.indicator_apply]
  split_ifs with h
  · rw [abs_mul, abs_mul]
    have hBb : |baxterPsi eta sigma rho (r - p.1)
        + baxterPsi eta sigma rho (r + p.1)| ≤ 2 * Cψ := by
      calc |baxterPsi eta sigma rho (r - p.1) + baxterPsi eta sigma rho (r + p.1)|
          ≤ |baxterPsi eta sigma rho (r - p.1)| + |baxterPsi eta sigma rho (r + p.1)| :=
            abs_add_le _ _
        _ ≤ Cψ + Cψ := add_le_add (hCψ (r - p.1) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
            (hCψ (r + p.1) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
        _ = 2 * Cψ := by ring
    exact mul_le_mul (mul_le_mul (hCq p.2 (mem_uIcc_q0 hsigma (by linarith) hp2.2))
      (hCq (p.2 - p.1) (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hCq0)
      hBb (abs_nonneg _) (mul_nonneg hCq0 hCq0)
  · rw [abs_zero]
    exact mul_nonneg (mul_nonneg hCq0 hCq0) (mul_nonneg (by norm_num) hCψ0)

/-- `hswapA`: the Fubini integrand for the outer double integral is integrable on the product. -/
theorem ozstar_hswapA {eta sigma rho r : ℝ} (hsigma : 0 < sigma) :
    Integrable
      (Function.uncurry fun t s => (Set.Ioi t).indicator
        (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
          * baxterPsi eta sigma rho (r + t - s)) s)
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma))) := by
  obtain ⟨Cq, hCq0, hCq⟩ :=
    q0_poly_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (-sigma) sigma
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    baxterPsi_bddOn_uIcc (eta := eta) (sigma := sigma) (rho := rho) (r - sigma) (r + sigma)
  have hmeas : Measurable (Function.uncurry fun t s => (Set.Ioi t).indicator
      (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) s) := by
    have heq : (Function.uncurry fun t s => (Set.Ioi t).indicator
        (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
          * baxterPsi eta sigma rho (r + t - s)) s)
        = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => q0_poly eta sigma rho p.1
            * q0_poly eta sigma rho p.2 * baxterPsi eta sigma rho (r + p.1 - p.2)) := by
      funext p; simp only [Function.uncurry, Set.indicator_apply, Set.mem_Ioi, Set.mem_setOf_eq]
    rw [heq]
    refine Measurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
    exact (((q0_poly_continuous eta sigma rho).measurable.comp measurable_fst).mul
      ((q0_poly_continuous eta sigma rho).measurable.comp measurable_snd)).mul
      (baxterPsi_measurable.comp (by fun_prop))
  refine integrable_prod_restrict_of_measurable_bddOn (C := Cq * Cq * Cψ) hmeas ?_
  intro p hp
  have hp1 := hp.1
  have hp2 := hp.2
  rw [Set.mem_Ioc] at hp1 hp2
  change |(Set.Ioi p.1).indicator
      (fun s => q0_poly eta sigma rho p.1 * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + p.1 - s)) p.2| ≤ _
  rw [Set.indicator_apply]
  split_ifs with h
  · rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hCq p.1 (mem_uIcc_q0 hsigma (by linarith) hp1.2))
      (hCq p.2 (mem_uIcc_q0 hsigma (by linarith) hp2.2)) (abs_nonneg _) hCq0)
      (hCψ (r + p.1 - p.2) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      (abs_nonneg _) (mul_nonneg hCq0 hCq0)
  · rw [abs_zero]; exact mul_nonneg (mul_nonneg hCq0 hCq0) hCψ0

/-! ### The unconditional OZ★ identity -/

/-- **OZ★, unconditional.**  The real-space Ornstein–Zernike renewal identity for the constructed
Baxter solution `baxterPsi`, with all fourteen integrability side-conditions of
`baxterPsi_eq_phi_add_rho_conv` discharged as theorems (no axiom, no decay hypothesis). -/
theorem baxterPsi_ozstar {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ r, 0 < r → baxterPsi eta sigma rho r
      = r * c_HS eta sigma r
        + rho * (r * radial3d_conv (c_HS eta sigma)
            (fun x => baxterPsi eta sigma rho x / x) r) := by
  intro r hr
  exact baxterPsi_eq_phi_add_rho_conv hsigma heta heta_def hr
    ozstar_hAminus ozstar_hAplus (ozstar_hAdbl hsigma) (ozstar_hKdblH hsigma)
    (fun t _ => ozstar_hshell) (ozstar_hjoint hsigma) (ozstar_hswapD hsigma)
    (ozstar_hswapA hsigma) ozstar_hsliceL ozstar_hsliceR ozstar_hsliceL2
    (ozstar_haddI hsigma) (ozstar_haddII hsigma) (ozstar_haddI2 hsigma)

end

end FMSA.HardSphere
