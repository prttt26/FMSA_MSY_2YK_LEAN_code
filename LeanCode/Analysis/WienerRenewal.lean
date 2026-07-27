/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.IntervalIntegralSwap
import LeanCode.Analysis.Volterra

/-!
# Paley–Wiener renewal decay — reduced to Wiener's `1/f` theorem (`MA.13`)

Registry: `MATH_AXIOMS.md`, task `MA.13`.  **Status (2026-07-21): `volterra_renewal_tendsto_zero` is
a THEOREM.**  The former bespoke axiom has been replaced by the single *named classical theorem*
`wiener_causal_resolvent` (Wiener's `1/f` / Gelfand inversion in the causal `L¹` convolution
algebra), from which everything else in this file is proved:

  `wiener_causal_resolvent`  (axiom — Mathlib has no Wiener algebra)
      ⇒ `resolvent_conv_eq`        (Fubini on the triangle + the resolvent equation)
      ⇒ `volterra_unique_Ici`      (`MA.10` uniqueness ⇒ `ψ = g + R ⋆ g`)
      ⇒ `resolvent_conv_tendsto_zero` (moving-window `L¹` tail)   ⇒ `ψ → 0`
      ⇒ `resolvent_conv_integrable`   (Young)                     ⇒ `ψ ∈ L¹(0,∞)`

so the assumed content is now exactly one theorem with a name, not a statement bundling decay,
integrability and the resolvent construction together.

## Statement

For a **right-compactly-supported** continuous kernel `q` (`q = 0` on `(S, ∞)`) and a continuous
forcing `g` that vanishes on a right tail, if the **Laplace symbol** `1 − q̂(z)`,
`q̂(z) = ∫₀^S q(t) e^{−zt} dt`, has **no zero in the closed right half-plane** `{Re z ≥ 0}`, then
(unique, continuous) solution of the renewal / Volterra second-kind equation

  `ψ(r) = g(r) + ∫₀^r q(r−t) ψ(t) dt`   (`r ≥ 0`)

both decays (`ψ(r) → 0` as `r → ∞`) and is **integrable** on `(0,∞)`.  Both follow from the same
Paley–Wiener resolvent representation `ψ = g + R ⋆ g` with `g` compactly supported (hence `L¹`) and
`R ∈ L¹` the causal Wiener resolvent, so `ψ ∈ L¹(ℝ₊)` and `ψ → 0`.

**Only `q|_{[0,S]}` enters.** The equation evaluates `q` at `r − t ∈ [0, r] ≥ 0` and the symbol
integrates over `[0, S]`, so the kernel's values on `(−∞, 0)` are irrelevant to both the equation
and the conclusion. The hypothesis therefore requires only `q = 0` on `(S, ∞)` — **no `t < 0`
"causality" clause** (which would be unsatisfiable by the intended instance `q0_poly`, a nonzero
polynomial for `t < 0`). Dropping it strengthens the statement (weaker hypothesis) without affecting
truth, and makes it instantiable at `q0_poly`. Verified numerically (`ma13_verify.py`,
`ma13_dense.py`): dense **negative** kernels (matching `q0_poly`'s sign, `‖q‖₁ ≥ 1`) with symbol
nonvanishing on the RHP give decay; a symbol with any RHP zero gives exponential growth (the symbol
hypothesis is load-bearing, not vacuous).

## Why the remaining assumption is genuinely axiom-worthy

Only the resolvent's *existence* is assumed.  That is irreducible here: in the physical regime
`η ≥ (3−√7)/2` one has `‖q‖₁ ≥ 1`, and the spectral radius of `q` in this algebra is
`sup_{Re z ≥ 0}|q̂(z)| = |q̂(0)| = ‖q‖₁ > 1`, so the Neumann series for `R` **diverges** — the
resolvent exists only by Wiener's `1/f` theorem (nonvanishing on the maximal ideal space, here the
closed right half-plane).  Mathlib has no Wiener algebra, no Laplace transform, no Paley–Wiener and
no Hardy spaces (re-verified 2026-07-21), so this is a **library gap**, not an effort gap.  Every
elementary substitute was tried and refuted — see `proof_notes_pole.md` → "POLE.11 decay half /
MA.13".  It is a **pure analysis** statement (no physics), hence Group MA.

## Instantiation

Discharge the `Tendsto (baxterPsiOuter …) atTop (𝓝 0)` hypothesis of
`baxterPsi_bounded_Ici_of_tendsto_zero` / `r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero`
(`HardSphere/BaxterExteriorDecayReduction.lean`) at `q := q0_poly`, `g := baxterForcing`,
`ψ := baxterPsiOuter` — after the `[σ,∞) → [0,∞)` shift and the symbol identification `z = i k`
(so `{Re z ≥ 0} ↔ {Im k ≤ 0}`, matching `Qhat_complex(k) ≠ 1` on the closed lower half-plane; cf.
`HardSphere/BaxterHermiteBiehler.lean`).
-/

open MeasureTheory Filter Topology intervalIntegral

namespace FMSA

/-! ### The axiom: Wiener's `1/f` theorem for the causal `L¹` convolution algebra

`ℂ·δ ⊕ L¹(0,∞)` is a commutative Banach algebra under convolution whose maximal ideal space is the
**closed right half-plane** (plus the point at infinity), the Gelfand transform being the Laplace
transform `q ↦ q̂`.  Wiener's `1/f` theorem says an element is invertible exactly when its Gelfand
transform does not vanish on that space.  Applied to `δ − q` (whose transform is `1 − q̂`) this
gives
the **causal resolvent** `R ∈ L¹(0,∞)` with `R = q + q ⋆ R`.

This is the *only* thing assumed below; everything else in this file is proved from it.  It is the
irreducible gap: with `‖q‖₁ ≥ 1` (the physical regime, `η ≥ (3−√7)/2`) the Neumann series for the
resolvent **diverges** — the spectral radius here is `sup_{Re z ≥ 0}|q̂(z)| = |q̂(0)| = ‖q‖₁`
— so the resolvent's existence is genuinely the Gelfand/Wiener statement and not a contraction
argument.  See `proof_notes_pole.md` → "POLE.11 decay half / MA.13" for the full route triage and
`verify_ma13_route.py` for the numerical confirmation (including that the resulting decay rate is
exactly the Ornstein–Zernike one, `Im k₁` of the lowest Baxter pole). -/
axiom wiener_causal_resolvent {q : ℝ → ℝ} {S : ℝ} (hS : 0 < S)
    (hq : Continuous q) (hqsupp : ∀ t : ℝ, S < t → q t = 0)
    (hsymbol : ∀ z : ℂ, 0 ≤ z.re →
      1 - (∫ t in (0:ℝ)..S, (q t : ℂ) * Complex.exp (-z * (t : ℂ))) ≠ 0) :
    ∃ R : ℝ → ℝ, Continuous R ∧ IntegrableOn R (Set.Ioi 0) ∧
      ∀ x : ℝ, 0 ≤ x → R x = q x + ∫ t in (0:ℝ)..x, q (x - t) * R t

/-- Joint integrability of the triangle indicator for a jointly continuous integrand on `(0,x]²` —
the hypothesis `intervalIntegral_triangle_swap_gen` takes.  Bounded (continuous on a compact box) ×
finite measure. -/
private theorem triangle_indicator_integrable {x : ℝ} (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) :
    MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (F u) s)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 x)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 x))) := by
  have hEq : (Function.uncurry fun u s => (Set.Ioi u).indicator (F u) s)
      = Set.indicator {p : ℝ × ℝ | p.1 < p.2} (Function.uncurry F) := by
    funext p
    by_cases h : p.1 < p.2 <;>
      simp [Function.uncurry, Set.indicator_apply, Set.mem_Ioi, h]
  have hmeasSet : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hF.continuousOn (s := Set.Icc 0 x ×ˢ Set.Icc 0 x))
  rw [hEq, MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := C) ?_ ?_ ?_
  · rw [MeasureTheory.Measure.prod_prod, Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · exact (hF.measurable.indicator hmeasSet).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hpbox : p ∈ Set.Icc (0:ℝ) x ×ˢ Set.Icc (0:ℝ) x :=
      ⟨Set.Ioc_subset_Icc_self hp.1, Set.Ioc_subset_Icc_self hp.2⟩
    by_cases h : p.1 < p.2
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < p.2} from h)]
      exact hC p hpbox
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < p.2} from h)]
      simpa using le_trans (norm_nonneg (Function.uncurry F p)) (hC p hpbox)

/-- **The resolvent turns the renewal equation into a formula.**  With `R` the causal resolvent
(`R = q + q ⋆ R`), the candidate `φ = g + R ⋆ g` satisfies `q ⋆ φ = R ⋆ g`, which is exactly the
statement that `φ` solves `φ = g + q ⋆ φ`.  Pure Fubini on the triangle `{0 ≤ u ≤ t ≤ x}` plus the
inner change of variable `t = v + u` and one application of the resolvent equation at `x − u`. -/
private theorem resolvent_conv_eq {q R g : ℝ → ℝ} (hq : Continuous q) (hR : Continuous R)
    (hg : Continuous g)
    (hres : ∀ x : ℝ, 0 ≤ x → R x = q x + ∫ t in (0:ℝ)..x, q (x - t) * R t)
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0:ℝ)..x, q (x - t) * (g t + ∫ s in (0:ℝ)..t, R (t - s) * g s))
      = ∫ t in (0:ℝ)..x, R (x - t) * g t := by
  -- The inner double integrand, as a jointly continuous function of `(u, t)`.
  set F : ℝ → ℝ → ℝ := fun u t => q (x - t) * (R (t - u) * g u) with hF
  have hFcont : Continuous (Function.uncurry F) := by
    simp only [hF]
    exact (hq.comp (continuous_const.sub continuous_snd)).mul
      ((hR.comp (continuous_snd.sub continuous_fst)).mul (hg.comp continuous_fst))
  -- Split off the `g`-only part.
  have hA : IntervalIntegrable (fun t => q (x - t) * g t) MeasureTheory.volume 0 x :=
    ((hq.comp (continuous_const.sub continuous_id)).mul hg).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..t, F s t) MeasureTheory.volume 0 x := by
    apply Continuous.intervalIntegrable
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_id
    simp only [hF]
    exact (hq.comp (continuous_const.sub continuous_fst)).mul
      ((hR.comp (continuous_fst.sub continuous_snd)).mul (hg.comp continuous_snd))
  have hpt : ∀ t : ℝ, q (x - t) * (g t + ∫ s in (0:ℝ)..t, R (t - s) * g s)
      = q (x - t) * g t + ∫ s in (0:ℝ)..t, F s t := by
    intro t
    have hin : (∫ s in (0:ℝ)..t, F s t) = q (x - t) * ∫ s in (0:ℝ)..t, R (t - s) * g s := by
      rw [← intervalIntegral.integral_const_mul]
    rw [hin, mul_add]
  rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_add hA hB]
  -- Fubini on the triangle, then the inner substitution + resolvent equation.
  rw [← intervalIntegral_triangle_swap_gen hx F (triangle_indicator_integrable F hFcont)]
  have hinner : ∀ u ∈ Set.uIcc (0:ℝ) x, (∫ t in u..x, F u t) = g u * (R (x - u) - q (x - u)) := by
    intro u hu
    rw [Set.uIcc_of_le hx] at hu
    have hxu : (0:ℝ) ≤ x - u := by linarith [hu.2]
    have hcv : (∫ v in (0:ℝ)..(x - u), F u (v + u)) = ∫ t in u..x, F u t := by
      have := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := x - u)
        (f := fun t => F u t) u
      simpa using this
    rw [← hcv]
    have hstep : (∫ v in (0:ℝ)..(x - u), F u (v + u))
        = g u * ∫ v in (0:ℝ)..(x - u), q ((x - u) - v) * R v := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v _ => ?_
      simp only [hF]
      rw [show v + u - u = v by ring, show x - (v + u) = x - u - v by ring]
      ring
    have hI : (∫ v in (0:ℝ)..(x - u), q ((x - u) - v) * R v) = R (x - u) - q (x - u) := by
      have h := hres (x - u) hxu
      linarith
    rw [hstep, hI]
  rw [intervalIntegral.integral_congr hinner]
  -- Recombine: the two `q`-terms cancel, leaving `R ⋆ g`.
  have hfin : (∫ u in (0:ℝ)..x, g u * (R (x - u) - q (x - u)))
      = (∫ t in (0:ℝ)..x, R (x - t) * g t) - ∫ t in (0:ℝ)..x, q (x - t) * g t := by
    rw [← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun u _ => ?_; ring
    · exact ((hR.comp (continuous_const.sub continuous_id)).mul hg).intervalIntegrable _ _
    · exact hA
  rw [hfin]; ring

/-- **Two continuous solutions of the same renewal equation on `[0,∞)` agree.**  Uniqueness is
`MA.10` (`volterra_convolution_existsUnique`) applied on each `Icc 0 r`; the only work is
packaging a
function on `[0,∞)` as a `C(Icc 0 r, ℝ)` and undoing `Set.IccExtend` inside the integral. -/
private theorem volterra_unique_Ici {q g u w : ℝ → ℝ} (hq : Continuous q) (hg : Continuous g)
    (hu : ContinuousOn u (Set.Ici 0)) (hw : ContinuousOn w (Set.Ici 0))
    (hueq : ∀ r : ℝ, 0 ≤ r → u r = g r + ∫ t in (0:ℝ)..r, q (r - t) * u t)
    (hweq : ∀ r : ℝ, 0 ≤ r → w r = g r + ∫ t in (0:ℝ)..r, q (r - t) * w t) :
    ∀ r : ℝ, 0 ≤ r → u r = w r := by
  intro r hr
  obtain ⟨v, -, hvuniq⟩ := volterra_convolution_existsUnique hr q g hq hg
  -- Package a solution on `[0,∞)` as a fixed point of the `Icc 0 r` Volterra operator.
  have key : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Ici 0) →
      (∀ s : ℝ, 0 ≤ s → f s = g s + ∫ t in (0:ℝ)..s, q (s - t) * f t) →
      ∃ F : C(Set.Icc (0:ℝ) r, ℝ), (∀ p : Set.Icc (0:ℝ) r, F p = f (p : ℝ)) ∧ F = v := by
    intro f hf hfeq
    have hsub : Set.Icc (0:ℝ) r ⊆ Set.Ici 0 := fun t ht => ht.1
    refine ⟨⟨Set.restrict (Set.Icc (0:ℝ) r) f, (hf.mono hsub).restrict⟩, fun p => rfl, ?_⟩
    refine hvuniq _ (fun p => ?_)
    have hp0 : (0:ℝ) ≤ (p : ℝ) := p.2.1
    have hcongr : (∫ t in (0:ℝ)..(p : ℝ), q ((p : ℝ) - t) *
          Set.IccExtend hr (⟨Set.restrict (Set.Icc (0:ℝ) r) f, (hf.mono hsub).restrict⟩ :
            C(Set.Icc (0:ℝ) r, ℝ)) t)
        = ∫ t in (0:ℝ)..(p : ℝ), q ((p : ℝ) - t) * f t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hp0] at ht
      have htmem : t ∈ Set.Icc (0:ℝ) r := ⟨ht.1, le_trans ht.2 p.2.2⟩
      simp only [Set.IccExtend, Function.comp_apply, Set.projIcc_of_mem hr htmem]
      rfl
    show f (p : ℝ) = _
    rw [hcongr]
    exact hfeq (p : ℝ) hp0
  obtain ⟨U, hU1, hUv⟩ := key u hu hueq
  obtain ⟨W, hW1, hWv⟩ := key w hw hweq
  have hUW : U = W := hUv.trans hWv.symm
  have := congrArg (fun F : C(Set.Icc (0:ℝ) r, ℝ) => F ⟨r, ⟨hr, le_refl r⟩⟩) hUW
  simpa [hU1, hW1] using this

/-- `R ⋆ g → 0` when `R ∈ L¹(0,∞)` and `g` is continuous and vanishes past `T`: only the window
`[x−T, x]` of `R` contributes, and an `L¹` function has vanishing tail integrals. -/
private theorem resolvent_conv_tendsto_zero {R g : ℝ → ℝ} (hRcont : Continuous R)
    (hg : Continuous g) (hRint : IntegrableOn R (Set.Ioi 0)) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ t : ℝ, T ≤ t → g t = 0) :
    Tendsto (fun x => ∫ t in (0:ℝ)..x, R (x - t) * g t) atTop (𝓝 0) := by
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn (s := Set.Icc 0 T))
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (g 0)) (hCg 0 ⟨le_refl 0, hT0⟩)
  have hRabs : IntegrableOn (fun v => |R v|) (Set.Ioi 0) := hRint.abs
  -- the `L¹` tail of `|R|` over the moving window
  have htail : Tendsto (fun x : ℝ => ∫ v in Set.Ioi (x - T), |R v|) atTop (𝓝 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero (f := fun v => |R v|)
      (tendsto_atTop_add_const_right _ (-T) tendsto_id)
  refine squeeze_zero_norm' ?_ (by simpa using htail.const_mul Cg)
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (0:ℝ)] with x hxT hx0
  -- past `T` the forcing vanishes, so the integral truncates to `[0,T]`
  have hsplit : (∫ t in (0:ℝ)..x, R (x - t) * g t) = ∫ t in (0:ℝ)..T, R (x - t) * g t := by
    have hzero : (∫ t in T..x, R (x - t) * g t) = 0 := by
      rw [show (0:ℝ) = ∫ _t in T..x, (0:ℝ) by simp]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hxT] at ht
      rw [hT t ht.1, mul_zero]
    have hcont : Continuous (fun t : ℝ => R (x - t) * g t) := by fun_prop
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := T) (c := x)
      (f := fun t => R (x - t) * g t)
      (hcont.intervalIntegrable 0 T) (hcont.intervalIntegrable T x)
    rw [hzero, add_zero] at hadd
    exact hadd.symm
  rw [hsplit]
  -- `|∫_0^T R(x−t) g t dt| ≤ Cg · ∫_{x−T}^x |R|` and the window sits inside `Ioi (x−T)`
  have hb1 : ‖∫ t in (0:ℝ)..T, R (x - t) * g t‖ ≤ ∫ t in (0:ℝ)..T, Cg * |R (x - t)| := by
    rw [intervalIntegral.integral_of_le hT0, intervalIntegral.integral_of_le hT0]
    have hbcont : Continuous (fun t : ℝ => Cg * |R (x - t)|) := by fun_prop
    refine norm_integral_le_of_norm_le hbcont.integrableOn_Ioc ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hgt : |g t| ≤ Cg := by simpa [Real.norm_eq_abs] using hCg t ⟨ht.1.le, ht.2⟩
    calc ‖R (x - t) * g t‖ = |g t| * |R (x - t)| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]; ring
      _ ≤ Cg * |R (x - t)| := mul_le_mul_of_nonneg_right hgt (abs_nonneg _)
  have hb2 : (∫ t in (0:ℝ)..T, Cg * |R (x - t)|) = Cg * ∫ v in (x - T)..x, |R v| := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := T)
      (f := fun v => |R v|) x
    simpa using this
  have hb3 : (∫ v in (x - T)..x, |R v|) ≤ ∫ v in Set.Ioi (x - T), |R v| := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine MeasureTheory.setIntegral_mono_set (hRabs.mono_set ?_) ?_ ?_
    · exact Set.Ioi_subset_Ioi (by linarith)
    · filter_upwards with v using abs_nonneg _
    · exact Filter.Eventually.of_forall (Set.Ioc_subset_Ioi_self)
  calc ‖∫ t in (0:ℝ)..T, R (x - t) * g t‖
      ≤ ∫ t in (0:ℝ)..T, Cg * |R (x - t)| := hb1
    _ = Cg * ∫ v in (x - T)..x, |R v| := hb2
    _ ≤ Cg * ∫ v in Set.Ioi (x - T), |R v| := mul_le_mul_of_nonneg_left hb3 hCg0

/-- `g` is integrable on `(0,∞)` when continuous and vanishing past `T`. -/
private theorem forcing_integrableOn {g : ℝ → ℝ} (hg : Continuous g) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ t : ℝ, T ≤ t → g t = 0) : IntegrableOn g (Set.Ioi 0) := by
  have h2 : IntegrableOn g (Set.Ioi T) :=
    (integrableOn_zero (μ := MeasureTheory.volume) (s := Set.Ioi T)).congr_fun
      (fun t ht => (hT t (le_of_lt ht)).symm) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT0]
  exact hg.integrableOn_Ioc.union h2

/-- `R ⋆ g ∈ L¹(0,∞)` — Young's inequality, after identifying the Volterra integral with a genuine
convolution of the two zero-extended kernels. -/
private theorem resolvent_conv_integrable {R g : ℝ → ℝ} (hRcont : Continuous R)
    (hg : Continuous g) (hRint : IntegrableOn R (Set.Ioi 0)) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ t : ℝ, T ≤ t → g t = 0) :
    IntegrableOn (fun x => ∫ t in (0:ℝ)..x, R (x - t) * g t) (Set.Ioi 0) := by
  set gp : ℝ → ℝ := Set.indicator (Set.Ioi 0) g with hgp
  set Rp : ℝ → ℝ := Set.indicator (Set.Ici 0) R with hRp
  have hgpInt : Integrable gp := by
    rw [hgp, MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
    exact forcing_integrableOn hg hT0 hT
  have hRpInt : Integrable Rp := by
    rw [hRp, MeasureTheory.integrable_indicator_iff measurableSet_Ici]
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  have hyoung : Integrable (convolution gp Rp (ContinuousLinearMap.mul ℝ ℝ)
      MeasureTheory.volume) := hgpInt.integrable_convolution _ hRpInt
  refine (hyoung.integrableOn (s := Set.Ioi 0)).congr_fun (fun x hx => ?_) measurableSet_Ioi
  -- the Volterra integral IS the convolution, for `x > 0`
  have hx0 : (0:ℝ) < x := hx
  have hcompl : ∀ t : ℝ, t ∉ Set.Ioc (0:ℝ) x → gp t * Rp (x - t) = 0 := by
    intro t ht
    rcases lt_or_ge x t with hlt | hge
    · have : x - t ∉ Set.Ici (0:ℝ) := by simp; linarith
      rw [hRp, Set.indicator_of_notMem this, mul_zero]
    · have ht0 : t ≤ 0 := by
        by_contra hpos
        exact ht ⟨lt_of_not_ge hpos, hge⟩
      have : t ∉ Set.Ioi (0:ℝ) := by simp; linarith
      rw [hgp, Set.indicator_of_notMem this, zero_mul]
  have hconv : convolution gp Rp (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume x
      = ∫ t in Set.Ioc (0:ℝ) x, gp t * Rp (x - t) := by
    rw [convolution_def]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hcompl).symm
  rw [hconv, intervalIntegral.integral_of_le (le_of_lt hx0)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have h1 : gp t = g t := by rw [hgp, Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht.1)]
  have h2 : Rp (x - t) = R (x - t) := by
    rw [hRp, Set.indicator_of_mem (show x - t ∈ Set.Ici (0:ℝ) by simp; linarith [ht.2])]
  rw [h1, h2]; ring

/-- **`MA.13` — RETIRED AXIOM → THEOREM (2026-07-21).**  The renewal solution decays and is
integrable.  Proved from the single citable axiom `wiener_causal_resolvent` (Wiener's `1/f`): the
resolvent turns the equation into the formula `ψ = g + R ⋆ g` (`resolvent_conv_eq`, identified with
`ψ` by Volterra uniqueness `MA.10`), and then a compactly-supported `g` against an `L¹` resolvent
gives decay (moving-window `L¹` tail) and integrability (Young). -/
theorem volterra_renewal_tendsto_zero {q g ψ : ℝ → ℝ} {S : ℝ} (hS : 0 < S)
    (hq : Continuous q) (hg : Continuous g)
    (hqsupp : ∀ t : ℝ, S < t → q t = 0)
    (hgsupp : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → g t = 0)
    (hψcont : ContinuousOn ψ (Set.Ici (0 : ℝ)))
    (hsymbol : ∀ z : ℂ, 0 ≤ z.re →
      1 - (∫ t in (0:ℝ)..S, (q t : ℂ) * Complex.exp (-z * (t : ℂ))) ≠ 0)
    (hψ : ∀ r : ℝ, 0 ≤ r → ψ r = g r + ∫ t in (0:ℝ)..r, q (r - t) * ψ t) :
    Tendsto ψ atTop (𝓝 0) ∧ IntegrableOn ψ (Set.Ioi 0) := by
  obtain ⟨R, hRcont, hRint, hres⟩ := wiener_causal_resolvent hS hq hqsupp hsymbol
  obtain ⟨T0, hT0'⟩ := hgsupp
  obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → g t = 0 :=
    ⟨max T0 0, le_max_right _ _, fun t ht => hT0' t (le_trans (le_max_left _ _) ht)⟩
  have hconvcont : Continuous (fun x : ℝ => ∫ t in (0:ℝ)..x, R (x - t) * g t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_id
    exact (hRcont.comp (continuous_fst.sub continuous_snd)).mul (hg.comp continuous_snd)
  -- `ψ` equals the resolvent formula `g + R ⋆ g` on `[0,∞)`
  have hψeq : ∀ r : ℝ, 0 ≤ r → ψ r = g r + ∫ t in (0:ℝ)..r, R (r - t) * g t := by
    refine volterra_unique_Ici hq hg hψcont (hg.add hconvcont).continuousOn hψ (fun r hr => ?_)
    rw [resolvent_conv_eq hq hRcont hg hres hr]
  constructor
  · have hg0 : Tendsto g atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop T] with t ht using (hT t ht).symm
    have hsum : Tendsto (fun x => g x + ∫ t in (0:ℝ)..x, R (x - t) * g t) atTop (𝓝 0) := by
      simpa using hg0.add (resolvent_conv_tendsto_zero hRcont hg hRint hT0 hT)
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr using (hψeq r hr).symm
  · refine ((forcing_integrableOn hg hT0 hT).add
      (resolvent_conv_integrable hRcont hg hRint hT0 hT)).congr_fun
      (fun r hr => (hψeq r (le_of_lt hr)).symm) measurableSet_Ioi

end FMSA
