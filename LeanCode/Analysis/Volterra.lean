/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Volterra integral equation of the second kind: existence & uniqueness — PROVED, no axiom

Group MA (`MATH_AXIOMS.md`), task `MA.10`. The classical existence-and-uniqueness theorem for the
**Volterra equation of the second kind** (Tricomi, *Integral Equations* §1.2 / Kress, *Linear
Integral Equations* Thm 3.10):

  `u(r) = g(r) + ∫_a^r K(r,t) · u(t) dt`,   `K` continuous on `[a,b]²`, `g` continuous on `[a,b]`

has a **unique** continuous solution on `[a,b]` — for *every* kernel, with no smallness
assumption on `K` and no restriction on the interval length. That unconditionality is what
separates Volterra from Fredholm: the variable upper limit makes the `n`-th iterate of the
integral operator satisfy `‖Vⁿ‖ ≤ (M·(b−a))ⁿ/n!`, whose factorial denominator eventually beats
any constant, so some iterate is a contraction even when `V` itself is not.

## Why this is proved rather than axiomatized

Volterra is absent from Mathlib, but unlike the other Group MA entries it is *not* a genuine
formalization gap: every ingredient is already in tree, and `ODE/PicardLindelof.lean` is a
worked precedent running the identical `(M·L)ⁿ/n!` iterate-contraction argument. Axiomatizing it
would also have been a strictly losing trade — MA.10's consumers exist in order to *retire*
physics axioms (`OZFIX.15` claim A's ψ construction, `OZ.10`'s `oz_fixed_pt_unique` — since retired
to the theorem `oz_fixed_pt_unique_thm`), so paying
a math axiom to retire a physics axiom is no net gain.

## Main results

* `volterraT` — the affine operator `T u = g + V u` as a self-map of `C(Icc a b, ℝ)`.
* `volterra_iterate_bound` — the iterate estimate `|Tⁿu(r) − Tⁿw(r)| ≤ Mⁿ(r−a)ⁿ/n! · dist u w`.
  This is the heart of the argument; the `(r−a)ⁿ` factor (not `(b−a)ⁿ`) is what the induction
  needs, since the integral only accumulates up to `r`.
* `volterra_existsUnique` — existence & uniqueness given an explicit kernel bound `M`.
* `volterra_existsUnique_of_continuous` — the same with `M` supplied by compactness of `[a,b]²`,
  stated pointwise. **This is the form consumers should use.**
* `volterra_convolution_existsUnique` — the renewal/convolution kernel `K(r,t) = q(r−t)`, which
  is the shape the OZ–Baxter factorisation actually produces.

All results are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

## Implementation notes

Solutions live in `C(Icc a b, ℝ)` (a complete metric space with the sup-distance), but the
integrand needs a function on all of `ℝ`, so `Set.IccExtend` mediates: the fixed-point equation
is stated with `Set.IccExtend hab u` under the integral sign. Since the integration range
`[a,r] ⊆ [a,b]` never leaves the interval, the extension is invisible to the mathematics and only
appears as bookkeeping (`Set.projIcc` round-trips in `volterra_iterate_bound`'s `hext`).
-/

open Metric Set Filter Topology MeasureTheory Nat

noncomputable section

variable {a b : ℝ}

/-- The affine Volterra operator `T u = g + V u`, `(V u)(r) = ∫_a^r K r t · u t dt`. -/
def volterraT (hab : a ≤ b) (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hK : Continuous (Function.uncurry K)) (hg : Continuous g)
    (u : C(Icc a b, ℝ)) : C(Icc a b, ℝ) where
  toFun := fun r => g r + ∫ t in a..(r : ℝ), K r t * Set.IccExtend hab u t
  continuous_toFun := by
    have hext : Continuous (Set.IccExtend hab u) := u.continuous.Icc_extend'
    have huc : Continuous (Function.uncurry fun r t => K r t * Set.IccExtend hab u t) := by
      simp only [Function.uncurry_def]
      exact hK.mul (hext.comp continuous_snd)
    have hcore : Continuous fun r : ℝ => g r + ∫ t in a..r, K r t * Set.IccExtend hab u t :=
      hg.add (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous huc
        continuous_id)
    exact hcore.comp continuous_subtype_val

@[simp] lemma volterraT_apply (hab : a ≤ b) (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hK : Continuous (Function.uncurry K)) (hg : Continuous g)
    (u : C(Icc a b, ℝ)) (r : Icc a b) :
    volterraT hab K g hK hg u r = g r + ∫ t in a..(r : ℝ), K r t * Set.IccExtend hab u t := rfl


/-- `∫_a^r (t-a)^n dt = (r-a)^(n+1)/(n+1)`. -/
lemma volterra_integral_sub_pow (a r : ℝ) (n : ℕ) :
    (∫ t in a..r, (t - a) ^ n) = (r - a) ^ (n + 1) / (n + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun t => t ^ n) a, sub_self,
    integral_pow]
  simp

variable {M : ℝ}

/-- **The iterate bound.** `|Tⁿu(r) − Tⁿw(r)| ≤ Mⁿ(r−a)ⁿ/n! · dist u w`. -/
lemma volterra_iterate_bound (hab : a ≤ b) (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hK : Continuous (Function.uncurry K)) (hg : Continuous g)
    (hM : 0 ≤ M) (hKb : ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, |K r t| ≤ M)
    (u w : C(Icc a b, ℝ)) (n : ℕ) (r : Icc a b) :
    |(volterraT hab K g hK hg)^[n] u r - (volterraT hab K g hK hg)^[n] w r|
      ≤ M ^ n * ((r : ℝ) - a) ^ n / n ! * dist u w := by
  set T := volterraT hab K g hK hg with hT
  set D := dist u w with hD
  have hD0 : 0 ≤ D := dist_nonneg
  induction n generalizing r with
  | zero =>
      simpa [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := u) (g := w) r
  | succ n ih =>
      have hra : (r : ℝ) ∈ Icc a b := r.2
      have har : a ≤ (r : ℝ) := hra.1
      -- pointwise IH on the extension, valid on [a,b]
      have hext : ∀ t ∈ Icc a b,
          |Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t|
            ≤ M ^ n * (t - a) ^ n / n ! * D := by
        intro t ht
        have : Set.projIcc a b hab t = ⟨t, ht⟩ := by
          simp [Set.projIcc, ht.1, ht.2]
        simpa [Set.IccExtend, this] using ih ⟨t, ht⟩
      -- the difference is a single integral
      have hdiff : T^[n+1] u r - T^[n+1] w r
          = ∫ t in a..(r:ℝ), K r t *
              (Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hT]
        simp only [volterraT_apply]
        rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub]
        · congr 1; funext t; ring
        · apply Continuous.intervalIntegrable
          exact (hK.uncurry_left (r:ℝ)).mul ((T^[n] u).continuous.Icc_extend' (h := hab))
        · apply Continuous.intervalIntegrable
          exact (hK.uncurry_left (r:ℝ)).mul ((T^[n] w).continuous.Icc_extend' (h := hab))
      rw [hdiff]
      have hfac : ((n ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hbound : |∫ t in a..(r:ℝ), K r t *
            (Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t)|
          ≤ ∫ t in a..(r:ℝ), M ^ (n+1) * (t - a) ^ n / n ! * D := by
        rw [← Real.norm_eq_abs]
        apply intervalIntegral.norm_integral_le_of_norm_le har
        · filter_upwards with t ht
          have htab : t ∈ Icc a b := ⟨le_of_lt ht.1, le_trans ht.2 hra.2⟩
          rw [Real.norm_eq_abs, abs_mul]
          calc |K (r:ℝ) t| * |Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t|
              ≤ M * (M ^ n * (t - a) ^ n / n ! * D) :=
                mul_le_mul (hKb _ hra _ htab) (hext t htab) (abs_nonneg _) hM
            _ = M ^ (n+1) * (t - a) ^ n / n ! * D := by ring
        · apply Continuous.intervalIntegrable; fun_prop
      have heval : (∫ t in a..(r:ℝ), M ^ (n+1) * (t - a) ^ n / n ! * D)
          = (M ^ (n+1) * D / n !) * (((r:ℝ) - a) ^ (n+1) / (n+1)) := by
        have hre : (fun t : ℝ => M ^ (n+1) * (t - a) ^ n / n ! * D)
            = fun t => (M ^ (n+1) * D / n !) * (t - a) ^ n := by funext t; ring
        rw [hre, intervalIntegral.integral_const_mul, volterra_integral_sub_pow]
      rw [heval] at hbound
      refine hbound.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]
      push_cast
      field_simp

/-- Sup-distance form of the iterate bound. -/
lemma volterra_iterate_dist (hab : a ≤ b) (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hK : Continuous (Function.uncurry K)) (hg : Continuous g)
    (hM : 0 ≤ M) (hKb : ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, |K r t| ≤ M)
    (u w : C(Icc a b, ℝ)) (n : ℕ) :
    dist ((volterraT hab K g hK hg)^[n] u) ((volterraT hab K g hK hg)^[n] w)
      ≤ (M * (b - a)) ^ n / n ! * dist u w := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hnn : 0 ≤ (M * (b - a)) ^ n / n ! * dist u w := by positivity
  rw [ContinuousMap.dist_le hnn]
  intro r
  rw [Real.dist_eq]
  refine (volterra_iterate_bound hab K g hK hg hM hKb u w n r).trans ?_
  rw [mul_pow]
  gcongr
  · exact sub_nonneg.mpr r.2.1
  · exact r.2.2

/-- **MA.10 / Volterra equation of the second kind: existence & uniqueness.**
For a continuous kernel `K` bounded by `M` on `[a,b]²` and continuous `g`, the equation
`u(r) = g(r) + ∫_a^r K r t · u t dt` has a unique continuous solution on `[a,b]`. -/
theorem volterra_existsUnique (hab : a ≤ b) (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hK : Continuous (Function.uncurry K)) (hg : Continuous g)
    (hM : 0 ≤ M) (hKb : ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, |K r t| ≤ M) :
    ∃! u : C(Icc a b, ℝ), volterraT hab K g hK hg u = u := by
  set T := volterraT hab K g hK hg with hT
  haveI : Nonempty C(Icc a b, ℝ) := ⟨0⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (M * (b - a)) ^ n / n ! < 1 / 2 := by
    have htend := FloorSemiring.tendsto_pow_div_factorial_atTop (M * (b - a))
    exact (htend.eventually_lt_const (by norm_num)).exists
  have hcontract : ContractingWith (1/2 : NNReal) T^[n] := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
    refine (volterra_iterate_dist hab K g hK hg hM hKb u w n).trans ?_
    have hhalf : ((1/2 : NNReal) : ℝ) = 1/2 := by norm_num
    rw [hhalf]
    exact mul_le_mul_of_nonneg_right hn.le dist_nonneg
  refine ⟨hcontract.fixedPoint _, hcontract.isFixedPt_fixedPoint_iterate, fun w hw => ?_⟩
  exact hcontract.fixedPoint_unique (Function.IsFixedPt.iterate (f := T) hw n)

/-- The kernel bound is automatic: a continuous `K` is bounded on the compact square `[a,b]²`. -/
lemma volterra_exists_kernel_bound (K : ℝ → ℝ → ℝ)
    (hK : Continuous (Function.uncurry K)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, |K r t| ≤ M := by
  have hcpt : IsCompact ((Icc a b) ×ˢ (Icc a b) : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hK.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun r hr t ht => ?_⟩
  exact le_trans (by simpa [Real.norm_eq_abs] using hC (r, t) ⟨hr, ht⟩) (le_max_left _ _)

/-- **MA.10, hypothesis-free form.** Continuous kernel and data suffice: the Volterra equation
`u(r) = g(r) + ∫_a^r K r t · u t dt` has a unique continuous solution on `[a,b]`. -/
theorem volterra_existsUnique_of_continuous (hab : a ≤ b) (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hK : Continuous (Function.uncurry K)) (hg : Continuous g) :
    ∃! u : C(Icc a b, ℝ), ∀ r : Icc a b,
      u r = g r + ∫ t in a..(r : ℝ), K r t * Set.IccExtend hab u t := by
  obtain ⟨M, hM, hKb⟩ := volterra_exists_kernel_bound (a := a) (b := b) K hK
  obtain ⟨u, hu, huniq⟩ := volterra_existsUnique (M := M) hab K g hK hg hM hKb
  exact ⟨u, fun r => (ContinuousMap.ext_iff.mp hu r).symm,
    fun w hw => huniq w (ContinuousMap.ext fun r => (hw r).symm)⟩

/-- **Renewal / convolution kernel** `K r t = q (r − t)`, the form the OZ–Baxter factorisation
produces. Unique continuous solution of `u(r) = g(r) + ∫_a^r q(r−t) · u(t) dt`. -/
theorem volterra_convolution_existsUnique (hab : a ≤ b) (q : ℝ → ℝ) (g : ℝ → ℝ)
    (hq : Continuous q) (hg : Continuous g) :
    ∃! u : C(Icc a b, ℝ), ∀ r : Icc a b,
      u r = g r + ∫ t in a..(r : ℝ), q ((r : ℝ) - t) * Set.IccExtend hab u t := by
  have hK : Continuous (Function.uncurry fun r t => q (r - t)) := by
    simp only [Function.uncurry_def]
    exact hq.comp (continuous_fst.sub continuous_snd)
  exact volterra_existsUnique_of_continuous hab _ g hK hg

end

