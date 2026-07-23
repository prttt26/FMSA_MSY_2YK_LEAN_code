/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Jordan's lemma (quantitative arc-vanishing bound), general-purpose

**Why this file exists.** `OZFIX.6`'s **Route B** (whole-series Fourier inversion, the alternative
to the termwise Route A being pursued via `OZFIX.9`) needs to close a *growing* semicircular
contour — the classical Jordan's-lemma argument that the arc contribution vanishes as the radius
`R → ∞`, so that `circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles`
(`LeanCode/Analysis/ContourDeformation.lean`) can be bootstrapped from a *finite* residue sum to
the *infinite* Mittag-Leffler expansion a real-line Fourier-inversion argument needs. Group
Y2/MZERO's own Route B (`proof_notes_mixture_rdf.md`, `MZERO.9`–`MZERO.11`) independently hits the
identical gap, so this is deliberately kept general-purpose.

**Unlike `ContourDeformation.lean`, this needs no new axiom.** A dedicated research pass
(2026-07-15) checked whether the classical quantitative bound `‖arc integral‖ ≤ πM/a` requires
axiomatizing (mirroring `ContourDeformation.lean`'s topological gap) or is provable outright from
this project's pinned Mathlib (`v4.31.0`, commit `fabf563a`). Result: **fully provable**. Every
step of the classical 5-step proof (ML inequality, `‖exp(iaz)‖` via `Complex.norm_exp`, a
symmetric interval split at `π/2`, Jordan's inequality itself, and an elementary antiderivative)
is either a named Mathlib lemma — most notably `Real.mul_le_sin`, docstringed *"One half of
Jordan's inequality"* — or a direct copy of the `HasDerivAt`+FTC pattern this project already uses
(`zeta0_formula`, `LeanCode/HardSphere/BaxterZeros.lean`). `#print axioms` on the main theorem
below confirms it depends on exactly the standard three (`propext`, `Classical.choice`,
`Quot.sound`), nothing new.

**Status:** ✓ DONE, `sorry`-free, no new axiom.
-/

open MeasureTheory Real Set intervalIntegral

noncomputable section

/-- `∫₀^{π/2} exp(-c·θ) dθ = (1-exp(-c·π/2))/c` for `c ≠ 0` — the elementary antiderivative
Jordan's lemma's proof needs, via the same `HasDerivAt`+FTC idiom as `zeta0_formula`
(`BaxterZeros.lean`). -/
private theorem exp_neg_mul_integral (c : ℝ) (hc : c ≠ 0) :
    ∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(c * θ)) =
      (1 - Real.exp (-(c * (Real.pi / 2)))) / c := by
  have heqfun : (fun θ : ℝ => -(c * θ)) = fun θ : ℝ => (-c) * θ := by funext θ; ring
  have hderiv : ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => -Real.exp (-(c * θ)) / c) (Real.exp (-(c * θ))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => -(c * θ)) (-c) θ := by
      rw [heqfun]; simpa using (hasDerivAt_id θ).const_mul (-c)
    exact (((h1.exp).neg).div_const c).congr_deriv (by field_simp)
  have hint : IntervalIntegrable (fun θ => Real.exp (-(c * θ))) volume 0 (Real.pi / 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ) hint]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  field_simp; ring

/-- `∫₀^π f(sinθ) dθ = 2·∫₀^{π/2} f(sinθ) dθ`, via the reflection identity `sin(π-θ)=sinθ`
(`Real.sin_pi_sub`) reindexing the `[π/2,π]` half onto `[0,π/2]`. -/
private theorem sin_arg_symmetric_split (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ θ in (0:ℝ)..Real.pi, f (Real.sin θ) = 2 * ∫ θ in (0:ℝ)..(Real.pi / 2), f (Real.sin θ) := by
  have hcont : Continuous (fun θ : ℝ => f (Real.sin θ)) := hf.comp Real.continuous_sin
  have hsplit : (∫ θ in (0:ℝ)..(Real.pi / 2), f (Real.sin θ)) +
      ∫ θ in (Real.pi / 2)..Real.pi, f (Real.sin θ) = ∫ θ in (0:ℝ)..Real.pi, f (Real.sin θ) :=
    integral_add_adjacent_intervals (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hreindex : (∫ θ in (0:ℝ)..(Real.pi / 2), f (Real.sin (Real.pi - θ))) =
      ∫ x in (Real.pi - Real.pi / 2)..(Real.pi - 0), f (Real.sin x) :=
    integral_comp_sub_left (fun θ => f (Real.sin θ)) Real.pi
  simp only [sub_zero, sub_half] at hreindex
  have hreindex2 : (∫ θ in (0:ℝ)..(Real.pi / 2), f (Real.sin θ)) =
      ∫ θ in (Real.pi / 2)..Real.pi, f (Real.sin θ) := by
    rw [← hreindex]; congr 1; funext θ; rw [Real.sin_pi_sub]
  rw [← hsplit, hreindex2]; ring

/-- Jordan's inequality (`Real.mul_le_sin`) applied pointwise, then integrated:
`∫₀^{π/2} exp(-c·sinθ)dθ ≤ ∫₀^{π/2} exp(-c·(2/π)θ)dθ` for `c > 0`. -/
private theorem jordan_ineq_integral_mono (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(c * Real.sin θ)) ≤
      ∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(c * ((2 / Real.pi) * θ))) := by
  have hle : (0:ℝ) ≤ Real.pi / 2 := by positivity
  apply integral_mono_on hle
  · exact
      (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sin).neg).intervalIntegrable
        _ _
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.mul continuous_id)).neg).intervalIntegrable _ _
  · intro θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hjordan : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0 hθ1
    apply Real.exp_le_exp.mpr
    have : c * (2 / Real.pi * θ) ≤ c * Real.sin θ := mul_le_mul_of_nonneg_left hjordan hc.le
    linarith

/-- **Jordan's lemma (quantitative arc-vanishing bound).** For `g : ℂ → ℂ` continuous and bounded
by `M` on the upper-half circle of radius `R`, and `a > 0`, the semicircular arc integral of
`g(z)·exp(iaz)` (with the `dz = iRe^{iθ}dθ` Jacobian folded into the integrand) is bounded by
`πM/a` — the classical estimate used to close a growing Fourier-inversion contour in the upper
half-plane. See the file docstring for why this needs no new axiom. -/
theorem jordan_lemma_arc_bound {g : ℂ → ℂ} {R a M : ℝ} (hR : 0 < R) (ha : 0 < a) (hM0 : 0 ≤ M)
    (hg : ContinuousOn g {z : ℂ | ‖z‖ = R ∧ 0 ≤ z.im})
    (hMbound : ∀ z : ℂ, ‖z‖ = R → 0 ≤ z.im → ‖g z‖ ≤ M) :
    ‖∫ θ in (0:ℝ)..Real.pi,
        g ((R:ℂ) * Complex.exp (θ * Complex.I)) *
          Complex.exp (Complex.I * (a:ℂ) * (R:ℂ) * Complex.exp (θ * Complex.I)) *
          (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I))‖ ≤ Real.pi * M / a := by
  set bd : ℝ → ℝ := fun θ => M * R * Real.exp (-(a * R * Real.sin θ)) with hbddef
  have hpointwise : ∀ θ ∈ Set.Ioc (0:ℝ) Real.pi,
      ‖g ((R:ℂ) * Complex.exp (θ * Complex.I)) *
          Complex.exp (Complex.I * (a:ℂ) * (R:ℂ) * Complex.exp (θ * Complex.I)) *
          (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I))‖ ≤ bd θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (0:ℝ) Real.pi := ⟨hθ.1.le, hθ.2⟩
    have hznorm : ‖(R:ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR]
    have hzim : ((R:ℂ) * Complex.exp (θ * Complex.I)).im = R * Real.sin θ := by
      rw [Complex.mul_im]; simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have hsinnn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ'
    have hzimnn : 0 ≤ ((R:ℂ) * Complex.exp (θ * Complex.I)).im := by
      rw [hzim]; positivity
    have hgbound := hMbound _ hznorm hzimnn
    have hre : (Complex.I * (a:ℂ) * (R:ℂ) * Complex.exp (θ * Complex.I)).re =
        -(a * R * Real.sin θ) := by
      have h1 : Complex.I * (a:ℂ) * (R:ℂ) * Complex.exp (θ * Complex.I) =
          ((a * R : ℝ):ℂ) * (Complex.I * Complex.exp (θ * Complex.I)) := by push_cast; ring
      rw [h1, Complex.mul_re]
      simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have hnormexp : ‖Complex.exp (Complex.I * (a:ℂ) * (R:ℂ) * Complex.exp (θ * Complex.I))‖ =
        Real.exp (-(a * R * Real.sin θ)) := by rw [Complex.norm_exp, hre]
    have hnormIRe : ‖Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, one_mul, mul_one]
    rw [norm_mul, norm_mul, hnormexp, hnormIRe, hbddef]
    calc ‖g ((R:ℂ) * Complex.exp (θ * Complex.I))‖ * Real.exp (-(a * R * Real.sin θ)) * R
        ≤ M * Real.exp (-(a * R * Real.sin θ)) * R := by gcongr
      _ = M * R * Real.exp (-(a * R * Real.sin θ)) := by ring
  have hbdint : IntervalIntegrable bd volume 0 Real.pi := by
    rw [hbddef]
    exact (Continuous.mul continuous_const
      (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sin).neg)).intervalIntegrable
      _ _
  have hMLbound := intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
    (ae_of_all _ hpointwise) hbdint
  refine hMLbound.trans ?_
  have hpullconst : (∫ θ in (0:ℝ)..Real.pi, bd θ) =
      (M * R) * ∫ θ in (0:ℝ)..Real.pi, Real.exp (-(a * R * Real.sin θ)) := by
    rw [hbddef]; exact intervalIntegral.integral_const_mul (M * R) _
  rw [hpullconst]
  have hsplit := sin_arg_symmetric_split (fun x => Real.exp (-(a * R * x))) (by fun_prop)
  rw [hsplit]
  have hjordan := jordan_ineq_integral_mono (a * R) (mul_pos ha hR)
  have hantideriv := exp_neg_mul_integral (a * R * (2 / Real.pi)) (by positivity)
  have hcalc :
      ∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(a * R * ((2 / Real.pi) * θ))) ≤
        Real.pi / (2 * (a * R)) := by
    rw [show (∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(a * R * ((2 / Real.pi) * θ)))) =
        ∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(a * R * (2 / Real.pi) * θ)) from by
      congr 1; funext θ; ring_nf]
    rw [hantideriv]
    have hexppos : 0 ≤ Real.exp (-(a * R * (2 / Real.pi) * (Real.pi / 2))) := (Real.exp_pos _).le
    have hcpos : 0 < a * R * (2 / Real.pi) := by positivity
    have hstep : (1 - Real.exp (-(a * R * (2 / Real.pi) * (Real.pi / 2)))) / (a * R * (2 / Real.pi))
        ≤ 1 / (a * R * (2 / Real.pi)) := by
      gcongr
      linarith
    refine hstep.trans_eq ?_
    field_simp
  have hfinal := hjordan.trans hcalc
  calc (M * R) * (2 * ∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(a * R * Real.sin θ)))
      ≤ (M * R) * (2 * (Real.pi / (2 * (a * R)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hfinal]
    _ = Real.pi * M / a := by field_simp

end
