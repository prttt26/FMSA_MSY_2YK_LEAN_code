/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Van der Corput first-derivative test — PROVED (axiom retired), general-purpose

Group MA (`MATH_AXIOMS.md`), task `MA.4`. The classical **van der Corput lemma**
(first-derivative / non-stationary-phase test with amplitude; Stein, *Harmonic Analysis*,
Prop. VIII.1.2 + corollary): for a `C²` phase `φ` with monotonic derivative bounded away from
zero (`|φ'| ≥ λ > 0`) and a `C¹` amplitude `ψ`,

`‖∫_a^b e^{iφ(θ)}·ψ(θ) dθ‖ ≤ (3/λ)·(‖ψ(b)‖ + ∫_a^b ‖ψ'‖)`.

**History (retire-by-proving, 2026-07-16).** First landed (2026-07-15) as an axiom whose phase
was merely `C¹` with monotone derivative — the textbook generality. That form is classically
proved via Riemann–Stieltjes integration by parts against the monotone `1/φ'` (or the second mean
value theorem for integrals); a reconnaissance pass confirmed **Mathlib has neither**, so the
effort. The axiom as stated was not provable. Since it had **no consumers** (pure
toolbox; every phase in this project is analytic), it was replaced by this `C²` version — the
hypotheses add second-derivative data (`hphi'`, `hphi''c`) and strengthen the amplitude
integrability to continuity (`hpsi'c`) — which is **fully proved** from Mathlib:
`#print axioms` = the standard three. The lost generality (merely-monotone `φ'`) can be
re-axiomatized on demand if a genuinely non-`C²` consumer ever appears.

**Proof structure.** (1) `vdc_single_signed`: `φ'` is single-signed on `[a,b]` (IVT + `|φ'| ≥ λ`).
(2) `vdc_deriv_nonneg_of_monotoneOn`: monotone `φ'` forces `φ'' ≥ 0` pointwise including
endpoints (one-sided slope limits via `hasDerivWithinAt_iff_tendsto_slope`; the antitone case by
negation). (3) `vdc_free_bound`: the amplitude-free bound `‖∫_a^x e^{iφ}‖ ≤ 3/λ` — integrate by
parts against `u = 1/(iφ')` (`HasDerivAt.fun_div` for the ℝ→ℂ quotient), evaluate
`∫|φ''|/φ'² = |1/φ'(a) − 1/φ'(x)| ≤ 1/λ` by FTC on `−1/φ'` plus the sign facts; the three pieces
(two boundary terms + variation term) give `3/λ`. (4) Main theorem: second integration by parts
against the running primitive `G(y) = ∫_a^y e^{iφ}` — continuity via
`continuousOn_primitive_interval`, interior differentiability via FTC-1
(`integral_hasDerivAt_right` + `stronglyMeasurableAtFilter` on the open interval, sidestepping
endpoint issues with the interior-hypothesis IBP variant
`integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`) — then
`‖∫e^{iφ}ψ‖ ≤ ‖G(b)‖·‖ψ(b)‖ + ∫‖G‖·‖ψ'‖ ≤ (3/λ)(‖ψ(b)‖ + ∫‖ψ'‖)`.

Numerically verified (scratch `ma45_check.py`, 2026-07-15): both monotone branches, two
amplitudes, `λ ∈ {1..500}` — bound holds with wide margin, LHS decaying `~1/λ`.

Historical note (`proof_notes_ozfix.md` `OZFIX.10`): plain van der Corput was shown
*insufficient* for the once-blocked monolithic `k·Ĥ(k)·e^{ikr}` arc estimate (amplitude `O(R)` ×
VdC gain `1/(rR)` = `O(1)`); that consumer was resolved by the `MA.2`+`MA.3` Mittag-Leffler
decomposition instead. This theorem is general toolbox material.
-/

open Set MeasureTheory intervalIntegral

noncomputable section

private lemma vdc_free_bound {phi phi' phi'' : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam)
    (hphi : ∀ θ ∈ Set.Icc a b, HasDerivAt phi (phi' θ) θ)
    (hphi' : ∀ θ ∈ Set.Icc a b, HasDerivAt phi' (phi'' θ) θ)
    (hphi''c : ContinuousOn phi'' (Set.Icc a b))
    (hsign : (∀ θ ∈ Set.Icc a b, 0 ≤ phi'' θ) ∨ (∀ θ ∈ Set.Icc a b, phi'' θ ≤ 0))
    (hpos : (∀ θ ∈ Set.Icc a b, 0 < phi' θ) ∨ (∀ θ ∈ Set.Icc a b, phi' θ < 0))
    {x : ℝ} (hx : x ∈ Set.Icc a b)
    (hlb : ∀ θ ∈ Set.Icc a b, lam ≤ |phi' θ|) :
    ‖∫ θ in a..x, Complex.exp (Complex.I * (phi θ : ℂ))‖ ≤ 3 / lam := by
  obtain ⟨hax, hxb⟩ := hx
  have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hxb
  have huIcc : Set.uIcc a x = Set.Icc a x := Set.uIcc_of_le hax
  -- nonvanishing
  have hne : ∀ θ ∈ Set.Icc a b, phi' θ ≠ 0 := by
    intro θ hθ
    rcases hpos with h | h
    · exact (h θ hθ).ne'
    · exact (h θ hθ).ne
  have hIne : ∀ θ ∈ Set.Icc a b, Complex.I * (phi' θ : ℂ) ≠ 0 := by
    intro θ hθ
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hne θ hθ)
  -- continuity building blocks
  have hphi'c : ContinuousOn phi' (Set.Icc a b) :=
    fun θ hθ => (hphi' θ hθ).continuousAt.continuousWithinAt
  have hphic : ContinuousOn phi (Set.Icc a b) :=
    fun θ hθ => (hphi θ hθ).continuousAt.continuousWithinAt
  have hc1 : ContinuousOn (fun θ => Complex.I * (phi' θ : ℂ)) (Set.Icc a x) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hphi'c.mono hsub))
  have hc2 : ContinuousOn (fun θ => Complex.I * (phi'' θ : ℂ)) (Set.Icc a x) :=
    continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (hphi''c.mono hsub))
  have hc0 : ContinuousOn (fun θ => Complex.exp (Complex.I * (phi θ : ℂ))) (Set.Icc a x) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hphic.mono hsub)))
  -- ‖exp(I·φθ)‖ = 1
  have hnormv : ∀ θ : ℝ, ‖Complex.exp (Complex.I * (phi θ : ℂ))‖ = 1 := by
    intro θ
    rw [Complex.norm_exp]
    have h0 : (Complex.I * (phi θ : ℂ)).re = 0 := by simp [Complex.mul_re]
    rw [h0, Real.exp_zero]
  -- IBP: u = 1/(Iφ'), v = exp(Iφ)
  have hu : ∀ θ ∈ Set.uIcc a x, HasDerivAt (fun t => 1 / (Complex.I * (phi' t : ℂ)))
      (-(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2) θ := by
    intro θ hθ
    rw [huIcc] at hθ
    have h1 : HasDerivAt (fun t => Complex.I * (phi' t : ℂ)) (Complex.I * (phi'' θ : ℂ)) θ :=
      ((hphi' θ (hsub hθ)).ofReal_comp).const_mul Complex.I
    have h2 := (hasDerivAt_const θ (1:ℂ)).fun_div h1 (hIne θ (hsub hθ))
    exact h2.congr_deriv (by ring)
  have hv : ∀ θ ∈ Set.uIcc a x, HasDerivAt (fun t => Complex.exp (Complex.I * (phi t : ℂ)))
      (Complex.exp (Complex.I * (phi θ : ℂ)) * (Complex.I * (phi' θ : ℂ))) θ := by
    intro θ hθ
    rw [huIcc] at hθ
    exact (((hphi θ (hsub hθ)).ofReal_comp).const_mul Complex.I).cexp
  have hu'int : IntervalIntegrable
      (fun θ => -(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2) volume a x := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hc2.neg.div (hc1.pow 2) (fun θ hθ => pow_ne_zero 2 (hIne θ (hsub hθ)))
  have hv'int : IntervalIntegrable
      (fun θ => Complex.exp (Complex.I * (phi θ : ℂ)) * (Complex.I * (phi' θ : ℂ)))
      volume a x := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hc0.mul hc1
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int
  have hcongr : (∫ θ in a..x, (1 / (Complex.I * (phi' θ : ℂ))) *
      (Complex.exp (Complex.I * (phi θ : ℂ)) * (Complex.I * (phi' θ : ℂ)))) =
      ∫ θ in a..x, Complex.exp (Complex.I * (phi θ : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [huIcc] at hθ
    have hne' := hIne θ (hsub hθ)
    have hne'' : (phi' θ : ℂ) ≠ 0 := by exact_mod_cast hne θ (hsub hθ)
    field_simp
  rw [hcongr] at hibp
  -- norm of 1/(Iφ')
  have hinvnorm : ∀ θ ∈ Set.Icc a b, ‖1 / (Complex.I * (phi' θ : ℂ))‖ ≤ lam⁻¹ := by
    intro θ hθ
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, one_div]
    gcongr
    exact hlb θ hθ
  -- FTC for ∫ φ''/φ'²
  have hw : ∀ θ ∈ Set.uIcc a x, HasDerivAt (fun t => -(phi' t)⁻¹)
      (phi'' θ / (phi' θ) ^ 2) θ := by
    intro θ hθ
    rw [huIcc] at hθ
    have h1 := ((hphi' θ (hsub hθ)).inv (hne θ (hsub hθ))).neg
    exact h1.congr_deriv (by ring)
  have hwint : IntervalIntegrable (fun θ => phi'' θ / (phi' θ) ^ 2) volume a x := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (hphi''c.mono hsub).div ((hphi'c.mono hsub).pow 2)
      (fun θ hθ => pow_ne_zero 2 (hne θ (hsub hθ)))
  have hFTC : (∫ θ in a..x, phi'' θ / (phi' θ) ^ 2) = (phi' a)⁻¹ - (phi' x)⁻¹ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ hθ => hw θ hθ) hwint]
    ring
  -- inverse difference bound, both φ' sign cases
  have hmema : a ∈ Set.Icc a b := ⟨le_refl a, le_trans hax hxb⟩
  have hmemx : x ∈ Set.Icc a b := ⟨hax, hxb⟩
  have hinv_bound : (phi' a)⁻¹ - (phi' x)⁻¹ ≤ lam⁻¹ ∧ (phi' x)⁻¹ - (phi' a)⁻¹ ≤ lam⁻¹ := by
    rcases hpos with h | h
    · have hpa : lam ≤ phi' a := by
        have h0 := hlb a hmema; rwa [abs_of_pos (h a hmema)] at h0
      have hpx : lam ≤ phi' x := by
        have h0 := hlb x hmemx; rwa [abs_of_pos (h x hmemx)] at h0
      have h1 : (phi' a)⁻¹ ≤ lam⁻¹ := by gcongr
      have h2 : (phi' x)⁻¹ ≤ lam⁻¹ := by gcongr
      have h3 : 0 < (phi' a)⁻¹ := inv_pos.mpr (h a hmema)
      have h4 : 0 < (phi' x)⁻¹ := inv_pos.mpr (h x hmemx)
      constructor <;> linarith
    · have hpa : lam ≤ -phi' a := by
        have h0 := hlb a hmema; rwa [abs_of_neg (h a hmema)] at h0
      have hpx : lam ≤ -phi' x := by
        have h0 := hlb x hmemx; rwa [abs_of_neg (h x hmemx)] at h0
      have h1 : (-phi' a)⁻¹ ≤ lam⁻¹ := by gcongr
      have h2 : (-phi' x)⁻¹ ≤ lam⁻¹ := by gcongr
      rw [inv_neg] at h1 h2
      have h3 : (phi' a)⁻¹ < 0 := inv_lt_zero.mpr (h a hmema)
      have h4 : (phi' x)⁻¹ < 0 := inv_lt_zero.mpr (h x hmemx)
      constructor <;> linarith
  -- ∫ ‖u'‖ ≤ lam⁻¹
  have hu'norm_int : (∫ θ in a..x, ‖-(Complex.I * (phi'' θ : ℂ)) /
      (Complex.I * (phi' θ : ℂ)) ^ 2‖) ≤ lam⁻¹ := by
    have hpoint : Set.EqOn (fun θ => ‖-(Complex.I * (phi'' θ : ℂ)) /
        (Complex.I * (phi' θ : ℂ)) ^ 2‖) (fun θ => |phi'' θ| / (phi' θ) ^ 2)
        (Set.uIcc a x) := by
      intro θ _
      show ‖-(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2‖ =
        |phi'' θ| / (phi' θ) ^ 2
      rw [norm_div, norm_neg, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs]
    rw [intervalIntegral.integral_congr hpoint]
    rcases hsign with h | h
    · have heq : Set.EqOn (fun θ => |phi'' θ| / (phi' θ) ^ 2)
          (fun θ => phi'' θ / (phi' θ) ^ 2) (Set.uIcc a x) := by
        intro θ hθ
        rw [huIcc] at hθ
        show |phi'' θ| / (phi' θ) ^ 2 = phi'' θ / (phi' θ) ^ 2
        rw [abs_of_nonneg (h θ (hsub hθ))]
      rw [intervalIntegral.integral_congr heq, hFTC]
      exact hinv_bound.1
    · have heq : Set.EqOn (fun θ => |phi'' θ| / (phi' θ) ^ 2)
          (fun θ => -(phi'' θ / (phi' θ) ^ 2)) (Set.uIcc a x) := by
        intro θ hθ
        rw [huIcc] at hθ
        show |phi'' θ| / (phi' θ) ^ 2 = -(phi'' θ / (phi' θ) ^ 2)
        rw [abs_of_nonpos (h θ (hsub hθ))]
        ring
      rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_neg, hFTC]
      have h5 := hinv_bound.2
      linarith
  -- assemble
  have hlast : ‖∫ θ in a..x, -(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2 *
      Complex.exp (Complex.I * (phi θ : ℂ))‖ ≤ lam⁻¹ := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hax
      (f := fun θ => -(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2 *
        Complex.exp (Complex.I * (phi θ : ℂ)))
      (g := fun θ => ‖-(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2‖)
      (Filter.Eventually.of_forall (fun θ hθ =>
        le_of_eq (by rw [norm_mul, hnormv θ, mul_one])))
      hu'int.norm
    exact le_trans hb hu'norm_int
  rw [hibp]
  have e1 : ‖1 / (Complex.I * (phi' x : ℂ)) * Complex.exp (Complex.I * (phi x : ℂ))‖ ≤ lam⁻¹ := by
    rw [norm_mul, hnormv x, mul_one]
    exact hinvnorm x hmemx
  have e2 : ‖1 / (Complex.I * (phi' a : ℂ)) * Complex.exp (Complex.I * (phi a : ℂ))‖ ≤ lam⁻¹ := by
    rw [norm_mul, hnormv a, mul_one]
    exact hinvnorm a hmema
  calc ‖1 / (Complex.I * (phi' x : ℂ)) * Complex.exp (Complex.I * (phi x : ℂ)) -
        1 / (Complex.I * (phi' a : ℂ)) * Complex.exp (Complex.I * (phi a : ℂ)) -
        ∫ θ in a..x, -(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2 *
          Complex.exp (Complex.I * (phi θ : ℂ))‖
      ≤ ‖1 / (Complex.I * (phi' x : ℂ)) * Complex.exp (Complex.I * (phi x : ℂ)) -
        1 / (Complex.I * (phi' a : ℂ)) * Complex.exp (Complex.I * (phi a : ℂ))‖ +
        ‖∫ θ in a..x, -(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2 *
          Complex.exp (Complex.I * (phi θ : ℂ))‖ := norm_sub_le _ _
    _ ≤ (‖1 / (Complex.I * (phi' x : ℂ)) * Complex.exp (Complex.I * (phi x : ℂ))‖ +
        ‖1 / (Complex.I * (phi' a : ℂ)) * Complex.exp (Complex.I * (phi a : ℂ))‖) +
        ‖∫ θ in a..x, -(Complex.I * (phi'' θ : ℂ)) / (Complex.I * (phi' θ : ℂ)) ^ 2 *
          Complex.exp (Complex.I * (phi θ : ℂ))‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (lam⁻¹ + lam⁻¹) + lam⁻¹ := add_le_add (add_le_add e1 e2) hlast
    _ = 3 / lam := by ring


-- φ' is single-signed (IVT)
private lemma vdc_single_signed {phi' : ℝ → ℝ} {a b lam : ℝ} (hlam : 0 < lam)
    (hc : ContinuousOn phi' (Set.Icc a b))
    (hlb : ∀ θ ∈ Set.Icc a b, lam ≤ |phi' θ|) (hab : a ≤ b) :
    (∀ θ ∈ Set.Icc a b, 0 < phi' θ) ∨ (∀ θ ∈ Set.Icc a b, phi' θ < 0) := by
  have hmema : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hne : ∀ θ ∈ Set.Icc a b, phi' θ ≠ 0 := by
    intro θ hθ h0
    have := hlb θ hθ
    rw [h0, abs_zero] at this
    linarith
  rcases lt_or_gt_of_ne (hne a hmema) with hA | hA
  · right
    intro c hc'
    by_contra hcon
    push_neg at hcon
    have hzero : (0:ℝ) ∈ Set.uIcc (phi' a) (phi' c) :=
      Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hA, hcon⟩)
    have hsub2 : Set.uIcc a c ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hc'.1]
      exact Set.Icc_subset_Icc le_rfl hc'.2
    obtain ⟨d, hd, hd0⟩ := intermediate_value_uIcc (hc.mono hsub2) hzero
    exact hne d (hsub2 hd) hd0
  · left
    intro c hc'
    by_contra hcon
    push_neg at hcon
    have hzero : (0:ℝ) ∈ Set.uIcc (phi' a) (phi' c) :=
      Set.mem_uIcc.mpr (Or.inr ⟨hcon, le_of_lt hA⟩)
    have hsub2 : Set.uIcc a c ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hc'.1]
      exact Set.Icc_subset_Icc le_rfl hc'.2
    obtain ⟨d, hd, hd0⟩ := intermediate_value_uIcc (hc.mono hsub2) hzero
    exact hne d (hsub2 hd) hd0

-- monotone φ' ⇒ φ'' ≥ 0 on the closed interval
private lemma vdc_deriv_nonneg_of_monotoneOn {phi' phi'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hphi' : ∀ θ ∈ Set.Icc a b, HasDerivAt phi' (phi'' θ) θ)
    (hm : MonotoneOn phi' (Set.Icc a b)) :
    ∀ θ ∈ Set.Icc a b, 0 ≤ phi'' θ := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.2 with hθb | hθb
  · -- right-sided slopes
    have h := ((hphi' θ hθ).hasDerivWithinAt (s := Set.Ioi θ))
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    have hsimp : Set.Ioi θ \ {θ} = Set.Ioi θ := by
      ext t; simp +contextual [ne_of_gt]
    rw [hsimp] at h
    refine ge_of_tendsto h ?_
    filter_upwards [Ioc_mem_nhdsGT hθb] with t ht
    have ht' : t ∈ Set.Icc a b := ⟨le_trans hθ.1 (le_of_lt ht.1), ht.2⟩
    have hmon := hm hθ ht' (le_of_lt ht.1)
    rw [slope_def_field]
    exact div_nonneg (by linarith) (by linarith [ht.1])
  · -- θ = b: left-sided slopes
    subst hθb
    have h := ((hphi' θ hθ).hasDerivWithinAt (s := Set.Iio θ))
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    have hsimp : Set.Iio θ \ {θ} = Set.Iio θ := by
      ext t; simp +contextual [ne_of_lt]
    rw [hsimp] at h
    refine ge_of_tendsto h ?_
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    have ht' : t ∈ Set.Icc a θ := ⟨ht.1, le_of_lt ht.2⟩
    have hmon := hm ht' hθ (le_of_lt ht.2)
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (by linarith) (by linarith [ht.2])

-- the main theorem: van der Corput with amplitude, C² phase
theorem vanDerCorput_first_derivative_test {phi phi' phi'' : ℝ → ℝ} {psi psi' : ℝ → ℂ}
    {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam)
    (hphi : ∀ θ ∈ Set.Icc a b, HasDerivAt phi (phi' θ) θ)
    (hphi' : ∀ θ ∈ Set.Icc a b, HasDerivAt phi' (phi'' θ) θ)
    (hphi''c : ContinuousOn phi'' (Set.Icc a b))
    (hmono : MonotoneOn phi' (Set.Icc a b) ∨ AntitoneOn phi' (Set.Icc a b))
    (hlb : ∀ θ ∈ Set.Icc a b, lam ≤ |phi' θ|)
    (hpsi : ∀ θ ∈ Set.Icc a b, HasDerivAt psi (psi' θ) θ)
    (hpsi'c : ContinuousOn psi' (Set.Icc a b)) :
    ‖∫ θ in a..b, Complex.exp (Complex.I * (phi θ : ℂ)) * psi θ‖ ≤
      3 / lam * (‖psi b‖ + ∫ θ in a..b, ‖psi' θ‖) := by
  rcases eq_or_lt_of_le hab with heq | hab'
  · subst heq
    simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  -- derived sign facts
  have hphi'c : ContinuousOn phi' (Set.Icc a b) :=
    fun θ hθ => (hphi' θ hθ).continuousAt.continuousWithinAt
  have hpos := vdc_single_signed hlam hphi'c hlb hab
  have hsign : (∀ θ ∈ Set.Icc a b, 0 ≤ phi'' θ) ∨ (∀ θ ∈ Set.Icc a b, phi'' θ ≤ 0) := by
    rcases hmono with hm | hm
    · exact Or.inl (vdc_deriv_nonneg_of_monotoneOn hab' hphi' hm)
    · refine Or.inr ?_
      have hneg := vdc_deriv_nonneg_of_monotoneOn hab' (phi' := fun θ => -phi' θ)
        (phi'' := fun θ => -phi'' θ) (fun θ hθ => (hphi' θ hθ).neg) (fun s hs t ht hst => by
          simp only [neg_le_neg_iff]
          exact hm hs ht hst)
      intro θ hθ
      have := hneg θ hθ
      linarith
  -- the running primitive
  set G : ℝ → ℂ := fun y => ∫ θ in a..y, Complex.exp (Complex.I * (phi θ : ℂ)) with hGdef
  have hphic : ContinuousOn phi (Set.Icc a b) :=
    fun θ hθ => (hphi θ hθ).continuousAt.continuousWithinAt
  have hexpc : ContinuousOn (fun θ => Complex.exp (Complex.I * (phi θ : ℂ))) (Set.uIcc a b) := by
    rw [huIcc]
    exact Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hphic))
  have hGc : ContinuousOn G (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval hexpc.integrableOn_uIcc
  have hGbound : ∀ y ∈ Set.Icc a b, ‖G y‖ ≤ 3 / lam := by
    intro y hy
    exact vdc_free_bound hab hlam hphi hphi' hphi''c hsign hpos hy hlb
  have hGd : ∀ y ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt G (Complex.exp (Complex.I * (phi y : ℂ))) y := by
    rw [min_eq_left hab, max_eq_right hab]
    intro y hy
    have hyIcc : y ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hy
    apply intervalIntegral.integral_hasDerivAt_right
    · apply ContinuousOn.intervalIntegrable
      exact hexpc.mono (by
        rw [huIcc, Set.uIcc_of_le hyIcc.1]
        exact Set.Icc_subset_Icc le_rfl hyIcc.2)
    · exact (hexpc.mono (by rw [huIcc]; exact Set.Ioo_subset_Icc_self)).stronglyMeasurableAtFilter
        isOpen_Ioo y hy
    · have h1 : ContinuousAt (fun t : ℝ => Complex.I * (phi t : ℂ)) y :=
        continuousAt_const.mul
          (Complex.continuous_ofReal.continuousAt.comp (hphi y hyIcc).continuousAt)
      exact h1.cexp
  -- interior data for ψ and integrabilities
  have hpsic : ContinuousOn psi (Set.Icc a b) :=
    fun θ hθ => (hpsi θ hθ).continuousAt.continuousWithinAt
  have hpsid : ∀ y ∈ Set.Ioo (min a b) (max a b), HasDerivAt psi (psi' y) y := by
    rw [min_eq_left hab, max_eq_right hab]
    intro y hy
    exact hpsi y (Set.Ioo_subset_Icc_self hy)
  have hexpint : IntervalIntegrable (fun θ => Complex.exp (Complex.I * (phi θ : ℂ)))
      volume a b := hexpc.intervalIntegrable
  have hpsi'int : IntervalIntegrable psi' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hpsi'c
  -- integration by parts with the running primitive
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := G) (v := psi)
    (u' := fun θ => Complex.exp (Complex.I * (phi θ : ℂ))) (v' := psi')
    hGc (by rw [huIcc]; exact hpsic) hGd hpsid hexpint hpsi'int
  have hGa : G a = 0 := intervalIntegral.integral_same
  have hkey : (∫ θ in a..b, Complex.exp (Complex.I * (phi θ : ℂ)) * psi θ) =
      G b * psi b - ∫ θ in a..b, G θ * psi' θ := by
    rw [hGa, zero_mul, sub_zero] at hibp
    linear_combination hibp
  rw [hkey]
  -- final bounds
  have hGb : ‖G b‖ ≤ 3 / lam := hGbound b ⟨hab, le_refl b⟩
  have hmajint : IntervalIntegrable (fun θ => 3 / lam * ‖psi' θ‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact continuousOn_const.mul hpsi'c.norm
  have hint2 : ‖∫ θ in a..b, G θ * psi' θ‖ ≤ ∫ θ in a..b, 3 / lam * ‖psi' θ‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun θ hθ => ?_)) hmajint
    have hθIcc : θ ∈ Set.Icc a b := ⟨le_of_lt hθ.1, hθ.2⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hGbound θ hθIcc) (norm_nonneg _)
  have hconst : (∫ θ in a..b, 3 / lam * ‖psi' θ‖) = 3 / lam * ∫ θ in a..b, ‖psi' θ‖ :=
    intervalIntegral.integral_const_mul _ _
  calc ‖G b * psi b - ∫ θ in a..b, G θ * psi' θ‖
      ≤ ‖G b * psi b‖ + ‖∫ θ in a..b, G θ * psi' θ‖ := norm_sub_le _ _
    _ ≤ 3 / lam * ‖psi b‖ + 3 / lam * ∫ θ in a..b, ‖psi' θ‖ := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hGb (norm_nonneg _)
        · rw [← hconst]
          exact hint2
    _ = 3 / lam * (‖psi b‖ + ∫ θ in a..b, ‖psi' θ‖) := by ring

end
