/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.Analysis.ContourSumUpperHalfPlane

/-!
# Contour sum of the leading eq (20) term — a fully-worked instance (Tang & Lu eq (19)→(21))

This discharges the engine's integrand-specific inputs `hc`/`hd`/`harc` for the **leading term**
of a fixed RDF matrix entry `{Ĥ₁(k)}ᵢⱼ` (the `[Q̂₀]⁻¹ ≈ I` contribution of eq 20), giving a
complete, end-to-end contour sum — no remaining hypotheses beyond the state-point positivity.

**Why the leading term is exponential-free.**  The eq (19) integrand is
`E(−y)[Q̂₀(−y)]⁻¹U₁(y)[Q̂₀ᵀ(−y)]⁻¹E(−y)/(y−k)`.  Its leading (`[Q̂₀(−y)]⁻¹ = I`) contribution to
entry `(i,j)` is `E(−y)ᵢᵢ·U₁(y)ᵢⱼ·E(−y)ⱼⱼ/(y−k)` (both `E` diagonal).  With
`E(−y)ₘₘ = e^{iyRₘ/2}`, `U₁(y)ᵢⱼ = Kᵢⱼ e^{−iyRᵢⱼ}/(iy+zᵢⱼ)` and the **additive-diameter identity**
`Rᵢⱼ = Rᵢ/2 + Rⱼ/2`, the three exponentials cancel *exactly*:
`e^{iyRᵢ/2}·Kᵢⱼ e^{−iy(Rᵢ/2+Rⱼ/2)}·e^{iyRⱼ/2}/(iy+zᵢⱼ) = Kᵢⱼ/(iy+zᵢⱼ)`.
So the leading integrand is `Kᵢⱼ/((y−k)(iy+zᵢⱼ))`: a **single** simple Yukawa pole `y = i zᵢⱼ` and
no exponential, hence `O(1/y²)` decay — the arc bound is elementary (arc length `πR` × `O(1/R²)`
→ 0), no Jordan lemma needed.

`contourSum_leading_term` then feeds `improper_integral_eq_sum_yukawa_residues` (single pole,
`ι = Fin 1`) and reads off `∫_{−R}^{R} Kᵢⱼ/((y−k)(iy+zᵢⱼ)) dy → 2πi·(−Kᵢⱼ/(ik+zᵢⱼ))` — exactly
the eq (21) leading term (`−E(k) Res(…) E(k)` restores the `+Kᵢⱼ/(ik+zᵢⱼ)` sign of `bᵢⱼ`).

The Cauchy point `k` is placed just below the real axis (`Im k < 0`), so there is no on-contour
pole: this is the lower boundary value whose real-axis limit is the `½`-Plemelj term
(`SokhotskiPlemelj.lean`).  `#print axioms` = `halfDiskBoundary_eq_sum_of_small_circles` + the
standard three — the single accepted contour axiom, no new one.  The remaining eq (20) terms carry
the `A(−iy) = 2π√(ρρ)W/(Δ det)` factors (from `[Q̂₀(−y)]⁻¹ − I`); their `hc`/`hd` need the UHP
holomorphy of the closed-form inverse (`mixtureDet_pole_free_N` + entirety of the Baxter entries)
and their `harc` the same cancellation with the `W/det` growth — the full-matrix extension of this
worked leading term.
-/

open Filter Topology Metric MeasureTheory Complex

namespace FMSA.MixtureRDF

set_option maxHeartbeats 1200000 in
-- One heavy application of the multi-hypothesis contour-sum engine with an inline arc bound.
/-- **Contour sum of the leading eq (20) term.**  After the `E(−y)` exponential cancellation
`E(−y)ᵢᵢ·U₁(y)ᵢⱼ·E(−y)ⱼⱼ = Kᵢⱼ/(iy+zᵢⱼ)` (additive diameters `Rᵢⱼ = Rᵢ/2 + Rⱼ/2`) the leading
integrand is `K/((y−k)(iy+z))` — a single simple Yukawa pole `y = i z`, no exponential, `O(1/y²)`
decay.  Its principal-value inversion equals the pole residue:
`∫_{−R}^{R} K/((y−k)(iy+z)) dy → 2πi·(−K/(ik+z))`.  All of the engine's `hc`/`hd`/`harc` are
discharged here; hypotheses are only the state-point positivity `0 < r0`, the pole strictly inside
the UHP `r0 < Im(iz)`, and the Cauchy point just below the axis `Im k < 0`. -/
theorem contourSum_leading_term {K z0 k : ℂ} {r0 : ℝ}
    (hr0 : 0 < r0) (hUHP : r0 < (Complex.I * z0).im) (hk : k.im < 0) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, K / (((x:ℂ) - k) * (Complex.I * (x:ℂ) + z0))) atTop
      (𝓝 (2 * (Real.pi : ℂ) * Complex.I * (- K / (Complex.I * k + z0)))) := by
  have hzfac : ∀ w : ℂ, Complex.I * w + z0 = Complex.I * (w - Complex.I * z0) := fun w => by
    linear_combination z0 * Complex.I_sq
  have hknotim : ∀ w : ℂ, 0 ≤ w.im → w ≠ k := by
    intro w hw hcon; rw [hcon] at hw; linarith
  have hdenne : ∀ w : ℂ, w ≠ k → w ≠ Complex.I * z0 →
      (w - k) * (Complex.I * w + z0) ≠ 0 := fun w hwk hwp =>
    mul_ne_zero (sub_ne_zero.mpr hwk)
      (by rw [hzfac]; exact mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hwp))
  have hkball : k ∉ closedBall (Complex.I * z0) r0 := by
    rw [mem_closedBall_iff_norm]
    intro hcon
    have him : |(k - Complex.I * z0).im| ≤ ‖k - Complex.I * z0‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at him
    linarith [hUHP, hk, (abs_le.mp him).1, hcon]
  have hnotpole : ∀ w : ℂ, w ∉ (⋃ _ : Fin 1, ball (Complex.I * z0) r0) → w ≠ Complex.I * z0 :=
    fun w hw hcon => hw (Set.mem_iUnion.mpr ⟨0, by rw [hcon]; exact mem_ball_self hr0⟩)
  have hnotpole' : ∀ w : ℂ, w ∉ (⋃ _ : Fin 1, closedBall (Complex.I * z0) r0) →
      w ≠ Complex.I * z0 :=
    fun w hw hcon => hw (Set.mem_iUnion.mpr ⟨0, by rw [hcon]; exact mem_closedBall_self hr0.le⟩)
  have hgeqf : ∀ w : ℂ, K / ((w - k) * (Complex.I * w + z0))
      = (K / ((w - k) * Complex.I)) / (w - Complex.I * z0) := by
    intro w
    rw [div_div, mul_assoc, ← hzfac w]
  -- hc : continuity on the closed UHP minus the pole ball
  have hc : ContinuousOn (fun w => K / ((w - k) * (Complex.I * w + z0)))
      ({w : ℂ | 0 ≤ w.im} \ ⋃ _ : Fin 1, ball (Complex.I * z0) r0) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro w hw
    exact hdenne w (hknotim w hw.1) (hnotpole w hw.2)
  -- hd : holomorphy there
  have hd : ∀ w ∈ (({w : ℂ | 0 ≤ w.im} \ ⋃ _ : Fin 1, closedBall (Complex.I * z0) r0) \
      (∅ : Set ℂ)), DifferentiableAt ℂ (fun w => K / ((w - k) * (Complex.I * w + z0))) w := by
    intro w hw
    exact (differentiableAt_const K).div (by fun_prop)
      (hdenne w (hknotim w hw.1.1) (hnotpole' w hw.1.2))
  -- harc : the Jordan-free O(1/R²) arc bound
  have harc : Tendsto (fun R : ℝ => ∫ θ in (0:ℝ)..Real.pi,
      (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
        (fun w => K / ((w - k) * (Complex.I * w + z0)))
          ((R:ℂ) * Complex.exp (θ * Complex.I))) atTop (𝓝 0) := by
    have hbd : Tendsto (fun R : ℝ => 4 * ‖K‖ * Real.pi / R) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 4 * ‖K‖ * Real.pi)).div_atTop tendsto_id
    apply squeeze_zero_norm' _ hbd
    filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (2 * ‖k‖),
      eventually_ge_atTop (2 * ‖z0‖)] with R hR0 hRk hRz
    have hle : ∀ θ ∈ Set.uIoc (0:ℝ) Real.pi,
        ‖(Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
          (fun w => K / ((w - k) * (Complex.I * w + z0)))
            ((R:ℂ) * Complex.exp (θ * Complex.I))‖ ≤ 4 * ‖K‖ / R := by
      intro θ _
      simp only
      set w : ℂ := (R:ℂ) * Complex.exp (θ * Complex.I) with hwdef
      have hcoef : ‖Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
        simp [Complex.norm_real, abs_of_nonneg hR0.le]
      have hwnorm : ‖w‖ = R := by
        rw [hwdef, norm_mul, Complex.norm_exp]
        simp [Complex.norm_real, abs_of_nonneg hR0.le]
      have hd1 : R / 2 ≤ ‖w - k‖ := by
        have h := norm_sub_norm_le w k; rw [hwnorm] at h; linarith
      have hd2 : R / 2 ≤ ‖Complex.I * w + z0‖ := by
        rw [hzfac, norm_mul, Complex.norm_I, one_mul]
        have h := norm_sub_norm_le w (Complex.I * z0)
        rw [hwnorm, norm_mul, Complex.norm_I, one_mul] at h; linarith
      have hprod : R ^ 2 / 4 ≤ ‖w - k‖ * ‖Complex.I * w + z0‖ :=
        calc R ^ 2 / 4 = (R / 2) * (R / 2) := by ring
          _ ≤ ‖w - k‖ * ‖Complex.I * w + z0‖ :=
              mul_le_mul hd1 hd2 (by positivity) (le_trans (by positivity) hd1)
      have hfw : ‖K / ((w - k) * (Complex.I * w + z0))‖ ≤ 4 * ‖K‖ / R ^ 2 := by
        rw [norm_div, norm_mul]
        calc ‖K‖ / (‖w - k‖ * ‖Complex.I * w + z0‖) ≤ ‖K‖ / (R ^ 2 / 4) := by gcongr
          _ = 4 * ‖K‖ / R ^ 2 := by ring
      rw [norm_smul, hcoef]
      calc R * ‖K / ((w - k) * (Complex.I * w + z0))‖
            ≤ R * (4 * ‖K‖ / R ^ 2) := by gcongr
        _ = 4 * ‖K‖ / R := by
            rw [mul_div_assoc', pow_two, mul_div_mul_left _ _ hR0.ne']
    calc ‖∫ θ in (0:ℝ)..Real.pi, (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
              (fun w => K / ((w - k) * (Complex.I * w + z0)))
                ((R:ℂ) * Complex.exp (θ * Complex.I))‖
          ≤ (4 * ‖K‖ / R) * |Real.pi - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hle
      _ = 4 * ‖K‖ * Real.pi / R := by rw [sub_zero, abs_of_pos Real.pi_pos]; ring
  have key := improper_integral_eq_sum_yukawa_residues (ι := Fin 1) (z := fun _ => z0)
    (r' := fun _ => r0) (ĝ := fun _ _ => K) (k := k)
    (f := fun w => K / ((w - k) * (Complex.I * w + z0)))
    Set.countable_empty (fun _ => hr0) (fun _ => hUHP)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    hc hd (fun i w _ => hgeqf w)
    (fun i => by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro w hw
      exact mul_ne_zero (sub_ne_zero.mpr (fun hcon => hkball (hcon ▸ hw))) Complex.I_ne_zero)
    (fun i w hw => (differentiableAt_const K).div (by fun_prop)
      (mul_ne_zero (sub_ne_zero.mpr
        (fun hcon => hkball (ball_subset_closedBall (hcon ▸ hw.1)))) Complex.I_ne_zero))
    harc
  rw [Fin.sum_univ_one] at key
  exact key

end FMSA.MixtureRDF
