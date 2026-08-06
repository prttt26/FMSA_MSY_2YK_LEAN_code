/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.Analysis.ContourSumUpperHalfPlane

/-!
# General Yukawa-denominator arc bound (item (iii) of the `A(−iy)` wiring)

The contour-sum engine's `harc` hypothesis asks the upper semicircular arc integral of the eq (20)
integrand to vanish as `R → ∞`.  Every eq (20) term has the Yukawa-denominator shape
`g(y)/((y−k)(iy+z))` (the exponentials of `E(−y)`, `U₁`, `[Q̂₀]⁻¹` having cancelled via the
additive-diameter identity `Rᵢⱼ = Rᵢ/2 + Rⱼ/2`, as for the leading term in
`MixtureYukawaContourTerm`).

`arc_integral_tendsto_zero` is the reusable mechanism: **if the numerator `g` is bounded by `M` on
the arc, the arc integral vanishes** (the integrand decays like `M/R²`, the arc length is `πR`, so
the integral is `O(M/R) → 0`).  It generalizes the leading term's arc bound (`g ≡ K`, constant) to
any bounded numerator, and reduces the `A(−iy)`-term arc bound to a single question: *is the
numerator `K·A(−iy)` (resp. `K·A(−iy)·A(−iy)`) bounded on the arc?*

**Why the numerator boundedness is not entrywise — the remaining concrete work.**  `A(−iy)` is an
entry of `[Q̂₀(−y)]⁻¹ − I`.  On the arc `y = R e^{iθ}` the Baxter argument is `s = I·(−y)` with
`Re s = R sin θ ≥ 0`, so the diagonal kernels `e^{−sσ}` decay — but the **unlike-pair** factor
`e^{−λs}` with `λ = (σⱼ − σᵢ)/2 < 0` *grows* like `e^{|λ| R sin θ}`.  So `q0_entry_c`, hence
`A(−iy)`, is **not** bounded entrywise on the arc.  The boundedness holds only for the *full
product* `E(−y)[Q̂₀(−y)]⁻¹U₁(y)[Q̂₀ᵀ(−y)]⁻¹E(−y)`, where the additive-diameter cancellation
`Rᵢⱼ = Rᵢ/2 + Rⱼ/2` kills the growing exponentials (exactly as it collapses the leading term to the
exponential-free `K/(iy+z)`).  Establishing that cancellation-tamed numerator bound is the
concrete-`Q̂₀` step that
feeds this general lemma; the arc-vanishing *mechanism* itself is what is proved here.
-/

open Filter Topology Metric MeasureTheory Complex

namespace FMSA.MixtureRDF

/-- **General Yukawa-denominator arc bound.**  If the numerator `g` is bounded by `M ≥ 0` on the
upper arc of radius `R` (eventually in `R`), then the arc integral of `g(y)/((y−k)(iy+z))` vanishes
as `R → ∞`: the integrand is `O(M/R²)` and the arc length `πR`, so the integral is `O(M/R) → 0`.
The leading eq (20) term is the constant case `g ≡ K`; the `A(−iy)` terms are `g = K·A(−iy)` etc. -/
theorem arc_integral_tendsto_zero {k z : ℂ} {g : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ᶠ R : ℝ in atTop, ∀ θ ∈ Set.uIoc (0:ℝ) Real.pi,
      ‖g ((R:ℂ) * Complex.exp (θ * Complex.I))‖ ≤ M) :
    Tendsto (fun R : ℝ => ∫ θ in (0:ℝ)..Real.pi,
      (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
        (g ((R:ℂ) * Complex.exp (θ * Complex.I)) /
          (((R:ℂ) * Complex.exp (θ * Complex.I) - k) *
           (Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) + z)))) atTop (𝓝 0) := by
  have hbd : Tendsto (fun R : ℝ => 4 * M * Real.pi / R) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 4 * M * Real.pi)).div_atTop tendsto_id
  apply squeeze_zero_norm' _ hbd
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (2 * ‖k‖),
    eventually_ge_atTop (2 * ‖z‖), hg] with R hR0 hRk hRz hgR
  have hle : ∀ θ ∈ Set.uIoc (0:ℝ) Real.pi,
      ‖(Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
        (g ((R:ℂ) * Complex.exp (θ * Complex.I)) /
          (((R:ℂ) * Complex.exp (θ * Complex.I) - k) *
           (Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) + z)))‖ ≤ 4 * M / R := by
    intro θ hθ
    set w : ℂ := (R:ℂ) * Complex.exp (θ * Complex.I) with hwdef
    have hcoef : ‖Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
      simp [Complex.norm_real, abs_of_nonneg hR0.le]
    have hwnorm : ‖w‖ = R := by
      rw [hwdef, norm_mul, Complex.norm_exp]
      simp [Complex.norm_real, abs_of_nonneg hR0.le]
    have hzfac : Complex.I * w + z = Complex.I * (w - Complex.I * z) := by
      linear_combination z * Complex.I_sq
    have hd1 : R / 2 ≤ ‖w - k‖ := by
      have h := norm_sub_norm_le w k; rw [hwnorm] at h; linarith
    have hd2 : R / 2 ≤ ‖Complex.I * w + z‖ := by
      rw [hzfac, norm_mul, Complex.norm_I, one_mul]
      have h := norm_sub_norm_le w (Complex.I * z)
      rw [hwnorm, norm_mul, Complex.norm_I, one_mul] at h; linarith
    have hprod : R ^ 2 / 4 ≤ ‖w - k‖ * ‖Complex.I * w + z‖ :=
      calc R ^ 2 / 4 = (R / 2) * (R / 2) := by ring
        _ ≤ ‖w - k‖ * ‖Complex.I * w + z‖ :=
            mul_le_mul hd1 hd2 (by positivity) (le_trans (by positivity) hd1)
    have hfw : ‖g w / ((w - k) * (Complex.I * w + z))‖ ≤ 4 * M / R ^ 2 := by
      rw [norm_div, norm_mul]
      calc ‖g w‖ / (‖w - k‖ * ‖Complex.I * w + z‖) ≤ M / (R ^ 2 / 4) := by
            gcongr; exact hgR θ hθ
        _ = 4 * M / R ^ 2 := by ring
    rw [norm_smul, hcoef]
    calc R * ‖g w / ((w - k) * (Complex.I * w + z))‖
          ≤ R * (4 * M / R ^ 2) := by gcongr
      _ = 4 * M / R := by rw [mul_div_assoc', pow_two, mul_div_mul_left _ _ hR0.ne']
  calc ‖∫ θ in (0:ℝ)..Real.pi, (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
            (g ((R:ℂ) * Complex.exp (θ * Complex.I)) /
              (((R:ℂ) * Complex.exp (θ * Complex.I) - k) *
               (Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) + z)))‖
        ≤ (4 * M / R) * |Real.pi - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hle
    _ = 4 * M * Real.pi / R := by rw [sub_zero, abs_of_pos Real.pi_pos]; ring

end FMSA.MixtureRDF
