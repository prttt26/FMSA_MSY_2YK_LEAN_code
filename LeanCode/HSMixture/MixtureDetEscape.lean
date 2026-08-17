/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureChordFamily

/-!
# Right-half-plane zero escape for `det Q̂₀` (`hbound` core, `OZFIX.17` matrix)

The homotopy pole-freeness `matDet_zeroFree_lowerHalfPlane_of_homotopy` (`MatrixDetPoleFree.lean`)
needs `hbound`: the zeros of `det Q̂₀` in the closed lower half `k`-plane are bounded.  Under the
Baxter convention the open lower half `k`-plane is the **right** half `s`-plane (`Re s > 0`), so
`hbound` is: `det Q̂₀(s) ≠ 0` for `Re s ≥ 0`, `‖s‖ ≥ R`.

This file proves the **escape mechanism**.  Via the monomial bridge
`s⁶·detF(s) = W(s) = Mc(s) + M₀(s)e^{−sσ₀} + M₁(s)e^{−sσ₁} + M₀₁(s)e^{−s(σ₀+σ₁)}`
(`detC_monomial_eq`), on `Re s ≥ 0` every exponential is a contraction (`exp_neg_mul_norm_le_one`,
`‖e^{−sσ}‖ ≤ 1`), so the three exponential terms are dominated by their polynomial coefficients.
`Wfun_ne_zero_of_dominant` / `detF_ne_zero_of_dominant`: if the degree-6 leading `Mc` outweighs the
sum `M₀+M₁+M₀₁`, then `W ≠ 0`, hence `detF ≠ 0`.  This is the matrix analog of the scalar
`exists_uniform_escape_radius` (`BaxterPoles.lean`) — the numerator-polynomial norm-dominance.

`exists_escape_radius` closes the per-`P` `hbound` (the polynomial asymptotics are discharged by the
`MixtureChordFamily.lean` bounds at `M := ‖s‖`).  `detF_ne_zero_of_Kbound` is the **uniform** version:
escape from a common bound `B` on the five envelope constants `K_Mc, K₀, μ, K₁, K₀₁ ≤ B`, at
`‖s‖ ≥ max(1, 5B+1)` — the mechanism the density-homotopy `hRunif` (uniform-in-`t` escape) needs, once
a `B` uniform over `t ∈ [0,1]` is supplied (the `K`-constants are continuous in `t`, hence bounded on
the compact `[0,1]`).
-/

set_option linter.style.longLine false

open Complex
namespace FMSA.MixtureHSPoles
noncomputable section

/-- For `Re s ≥ 0` and `σ ≥ 0`, the decaying exponential is a contraction: `‖e^{−sσ}‖ ≤ 1`.
The mechanism that makes the exponential terms subdominant in the right half `s`-plane. -/
theorem exp_neg_mul_norm_le_one {s : ℂ} {sigma : ℝ} (hre : 0 ≤ s.re) (hsigma : 0 ≤ sigma) :
    ‖Complex.exp (-(s * (sigma : ℂ)))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (-(s * (sigma : ℂ))).re = -(s.re * sigma) := by
    simp [Complex.mul_re]
  rw [this]
  have : 0 ≤ s.re * sigma := mul_nonneg hre hsigma
  linarith

/-- **Norm-dominance ⇒ `W ≠ 0`.**  In the right half-plane the three exponential terms of the monomial
form `W = Mc + M₀e^{−sσ₀} + M₁e^{−sσ₁} + M₀₁e^{−s(σ₀+σ₁)}` are each dominated by their polynomial
coefficient (`‖e‖ ≤ 1`), so if the leading `Mc` outweighs the sum `M₀+M₁+M₀₁` then `W ≠ 0`. -/
theorem Wfun_ne_zero_of_dominant (P : MixParams) (hP : P.Phys) {s : ℂ} (hre : 0 ≤ s.re)
    (hdom : ‖M0Num P s‖ + ‖M1Num P s‖ + ‖M01Num P s‖ < ‖McNum P s‖) :
    Wfun P s ≠ 0 := by
  obtain ⟨hs0, hs01, _, _⟩ := hP
  have hs1 : (0 : ℝ) < P.sig1 := lt_trans hs0 hs01
  have he0 : ‖Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤ 1 := exp_neg_mul_norm_le_one hre hs0.le
  have he1 : ‖Complex.exp (-(s * (P.sig1 : ℂ)))‖ ≤ 1 := exp_neg_mul_norm_le_one hre hs1.le
  have he01 : ‖Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤ 1 :=
    exp_neg_mul_norm_le_one hre (by positivity)
  intro hW
  -- from `Wfun = 0`, `Mc = −(rest)`, so `‖Mc‖ = ‖rest‖`
  have hMc : McNum P s = -(M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ)))
      + M1Num P s * Complex.exp (-(s * (P.sig1 : ℂ)))
      + M01Num P s * Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))) := by
    have := hW
    unfold Wfun at this
    linear_combination this
  have hbound : ‖M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ)))
      + M1Num P s * Complex.exp (-(s * (P.sig1 : ℂ)))
      + M01Num P s * Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖
      ≤ ‖M0Num P s‖ + ‖M1Num P s‖ + ‖M01Num P s‖ := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_
    · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) he0
    · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) he1
    · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) he01
  rw [hMc, norm_neg] at hdom
  exact absurd (lt_of_le_of_lt hbound hdom) (lt_irrefl _)

/-- **Escape from zeros in the right half-plane.**  With norm-dominance and `s ≠ 0`, the determinant
`detF` itself is nonzero (via the monomial bridge `s⁶·detF = W`). -/
theorem detF_ne_zero_of_dominant (P : MixParams) (hP : P.Phys) {s : ℂ} (hs : s ≠ 0)
    (hre : 0 ≤ s.re)
    (hdom : ‖M0Num P s‖ + ‖M1Num P s‖ + ‖M01Num P s‖ < ‖McNum P s‖) :
    P.detF s ≠ 0 := by
  intro hdet
  have hW : Wfun P s = 0 := by rw [← detC_monomial_eq P hs, hdet, mul_zero]
  exact Wfun_ne_zero_of_dominant P hP hre hdom hW

/-- The `M₁`-leading constant `μ = rr₁₁·Q'₁₁` is nonnegative. -/
theorem mu_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.mu := by
  obtain ⟨_, _, hrr, hqp, _⟩ := hP
  unfold MixParams.mu
  exact mul_nonneg (hrr 1 1).le (hqp 1 1).le

/-- **Uniform escape radius for `det Q̂₀` in the right half-plane — `hbound`, fully closed.**
There is an `R > 0` with `detF(s) ≠ 0` for every `s` with `Re s ≥ 0` and `‖s‖ ≥ R`.  The large-`‖s‖`
polynomial asymptotics (all bounds already in `MixtureChordFamily.lean`, evaluated at `M := ‖s‖`)
make the degree-6 leading `Mc ~ s⁶` outweigh `M₀,M₁ ~ s⁴` and `M₀₁ ~ s²`:
`‖Mc‖ ≥ ‖s‖⁶ − K_Mc‖s‖⁵` (from `McNum_sub_norm_le` + reverse triangle) while
`‖M₀‖+‖M₁‖+‖M₀₁‖ ≤ (K₀+μ+K₁+K₀₁)‖s‖⁴`, so for `‖s‖ ≥ K_Mc+K₀+μ+K₁+K₀₁+1` the norm-dominance holds
and `detF_ne_zero_of_dominant` applies.  Under the Baxter convention this is exactly the `hbound`
hypothesis (closed lower half `k`-plane = closed right half `s`-plane) of
`matDet_zeroFree_lowerHalfPlane_of_homotopy`. -/
theorem exists_escape_radius (P : MixParams) (hP : P.Phys) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℂ, 0 ≤ s.re → R ≤ ‖s‖ → P.detF s ≠ 0 := by
  have hKMc := KMc_nonneg P hP
  have hK0 := K0_nonneg P hP
  have hK1 := K1_nonneg P hP
  have hK01 := K01_nonneg P hP
  have hmu := mu_nonneg P hP
  refine ⟨max 1 (P.KMc + P.K0 + (P.mu + P.K1) + P.K01 + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  intro s hre hR
  have hx1 : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_left _ _) hR
  have hxR : P.KMc + P.K0 + (P.mu + P.K1) + P.K01 + 1 ≤ ‖s‖ := le_trans (le_max_right _ _) hR
  have hx0 : (0 : ℝ) ≤ ‖s‖ := by linarith
  have hne : s ≠ 0 := by
    intro h; rw [h, norm_zero] at hx1; linarith
  have hM0 := M0Num_norm_le P hP hx1 (le_refl ‖s‖)
  have hM1 := M1Num_norm_le P hP hx1 (le_refl ‖s‖)
  have hM01 := M01Num_norm_le P hP hx1 (le_refl ‖s‖)
  have hMcsub := McNum_sub_norm_le P hP hx1 (le_refl ‖s‖)
  have hMclow : ‖s‖ ^ 6 - P.KMc * ‖s‖ ^ 5 ≤ ‖McNum P s‖ := by
    have hrt : ‖(s ^ 6 : ℂ)‖ - ‖McNum P s‖ ≤ ‖McNum P s - s ^ 6‖ := by
      rw [← norm_sub_rev]; exact norm_sub_norm_le _ _
    rw [norm_pow] at hrt
    linarith
  have hx24 : ‖s‖ ^ 2 ≤ ‖s‖ ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hsum : ‖M0Num P s‖ + ‖M1Num P s‖ + ‖M01Num P s‖
      ≤ (P.K0 + (P.mu + P.K1) + P.K01) * ‖s‖ ^ 4 := by
    have h01 : P.K01 * ‖s‖ ^ 2 ≤ P.K01 * ‖s‖ ^ 4 := mul_le_mul_of_nonneg_left hx24 hK01
    nlinarith [hM0, hM1, hM01, h01]
  have hdom : ‖M0Num P s‖ + ‖M1Num P s‖ + ‖M01Num P s‖ < ‖McNum P s‖ := by
    have hkey : (P.K0 + (P.mu + P.K1) + P.K01) * ‖s‖ ^ 4 < ‖s‖ ^ 6 - P.KMc * ‖s‖ ^ 5 := by
      have hlead : (P.KMc + (P.K0 + (P.mu + P.K1) + P.K01) + 1) * ‖s‖ ≤ ‖s‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right hxR hx0
        nlinarith [this]
      nlinarith [hlead, hx1, hK0, hK1, hK01, hmu, hKMc,
        mul_nonneg (pow_nonneg hx0 4) hx0, pow_nonneg hx0 4, pow_nonneg hx0 5]
    linarith [hMclow, hsum]
  exact detF_ne_zero_of_dominant P hP hne hre hdom


/-- **Escape from a uniform `K`-bound.**  If all five envelope constants of `P` are `≤ B`, then
`detF(P, s) ≠ 0` for `Re s ≥ 0` and `‖s‖ ≥ max(1, 5B+1)`.  (Uniform version of `exists_escape_radius`,
for the density-homotopy escape.) -/
theorem detF_ne_zero_of_Kbound (P : MixParams) (hP : P.Phys) {B : ℝ} (hB : 0 ≤ B)
    (hKMc : P.KMc ≤ B) (hK0 : P.K0 ≤ B) (hmu : P.mu ≤ B) (hK1 : P.K1 ≤ B) (hK01 : P.K01 ≤ B)
    {s : ℂ} (hre : 0 ≤ s.re) (hs : max 1 (5 * B + 1) ≤ ‖s‖) :
    P.detF s ≠ 0 := by
  have hKMc0 := KMc_nonneg P hP
  have hx1 : (1:ℝ) ≤ ‖s‖ := le_trans (le_max_left _ _) hs
  have hxR : 5 * B + 1 ≤ ‖s‖ := le_trans (le_max_right _ _) hs
  have hx0 : (0:ℝ) ≤ ‖s‖ := by linarith
  have hne : s ≠ 0 := by intro h; rw [h, norm_zero] at hx1; linarith
  have hM0 := M0Num_norm_le P hP hx1 (le_refl ‖s‖)
  have hM1 := M1Num_norm_le P hP hx1 (le_refl ‖s‖)
  have hM01 := M01Num_norm_le P hP hx1 (le_refl ‖s‖)
  have hMcsub := McNum_sub_norm_le P hP hx1 (le_refl ‖s‖)
  have hMclow : ‖s‖ ^ 6 - P.KMc * ‖s‖ ^ 5 ≤ ‖McNum P s‖ := by
    have hrt : ‖(s ^ 6 : ℂ)‖ - ‖McNum P s‖ ≤ ‖McNum P s - s ^ 6‖ := by
      rw [← norm_sub_rev]; exact norm_sub_norm_le _ _
    rw [norm_pow] at hrt; linarith
  have hx24 : ‖s‖ ^ 2 ≤ ‖s‖ ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx45 : ‖s‖ ^ 4 ≤ ‖s‖ ^ 5 := pow_le_pow_right₀ hx1 (by norm_num)
  have hdom : ‖M0Num P s‖ + ‖M1Num P s‖ + ‖M01Num P s‖ < ‖McNum P s‖ := by
    have hsum : ‖M0Num P s‖ + ‖M1Num P s‖ + ‖M01Num P s‖ ≤ 4 * B * ‖s‖ ^ 4 := by
      have e0 : ‖M0Num P s‖ ≤ B * ‖s‖ ^ 4 :=
        le_trans hM0 (mul_le_mul_of_nonneg_right hK0 (pow_nonneg hx0 4))
      have e1 : ‖M1Num P s‖ ≤ 2 * B * ‖s‖ ^ 4 :=
        le_trans hM1 (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hx0 4))
      have e01 : ‖M01Num P s‖ ≤ B * ‖s‖ ^ 4 := by
        refine le_trans hM01 (le_trans (mul_le_mul_of_nonneg_right hK01 (pow_nonneg hx0 2)) ?_)
        exact mul_le_mul_of_nonneg_left hx24 hB
      linarith
    have hMclow' : ‖s‖ ^ 6 - B * ‖s‖ ^ 5 ≤ ‖McNum P s‖ := by nlinarith [hMclow, pow_nonneg hx0 5]
    have hkey : 4 * B * ‖s‖ ^ 4 < ‖s‖ ^ 6 - B * ‖s‖ ^ 5 := by
      have hlead : (5 * B + 1) * ‖s‖ ≤ ‖s‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hxR hx0]
      have hinner : (1:ℝ) ≤ ‖s‖ ^ 2 - B * ‖s‖ - 4 * B := by nlinarith [hlead, hx1, hB]
      nlinarith [mul_le_mul_of_nonneg_left hinner (pow_nonneg hx0 4), pow_pos (by linarith : (0:ℝ) < ‖s‖) 4]
    linarith
  exact detF_ne_zero_of_dominant P hP hne hre hdom
end
end FMSA.MixtureHSPoles
