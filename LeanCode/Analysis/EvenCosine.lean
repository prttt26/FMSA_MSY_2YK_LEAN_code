import LeanCode.Analysis.RadialFourierInversion

/-! The cosine bridge only needs almost-everywhere evenness. In particular,
isolated choices of values at compact-support endpoints do not affect it. -/
noncomputable section
open MeasureTheory Set Real
open scoped FourierTransform

theorem fourier_of_ae_even (Φ : ℝ → ℂ)
    (heven : (fun v => Φ (-v)) =ᵐ[volume] Φ) (hint : Integrable Φ) (w : ℝ) :
    𝓕 Φ w = 2 * ∫ v in Ioi (0 : ℝ), (Real.cos (2 * π * v * w) : ℂ) * Φ v := by
  let Ψ : ℝ → ℂ := fun v => (Φ v + Φ (-v)) / 2
  have hΨ : Integrable Ψ := (hint.add hint.comp_neg).div_const 2
  have hsym : ∀ v, Ψ (-v) = Ψ v := by intro v; simp [Ψ, add_comm]
  have heq : Φ =ᵐ[volume] Ψ := by
    filter_upwards [heven] with v hv
    dsimp [Ψ]
    rw [hv]
    ring
  have hf : 𝓕 Φ w = 𝓕 Ψ w := by
    rw [Real.fourier_eq, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards [heq] with v hv
    rw [hv]
  rw [hf, fourier_of_even Ψ hsym hΨ w]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae heq] with v hv
  rw [hv]
