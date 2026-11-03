import MSAConvergence.TracerTailCovarianceBudget
import MSAConvergence.TracerEnergyCauchy

/-! Young inequality and the integrated algebra converting two forcing
budgets into a positive row energy bound. -/
open MeasureTheory
noncomputable section
namespace FMSA.Convergence.TracerEnergyYoung

/-- A quarter-energy Young inequality for nonnegative forcing norms. -/
theorem sqrt_mul_le_quarter_energy_add (E Q : ℝ) (hE : 0 ≤ E) (hQ : 0 ≤ Q) :
    Real.sqrt E * Real.sqrt Q ≤ E/4+Q := by
  have h := sq_nonneg (Real.sqrt E/2-Real.sqrt Q)
  nlinarith [Real.sq_sqrt hE,Real.sq_sqrt hQ]

/-- An exact integrated forcing split and two quarter-energy pointwise
bounds yield a uniform total energy bound. -/
theorem integrated_energy_le_two_forcings (E F G Q₁ Q₂ : ℝ → ℝ) (M₁ M₂ : ℝ)
    (hE : Integrable E) (hF : Integrable F) (hG : Integrable G)
    (hQ₁ : Integrable Q₁) (hQ₂ : Integrable Q₂)
    (hid : (∫ w : ℝ, E w) = (∫ w : ℝ, F w) + (∫ w : ℝ, G w))
    (hFp : ∀ w, F w ≤ E w / 4 + Q₁ w)
    (hGp : ∀ w, G w ≤ E w / 4 + Q₂ w)
    (hM₁ : (∫ w : ℝ, Q₁ w) ≤ M₁)
    (hM₂ : (∫ w : ℝ, Q₂ w) ≤ M₂) :
    (∫ w : ℝ, E w) ≤ 2*(M₁+M₂) := by
  have hFi : Integrable (fun w : ℝ => E w / 4 + Q₁ w) := (hE.div_const 4).add hQ₁
  have hGi : Integrable (fun w : ℝ => E w / 4 + Q₂ w) := (hE.div_const 4).add hQ₂
  have hf := integral_mono hF hFi hFp
  have hg := integral_mono hG hGi hGp
  rw [integral_add (hE.div_const 4) hQ₁] at hf
  rw [integral_add (hE.div_const 4) hQ₂] at hg
  simp only [integral_div] at hf hg
  linarith

end FMSA.Convergence.TracerEnergyYoung
/-- info: 'FMSA.Convergence.TracerEnergyYoung.sqrt_mul_le_quarter_energy_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyYoung.sqrt_mul_le_quarter_energy_add
/-- info: 'FMSA.Convergence.TracerEnergyYoung.integrated_energy_le_two_forcings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerEnergyYoung.integrated_energy_le_two_forcings
