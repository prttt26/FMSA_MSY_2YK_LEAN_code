import FMSAPaper.MixedRatePlateau
import FMSAPaper.FiniteBasisJets

/-! The mixed exponential blocks have no radial modes beyond the original
rates. These are the new cross terms absent from the single-rate proof. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.Paper.MixedRateCross

open MixedRateTails MixedRateWindows MixedRatePlateau FiniteBasis

def cross (z w a A b B u U v V r : ℝ) : ℝ :=
  ∫ t : ℝ, (-z * u * tail z a (t + r) - z * U * tail z A (t + r)) *
    (v * tail w b t + V * plateau w b B t)

theorem tail_plateau_integrable (z w a b B r : ℝ) (hz : 0 < z) (hw : 0 < w) :
    Integrable (fun t : ℝ => tail z a (t + r) * plateau w b B t) := by
  simp only [plateau, mul_add]
  exact (tail_box_integrable z a b B r).add (tail_tail_integrable z w a B r hz hw)

theorem cross_expansion (z w a A b B u U v V r : ℝ) (hz : 0 < z) (hw : 0 < w) :
    cross z w a A b B u U v V r =
      (-z * u) * (v * (∫ t : ℝ, tail z a (t + r) * tail w b t) +
        V * (∫ t : ℝ, tail z a (t + r) * plateau w b B t)) +
      (-z * U) * (v * (∫ t : ℝ, tail z A (t + r) * tail w b t) +
        V * (∫ t : ℝ, tail z A (t + r) * plateau w b B t)) := by
  let phi : Fin 2 → ℝ → ℝ := ![fun t => tail z a (t + r), fun t => tail z A (t + r)]
  let psi : Fin 2 → ℝ → ℝ := ![tail w b, plateau w b B]
  have hi : ∀ i j, Integrable (fun t : ℝ => phi i t * psi j t) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact tail_tail_integrable z w a b r hz hw
    · exact tail_plateau_integrable z w a b B r hz hw
    · exact tail_tail_integrable z w A b r hz hw
    · exact tail_plateau_integrable z w A b B r hz hw
  have he := integral_expansion (![-z * u, -z * U]) (![v, V]) phi psi hi
  simp only [linear, bilinear, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    phi, psi, Matrix.cons_val_fin_one] at he
  convert he using 1
  · unfold cross
    congr 1
    funext t
    ring
  · ring

theorem cross_inner_form (z w a A b B u U v V r : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hbB : b <= B) (hlo : a - b <= r) (hhi : r <= A - B) :
    cross z w a A b B u U v V r =
      ((-z * u) * (v * exp (z * (a - b)) / (z + w) +
        V * ((exp (z * (a - b)) - exp (z * (a - B))) / z + exp (z * (a - B)) / (z + w)))) * exp (-z * r) +
      ((-z * U) * (v * exp (w * (b - A)) / (z + w) +
        V * exp (w * (B - A)) / (z + w))) * exp (w * r) := by
  rw [cross_expansion z w a A b B u U v V r hz hw,
    tail_overlap_right z w a b r hz hw hlo,
    tail_plateau_overlap_right z w a b B r hz hw hbB hlo,
    tail_overlap_left z w A b r hz hw (by linarith),
    tail_plateau_overlap_left z w A b B r hz hw hhi]
  ring

theorem cross_middle_form (z w a A b B u U v V r : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hbB : b <= B) (hlo : a - b <= r) (hm : A - B <= r) (hhi : r <= A - b) :
    cross z w a A b B u U v V r =
      (-z * U) * V / z +
      ((-z * u) * (v * exp (z * (a - b)) / (z + w) +
          V * ((exp (z * (a - b)) - exp (z * (a - B))) / z + exp (z * (a - B)) / (z + w))) +
        (-z * U) * V * exp (z * (A - B)) * (1 / (z + w) - 1 / z)) * exp (-z * r) +
      ((-z * U) * v * exp (w * (b - A)) / (z + w)) * exp (w * r) := by
  rw [cross_expansion z w a A b B u U v V r hz hw,
    tail_overlap_right z w a b r hz hw hlo,
    tail_plateau_overlap_right z w a b B r hz hw hbB hlo,
    tail_overlap_left z w A b r hz hw hhi,
    tail_plateau_overlap_middle z w A b B r hz hw hm hhi]
  ring

/-- Coefficient tables do not depend on r. The interval can be degenerate;
coincident rates are allowed throughout. -/
theorem cross_inner_fixed_span (z w a A b B u U v V : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hbB : b <= B) :
    ∃ cm cp : ℝ, ∀ r, a - b <= r → r <= A - B →
      cross z w a A b B u U v V r = cm * exp (-z * r) + cp * exp (w * r) := by
  refine ⟨_, _, fun r hlo hhi => cross_inner_form z w a A b B u U v V r hz hw hbB hlo hhi⟩

theorem cross_middle_fixed_span (z w a A b B u U v V : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hbB : b <= B) :
    ∃ c0 cm cp : ℝ, ∀ r, a - b <= r → A - B <= r → r <= A - b →
      cross z w a A b B u U v V r = c0 + cm * exp (-z * r) + cp * exp (w * r) := by
  refine ⟨_, _, _, fun r hlo hm hhi => cross_middle_form z w a A b B u U v V r hz hw hbB hlo hm hhi⟩

end FMSA.Paper.MixedRateCross

/-- info: 'FMSA.Paper.MixedRateCross.tail_plateau_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateCross.tail_plateau_integrable

/-- info: 'FMSA.Paper.MixedRateCross.cross_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateCross.cross_expansion

/-- info: 'FMSA.Paper.MixedRateCross.cross_inner_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateCross.cross_inner_form

/-- info: 'FMSA.Paper.MixedRateCross.cross_middle_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateCross.cross_middle_form

/-- info: 'FMSA.Paper.MixedRateCross.cross_inner_fixed_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateCross.cross_inner_fixed_span

/-- info: 'FMSA.Paper.MixedRateCross.cross_middle_fixed_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateCross.cross_middle_fixed_span
