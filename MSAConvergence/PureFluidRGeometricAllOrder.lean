import MSAConvergence.PureFluidROddCoeffSign

set_option linter.style.header false

/-! An exact recurrence for every multivariate coefficient of the
geometric inverse occurring in the pure-fluid r dispersion identity. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRGeometricAllOrder
open FMSA.Convergence.PureFluidROddCoeffSign
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [DecidableEq T] in
/-- For any nonconstant multiindex, the geometric inverse coefficient
is the sum of its predecessor coefficients weighted by the corresponding
linear theta coefficients. Repeated indices and coincident coefficients
require no special treatment. -/
theorem geometricTheta_coeff_recursion
    (c : T → ℝ) (m : T →₀ ℕ) (hm : m ≠ 0) :
    MvPowerSeries.coeff m (geometricTheta c) =
      ∑ t, if Finsupp.single t 1 ≤ m then
        c t * MvPowerSeries.coeff (m - Finsupp.single t 1) (geometricTheta c)
      else 0 := by
  classical
  conv_lhs => rw [geometricTheta_fixed_point c]
  simp only [map_add, linearTheta, Finset.sum_mul, map_sum]
  rw [MvPowerSeries.coeff_one, if_neg hm, zero_add]
  congr 1
  ext t
  rw [mul_assoc, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  split_ifs <;> simp

open FMSA.Convergence.PureFluidRFormalDispersion

/-- The exact odd part of every nonconstant formal r coefficient is a
geometric-inverse coefficient, including arbitrary repeated indices. -/
theorem physical_formal_R_odd_coeff_geometric
    (z : T → ℝ) (hz : ∀ t, 0 < z t) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (m : T →₀ ℕ) (hm : m ≠ 0) :
    MvPowerSeries.coeff m
      (physicalFormalR z x - physicalFormalR z (-x)) =
      -x * MvPowerSeries.coeff m
        (geometricTheta (fun t => 2 * z t / ((z t)^2 - x^2))) := by
  rw [physical_formal_R_odd_dispersion z hz x hplus hminus]
  rw [MvPowerSeries.coeff_C_mul]
  simp only [map_sub, MvPowerSeries.coeff_one, if_neg hm, zero_sub]
  change x * -(MvPowerSeries.coeff m
    (geometricTheta (fun t => 2 * z t / ((z t)^2 - x^2)))) = _
  ring

end FMSA.Convergence.PureFluidRGeometricAllOrder

/-- info: 'FMSA.Convergence.PureFluidRGeometricAllOrder.geometricTheta_coeff_recursion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRGeometricAllOrder.geometricTheta_coeff_recursion
/-- info: 'FMSA.Convergence.PureFluidRGeometricAllOrder.physical_formal_R_odd_coeff_geometric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRGeometricAllOrder.physical_formal_R_odd_coeff_geometric
