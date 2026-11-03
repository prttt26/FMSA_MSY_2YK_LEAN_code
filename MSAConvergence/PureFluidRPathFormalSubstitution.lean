import MSAConvergence.PureFluidRFormalSolution
import MSAConvergence.PureFluidRFormalPath
import Mathlib.RingTheory.MvPowerSeries.Substitution

set_option linter.style.header false

/-! Substitution of a zero-seeded coupling path into the independent
multivariate pure-fluid r solution. -/
noncomputable section
namespace FMSA.Convergence.PureFluidRPathFormalSubstitution
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRFormalPath
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Substituting any zero-constant-term theta path into the unique
multivariate r series solves the corresponding one-variable r system,
with the similarly substituted H series. -/
theorem RSeries_subst_path_system
    (z : T → ℝ) (theta : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0) :
    RNodePathSystem z theta
      (fun s => MvPowerSeries.subst theta (physicalH z s))
      (fun s => MvPowerSeries.subst theta (RSeries z s)) := by
  let ha : MvPowerSeries.HasSubst theta :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => hzero t)
  intro s
  have hs := congrArg (MvPowerSeries.substAlgHom (R := ℝ) ha)
    (RSeries_system z s)
  simp only [map_sum, map_mul, map_sub,
    MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X ha,
    MvPowerSeries.subst_C] at hs
  calc
    MvPowerSeries.subst theta (RSeries z s) =
        ∑ t, PowerSeries.C ((z s + z t)⁻¹) *
          (theta t *
            ((MvPowerSeries.subst theta (physicalH z s) *
              MvPowerSeries.subst theta (physicalH z t)) *
              (PowerSeries.C (z t) -
                MvPowerSeries.subst theta (RSeries z t)))) := by
              simpa only [PowerSeries.C] using hs
    _ = MvPowerSeries.subst theta (physicalH z s) *
        ∑ t, PowerSeries.C ((z s + z t)⁻¹) *
          (theta t *
            (MvPowerSeries.subst theta (physicalH z t) *
              (PowerSeries.C (z t) -
                MvPowerSeries.subst theta (RSeries z t)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          ring

/-- For a substituted H path, the unique one-variable r path is the
substitution of the independent multivariate r series. -/
theorem RNodePathSystem_eq_RSeries_subst
    (z : T → ℝ) (theta H R : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0)
    (hH : H = fun s => MvPowerSeries.subst theta (physicalH z s))
    (hR : RNodePathSystem z theta H R) :
    R = fun s => MvPowerSeries.subst theta (RSeries z s) := by
  subst H
  exact RNodePathSystem_unique z theta
    (fun s => MvPowerSeries.subst theta (physicalH z s))
    R _ hzero hR (RSeries_subst_path_system z theta hzero)

end FMSA.Convergence.PureFluidRPathFormalSubstitution

/-- info: 'FMSA.Convergence.PureFluidRPathFormalSubstitution.RSeries_subst_path_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRPathFormalSubstitution.RSeries_subst_path_system
/-- info: 'FMSA.Convergence.PureFluidRPathFormalSubstitution.RNodePathSystem_eq_RSeries_subst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRPathFormalSubstitution.RNodePathSystem_eq_RSeries_subst
