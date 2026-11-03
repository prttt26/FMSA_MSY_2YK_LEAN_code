import MSAConvergence.PureFluidRActualNodeBridge
import MSAConvergence.PureFluidHPathFormalSubstitution

set_option linter.style.header false

/-! Uniqueness of the formal one-parameter r-node system once the theta
and H paths are fixed. The actual-root coefficient bridge comes later. -/
noncomputable section
namespace FMSA.Convergence.PureFluidRFormalPath
open FMSA.Convergence.PureFluidHPathFormalSubstitution
variable {T : Type*} [Fintype T]

def RNodePathSystem (z : T → ℝ)
    (theta H R : T → PowerSeries ℝ) : Prop :=
  ∀ s, R s = H s * ∑ t,
    PowerSeries.C ((z s + z t)⁻¹) *
      (theta t * (H t * (PowerSeries.C (z t) - R t)))

/-- The theta factor has zero constant term, so every degree-n r
coefficient is determined by lower-degree r coefficients. -/
theorem RNodePathSystem_unique
    (z : T → ℝ) (theta H R Q : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0)
    (hR : RNodePathSystem z theta H R)
    (hQ : RNodePathSystem z theta H Q) : R = Q := by
  have hcoeff : ∀ n : ℕ, ∀ s : T,
      PowerSeries.coeff n (R s) = PowerSeries.coeff n (Q s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s
      rw [hR s, hQ s]
      apply coeff_mul_eq_of_coeff_le _ _ _ _ n
      · intro k hk
        rfl
      · intro k hk
        simp only [map_sum, PowerSeries.coeff_C_mul]
        congr 1
        funext t
        congr 1
        apply coeff_mul_zero_const_eq_of_coeff_lt _ _ _ k (hzero t)
        intro j hj
        apply coeff_mul_eq_of_coeff_le _ _ _ _ j
        · intro l hl
          rfl
        · intro l hl
          simp only [map_sub]
          rw [ih l (by omega) t]
  funext s
  ext n
  exact hcoeff n s

end FMSA.Convergence.PureFluidRFormalPath

/-- info: 'FMSA.Convergence.PureFluidRFormalPath.RNodePathSystem_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalPath.RNodePathSystem_unique
