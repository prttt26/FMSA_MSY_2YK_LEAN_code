import MSAConvergence.PureFluidHFormalSolution
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic

set_option linter.style.header false

/-! Formal substitution of a one-parameter theta path into the unique
multivariate Chandrasekhar H-node series. -/
noncomputable section
open MvPowerSeries
namespace FMSA.Convergence.PureFluidHPathFormalSubstitution
open FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidHFormalPositivity
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The finite H-node equation in one-variable formal coupling series. -/
def HNodePathSystem (c : T → T → ℝ)
    (theta H : T → PowerSeries ℝ) : Prop :=
  ∀ s, H s = 1 + ∑ t, PowerSeries.C (c s t) *
    (theta t * (H s * H t))

/-- Substituting any zero-constant-term formal theta path into the
constructed multivariate H series gives a solution of the path equation. -/
theorem HSeries_subst_path_system
    (c : T → T → ℝ) (theta : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0) :
    HNodePathSystem c theta
      (fun s => MvPowerSeries.subst theta (HSeries c s)) := by
  let ha : MvPowerSeries.HasSubst theta :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => hzero t)
  intro s
  have hs := congrArg (MvPowerSeries.substAlgHom (R := ℝ) ha)
    (HSeries_system c s)
  simp only [map_add, map_sum, map_one, map_mul,
    MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X ha] at hs
  simpa only [MvPowerSeries.subst_C, PowerSeries.C, mul_assoc] using hs

/-- Equal coefficients through degree n are preserved by multiplication. -/
theorem coeff_mul_eq_of_coeff_le
    (f g f' g' : PowerSeries ℝ) (n : ℕ)
    (hf : ∀ k ≤ n, PowerSeries.coeff k f = PowerSeries.coeff k f')
    (hg : ∀ k ≤ n, PowerSeries.coeff k g = PowerSeries.coeff k g') :
    PowerSeries.coeff n (f * g) = PowerSeries.coeff n (f' * g') := by
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [hf p.1 (by omega), hg p.2 (by omega)]

/-- A zero-constant-term factor makes the degree-n coefficient depend
only on the other factor's coefficients below degree n. -/
theorem coeff_mul_zero_const_eq_of_coeff_lt
    (theta f g : PowerSeries ℝ) (n : ℕ)
    (hzero : PowerSeries.constantCoeff theta = 0)
    (hfg : ∀ k < n, PowerSeries.coeff k f = PowerSeries.coeff k g) :
    PowerSeries.coeff n (theta * f) =
      PowerSeries.coeff n (theta * g) := by
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  by_cases hp0 : p.1 = 0
  · simp [hp0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero]
  · rw [hfg p.2 (by omega)]

omit [DecidableEq T] in
/-- The H-node path system has only one formal one-variable solution
when every theta path starts at zero. -/
theorem HNodePathSystem_unique
    (c : T → T → ℝ) (theta : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0)
    (H J : T → PowerSeries ℝ)
    (hH : HNodePathSystem c theta H)
    (hJ : HNodePathSystem c theta J) : H = J := by
  have hcoeff : ∀ n : ℕ, ∀ s : T,
      PowerSeries.coeff n (H s) = PowerSeries.coeff n (J s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s
      rw [hH s, hJ s]
      simp only [map_add, map_sum, PowerSeries.coeff_C_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      apply coeff_mul_zero_const_eq_of_coeff_lt _ _ _ n (hzero t)
      intro k hk
      exact coeff_mul_eq_of_coeff_le _ _ _ _ k
        (fun j hj => ih j (by omega) s)
        (fun j hj => ih j (by omega) t)
  funext s
  ext n
  exact hcoeff n s

/-- Every formal one-parameter H solution equals substitution of the
unique multivariate H solution along that zero-seeded theta path. -/
theorem HNodePathSystem_eq_HSeries_subst
    (c : T → T → ℝ) (theta H : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0)
    (hH : HNodePathSystem c theta H) :
    H = fun s => MvPowerSeries.subst theta (HSeries c s) :=
  HNodePathSystem_unique c theta hzero H _ hH
    (HSeries_subst_path_system c theta hzero)

end FMSA.Convergence.PureFluidHPathFormalSubstitution

/-- info: 'FMSA.Convergence.PureFluidHPathFormalSubstitution.HSeries_subst_path_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHPathFormalSubstitution.HSeries_subst_path_system
/-- info: 'FMSA.Convergence.PureFluidHPathFormalSubstitution.coeff_mul_eq_of_coeff_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHPathFormalSubstitution.coeff_mul_eq_of_coeff_le
/-- info: 'FMSA.Convergence.PureFluidHPathFormalSubstitution.coeff_mul_zero_const_eq_of_coeff_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHPathFormalSubstitution.coeff_mul_zero_const_eq_of_coeff_lt
/-- info: 'FMSA.Convergence.PureFluidHPathFormalSubstitution.HNodePathSystem_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHPathFormalSubstitution.HNodePathSystem_unique
/-- info: 'FMSA.Convergence.PureFluidHPathFormalSubstitution.HNodePathSystem_eq_HSeries_subst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHPathFormalSubstitution.HNodePathSystem_eq_HSeries_subst
