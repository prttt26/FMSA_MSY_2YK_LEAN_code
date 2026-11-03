import MSAConvergence.PureFluidRCoeffRateContinuity
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.header false

/-! Positive pairwise-distinct rate vectors approximate every
positive finite rate vector, including collisions. -/
noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidRDistinctRateApprox
open FMSA.Convergence.PureFluidRKernelContinuity
open FMSA.Convergence.PureFluidRCoeffRateContinuity
open FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidRFormalDispersion
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
/-- A finite positive rate family admits an explicit sequence of
positive rate families that is eventually injective and converges
coordinatewise to the original family. -/
theorem exists_positive_injective_rate_approx
    [Finite T] (z : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃ w : ℕ → T → ℝ,
      Tendsto w atTop (𝓝 z) ∧
      (∀ n t, 0 < w n t) ∧
      (∀ᶠ n in atTop, Function.Injective (w n)) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let rank : T → ℝ := fun t => (e t).val
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let w : ℕ → T → ℝ := fun n t => z t + rank t * eps n
  have hrank_nonneg (t : T) : 0 ≤ rank t := by
    dsimp [rank]
    exact Nat.cast_nonneg _
  have hrank_inj : Function.Injective rank := by
    intro a b h
    have hv : (e a).val = (e b).val := by
      change (((e a).val : ℝ) = ((e b).val : ℝ)) at h
      exact_mod_cast h
    exact e.injective (Fin.ext hv)
  have heps_pos (n : ℕ) : 0 < eps n := by
    dsimp [eps]
    positivity
  have heps_lim : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hwlim : Tendsto w atTop (𝓝 z) := by
    apply tendsto_pi_nhds.mpr
    intro t
    have hterm : Tendsto (fun n => rank t * eps n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul heps_lim)
    simpa only [w, add_zero] using (tendsto_const_nhds.add hterm)
  have hwpos (n : ℕ) (t : T) : 0 < w n t := by
    dsimp [w]
    exact add_pos_of_pos_of_nonneg (hz t)
      (mul_nonneg (hrank_nonneg t) (heps_pos n).le)
  have hpair (a b : T) (hab : a ≠ b) :
      ∀ᶠ n in atTop, w n a ≠ w n b := by
    by_cases hzab : z a = z b
    · apply Filter.Eventually.of_forall
      intro n heq
      have heps : eps n ≠ 0 := (heps_pos n).ne'
      have hmul : rank a * eps n = rank b * eps n := by
        dsimp [w] at heq
        rw [hzab] at heq
        exact add_left_cancel heq
      exact hab (hrank_inj (mul_right_cancel₀ heps hmul))
    · have hlimdiff : Tendsto (fun n => w n a - w n b) atTop
          (𝓝 (z a - z b)) :=
        (tendsto_pi_nhds.mp hwlim a).sub (tendsto_pi_nhds.mp hwlim b)
      have hne : ∀ᶠ n in atTop, w n a - w n b ≠ 0 :=
        hlimdiff.eventually_ne (sub_ne_zero.mpr hzab)
      exact hne.mono (fun n hn heq => hn (sub_eq_zero.mpr heq))
  have hwinj : ∀ᶠ n in atTop, Function.Injective (w n) := by
    change ∀ᶠ n in atTop, ∀ a b : T, w n a = w n b → a = b
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (fun n _ => hab)
    · exact (hpair a b hab).mono (fun n hn heq => False.elim (hn heq))
  exact ⟨w, hwlim, hwpos, hwinj⟩

/-- The actual squarefree r coefficient has its positive kernel
integral formula for every strictly positive finite rate family,
including arbitrarily many coincident selected rates. -/
theorem physicalFormalR_squarefree_eq_kernel_any_rates
    (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 < x) :
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
      (Nat.factorial s.card : ℝ) *
        ((2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ), kernelProduct s z x k))) := by
  classical
  obtain ⟨w, hwlim, hwpos, hwinj⟩ :=
    exists_positive_injective_rate_approx z hz
  have hL : Tendsto
      (fun n => MvPowerSeries.coeff (squarefreeMonomial s)
        (physicalFormalR (w n) x)) atTop
      (𝓝 (MvPowerSeries.coeff (squarefreeMonomial s)
        (physicalFormalR z x))) :=
    (physicalFormalR_coeff_continuousAt_rate z hz x hx
      (squarefreeMonomial s)).tendsto.comp hwlim
  have hprod : ContinuousAt
      (fun z' : T → ℝ => ∏ i ∈ s, z' i) z := by
    apply tendsto_finsetProd s
    intro i hi
    exact continuousAt_apply i z
  have hI := kernelProduct_integral_continuousAt_rate s z
    (fun i _ => hz i) hs x hx
  have hRcont : ContinuousAt
      (fun z' : T → ℝ => (Nat.factorial s.card : ℝ) *
        ((2 ^ (s.card - 1) * ∏ i ∈ s, z' i) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ), kernelProduct s z' x k)))) z :=
    continuousAt_const.mul
      ((continuousAt_const.mul hprod).mul (continuousAt_const.mul hI))
  have hR := hRcont.tendsto.comp hwlim
  have heq :
      (fun n => MvPowerSeries.coeff (squarefreeMonomial s)
        (physicalFormalR (w n) x)) =ᶠ[atTop]
      (fun n => (Nat.factorial s.card : ℝ) *
        ((2 ^ (s.card - 1) * ∏ i ∈ s, w n i) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ), kernelProduct s (w n) x k)))) := by
    filter_upwards [hwinj] with n hn
    exact physicalFormalR_squarefree_eq_kernel_all_x
      s (w n) (hwpos n) (fun a ha b hb h => hn h) hs x hx
  exact tendsto_nhds_unique_of_eventuallyEq hL hR heq

/-- Every nonempty squarefree coefficient of the actual formal r
coordinate is strictly positive at positive frequency for arbitrary
positive tail rates, even when selected rates coincide. -/
theorem physicalFormalR_squarefree_coeff_pos_any_rates
    (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 < x) :
    0 < MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) := by
  rw [physicalFormalR_squarefree_eq_kernel_any_rates s hs z hz x hx]
  have hprod : 0 < ∏ i ∈ s, z i :=
    Finset.prod_pos (fun i _ => hz i)
  have hint := kernelProduct_integral_pos s z (fun i _ => hz i) hs x hx
  have hfac : (0 : ℝ) < Nat.factorial s.card := by
    exact_mod_cast Nat.factorial_pos s.card
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- The independently recursive r-node series has strictly positive
nonempty squarefree coefficients for any positive rates, including
rate collisions. -/
theorem RSeries_squarefree_coeff_pos_any_rates
    (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t) (t : T) :
    0 < MvPowerSeries.coeff (squarefreeMonomial s)
      (FMSA.Convergence.PureFluidRFormalSolution.RSeries z t) := by
  rw [← physicalFormalR_at_node z t]
  exact physicalFormalR_squarefree_coeff_pos_any_rates
    s hs z hz (z t) (hz t)

end FMSA.Convergence.PureFluidRDistinctRateApprox

/-- info: 'FMSA.Convergence.PureFluidRDistinctRateApprox.exists_positive_injective_rate_approx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRDistinctRateApprox.exists_positive_injective_rate_approx
/-- info: 'FMSA.Convergence.PureFluidRDistinctRateApprox.physicalFormalR_squarefree_eq_kernel_any_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRDistinctRateApprox.physicalFormalR_squarefree_eq_kernel_any_rates
/-- info: 'FMSA.Convergence.PureFluidRDistinctRateApprox.physicalFormalR_squarefree_coeff_pos_any_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRDistinctRateApprox.physicalFormalR_squarefree_coeff_pos_any_rates
/-- info: 'FMSA.Convergence.PureFluidRDistinctRateApprox.RSeries_squarefree_coeff_pos_any_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRDistinctRateApprox.RSeries_squarefree_coeff_pos_any_rates
