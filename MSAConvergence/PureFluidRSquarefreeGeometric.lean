import MSAConvergence.PureFluidROddCoeffSign
import MSAConvergence.PureFluidRWeightOddPart
import Mathlib.Data.Finsupp.Indicator

set_option linter.style.header false

/-! Squarefree coefficients of a multivariate geometric inverse. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidROddCoeffSign
variable {T : Type*} [Fintype T] [DecidableEq T]

def squarefreeMonomial (s : Finset T) : T →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

omit [Fintype T] in
theorem squarefreeMonomial_apply (s : Finset T) (t : T) :
    squarefreeMonomial s t = if t ∈ s then 1 else 0 := by
  classical
  simp [squarefreeMonomial, Finsupp.indicator_apply]

omit [Fintype T] [DecidableEq T] in
theorem squarefreeMonomial_empty :
    squarefreeMonomial (∅ : Finset T) = 0 := by
  classical
  ext t
  simp [squarefreeMonomial_apply]

omit [Fintype T] in
theorem squarefreeMonomial_single_erase
    (s : Finset T) (t : T) (ht : t ∈ s) :
    Finsupp.single t 1 + squarefreeMonomial (s.erase t) =
      squarefreeMonomial s := by
  ext u
  by_cases hut : u = t
  · subst u
    simp [squarefreeMonomial_apply, ht]
  · by_cases hus : u ∈ s
    · simp [squarefreeMonomial_apply, hus, hut, Finset.mem_erase]
    · simp [squarefreeMonomial_apply, hus, hut, Finset.mem_erase]

omit [Fintype T] [DecidableEq T] in
theorem squarefreeMonomial_single_le_iff
    (s : Finset T) (t : T) :
    Finsupp.single t 1 ≤ squarefreeMonomial s ↔ t ∈ s := by
  classical
  rw [Finsupp.single_le_iff, squarefreeMonomial_apply]
  by_cases ht : t ∈ s <;> simp [ht]

omit [Fintype T] in
theorem squarefreeMonomial_tsub_single
    (s : Finset T) (t : T) (ht : t ∈ s) :
    squarefreeMonomial s - Finsupp.single t 1 =
      squarefreeMonomial (s.erase t) := by
  rw [← squarefreeMonomial_single_erase s t ht]
  exact add_tsub_cancel_left _ _

theorem coeff_X_mul_geometric_squarefree
    (c : T → ℝ) (s : Finset T) (t : T) :
    MvPowerSeries.coeff (squarefreeMonomial s) (X t * geometricTheta c) =
      if t ∈ s then
        MvPowerSeries.coeff (squarefreeMonomial (s.erase t)) (geometricTheta c)
      else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases ht : t ∈ s
  · rw [if_pos (squarefreeMonomial_single_le_iff s t |>.mpr ht)]
    rw [squarefreeMonomial_tsub_single s t ht]
    simp [ht]
  · rw [if_neg (fun h => ht ((squarefreeMonomial_single_le_iff s t).mp h))]
    simp [ht]

omit [Fintype T] [DecidableEq T] in
theorem squarefreeMonomial_ne_zero_of_nonempty
    (s : Finset T) (hs : s.Nonempty) : squarefreeMonomial s ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := hs
  intro heq
  have h := congrArg (fun m : T →₀ ℕ => m t) heq
  simp [squarefreeMonomial_apply, ht] at h

theorem coeff_geometric_squarefree_recursion
    (c : T → ℝ) (s : Finset T) (hs : s.Nonempty) :
    MvPowerSeries.coeff (squarefreeMonomial s) (geometricTheta c) =
      ∑ t ∈ s, c t *
        MvPowerSeries.coeff (squarefreeMonomial (s.erase t))
          (geometricTheta c) := by
  classical
  have hne := squarefreeMonomial_ne_zero_of_nonempty s hs
  conv_lhs => rw [geometricTheta_fixed_point c]
  simp only [map_add, linearTheta, Finset.sum_mul, map_sum]
  rw [MvPowerSeries.coeff_one, if_neg hne, zero_add]
  simp_rw [mul_assoc, MvPowerSeries.coeff_C_mul,
    coeff_X_mul_geometric_squarefree]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite]
  simp

omit [DecidableEq T] in
/-- The inverse of one minus a linear multivariate theta series has
the expected factorial product coefficient at every squarefree monomial. -/
theorem coeff_geometric_squarefree
    (c : T → ℝ) (s : Finset T) :
    MvPowerSeries.coeff (squarefreeMonomial s) (geometricTheta c) =
      (Nat.factorial s.card : ℝ) * ∏ t ∈ s, c t := by
  classical
  have hmain : ∀ n : ℕ, ∀ s : Finset T, s.card = n →
      MvPowerSeries.coeff (squarefreeMonomial s) (geometricTheta c) =
        (Nat.factorial s.card : ℝ) * ∏ t ∈ s, c t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs_card
      by_cases hs : s.Nonempty
      · rw [coeff_geometric_squarefree_recursion c s hs]
        have hterm (t : T) (ht : t ∈ s) :
            c t * MvPowerSeries.coeff (squarefreeMonomial (s.erase t))
              (geometricTheta c) =
            (Nat.factorial (s.card - 1) : ℝ) * ∏ u ∈ s, c u := by
          have hcard : (s.erase t).card < n := by
            rw [← hs_card]
            exact Finset.card_erase_lt_of_mem ht
          rw [ih (s.erase t).card hcard (s.erase t) rfl]
          rw [Finset.card_erase_of_mem ht]
          have hprod := Finset.mul_prod_erase s c ht
          rw [← hprod]
          ring
        calc
          (∑ t ∈ s, c t *
              MvPowerSeries.coeff (squarefreeMonomial (s.erase t))
                (geometricTheta c)) =
            ∑ t ∈ s,
              (Nat.factorial (s.card - 1) : ℝ) * ∏ u ∈ s, c u := by
                apply Finset.sum_congr rfl
                exact hterm
          _ = (s.card : ℝ) *
              ((Nat.factorial (s.card - 1) : ℝ) * ∏ u ∈ s, c u) := by
                simp
          _ = (Nat.factorial s.card : ℝ) * ∏ t ∈ s, c t := by
                have hcard : s.card - 1 + 1 = s.card := by
                  have hp := Finset.card_pos.mpr hs
                  omega
                have hfac : Nat.factorial s.card =
                    s.card * Nat.factorial (s.card - 1) := by
                  conv_lhs => rw [← hcard, Nat.factorial_succ]
                  rw [hcard]
                rw [hfac]
                push_cast
                ring
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simp only [squarefreeMonomial_empty, Finset.card_empty,
          Nat.factorial_zero, Nat.cast_one, Finset.prod_empty, mul_one]
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          geometricTheta, MvPowerSeries.constantCoeff_inv,
          map_sub, map_one, linearTheta_constantCoeff_zero]
        norm_num
  exact hmain s.card s rfl

open FMSA.Convergence.PureFluidRFormalDispersion
open FMSA.Convergence.PureFluidRWeightOddPart

/-- For every nonempty squarefree set with distinct positive rates,
the actual formal r odd coefficient equals the odd part of the
factorial W candidate. The remaining gap is the simple-pole shape
of the r coefficient itself. -/
theorem physical_formal_squarefree_odd_eq_W_odd
    (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (hzinj : Set.InjOn z s) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0) :
    MvPowerSeries.coeff (squarefreeMonomial s)
      (physicalFormalR z x - physicalFormalR z (-x)) =
      (Nat.factorial s.card : ℝ) *
        (multilinearWeight s z x - multilinearWeight s z (-x)) := by
  classical
  let c : T → ℝ := fun t => 2 * z t / ((z t)^2 - x^2)
  have hcoeff :
      MvPowerSeries.coeff (squarefreeMonomial s)
        (physicalFormalR z x - physicalFormalR z (-x)) =
      -x * ((Nat.factorial s.card : ℝ) * ∏ t ∈ s, c t) := by
    rw [physical_formal_R_odd_dispersion z hz x hplus hminus]
    rw [MvPowerSeries.coeff_C_mul]
    simp only [map_sub, MvPowerSeries.coeff_one,
      if_neg (squarefreeMonomial_ne_zero_of_nonempty s hs), zero_sub]
    change x * -(MvPowerSeries.coeff (squarefreeMonomial s)
      (geometricTheta c)) = _
    rw [coeff_geometric_squarefree]
    ring
  have hW := multilinearWeight_odd_part_off_poles s z x hs
    (fun i _ => hz i) hzinj
    (fun i _ => hplus i)
    (fun i _ => by simpa only [sub_eq_add_neg, add_comm] using hminus i)
  have hprod : (∏ t ∈ s, c t) =
      (∏ t ∈ s, 2 * z t) *
        (∏ t ∈ s, (z t ^ 2 - x ^ 2))⁻¹ := by
    dsimp [c]
    simp only [div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib]
  rw [hcoeff, hW, hprod]
  ring

end FMSA.Convergence.PureFluidRSquarefreeGeometric

/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_apply
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_empty
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_single_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_single_erase
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_single_le_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_single_le_iff
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_tsub_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_tsub_single
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.coeff_X_mul_geometric_squarefree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.coeff_X_mul_geometric_squarefree
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_ne_zero_of_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial_ne_zero_of_nonempty
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.coeff_geometric_squarefree_recursion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.coeff_geometric_squarefree_recursion
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.coeff_geometric_squarefree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.coeff_geometric_squarefree
/-- info: 'FMSA.Convergence.PureFluidRSquarefreeGeometric.physical_formal_squarefree_odd_eq_W_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreeGeometric.physical_formal_squarefree_odd_eq_W_odd
