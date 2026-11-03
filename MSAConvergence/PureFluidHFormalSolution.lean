import MSAConvergence.PureFluidHFormalPositivity
import Mathlib.Data.Finsupp.Antidiagonal

set_option linter.style.header false

/-! Construct the finite Chandrasekhar H-node formal solution by total
degree recursion, then identify its fixed-point equation. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidHFormalPositivity
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [Fintype T] in
/-- Removing one variable from a monomial lowers total degree; both
indices in the resulting convolution are strictly below the original. -/
theorem antidiagonal_degree_lt_of_single_le
    (m : T →₀ ℕ) (t : T)
    (hle : Finsupp.single t 1 ≤ m)
    (p : (T →₀ ℕ) × (T →₀ ℕ))
    (hp : p ∈ Finset.antidiagonal (m - Finsupp.single t 1)) :
    p.1.degree < m.degree ∧ p.2.degree < m.degree := by
  let e : T →₀ ℕ := Finsupp.single t 1
  have hdecomp : e+(m-e)=m := add_tsub_cancel_of_le hle
  have hdeg : (m-e).degree < m.degree := by
    have heq : m.degree = 1+(m-e).degree := by
      calc
        m.degree = (e+(m-e)).degree := by rw [hdecomp]
        _ = 1+(m-e).degree := by simp [e]
    omega
  have hpadd : p.1+p.2=m-e := by
    simpa only [Finset.mem_antidiagonal] using hp
  constructor
  · have ha : p.1.degree ≤ (m-e).degree := by
      rw [← hpadd, map_add]
      exact Nat.le_add_right _ _
    exact lt_of_le_of_lt ha hdeg
  · have hb : p.2.degree ≤ (m-e).degree := by
      rw [← hpadd, map_add]
      exact Nat.le_add_left _ _
    exact lt_of_le_of_lt hb hdeg

/-- Recursive coefficient family for the finite H node system. -/
noncomputable def hCoeff (c : T → T → ℝ) (m : T →₀ ℕ) (s : T) : ℝ :=
  if m=0 then 1 else
    ∑ t, c s t *
      (if hle : Finsupp.single t 1 ≤ m then
        ∑ p ∈ (Finset.antidiagonal (m-Finsupp.single t 1)).attach,
          hCoeff c p.1.1 s * hCoeff c p.1.2 t
      else 0)
termination_by m.degree
decreasing_by
  all_goals
    first
    | exact (antidiagonal_degree_lt_of_single_le m t hle p.1 p.2).1
    | exact (antidiagonal_degree_lt_of_single_le m t hle p.1 p.2).2

/-- The finite node solution assembled from its recursively defined
multivariate coefficients. -/
def HSeries (c : T → T → ℝ) (s : T) : MvPowerSeries T ℝ :=
  fun m => hCoeff c m s

/-- The recursive series satisfies the denominator-free H-node equation. -/
theorem HSeries_system (c : T → T → ℝ) : HNodeSystem c (HSeries c) := by
  classical
  intro s
  ext m
  change hCoeff c m s = MvPowerSeries.coeff m
    (1 + ∑ t, MvPowerSeries.C (c s t) *
      (MvPowerSeries.X t * (HSeries c s * HSeries c t)))
  rw [hCoeff.eq_1]
  simp only [map_add, map_sum, MvPowerSeries.coeff_one]
  simp_rw [MvPowerSeries.coeff_C_mul]
  simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  simp_rw [MvPowerSeries.coeff_mul]
  by_cases hm : m = 0
  · subst m
    simp
  · simp only [if_neg hm, zero_add, one_mul]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs with hle
    · exact congrArg (fun v : ℝ => c s t * v) (by
        change (∑ p ∈ (Finset.antidiagonal (m - Finsupp.single t 1)).attach,
          hCoeff c p.1.1 s * hCoeff c p.1.2 t) =
          ∑ p ∈ Finset.antidiagonal (m - Finsupp.single t 1),
            hCoeff c p.1 s * hCoeff c p.2 t
        exact Finset.sum_attach (Finset.antidiagonal (m - Finsupp.single t 1))
          (fun p => hCoeff c p.1 s * hCoeff c p.2 t))
    · rfl

/-- The constructed formal node solution has nonnegative coefficients for
every nonnegative kernel. -/
theorem HSeries_coeff_nonneg (c : T → T → ℝ) (hc : ∀ s t, 0 ≤ c s t) :
    ∀ s m, 0 ≤ MvPowerSeries.coeff m (HSeries c s) :=
  h_node_system_coeff_nonneg c (HSeries c) hc (HSeries_system c)

/-- For positive Yukawa rates, the constructed H-node series is
coefficientwise nonnegative. -/
theorem physical_HSeries_coeff_nonneg (z : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∀ s m, 0 ≤ MvPowerSeries.coeff m
      (HSeries (fun s t => 1 / (z s + z t)) s) :=
  physical_h_node_coeff_nonneg z hz _ (HSeries_system _)

omit [Fintype T] [DecidableEq T] in
/-- The coefficient of an `X_t`-weighted H product depends only on
coefficients of lower total degree. -/
theorem coeff_X_mul_two_eq_of_lower_degree
    (H J : T → MvPowerSeries T ℝ) (s t : T) (m : T →₀ ℕ)
    (hprev : ∀ u d, d.degree < m.degree →
      MvPowerSeries.coeff d (H u) = MvPowerSeries.coeff d (J u)) :
    MvPowerSeries.coeff m (MvPowerSeries.X t * (H s * H t)) =
      MvPowerSeries.coeff m (MvPowerSeries.X t * (J s * J t)) := by
  classical
  simp only [MvPowerSeries.X_def]
  rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle
  · simp only [one_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpl, hpr⟩ := antidiagonal_degree_lt_of_single_le m t hle p hp
    rw [hprev s p.1 hpl, hprev t p.2 hpr]
  · rfl

omit [DecidableEq T] in
/-- The denominator-free finite H-node equation has at most one formal
multivariate solution, by induction on monomial total degree. -/
theorem HNodeSystem_unique (c : T → T → ℝ)
    (H J : T → MvPowerSeries T ℝ)
    (hH : HNodeSystem c H) (hJ : HNodeSystem c J) : H = J := by
  classical
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      ∀ s, MvPowerSeries.coeff m (H s) = MvPowerSeries.coeff m (J s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm s
      have hprev : ∀ u d, d.degree < m.degree →
          MvPowerSeries.coeff d (H u) = MvPowerSeries.coeff d (J u) := by
        intro u d hd
        exact ih d.degree (by omega) d rfl u
      rw [hH s, hJ s]
      simp only [map_add, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      simp only [MvPowerSeries.coeff_C_mul]
      exact congrArg (fun q : ℝ => c s t * q)
        (coeff_X_mul_two_eq_of_lower_degree H J s t m hprev)
  funext s
  ext m
  exact hmain m.degree m rfl s

omit [DecidableEq T] in
/-- The recursive construction is the unique formal solution of the
finite H-node system. -/
theorem HSeries_unique (c : T → T → ℝ) :
    ∃! H : T → MvPowerSeries T ℝ, HNodeSystem c H := by
  classical
  exact ⟨HSeries c, HSeries_system c,
    fun J hJ => (HNodeSystem_unique c J (HSeries c) hJ (HSeries_system c))⟩

end FMSA.Convergence.PureFluidHFormalSolution
/-- info: 'FMSA.Convergence.PureFluidHFormalSolution.antidiagonal_degree_lt_of_single_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalSolution.antidiagonal_degree_lt_of_single_le
/-- info: 'FMSA.Convergence.PureFluidHFormalSolution.HSeries_system' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalSolution.HSeries_system
/-- info: 'FMSA.Convergence.PureFluidHFormalSolution.HSeries_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalSolution.HSeries_coeff_nonneg
/-- info: 'FMSA.Convergence.PureFluidHFormalSolution.physical_HSeries_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalSolution.physical_HSeries_coeff_nonneg
/-- info: 'FMSA.Convergence.PureFluidHFormalSolution.coeff_X_mul_two_eq_of_lower_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalSolution.coeff_X_mul_two_eq_of_lower_degree
/-- info: 'FMSA.Convergence.PureFluidHFormalSolution.HNodeSystem_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalSolution.HNodeSystem_unique
/-- info: 'FMSA.Convergence.PureFluidHFormalSolution.HSeries_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalSolution.HSeries_unique
