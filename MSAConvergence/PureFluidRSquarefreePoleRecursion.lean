import MSAConvergence.PureFluidRSquarefreeGeometric

set_option linter.style.header false

/-! The off-node formal r recursion restricted to squarefree theta
monomials. Every right-hand term removes one selected tail index. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRSquarefreePoleRecursion
open FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidRFormalDispersion
open FMSA.Convergence.PureFluidRFormalSolution
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [Fintype T] in
/-- Multiplication by a theta generator deletes that index from a
squarefree coefficient, and gives zero when the index is absent. -/
theorem coeff_X_mul_squarefree
    (F : MvPowerSeries T ℝ) (s : Finset T) (t : T) :
    MvPowerSeries.coeff (squarefreeMonomial s) (X t * F) =
      if t ∈ s then
        MvPowerSeries.coeff (squarefreeMonomial (s.erase t)) F
      else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases ht : t ∈ s
  · rw [if_pos (squarefreeMonomial_single_le_iff s t |>.mpr ht)]
    rw [squarefreeMonomial_tsub_single s t ht]
    simp [ht]
  · rw [if_neg (fun h => ht ((squarefreeMonomial_single_le_iff s t).mp h))]
    simp [ht]

omit [Fintype T] [DecidableEq T] in
/-- Every submonomial of a squarefree monomial is itself the
squarefree monomial on a subset of the original support. -/
theorem submonomial_of_squarefree
    (s : Finset T) (q : T →₀ ℕ)
    (hq : q ≤ squarefreeMonomial s) :
    q.support ⊆ s ∧ q = squarefreeMonomial q.support := by
  classical
  have hsub : q.support ⊆ s := by
    intro t ht
    by_contra hts
    have hle := ((Finsupp.le_iff q (squarefreeMonomial s)).mp hq) t ht
    have hzero : squarefreeMonomial s t = 0 := by
      simp [squarefreeMonomial_apply, hts]
    rw [hzero] at hle
    have hne : q t ≠ 0 := Finsupp.mem_support_iff.mp ht
    omega
  refine ⟨hsub, ?_⟩
  ext t
  by_cases ht : t ∈ q.support
  · have hle := ((Finsupp.le_iff q (squarefreeMonomial s)).mp hq) t ht
    have hne : q t ≠ 0 := Finsupp.mem_support_iff.mp ht
    have hst : t ∈ s := hsub ht
    have hsval : squarefreeMonomial s t = 1 := by
      simp [squarefreeMonomial_apply, hst]
    rw [hsval] at hle
    rw [squarefreeMonomial_apply, if_pos ht]
    omega
  · have hzero : q t = 0 := by
      by_contra hn
      exact ht (Finsupp.mem_support_iff.mpr hn)
    rw [hzero, squarefreeMonomial_apply, if_neg ht]

omit [Fintype T] [DecidableEq T] in
/-- The total theta degree of a squarefree monomial is the number
of selected tails. -/
theorem squarefreeMonomial_degree (s : Finset T) :
    (squarefreeMonomial s).degree = s.card := by
  classical
  have hsupp : (squarefreeMonomial s).support = s := by
    ext t
    simp [Finsupp.mem_support_iff, squarefreeMonomial_apply]
  rw [Finsupp.degree_apply, hsupp]
  simp [squarefreeMonomial_apply]

omit [Fintype T] [DecidableEq T] in
/-- Both factors in a squarefree Cauchy-product coefficient are
squarefree on subsets of the original selected tails. -/
theorem squarefree_antidiagonal_support
    (s : Finset T) (p q : T →₀ ℕ)
    (hpq : p + q = squarefreeMonomial s) :
    p.support ⊆ s ∧ q.support ⊆ s ∧
      p = squarefreeMonomial p.support ∧
      q = squarefreeMonomial q.support := by
  classical
  have hple : p ≤ squarefreeMonomial s :=
    (Finsupp.le_iff p (squarefreeMonomial s)).mpr (by
      intro t ht
      have h := congrArg (fun f : T →₀ ℕ => f t) hpq
      simp only [Finsupp.add_apply] at h
      omega)
  have hqle : q ≤ squarefreeMonomial s :=
    (Finsupp.le_iff q (squarefreeMonomial s)).mpr (by
      intro t ht
      have h := congrArg (fun f : T →₀ ℕ => f t) hpq
      simp only [Finsupp.add_apply] at h
      omega)
  obtain ⟨hps, hpe⟩ := submonomial_of_squarefree s p hple
  obtain ⟨hqs, hqe⟩ := submonomial_of_squarefree s q hqle
  exact ⟨hps, hqs, hpe, hqe⟩

omit [Fintype T] in
/-- In the coefficient of a product after the fresh index is
removed, the r factor lies on a strictly smaller selected set. -/
theorem squarefree_antidiagonal_strict
    (s : Finset T) (t : T) (ht : t ∈ s)
    (p q : T →₀ ℕ)
    (hpq : p + q = squarefreeMonomial (s.erase t)) :
    q = squarefreeMonomial q.support ∧ q.support.card < s.card := by
  obtain ⟨_, hqsub, _, hqeq⟩ :=
    squarefree_antidiagonal_support (s.erase t) p q hpq
  exact ⟨hqeq,
    (Finset.card_le_card hqsub).trans_lt
      (Finset.card_erase_lt_of_mem ht)⟩

/-- Every squarefree off-node r coefficient is a sum of fresh simple
pole factors times coefficients at strictly smaller selected sets. -/
theorem physicalFormalR_coeff_squarefree_recursion
    (z : T → ℝ) (x : ℝ) (s : Finset T) :
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
      ∑ t ∈ s, (x + z t)⁻¹ *
        MvPowerSeries.coeff (squarefreeMonomial (s.erase t))
          (physicalH z t * (C (z t) - RSeries z t + physicalFormalR z x)) := by
  classical
  rw [physicalFormalR_coeff_recursion]
  simp_rw [mul_assoc, coeff_X_mul_squarefree]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite]
  simp

/-- The off-node r series has no theta-independent term. -/
theorem physicalFormalR_coeff_empty (z : T → ℝ) (x : ℝ) :
    MvPowerSeries.coeff (squarefreeMonomial (∅ : Finset T))
      (physicalFormalR z x) = 0 := by
  rw [physicalFormalR_coeff_squarefree_recursion]
  simp

end FMSA.Convergence.PureFluidRSquarefreePoleRecursion

/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleRecursion.coeff_X_mul_squarefree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleRecursion.coeff_X_mul_squarefree
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleRecursion.submonomial_of_squarefree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleRecursion.submonomial_of_squarefree
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleRecursion.squarefreeMonomial_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleRecursion.squarefreeMonomial_degree
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleRecursion.squarefree_antidiagonal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleRecursion.squarefree_antidiagonal_support
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleRecursion.squarefree_antidiagonal_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleRecursion.squarefree_antidiagonal_strict
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleRecursion.physicalFormalR_coeff_squarefree_recursion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleRecursion.physicalFormalR_coeff_squarefree_recursion
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleRecursion.physicalFormalR_coeff_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleRecursion.physicalFormalR_coeff_empty
