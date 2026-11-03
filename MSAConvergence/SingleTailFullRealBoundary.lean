import MSAConvergence.NonnegativeAbelConverse

set_option linter.style.header false

/-! The exact real-axis convergence set of the original HS-seeded
one-tail BH amplitude vector, including both boundary points. -/
noncomputable section
namespace FMSA.Convergence.SingleTailFullRealBoundary

open FMSA.Paper.FoldRadius
open FMSA.Paper.SingleTailRadius
open FMSA.Paper.TaylorRoot
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.SingleTailNegativeCouplingCounterexample
open FMSA.Convergence.NonnegativeAbelConverse
open FMSA.Convergence.ActualSeriesRootImplication
open scoped Topology ContDiff ENNReal

/-- Every finite original-amplitude vector series converges strictly
inside its common scalar coefficient radius on the nonnegative axis. -/
theorem vector_summable_inside_radius {T : Type*} [Fintype T] {N : ℕ}
    (a : ℕ → TailMatrix T N × TailMatrix T N)
    (tau : ℝ) (htau : 0 ≤ tau)
    (h : ENNReal.ofReal tau < amplitudeRadius a) :
    Summable (fun n => tau ^ n • a n) := by
  obtain ⟨hD, hG⟩ := hasSum_inside_amplitudeRadius a tau htau h
  have hd : Summable (fun n => (tau ^ n • a n).1) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using (hD u i j).summable
  have hg : Summable (fun n => (tau ^ n • a n).2) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using (hG u i j).summable
  exact (hd.hasSum.prodMk hg.hasSum).summable

/-- The complete original-amplitude HS series for a positive one-tail
strength converges on precisely the closed real fold interval. -/
theorem attractive_series_summable_iff_abs_le_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) (tau : ℝ) :
    Summable (fun n => tau ^ n •
      branchCoefficients (physBranch z rho sigma K) n) ↔
      |tau| ≤ foldCoupling z rho sigma K := by
  have hf : 0 < foldCoupling z rho sigma K :=
    foldCoupling_pos z rho sigma K hz hr hs hv hk
  have hrad : amplitudeRadius
      (branchCoefficients (physBranch z rho sigma K)) =
      ENNReal.ofReal (foldCoupling z rho sigma K) :=
    single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk
      (physBranch z rho sigma K)
      (physBranch_continuousAt z rho sigma K hz hr hs hv hk)
      (physBranch_zero z rho sigma K hz hr hs hv hk)
      (physBranch_local_root z rho sigma K hz hr hs hv hk)
  constructor
  · intro hsum
    have hle := radius_ge_of_vector_summable
      (branchCoefficients (physBranch z rho sigma K)) tau hsum
    rw [hrad] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hf.le).mp hle
  · intro habs
    by_cases ht : 0 ≤ tau
    · have hle : tau ≤ foldCoupling z rho sigma K := by
        simpa only [abs_of_nonneg ht] using habs
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact vector_summable_inside_radius _ tau ht (by
          rw [hrad]
          exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ht hlt)).mpr hlt)
      · subst tau
        exact attractive_fold_vector_summable z rho sigma K hz hr hs hv hk
    · have hneg : tau < 0 := lt_of_not_ge ht
      have hsneg : 0 ≤ -tau := by linarith
      have hle : -tau ≤ foldCoupling z rho sigma K := by
        simpa only [abs_of_neg hneg] using habs
      have hrep := (repulsive_series_summable_iff_le_fold
        z rho sigma K hz hr hs hv hk (-tau) hsneg).mpr hle
      have heq (n : ℕ) : tau ^ n • branchCoefficients (physBranch z rho sigma K) n =
          (-tau) ^ n • branchCoefficients (fun t => physBranch z rho sigma K (-t)) n := by
        rw [branchCoefficients_reflected, smul_smul, ← mul_pow]
        simp
      simpa only [← heq] using hrep

/-- At every coupling where the complete original one-tail series
converges, its sum solves the exact real MSA equations. -/
theorem attractive_series_sum_is_exact_root_of_abs_le_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) (tau : ℝ)
    (habs : |tau| ≤ foldCoupling z rho sigma K) :
    IsRoot z rho sigma (tau • K)
      (∑' n, tau ^ n • branchCoefficients (physBranch z rho sigma K) n).1
      (∑' n, tau ^ n • branchCoefficients (physBranch z rho sigma K) n).2 := by
  exact summable_at_real_coupling_implies_exact_root
    z rho sigma K (physBranch z rho sigma K)
    ((physBranch_analyticAt z rho sigma K hz hr hs hv hk
      (zero_mem_Ioo z rho sigma K hz hr hs hv hk)).contDiffAt.of_le le_top)
    (physBranch_local_root z rho sigma K hz hr hs hv hk) tau
    ((attractive_series_summable_iff_abs_le_fold
      z rho sigma K hz hr hs hv hk tau).mpr habs)

/-- Changing the sign of the one-tail strength preserves the exact
closed real-axis convergence interval. -/
theorem repulsive_series_summable_iff_abs_le_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) (tau : ℝ) :
    Summable (fun n => tau ^ n •
      branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) ↔
      |tau| ≤ foldCoupling z rho sigma K := by
  have heq (n : ℕ) : tau ^ n •
      branchCoefficients (fun t => physBranch z rho sigma K (-t)) n =
      (-tau) ^ n • branchCoefficients (physBranch z rho sigma K) n := by
    rw [branchCoefficients_reflected, smul_smul, ← mul_pow]
    simp
  have hseries : (fun n => tau ^ n •
      branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) =
      (fun n => (-tau) ^ n • branchCoefficients (physBranch z rho sigma K) n) :=
    funext heq
  rw [hseries]
  simpa only [abs_neg] using attractive_series_summable_iff_abs_le_fold
    z rho sigma K hz hr hs hv hk (-tau)

/-- On that closed interval the reflected series sum solves the
original repulsive MSA equations. -/
theorem repulsive_series_sum_is_exact_root_of_abs_le_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) (tau : ℝ)
    (habs : |tau| ≤ foldCoupling z rho sigma K) :
    IsRoot z rho sigma (tau • (-K))
      (∑' n, tau ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).1
      (∑' n, tau ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).2 := by
  obtain ⟨_, ha, hroot⟩ :=
    reflected_physBranch_hs_germ z rho sigma K hz hr hs hv hk
  exact summable_at_real_coupling_implies_exact_root
    z rho sigma (-K) (fun t => physBranch z rho sigma K (-t))
    (ha.contDiffAt.of_le le_top) hroot tau
    ((repulsive_series_summable_iff_abs_le_fold
      z rho sigma K hz hr hs hv hk tau).mpr habs)

end FMSA.Convergence.SingleTailFullRealBoundary

/-- info: 'FMSA.Convergence.SingleTailFullRealBoundary.vector_summable_inside_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailFullRealBoundary.vector_summable_inside_radius
/-- info: 'FMSA.Convergence.SingleTailFullRealBoundary.attractive_series_summable_iff_abs_le_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailFullRealBoundary.attractive_series_summable_iff_abs_le_fold
/-- info: 'FMSA.Convergence.SingleTailFullRealBoundary.attractive_series_sum_is_exact_root_of_abs_le_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailFullRealBoundary.attractive_series_sum_is_exact_root_of_abs_le_fold
/-- info: 'FMSA.Convergence.SingleTailFullRealBoundary.repulsive_series_summable_iff_abs_le_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailFullRealBoundary.repulsive_series_summable_iff_abs_le_fold
/-- info: 'FMSA.Convergence.SingleTailFullRealBoundary.repulsive_series_sum_is_exact_root_of_abs_le_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailFullRealBoundary.repulsive_series_sum_is_exact_root_of_abs_le_fold
