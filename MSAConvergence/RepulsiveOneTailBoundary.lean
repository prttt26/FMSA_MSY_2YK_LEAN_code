import MSAConvergence.ActualSeriesRootImplication

set_option linter.style.header false

/-! The exact strict Taylor-radius boundary for the HS-seeded original
one-tail amplitude vector with a repulsive Yukawa strength. Real MSA
roots exist on the entire positive-coupling axis, on both sides of
that boundary. Nothing is asserted at equality. -/
noncomputable section
namespace FMSA.Convergence.RepulsiveOneTailBoundary

open FMSA.Paper.FoldRadius
open FMSA.Paper.SingleTailRadius
open FMSA.Paper.TaylorRoot
open FMSA.Paper.Abel
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.SingleTailNegativeCouplingCounterexample
open FMSA.Convergence.ActualSeriesRootImplication
open scoped Topology ContDiff ENNReal

private def repulsiveCoefficients
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1) :
    ℕ → TailMatrix (Fin 1) 1 × TailMatrix (Fin 1) 1 :=
  branchCoefficients (fun t => physBranch z rho sigma K (-t))

/-- Strictly inside the exact one-tail radius, the original repulsive
BH amplitude Taylor vector is summable. -/
theorem repulsive_series_summable_inside
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau0 : 0 ≤ tau)
    (htauf : tau < foldCoupling z rho sigma K) :
    Summable (fun n => tau ^ n • repulsiveCoefficients z rho sigma K n) := by
  have hrad : ENNReal.ofReal tau <
      amplitudeRadius (repulsiveCoefficients z rho sigma K) := by
    rw [repulsiveCoefficients, repulsive_hs_radius_eq_fold z rho sigma K hz hr hs hv hk]
    exact (ENNReal.ofReal_lt_ofReal_iff
      ((lt_of_le_of_lt htau0 htauf))).mpr htauf
  obtain ⟨hD, hG⟩ := hasSum_inside_amplitudeRadius
    (repulsiveCoefficients z rho sigma K) tau htau0 hrad
  have hd : Summable (fun n => (tau ^ n • repulsiveCoefficients z rho sigma K n).1) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using (hD u i j).summable
  have hg : Summable (fun n => (tau ^ n • repulsiveCoefficients z rho sigma K n).2) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using (hG u i j).summable
  exact (hd.hasSum.prodMk hg.hasSum).summable

/-- The Taylor sum inside the strict radius is itself a solution of the
original repulsive MSA equations, including the zero-coupling seed. -/
theorem repulsive_series_sum_is_exact_root_inside
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau0 : 0 ≤ tau)
    (htauf : tau < foldCoupling z rho sigma K) :
    IsRoot z rho sigma (tau • (-K))
      (∑' n, tau ^ n • repulsiveCoefficients z rho sigma K n).1
      (∑' n, tau ^ n • repulsiveCoefficients z rho sigma K n).2 := by
  obtain ⟨_, ha, hroot⟩ :=
    reflected_physBranch_hs_germ z rho sigma K hz hr hs hv hk
  exact summable_at_real_coupling_implies_exact_root
    z rho sigma (-K) (fun t => physBranch z rho sigma K (-t))
    (ha.contDiffAt.of_le le_top) hroot tau
    (repulsive_series_summable_inside z rho sigma K
      hz hr hs hv hk tau htau0 htauf)

/-- Past the same exact radius, the original amplitude vector diverges
although the original MSA equation still has a real root. -/
theorem repulsive_root_exists_but_series_diverges_outside
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htauf : foldCoupling z rho sigma K < tau) :
    (∃ D G : TailMatrix (Fin 1) 1,
      IsRoot z rho sigma (tau • (-K)) D G) ∧
    ¬Summable (fun n => tau ^ n • repulsiveCoefficients z rho sigma K n) :=
  repulsive_root_and_divergence_beyond_radius
    z rho sigma K hz hr hs hv hk tau htauf

end FMSA.Convergence.RepulsiveOneTailBoundary

/-- info: 'FMSA.Convergence.RepulsiveOneTailBoundary.repulsive_series_summable_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RepulsiveOneTailBoundary.repulsive_series_summable_inside
/-- info: 'FMSA.Convergence.RepulsiveOneTailBoundary.repulsive_series_sum_is_exact_root_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RepulsiveOneTailBoundary.repulsive_series_sum_is_exact_root_inside
/-- info: 'FMSA.Convergence.RepulsiveOneTailBoundary.repulsive_root_exists_but_series_diverges_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RepulsiveOneTailBoundary.repulsive_root_exists_but_series_diverges_outside
