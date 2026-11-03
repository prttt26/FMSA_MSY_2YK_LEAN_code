import MSAConvergence.RepulsiveOneTailBoundary

set_option linter.style.header false

/-! A real nonnegative-coefficient converse to Abel's endpoint theorem:
finite radial limits force summability at the endpoint. The constant
coefficient may have either sign. -/
noncomputable section
namespace FMSA.Convergence.NonnegativeAbelConverse

open Filter Set
open FMSA.Paper.QuarticBranch
open FMSA.Paper.SingleTailRadius
open FMSA.Paper.SingleTail
open FMSA.Paper.ActualAnalyticTaylor
open FMSA.Paper.TaylorRoot
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.SingleTailNegativeCouplingCounterexample
open FMSA.Convergence.RepulsiveOneTailBoundary
open FMSA.Convergence.ActualSeriesRootImplication
open scoped Topology BigOperators

/-- If all positive-order coefficients are nonnegative and the interior
power-series sum has a finite left limit, the series is summable at the
positive endpoint. The constant coefficient need not be nonnegative. -/
theorem summable_endpoint_of_nonnegative_coefficients
    (a : ℕ → ℝ) (f : ℝ → ℝ) (R L : ℝ) (hR : 0 < R)
    (ha : ∀ n, 0 < n → 0 ≤ a n)
    (hinside : ∀ t ∈ Ico 0 R,
      HasSum (fun n => a n * t ^ n) (f t))
    (hlim : Tendsto f (𝓝[<] R) (𝓝 L)) :
    Summable (fun n => a n * R ^ n) := by
  let g : ℕ → ℝ := fun n => a (n + 1) * R ^ (n + 1)
  have hg0 (n : ℕ) : 0 ≤ g n := by
    exact mul_nonneg (ha (n + 1) (by omega)) (pow_nonneg hR.le _)
  have hbound (n : ℕ) : ∑ i ∈ Finset.range n, g i ≤ L - a 0 := by
    have hp : Continuous (fun t : ℝ =>
        ∑ i ∈ Finset.range n, a (i + 1) * t ^ (i + 1)) := by fun_prop
    have hplim : Tendsto (fun t : ℝ =>
        ∑ i ∈ Finset.range n, a (i + 1) * t ^ (i + 1))
        (𝓝[<] R) (𝓝 (∑ i ∈ Finset.range n,
          a (i + 1) * R ^ (i + 1))) :=
      (hp.tendsto R).mono_left nhdsWithin_le_nhds
    have hrlim : Tendsto (fun t => f t - a 0) (𝓝[<] R) (𝓝 (L - a 0)) :=
      hlim.sub tendsto_const_nhds
    have hle := le_of_tendsto_of_tendsto hplim hrlim (by
      filter_upwards [Ico_mem_nhdsLT hR] with t ht
      have hs := hinside t ht
      have htail : Summable (fun i => a (i + 1) * t ^ (i + 1)) :=
        (summable_nat_add_iff (f := fun n => a n * t ^ n) 1).mpr hs.summable
      have hsum : a 0 + ∑' i, a (i + 1) * t ^ (i + 1) = f t := by
        simpa [hs.tsum_eq] using hs.summable.sum_add_tsum_nat_add 1
      have hnonneg (i : ℕ) : 0 ≤ a (i + 1) * t ^ (i + 1) :=
        mul_nonneg (ha (i + 1) (by omega)) (pow_nonneg ht.1 _)
      have hpartial := htail.sum_le_tsum (Finset.range n) (fun i _ => hnonneg i)
      linarith)
    simpa only [g] using hle
  have hgs : Summable g := summable_of_sum_range_le hg0 hbound
  exact (summable_nat_add_iff (f := fun n => a n * R ^ n) 1).mp
    (by simpa only [g] using hgs)

/-- Both original one-tail amplitudes have finite left limits at the
quartic fold. -/
theorem single_tail_amplitudes_tendsto_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    Tendsto (fun t => (physBranch z rho sigma K t).1 0 0 0)
      (𝓝[<] (foldCoupling z rho sigma K))
      (𝓝 (DtS (z 0) (rho 0) (sigma 0)
        (c1 (aR z rho sigma) (bR z rho sigma)))) ∧
    Tendsto (fun t => (physBranch z rho sigma K t).2 0 0 0)
      (𝓝[<] (foldCoupling z rho sigma K))
      (𝓝 (GS (z 0) (rho 0) (sigma 0)
        (c1 (aR z rho sigma) (bR z rho sigma)))) := by
  have hab : aR z rho sigma < bR z rho sigma :=
    FMSA.Paper.SingleTailRadius.hab z rho sigma hz hr hs hv
  have hb : bR z rho sigma < 0 :=
    FMSA.Paper.SingleTailRadius.hb z rho sigma hz hr hs hv
  have hL : 0 < LR z rho sigma K :=
    FMSA.Paper.SingleTailRadius.hL z rho sigma K hz hr hs hv hk
  have hbr : Tendsto
      (branch (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K))
      (𝓝[<] (foldCoupling z rho sigma K))
      (𝓝 (c1 (aR z rho sigma) (bR z rho sigma))) := by
    have h : Tendsto
        (branch (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K))
        (𝓝[<] (foldTau (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K)))
        (𝓝 (branch (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K)
          (foldTau (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K)))) :=
      (branch_continuousWithinAt_fold hab hb hL).tendsto.mono_left
        (nhdsWithin_mono _ Iio_subset_Iic_self)
    rw [branch_fold hab hb hL] at h
    exact h
  have hc1 : c1 (aR z rho sigma) (bR z rho sigma) ≠ 0 :=
    (by linarith [(crit_order hab hb).2.1] :
      c1 (aR z rho sigma) (bR z rho sigma) < 0).ne
  have hDc : ContinuousAt (DtS (z 0) (rho 0) (sigma 0))
      (c1 (aR z rho sigma) (bR z rho sigma)) := by
    unfold DtS
    fun_prop
  have hGc : ContinuousAt (GS (z 0) (rho 0) (sigma 0))
      (c1 (aR z rho sigma) (bR z rho sigma)) := by
    unfold GS
    fun_prop (disch := assumption)
  have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
  constructor
  · simpa only [physBranch, sc, Function.comp_def, hdef] using hDc.tendsto.comp hbr
  · simpa only [physBranch, sc, Function.comp_def, hdef] using hGc.tendsto.comp hbr

/-- Both original attractive one-tail amplitude component series also
converge at the fold itself. This follows from their nonnegative
positive-order coefficients and the finite physical left limit. -/
theorem attractive_fold_components_summable
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    Summable (fun n =>
      (branchCoefficients (physBranch z rho sigma K) n).1 0 0 0 *
        (foldCoupling z rho sigma K) ^ n) ∧
    Summable (fun n =>
      (branchCoefficients (physBranch z rho sigma K) n).2 0 0 0 *
        (foldCoupling z rho sigma K) ^ n) := by
  have hf : 0 < foldCoupling z rho sigma K :=
    foldCoupling_pos z rho sigma K hz hr hs hv hk
  have hDpos : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 ≤ s * (branchCoefficients
        (physBranch z rho sigma K) n).1 u i j := by
    intro u i j
    exact ⟨1, one_ne_zero, fun n hn => by
      rw [one_mul]
      exact D_coeff_nonneg z rho sigma K hz hr hs hv hk n hn⟩
  have hGpos : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 ≤ s * (branchCoefficients
        (physBranch z rho sigma K) n).2 u i j := by
    intro u i j
    exact ⟨1, one_ne_zero, fun n hn => by
      rw [one_mul]
      exact G_coeff_nonneg z rho sigma K hz hr hs hv hk n hn⟩
  have hinside (t : ℝ) (ht : t ∈ Ico 0 (foldCoupling z rho sigma K)) :=
    hasSum_of_signed_analytic_branch (physBranch z rho sigma K)
      (foldCoupling z rho sigma K) hf
      (physBranch_analyticOnNhd z rho sigma K hz hr hs hv hk)
      hDpos hGpos t ht
  obtain ⟨hDlim, hGlim⟩ :=
    single_tail_amplitudes_tendsto_fold z rho sigma K hz hr hs hv hk
  constructor
  · apply summable_endpoint_of_nonnegative_coefficients
      (fun n => (branchCoefficients (physBranch z rho sigma K) n).1 0 0 0)
      (fun t => (physBranch z rho sigma K t).1 0 0 0)
      (foldCoupling z rho sigma K)
      (DtS (z 0) (rho 0) (sigma 0)
        (c1 (aR z rho sigma) (bR z rho sigma))) hf
    · intro n hn
      exact D_coeff_nonneg z rho sigma K hz hr hs hv hk n hn
    · intro t ht
      exact (hinside t ht).1 0 0 0
    · exact hDlim
  · apply summable_endpoint_of_nonnegative_coefficients
      (fun n => (branchCoefficients (physBranch z rho sigma K) n).2 0 0 0)
      (fun t => (physBranch z rho sigma K t).2 0 0 0)
      (foldCoupling z rho sigma K)
      (GS (z 0) (rho 0) (sigma 0)
        (c1 (aR z rho sigma) (bR z rho sigma))) hf
    · intro n hn
      exact G_coeff_nonneg z rho sigma K hz hr hs hv hk n hn
    · intro t ht
      exact (hinside t ht).2 0 0 0
    · exact hGlim

/-- The complete original attractive one-tail amplitude vector also
converges at its positive fold coupling. -/
theorem attractive_fold_vector_summable
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    Summable (fun n => (foldCoupling z rho sigma K) ^ n •
      branchCoefficients (physBranch z rho sigma K) n) := by
  obtain ⟨hDs, hGs⟩ :=
    attractive_fold_components_summable z rho sigma K hz hr hs hv hk
  have hd : Summable (fun n =>
      ((foldCoupling z rho sigma K) ^ n •
        branchCoefficients (physBranch z rho sigma K) n).1) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    have hu : u = 0 := Subsingleton.elim _ _
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst u; subst i; subst j
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hDs
  have hg : Summable (fun n =>
      ((foldCoupling z rho sigma K) ^ n •
        branchCoefficients (physBranch z rho sigma K) n).2) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    have hu : u = 0 := Subsingleton.elim _ _
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst u; subst i; subst j
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hGs
  exact (hd.hasSum.prodMk hg.hasSum).summable

/-- The attractive endpoint series sum is a real root of the original
MSA equations at the fold. -/
theorem attractive_fold_series_sum_is_exact_root
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    IsRoot z rho sigma ((foldCoupling z rho sigma K) • K)
      (∑' n, (foldCoupling z rho sigma K) ^ n •
        branchCoefficients (physBranch z rho sigma K) n).1
      (∑' n, (foldCoupling z rho sigma K) ^ n •
        branchCoefficients (physBranch z rho sigma K) n).2 := by
  exact summable_at_real_coupling_implies_exact_root
    z rho sigma K (physBranch z rho sigma K)
    ((physBranch_analyticAt z rho sigma K hz hr hs hv hk
      (zero_mem_Ioo z rho sigma K hz hr hs hv hk)).contDiffAt.of_le le_top)
    (physBranch_local_root z rho sigma K hz hr hs hv hk)
    (foldCoupling z rho sigma K)
    (attractive_fold_vector_summable z rho sigma K hz hr hs hv hk)

/-- Alternating signs preserve summability at a positive endpoint when
all positive-order coefficients of the original series are nonnegative. -/
theorem summable_alternating_at_endpoint
    (a : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (ha : ∀ n, 0 < n → 0 ≤ a n)
    (hs : Summable (fun n => a n * R ^ n)) :
    Summable (fun n => (-1 : ℝ) ^ n * a n * R ^ n) := by
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have han : 0 ≤ a n := ha n (by omega)
  simp [Real.norm_eq_abs, abs_of_nonneg han,
    abs_of_nonneg hR, mul_assoc]

/-- The complete reflected one-tail amplitude vector converges exactly
at its positive fold radius. -/
theorem repulsive_fold_vector_summable
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    Summable (fun n => (foldCoupling z rho sigma K) ^ n •
      branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) := by
  obtain ⟨hDs, hGs⟩ :=
    attractive_fold_components_summable z rho sigma K hz hr hs hv hk
  have hf : 0 ≤ foldCoupling z rho sigma K :=
    (foldCoupling_pos z rho sigma K hz hr hs hv hk).le
  have hd : Summable (fun n =>
      ((foldCoupling z rho sigma K) ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).1) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    have hu : u = 0 := Subsingleton.elim _ _
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst u; subst i; subst j
    have hp : ∀ n, 0 < n →
        0 ≤ (branchCoefficients (physBranch z rho sigma K) n).1 0 0 0 :=
      fun n hn => D_coeff_nonneg z rho sigma K hz hr hs hv hk n hn
    have h := summable_alternating_at_endpoint
      (fun n => (branchCoefficients (physBranch z rho sigma K) n).1 0 0 0)
      (foldCoupling z rho sigma K) hf hp hDs
    convert h using 1
    ext n
    simp only [branchCoefficients_reflected, Prod.smul_fst,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hg : Summable (fun n =>
      ((foldCoupling z rho sigma K) ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).2) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    have hu : u = 0 := Subsingleton.elim _ _
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst u; subst i; subst j
    have hp : ∀ n, 0 < n →
        0 ≤ (branchCoefficients (physBranch z rho sigma K) n).2 0 0 0 :=
      fun n hn => G_coeff_nonneg z rho sigma K hz hr hs hv hk n hn
    have h := summable_alternating_at_endpoint
      (fun n => (branchCoefficients (physBranch z rho sigma K) n).2 0 0 0)
      (foldCoupling z rho sigma K) hf hp hGs
    convert h using 1
    ext n
    simp only [branchCoefficients_reflected, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul]
    ring
  exact (hd.hasSum.prodMk hg.hasSum).summable

/-- At the repulsive one-tail fold radius, the Taylor sum is an exact
real MSA root. -/
theorem repulsive_fold_series_sum_is_exact_root
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    IsRoot z rho sigma ((foldCoupling z rho sigma K) • (-K))
      (∑' n, (foldCoupling z rho sigma K) ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).1
      (∑' n, (foldCoupling z rho sigma K) ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).2 := by
  obtain ⟨_, ha, hroot⟩ :=
    reflected_physBranch_hs_germ z rho sigma K hz hr hs hv hk
  exact summable_at_real_coupling_implies_exact_root
    z rho sigma (-K) (fun t => physBranch z rho sigma K (-t))
    (ha.contDiffAt.of_le le_top) hroot (foldCoupling z rho sigma K)
    (repulsive_fold_vector_summable z rho sigma K hz hr hs hv hk)

/-- For an admissible repulsive one-tail state, the entire nonnegative
coupling convergence set is the closed interval through the fold. -/
theorem repulsive_series_summable_iff_le_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau0 : 0 ≤ tau) :
    Summable (fun n => tau ^ n •
      branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) ↔
      tau ≤ foldCoupling z rho sigma K := by
  constructor
  · intro hsum
    by_contra hn
    have hlt : foldCoupling z rho sigma K < tau := lt_of_not_ge hn
    exact (repulsive_root_exists_but_series_diverges_outside
      z rho sigma K hz hr hs hv hk tau hlt).2 hsum
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact repulsive_series_summable_inside z rho sigma K
        hz hr hs hv hk tau htau0 hlt
    · subst tau
      exact repulsive_fold_vector_summable z rho sigma K hz hr hs hv hk

/-- Throughout the closed convergence interval, the repulsive one-tail
Taylor sum solves the original real Exact MSA equations. -/
theorem repulsive_series_sum_is_exact_root_le_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau0 : 0 ≤ tau)
    (htauf : tau ≤ foldCoupling z rho sigma K) :
    IsRoot z rho sigma (tau • (-K))
      (∑' n, tau ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).1
      (∑' n, tau ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n).2 := by
  rcases lt_or_eq_of_le htauf with hlt | heq
  · exact repulsive_series_sum_is_exact_root_inside z rho sigma K
      hz hr hs hv hk tau htau0 hlt
  · subst tau
    exact repulsive_fold_series_sum_is_exact_root z rho sigma K hz hr hs hv hk

end FMSA.Convergence.NonnegativeAbelConverse

/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.summable_endpoint_of_nonnegative_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.summable_endpoint_of_nonnegative_coefficients
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.single_tail_amplitudes_tendsto_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.single_tail_amplitudes_tendsto_fold
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.attractive_fold_components_summable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.attractive_fold_components_summable
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.attractive_fold_vector_summable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.attractive_fold_vector_summable
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.attractive_fold_series_sum_is_exact_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.attractive_fold_series_sum_is_exact_root
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.summable_alternating_at_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.summable_alternating_at_endpoint
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.repulsive_fold_vector_summable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.repulsive_fold_vector_summable
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.repulsive_fold_series_sum_is_exact_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.repulsive_fold_series_sum_is_exact_root
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.repulsive_series_summable_iff_le_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.repulsive_series_summable_iff_le_fold
/-- info: 'FMSA.Convergence.NonnegativeAbelConverse.repulsive_series_sum_is_exact_root_le_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NonnegativeAbelConverse.repulsive_series_sum_is_exact_root_le_fold
