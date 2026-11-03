import MSAConvergence.RegularEndpointContinuation

/-! One attractive tail: the constructed maximal canonical endpoint is
strictly inside the genuine Taylor disk. The first unstable wave number
is not identified, and no physical RDF positivity is inferred. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.SingleTailCanonicalRadius
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper.StableIntervalRadius FMSA.Paper.TaylorRoot FMSA.Paper.FoldRadius
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.ActualCanonicalBranch
open FMSA.Convergence.MaximalCanonicalBranch FMSA.Convergence.MaximalMSAConvergence
open FMSA.Convergence.RegularEndpointContinuation
variable {T : Type*} [Fintype T] [Unique T]
variable (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
variable (hz : 0 < z default) (hr : 0 < rho 0) (hs : 0 < sigma 0)
  (hv : 0 < vacMix rho sigma) (hk : 0 < K default 0 0)
include hz hr hs hv hk

/-- The TRUE Taylor data of the data-constructed maximal representative
have the explicit single-tail fold radius; no sign hypothesis is supplied. -/
theorem maximal_radius_eq_fold
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    amplitudeRadius (branchCoefficients M.path) = ENNReal.ofReal (SingleTailRadius.foldCoupling z rho sigma K) := by
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound := ⟨le_rfl,by simpa using M.positive⟩
  exact SingleTailRadius.single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk M.path
    (M.analytic 0 h0).continuousAt M.at_seed M.local_roots

/-- Before both bounds, the ORIGINAL constructed canonical branch equals
the explicit actual quartic branch. This identifies values, not only jets. -/
theorem maximal_path_eq_explicit_before
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) (t : ℝ)
    (ht : 0 ≤ t) (htf : t < SingleTailRadius.foldCoupling z rho sigma K)
    (htM : ENNReal.ofReal t < M.bound) : M.path t = SingleTailRadius.physBranch z rho sigma K t := by
  have hzu : ∀ u, 0 < z u := fun u => by simpa only [Subsingleton.elim u default] using hz
  have hsig : ∀ i : Fin 1, 0 < sigma i := fun i => by simpa only [Subsingleton.elim i 0] using hs
  have hrho : ∀ i : Fin 1, 0 ≤ rho i := fun i => by simpa only [Subsingleton.elim i 0] using hr.le
  have hK : ∀ u (i j : Fin 1), K u i j = K u j i := by intro u i j; fin_cases i; fin_cases j; rfl
  have hdom : Icc (0 : ℝ) t ⊆ initialCouplings M.bound := fun s hs =>
    ⟨hs.1,(ENNReal.ofReal_le_ofReal hs.2).trans_lt htM⟩
  have hsub : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) (SingleTailRadius.foldCoupling z rho sigma K) :=
    fun s hs => ⟨hs.1,hs.2.trans_lt htf⟩
  have hphy := SingleTailRadius.physBranch_analyticOnNhd z rho sigma K hz hr hs hv hk
  have heq := actual_canonical_roots_eqOn_of_preconnected z hzu rho sigma hsig hrho K hK hv.ne'
    M.path (SingleTailRadius.physBranch z rho sigma K) (Icc 0 t) 0
    (convex_Icc 0 t).isPreconnected ⟨le_rfl,ht⟩ (M.analytic.continuousOn.mono hdom)
    (hphy.continuousOn.mono hsub) (M.at_seed.trans (SingleTailRadius.physBranch_zero z rho sigma K hz hr hs hv hk).symm)
    (fun s hs => M.roots s (hdom hs))
    (fun s hst => SingleTailRadius.physBranch_isRoot z rho sigma K hz hr hs hv hk
      ⟨(SingleTailRadius.zero_mem_Ioo z rho sigma K hz hr hs hv hk).1.le.trans hst.1,(hst.2.trans_lt htf).le⟩)
    (fun s hs => M.canonical s (hdom hs))
  exact heq ⟨ht,le_rfl⟩

/-- A true zero-mode witness strictly inside the Taylor disk bounds the
ENTIRE maximal initial canonical interval above. No claim is made that
this witness is the FIRST physical Fourier instability. -/
theorem maximal_bound_le_zero_before_radius
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    ∃ t : ℝ, 0 < t ∧ M.bound ≤ ENNReal.ofReal t ∧
      ENNReal.ofReal t < amplitudeRadius (branchCoefficients M.path) ∧
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1 (SingleTailRadius.physBranch z rho sigma K t).2)
        (amplitudeQp z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1 (SingleTailRadius.physBranch z rho sigma K t).2)
        (W z rho (SingleTailRadius.physBranch z rho sigma K t).1 (SingleTailRadius.physBranch z rho sigma K t).2)
        (C z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1 (SingleTailRadius.physBranch z rho sigma K t).2) 0).det = 0 := by
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound := ⟨le_rfl,by simpa using M.positive⟩
  obtain ⟨t,ht,hR,_hroot,hzero⟩ := BaxterZeroMode.actual_single_tail_zero_before_radius z rho sigma K
    hz hr hs hv hk M.path (M.analytic 0 h0).continuousAt M.at_seed M.local_roots
  refine ⟨t,ht,?_,hR,hzero⟩
  by_contra hn
  have htM : ENNReal.ofReal t < M.bound := lt_of_not_ge hn
  have htf : t < SingleTailRadius.foldCoupling z rho sigma K := by
    rw [maximal_radius_eq_fold z rho sigma K hz hr hs hv hk M] at hR
    exact (ENNReal.ofReal_lt_ofReal_iff (SingleTailRadius.foldCoupling_pos z rho sigma K hz hr hs hv hk)).mp hR
  have heq := maximal_path_eq_explicit_before z rho sigma K hz hr hs hv hk M t ht.le htf htM
  have hcanon := M.canonical t ⟨ht.le,htM⟩
  rw [heq] at hcanon
  have hrho : ∀ i : Fin 1, 0 ≤ rho i := fun i => by simpa only [Subsingleton.elim i 0] using hr.le
  exact physical_zero_not_canonical z rho sigma hrho (SingleTailRadius.physBranch z rho sigma K t) ⟨0,hzero⟩ hcanon

/-- For EVERY positive-density physical single-attractive-tail state,
the constructed canonical endpoint beta is STRICTLY smaller than the
intrinsic Taylor radius R. This is a real lower-bound conclusion for this
specified tail class, not the generic real-root/Taylor equivalence. -/
theorem maximal_bound_lt_radius
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    M.bound < amplitudeRadius (branchCoefficients M.path) := by
  obtain ⟨t,_ht,hb,hR,_hz⟩ := maximal_bound_le_zero_before_radius z rho sigma K hz hr hs hv hk M
  exact hb.trans_lt hR

/-- The physical one-attractive-tail maximal canonical endpoint is finite,
strictly before the explicit actual fold. -/
theorem maximal_bound_finite_before_fold
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    M.bound ≠ ⊤ ∧ M.bound.toReal < SingleTailRadius.foldCoupling z rho sigma K := by
  have h := maximal_bound_lt_radius z rho sigma K hz hr hs hv hk M
  rw [maximal_radius_eq_fold z rho sigma K hz hr hs hv hk M] at h
  have hn : M.bound ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.le
  refine ⟨hn,?_⟩
  have he : ENNReal.ofReal M.bound.toReal < ENNReal.ofReal (SingleTailRadius.foldCoupling z rho sigma K) := by
    rwa [ENNReal.ofReal_toReal hn]
  exact (ENNReal.ofReal_lt_ofReal_iff (SingleTailRadius.foldCoupling_pos z rho sigma K hz hr hs hv hk)).mp he

/-- ALL actual amplitude series sum to the ORIGINAL constructed physical
branch throughout its ENTIRE initial canonical interval. No radius, sign,
fold, first-wave-number or supplied branch hypothesis remains. -/
theorem maximal_whole_initial_interval_hasSum
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    AmplitudeHasSumBefore M.path M.bound :=
  (maximal_branch_taylor_criterion z rho sigma K _ M).mpr
    (maximal_bound_lt_radius z rho sigma K hz hr hs hv hk M).le

/-- The intrinsic HS Taylor coefficients sum to the EXPLICIT actual root
throughout 0<=t<fold, including points beyond the initial canonical bound.
No series value is assigned from arbitrary outside-domain M.path values. -/
theorem maximal_taylor_sums_to_explicit_until_fold
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    AmplitudeHasSumTo M.path (SingleTailRadius.physBranch z rho sigma K)
      (ENNReal.ofReal (SingleTailRadius.foldCoupling z rho sigma K)) := by
  let q := SingleTailRadius.physBranch z rho sigma K
  have hf : 0 < SingleTailRadius.foldCoupling z rho sigma K :=
    SingleTailRadius.foldCoupling_pos z rho sigma K hz hr hs hv hk
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound := ⟨le_rfl,by simpa using M.positive⟩
  have hcoeff := SingleTailRadius.branchCoefficients_eq z rho sigma K hz hr hs hv hk M.path
    (M.analytic 0 h0).continuousAt M.at_seed M.local_roots
  have hqA : AnalyticOnNhd ℝ q (initialCouplings (ENNReal.ofReal (SingleTailRadius.foldCoupling z rho sigma K))) := by
    rw [initial_couplings_ofReal _ hf]
    exact SingleTailRadius.physBranch_analyticOnNhd z rho sigma K hz hr hs hv hk
  have hqR : amplitudeRadius (branchCoefficients q) = ENNReal.ofReal (SingleTailRadius.foldCoupling z rho sigma K) :=
    SingleTailRadius.single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk q
      (SingleTailRadius.physBranch_continuousAt z rho sigma K hz hr hs hv hk)
      (SingleTailRadius.physBranch_zero z rho sigma K hz hr hs hv hk)
      (SingleTailRadius.physBranch_local_root z rho sigma K hz hr hs hv hk)
  have hsum := (analytic_branch_converges_before_iff q _ hqA).mpr hqR.ge
  intro t ht
  simpa only [hcoeff] using hsum t ht

/-- The canonical endpoint is strictly before the explicit fold, so its
WHOLE left branch has an explicit analytic root extension. No regularity or
full limit at the endpoint is supplied, even in a potentially singular case. -/
theorem maximal_endpoint_explicit_extension
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    HasAnalyticLeftRootExtension z rho sigma K M.path M.bound.toReal
      (SingleTailRadius.physBranch z rho sigma K M.bound.toReal) := by
  obtain ⟨hfinite,hbf⟩ := maximal_bound_finite_before_fold z rho sigma K hz hr hs hv hk M
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hlow := (SingleTailRadius.zero_mem_Ioo z rho sigma K hz hr hs hv hk).1
  let q := SingleTailRadius.physBranch z rho sigma K
  have hqa : AnalyticAt ℝ q M.bound.toReal :=
    SingleTailRadius.physBranch_analyticAt z rho sigma K hz hr hs hv hk ⟨hlow.trans hb,hbf⟩
  have hqr : ∀ᶠ t in 𝓝 M.bound.toReal, IsRoot z rho sigma (t • K) (q t).1 (q t).2 := by
    filter_upwards [Ioo_mem_nhds (hlow.trans hb) hbf] with t ht
    exact SingleTailRadius.physBranch_isRoot z rho sigma K hz hr hs hv hk ⟨ht.1.le,ht.2.le⟩
  have hleft : M.path =ᶠ[𝓝[<] M.bound.toReal] q := by
    have hpos : ∀ᶠ t : ℝ in 𝓝 M.bound.toReal, 0 < t := Ioi_mem_nhds hb
    filter_upwards [self_mem_nhdsWithin,hpos.filter_mono nhdsWithin_le_nhds] with t htb ht0
    have htM : ENNReal.ofReal t < M.bound := by
      rw [← ENNReal.ofReal_toReal hfinite]
      exact (ENNReal.ofReal_lt_ofReal_iff hb).mpr htb
    exact maximal_path_eq_explicit_before z rho sigma K hz hr hs hv hk M t ht0.le (htb.trans hbf) htM
  exact ⟨q,rfl,hqa,hqr,hleft⟩

/-- EVERY positive-density single-attractive-tail canonical endpoint has
a UNIQUE genuine finite left limit, given by the explicit actual branch. -/
theorem maximal_endpoint_full_limit
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    Tendsto M.path (𝓝[<] M.bound.toReal)
      (𝓝 (SingleTailRadius.physBranch z rho sigma K M.bound.toReal)) :=
  analytic_left_extension_gives_limit z rho sigma K M.path M.bound.toReal _
    (maximal_endpoint_explicit_extension z rho sigma K hz hr hs hv hk M)

/-- ALL approaching endpoint clusters equal the explicit endpoint state,
with no inverse or assumed continuity at M.path(bound). -/
theorem maximal_endpoint_clusters_unique
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma))
    (a : TailMatrix T 1 × TailMatrix T 1) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 M.bound.toReal) (ht : Tendsto u atTop (𝓝 M.bound.toReal))
    (ha : Tendsto (fun n => M.path (u n)) atTop (𝓝 a)) :
    a = SingleTailRadius.physBranch z rho sigma K M.bound.toReal :=
  endpoint_cluster_unique_of_left_limit M.path M.bound.toReal _ a
    (maximal_endpoint_full_limit z rho sigma K hz hr hs hv hk M) u (fun n => (hu n).2) ht ha

/-- The full explicit limiting state is an ACTUAL root in canonical closure
with a physical Fourier zero, hence noncanonical. Its wave number may be
zero or nonzero; no FIRST-zero-mode assertion is made. -/
theorem maximal_endpoint_physical_zero
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    let a := SingleTailRadius.physBranch z rho sigma K M.bound.toReal
    IsRoot z rho sigma (M.bound.toReal • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧ a ∉ canonicalAmplitudes z rho sigma ∧
      ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0 := by
  have hfinite := (maximal_bound_finite_before_fold z rho sigma K hz hr hs hv hk M).1
  have hzu : ∀ u, 0 < z u := fun u => by simpa only [Subsingleton.elim u default] using hz
  have hsig : ∀ i : Fin 1, 0 < sigma i := fun i => by simpa only [Subsingleton.elim i 0] using hs
  have hrho : ∀ i : Fin 1, 0 ≤ rho i := fun i => by simpa only [Subsingleton.elim i 0] using hr.le
  obtain ⟨a,u,hu,ht,ha,hroot,hclose,hzero⟩ :=
    FMSA.Convergence.ScalarCanonicalProperness.maximal_finite_endpoint_has_physical_cluster
      z hzu rho sigma hsig hrho K hv.ne' _ M hfinite
  have heq := maximal_endpoint_clusters_unique z rho sigma K hz hr hs hv hk M a u hu ht ha
  rw [heq] at hroot hclose hzero
  exact ⟨hroot,hclose,physical_zero_not_canonical z rho sigma hrho _ hzero,hzero⟩

/-- There is a strictly longer continuous actual root branch, retaining ALL
old values and analytic through its unique noncanonical endpoint. The user's
maximal INITIAL canonical interval is not enlarged by this construction. -/
theorem maximal_endpoint_longer_root_prefix
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    HasLongerAnalyticRootPrefix z rho sigma K M.path M.bound.toReal
      (SingleTailRadius.physBranch z rho sigma K M.bound.toReal) := by
  have hfinite := (maximal_bound_finite_before_fold z rho sigma K hz hr hs hv hk M).1
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings (ENNReal.ofReal_toReal hfinite).symm).trans (initial_couplings_ofReal _ hb)
  exact analytic_left_extension_gives_longer_root_prefix z rho sigma K M.path M.bound.toReal _
    (by simpa only [hset] using M.analytic.continuousOn) (by simpa only [hset] using M.roots)
    (maximal_endpoint_explicit_extension z rho sigma K hz hr hs hv hk M)

/-- The HS Taylor series converge even AT the excluded canonical endpoint,
to its TRUE explicit limiting root. This is not a value assigned to the
arbitrary representative M.path AT that excluded point. -/
theorem maximal_endpoint_taylor_hasSum
    (M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma)) :
    let b := M.bound.toReal
    let a := SingleTailRadius.physBranch z rho sigma K b
    (∀ u i j, HasSum (fun n => (branchCoefficients M.path n).1 u i j*b^n) (a.1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (branchCoefficients M.path n).2 u i j*b^n) (a.2 u i j)) := by
  obtain ⟨hfinite,hbf⟩ := maximal_bound_finite_before_fold z rho sigma K hz hr hs hv hk M
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  exact maximal_taylor_sums_to_explicit_until_fold z rho sigma K hz hr hs hv hk M _
    ⟨hb.le,(ENNReal.ofReal_lt_ofReal_iff (SingleTailRadius.foldCoupling_pos z rho sigma K hz hr hs hv hk)).mpr hbf⟩

/-- Physical DATA ALONE construct the maximal initial branch, prove beta<R
and ALL initial-interval amplitude sums, and give the full unique actual
noncanonical endpoint limit. No branch/radius/sign/fold or limit is supplied. -/
theorem exists_hs_branch_with_strict_radius_and_limit :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      M.bound < amplitudeRadius (branchCoefficients M.path) ∧
      AmplitudeHasSumBefore M.path M.bound ∧ M.bound ≠ ⊤ ∧
      Tendsto M.path (𝓝[<] M.bound.toReal) (𝓝 (SingleTailRadius.physBranch z rho sigma K M.bound.toReal)) ∧
      HasAnalyticLeftRootExtension z rho sigma K M.path M.bound.toReal
        (SingleTailRadius.physBranch z rho sigma K M.bound.toReal) := by
  have hzu : ∀ u, 0 < z u := fun u => by simpa only [Subsingleton.elim u default] using hz
  have hsig : ∀ i : Fin 1, 0 < sigma i := fun i => by simpa only [Subsingleton.elim i 0] using hs
  have hrho : ∀ i : Fin 1, 0 ≤ rho i := fun i => by simpa only [Subsingleton.elim i 0] using hr.le
  obtain ⟨M,hM⟩ := exists_scalar_hs_maximal_branch z hzu rho sigma hsig hrho K hv
  exact ⟨M,hM,maximal_bound_lt_radius z rho sigma K hz hr hs hv hk M,
    maximal_whole_initial_interval_hasSum z rho sigma K hz hr hs hv hk M,
    (maximal_bound_finite_before_fold z rho sigma K hz hr hs hv hk M).1,
    maximal_endpoint_full_limit z rho sigma K hz hr hs hv hk M,
    maximal_endpoint_explicit_extension z rho sigma K hz hr hs hv hk M⟩

end FMSA.Convergence.SingleTailCanonicalRadius

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_radius_eq_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_radius_eq_fold

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_path_eq_explicit_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_path_eq_explicit_before

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_bound_le_zero_before_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_bound_le_zero_before_radius

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_bound_lt_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_bound_lt_radius

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_bound_finite_before_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_bound_finite_before_fold

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_whole_initial_interval_hasSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_whole_initial_interval_hasSum

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_taylor_sums_to_explicit_until_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_taylor_sums_to_explicit_until_fold

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_explicit_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_explicit_extension

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_full_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_full_limit

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_clusters_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_clusters_unique

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_physical_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_physical_zero

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_longer_root_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_longer_root_prefix

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_taylor_hasSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.maximal_endpoint_taylor_hasSum

/-- info: 'FMSA.Convergence.SingleTailCanonicalRadius.exists_hs_branch_with_strict_radius_and_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailCanonicalRadius.exists_hs_branch_with_strict_radius_and_limit

