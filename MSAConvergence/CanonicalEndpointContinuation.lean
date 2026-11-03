import MSAConvergence.CanonicalFirstLoss

/-! Actual finite endpoint clusters and continuation. No value or continuity
of a given branch at its excluded endpoint is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.CanonicalEndpointContinuation
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.CanonicalFirstLoss
open FMSA.Convergence.ActualCanonicalBranch FMSA.Convergence.ActualTracerAmplitudeRecovery
open FMSA.Paper.ActualAnalyticBranch
variable {N : ℕ} {T : Type*} [Fintype T]

/-- A genuine analytic canonical extension of the LEFT germ at an excluded
finite endpoint. The arbitrary supplied value p(b) is never used. -/
def HasCanonicalLeftExtension (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) : Prop :=
  ∃ q : ℝ → TailMatrix T N × TailMatrix T N,
    AnalyticAt ℝ q b ∧
    (∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (q t).1 (q t).2 ∧
      q t ∈ canonicalAmplitudes z rho sigma) ∧ p =ᶠ[𝓝[<] b] q

/-- A bounded positive-length prefix has a finite approaching cluster in the
original amplitude norm. No endpoint value, continuity or root equation is needed. -/
theorem bounded_prefix_has_cluster
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b B : ℝ) (hb : 0 < b)
    (hB : ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B) :
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ u : ℕ → ℝ,
      ‖a‖ ≤ B ∧ (∀ n, u n ∈ Ico 0 b) ∧ Tendsto u atTop (𝓝 b) ∧
        Tendsto (fun n => p (u n)) atTop (𝓝 a) := by
  have hclose : b ∈ closure (Ico (0 : ℝ) b) := by rw [closure_Ico hb.ne]; exact ⟨hb.le,le_rfl⟩
  obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hclose
  have hcompact : IsCompact (Metric.closedBall (0 : TailMatrix T N × TailMatrix T N) B) := isCompact_closedBall _ _
  obtain ⟨a,ha,v,hv,hpa⟩ := hcompact.tendsto_subseq (fun n => by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hB (u n) (hu n))
  refine ⟨a,u ∘ v,?_,fun n => hu (v n),ht.comp hv.tendsto_atTop,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using ha
  · exact hpa

/-- Polynomial residual continuity makes every actual approaching branch
cluster a ROOT at the endpoint coupling. Endpoint continuity is not assumed. -/
theorem actual_endpoint_cluster_isRoot
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    IsRoot z rho sigma (b • K) a.1 a.2 := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hc : Continuous R := (residual_contDiff z rho sigma K).continuous
  have hz : IsClosed {x | R x = 0} := isClosed_eq hc continuous_const
  have hR : R (b,a) = 0 := hz.mem_of_tendsto (ht.prodMk_nhds ha)
    (Eventually.of_forall (fun n => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hroot (u n) (hu n))))
  exact (residual_eq_zero_iff _ _ _ _ _ _ _).mp hR

/-- Every approaching canonical cluster lies in the closure of the actual
canonical amplitude set, without assuming a full branch limit. -/
theorem actual_endpoint_cluster_mem_closure
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b)
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    a ∈ closure (canonicalAmplitudes z rho sigma) :=
  mem_closure_of_tendsto ha (Eventually.of_forall (fun n => hcanon (u n) (hu n)))

/-- A canonical actual cluster root forces a continuous actual branch to
match its analytic IFT root on the ENTIRE left germ, not just a subsequence.
Consequently the genuine one-sided limit and canonical extension exist. -/
theorem canonical_cluster_gives_extension
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hcanon : a ∈ canonicalAmplitudes z rho sigma) :
    HasCanonicalLeftExtension z rho sigma K p b ∧ Tendsto p (𝓝[<] b) (𝓝 a) := by
  have hbase := actual_endpoint_cluster_isRoot z rho sigma K p b a u hu ht ha hroot
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hc : ContDiffAt ℝ ω R (b,a) := (residual_analyticAt z rho sigma K (b,a)).contDiffAt
  have hi := actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK b a hv hbase hcanon
  let q := hc.implicitFunction (by simp) hi
  have hq0 : q b = a := hc.implicitFunction_apply_self (by simp) hi
  have hqa : AnalyticAt ℝ q b := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have hR0 : R (b,a) = 0 := (residual_eq_zero_iff _ _ _ _ _ _ _).mpr hbase
  have hqr : ∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (q t).1 (q t).2 := by
    filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mp (ht.trans hR0)
  have hqt : Tendsto q (𝓝 b) (𝓝 a) := by rw [← hq0]; exact hqa.continuousAt.tendsto
  have hqc : ∀ᶠ t in 𝓝 b, q t ∈ canonicalAmplitudes z rho sigma :=
    hqt.eventually (actual_canonicity_eventually z hz rho sigma (fun i => (hsigma i).le) a hcanon)
  have hnear := hqa.eventually_analyticAt.and (hqr.and hqc)
  obtain ⟨epsilon,hepsilon,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let c := max 0 (b-epsilon)
  have hcb : c < b := max_lt hb (by dsimp [c] at *; linarith)
  let S := Ioo c b
  have hS : S ⊆ Ico 0 b := fun t ht => ⟨(le_max_left _ _).trans ht.1.le,ht.2⟩
  have hQ (t : ℝ) (ht : t ∈ S) : AnalyticAt ℝ q t ∧
      IsRoot z rho sigma (t • K) (q t).1 (q t).2 ∧ q t ∈ canonicalAmplitudes z rho sigma := by
    apply hball
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr ht.2)]
    have hlo : b-epsilon ≤ c := le_max_right _ _
    linarith [ht.1]
  have hmeet : ∀ᶠ n in atTop, q (u n) = p (u n) := by
    have hlocal := (ht.prodMk_nhds ha).eventually (hc.eventually_apply_eq_iff_implicitFunction (by simp) hi)
    filter_upwards [hlocal] with n hn
    exact hn.mp (((residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hroot (u n) (hu n))).trans hR0.symm)
  have hinside : ∀ᶠ n in atTop, u n ∈ S := by
    filter_upwards [ht.eventually (Ioi_mem_nhds hcb)] with n hn
    exact ⟨hn,(hu n).2⟩
  obtain ⟨n,hn,heq⟩ := (hinside.and hmeet).exists
  have hmatch : Set.EqOn q p S := actual_canonical_roots_eqOn_of_preconnected z hz rho sigma hsigma hrho K hK hv
    q p S (u n) (convex_Ioo c b).isPreconnected hn
    (fun t ht => (hQ t ht).1.continuousAt.continuousWithinAt) (hp.mono hS) heq
    (fun t ht => (hQ t ht).2.1) (fun t ht => hroot t (hS ht)) (fun t ht => (hQ t ht).2.2)
  have hlow : ∀ᶠ t : ℝ in 𝓝 b, c < t := Ioi_mem_nhds hcb
  have hleft : p =ᶠ[𝓝[<] b] q := by
    filter_upwards [self_mem_nhdsWithin,hlow.filter_mono nhdsWithin_le_nhds] with t htb hct
    exact (hmatch ⟨hct,htb⟩).symm
  exact ⟨⟨q,hqa,hqr.and hqc,hleft⟩,(hqt.mono_left nhdsWithin_le_nhds).congr' hleft.symm⟩


/-- An actual continuous canonical prefix extended to a strictly longer initial
interval, with ALL previous branch values retained. -/
def HasLongerCanonicalPrefix (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) : Prop :=
  ∃ c : ℝ, b < c ∧ ∃ e : ℝ → TailMatrix T N × TailMatrix T N,
    Set.EqOn e p (Ico 0 b) ∧ ContinuousOn e (Ico 0 c) ∧
    ∀ t ∈ Ico 0 c, IsRoot z rho sigma (t • K) (e t).1 (e t).2 ∧
      e t ∈ canonicalAmplitudes z rho sigma

/-- A genuine analytic canonical left extension glues to the WHOLE original
prefix, giving an actual longer branch. No original value at b is assumed. -/
theorem left_extension_gives_longer_prefix
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (he : HasCanonicalLeftExtension z rho sigma K p b) :
    HasLongerCanonicalPrefix z rho sigma K p b := by
  obtain ⟨q,hqa,hqr,hleft⟩ := he
  let e := fun t : ℝ => if t < b then p t else q t
  have heq : e =ᶠ[𝓝 b] q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hleft] with t ht
    dsimp only [e]
    split_ifs with htb
    · exact ht htb
    · rfl
  have hea : AnalyticAt ℝ e b := hqa.congr heq.symm
  have her : ∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (e t).1 (e t).2 ∧
      e t ∈ canonicalAmplitudes z rho sigma := by
    filter_upwards [heq,hqr] with t ht hr
    rwa [ht]
  obtain ⟨delta,hd,hball⟩ := Metric.eventually_nhds_iff.mp (hea.eventually_analyticAt.and her)
  refine ⟨b+delta,by linarith,e,?_,?_,?_⟩
  · intro t ht
    simp only [e,if_pos ht.2]
  · intro t ht
    by_cases htb : t < b
    · have hlow : ∀ᶠ x : ℝ in 𝓝 t, x < b := Iio_mem_nhds htb
      have hold : Ico (0 : ℝ) b ∈ 𝓝[Ico 0 (b+delta)] t := by
        filter_upwards [self_mem_nhdsWithin,hlow.filter_mono nhdsWithin_le_nhds] with x hx hxb
        exact ⟨hx.1,hxb⟩
      have hep : e =ᶠ[𝓝 t] p := by
        filter_upwards [hlow] with x hx
        exact if_pos hx
      exact ((hp t ⟨ht.1,htb⟩).mono_of_mem_nhdsWithin hold).congr_of_eventuallyEq
        (hep.filter_mono nhdsWithin_le_nhds) (if_pos htb)
    · have hge : b ≤ t := le_of_not_gt htb
      have hn : dist t b < delta := by rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hge)]; linarith [ht.2]
      exact (hball hn).1.continuousAt.continuousWithinAt
  · intro t ht
    by_cases htb : t < b
    · simpa only [e,if_pos htb] using And.intro (hroot t ⟨ht.1,htb⟩) (hcanon t ⟨ht.1,htb⟩)
    · have hge : b ≤ t := le_of_not_gt htb
      have hn : dist t b < delta := by rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hge)]; linarith [ht.2]
      exact (hball hn).2

/-- Bounded canonical prefixes have the correct endpoint alternative:
continuation of the whole branch, or a finite ACTUAL cluster root with an
honest renewal determinant zero on the Fourier axis. No endpoint limit is given. -/
theorem bounded_prefix_continuation_or_axis_cluster
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b B : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hB : ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B) :
    HasLongerCanonicalPrefix z rho sigma K p b ∨
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ u : ℕ → ℝ,
      ‖a‖ ≤ B ∧ (∀ n, u n ∈ Ico 0 b) ∧ Tendsto u atTop (𝓝 b) ∧
      Tendsto (fun n => p (u n)) atTop (𝓝 a) ∧ IsRoot z rho sigma (b • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧
      ∃ k : ℝ, renewalDet z rho sigma a (Complex.I*k) = 0 := by
  obtain ⟨a,u,ha,hu,ht,hpu⟩ := bounded_prefix_has_cluster p b B hb hB
  have hRa := actual_endpoint_cluster_isRoot z rho sigma K p b a u hu ht hpu hroot
  have hCa := actual_endpoint_cluster_mem_closure z rho sigma p b a u hu hpu hcanon
  by_cases hc : a ∈ canonicalAmplitudes z rho sigma
  · exact Or.inl (left_extension_gives_longer_prefix z rho sigma K p b hp hroot hcanon
      (canonical_cluster_gives_extension z hz rho sigma hsigma hrho K hK hv p b hb hp hroot a u hu ht hpu hc).1)
  · exact Or.inr ⟨a,u,ha,hu,ht,hpu,hRa,hCa,
      noncanonical_closure_exists_real_frequency z hz rho sigma (fun i => (hsigma i).le) a hCa hc⟩

/-- The cluster obstruction is the actual physical Fourier-factor determinant,
including k=0 and arbitrary zero-density species. -/
theorem bounded_prefix_continuation_or_physical_cluster
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b B : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hB : ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B) :
    HasLongerCanonicalPrefix z rho sigma K p b ∨
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ u : ℕ → ℝ,
      ‖a‖ ≤ B ∧ (∀ n, u n ∈ Ico 0 b) ∧ Tendsto u atTop (𝓝 b) ∧
      Tendsto (fun n => p (u n)) atTop (𝓝 a) ∧ IsRoot z rho sigma (b • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧
      ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0 := by
  rcases bounded_prefix_continuation_or_axis_cluster z hz rho sigma hsigma hrho K hK hv p b B hb hp hroot hcanon hB with he | hc
  · exact Or.inl he
  · obtain ⟨a,u,ha,hu,ht,hpu,hRa,hCa,k,hk⟩ := hc
    refine Or.inr ⟨a,u,ha,hu,ht,hpu,hRa,hCa,k,?_⟩
    by_contra hn
    have hF := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
    have hA := (kernel_unit_iff_physical_factor_unit z rho sigma hrho a k).mpr hF
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)) hk

/-- For a bounded prefix maximal among actual continuous canonical initial
branches, a finite physical Fourier-zero cluster root exists at the endpoint. -/
theorem bounded_nonextendable_prefix_has_physical_cluster
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b B : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hB : ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B)
    (hmax : ¬HasLongerCanonicalPrefix z rho sigma K p b) :
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ u : ℕ → ℝ,
      ‖a‖ ≤ B ∧ (∀ n, u n ∈ Ico 0 b) ∧ Tendsto u atTop (𝓝 b) ∧
      Tendsto (fun n => p (u n)) atTop (𝓝 a) ∧ IsRoot z rho sigma (b • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧
      ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0 :=
  (bounded_prefix_continuation_or_physical_cluster z hz rho sigma hsigma hrho K hK hv p b B hb hp hroot hcanon hB).resolve_left hmax


/-- An actual finite boundary cluster of the given branch with a genuine
physical Fourier determinant zero. This does not assert a unique full limit. -/
def HasPhysicalEndpointCluster (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) : Prop :=
  ∃ a : TailMatrix T N × TailMatrix T N, ∃ u : ℕ → ℝ,
    (∀ n, u n ∈ Ico 0 b) ∧ Tendsto u atTop (𝓝 b) ∧
    Tendsto (fun n => p (u n)) atTop (𝓝 a) ∧ IsRoot z rho sigma (b • K) a.1 a.2 ∧
    a ∈ closure (canonicalAmplitudes z rho sigma) ∧
    ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
      (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0

/-- If a continuous finite prefix is unbounded, arbitrarily large amplitudes
occur arbitrarily close to its EXCLUDED endpoint. No full norm limit is asserted. -/
theorem unbounded_prefix_escapes_near_endpoint
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hp : ContinuousOn p (Ico 0 b)) (hunbounded : ¬∃ B : ℝ, ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B) :
    ∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  intro B c hcb
  by_contra hn
  apply hunbounded
  by_cases hc : 0 ≤ c
  · have hsub : Icc (0 : ℝ) c ⊆ Ico 0 b := fun t ht => ⟨ht.1,ht.2.trans_lt hcb⟩
    obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) c)).exists_bound_of_continuousOn (hp.mono hsub)
    refine ⟨max M B,?_⟩
    intro t ht
    by_cases htc : t ≤ c
    · exact (hM t ⟨ht.1,htc⟩).trans (le_max_left _ _)
    · exact (le_of_not_gt (fun hnorm => hn ⟨t,ht,lt_of_not_ge htc,hnorm⟩)).trans (le_max_right _ _)
  · refine ⟨B,?_⟩
    intro t ht
    exact le_of_not_gt (fun hnorm => hn ⟨t,ht,lt_of_lt_of_le (lt_of_not_ge hc) ht.1,hnorm⟩)

/-- Every finite positive-length actual canonical prefix has the complete
correct boundary alternatives: longer canonical continuation, arbitrarily large
amplitudes arbitrarily near the endpoint, or an actual Fourier-zero cluster root. -/
theorem finite_prefix_boundary_alternatives
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    HasLongerCanonicalPrefix z rho sigma K p b ∨
    (∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖) ∨
    HasPhysicalEndpointCluster z rho sigma K p b := by
  by_cases hbounded : ∃ B : ℝ, ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B
  · obtain ⟨B,hB⟩ := hbounded
    rcases bounded_prefix_continuation_or_physical_cluster z hz rho sigma hsigma hrho K hK hv p b B hb hp hroot hcanon hB with he | hc
    · exact Or.inl he
    · obtain ⟨a,u,_ha,hu,ht,hpu,hRa,hCa,hk⟩ := hc
      exact Or.inr (Or.inr ⟨a,u,hu,ht,hpu,hRa,hCa,hk⟩)
  · exact Or.inr (Or.inl (unbounded_prefix_escapes_near_endpoint p b hp hbounded))

/-- A finite maximal actual canonical prefix can end only through amplitude
escape (in the stated subsequential sense) or an actual Fourier-zero cluster.
Neither boundedness nor a finite continuous endpoint is silently assumed. -/
theorem finite_nonextendable_prefix_boundary_obstruction
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hmax : ¬HasLongerCanonicalPrefix z rho sigma K p b) :
    (∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖) ∨
    HasPhysicalEndpointCluster z rho sigma K p b :=
  (finite_prefix_boundary_alternatives z hz rho sigma hsigma hrho K hK hv p b hb hp hroot hcanon).resolve_left hmax

/-- A bounded canonical prefix must continue if every possible bounded
endpoint cluster ROOT has an invertible physical factor at EVERY real frequency. -/
theorem bounded_prefix_continues_of_endpoint_axis_units
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b B : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hB : ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B)
    (hF : ∀ a : TailMatrix T N × TailMatrix T N, ‖a‖ ≤ B →
      IsRoot z rho sigma (b • K) a.1 a.2 → a ∈ closure (canonicalAmplitudes z rho sigma) →
      ∀ k : ℝ, IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k)) :
    HasLongerCanonicalPrefix z rho sigma K p b := by
  rcases bounded_prefix_continuation_or_physical_cluster z hz rho sigma hsigma hrho K hK hv p b B hb hp hroot hcanon hB with he | hc
  · exact he
  · obtain ⟨a,_u,ha,_hu,_ht,_hpu,hRa,hCa,k,hk⟩ := hc
    exact False.elim ((isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hF a ha hRa hCa k))) hk)

end FMSA.Convergence.CanonicalEndpointContinuation

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_has_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_has_cluster

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.actual_endpoint_cluster_isRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.actual_endpoint_cluster_isRoot

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.actual_endpoint_cluster_mem_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.actual_endpoint_cluster_mem_closure

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.canonical_cluster_gives_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.canonical_cluster_gives_extension

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.left_extension_gives_longer_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.left_extension_gives_longer_prefix

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_continuation_or_axis_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_continuation_or_axis_cluster

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_continuation_or_physical_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_continuation_or_physical_cluster

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.bounded_nonextendable_prefix_has_physical_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.bounded_nonextendable_prefix_has_physical_cluster

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.unbounded_prefix_escapes_near_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.unbounded_prefix_escapes_near_endpoint

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.finite_prefix_boundary_alternatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.finite_prefix_boundary_alternatives

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.finite_nonextendable_prefix_boundary_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.finite_nonextendable_prefix_boundary_obstruction

/-- info: 'FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_continues_of_endpoint_axis_units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalEndpointContinuation.bounded_prefix_continues_of_endpoint_axis_units
