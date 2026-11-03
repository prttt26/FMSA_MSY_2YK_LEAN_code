import MSAConvergence.ScalarCanonicalProperness
import MSAConvergence.MixtureHSCanonicity

/-! Regular actual endpoint clusters determine the whole left limit even
when canonicity is lost. No full endpoint limit is supplied as a premise. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.RegularEndpointContinuation
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper.ActualAnalyticBranch FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.ActualCanonicalBranch
open FMSA.Convergence.CanonicalEndpointContinuation FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.MaximalMSAConvergence FMSA.Convergence.ScalarCanonicalProperness
open FMSA.Convergence.MixtureHSCanonicity
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The exact actual amplitude partial used by the analytic IFT. This is
not a replacement residual or an assumed canonical-to-Jacobian bridge. -/
def EndpointRegular (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) : Prop :=
  ((fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (b,a)).comp
    (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible

/-- A genuine two-sided analytic ROOT extension of the left branch germ.
No canonicity of the extension or supplied value p(b) is included. -/
def HasAnalyticLeftRootExtension (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (a : TailMatrix T N × TailMatrix T N) : Prop :=
  ∃ q : ℝ → TailMatrix T N × TailMatrix T N,
    q b = a ∧ AnalyticAt ℝ q b ∧
    (∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (q t).1 (q t).2) ∧
    p =ᶠ[𝓝[<] b] q

/-- At a REGULAR actual cluster root, an entire canonical left prefix
matches the analytic IFT branch. The cluster need NOT be canonical, and
neither endpoint value nor full one-sided limit is assumed. -/
theorem regular_cluster_gives_extension
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hi : EndpointRegular z rho sigma K b a) :
    HasAnalyticLeftRootExtension z rho sigma K p b a ∧ Tendsto p (𝓝[<] b) (𝓝 a) := by
  have hbase := actual_endpoint_cluster_isRoot z rho sigma K p b a u hu ht ha hroot
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hc : ContDiffAt ℝ ω R (b,a) := (residual_analyticAt z rho sigma K (b,a)).contDiffAt
  let q := hc.implicitFunction (by simp) hi
  have hq0 : q b = a := hc.implicitFunction_apply_self (by simp) hi
  have hqa : AnalyticAt ℝ q b := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have hR0 : R (b,a) = 0 := (residual_eq_zero_iff _ _ _ _ _ _ _).mpr hbase
  have hqr : ∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (q t).1 (q t).2 := by
    filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mp (ht.trans hR0)
  have hqt : Tendsto q (𝓝 b) (𝓝 a) := by rw [← hq0]; exact hqa.continuousAt.tendsto
  obtain ⟨epsilon,hepsilon,hball⟩ := Metric.eventually_nhds_iff.mp (hqa.eventually_analyticAt.and hqr)
  let c := max 0 (b-epsilon)
  have hcb : c < b := max_lt hb (by dsimp [c] at *; linarith)
  let S := Ioo c b
  have hS : S ⊆ Ico 0 b := fun t ht => ⟨(le_max_left _ _).trans ht.1.le,ht.2⟩
  have hQ (t : ℝ) (ht : t ∈ S) : AnalyticAt ℝ q t ∧ IsRoot z rho sigma (t • K) (q t).1 (q t).2 := by
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
  have hmatch : Set.EqOn p q S := actual_canonical_roots_eqOn_of_preconnected z hz rho sigma hsigma hrho K hK hv
    p q S (u n) (convex_Ioo c b).isPreconnected hn (hp.mono hS)
    (fun t ht => (hQ t ht).1.continuousAt.continuousWithinAt) heq.symm
    (fun t ht => hroot t (hS ht)) (fun t ht => (hQ t ht).2)
    (fun t ht => hcanon t (hS ht))
  have hlow : ∀ᶠ t : ℝ in 𝓝 b, c < t := Ioi_mem_nhds hcb
  have hleft : p =ᶠ[𝓝[<] b] q := by
    filter_upwards [self_mem_nhdsWithin,hlow.filter_mono nhdsWithin_le_nhds] with t htb hct
    exact hmatch ⟨hct,htb⟩
  exact ⟨⟨q,hq0,hqa,hqr,hleft⟩,(hqt.mono_left nhdsWithin_le_nhds).congr' hleft.symm⟩

/-- Every genuine analytic left-root extension gives the stated one-sided
limit, regardless of the arbitrary original representative at the endpoint. -/
theorem analytic_left_extension_gives_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (a : TailMatrix T N × TailMatrix T N)
    (h : HasAnalyticLeftRootExtension z rho sigma K p b a) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  obtain ⟨q,hq0,hqa,_hqr,hleft⟩ := h
  have hqt : Tendsto q (𝓝 b) (𝓝 a) := by rw [← hq0]; exact hqa.continuousAt.tendsto
  exact (hqt.mono_left nhdsWithin_le_nhds).congr' hleft.symm

omit [Fintype T] in
/-- A true left limit forces EVERY approaching cluster to equal it; no
root, canonicity or endpoint continuity premise is required. -/
theorem endpoint_cluster_unique_of_left_limit
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (a d : TailMatrix T N × TailMatrix T N) (hlim : Tendsto p (𝓝[<] b) (𝓝 a))
    (u : ℕ → ℝ) (hu : ∀ n, u n < b) (ht : Tendsto u atTop (𝓝 b))
    (hd : Tendsto (fun n => p (u n)) atTop (𝓝 d)) : d = a := by
  have hu' : Tendsto u atTop (𝓝[<] b) := tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall hu⟩
  exact tendsto_nhds_unique hd (hlim.comp hu')

/-- A longer continuous actual ROOT prefix, analytic through b and taking
the genuine endpoint value a. Canonicity beyond b is deliberately not asserted. -/
def HasLongerAnalyticRootPrefix (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (a : TailMatrix T N × TailMatrix T N) : Prop :=
  ∃ c : ℝ, b < c ∧ ∃ e : ℝ → TailMatrix T N × TailMatrix T N,
    Set.EqOn e p (Ico 0 b) ∧ e b = a ∧ AnalyticAt ℝ e b ∧ ContinuousOn e (Ico 0 c) ∧
      ∀ t ∈ Ico 0 c, IsRoot z rho sigma (t • K) (e t).1 (e t).2

/-- Glue the genuine analytic left germ to ALL old prefix values. The
result is an actual root branch strictly beyond the canonical endpoint,
with a proved endpoint value, rather than an arbitrary p(b). -/
theorem analytic_left_extension_gives_longer_root_prefix
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (a : TailMatrix T N × TailMatrix T N)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (h : HasAnalyticLeftRootExtension z rho sigma K p b a) :
    HasLongerAnalyticRootPrefix z rho sigma K p b a := by
  obtain ⟨q,hq0,hqa,hqr,hleft⟩ := h
  let e := fun t : ℝ => if t < b then p t else q t
  have heq : e =ᶠ[𝓝 b] q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hleft] with t ht
    dsimp only [e]
    split_ifs with htb
    · exact ht htb
    · rfl
  have hea : AnalyticAt ℝ e b := hqa.congr heq.symm
  have her : ∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (e t).1 (e t).2 := by
    filter_upwards [heq,hqr] with t ht hr
    rwa [ht]
  obtain ⟨delta,hd,hball⟩ := Metric.eventually_nhds_iff.mp (hea.eventually_analyticAt.and her)
  refine ⟨b+delta,by linarith,e,?_,?_,hea,?_,?_⟩
  · intro t ht
    simp only [e,if_pos ht.2]
  · simpa only [e,lt_self_iff_false,ite_false] using hq0
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
    · simpa only [e,if_pos htb] using hroot t ⟨ht.1,htb⟩
    · have hge : b ≤ t := le_of_not_gt htb
      have hn : dist t b < delta := by rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hge)]; linarith [ht.2]
      exact (hball hn).2

/-- If a canonical prefix has NO full finite left limit, EVERY one of its
finite approaching actual amplitude clusters is Jacobian-singular. No
boundedness, endpoint value or noncanonical full-limit premise is supplied. -/
theorem no_full_limit_forces_singular_clusters
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hnolim : ¬∃ d : TailMatrix T N × TailMatrix T N, Tendsto p (𝓝[<] b) (𝓝 d))
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) : ¬EndpointRegular z rho sigma K b a := by
  intro hi
  exact hnolim ⟨a,(regular_cluster_gives_extension z hz rho sigma hsigma hrho K hK hv
    p b hb hp hroot hcanon a u hu ht ha hi).2⟩

/-- A genuine physical Fourier-factor zero excludes full actual canonicity,
even for tracer densities and zero frequency. This uses the actual phase/
Sylvester dictionary, not a root-only OZ implication. -/
theorem physical_zero_not_canonical (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hrho : ∀ i, 0 ≤ rho i) (a : TailMatrix T N × TailMatrix T N)
    (hzero : ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
      (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0) :
    a ∉ canonicalAmplitudes z rho sigma := by
  intro hc
  obtain ⟨k,hk⟩ := hzero
  have hu := FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
    z rho sigma hrho a k (hc (Complex.I*(k : ℂ)) (by simp))
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu) hk

/-- A physical endpoint cluster, refined by its genuine actual Jacobian:
either it is singular, or the WHOLE branch has that unique finite limit
and an analytic actual root continuation strictly beyond the canonical bound. -/
def ResolvedPhysicalEndpoint (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) : Prop :=
  ∃ a : TailMatrix T N × TailMatrix T N, ∃ u : ℕ → ℝ,
    (∀ n, u n ∈ Ico 0 b) ∧ Tendsto u atTop (𝓝 b) ∧
    Tendsto (fun n => p (u n)) atTop (𝓝 a) ∧ IsRoot z rho sigma (b • K) a.1 a.2 ∧
    a ∈ closure (canonicalAmplitudes z rho sigma) ∧
    (∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
      (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0) ∧
    a ∉ canonicalAmplitudes z rho sigma ∧
    (¬EndpointRegular z rho sigma K b a ∨
      (Tendsto p (𝓝[<] b) (𝓝 a) ∧ HasAnalyticLeftRootExtension z rho sigma K p b a ∧
        HasLongerAnalyticRootPrefix z rho sigma K p b a))

/-- The earlier physical CLUSTER certificate now yields a full actual
limit/real-root continuation in its regular case, with no assumed full limit. -/
theorem physical_cluster_resolves
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hc : HasPhysicalEndpointCluster z rho sigma K p b) : ResolvedPhysicalEndpoint z rho sigma K p b := by
  obtain ⟨a,u,hu,ht,ha,hroota,hclose,hzero⟩ := hc
  refine ⟨a,u,hu,ht,ha,hroota,hclose,hzero,physical_zero_not_canonical z rho sigma hrho a hzero,?_⟩
  by_cases hi : EndpointRegular z rho sigma K b a
  · obtain ⟨hext,hlim⟩ := regular_cluster_gives_extension z hz rho sigma hsigma hrho K hK hv
      p b hb hp hroot hcanon a u hu ht ha hi
    exact Or.inr ⟨hlim,hext,analytic_left_extension_gives_longer_root_prefix z rho sigma K p b a hp hroot hext⟩
  · exact Or.inl hi

/-- For arbitrary N a finite CONSTRUCTED maximal endpoint has the refined
alternative: amplitude escape, singular physical cluster, or an analytic real
root continuation with a unique noncanonical physical Fourier-zero endpoint. -/
theorem maximal_finite_boundary_resolution
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound ≠ ⊤) :
    0 < M.bound.toReal ∧
      ((∀ B c : ℝ, c < M.bound.toReal → ∃ t ∈ Ico 0 M.bound.toReal, c < t ∧ B < ‖M.path t‖) ∨
        ResolvedPhysicalEndpoint z rho sigma K M.path M.bound.toReal) := by
  obtain ⟨hb,hcase⟩ := maximal_finite_endpoint_boundary z hz rho sigma hsigma hrho K hK hv seed M hfinite
  refine ⟨hb,?_⟩
  rcases hcase with he | hc
  · exact Or.inl he
  · have hbound : M.bound = ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
    have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
      (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
    exact Or.inr (physical_cluster_resolves z hz rho sigma hsigma hrho K hK hv M.path M.bound.toReal hb
      (by simpa only [hset] using M.analytic.continuousOn)
      (by simpa only [hset] using M.roots) (by simpa only [hset] using M.canonical) hc)

/-- Scalar finite amplitude escape is already excluded internally. Thus
EVERY finite constructed scalar endpoint is a singular physical cluster OR
has a unique full noncanonical limit and longer analytic actual ROOT branch. -/
theorem scalar_maximal_finite_boundary_resolution
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (hv : vacMix rho sigma ≠ 0) (seed : TailMatrix T 1 × TailMatrix T 1)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ResolvedPhysicalEndpoint z rho sigma K M.path M.bound.toReal := by
  have hK : ∀ u i j, K u i j = K u j i := by intro u i j; fin_cases i; fin_cases j; rfl
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  exact physical_cluster_resolves z hz rho sigma hsigma hrho K hK hv M.path M.bound.toReal hb
    (by simpa only [hset] using M.analytic.continuousOn)
    (by simpa only [hset] using M.roots) (by simpa only [hset] using M.canonical)
    (maximal_finite_endpoint_has_physical_cluster z hz rho sigma hsigma hrho K hv seed M hfinite)

/-- General physical HS mixture data construct the maximal initial branch
AND its refined finite-endpoint obstruction; no curve, seed canonicity,
maximality, amplitude bound or endpoint limit is supplied. -/
theorem exists_mixture_hs_branch_with_endpoint_resolution
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : 0 < vacMix rho sigma) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ → 0 < M.bound.toReal ∧
        ((∀ B c : ℝ, c < M.bound.toReal → ∃ t ∈ Ico 0 M.bound.toReal, c < t ∧ B < ‖M.path t‖) ∨
          ResolvedPhysicalEndpoint z rho sigma K M.path M.bound.toReal)) := by
  obtain ⟨M,hM⟩ := exists_mixture_hs_maximal_branch z hz rho sigma hsigma hrho K hK hv
  exact ⟨M,hM,fun hfinite => maximal_finite_boundary_resolution z hz rho sigma hsigma hrho K hK hv.ne' _ M hfinite⟩

/-- At every physical scalar HS state the data-only construction has NO
escape alternative; a regular endpoint cluster supplies the full analytic
real-root continuation even though its physical factor has a Fourier zero. -/
theorem exists_scalar_hs_branch_with_endpoint_resolution
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (hv : 0 < vacMix rho sigma) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ → ResolvedPhysicalEndpoint z rho sigma K M.path M.bound.toReal) := by
  obtain ⟨M,hM⟩ := exists_scalar_hs_maximal_branch z hz rho sigma hsigma hrho K hv
  exact ⟨M,hM,fun hfinite => scalar_maximal_finite_boundary_resolution z hz rho sigma hsigma hrho K hv.ne' _ M hfinite⟩

/-- A continuous finite prefix with a genuine finite left limit is bounded
in the ORIGINAL amplitude norm, even if its supplied endpoint value is arbitrary. -/
theorem left_limit_bounds_entire_prefix
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b)) (a : TailMatrix T N × TailMatrix T N)
    (hlim : Tendsto p (𝓝[<] b) (𝓝 a)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B := by
  have hnear : ∀ᶠ t : ℝ in 𝓝[<] b, ‖p t‖ < ‖a‖+1 :=
    hlim.norm.eventually_lt tendsto_const_nhds (by linarith)
  obtain ⟨epsilon,hepsilon,hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnear)
  let c := max 0 (b-epsilon/2)
  have hcb : c < b := max_lt hb (by linarith)
  have hsub : Icc (0 : ℝ) c ⊆ Ico 0 b := fun t ht => ⟨ht.1,ht.2.trans_lt hcb⟩
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) c)).exists_bound_of_continuousOn (hp.mono hsub)
  refine ⟨max 0 (max C (‖a‖+1)),le_max_left _ _,?_⟩
  intro t ht
  by_cases htc : t ≤ c
  · exact (hC t ⟨ht.1,htc⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hn : dist t b < epsilon := by
      rw [Real.dist_eq,abs_of_neg (sub_neg.mpr ht.2)]
      have hlo : b-epsilon/2 ≤ c := le_max_right _ _
      linarith [lt_of_not_ge htc]
    exact (hball hn ht.2).le.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- ONE regular finite cluster already excludes amplitude escape for the
entire continuous actual canonical prefix, with no bound supplied. -/
theorem regular_cluster_bounds_entire_prefix
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hi : EndpointRegular z rho sigma K b a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B :=
  left_limit_bounds_entire_prefix p b hb hp a
    (regular_cluster_gives_extension z hz rho sigma hsigma hrho K hK hv p b hb hp hroot hcanon a u hu ht ha hi).2

/-- An unbounded actual canonical prefix cannot have ANY regular finite
cluster. This constrains possible matrix escape without excluding it or
assuming the existence of a finite cluster in the escape case. -/
theorem unbounded_prefix_forces_singular_clusters
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hunbounded : ¬∃ B : ℝ, ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) : ¬EndpointRegular z rho sigma K b a := by
  intro hi
  obtain ⟨B,_hB,hbound⟩ := regular_cluster_bounds_entire_prefix z hz rho sigma hsigma hrho K hK hv
    p b hb hp hroot hcanon a u hu ht ha hi
  exact hunbounded ⟨B,hbound⟩

end FMSA.Convergence.RegularEndpointContinuation

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.regular_cluster_gives_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.regular_cluster_gives_extension

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.analytic_left_extension_gives_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.analytic_left_extension_gives_limit

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.endpoint_cluster_unique_of_left_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.endpoint_cluster_unique_of_left_limit

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.analytic_left_extension_gives_longer_root_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.analytic_left_extension_gives_longer_root_prefix

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.no_full_limit_forces_singular_clusters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.no_full_limit_forces_singular_clusters

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.physical_zero_not_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.physical_zero_not_canonical

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.physical_cluster_resolves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.physical_cluster_resolves

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.maximal_finite_boundary_resolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.maximal_finite_boundary_resolution

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.scalar_maximal_finite_boundary_resolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.scalar_maximal_finite_boundary_resolution

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.exists_mixture_hs_branch_with_endpoint_resolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.exists_mixture_hs_branch_with_endpoint_resolution

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.exists_scalar_hs_branch_with_endpoint_resolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.exists_scalar_hs_branch_with_endpoint_resolution

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.left_limit_bounds_entire_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.left_limit_bounds_entire_prefix

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.regular_cluster_bounds_entire_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.regular_cluster_bounds_entire_prefix

/-- info: 'FMSA.Convergence.RegularEndpointContinuation.unbounded_prefix_forces_singular_clusters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularEndpointContinuation.unbounded_prefix_forces_singular_clusters

