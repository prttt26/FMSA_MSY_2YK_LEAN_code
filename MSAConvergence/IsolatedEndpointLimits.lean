import MSAConvergence.RegularEndpointContinuation

/-! Isolated endpoint roots determine full one-sided branch limits, including
singular roots. Failure of a finite limit forces nonisolated actual endpoint
roots through compact spherical crossing sequences, without global boundedness. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.IsolatedEndpointLimits

section Metric
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

omit [ProperSpace E] in
/-- A finite cluster and frequent exits from its epsilon-ball force exact
sphere crossings arbitrarily near the excluded endpoint. The path need not
be bounded, regular or differentiable. -/
theorem cluster_and_exits_give_crossings
    (p : ℝ → E) (b : ℝ) (hb : 0 < b) (hp : ContinuousOn p (Ico 0 b))
    (a : E) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Ico 0 b)
    (ht : Tendsto u atTop (𝓝 b)) (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (epsilon : ℝ) (hexit : ∃ᶠ t in 𝓝[<] b, epsilon ≤ dist (p t) a)
    (r : ℝ) (hr : 0 < r) (hre : r < epsilon) (c : ℝ) (hcb : c < b) :
    ∃ t ∈ Ico 0 b, c < t ∧ dist (p t) a = r := by
  let d := max 0 c
  have hdb : d < b := max_lt hb hcb
  have hnear : ∀ᶠ n in atTop, dist (p (u n)) a < r := by
    have hd : Tendsto (fun n => dist (p (u n)) a) atTop (𝓝 0) := by
      simpa only [dist_self] using ha.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
    exact hd.eventually_lt tendsto_const_nhds hr
  have hulow : ∀ᶠ n in atTop, d < u n := ht.eventually (Ioi_mem_nhds hdb)
  obtain ⟨n,hn,hun⟩ := (hnear.and hulow).exists
  have hlow : ∀ᶠ t : ℝ in 𝓝[<] b, d < t :=
    (show ∀ᶠ t : ℝ in 𝓝 b, d < t from Ioi_mem_nhds hdb).filter_mono nhdsWithin_le_nhds
  obtain ⟨v,hvexit,hvlo,hvhi⟩ := (hexit.and_eventually (hlow.and self_mem_nhdsWithin)).exists
  let S := Ioo d b
  have hS : S ⊆ Ico 0 b := fun t ht => ⟨(le_max_left _ _).trans ht.1.le,ht.2⟩
  have hc : ContinuousOn (fun t => dist (p t) a) S := continuous_dist.comp_continuousOn ((hp.mono hS).prodMk continuousOn_const)
  obtain ⟨t,ht,htr⟩ := (convex_Ioo d b).isPreconnected.intermediate_value₂
    (show u n ∈ S from ⟨hun,(hu n).2⟩) (show v ∈ S from ⟨hvlo,hvhi⟩)
    hc continuousOn_const hn.le (hre.le.trans hvexit)
  exact ⟨t,hS ht,(le_max_right _ _).trans_lt ht.1,htr⟩

/-- Exact crossings arbitrarily near b provide an approaching sequence on
the compact sphere. A subsequence has a finite cluster on that SAME sphere.
No global bound on the original path is used. -/
theorem spherical_crossings_have_cluster
    (p : ℝ → E) (b : ℝ) (a : E) (r : ℝ)
    (hcross : ∀ c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ dist (p t) a = r) :
    ∃ d : E, ∃ v : ℕ → ℝ, dist d a = r ∧
      (∀ n, v n ∈ Ico 0 b) ∧ Tendsto v atTop (𝓝 b) ∧
      Tendsto (fun n => p (v n)) atTop (𝓝 d) := by
  classical
  have hseq (n : ℕ) : ∃ t ∈ Ico 0 b, b-1/(n+1 : ℝ) < t ∧ dist (p t) a = r :=
    hcross _ (sub_lt_self b (by positivity))
  choose v hv hlo hdist using hseq
  have hlow : Tendsto (fun n : ℕ => b-1/(n+1 : ℝ)) atTop (𝓝 b) := by
    simpa only [sub_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0))
  have ht : Tendsto v atTop (𝓝 b) := tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlow tendsto_const_nhds (fun n => (hlo n).le) (fun n => (hv n).2.le)
  obtain ⟨d,hd,w,hw,hpw⟩ := (isCompact_sphere a r).tendsto_subseq
    (fun n => show p (v n) ∈ Metric.sphere a r from Metric.mem_sphere.mpr (hdist n))
  exact ⟨d,v ∘ w,Metric.mem_sphere.mp hd,fun n => hv (w n),ht.comp hw.tendsto_atTop,hpw⟩

/-- If a continuous prefix has a finite cluster a but does NOT tend to a,
its endpoint cluster set meets EVERY sufficiently small sphere around a.
Thus a failure of a full limit cannot be explained by isolated singular roots. -/
theorem nonlimit_has_spherical_clusters
    (p : ℝ → E) (b : ℝ) (hb : 0 < b) (hp : ContinuousOn p (Ico 0 b))
    (a : E) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Ico 0 b)
    (ht : Tendsto u atTop (𝓝 b)) (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hn : ¬Tendsto p (𝓝[<] b) (𝓝 a)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ r : ℝ, 0 < r → r < epsilon →
      ∃ d : E, ∃ v : ℕ → ℝ, dist d a = r ∧
        (∀ n, v n ∈ Ico 0 b) ∧ Tendsto v atTop (𝓝 b) ∧
        Tendsto (fun n => p (v n)) atTop (𝓝 d) := by
  have he : ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ᶠ t in 𝓝[<] b, epsilon ≤ dist (p t) a := by
    rw [Metric.tendsto_nhds] at hn
    push Not at hn
    exact hn
  obtain ⟨epsilon,hepsilon,hex⟩ := he
  refine ⟨epsilon,hepsilon,fun r hr hre => spherical_crossings_have_cluster p b a r ?_⟩
  exact fun c hcb => cluster_and_exits_give_crossings p b hb hp a u hu ht ha epsilon hex r hr hre c hcb

/-- An ISOLATED endpoint root forces a full finite left limit at any one
approaching cluster, even when its Jacobian is singular. The original branch
need not be bounded or regular, and no endpoint value/limit is supplied. -/
theorem isolated_fiber_cluster_has_limit
    (R : ℝ × E → E) (hR : Continuous R)
    (p : ℝ → E) (b : ℝ) (hb : 0 < b) (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, R (t,p t) = 0)
    (a : E) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Ico 0 b)
    (ht : Tendsto u atTop (𝓝 b)) (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hiso : ∃ delta : ℝ, 0 < delta ∧ ∀ d : E, R (b,d) = 0 → dist d a < delta → d = a) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  by_contra hn
  obtain ⟨epsilon,hepsilon,hcl⟩ := nonlimit_has_spherical_clusters p b hb hp a u hu ht ha hn
  obtain ⟨delta,hdelta,hiso⟩ := hiso
  let r := min epsilon delta/2
  have hmin : 0 < min epsilon delta := lt_min hepsilon hdelta
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < epsilon := by dsimp [r]; linarith [min_le_left epsilon delta]
  have hrd : r < delta := by dsimp [r]; linarith [min_le_right epsilon delta]
  obtain ⟨d,v,hd,hv,hvt,hpd⟩ := hcl r hr hre
  have hRd : R (b,d) = 0 := (isClosed_eq hR continuous_const).mem_of_tendsto
    (hvt.prodMk_nhds hpd) (Eventually.of_forall (fun n => hroot (v n) (hv n)))
  have heq : d = a := hiso d hRd (by rw [hd]; exact hrd)
  rw [heq,dist_self] at hd
  linarith

omit [ProperSpace E] in
/-- Finite sets have isolated points in the ambient metric space. The
point a need not be regular or even belong to the set. -/
theorem finite_set_isolated (S : Set E) (hfinite : S.Finite) (a : E) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ d : E, d ∈ S → dist d a < delta → d = a := by
  have hc : IsClosed (S\{a}) := hfinite.sdiff.isClosed
  have ha : a ∈ (S\{a})ᶜ := by simp
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp (hc.isOpen_compl.mem_nhds ha)
  refine ⟨delta,hdelta,?_⟩
  intro d hd hdist
  by_contra hne
  exact (hball (show d ∈ Metric.ball a delta from hdist)) ⟨hd,by simpa using hne⟩

omit [ProperSpace E] in
/-- Every point of a FINITE endpoint fiber is isolated. This uses only
finiteness and the metric topology, not a Jacobian or square-free condition. -/
theorem finite_fiber_isolated (R : ℝ × E → E) (b : ℝ)
    (hfinite : {d : E | R (b,d) = 0}.Finite) (a : E) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ d : E, R (b,d) = 0 → dist d a < delta → d = a :=
  finite_set_isolated _ hfinite a

/-- Finite endpoint fibers imply a full limit at ANY approaching finite
cluster, including multiple/degenerate singular roots. No global path bound
is required once a cluster sequence is supplied. -/
theorem finite_fiber_cluster_has_limit
    (R : ℝ × E → E) (hR : Continuous R)
    (p : ℝ → E) (b : ℝ) (hb : 0 < b) (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, R (t,p t) = 0)
    (a : E) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Ico 0 b)
    (ht : Tendsto u atTop (𝓝 b)) (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hfinite : {d : E | R (b,d) = 0}.Finite) :
    Tendsto p (𝓝[<] b) (𝓝 a) :=
  isolated_fiber_cluster_has_limit R hR p b hb hp hroot a u hu ht ha (finite_fiber_isolated R b hfinite a)

end Metric
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CanonicalEndpointContinuation FMSA.Convergence.RegularEndpointContinuation
open FMSA.Convergence.MaximalCanonicalBranch FMSA.Convergence.MaximalMSAConvergence
open FMSA.Convergence.ScalarCanonicalProperness FMSA.Convergence.CanonicalNeighborhood
open FMSA.Paper.StableIntervalRadius
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual BH polynomial fiber inherits the spherical obstruction:
if a true finite cluster is NOT the full left limit, actual endpoint roots
occur on EVERY sufficiently small sphere around it. No canonical, density-
sign, amplitude-bound, or Jacobian premise is required. -/
theorem actual_nonlimit_has_spherical_roots
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) (hn : ¬Tendsto p (𝓝[<] b) (𝓝 a)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ r : ℝ, 0 < r → r < epsilon →
      ∃ d : TailMatrix T N × TailMatrix T N, dist d a = r ∧ IsRoot z rho sigma (b • K) d.1 d.2 ∧
        ∃ v : ℕ → ℝ, (∀ n, v n ∈ Ico 0 b) ∧ Tendsto v atTop (𝓝 b) ∧
          Tendsto (fun n => p (v n)) atTop (𝓝 d) := by
  obtain ⟨epsilon,he,hcl⟩ := nonlimit_has_spherical_clusters p b hb hp a u hu ht ha hn
  refine ⟨epsilon,he,?_⟩
  intro r hr hre
  obtain ⟨d,v,hd,hv,hvt,hpd⟩ := hcl r hr hre
  exact ⟨d,hd,actual_endpoint_cluster_isRoot z rho sigma K p b d v hv hvt hpd hroot,v,hv,hvt,hpd⟩

/-- Failure of the full actual limit forces NONISOLATION in the endpoint
root fiber, not merely Jacobian singularity. This covers arbitrary finite
mixtures/tails and does not assume boundedness of the original path. -/
theorem actual_nonlimit_forces_nonisolated_roots
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) (hn : ¬Tendsto p (𝓝[<] b) (𝓝 a)) :
    ∀ delta : ℝ, 0 < delta → ∃ d : TailMatrix T N × TailMatrix T N,
      IsRoot z rho sigma (b • K) d.1 d.2 ∧ d ≠ a ∧ dist d a < delta := by
  obtain ⟨epsilon,he,hcl⟩ := actual_nonlimit_has_spherical_roots z rho sigma K p b hb hp hroot a u hu ht ha hn
  intro delta hd
  let r := min epsilon delta/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < epsilon := by dsimp [r]; linarith [min_le_left epsilon delta]
  have hrd : r < delta := by dsimp [r]; linarith [min_le_right epsilon delta]
  obtain ⟨d,hdist,hrootd,_hseq⟩ := hcl r hr hre
  refine ⟨d,hrootd,?_,by rw [hdist]; exact hrd⟩
  intro heq
  rw [heq,dist_self] at hdist
  linarith

/-- An isolated ACTUAL BH endpoint root gives the whole left limit without
any partial-invertibility or canonicity premise. Singular isolated roots are
included. Isolation is explicit and is not inferred from algebraicity alone. -/
theorem actual_isolated_cluster_has_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hiso : ∃ delta : ℝ, 0 < delta ∧ ∀ d : TailMatrix T N × TailMatrix T N,
      IsRoot z rho sigma (b • K) d.1 d.2 → dist d a < delta → d = a) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  apply isolated_fiber_cluster_has_limit (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K)
    (residual_contDiff z rho sigma K).continuous p b hb hp
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hroot t ht)) a u hu ht ha
  obtain ⟨delta,hd,hiso⟩ := hiso
  exact ⟨delta,hd,fun d hR hdist => hiso d ((residual_eq_zero_iff _ _ _ _ _ _ _).mp hR) hdist⟩

/-- A finite ACTUAL endpoint root fiber discharges isolation, including
all degenerate/multiple roots. Finiteness is an explicit certificate target,
not a mathematical axiom or a claim about all BH fibers. -/
theorem actual_finite_fiber_cluster_has_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hfinite : {d : TailMatrix T N × TailMatrix T N | IsRoot z rho sigma (b • K) d.1 d.2}.Finite) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have heq : {d : TailMatrix T N × TailMatrix T N | R (b,d) = 0} =
      {d : TailMatrix T N × TailMatrix T N | IsRoot z rho sigma (b • K) d.1 d.2} := by
    ext d
    exact residual_eq_zero_iff z rho sigma K d.1 d.2 b
  have hfin : {d : TailMatrix T N × TailMatrix T N | R (b,d) = 0}.Finite := by
    rw [heq]
    exact hfinite
  exact finite_fiber_cluster_has_limit R (residual_contDiff z rho sigma K).continuous p b hb hp
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hroot t ht)) a u hu ht ha hfin

/-- Finite actual endpoint fibers turn a supplied finite prefix bound into
an ACTUAL root limit, with no endpoint value/continuity or Jacobian premise. -/
theorem bounded_actual_prefix_finite_fiber_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b B : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hB : ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B)
    (hfinite : {d : TailMatrix T N × TailMatrix T N | IsRoot z rho sigma (b • K) d.1 d.2}.Finite) :
    ∃ a : TailMatrix T N × TailMatrix T N, ‖a‖ ≤ B ∧ IsRoot z rho sigma (b • K) a.1 a.2 ∧
      Tendsto p (𝓝[<] b) (𝓝 a) := by
  obtain ⟨a,u,ha,hu,ht,hpa⟩ := bounded_prefix_has_cluster p b B hb hB
  exact ⟨a,ha,actual_endpoint_cluster_isRoot z rho sigma K p b a u hu ht hpa hroot,
    actual_finite_fiber_cluster_has_limit z rho sigma K p b hb hp hroot a u hu ht hpa hfinite⟩

/-- An isolated actual cluster also bounds the ENTIRE original-norm prefix,
without a supplied bound, even if it is singular/noncanonical. -/
theorem actual_isolated_cluster_bounds_prefix
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hiso : ∃ delta : ℝ, 0 < delta ∧ ∀ d : TailMatrix T N × TailMatrix T N,
      IsRoot z rho sigma (b • K) d.1 d.2 → dist d a < delta → d = a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B :=
  left_limit_bounds_entire_prefix p b hb hp a
    (actual_isolated_cluster_has_limit z rho sigma K p b hb hp hroot a u hu ht ha hiso)

/-- For a canonical prefix, ALL spherical crossing clusters are in actual
canonical closure. Only the physically relevant endpoint fiber needs to be
isolated; unrelated algebraic root components need not be finite. -/
theorem canonical_nonlimit_has_spherical_roots
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) (hn : ¬Tendsto p (𝓝[<] b) (𝓝 a)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ r : ℝ, 0 < r → r < epsilon →
      ∃ d : TailMatrix T N × TailMatrix T N, dist d a = r ∧ IsRoot z rho sigma (b • K) d.1 d.2 ∧
        d ∈ closure (canonicalAmplitudes z rho sigma) ∧
        ∃ v : ℕ → ℝ, (∀ n, v n ∈ Ico 0 b) ∧ Tendsto v atTop (𝓝 b) ∧
          Tendsto (fun n => p (v n)) atTop (𝓝 d) := by
  obtain ⟨epsilon,he,hcl⟩ := actual_nonlimit_has_spherical_roots z rho sigma K p b hb hp hroot a u hu ht ha hn
  refine ⟨epsilon,he,?_⟩
  intro r hr hre
  obtain ⟨d,hd,hrootd,v,hv,hvt,hpd⟩ := hcl r hr hre
  exact ⟨d,hd,hrootd,actual_endpoint_cluster_mem_closure z rho sigma p b d v hv hpd hcanon,v,hv,hvt,hpd⟩

/-- Isolation ONLY among actual endpoint roots in canonical closure suffices
for the full limit, including singular points. No finite fiber, global bound,
Jacobian or ordinary-fold hypothesis is supplied. -/
theorem canonical_isolated_cluster_has_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hiso : ∃ delta : ℝ, 0 < delta ∧ ∀ d : TailMatrix T N × TailMatrix T N,
      IsRoot z rho sigma (b • K) d.1 d.2 → d ∈ closure (canonicalAmplitudes z rho sigma) → dist d a < delta → d = a) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  by_contra hn
  obtain ⟨epsilon,he,hcl⟩ := canonical_nonlimit_has_spherical_roots z rho sigma K p b hb hp hroot hcanon a u hu ht ha hn
  obtain ⟨delta,hd,hiso⟩ := hiso
  let r := min epsilon delta/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < epsilon := by dsimp [r]; linarith [min_le_left epsilon delta]
  have hrd : r < delta := by dsimp [r]; linarith [min_le_right epsilon delta]
  obtain ⟨d,hdist,hrootd,hclose,_hseq⟩ := hcl r hr hre
  have heq := hiso d hrootd hclose (by rw [hdist]; exact hrd)
  rw [heq,dist_self] at hdist
  linarith

/-- Finiteness of the actual endpoint roots IN CANONICAL CLOSURE discharges
isolation. The whole algebraic fiber may contain other noncanonical components. -/
theorem canonical_finite_fiber_cluster_has_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hfinite : {d : TailMatrix T N × TailMatrix T N |
      IsRoot z rho sigma (b • K) d.1 d.2 ∧ d ∈ closure (canonicalAmplitudes z rho sigma)}.Finite) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  obtain ⟨delta,hd,hiso⟩ := finite_set_isolated _ hfinite a
  exact canonical_isolated_cluster_has_limit z rho sigma K p b hb hp hroot hcanon a u hu ht ha
    ⟨delta,hd,fun d hrootd hclose hdist => hiso d ⟨hrootd,hclose⟩ hdist⟩

/-- At a finite constructed scalar endpoint, an explicit finite-canonical-
fiber certificate gives the FULL actual physical Fourier-zero limiting root.
Escape and a supplied amplitude bound are already discharged internally. -/
theorem scalar_maximal_limit_of_finite_canonical_fiber
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (hv : vacMix rho sigma ≠ 0) (seed : TailMatrix T 1 × TailMatrix T 1)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤)
    (hfiber : {d : TailMatrix T 1 × TailMatrix T 1 |
      IsRoot z rho sigma (M.bound.toReal • K) d.1 d.2 ∧ d ∈ closure (canonicalAmplitudes z rho sigma)}.Finite) :
    ∃ a : TailMatrix T 1 × TailMatrix T 1, IsRoot z rho sigma (M.bound.toReal • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧ a ∉ canonicalAmplitudes z rho sigma ∧
      Tendsto M.path (𝓝[<] M.bound.toReal) (𝓝 a) ∧
      ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0 := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings (ENNReal.ofReal_toReal hfinite).symm).trans (initial_couplings_ofReal _ hb)
  obtain ⟨a,u,hu,ht,ha,hroot,hclose,hzero⟩ := maximal_finite_endpoint_has_physical_cluster
    z hz rho sigma hsigma hrho K hv seed M hfinite
  have hlim := canonical_finite_fiber_cluster_has_limit z rho sigma K M.path M.bound.toReal hb
    (by simpa only [hset] using M.analytic.continuousOn)
    (by simpa only [hset] using M.roots) (by simpa only [hset] using M.canonical) a u hu ht ha hfiber
  exact ⟨a,hroot,hclose,physical_zero_not_canonical z rho sigma hrho a hzero,hlim,hzero⟩

/-- Actual partial invertibility implies endpoint-root isolation by the
TRUE analytic IFT. No canonical/physical sign premise or root curve is used. -/
theorem actual_regular_root_isolated
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N)
    (ha : IsRoot z rho sigma (b • K) a.1 a.2)
    (hi : EndpointRegular z rho sigma K b a) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ d : TailMatrix T N × TailMatrix T N,
      IsRoot z rho sigma (b • K) d.1 d.2 → dist d a < delta → d = a := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hc : ContDiffAt ℝ ω R (b,a) :=
    (FMSA.Paper.ActualAnalyticBranch.residual_analyticAt z rho sigma K (b,a)).contDiffAt
  let q := hc.implicitFunction (by simp) hi
  have hq0 : q b = a := hc.implicitFunction_apply_self (by simp) hi
  have hR0 : R (b,a) = 0 := (residual_eq_zero_iff _ _ _ _ _ _ _).mpr ha
  have ht : Tendsto (fun d : TailMatrix T N × TailMatrix T N => (b,d)) (𝓝 a) (𝓝 (b,a)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have he : ∀ᶠ d in 𝓝 a, R (b,d) = 0 → d = a := by
    filter_upwards [ht.eventually (hc.eventually_apply_eq_iff_implicitFunction (by simp) hi)] with d hd hzero
    exact (hd.mp (hzero.trans hR0.symm)).symm.trans hq0
  obtain ⟨delta,hd,hball⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨delta,hd,fun d hrootd hdist => hball hdist ((residual_eq_zero_iff _ _ _ _ _ _ _).mpr hrootd)⟩

/-- The isolated-root argument strengthens regular cluster control to ANY
continuous actual BH root prefix: no canonicity or physical sign hypotheses
along the old branch are needed, just regularity of the approaching cluster. -/
theorem actual_regular_cluster_has_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hi : EndpointRegular z rho sigma K b a) : Tendsto p (𝓝[<] b) (𝓝 a) :=
  actual_isolated_cluster_has_limit z rho sigma K p b hb hp hroot a u hu ht ha
    (actual_regular_root_isolated z rho sigma K b a
      (actual_endpoint_cluster_isRoot z rho sigma K p b a u hu ht ha hroot) hi)

end FMSA.Convergence.IsolatedEndpointLimits

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.cluster_and_exits_give_crossings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.cluster_and_exits_give_crossings

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.spherical_crossings_have_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.spherical_crossings_have_cluster

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.nonlimit_has_spherical_clusters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.nonlimit_has_spherical_clusters

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.isolated_fiber_cluster_has_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.isolated_fiber_cluster_has_limit

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.finite_set_isolated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.finite_set_isolated

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.finite_fiber_isolated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.finite_fiber_isolated

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.finite_fiber_cluster_has_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.finite_fiber_cluster_has_limit

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.actual_nonlimit_has_spherical_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.actual_nonlimit_has_spherical_roots

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.actual_nonlimit_forces_nonisolated_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.actual_nonlimit_forces_nonisolated_roots

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.actual_isolated_cluster_has_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.actual_isolated_cluster_has_limit

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.actual_finite_fiber_cluster_has_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.actual_finite_fiber_cluster_has_limit

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.bounded_actual_prefix_finite_fiber_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.bounded_actual_prefix_finite_fiber_limit

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.actual_isolated_cluster_bounds_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.actual_isolated_cluster_bounds_prefix

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.canonical_nonlimit_has_spherical_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.canonical_nonlimit_has_spherical_roots

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.canonical_isolated_cluster_has_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.canonical_isolated_cluster_has_limit

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.canonical_finite_fiber_cluster_has_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.canonical_finite_fiber_cluster_has_limit

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.scalar_maximal_limit_of_finite_canonical_fiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.scalar_maximal_limit_of_finite_canonical_fiber

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.actual_regular_root_isolated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.actual_regular_root_isolated

/-- info: 'FMSA.Convergence.IsolatedEndpointLimits.actual_regular_cluster_has_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.IsolatedEndpointLimits.actual_regular_cluster_has_limit
