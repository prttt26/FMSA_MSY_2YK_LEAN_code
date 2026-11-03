import MSAConvergence.CanonicalEndpointContinuation

/-! Construction of the actual maximal initial canonical branch by coherent
prefixes. Neither a root curve nor its global existence is assumed. -/
noncomputable section
open Filter Topology Set
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.ActualCanonicalBranch
open FMSA.Convergence.CanonicalEndpointContinuation
open FMSA.Paper.StableIntervalRadius
variable {N : ℕ} {T : Type*} [Fintype T]

/-- A positive finite actual canonical initial root prefix through a fixed seed. -/
structure CanonicalPrefix (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) where
  stop : ℝ
  stop_pos : 0 < stop
  path : ℝ → TailMatrix T N × TailMatrix T N
  at_seed : path 0 = seed
  continuous : ContinuousOn path (Ico 0 stop)
  roots : ∀ t ∈ Ico 0 stop, IsRoot z rho sigma (t • K) (path t).1 (path t).2
  canonical : ∀ t ∈ Ico 0 stop, path t ∈ canonicalAmplitudes z rho sigma

/-- Supremum of ALL actual admissible finite initial-prefix lengths. Infinity
is allowed. Positivity will be proved from the true local canonical seed. -/
def maximalBound (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) : ENNReal :=
  ⨆ P : CanonicalPrefix z rho sigma K seed, ENNReal.ofReal P.stop

/-- A point is before the supremal endpoint exactly when some actual prefix
reaches strictly beyond that point. This also handles an infinite supremum. -/
theorem mem_maximal_domain_iff (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (t : ℝ) :
    t ∈ initialCouplings (maximalBound z rho sigma K seed) ↔
      0 ≤ t ∧ ∃ P : CanonicalPrefix z rho sigma K seed, t < P.stop := by
  change (0 ≤ t ∧ ENNReal.ofReal t < ⨆ P : CanonicalPrefix z rho sigma K seed, ENNReal.ofReal P.stop) ↔ _
  constructor
  · rintro ⟨ht,hlt⟩
    obtain ⟨P,hP⟩ := lt_iSup_iff.mp hlt
    exact ⟨ht,P,(ENNReal.ofReal_lt_ofReal_iff P.stop_pos).mp hP⟩
  · rintro ⟨ht,P,hP⟩
    exact ⟨ht,lt_iSup_iff.mpr ⟨P,(ENNReal.ofReal_lt_ofReal_iff P.stop_pos).mpr hP⟩⟩

/-- Choice of an admissible prefix at a point of the union domain. Coherence
will make the resulting branch independent of this choice on its domain. -/
def chosenPrefix (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (t : ℝ)
    (ht : t ∈ initialCouplings (maximalBound z rho sigma K seed)) :
    CanonicalPrefix z rho sigma K seed :=
  Classical.choose ((mem_maximal_domain_iff z rho sigma K seed t).mp ht).2

theorem chosen_prefix_reaches (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (t : ℝ)
    (ht : t ∈ initialCouplings (maximalBound z rho sigma K seed)) :
    t < (chosenPrefix z rho sigma K seed t ht).stop :=
  Classical.choose_spec ((mem_maximal_domain_iff z rho sigma K seed t).mp ht).2

/-- The actual coherent-union path. Values outside its nonnegative maximal
domain are placeholders, not asserted to be roots or analytic. -/
def maximalPath (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (t : ℝ) : TailMatrix T N × TailMatrix T N := by
  classical
  exact if ht : t ∈ initialCouplings (maximalBound z rho sigma K seed) then
    (chosenPrefix z rho sigma K seed t ht).path t else seed

/-- Every actual finite prefix length is bounded by the declared supremum. -/
theorem prefix_bound_le_maximal (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (P : CanonicalPrefix z rho sigma K seed) :
    ENNReal.ofReal P.stop ≤ maximalBound z rho sigma K seed := by
  unfold maximalBound
  exact le_iSup (fun Q : CanonicalPrefix z rho sigma K seed => ENNReal.ofReal Q.stop) P

/-- At zero the union path has the fixed seed, even before nonemptiness is
established. Every admissible representative has the same seed value. -/
theorem maximal_path_at_seed (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) : maximalPath z rho sigma K seed 0 = seed := by
  classical
  unfold maximalPath
  split_ifs with h
  · exact (chosenPrefix z rho sigma K seed 0 h).at_seed
  · rfl

/-- A true canonical seed generates a positive finite actual initial prefix;
no local root curve or inverse is supplied by the caller. -/
theorem canonical_prefix_nonempty
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma 0 seed.1 seed.2)
    (hcanon : seed ∈ canonicalAmplitudes z rho sigma) :
    Nonempty (CanonicalPrefix z rho sigma K seed) := by
  obtain ⟨q,hq0,hqa,hqr,hqc⟩ := exists_analytic_canonical_root z hz rho sigma hsigma hrho K hK hv 0 seed
    (by simpa only [zero_smul] using hroot) hcanon
  obtain ⟨delta,hd,hball⟩ := Metric.eventually_nhds_iff.mp (hqa.eventually_analyticAt.and (hqr.and hqc))
  have hnear (t : ℝ) (ht : t ∈ Ico 0 delta) : AnalyticAt ℝ q t ∧
      IsRoot z rho sigma (t • K) (q t).1 (q t).2 ∧ q t ∈ canonicalAmplitudes z rho sigma :=
    hball (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht.1] using ht.2)
  exact ⟨⟨delta,hd,q,hq0,fun t ht => (hnear t ht).1.continuousAt.continuousWithinAt,
    fun t ht => (hnear t ht).2.1,fun t ht => (hnear t ht).2.2⟩⟩

/-- Any two actual canonical prefixes through the same seed agree at EVERY
point in their overlap, by the genuine actual Jacobian/branch uniqueness. -/
theorem prefixes_agree
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (P Q : CanonicalPrefix z rho sigma K seed)
    (t : ℝ) (ht : 0 ≤ t) (hP : t < P.stop) (hQ : t < Q.stop) : P.path t = Q.path t := by
  have hsubP : Ico (0 : ℝ) (min P.stop Q.stop) ⊆ Ico 0 P.stop :=
    fun x hx => ⟨hx.1,hx.2.trans_le (min_le_left _ _)⟩
  have hsubQ : Ico (0 : ℝ) (min P.stop Q.stop) ⊆ Ico 0 Q.stop :=
    fun x hx => ⟨hx.1,hx.2.trans_le (min_le_right _ _)⟩
  have he := actual_canonical_roots_eqOn_of_preconnected z hz rho sigma hsigma hrho K hK hv
    P.path Q.path (Ico 0 (min P.stop Q.stop)) 0 (convex_Ico _ _).isPreconnected
    ⟨le_rfl,lt_min P.stop_pos Q.stop_pos⟩ (P.continuous.mono hsubP) (Q.continuous.mono hsubQ)
    (P.at_seed.trans Q.at_seed.symm) (fun x hx => P.roots x (hsubP hx))
    (fun x hx => Q.roots x (hsubQ hx)) (fun x hx => P.canonical x (hsubP hx))
  exact he ⟨ht,lt_min hP hQ⟩

/-- The union path agrees with EVERY old prefix on its WHOLE domain. -/
theorem maximal_path_eq_prefix
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (P : CanonicalPrefix z rho sigma K seed) :
    Set.EqOn (maximalPath z rho sigma K seed) P.path (Ico 0 P.stop) := by
  classical
  intro t ht
  have hD := (mem_maximal_domain_iff z rho sigma K seed t).mpr ⟨ht.1,P,ht.2⟩
  rw [maximalPath,dif_pos hD]
  exact prefixes_agree z hz rho sigma hsigma hrho K hK hv seed _ P t ht.1
    (chosen_prefix_reaches z rho sigma K seed t hD) ht.2

/-- The supremal domain has positive length as soon as one true prefix exists. -/
theorem maximal_bound_pos_of_prefix (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (P : CanonicalPrefix z rho sigma K seed) :
    0 < maximalBound z rho sigma K seed :=
  (ENNReal.ofReal_pos.mpr P.stop_pos).trans_le (prefix_bound_le_maximal z rho sigma K seed P)


/-- At every point BEFORE the supremal bound, the constructed path is an
actual root and is fully canonical. Outside-domain placeholders are not used. -/
theorem maximal_path_roots_and_canonicity
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (t : ℝ)
    (ht : t ∈ initialCouplings (maximalBound z rho sigma K seed)) :
    IsRoot z rho sigma (t • K) (maximalPath z rho sigma K seed t).1
      (maximalPath z rho sigma K seed t).2 ∧
      maximalPath z rho sigma K seed t ∈ canonicalAmplitudes z rho sigma := by
  classical
  rw [maximalPath,dif_pos ht]
  have hi : t ∈ Ico 0 (chosenPrefix z rho sigma K seed t ht).stop :=
    ⟨((mem_maximal_domain_iff z rho sigma K seed t).mp ht).1,chosen_prefix_reaches z rho sigma K seed t ht⟩
  exact ⟨(chosenPrefix z rho sigma K seed t ht).roots t hi,(chosenPrefix z rho sigma K seed t ht).canonical t hi⟩

/-- Coherence with one fixed prefix near each point proves genuine relative
continuity of the constructed path on its ENTIRE maximal initial domain. -/
theorem maximal_path_continuousOn
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) :
    ContinuousOn (maximalPath z rho sigma K seed) (initialCouplings (maximalBound z rho sigma K seed)) := by
  intro t ht
  obtain ⟨ht0,P,hPt⟩ := (mem_maximal_domain_iff z rho sigma K seed t).mp ht
  have hlow : ∀ᶠ x : ℝ in 𝓝 t, x < P.stop := Iio_mem_nhds hPt
  have hlocal : Ico (0 : ℝ) P.stop ∈ 𝓝[initialCouplings (maximalBound z rho sigma K seed)] t := by
    filter_upwards [self_mem_nhdsWithin,hlow.filter_mono nhdsWithin_le_nhds] with x hx hxP
    exact ⟨((mem_maximal_domain_iff z rho sigma K seed x).mp hx).1,hxP⟩
  have heq : maximalPath z rho sigma K seed =ᶠ[𝓝[initialCouplings (maximalBound z rho sigma K seed)] t] P.path := by
    filter_upwards [hlocal] with x hx
    exact maximal_path_eq_prefix z hz rho sigma hsigma hrho K hK hv seed P hx
  exact ((P.continuous t ⟨ht0,hPt⟩).mono_of_mem_nhdsWithin hlocal).congr_of_eventuallyEq heq
    (maximal_path_eq_prefix z hz rho sigma hsigma hrho K hK hv seed P ⟨ht0,hPt⟩)

/-- The true canonical seed makes the constructed supremal endpoint positive. -/
theorem maximal_bound_pos
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma 0 seed.1 seed.2)
    (hcanon : seed ∈ canonicalAmplitudes z rho sigma) :
    0 < maximalBound z rho sigma K seed := by
  obtain ⟨P⟩ := canonical_prefix_nonempty z hz rho sigma hsigma hrho K hK hv seed hroot hcanon
  exact maximal_bound_pos_of_prefix z rho sigma K seed P

/-- If the supremum is a finite positive b, NO same-seed path can have a
longer continuous canonical prefix through b. Maximality is proved, not supplied. -/
theorem no_longer_prefix_at_maximal_bound
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp0 : p 0 = seed)
    (b : ℝ) (hb : 0 < b) (hbound : maximalBound z rho sigma K seed = ENNReal.ofReal b) :
    ¬HasLongerCanonicalPrefix z rho sigma K p b := by
  rintro ⟨c,hbc,e,heq,hecont,her⟩
  let P : CanonicalPrefix z rho sigma K seed :=
    ⟨c,hb.trans hbc,e,(heq ⟨le_rfl,hb⟩).trans hp0,hecont,
      fun t ht => (her t ht).1,fun t ht => (her t ht).2⟩
  have hle := prefix_bound_le_maximal z rho sigma K seed P
  rw [hbound] at hle
  have hlt : ENNReal.ofReal b < ENNReal.ofReal c := (ENNReal.ofReal_lt_ofReal_iff (hb.trans hbc)).mpr hbc
  exact (not_lt_of_ge hle) hlt


/-- A globally maximal initial canonical branch with a TRUE analytic
representative, not arbitrary outside-domain values used as Taylor data. -/
structure MaximalBranch (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) where
  bound : ENNReal
  positive : 0 < bound
  path : ℝ → TailMatrix T N × TailMatrix T N
  at_seed : path 0 = seed
  analytic : AnalyticOnNhd ℝ path (initialCouplings bound)
  roots : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (path t).1 (path t).2
  canonical : ∀ t ∈ initialCouplings bound, path t ∈ canonicalAmplitudes z rho sigma
  local_roots : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (path t).1 (path t).2
  local_canonical : ∀ᶠ t in 𝓝 (0 : ℝ), path t ∈ canonicalAmplitudes z rho sigma
  maximal : ∀ P : CanonicalPrefix z rho sigma K seed,
    ENNReal.ofReal P.stop ≤ bound ∧ Set.EqOn path P.path (Ico 0 P.stop)

/-- Construction of a genuine GLOBAL maximal initial analytic canonical
branch, whose endpoint is exactly the supremum of all admissible prefix
lengths. Only actual seed-root/canonicity data are supplied, no root curve. -/
theorem exists_maximal_branch
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma 0 seed.1 seed.2)
    (hcanon : seed ∈ canonicalAmplitudes z rho sigma) :
    ∃ M : MaximalBranch z rho sigma K seed, M.bound = maximalBound z rho sigma K seed := by
  have hpos := maximal_bound_pos z hz rho sigma hsigma hrho K hK hv seed hroot hcanon
  have hcont := maximal_path_continuousOn z hz rho sigma hsigma hrho K hK hv seed
  have hrc := maximal_path_roots_and_canonicity z rho sigma K seed
  obtain ⟨g,heq,hga,hgr,hgc,_hR,_hsum⟩ := exists_canonical_series_extension z hz rho sigma hsigma hrho K hK hv
    (maximalPath z rho sigma K seed) (maximalBound z rho sigma K seed) hpos hcont
    (fun t ht => (hrc t ht).1) (fun t ht => (hrc t ht).2)
  have h0 : (0 : ℝ) ∈ initialCouplings (maximalBound z rho sigma K seed) := ⟨le_rfl,by simpa using hpos⟩
  have hg0 : g 0 = seed := (heq h0).trans (maximal_path_at_seed z rho sigma K seed)
  let M : MaximalBranch z rho sigma K seed := {
    bound := maximalBound z rho sigma K seed
    positive := hpos
    path := g
    at_seed := hg0
    analytic := hga
    roots := fun t ht => by rw [heq ht]; exact (hrc t ht).1
    canonical := fun t ht => by rw [heq ht]; exact (hrc t ht).2
    local_roots := hgr
    local_canonical := hgc
    maximal := fun P => ⟨prefix_bound_le_maximal z rho sigma K seed P,fun t ht =>
      (heq ((mem_maximal_domain_iff z rho sigma K seed t).mpr ⟨ht.1,P,ht.2⟩)).trans
        (maximal_path_eq_prefix z hz rho sigma hsigma hrho K hK hv seed P ht)⟩ }
  exact ⟨M,rfl⟩

/-- Finite endpoint data can be expressed using the ordinary half-open
interval; positivity is essential for the exact ofReal conversion. -/
theorem initial_couplings_ofReal (b : ℝ) (hb : 0 < b) :
    initialCouplings (ENNReal.ofReal b) = Ico (0 : ℝ) b := by
  ext t
  simp only [initialCouplings,mem_setOf_eq,mem_Ico]
  exact and_congr_right (fun _ => ENNReal.ofReal_lt_ofReal_iff hb)

/-- The maximality field EXCLUDES a longer continuous canonical prefix at
any finite positive endpoint. No nonextendability assumption is supplied. -/
theorem maximal_branch_nonextendable
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (b : ℝ) (hb : 0 < b) (hbound : M.bound = ENNReal.ofReal b) :
    ¬HasLongerCanonicalPrefix z rho sigma K M.path b := by
  rintro ⟨c,hbc,e,heq,hcont,hrc⟩
  let P : CanonicalPrefix z rho sigma K seed :=
    ⟨c,hb.trans hbc,e,(heq ⟨le_rfl,hb⟩).trans M.at_seed,hcont,
      fun t ht => (hrc t ht).1,fun t ht => (hrc t ht).2⟩
  have hle := (M.maximal P).1
  rw [hbound] at hle
  have hlt : ENNReal.ofReal b < ENNReal.ofReal c := (ENNReal.ofReal_lt_ofReal_iff (hb.trans hbc)).mpr hbc
  exact (not_lt_of_ge hle) hlt

/-- The constructed analytic maximal branch has a strictly positive intrinsic
common Taylor radius, even though its maximal real endpoint may be infinite. -/
theorem maximal_branch_radius_pos
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed) :
    0 < FMSA.Paper.FoldRadius.amplitudeRadius (FMSA.Paper.TaylorRoot.branchCoefficients M.path) := by
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound := ⟨le_rfl,by simpa using M.positive⟩
  exact FMSA.Paper.ActualAnalyticTaylor.amplitudeRadius_pos M.path (M.analytic 0 h0)

/-- Exact whole-maximal-interval Taylor criterion for the CONSTRUCTED true
analytic representative. Real global existence is NOT a complex-radius bound. -/
theorem maximal_branch_taylor_criterion
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed) :
    AmplitudeHasSumBefore M.path M.bound ↔ M.bound ≤
      FMSA.Paper.FoldRadius.amplitudeRadius (FMSA.Paper.TaylorRoot.branchCoefficients M.path) :=
  analytic_branch_converges_before_iff M.path M.bound M.analytic

/-- At a finite endpoint of the CONSTRUCTED maximal branch the genuine
boundary obstruction is amplitude escape OR an actual Fourier-zero cluster.
Nonextendability is derived, and exists_maximal_branch constructs M from
actual canonical seed data. -/
theorem maximal_branch_finite_boundary
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (b : ℝ) (hb : 0 < b) (hbound : M.bound = ENNReal.ofReal b) :
    (∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖M.path t‖) ∨
    HasPhysicalEndpointCluster z rho sigma K M.path b := by
  have hset : initialCouplings M.bound = Ico (0 : ℝ) b := by rw [hbound,initial_couplings_ofReal b hb]
  apply finite_nonextendable_prefix_boundary_obstruction z hz rho sigma hsigma hrho K hK hv M.path b hb
  · simpa only [hset] using M.analytic.continuousOn
  · simpa only [hset] using M.roots
  · simpa only [hset] using M.canonical
  · exact maximal_branch_nonextendable z rho sigma K seed M b hb hbound


/-- Restrict a maximal analytic branch to any positive finite prefix whose
endpoint is no larger than its bound. No extra branch is assumed. -/
def restrictedPrefix
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (c : ℝ) (hc : 0 < c) (hbound : ENNReal.ofReal c ≤ M.bound) : CanonicalPrefix z rho sigma K seed := by
  have hsub : Ico (0 : ℝ) c ⊆ initialCouplings M.bound := fun t ht =>
    ⟨ht.1,((ENNReal.ofReal_lt_ofReal_iff hc).mpr ht.2).trans_le hbound⟩
  exact ⟨c,hc,M.path,M.at_seed,M.analytic.continuousOn.mono hsub,
    fun t ht => M.roots t (hsub ht),fun t ht => M.canonical t (hsub ht)⟩

/-- Every maximal representative has EXACTLY the same bound as the actual
supremum definition. No room remains for a larger arbitrary record endpoint. -/
theorem maximal_branch_bound_eq_supremum
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed) :
    M.bound = maximalBound z rho sigma K seed := by
  apply le_antisymm
  · by_contra hn
    obtain ⟨c,_hc,hlt,hcM⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have hcp : 0 < c := ENNReal.ofReal_pos.mp ((show (0 : ENNReal) ≤ maximalBound z rho sigma K seed from bot_le).trans_lt hlt)
    let P := restrictedPrefix z rho sigma K seed M c hcp hcM.le
    exact (not_lt_of_ge (prefix_bound_le_maximal z rho sigma K seed P)) hlt
  · unfold maximalBound
    exact iSup_le (fun P => (M.maximal P).1)

/-- The maximal endpoint and all values on the maximal nonnegative domain
are UNIQUE, independently of every choice used in the coherent construction. -/
theorem maximal_branches_agree
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N) (M Q : MaximalBranch z rho sigma K seed) :
    M.bound = Q.bound ∧ Set.EqOn M.path Q.path (initialCouplings M.bound) := by
  have hM := maximal_branch_bound_eq_supremum z rho sigma K seed M
  have hQ := maximal_branch_bound_eq_supremum z rho sigma K seed Q
  refine ⟨hM.trans hQ.symm,?_⟩
  intro t ht
  rw [hM] at ht
  obtain ⟨ht0,P,hPt⟩ := (mem_maximal_domain_iff z rho sigma K seed t).mp ht
  exact ((M.maximal P).2 ⟨ht0,hPt⟩).trans ((Q.maximal P).2 ⟨ht0,hPt⟩).symm


/-- The actual Taylor coefficients and common radius are intrinsic to the
maximal canonical branch, independently of its analytic representative. -/
theorem maximal_branch_coefficients_and_radius_unique
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M Q : MaximalBranch z rho sigma K seed) :
    FMSA.Paper.TaylorRoot.branchCoefficients M.path = FMSA.Paper.TaylorRoot.branchCoefficients Q.path ∧
    FMSA.Paper.FoldRadius.amplitudeRadius (FMSA.Paper.TaylorRoot.branchCoefficients M.path) =
      FMSA.Paper.FoldRadius.amplitudeRadius (FMSA.Paper.TaylorRoot.branchCoefficients Q.path) := by
  have hM0 : (0 : ℝ) ∈ initialCouplings M.bound := ⟨le_rfl,by simpa using M.positive⟩
  have hQ0 : (0 : ℝ) ∈ initialCouplings Q.bound := ⟨le_rfl,by simpa using Q.positive⟩
  have he := actual_canonical_root_coefficients_unique z hz rho sigma hsigma hrho K hK hv M.path Q.path
    (M.analytic 0 hM0).continuousAt (Q.analytic 0 hQ0).continuousAt (M.at_seed.trans Q.at_seed.symm)
    M.local_roots Q.local_roots (M.canonical 0 hM0)
  exact ⟨he,by rw [he]⟩

end FMSA.Convergence.MaximalCanonicalBranch

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.mem_maximal_domain_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.mem_maximal_domain_iff

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.chosen_prefix_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.chosen_prefix_reaches

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.prefix_bound_le_maximal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.prefix_bound_le_maximal

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_path_at_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_path_at_seed

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.canonical_prefix_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.canonical_prefix_nonempty

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.prefixes_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.prefixes_agree

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_path_eq_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_path_eq_prefix

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_bound_pos_of_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_bound_pos_of_prefix

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_path_roots_and_canonicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_path_roots_and_canonicity

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_path_continuousOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_path_continuousOn

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_bound_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_bound_pos

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.no_longer_prefix_at_maximal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.no_longer_prefix_at_maximal_bound

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.exists_maximal_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.exists_maximal_branch

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.initial_couplings_ofReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.initial_couplings_ofReal

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_nonextendable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_nonextendable

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_radius_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_radius_pos

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_taylor_criterion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_taylor_criterion

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_finite_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_finite_boundary

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_bound_eq_supremum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_bound_eq_supremum

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_branches_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_branches_agree

/-- info: 'FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_coefficients_and_radius_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalCanonicalBranch.maximal_branch_coefficients_and_radius_unique
