import MSAConvergence.MaximalCanonicalBranch
import MSAConvergence.ScalarCanonicalSeed
import MSAConvergence.AmplitudeEscapeRadius

/-! Physical HS maximal initial branches and their true endpoint/Taylor
obstructions. Global existence data and nonextendability are CONSTRUCTED. -/
noncomputable section
open Filter Topology Set
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MaximalMSAConvergence
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.CanonicalEndpointContinuation FMSA.Convergence.AmplitudeEscapeRadius
open FMSA.Convergence.ScalarCanonicalSeed FMSA.Convergence.LowDensityCanonicalSeed
open FMSA.Paper.StableIntervalRadius FMSA.Paper.TaylorRoot FMSA.Paper.FoldRadius
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual physical HS root is discharged internally. For general mixtures
only honest initial full canonicity remains as a seed premise, not a root curve. -/
theorem exists_hs_maximal_branch_of_initial_canonicity
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : 0 < vacMix rho sigma)
    (hcanon : (0,baseSeed z rho sigma) ∈ canonicalAmplitudes z rho sigma) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) :=
  exists_maximal_branch z hz rho sigma hsigma hrho K hK hv.ne' (0,baseSeed z rho sigma)
    (baseSeed_isRoot z rho sigma hz hv hrho hsigma) hcanon

/-- For ONE species at EVERY physical eta<1, the global maximal initial
analytic canonical MSA branch is CONSTRUCTED from physical data alone. No
seed canonicity, root curve, inverse or maximality is supplied by the caller. -/
theorem exists_scalar_hs_maximal_branch
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T 1) (hv : 0 < vacMix rho sigma) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) := by
  have hK : ∀ u i j, K u i j = K u j i := by intro u i j; fin_cases i; fin_cases j; rfl
  have heta : etaMix rho sigma < 1 := by unfold vacMix at hv; linarith
  exact exists_hs_maximal_branch_of_initial_canonicity z hz rho sigma hsigma hrho K hK hv
    (actual_scalar_hs_canonical z hz rho sigma hsigma hrho heta (baseSeed z rho sigma))

/-- A whole density ball of arbitrary finite mixtures has CONSTRUCTED global
maximal initial canonical HS-seeded branches, uniformly for all symmetric K.
Initial canonicity and positive vacancy are conclusions in that ball. -/
theorem exists_low_density_hs_maximal_branch
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 < sigma i) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ rho : Fin N → ℝ,
      (∀ i, 0 ≤ rho i) → ‖rho‖ < epsilon → ∀ K : TailMatrix T N,
      (∀ u i j, K u i j = K u j i) →
      ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
        M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) := by
  obtain ⟨epsilon,he,hball⟩ := exists_hs_canonical_density_ball z hz sigma
  refine ⟨epsilon,he,?_⟩
  intro rho hrho hr K hK
  have h := hball rho hr
  exact exists_hs_maximal_branch_of_initial_canonicity z hz rho sigma hsigma hrho K hK h.1
    (h.2.2 (baseSeed z rho sigma))

/-- Any FINITE constructed maximal endpoint is positive and has the proved
amplitude-escape / actual Fourier-zero-cluster alternative. No endpoint limit
or nonextendability premise is supplied. An infinite maximal endpoint is allowed. -/
theorem maximal_finite_endpoint_boundary
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound ≠ ⊤) :
    0 < M.bound.toReal ∧
      ((∀ B c : ℝ, c < M.bound.toReal → ∃ t ∈ Ico 0 M.bound.toReal,
          c < t ∧ B < ‖M.path t‖) ∨
        HasPhysicalEndpointCluster z rho sigma K M.path M.bound.toReal) := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  exact ⟨hb,maximal_branch_finite_boundary z hz rho sigma hsigma hrho K hK hv seed M
    M.bound.toReal hb (ENNReal.ofReal_toReal hfinite).symm⟩

/-- If amplitudes of the CONSTRUCTED maximal branch stay bounded to its finite
endpoint, an actual bounded cluster ROOT and physical Fourier zero exist there.
No root/continuity at that endpoint or separately assumed maximality is used. -/
theorem maximal_bounded_endpoint_cluster
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound ≠ ⊤) (B : ℝ)
    (hB : ∀ t ∈ Ico 0 M.bound.toReal, ‖M.path t‖ ≤ B) :
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ u : ℕ → ℝ,
      ‖a‖ ≤ B ∧ (∀ n, u n ∈ Ico 0 M.bound.toReal) ∧ Tendsto u atTop (𝓝 M.bound.toReal) ∧
      Tendsto (fun n => M.path (u n)) atTop (𝓝 a) ∧
      IsRoot z rho sigma (M.bound.toReal • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧
      ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k).det = 0 := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal := by
    exact (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  apply bounded_nonextendable_prefix_has_physical_cluster z hz rho sigma hsigma hrho K hK hv M.path M.bound.toReal B hb
  · simpa only [hset] using M.analytic.continuousOn
  · simpa only [hset] using M.roots
  · simpa only [hset] using M.canonical
  · exact hB
  · exact maximal_branch_nonextendable z rho sigma K seed M _ hb hbound

/-- If the constructed maximal branch escapes at its finite endpoint, its
intrinsic radius is at most that endpoint and full-open-interval convergence
is equivalent to R=bound. This does NOT assert that equality or convergence
at the endpoint. All-component convergence at larger r is excluded. -/
theorem maximal_escape_taylor_obstruction
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound ≠ ⊤)
    (hunbounded : ¬∃ B : ℝ, ∀ t ∈ Ico 0 M.bound.toReal, ‖M.path t‖ ≤ B) :
    amplitudeRadius (branchCoefficients M.path) ≤ M.bound ∧
    (AmplitudeHasSumBefore M.path M.bound ↔ amplitudeRadius (branchCoefficients M.path) = M.bound) ∧
    ∀ r : ℝ, M.bound.toReal < r →
      ¬∃ a : TailMatrix T N × TailMatrix T N,
        (∀ u i j, HasSum (fun n => (branchCoefficients M.path n).1 u i j*r^n) (a.1 u i j)) ∧
        (∀ u i j, HasSum (fun n => (branchCoefficients M.path n).2 u i j*r^n) (a.2 u i j)) := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal := by
    exact (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  have hcont : ContinuousOn M.path (Ico 0 M.bound.toReal) := by simpa only [hset] using M.analytic.continuousOn
  have hroot : ∀ t ∈ Ico 0 M.bound.toReal, IsRoot z rho sigma (t • K) (M.path t).1 (M.path t).2 := by
    simpa only [hset] using M.roots
  have hcanon : ∀ t ∈ Ico 0 M.bound.toReal, M.path t ∈ canonicalAmplitudes z rho sigma := by
    simpa only [hset] using M.canonical
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound := ⟨le_rfl,by simpa using M.positive⟩
  have hg := (M.analytic 0 h0).contDiffAt (n := ∞)
  have hu := amplitude_radius_le_escape_endpoint z hz rho sigma hsigma hrho K hK hv M.path M.bound.toReal hb
    hcont hroot hcanon hunbounded M.path hg rfl M.local_roots
  have hupper : amplitudeRadius (branchCoefficients M.path) ≤ M.bound := by rw [hbound]; exact hu
  have hc := maximal_branch_taylor_criterion z rho sigma K seed M
  refine ⟨hupper,?_,?_⟩
  · exact ⟨fun hsum => le_antisymm hupper (hc.mp hsum),fun heq => hc.mpr heq.ge⟩
  · exact nonconvergence_beyond_amplitude_escape z hz rho sigma hsigma hrho K hK hv M.path M.bound.toReal hb
      hcont hroot hcanon hunbounded M.path hg rfl M.local_roots

end FMSA.Convergence.MaximalMSAConvergence

/-- info: 'FMSA.Convergence.MaximalMSAConvergence.exists_hs_maximal_branch_of_initial_canonicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalMSAConvergence.exists_hs_maximal_branch_of_initial_canonicity

/-- info: 'FMSA.Convergence.MaximalMSAConvergence.exists_scalar_hs_maximal_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalMSAConvergence.exists_scalar_hs_maximal_branch

/-- info: 'FMSA.Convergence.MaximalMSAConvergence.exists_low_density_hs_maximal_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalMSAConvergence.exists_low_density_hs_maximal_branch

/-- info: 'FMSA.Convergence.MaximalMSAConvergence.maximal_finite_endpoint_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalMSAConvergence.maximal_finite_endpoint_boundary

/-- info: 'FMSA.Convergence.MaximalMSAConvergence.maximal_bounded_endpoint_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalMSAConvergence.maximal_bounded_endpoint_cluster

/-- info: 'FMSA.Convergence.MaximalMSAConvergence.maximal_escape_taylor_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.MaximalMSAConvergence.maximal_escape_taylor_obstruction
