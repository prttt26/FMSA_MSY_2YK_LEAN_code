import MSAConvergence.SelectedBranchAlgebraicity
import MSAConvergence.BHPolynomialJacobian

/-! Full finite physical endpoint limits of actual canonical BH branches.
Literal residual and amplitude-Jacobian repacking connect internally constructed
primitive coordinate relations to the ORIGINAL Dt/G system. Scalar properness
supplies a finite cluster from physical data, with no isolation, finite-fiber
certificate, endpoint inverse or assumed full limit. -/

noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ActualAlgebraicEndpoint
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.Convergence.SelectedBranchAlgebraicity
open FMSA.Convergence.RegularEndpointContinuation FMSA.Convergence.ActualTracerAmplitudeRecovery
open FMSA.Convergence.MaximalCanonicalBranch FMSA.Convergence.MaximalMSAConvergence
open FMSA.Convergence.CanonicalEndpointContinuation FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.ScalarCanonicalProperness FMSA.Paper.StableIntervalRadius
variable {N : ℕ} {T : Type*} [Fintype T]
local instance : DecidableEq (AmpIndex T N) := Classical.decEq _

def repackedResidual (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (i : AmpIndex T N) : MvPolynomial (AmpIndex T N) (Polynomial ℝ) :=
  couplingCoefficientMap (residualPoly z rho sigma K i)

/-- Literal coupling-coefficient repacking recovers EVERY original BH residual
coordinate, for all actual data, couplings and amplitudes, including nonroots. -/
theorem repacked_residual_eval (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) (i : AmpIndex T N) :
    MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (amplitudeValues a)
      (repackedResidual z rho sigma K i) =
      amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (t,a)) i := by
  rw [repackedResidual,eval₂_couplingCoefficientMap]
  exact eval_residualPoly z rho sigma K (t,a) i

/-- Repacked polynomial roots are exactly ORIGINAL BH roots, without a
regularity, density, activity, positivity or denominator exclusion. -/
theorem actual_root_iff_repacked_zeros
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    IsRoot z rho sigma (t • K) a.1 a.2 ↔
      ∀ i, MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (amplitudeValues a)
        (repackedResidual z rho sigma K i)=0 := by
  rw [actual_root_iff_polynomial_zeros]
  simp only [repackedResidual,eval₂_couplingCoefficientMap]
  rfl

/-- The repacked formal determinant is the TRUE original amplitude partial
matrix determinant in all Dt/G coordinates; no regularity is assumed. -/
theorem repacked_determinant_eq_actual
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (amplitudeValues a)
      (determinantPolynomial (repackedResidual z rho sigma K)) =
      (jacobian z rho sigma K t a).det := by
  change MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (amplitudeValues a)
    (determinantPolynomial (fun i => couplingCoefficientMap (residualPoly z rho sigma K i))) = _
  rw [eval₂_couplingCoefficientMap_jacobian]
  rfl

/-- One finite approaching cluster of any continuous REGULAR actual BH root
prefix is its FULL left limit. No endpoint regularity, isolated root,
finite-fiber certificate, boundedness or supplied full limit is used. -/
theorem actual_regular_prefix_cluster_has_limit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0<b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hreg : ∀ t ∈ Ico 0 b, EndpointRegular z rho sigma K t (p t))
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  let e := amplitudeCoordinates (T := T) (N := N)
  let pc : ℝ → AmpIndex T N → ℝ := fun t => amplitudeValues (p t)
  have hpc : ContinuousOn pc (Ico 0 b) := e.continuous.comp_continuousOn hp
  have hroots : ∀ t ∈ Ico 0 b, ∀ i,
      MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (pc t)
        (repackedResidual z rho sigma K i)=0 := by
    intro t ht
    exact (actual_root_iff_repacked_zeros z rho sigma K t (p t)).mp (hroot t ht)
  have hregular : ∀ t ∈ Ico 0 b,
      MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (pc t)
        (determinantPolynomial (repackedResidual z rho sigma K)) ≠ 0 := by
    intro t ht
    rw [repacked_determinant_eq_actual]
    exact (endpoint_regular_iff_jacobian_det_ne_zero z rho sigma K t (p t)).mp (hreg t ht)
  have hca : Tendsto (fun n => pc (u n)) atTop (𝓝 (amplitudeValues a)) :=
    (e.continuous.tendsto a).comp ha
  have hc := regular_polynomial_prefix_cluster_has_limit (repackedResidual z rho sigma K)
    pc b hb hpc hroots hregular (amplitudeValues a) u hu ht hca
  have hback : Tendsto (fun t => e.symm (pc t)) (𝓝[<] b) (𝓝 (e.symm (amplitudeValues a))) :=
    (e.symm.continuous.tendsto (amplitudeValues a)).comp hc
  have hf : (fun t => e.symm (pc t))=p := by
    funext t
    exact e.symm_apply_apply (p t)
  have he : e.symm (amplitudeValues a)=a := e.symm_apply_apply a
  rw [hf,he] at hback
  exact hback

/-- On an actual canonical root prefix regularity is DISCHARGED internally.
Every finite cluster is its full left limit, including singular/nonisolated
endpoint fibers, for arbitrary finite mixtures and finite signed tails. -/
theorem actual_canonical_prefix_cluster_has_limit
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j=K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0<b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  apply actual_regular_prefix_cluster_has_limit z rho sigma K p b hb hp hroot _ a u hu ht ha
  intro t ht
  exact actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t (p t) hv
    (hroot t ht) (hcanon t ht)

/-- Endpoint facts for this SELECTED path and its genuine left limit.
Uniqueness of all other actual roots at the same endpoint is not included. -/
def PhysicalEndpointLimit (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (a : TailMatrix T N × TailMatrix T N) : Prop :=
  IsRoot z rho sigma (b • K) a.1 a.2 ∧ a ∈ closure (canonicalAmplitudes z rho sigma) ∧
    a ∉ canonicalAmplitudes z rho sigma ∧ Tendsto p (𝓝[<] b) (𝓝 a) ∧
    ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
      (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2)
      (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det=0

/-- Every finite cluster of the CONSTRUCTED maximal canonical branch is
its full endpoint limit. No original endpoint-fiber isolation is required. -/
theorem maximal_finite_cluster_has_limit
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j=K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound ≠ ⊤) (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 M.bound.toReal) (ht : Tendsto u atTop (𝓝 M.bound.toReal))
    (ha : Tendsto (fun n => M.path (u n)) atTop (𝓝 a)) :
    Tendsto M.path (𝓝[<] M.bound.toReal) (𝓝 a) := by
  have hb : 0<M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound=ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound=Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  apply actual_canonical_prefix_cluster_has_limit z hz rho sigma hsigma hrho K hK hv
    M.path M.bound.toReal hb _ _ _ a u hu ht ha
  · simpa only [hset] using M.analytic.continuousOn
  · simpa only [hset] using M.roots
  · simpa only [hset] using M.canonical

/-- For general finite mixtures a supplied UNIFORM amplitude bound gives a
full physical endpoint limit, with no isolation or endpoint inverse. The
bound is not silently asserted to exist for every mixture. -/
theorem maximal_bounded_endpoint_has_limit
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j=K u j i) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound ≠ ⊤) (B : ℝ)
    (hB : ∀ t ∈ Ico 0 M.bound.toReal, ‖M.path t‖≤B) :
    ∃ a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a := by
  obtain ⟨a,u,_hB,hu,ht,ha,hr,hcl,hzero⟩ :=
    maximal_bounded_endpoint_cluster z hz rho sigma hsigma hrho K hK hv seed M hfinite B hB
  exact ⟨a,hr,hcl,physical_zero_not_canonical z rho sigma hrho a hzero,
    maximal_finite_cluster_has_limit z hz rho sigma hsigma hrho K hK hv seed M hfinite a u hu ht ha,hzero⟩

/-- For ONE species at arbitrary finite signed/repeated/inactive tails,
every finite maximal canonical endpoint has its FULL physical Fourier-zero
limiting root. Escape, finite-cluster existence and path regularity are all
discharged; no amplitude bound, certificate, isolation or inverse is supplied. -/
theorem scalar_maximal_finite_endpoint_has_limit
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i) (K : TailMatrix T 1)
    (hv : vacMix rho sigma ≠ 0) (seed : TailMatrix T 1 × TailMatrix T 1)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃ a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a := by
  have hK : ∀ u i j, K u i j=K u j i := by intro u i j; fin_cases i; fin_cases j; rfl
  obtain ⟨a,u,hu,ht,ha,hr,hcl,hzero⟩ :=
    maximal_finite_endpoint_has_physical_cluster z hz rho sigma hsigma hrho K hv seed M hfinite
  exact ⟨a,hr,hcl,physical_zero_not_canonical z rho sigma hrho a hzero,
    maximal_finite_cluster_has_limit z hz rho sigma hsigma hrho K hK hv seed M hfinite a u hu ht ha,hzero⟩

/-- The limiting physical amplitude is UNIQUE FOR THIS PATH, even if there
are other original BH roots or nonisolated components at the same coupling. -/
theorem scalar_maximal_unique_physical_limit
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i) (K : TailMatrix T 1)
    (hv : vacMix rho sigma ≠ 0) (seed : TailMatrix T 1 × TailMatrix T 1)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃! a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a := by
  obtain ⟨a,ha⟩ := scalar_maximal_finite_endpoint_has_limit z hz rho sigma hsigma hrho K hv seed M hfinite
  refine ⟨a,ha,?_⟩
  rintro d ⟨_hr,_hcl,_hnc,hd,_hz⟩
  exact tendsto_nhds_unique hd ha.2.2.2.1

/-- At EVERY physical one-species HS state eta<1, construct the maximal
initial canonical branch from data alone. Each FINITE endpoint has a unique
full physical limiting root, with a genuine real Fourier zero and failed
canonicity. No root curve, seed canonicity, inverse, bound, cluster, isolation
or elimination certificate is assumed. Infinite maximal intervals are allowed. -/
theorem exists_scalar_hs_maximal_branch_with_finite_endpoint_limit
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i) (hv : 0<vacMix rho sigma)
    (K : TailMatrix T 1) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound=maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ → 0<M.bound.toReal ∧
        ∃! a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a) := by
  obtain ⟨M,hM⟩ := exists_scalar_hs_maximal_branch z hz rho sigma hsigma hrho K hv
  refine ⟨M,hM,fun hfinite => ⟨ENNReal.toReal_pos (ne_of_gt M.positive) hfinite,?_⟩⟩
  exact scalar_maximal_unique_physical_limit z hz rho sigma hsigma hrho K hv.ne' _ M hfinite

/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.repacked_residual_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.repacked_residual_eval
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.actual_root_iff_repacked_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.actual_root_iff_repacked_zeros
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.repacked_determinant_eq_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.repacked_determinant_eq_actual
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.actual_regular_prefix_cluster_has_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.actual_regular_prefix_cluster_has_limit
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.actual_canonical_prefix_cluster_has_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.actual_canonical_prefix_cluster_has_limit
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.maximal_finite_cluster_has_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.maximal_finite_cluster_has_limit
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.maximal_bounded_endpoint_has_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.maximal_bounded_endpoint_has_limit
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.scalar_maximal_finite_endpoint_has_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.scalar_maximal_finite_endpoint_has_limit
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.scalar_maximal_unique_physical_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.scalar_maximal_unique_physical_limit
/-- info: 'FMSA.Convergence.ActualAlgebraicEndpoint.exists_scalar_hs_maximal_branch_with_finite_endpoint_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualAlgebraicEndpoint.exists_scalar_hs_maximal_branch_with_finite_endpoint_limit
end FMSA.Convergence.ActualAlgebraicEndpoint
