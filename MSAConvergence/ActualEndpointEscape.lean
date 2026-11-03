import MSAConvergence.EndpointEscape
import MSAConvergence.ActualAlgebraicEndpoint

/-! Sharp finite endpoint alternatives for ACTUAL finite mixtures. Selected
polynomial relations eliminate finite-cluster oscillation, so the only open
escape possibility is norm tending to infinity along the whole prefix. -/
noncomputable section
open Set Real Filter Topology
namespace FMSA.Convergence.ActualEndpointEscape
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.EndpointEscape FMSA.Convergence.ActualAlgebraicEndpoint
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.CanonicalEndpointContinuation
open FMSA.Convergence.RegularEndpointContinuation FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.MixtureHSCanonicity FMSA.Convergence.MaximalMSAConvergence
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Every continuous canonical ORIGINAL root prefix has a full finite left
limit OR its ORIGINAL amplitude norm tends to infinity. No finite-fiber,
isolation, cluster, endpoint inverse or amplitude bound is supplied. -/
theorem actual_canonical_prefix_limit_or_norm_escape
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j=K u j i) (hv : vacMix rho sigma≠0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0<b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    (∃ a, Tendsto p (𝓝[<] b) (𝓝 a)) ∨ Tendsto (fun t => ‖p t‖) (𝓝[<] b) atTop := by
  apply full_limit_or_norm_escape p b hb
  exact fun a u hu ht ha => actual_canonical_prefix_cluster_has_limit z hz rho sigma
    hsigma hrho K hK hv p b hb hp hroot hcanon a u hu ht ha

/-- At a finite CONSTRUCTED maximal endpoint the finite alternative is an
honest physical Fourier-zero root with a full selected limit. The escape
alternative is genuine norm→infinity, not just arbitrarily large values. -/
theorem maximal_finite_physical_limit_or_norm_escape
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j=K u j i) (hv : vacMix rho sigma≠0)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound≠⊤) :
    (∃ a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a) ∨
      Tendsto (fun t => ‖M.path t‖) (𝓝[<] M.bound.toReal) atTop := by
  have hb : 0<M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound=ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound=Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  rcases norm_escape_or_finite_cluster M.path M.bound.toReal hb with he|⟨a,u,hu,ht,ha⟩
  · exact Or.inr he
  left
  have hlim := maximal_finite_cluster_has_limit z hz rho sigma hsigma hrho K hK hv
    seed M hfinite a u hu ht ha
  have hp : ContinuousOn M.path (Ico 0 M.bound.toReal) := by
    simpa only [hset] using M.analytic.continuousOn
  obtain ⟨B,_,hB⟩ := left_limit_bounds_entire_prefix M.path M.bound.toReal hb hp a hlim
  exact maximal_bounded_endpoint_has_limit z hz rho sigma hsigma hrho K hK hv seed M hfinite B hB

/-- Physical mixture data with eta<1 construct their HS maximal initial
canonical branch. Every FINITE endpoint has the precise physical-limit or
norm-escape alternative; the theorem does not rule out the second case. -/
theorem exists_mixture_hs_branch_with_sharp_endpoint_alternative
    (z : T → ℝ) (hz : ∀ u, 0<z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0<sigma i) (hrho : ∀ i, 0≤rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j=K u j i) (hv : 0<vacMix rho sigma) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound=maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound≠⊤ → (∃ a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a) ∨
        Tendsto (fun t => ‖M.path t‖) (𝓝[<] M.bound.toReal) atTop) := by
  obtain ⟨M,hM⟩ := exists_mixture_hs_maximal_branch z hz rho sigma hsigma hrho K hK hv
  exact ⟨M,hM,fun hfinite => maximal_finite_physical_limit_or_norm_escape z hz rho sigma
    hsigma hrho K hK hv.ne' _ M hfinite⟩

/-- info: 'FMSA.Convergence.ActualEndpointEscape.actual_canonical_prefix_limit_or_norm_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualEndpointEscape.actual_canonical_prefix_limit_or_norm_escape
/-- info: 'FMSA.Convergence.ActualEndpointEscape.maximal_finite_physical_limit_or_norm_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualEndpointEscape.maximal_finite_physical_limit_or_norm_escape
/-- info: 'FMSA.Convergence.ActualEndpointEscape.exists_mixture_hs_branch_with_sharp_endpoint_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualEndpointEscape.exists_mixture_hs_branch_with_sharp_endpoint_alternative
end FMSA.Convergence.ActualEndpointEscape
