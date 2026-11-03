import MSAConvergence.MixtureEndpointNoEscape
import FMSAPaper.AbelEndpoint

set_option linter.style.header false

/-! Conditional Taylor summation at a finite canonical mixture endpoint:
if every ORIGINAL amplitude component sums there, Abel identifies the sum
with the unique selected physical Fourier-zero endpoint root. -/
noncomputable section
open Filter Topology Set Real
namespace FMSA.Convergence.MixtureEndpointTaylorIdentification
open FMSA.Paper FMSA.Paper.Abel FMSA.Paper.StableIntervalRadius
open FMSA.Paper.TaylorRoot FMSA.Paper.FoldRadius
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.MixtureEndpointNoEscape
open FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.ActualAlgebraicEndpoint
open FMSA.Convergence.MixtureHSCanonicity
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Abel's theorem at an arbitrary positive endpoint, including conditional
convergence of the coefficient series at that endpoint. -/
theorem coordinatewise_abel_at_pos (a : ℕ → ℝ) (b y : ℝ)
    (hb : 0 < b) (hs : HasSum (fun n => a n * b ^ n) y) :
    Tendsto (fun t : ℝ => ∑' n, a n * t ^ n) (𝓝[<] b) (𝓝 y) := by
  have hscale : Tendsto (fun t : ℝ => t/b) (𝓝[<] b) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert (tendsto_id.mono_left nhdsWithin_le_nhds).div_const b using 1 <;> norm_num [hb.ne']
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (div_lt_one hb).mpr ht
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hs.tendsto_sum_nat
  have h := hab.comp hscale
  convert h using 1
  funext t
  congr 1
  funext n
  have hmul : b*(t/b)=t := by field_simp [hb.ne']
  calc
    a n*t^n = a n*(b*(t/b))^n := by rw [hmul]
    _ = a n*b^n*(t/b)^n := by rw [mul_pow]; ring

omit [Fintype T] in
/-- Abel convergence of the full original amplitude vector at any positive
coupling, even if component endpoint convergence is only conditional. -/
theorem amplitudeSeries_abel_at_pos
    (a : ℕ → TailMatrix T N × TailMatrix T N) (b : ℝ) (x : TailMatrix T N × TailMatrix T N)
    (hb : 0 < b)
    (hD : ∀ u i j, HasSum (fun n => (a n).1 u i j * b ^ n) (x.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (a n).2 u i j * b ^ n) (x.2 u i j)) :
    Tendsto (amplitudeSeries a) (𝓝[<] b) (𝓝 x) := by
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro u
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact coordinatewise_abel_at_pos _ b _ hb (hD u i j)
  · apply tendsto_pi_nhds.mpr
    intro u
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact coordinatewise_abel_at_pos _ b _ hb (hG u i j)

omit [Fintype T] in
/-- Componentwise convergence at a positive real endpoint bounds the
intrinsic common amplitude radius below by that endpoint. -/
theorem endpoint_sums_bound_radius
    (a : ℕ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hb : 0 ≤ b) (x : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum (fun n => (a n).1 u i j * b ^ n) (x.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (a n).2 u i j * b ^ n) (x.2 u i j)) :
    ENNReal.ofReal b ≤ amplitudeRadius a := by
  apply le_iInf
  intro u
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_min
  · exact radius_bound_of_summable_at _ b hb (hD u i j).summable
  · exact radius_bound_of_summable_at _ b hb (hG u i j).summable

/-- If all original amplitude Taylor series converge at a finite maximal
canonical mixture endpoint, their vector sum is exactly its unique selected
physical Fourier-zero limiting root. Endpoint convergence is a premise. -/
theorem maximal_endpoint_taylor_sum_is_physical_limit
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤)
    (x : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum
      (fun n => (branchCoefficients M.path n).1 u i j * M.bound.toReal ^ n) (x.1 u i j))
    (hG : ∀ u i j, HasSum
      (fun n => (branchCoefficients M.path n).2 u i j * M.bound.toReal ^ n) (x.2 u i j)) :
    PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal x := by
  let b : ℝ := M.bound.toReal
  have hb : 0 < b := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal b := (ENNReal.ofReal_toReal hfinite).symm
  have hrad : M.bound ≤ amplitudeRadius (branchCoefficients M.path) := by
    rw [hbound]
    exact endpoint_sums_bound_radius _ b hb.le x hD hG
  have hsum := (maximal_branch_taylor_criterion z rho sigma K seed M).mpr hrad
  have hset : initialCouplings M.bound = Ico (0 : ℝ) b := by
    rw [hbound, initial_couplings_ofReal b hb]
  have heq : ∀ t ∈ Ico (0 : ℝ) b,
      M.path t = amplitudeSeries (branchCoefficients M.path) t := by
    intro t ht
    have htM : t ∈ initialCouplings M.bound := by simpa only [hset] using ht
    obtain ⟨hsD,hsG⟩ := hsum t htM
    apply Prod.ext
    · funext u i j
      exact (hsD u i j).tsum_eq.symm
    · funext u i j
      exact (hsG u i j).tsum_eq.symm
  have hevent : M.path =ᶠ[𝓝[<] b] amplitudeSeries (branchCoefficients M.path) := by
    have hpos : ∀ᶠ t : ℝ in 𝓝[<] b, 0 < t :=
      (show ∀ᶠ t : ℝ in 𝓝 b, 0 < t from Ioi_mem_nhds hb).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hpos,self_mem_nhdsWithin] with t ht0 htb
    exact heq t ⟨ht0.le,htb⟩
  have hab := amplitudeSeries_abel_at_pos (branchCoefficients M.path) b x hb hD hG
  have hleft : Tendsto M.path (𝓝[<] b) (𝓝 x) := hab.congr' hevent.symm
  obtain ⟨a,ha,_hu⟩ := maximal_finite_mixture_endpoint_unique_physical_limit
    z hz rho sigma hρ hσ hv K hK seed M hfinite
  have heqxa : x = a := tendsto_nhds_unique hleft ha.2.2.2.1
  simpa only [heqxa] using ha

/-- A strictly larger intrinsic Taylor radius guarantees actual summation
at the excluded finite canonical endpoint, to its physical Fourier-zero
limit. The strict radius inequality is a premise, not inferred from real
canonicity. -/
theorem maximal_strict_radius_endpoint_series_is_physical_limit
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤)
    (hrad : M.bound < amplitudeRadius (branchCoefficients M.path)) :
    PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal
      (amplitudeSeries (branchCoefficients M.path) M.bound.toReal) := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hrad' : ENNReal.ofReal M.bound.toReal <
      amplitudeRadius (branchCoefficients M.path) := by
    simpa only [ENNReal.ofReal_toReal hfinite] using hrad
  obtain ⟨hD,hG⟩ := hasSum_inside_amplitudeRadius
    (branchCoefficients M.path) M.bound.toReal hb.le hrad'
  exact maximal_endpoint_taylor_sum_is_physical_limit z hz rho sigma
    hρ hσ hv K hK seed M hfinite _ hD hG

/-- From physical HS mixture data alone, construct the initial maximal
canonical branch and identify any componentwise convergent Taylor sum at
its finite endpoint with the selected noncanonical Fourier-zero MSA root. -/
theorem exists_mixture_hs_branch_with_conditional_endpoint_sum
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ → ∀ x : TailMatrix T N × TailMatrix T N,
        (∀ u i j, HasSum
          (fun n => (branchCoefficients M.path n).1 u i j * M.bound.toReal ^ n) (x.1 u i j)) →
        (∀ u i j, HasSum
          (fun n => (branchCoefficients M.path n).2 u i j * M.bound.toReal ^ n) (x.2 u i j)) →
        PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal x) := by
  obtain ⟨M,hM⟩ := exists_mixture_hs_maximal_branch z hz rho sigma hσ hρ K hK hv
  refine ⟨M,hM,fun hfinite x hD hG => ?_⟩
  exact maximal_endpoint_taylor_sum_is_physical_limit z hz rho sigma hρ hσ
    hv.ne' K hK _ M hfinite x hD hG

end FMSA.Convergence.MixtureEndpointTaylorIdentification
/-- info: 'FMSA.Convergence.MixtureEndpointTaylorIdentification.coordinatewise_abel_at_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointTaylorIdentification.coordinatewise_abel_at_pos
/-- info: 'FMSA.Convergence.MixtureEndpointTaylorIdentification.amplitudeSeries_abel_at_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointTaylorIdentification.amplitudeSeries_abel_at_pos
/-- info: 'FMSA.Convergence.MixtureEndpointTaylorIdentification.endpoint_sums_bound_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointTaylorIdentification.endpoint_sums_bound_radius
/-- info: 'FMSA.Convergence.MixtureEndpointTaylorIdentification.maximal_endpoint_taylor_sum_is_physical_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointTaylorIdentification.maximal_endpoint_taylor_sum_is_physical_limit
/-- info: 'FMSA.Convergence.MixtureEndpointTaylorIdentification.maximal_strict_radius_endpoint_series_is_physical_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointTaylorIdentification.maximal_strict_radius_endpoint_series_is_physical_limit
/-- info: 'FMSA.Convergence.MixtureEndpointTaylorIdentification.exists_mixture_hs_branch_with_conditional_endpoint_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointTaylorIdentification.exists_mixture_hs_branch_with_conditional_endpoint_sum
