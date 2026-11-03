import MSAConvergence.MixtureEndpointTaylorIdentification
import MSAConvergence.EventuallySignedTaylor
import MSAConvergence.NonnegativeAbelConverse

set_option linter.style.header false

/-! A finite left limit and eventual coefficient sign imply summability
at a positive endpoint. Applied to the actual maximal mixture branch,
this turns a sign hypothesis into an identified physical endpoint sum. -/
noncomputable section
namespace FMSA.Convergence.EventuallySignedEndpointSummation

open Filter Set
open FMSA.Convergence.EventuallySignedTaylor
open FMSA.Convergence.MixtureEndpointTaylorIdentification
open FMSA.Convergence.MixtureEndpointNoEscape
open FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.ActualAlgebraicEndpoint
open FMSA.Paper.StableIntervalRadius
open FMSA.Paper.TaylorRoot
open FMSA.Paper.FoldRadius
open FMSA.ExactMSA.MultiTailMixture
open scoped Topology BigOperators ENNReal

/-- Finite sign exceptions do not affect the Abel converse: the
positive tail partial sums are bounded by the interior left limit. -/
theorem summable_endpoint_of_eventually_nonnegative_coefficients
    (a : ℕ → ℝ) (f : ℝ → ℝ) (R L : ℝ) (m : ℕ) (hR : 0 < R)
    (ha : ∀ n, m ≤ n → 0 ≤ a n)
    (hinside : ∀ t ∈ Ico 0 R,
      HasSum (fun n => a n * t ^ n) (f t))
    (hlim : Tendsto f (𝓝[<] R) (𝓝 L)) :
    Summable (fun n => a n * R ^ n) := by
  let g : ℕ → ℝ := fun n => a (n + m) * R ^ (n + m)
  have hg0 (n : ℕ) : 0 ≤ g n := by
    exact mul_nonneg (ha (n + m) (by omega)) (pow_nonneg hR.le _)
  have hbound (n : ℕ) :
      ∑ i ∈ Finset.range n, g i ≤
        L - ∑ i ∈ Finset.range m, a i * R ^ i := by
    have hp : Continuous (fun t : ℝ =>
        ∑ i ∈ Finset.range n, a (i + m) * t ^ (i + m)) := by fun_prop
    have hh : Continuous (fun t : ℝ =>
        ∑ i ∈ Finset.range m, a i * t ^ i) := by fun_prop
    have hplim : Tendsto (fun t : ℝ =>
        ∑ i ∈ Finset.range n, a (i + m) * t ^ (i + m))
        (𝓝[<] R) (𝓝 (∑ i ∈ Finset.range n,
          a (i + m) * R ^ (i + m))) :=
      (hp.tendsto R).mono_left nhdsWithin_le_nhds
    have hrlim : Tendsto (fun t => f t -
        ∑ i ∈ Finset.range m, a i * t ^ i) (𝓝[<] R)
        (𝓝 (L - ∑ i ∈ Finset.range m, a i * R ^ i)) :=
      hlim.sub ((hh.tendsto R).mono_left nhdsWithin_le_nhds)
    have hle := le_of_tendsto_of_tendsto hplim hrlim (by
      filter_upwards [Ico_mem_nhdsLT hR] with t ht
      have hs := hinside t ht
      have htail : Summable (fun i => a (i + m) * t ^ (i + m)) :=
        (summable_nat_add_iff (f := fun n => a n * t ^ n) m).mpr hs.summable
      have hsum : (∑ i ∈ Finset.range m, a i * t ^ i) +
          ∑' i, a (i + m) * t ^ (i + m) = f t := by
        simpa [hs.tsum_eq] using hs.summable.sum_add_tsum_nat_add m
      have hnonneg (i : ℕ) : 0 ≤ a (i + m) * t ^ (i + m) :=
        mul_nonneg (ha (i + m) (by omega)) (pow_nonneg ht.1 _)
      have hpartial := htail.sum_le_tsum (Finset.range n) (fun i _ => hnonneg i)
      linarith)
    simpa only [g] using hle
  have hgs : Summable g := summable_of_sum_range_le hg0 hbound
  exact (summable_nat_add_iff (f := fun n => a n * R ^ n) m).mp
    (by simpa only [g] using hgs)

/-- Multiplying by a nonzero sign reduces eventual one-sign
coefficients to the nonnegative case. -/
theorem summable_endpoint_of_eventually_signed_coefficients
    (a : ℕ → ℝ) (f : ℝ → ℝ) (R L s : ℝ) (m : ℕ)
    (hR : 0 < R) (hs : s ≠ 0)
    (ha : ∀ n, m ≤ n → 0 ≤ s * a n)
    (hinside : ∀ t ∈ Ico 0 R,
      HasSum (fun n => a n * t ^ n) (f t))
    (hlim : Tendsto f (𝓝[<] R) (𝓝 L)) :
    Summable (fun n => a n * R ^ n) := by
  have hscaled : Summable (fun n => (s * a n) * R ^ n) := by
    apply summable_endpoint_of_eventually_nonnegative_coefficients
      (fun n => s * a n) (fun t => s * f t) R (s * L) m hR ha
    · intro t ht
      simpa only [mul_assoc] using (hinside t ht).mul_left s
    · exact tendsto_const_nhds.mul hlim
  have h := Summable.mul_left s⁻¹ hscaled
  have heq : (fun n => a n * R ^ n) =
      (fun n => s⁻¹ * (s * a n * R ^ n)) := by
    funext n
    simp [hs, mul_assoc]
  rw [heq]
  exact h

/-- For the constructed maximal physical mixture branch, eventual
one-sign coefficients turn its unique finite left limit into endpoint
summability. The resulting original-amplitude sum is precisely its
selected noncanonical Fourier-zero physical endpoint. -/
theorem maximal_mixture_endpoint_sum_of_eventual_component_signs
    {N : ℕ} {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤)
    (hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 ≤ s * (branchCoefficients M.path n).1 u i j)
    (hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 ≤ s * (branchCoefficients M.path n).2 u i j) :
    let b := M.bound.toReal
    let x := ∑' n, b ^ n • branchCoefficients M.path n
    Summable (fun n => b ^ n • branchCoefficients M.path n) ∧
      PhysicalEndpointLimit z rho sigma K M.path b x := by
  dsimp
  let b : ℝ := M.bound.toReal
  have hb : 0 < b := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) b := by
    rw [hbound, initial_couplings_ofReal b hb]
  have han : AnalyticOnNhd ℝ M.path (Ico (0 : ℝ) b) := by
    simpa only [hset] using M.analytic
  have hrad : M.bound ≤ amplitudeRadius (branchCoefficients M.path) := by
    rw [hbound]
    exact le_amplitudeRadius_of_eventually_signed_analytic_branch
      M.path b hb han hD hG
  have hbefore : AmplitudeHasSumBefore M.path M.bound :=
    (maximal_branch_taylor_criterion z rho sigma K seed M).mpr hrad
  obtain ⟨a, ha, _⟩ := maximal_finite_mixture_endpoint_unique_physical_limit
    z hz rho sigma hρ hσ hv K hK seed M hfinite
  have hlim : Tendsto M.path (𝓝[<] b) (𝓝 a) := ha.2.2.2.1
  have hlimD : Tendsto (fun t => (M.path t).1) (𝓝[<] b) (𝓝 a.1) :=
    (continuous_fst.tendsto a).comp hlim
  have hlimG : Tendsto (fun t => (M.path t).2) (𝓝[<] b) (𝓝 a.2) :=
    (continuous_snd.tendsto a).comp hlim
  have hsD (u : T) (i j : Fin N) : Summable (fun n =>
      (branchCoefficients M.path n).1 u i j * b ^ n) := by
    obtain ⟨s, hs, m, hsgn⟩ := hD u i j
    apply summable_endpoint_of_eventually_signed_coefficients
      (fun n => (branchCoefficients M.path n).1 u i j)
      (fun t => (M.path t).1 u i j) b (a.1 u i j) s m hb hs hsgn
    · intro t ht
      exact (hbefore t (by simpa only [hset] using ht)).1 u i j
    · exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp
        ((tendsto_pi_nhds.mp hlimD) u)) i)) j)
  have hsG (u : T) (i j : Fin N) : Summable (fun n =>
      (branchCoefficients M.path n).2 u i j * b ^ n) := by
    obtain ⟨s, hs, m, hsgn⟩ := hG u i j
    apply summable_endpoint_of_eventually_signed_coefficients
      (fun n => (branchCoefficients M.path n).2 u i j)
      (fun t => (M.path t).2 u i j) b (a.2 u i j) s m hb hs hsgn
    · intro t ht
      exact (hbefore t (by simpa only [hset] using ht)).2 u i j
    · exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp
        ((tendsto_pi_nhds.mp hlimG) u)) i)) j)
  have hsvec : Summable (fun n => b ^ n • branchCoefficients M.path n) := by
    have hd : Summable (fun n => (b ^ n • branchCoefficients M.path n).1) := by
      apply Pi.summable.mpr
      intro u
      apply Pi.summable.mpr
      intro i
      apply Pi.summable.mpr
      intro j
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hsD u i j
    have hg : Summable (fun n => (b ^ n • branchCoefficients M.path n).2) := by
      apply Pi.summable.mpr
      intro u
      apply Pi.summable.mpr
      intro i
      apply Pi.summable.mpr
      intro j
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hsG u i j
    exact (hd.hasSum.prodMk hg.hasSum).summable
  let x : TailMatrix T N × TailMatrix T N :=
    ∑' n, b ^ n • branchCoefficients M.path n
  have hDsum : ∀ u i j, HasSum
      (fun n => (branchCoefficients M.path n).1 u i j * b ^ n) (x.1 u i j) := by
    intro u i j
    let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.fst ℝ _ _)
    simpa [l, x, entry, Pi.smul_apply, smul_eq_mul, mul_comm] using
      l.hasSum hsvec.hasSum
  have hGsum : ∀ u i j, HasSum
      (fun n => (branchCoefficients M.path n).2 u i j * b ^ n) (x.2 u i j) := by
    intro u i j
    let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.snd ℝ _ _)
    simpa [l, x, entry, Pi.smul_apply, smul_eq_mul, mul_comm] using
      l.hasSum hsvec.hasSum
  exact ⟨hsvec, maximal_endpoint_taylor_sum_is_physical_limit
    z hz rho sigma hρ hσ hv K hK seed M hfinite x hDsum hGsum⟩

end FMSA.Convergence.EventuallySignedEndpointSummation

/-- info: 'FMSA.Convergence.EventuallySignedEndpointSummation.summable_endpoint_of_eventually_nonnegative_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedEndpointSummation.summable_endpoint_of_eventually_nonnegative_coefficients
/-- info: 'FMSA.Convergence.EventuallySignedEndpointSummation.summable_endpoint_of_eventually_signed_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedEndpointSummation.summable_endpoint_of_eventually_signed_coefficients
/-- info: 'FMSA.Convergence.EventuallySignedEndpointSummation.maximal_mixture_endpoint_sum_of_eventual_component_signs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedEndpointSummation.maximal_mixture_endpoint_sum_of_eventual_component_signs
