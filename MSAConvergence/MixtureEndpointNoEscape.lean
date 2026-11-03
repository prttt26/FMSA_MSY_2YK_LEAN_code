import MSAConvergence.TracerActiveGUniform
import MSAConvergence.ActualAlgebraicEndpoint
import MSAConvergence.EndpointEscape
import MSAConvergence.MixtureHSCanonicity
import MSAConvergence.ActualRadialTangentOZ
import MSAConvergence.CanonicalFirstLoss
import MSAConvergence.MixtureAxisHighFrequency
import MSAConvergence.MixtureCoefficientBudget

set_option linter.style.header false

/-! Every finite endpoint of the actual HS-seeded maximal canonical branch
of a finite physical mixture has a unique physical Fourier-zero limit.
The amplitude bound is proved from the actual MSA equations and canonicity. -/
noncomputable section
open Set Real Filter Topology
namespace FMSA.Convergence.MixtureEndpointNoEscape
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.ActualAlgebraicEndpoint
open FMSA.Convergence.EndpointEscape
open FMSA.Convergence.MixtureHSCanonicity
open FMSA.Convergence.TracerActiveGUniform
open FMSA.Convergence.ActualRadialTangentOZ
open FMSA.Convergence.CanonicalFirstLoss
open FMSA.Convergence.RegularEndpointContinuation
open FMSA.Convergence.MixtureAxisHighFrequency
open FMSA.Convergence.MixtureCoefficientBudget
variable {N : ℕ} {T : Type*} [Fintype T]

/-- A finite family of strictly positive diameters has a common positive
test radius below each diameter, including the empty species family. -/
theorem exists_uniform_test_radius (sigma : Fin N → ℝ)
    (hσ : ∀ i, 0 < sigma i) :
    ∃ R : ℝ, 0 < R ∧ ∀ i, R < sigma i := by
  classical
  by_cases hN : Nonempty (Fin N)
  · obtain ⟨a,_,ha⟩ := Finset.exists_min_image Finset.univ sigma
      ⟨Classical.choice hN,Finset.mem_univ _⟩
    refine ⟨sigma a/2,by linarith [hσ a],?_⟩
    intro i
    have hi := ha i (Finset.mem_univ i)
    linarith [hσ a]
  · refine ⟨1,by norm_num,?_⟩
    intro i
    exact False.elim (hN ⟨i⟩)

/-- Full original-pair properness stated directly from finite physical
mixture data: no auxiliary test radius is supplied by the caller. -/
theorem actual_full_mixture_amplitude_properness_from_data
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re →
        IsUnit (FMSA.Convergence.CanonicalInverseCovariance.causalFactor
          z rho sigma D G s)) →
      ‖(D,G)‖ ≤ M := by
  obtain ⟨R,hR,hRσ⟩ := exists_uniform_test_radius sigma hσ
  exact actual_full_mixture_amplitude_properness
    z hz rho sigma hρ hσ hv R hR hRσ B

/-- At a physical mixture state, `etaMix < 1` supplies the nonzero free
volume needed by the actual original-amplitude properness theorem. -/
theorem actual_full_mixture_amplitude_properness_at_eta_lt_one
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re →
        IsUnit (FMSA.Convergence.CanonicalInverseCovariance.causalFactor
          z rho sigma D G s)) →
      ‖(D,G)‖ ≤ M := by
  have hv : vacMix rho sigma ≠ 0 := by
    unfold vacMix
    linarith
  exact actual_full_mixture_amplitude_properness_from_data
    z hz rho sigma hρ hσ hv B

/-- Finite canonical mixture prefix noescape, with the auxiliary exterior
test radius eliminated for every finite positive-diameter species family. -/
theorem no_finite_mixture_amplitude_escape_from_data
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (FMSA.Convergence.CanonicalInverseCovariance.causalFactor
        z rho sigma (p t).1 (p t).2 s)) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  obtain ⟨R,hR,hRσ⟩ := exists_uniform_test_radius sigma hσ
  exact no_finite_mixture_amplitude_escape z hz rho sigma hρ hσ hv
    R hR hRσ K hK p b hb hroot hcanon

/-- Every original amplitude on a finite canonical physical mixture prefix
has one common bound, including retained zero-density tracer entries. -/
theorem canonical_mixture_prefix_uniform_bound_at_eta_lt_one
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b : ℝ)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (FMSA.Convergence.CanonicalInverseCovariance.causalFactor
        z rho sigma (p t).1 (p t).2 s)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := actual_full_mixture_amplitude_properness_at_eta_lt_one
    z hz rho sigma hρ hσ hη (b*‖K‖)
  refine ⟨M,hM,?_⟩
  intro t ht
  have hKt : ‖t • K‖ ≤ b*‖K‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
  have hKtSym : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hK u i j]
  exact hbound (t • K) (p t).1 (p t).2 hKt hKtSym
    (hroot t ht) (hcanon t ht)

/-- A continuous HS-seeded actual mixture root prefix with no physical
Fourier zero on the real axis has uniformly bounded original amplitudes.
Full half-plane canonicity is derived from the zero-free path and HS seed. -/
theorem hs_axis_zero_free_prefix_uniform_amplitude_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (haxis : ∀ t ∈ Ico 0 b, ∀ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k).det ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B := by
  have hv : 0 < vacMix rho sigma := by
    unfold vacMix
    linarith
  obtain ⟨M,_⟩ := exists_mixture_hs_maximal_branch
    z hz rho sigma hσ hρ K hK hv
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound :=
    ⟨le_rfl,by simpa using M.positive⟩
  have hseed : p 0 ∈ canonicalAmplitudes z rho sigma := by
    rw [hp0,← M.at_seed]
    exact M.canonical 0 h0
  have hF : ∀ t ∈ Ico (0 : ℝ) b, ∀ k : ℝ, IsUnit
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k) := by
    intro t ht k
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (haxis t ht k))
  have hcanon : ∀ t ∈ Ico (0 : ℝ) b,
      p t ∈ canonicalAmplitudes z rho sigma :=
    canonical_path_of_physical_factor_units z hz rho sigma
      (fun i => (hσ i).le) hρ p (Ico 0 b) 0
      (convex_Ico 0 b).isPreconnected ⟨le_rfl,hb⟩ hp hseed hF
  exact canonical_mixture_prefix_uniform_bound_at_eta_lt_one
    z hz rho sigma hρ hσ hη K hK p b hroot hcanon

/-- A finite-frequency coefficient certificate rules out finite original
amplitude escape on a continuous actual HS-seeded mixture root prefix.
No endpoint value, zero, or closed-path extension is assumed. -/
theorem hs_coefficient_certificate_uniform_amplitude_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ t ∈ Ico 0 b, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Abar j)
    (hQ : ∀ t ∈ Ico 0 b, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qbar i j)
    (hW : ∀ t ∈ Ico 0 b, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wbar u i j)
    (hC : ∀ t ∈ Ico 0 b, ∀ u i j,
      |FMSA.ExactMSA.MultiTailMixture.C z rho sigma
        (p t).1 (p t).2 u i j| ≤ Cbar u i j)
    (hcompact : ∀ t ∈ Ico 0 b, ∀ k : ℝ,
      |k| ≤ rateCutoff z + explicitBudget z rho sigma Abar Qbar Wbar Cbar + 1 →
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k).det ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B := by
  have haxis := path_axis_zero_free_of_coefficient_caps
    z hz rho sigma hρ (fun i => (hσ i).le) p (Ico 0 b)
    Abar Qbar Wbar Cbar hA hQ hW hC hcompact
  exact hs_axis_zero_free_prefix_uniform_amplitude_bound
    z hz rho sigma hρ hσ hη K hK p b hb hp0 hp hroot haxis

/-- No finite original-amplitude escape on a canonical physical mixture
prefix when packing fraction is below one. No continuity is required. -/
theorem no_finite_mixture_amplitude_escape_at_eta_lt_one
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (FMSA.Convergence.CanonicalInverseCovariance.causalFactor
        z rho sigma (p t).1 (p t).2 s)) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  obtain ⟨M,_hM,hbound⟩ := canonical_mixture_prefix_uniform_bound_at_eta_lt_one
    z hz rho sigma hρ hσ hη K hK p b hroot hcanon
  intro hescape
  obtain ⟨t,ht,_hc,hlarge⟩ := hescape M 0 hb
  exact (not_lt_of_ge (hbound t ht)) hlarge

/-- The original amplitudes on a finite maximal canonical mixture prefix
have one global norm bound. It is derived from bounded K, not supplied. -/
theorem maximal_finite_mixture_prefix_bounded
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 M.bound.toReal, ‖M.path t‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := actual_full_mixture_amplitude_properness_from_data
    z hz rho sigma hρ hσ hv (M.bound.toReal*‖K‖)
  have hboundReal : M.bound = ENNReal.ofReal M.bound.toReal :=
    (ENNReal.ofReal_toReal hfinite).symm
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hboundReal).trans (initial_couplings_ofReal _ hb)
  refine ⟨B,hB,?_⟩
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hKt : ‖t • K‖ ≤ M.bound.toReal*‖K‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
  have hKtSym : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hK u i j]
  have hmem : t ∈ initialCouplings M.bound := by simpa only [hset] using ht
  have hroot := M.roots t hmem
  have hcanon := M.canonical t hmem
  exact hbound (t • K) (M.path t).1 (M.path t).2 hKt hKtSym
    hroot (fun s hs => hcanon s hs)

/-- Every continuous canonical original mixture root prefix ending at a
finite positive coupling has a unique full finite left limit. Maximality,
endpoint canonicity and endpoint root isolation are not assumed. -/
theorem actual_canonical_mixture_prefix_has_unique_finite_limit
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    ∃! a, Tendsto p (𝓝[<] b) (𝓝 a) := by
  have hcanonFactor : ∀ t ∈ Ico 0 b, ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (FMSA.Convergence.CanonicalInverseCovariance.causalFactor
        z rho sigma (p t).1 (p t).2 s) := by
    intro t ht s hs
    exact hcanon t ht s hs
  have hno := no_finite_mixture_amplitude_escape_from_data
    z hz rho sigma hρ hσ hv K hK p b hb hroot hcanonFactor
  rcases full_limit_or_norm_escape p b hb
      (actual_canonical_prefix_cluster_has_limit z hz rho sigma hσ hρ
        K hK hv p b hb hp hroot hcanon) with ⟨a,ha⟩|he
  · refine ⟨a,ha,?_⟩
    intro d hd
    exact tendsto_nhds_unique hd ha
  · exfalso
    apply hno
    intro B c hc
    have hnear : ∀ᶠ t : ℝ in 𝓝[<] b, max 0 c < t :=
      (show ∀ᶠ t : ℝ in 𝓝 b, max 0 c < t from Ioi_mem_nhds (max_lt hb hc)).filter_mono
        nhdsWithin_le_nhds
    have hbelow : ∀ᶠ t : ℝ in 𝓝[<] b, t < b := self_mem_nhdsWithin
    have hlarge : ∀ᶠ t : ℝ in 𝓝[<] b, B < ‖p t‖ :=
      ((tendsto_atTop.mp he) (B+1)).mono (fun t ht => by linarith)
    obtain ⟨t,htnear,htbelow,htlarge⟩ :=
      (hnear.and (hbelow.and hlarge)).exists
    exact ⟨t,⟨(le_max_left 0 c).trans htnear.le,htbelow⟩,
      (le_max_right 0 c).trans_lt htnear,htlarge⟩

/-- The noescape bound controls the high-frequency physical factor both
throughout a finite canonical mixture prefix and at its selected left limit.
No closed-path extension or endpoint root equation is assumed. -/
theorem canonical_mixture_prefix_and_endpoint_uniform_axis_cutoff_at_eta_lt_one
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ R : ℝ,
      Tendsto p (𝓝[<] b) (𝓝 a) ∧ 0 < R ∧
      (∀ t ∈ Ico 0 b, ∀ k : ℝ, R ≤ |k| →
        IsUnit (fourierFactor z rho sigma
          (amplitudeA z rho sigma (p t).1 (p t).2)
          (amplitudeQp z rho sigma (p t).1 (p t).2)
          (W z rho (p t).1 (p t).2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
            (p t).1 (p t).2) k)) ∧
      (∀ k : ℝ, R ≤ |k| →
        IsUnit (fourierFactor z rho sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k)) := by
  have hv : vacMix rho sigma ≠ 0 := by
    unfold vacMix
    linarith
  obtain ⟨a,ha,_⟩ := actual_canonical_mixture_prefix_has_unique_finite_limit
    z hz rho sigma hρ hσ hv K hK p b hb hp hroot hcanon
  obtain ⟨M,_hM,hbound⟩ := canonical_mixture_prefix_uniform_bound_at_eta_lt_one
    z hz rho sigma hρ hσ hη K hK p b hroot
    (fun t ht s hs => hcanon t ht s hs)
  have hprefix : ∀ᶠ t : ℝ in 𝓝[<] b, t ∈ Ico 0 b := by
    have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] b :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)
    filter_upwards [hpos, self_mem_nhdsWithin] with t ht0 htb
    exact ⟨ht0.le,htb⟩
  have haNorm : ‖a‖ ≤ M :=
    le_of_tendsto ((continuous_norm.tendsto a).comp ha)
      (hprefix.mono (fun t ht => hbound t ht))
  obtain ⟨B,hB,hbudget⟩ := exists_budget_bound_on_amplitude_ball
    z rho sigma M
  let R : ℝ := rateCutoff z + B + 1
  have hR : 0 < R := by
    have hrate := (cutoff_nonneg z rho sigma a).1
    dsimp only [R]
    linarith
  refine ⟨a,R,ha,hR,?_,?_⟩
  · exact path_physical_factor_unit_above_cutoff z hz rho sigma hρ
      (fun i => (hσ i).le) p (Ico 0 b) B
      (fun t ht => hbudget (p t) (hbound t ht))
  · intro k hk
    apply physical_factor_unit_at_high_frequency z hz rho sigma hρ
      (fun i => (hσ i).le) a k
    unfold safeCutoff
    dsimp only [R] at hk
    linarith [hbudget a haNorm]

/-- Full canonicity of an original mixture amplitude prefix excludes every
real-frequency physical Fourier zero at every point of that prefix. -/
theorem canonical_mixture_prefix_no_physical_axis_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    ∀ t ∈ Ico 0 b, ∀ k : ℝ,
      (fourierFactor z rho sigma (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma (p t).1 (p t).2) k).det ≠ 0 := by
  intro t ht k
  have hunit := physical_fourier_factor_unit_of_kernel_unit z rho sigma hρ (p t) k
    (hcanon t ht (Complex.I*k) (by simp))
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- At every finite endpoint of the constructed maximal canonical mixture
branch, the original amplitude path has a unique full physical limit. The
limit is an actual MSA root with a real Fourier zero and is not canonical. -/
theorem maximal_finite_mixture_endpoint_unique_physical_limit
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃! a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a := by
  obtain ⟨B,_hB,hbound⟩ := maximal_finite_mixture_prefix_bounded
    z hz rho sigma hρ hσ hv K hK seed M hfinite
  obtain ⟨a,ha⟩ := maximal_bounded_endpoint_has_limit z hz rho sigma hσ hρ
    K hK hv seed M hfinite B hbound
  refine ⟨a,ha,?_⟩
  rintro d ⟨_hr,_hcl,_hnc,hd,_hz⟩
  exact tendsto_nhds_unique hd ha.2.2.2.1

/-- The finite maximal canonical mixture endpoint is the FIRST physical
Fourier-axis loss along its selected initial branch: all earlier branch
states are zero-free at every real frequency, and the unique endpoint
limit is an actual root with a real-frequency zero. -/
theorem maximal_finite_mixture_endpoint_first_physical_axis_loss
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    (∀ t ∈ Ico 0 M.bound.toReal, ∀ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (M.path t).1 (M.path t).2)
        (amplitudeQp z rho sigma (M.path t).1 (M.path t).2)
        (W z rho (M.path t).1 (M.path t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (M.path t).1 (M.path t).2) k).det ≠ 0) ∧
      ∃! a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal :=
    (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  refine ⟨canonical_mixture_prefix_no_physical_axis_zero z rho sigma hρ
    M.path M.bound.toReal ?_,
    maximal_finite_mixture_endpoint_unique_physical_limit
      z hz rho sigma hρ hσ hv K hK seed M hfinite⟩
  intro t ht
  exact M.canonical t (by simpa only [hset] using ht)

/-- At a finite maximal endpoint, one frequency cutoff works throughout
the canonical prefix and at its selected physical limit. Every endpoint
Fourier zero lies strictly below this cutoff. -/
theorem maximal_finite_mixture_endpoint_zero_in_uniform_frequency_window
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ R : ℝ,
      PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a ∧
      0 < R ∧
      (∀ t ∈ Ico 0 M.bound.toReal, ∀ k : ℝ, R ≤ |k| →
        IsUnit (fourierFactor z rho sigma
          (amplitudeA z rho sigma (M.path t).1 (M.path t).2)
          (amplitudeQp z rho sigma (M.path t).1 (M.path t).2)
          (W z rho (M.path t).1 (M.path t).2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
            (M.path t).1 (M.path t).2) k)) ∧
      (∀ k : ℝ, R ≤ |k| →
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det ≠ 0) ∧
      (∃ k : ℝ, |k| < R ∧
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det = 0) := by
  have hb : 0 < M.bound.toReal :=
    ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal :=
    (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  obtain ⟨a,R,ha,hR,hprefix,hend⟩ :=
    canonical_mixture_prefix_and_endpoint_uniform_axis_cutoff_at_eta_lt_one
      z hz rho sigma hρ hσ hη K hK M.path M.bound.toReal hb
      (by simpa only [hset] using M.analytic.continuousOn)
      (fun t ht => M.roots t (by simpa only [hset] using ht))
      (fun t ht => M.canonical t (by simpa only [hset] using ht))
  have hv : vacMix rho sigma ≠ 0 := by
    unfold vacMix
    linarith
  obtain ⟨a',hphys,_⟩ :=
    maximal_finite_mixture_endpoint_unique_physical_limit
      z hz rho sigma hρ hσ hv K hK seed M hfinite
  have heq : a = a' := tendsto_nhds_unique ha hphys.2.2.2.1
  subst a'
  obtain ⟨k,hzero⟩ := hphys.2.2.2.2
  have hk : |k| < R := by
    by_contra hn
    have hu := hend k (le_of_not_gt hn)
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)) hzero
  refine ⟨a,R,hphys,hR,hprefix,?_,k,hk,hzero⟩
  intro v hvR
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (hend v hvR))

/-- The selected finite maximal mixture endpoint has a nonempty compact
set of real physical Fourier zeros, with no uniqueness assumption on their
wave numbers. -/
theorem maximal_finite_mixture_endpoint_zero_set_compact_nonempty
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃ a : TailMatrix T N × TailMatrix T N,
      PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a ∧
      IsCompact {k : ℝ |
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det = 0} ∧
      Set.Nonempty {k : ℝ |
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det = 0} := by
  obtain ⟨a,ha,_⟩ := maximal_finite_mixture_endpoint_unique_physical_limit
    z hz rho sigma hρ hσ hv K hK seed M hfinite
  obtain ⟨k,hk⟩ := ha.2.2.2.2
  exact ⟨a,ha,
    physical_fourier_zero_set_isCompact z hz rho sigma hρ
      (fun i => (hσ i).le) a,
    ⟨k,hk⟩⟩

/-- A finite selected physical endpoint has a least nonnegative real
Fourier-zero wave number. The least value may be attained by several modes;
it is zero exactly when the endpoint's zero mode is present. -/
theorem maximal_finite_mixture_endpoint_has_minimal_nonnegative_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃ a : TailMatrix T N × TailMatrix T N, ∃ k₀ : ℝ,
      PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a ∧
      0 ≤ k₀ ∧
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2)
        (W z rho a.1 a.2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k₀).det = 0 ∧
      (∀ k : ℝ,
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det = 0 →
          k₀ ≤ |k|) ∧
      (k₀ = 0 ↔
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) 0).det = 0) := by
  obtain ⟨a,ha,_⟩ := maximal_finite_mixture_endpoint_unique_physical_limit
    z hz rho sigma hρ hσ hv K hK seed M hfinite
  obtain ⟨k₀,hk₀,hzero,hmin⟩ := physical_fourier_nonnegative_zero_minimum
    z hz rho sigma hρ (fun i => (hσ i).le) a ha.2.2.2.2
  refine ⟨a,k₀,ha,hk₀,hzero,hmin,?_⟩
  constructor
  · intro heq
    simpa only [heq] using hzero
  · intro h0
    have hle : k₀ ≤ 0 := by simpa using hmin 0 h0
    exact le_antisymm hle hk₀

/-- Physical data with packing fraction below one construct a maximal
HS-seeded branch. Every finite endpoint has a unique actual physical
Fourier-zero limiting root; no amplitude bound or root path is supplied. -/
theorem exists_mixture_hs_maximal_branch_with_finite_endpoint_limit
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : 0 < vacMix rho sigma)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ → 0 < M.bound.toReal ∧
        ∃! a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a) := by
  obtain ⟨M,hM⟩ := exists_mixture_hs_maximal_branch z hz rho sigma hσ hρ K hK hv
  refine ⟨M,hM,fun hfinite => ⟨ENNReal.toReal_pos (ne_of_gt M.positive) hfinite,?_⟩⟩
  exact maximal_finite_mixture_endpoint_unique_physical_limit z hz rho sigma
    hρ hσ hv.ne' K hK _ M hfinite

/-- The physical packing condition gives the HS-seeded maximal mixture
branch directly. Every finite endpoint has one selected physical
Fourier-zero limit of the original amplitudes, including retained tracers. -/
theorem exists_mixture_hs_maximal_branch_with_finite_endpoint_limit_at_eta_lt_one
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ → 0 < M.bound.toReal ∧
        ∃! a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a) := by
  have hv : 0 < vacMix rho sigma := by
    unfold vacMix
    linarith
  exact exists_mixture_hs_maximal_branch_with_finite_endpoint_limit
    z hz rho sigma hρ hσ hv K hK

/-- Physical data construct the unique HS-seeded maximal initial branch.
If its endpoint is finite, that endpoint is its first real-frequency
physical Fourier zero, with a unique selected actual MSA limit. -/
theorem exists_mixture_hs_maximal_branch_with_first_axis_loss_at_eta_lt_one
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ →
        (∀ t ∈ Ico 0 M.bound.toReal, ∀ k : ℝ,
          (fourierFactor z rho sigma
            (amplitudeA z rho sigma (M.path t).1 (M.path t).2)
            (amplitudeQp z rho sigma (M.path t).1 (M.path t).2)
            (W z rho (M.path t).1 (M.path t).2)
            (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
              (M.path t).1 (M.path t).2) k).det ≠ 0) ∧
        ∃! a, PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a) := by
  obtain ⟨M,hM,_⟩ := exists_mixture_hs_maximal_branch_with_finite_endpoint_limit_at_eta_lt_one
    z hz rho sigma hρ hσ hη K hK
  refine ⟨M,hM,fun hf => ?_⟩
  have hv : vacMix rho sigma ≠ 0 := by
    unfold vacMix
    linarith
  exact maximal_finite_mixture_endpoint_first_physical_axis_loss
    z hz rho sigma hρ hσ hv K hK _ M hf

/-- Converse identification of a supplied same-seed physical first-loss
certificate. If a continuous actual root prefix has no real Fourier zero
before `b` and has a finite left limit with a real Fourier zero at `b`,
then the constructed maximal initial canonical endpoint is exactly `b`.
No endpoint root equation or global continuation is assumed of the caller. -/
theorem supplied_first_physical_axis_loss_eq_maximal_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i)
    (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = seed) (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (haxis : ∀ t ∈ Ico 0 b, ∀ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k).det ≠ 0)
    (hleft : Tendsto p (𝓝[<] b) (𝓝 (p b)))
    (hzero : ∃ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p b).1 (p b).2)
        (amplitudeQp z rho sigma (p b).1 (p b).2)
        (W z rho (p b).1 (p b).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p b).1 (p b).2) k).det = 0) :
    M.bound = ENNReal.ofReal b := by
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound :=
    ⟨le_rfl,by simpa using M.positive⟩
  have hseed : p 0 ∈ canonicalAmplitudes z rho sigma := by
    rw [hp0]
    rw [← M.at_seed]
    exact M.canonical 0 h0
  have hF : ∀ t ∈ Ico (0 : ℝ) b, ∀ k : ℝ, IsUnit
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k) := by
    intro t ht k
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (haxis t ht k))
  have hcanon : ∀ t ∈ Ico (0 : ℝ) b,
      p t ∈ canonicalAmplitudes z rho sigma :=
    canonical_path_of_physical_factor_units z hz rho sigma
      (fun i => (hσ i).le) hρ p (Ico 0 b) 0
      (convex_Ico 0 b).isPreconnected ⟨le_rfl,hb⟩ hp hseed hF
  let P : CanonicalPrefix z rho sigma K seed :=
    ⟨b,hb,p,hp0,hp,hroot,hcanon⟩
  have hle : ENNReal.ofReal b ≤ M.bound := (M.maximal P).1
  apply le_antisymm
  · by_contra hn
    have hlt : ENNReal.ofReal b < M.bound := lt_of_not_ge hn
    have hbM : b ∈ initialCouplings M.bound := ⟨hb.le,hlt⟩
    have hMlim : Tendsto M.path (𝓝[<] b) (𝓝 (M.path b)) :=
      ((M.analytic b hbM).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hevent : M.path =ᶠ[𝓝[<] b] p := by
      have hpos : ∀ᶠ t : ℝ in 𝓝[<] b, 0 < t :=
        (show ∀ᶠ t : ℝ in 𝓝 b, 0 < t from Ioi_mem_nhds hb).filter_mono
          nhdsWithin_le_nhds
      filter_upwards [hpos,self_mem_nhdsWithin] with t ht0 htb
      exact (M.maximal P).2 ⟨ht0.le,htb⟩
    have heq : M.path b = p b :=
      tendsto_nhds_unique hMlim (hleft.congr' hevent.symm)
    have hnc : p b ∉ canonicalAmplitudes z rho sigma :=
      physical_zero_not_canonical z rho sigma hρ (p b) hzero
    have hc := M.canonical b hbM
    rw [heq] at hc
    exact hnc hc
  · exact hle

/-- A same-seed canonical prefix reaching the maximal finite bound has the
same selected physical endpoint as the maximal branch whenever it has a
full left limit. The supplied limit is therefore an original MSA root. -/
theorem canonical_prefix_left_limit_is_selected_physical_endpoint
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed)
    (P : CanonicalPrefix z rho sigma K seed)
    (hbound : M.bound = ENNReal.ofReal P.stop)
    (a : TailMatrix T N × TailMatrix T N)
    (hleft : Tendsto P.path (𝓝[<] P.stop) (𝓝 a)) :
    PhysicalEndpointLimit z rho sigma K M.path P.stop a := by
  have hfinite : M.bound ≠ ⊤ := by
    rw [hbound]
    exact ENNReal.ofReal_ne_top
  have hbreal : M.bound.toReal = P.stop := by
    rw [hbound,ENNReal.toReal_ofReal P.stop_pos.le]
  obtain ⟨v,hvlim,_⟩ := maximal_finite_mixture_endpoint_unique_physical_limit
    z hz rho sigma hρ hσ hv K hK seed M hfinite
  have hvlim' : PhysicalEndpointLimit z rho sigma K M.path P.stop v := by
    simpa only [hbreal] using hvlim
  have hevent : M.path =ᶠ[𝓝[<] P.stop] P.path := by
    have hpos : ∀ᶠ t : ℝ in 𝓝[<] P.stop, 0 < t :=
      (show ∀ᶠ t : ℝ in 𝓝 P.stop, 0 < t from Ioi_mem_nhds P.stop_pos).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hpos,self_mem_nhdsWithin] with t ht0 htb
    exact (M.maximal P).2 ⟨ht0.le,htb⟩
  have heq : a = v :=
    tendsto_nhds_unique (hleft.congr' hevent.symm) hvlim'.2.2.2.1
  simpa only [heq] using hvlim'

/-- An independently certified first physical Fourier loss also certifies
its limiting amplitude as the actual MSA endpoint root selected by the
constructed maximal branch. The endpoint root equation is a conclusion. -/
theorem supplied_first_physical_axis_loss_is_selected_physical_endpoint
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = seed) (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (haxis : ∀ t ∈ Ico 0 b, ∀ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k).det ≠ 0)
    (hleft : Tendsto p (𝓝[<] b) (𝓝 (p b)))
    (hzero : ∃ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p b).1 (p b).2)
        (amplitudeQp z rho sigma (p b).1 (p b).2)
        (W z rho (p b).1 (p b).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p b).1 (p b).2) k).det = 0) :
    M.bound = ENNReal.ofReal b ∧
      PhysicalEndpointLimit z rho sigma K M.path b (p b) := by
  have hbound := supplied_first_physical_axis_loss_eq_maximal_bound
    z hz rho sigma hρ hσ K seed M p b hb hp0 hp hroot haxis hleft hzero
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound :=
    ⟨le_rfl,by simpa using M.positive⟩
  have hseed : p 0 ∈ canonicalAmplitudes z rho sigma := by
    rw [hp0,← M.at_seed]
    exact M.canonical 0 h0
  have hF : ∀ t ∈ Ico (0 : ℝ) b, ∀ k : ℝ, IsUnit
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k) := by
    intro t ht k
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (haxis t ht k))
  have hcanon : ∀ t ∈ Ico (0 : ℝ) b,
      p t ∈ canonicalAmplitudes z rho sigma :=
    canonical_path_of_physical_factor_units z hz rho sigma
      (fun i => (hσ i).le) hρ p (Ico 0 b) 0
      (convex_Ico 0 b).isPreconnected ⟨le_rfl,hb⟩ hp hseed hF
  let P : CanonicalPrefix z rho sigma K seed :=
    ⟨b,hb,p,hp0,hp,hroot,hcanon⟩
  refine ⟨hbound,?_⟩
  exact canonical_prefix_left_limit_is_selected_physical_endpoint
    z hz rho sigma hρ hσ hv K hK seed M P hbound (p b) hleft

/-- A certified first physical Fourier loss can be matched to the HS-seeded
maximal initial branch from finite physical mixture data alone. The branch,
its endpoint coupling and its unique selected actual MSA endpoint root are
constructed; no maximal-branch record is supplied by the caller. -/
theorem exists_hs_maximal_branch_at_certified_first_axis_loss
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (haxis : ∀ t ∈ Ico 0 b, ∀ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k).det ≠ 0)
    (hleft : Tendsto p (𝓝[<] b) (𝓝 (p b)))
    (hzero : ∃ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p b).1 (p b).2)
        (amplitudeQp z rho sigma (p b).1 (p b).2)
        (W z rho (p b).1 (p b).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p b).1 (p b).2) k).det = 0) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      M.bound = ENNReal.ofReal b ∧
      PhysicalEndpointLimit z rho sigma K M.path b (p b) ∧
      ∀ a, PhysicalEndpointLimit z rho sigma K M.path b a → a = p b := by
  have hv : 0 < vacMix rho sigma := by
    unfold vacMix
    linarith
  obtain ⟨M,hM⟩ := exists_mixture_hs_maximal_branch
    z hz rho sigma hσ hρ K hK hv
  obtain ⟨hbM,hphys⟩ := supplied_first_physical_axis_loss_is_selected_physical_endpoint
    z hz rho sigma hρ hσ hv.ne' K hK _ M p b hb hp0 hp hroot haxis hleft hzero
  refine ⟨M,hM,hbM,hphys,?_⟩
  intro a ha
  exact tendsto_nhds_unique ha.2.2.2.1 hphys.2.2.2.1

/-- On a closed continuous candidate path, a single finite Fourier window
suffices to certify the first physical axis loss. The window radius is
obtained from the actual high-frequency kernel bound. -/
theorem exists_hs_maximal_branch_at_compact_first_axis_loss
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Icc 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hzero : ∃ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p b).1 (p b).2)
        (amplitudeQp z rho sigma (p b).1 (p b).2)
        (W z rho (p b).1 (p b).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p b).1 (p b).2) k).det = 0) :
    ∃ R : ℝ, 0 < R ∧
      ((∀ t ∈ Ico 0 b, ∀ k : ℝ, |k| ≤ R →
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma (p t).1 (p t).2)
          (amplitudeQp z rho sigma (p t).1 (p t).2)
          (W z rho (p t).1 (p t).2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
            (p t).1 (p t).2) k).det ≠ 0) →
        ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
          M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
          M.bound = ENNReal.ofReal b ∧
          PhysicalEndpointLimit z rho sigma K M.path b (p b) ∧
          ∀ a, PhysicalEndpointLimit z rho sigma K M.path b a → a = p b) := by
  obtain ⟨R,hR,haxis⟩ :=
    exists_compact_prefix_axis_test_of_continuous_closed_path
      z hz rho sigma hρ (fun i => (hσ i).le) p b hp
  refine ⟨R,hR,?_⟩
  intro hcompact
  have hpIco : ContinuousOn p (Ico 0 b) :=
    hp.mono (fun _ ht => ⟨ht.1,ht.2.le⟩)
  have hIcc : Icc (0 : ℝ) b ∈ 𝓝[<] b := by
    have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] b :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)
    filter_upwards [hpos, self_mem_nhdsWithin] with t ht0 htb
    exact ⟨ht0.le,htb.le⟩
  have hleft : Tendsto p (𝓝[<] b) (𝓝 (p b)) :=
    ((hp b ⟨hb.le,le_rfl⟩).mono_of_mem_nhdsWithin hIcc).tendsto
  exact exists_hs_maximal_branch_at_certified_first_axis_loss
    z hz rho sigma hρ hσ hη K hK p b hb hp0 hpIco hroot
    (haxis hcompact) hleft hzero

/-- A fully explicit coefficientwise interval certificate identifies the
first physical axis loss of the actual HS-seeded mixture branch. The
frequency window is computed from four bounded BH coefficient families. -/
theorem exists_hs_maximal_branch_at_explicit_coefficient_first_axis_loss
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Icc 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ t ∈ Ico 0 b, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Abar j)
    (hQ : ∀ t ∈ Ico 0 b, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qbar i j)
    (hW : ∀ t ∈ Ico 0 b, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wbar u i j)
    (hC : ∀ t ∈ Ico 0 b, ∀ u i j,
      |FMSA.ExactMSA.MultiTailMixture.C z rho sigma
        (p t).1 (p t).2 u i j| ≤ Cbar u i j)
    (hcompact : ∀ t ∈ Ico 0 b, ∀ k : ℝ,
      |k| ≤ rateCutoff z + explicitBudget z rho sigma Abar Qbar Wbar Cbar + 1 →
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) k).det ≠ 0)
    (hzero : ∃ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p b).1 (p b).2)
        (amplitudeQp z rho sigma (p b).1 (p b).2)
        (W z rho (p b).1 (p b).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p b).1 (p b).2) k).det = 0) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      M.bound = ENNReal.ofReal b ∧
      PhysicalEndpointLimit z rho sigma K M.path b (p b) ∧
      ∀ a, PhysicalEndpointLimit z rho sigma K M.path b a → a = p b := by
  have hpIco : ContinuousOn p (Ico 0 b) :=
    hp.mono (fun _ ht => ⟨ht.1,ht.2.le⟩)
  have hIcc : Icc (0 : ℝ) b ∈ 𝓝[<] b := by
    have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] b :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)
    filter_upwards [hpos, self_mem_nhdsWithin] with t ht0 htb
    exact ⟨ht0.le,htb.le⟩
  have hleft : Tendsto p (𝓝[<] b) (𝓝 (p b)) :=
    ((hp b ⟨hb.le,le_rfl⟩).mono_of_mem_nhdsWithin hIcc).tendsto
  have haxis := path_axis_zero_free_of_coefficient_caps
    z hz rho sigma hρ (fun i => (hσ i).le) p (Ico 0 b)
    Abar Qbar Wbar Cbar hA hQ hW hC hcompact
  exact exists_hs_maximal_branch_at_certified_first_axis_loss
    z hz rho sigma hρ hσ hη K hK p b hb hp0 hpIco hroot
    haxis hleft hzero

end FMSA.Convergence.MixtureEndpointNoEscape
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.exists_uniform_test_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.exists_uniform_test_radius
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.actual_full_mixture_amplitude_properness_from_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.actual_full_mixture_amplitude_properness_from_data
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.actual_full_mixture_amplitude_properness_at_eta_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.actual_full_mixture_amplitude_properness_at_eta_lt_one
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.no_finite_mixture_amplitude_escape_from_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.no_finite_mixture_amplitude_escape_from_data
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.canonical_mixture_prefix_uniform_bound_at_eta_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.canonical_mixture_prefix_uniform_bound_at_eta_lt_one
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.hs_axis_zero_free_prefix_uniform_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.hs_axis_zero_free_prefix_uniform_amplitude_bound
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.hs_coefficient_certificate_uniform_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.hs_coefficient_certificate_uniform_amplitude_bound
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.no_finite_mixture_amplitude_escape_at_eta_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.no_finite_mixture_amplitude_escape_at_eta_lt_one
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_prefix_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_prefix_bounded
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.actual_canonical_mixture_prefix_has_unique_finite_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.actual_canonical_mixture_prefix_has_unique_finite_limit
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.canonical_mixture_prefix_and_endpoint_uniform_axis_cutoff_at_eta_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.canonical_mixture_prefix_and_endpoint_uniform_axis_cutoff_at_eta_lt_one
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.canonical_mixture_prefix_no_physical_axis_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.canonical_mixture_prefix_no_physical_axis_zero
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_unique_physical_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_unique_physical_limit
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_first_physical_axis_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_first_physical_axis_loss
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_zero_in_uniform_frequency_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_zero_in_uniform_frequency_window
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_zero_set_compact_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_zero_set_compact_nonempty
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_has_minimal_nonnegative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_has_minimal_nonnegative_zero
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.exists_mixture_hs_maximal_branch_with_finite_endpoint_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.exists_mixture_hs_maximal_branch_with_finite_endpoint_limit
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.exists_mixture_hs_maximal_branch_with_finite_endpoint_limit_at_eta_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.exists_mixture_hs_maximal_branch_with_finite_endpoint_limit_at_eta_lt_one
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.exists_mixture_hs_maximal_branch_with_first_axis_loss_at_eta_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.exists_mixture_hs_maximal_branch_with_first_axis_loss_at_eta_lt_one
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.supplied_first_physical_axis_loss_eq_maximal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.supplied_first_physical_axis_loss_eq_maximal_bound
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.canonical_prefix_left_limit_is_selected_physical_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.canonical_prefix_left_limit_is_selected_physical_endpoint
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.supplied_first_physical_axis_loss_is_selected_physical_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.supplied_first_physical_axis_loss_is_selected_physical_endpoint
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.exists_hs_maximal_branch_at_certified_first_axis_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.exists_hs_maximal_branch_at_certified_first_axis_loss
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.exists_hs_maximal_branch_at_compact_first_axis_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.exists_hs_maximal_branch_at_compact_first_axis_loss
/-- info: 'FMSA.Convergence.MixtureEndpointNoEscape.exists_hs_maximal_branch_at_explicit_coefficient_first_axis_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureEndpointNoEscape.exists_hs_maximal_branch_at_explicit_coefficient_first_axis_loss
