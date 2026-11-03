import MSAConvergence.MixtureFirstAmplitudeBounds
import MSAConvergence.MixtureSecondAmplitudeBounds
import MSAConvergence.MixtureHSCanonicity

/-! General positive-density mixture amplitude escape is excluded in the
ORIGINAL product/Pi norm. Constructed finite maximal endpoints have actual
physical Fourier-zero cluster roots. Tracer amplitudes are separate work. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.MixtureCanonicalProperness
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture FMSA.MatrixQ0
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Convergence.MixtureFirstAmplitudeBounds FMSA.Convergence.MixtureSecondAmplitudeBounds
open FMSA.Convergence.MaximalCanonicalBranch FMSA.Convergence.MaximalMSAConvergence
open FMSA.Paper.StableIntervalRadius FMSA.Convergence.CanonicalEndpointContinuation
variable {N : ℕ} {T : Type*} [Fintype T]

/-- All actual canonical reciprocal roots at bounded strengths have bounded
ORIGINAL amplitude pairs, with no equal-diameter or exchange restriction. -/
theorem canonical_roots_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : TailMatrix T N, ∀ p : TailMatrix T N × TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) → IsRoot z ρ σ K p.1 p.2 →
      p ∈ canonicalAmplitudes z ρ σ → ‖p‖ ≤ C := by
  obtain ⟨CD,hCD,hD⟩ := first_amplitudes_uniformly_bounded z hz ρ σ hρ hσ hv B
  obtain ⟨CG,hCG,hG⟩ := second_amplitudes_uniformly_bounded z hz ρ σ hρ hσ hv
  refine ⟨max CD CG,hCD.trans (le_max_left _ _),?_⟩
  intro K p hnorm hK hroot hcanon
  rw [Prod.norm_def,max_le_iff]
  exact ⟨(hD K p.1 p.2 hnorm hK hroot hcanon).trans (le_max_left _ _),
    (hG K p.1 p.2 hK hroot hcanon).trans (le_max_right _ _)⟩

/-- Every finite actual canonical prefix is bounded. No seed, continuity,
maximality or endpoint value is required for this original amplitude bound. -/
theorem finite_canonical_prefix_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z ρ σ (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z ρ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := canonical_roots_uniformly_bounded z hz ρ σ hρ hσ hv (max b 0*‖K‖)
  refine ⟨C,hC,?_⟩
  intro t ht
  apply hbound (t • K) (p t) _ _ (hroot t ht) (hcanon t ht)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_right (ht.2.le.trans (le_max_left _ _)) (norm_nonneg _)
  · intro u i j
    simp only [Pi.smul_apply,smul_eq_mul,hK u i j]

/-- Finite amplitude escape is impossible for general positive-density
canonical reciprocal mixtures, in the ORIGINAL pair norm. -/
theorem no_finite_canonical_amplitude_escape (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z ρ σ (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z ρ σ) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  obtain ⟨C,_hC,hbound⟩ := finite_canonical_prefix_bounded z hz ρ σ hρ hσ hv K hK p b hroot hcanon
  intro hescape
  obtain ⟨t,ht,_hc,hlarge⟩ := hescape C 0 hb
  exact (not_lt_of_ge (hbound t ht)) hlarge

/-- Every constructed maximal positive-density mixture branch with a finite
endpoint has an actual cluster ROOT and an actual real-frequency Fourier zero.
No supplied boundedness or full endpoint limit is used. -/
theorem maximal_finite_endpoint_has_physical_cluster (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N) (M : MaximalBranch z ρ σ K seed) (hf : M.bound ≠ ⊤) :
    0 < M.bound.toReal ∧ HasPhysicalEndpointCluster z ρ σ K M.path M.bound.toReal := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hf
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hf).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  obtain ⟨C,_hC,hCbound⟩ := finite_canonical_prefix_bounded z hz ρ σ hρ hσ hv K hK M.path M.bound.toReal
    (by simpa only [hset] using M.roots) (by simpa only [hset] using M.canonical)
  obtain ⟨a,u,_ha,hu,ht,hp,hr,hcl,hzero⟩ := maximal_bounded_endpoint_cluster z hz ρ σ hσ
    (fun i => (hρ i).le) K hK hv seed M hf C hCbound
  exact ⟨hb,a,u,hu,ht,hp,hr,hcl,hzero⟩

/-- Physical data alone construct an HS-seeded maximal branch at every eta<1.
Its finite endpoint necessarily has an actual physical Fourier-zero cluster;
general positive-density mixture amplitude escape has been excluded. -/
theorem exists_hs_maximal_branch_with_finite_axis_cluster (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : 0 < vacMix ρ σ) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ M : MaximalBranch z ρ σ K (0,baseSeed z ρ σ),
      M.bound = maximalBound z ρ σ K (0,baseSeed z ρ σ) ∧
      (M.bound ≠ ⊤ → 0 < M.bound.toReal ∧ HasPhysicalEndpointCluster z ρ σ K M.path M.bound.toReal) := by
  obtain ⟨M,hM⟩ := MixtureHSCanonicity.exists_mixture_hs_maximal_branch z hz ρ σ hσ
    (fun i => (hρ i).le) K hK hv
  exact ⟨M,hM,fun hf => maximal_finite_endpoint_has_physical_cluster z hz ρ σ hρ hσ hv.ne' K hK _ M hf⟩

end FMSA.Convergence.MixtureCanonicalProperness
/-- info: 'FMSA.Convergence.MixtureCanonicalProperness.canonical_roots_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCanonicalProperness.canonical_roots_uniformly_bounded
/-- info: 'FMSA.Convergence.MixtureCanonicalProperness.finite_canonical_prefix_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCanonicalProperness.finite_canonical_prefix_bounded
/-- info: 'FMSA.Convergence.MixtureCanonicalProperness.no_finite_canonical_amplitude_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCanonicalProperness.no_finite_canonical_amplitude_escape
/-- info: 'FMSA.Convergence.MixtureCanonicalProperness.maximal_finite_endpoint_has_physical_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCanonicalProperness.maximal_finite_endpoint_has_physical_cluster
/-- info: 'FMSA.Convergence.MixtureCanonicalProperness.exists_hs_maximal_branch_with_finite_axis_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCanonicalProperness.exists_hs_maximal_branch_with_finite_axis_cluster
