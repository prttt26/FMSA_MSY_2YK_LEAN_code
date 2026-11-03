import MSAConvergence.BinaryCanonicalProperness
import MSAConvergence.MixtureHSCanonicity

/-! Species exchange in the ORIGINAL binary BH dictionary. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.BinaryExchangeSymmetry
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.BinaryCanonicalChannels FMSA.Convergence.CanonicalNeighborhood
variable {T : Type*} [Fintype T]

def flip (i : Fin 2) : Fin 2 := if i=0 then 1 else 0

def swapMat (A : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => A (flip i) (flip j)

def swapAmp (p : Amp T) : Amp T :=
  ((fun u => swapMat (p.1 u)),fun u => swapMat (p.2 u))

private theorem Wt_flip (s r : ℝ) (G D : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    Wt s (density r) (swapMat G) (swapMat D) i j = Wt s (density r) G D (flip i) (flip j) := by
  fin_cases i <;> fin_cases j <;> simp [Wt,swapMat,flip,Fin.sum_univ_two,density] <;> ring_nf <;> simp

private theorem Ct_flip (s r a : ℝ) (G D : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    Ct s (density r) (diameter a) (swapMat G) (swapMat D) i j =
      Ct s (density r) (diameter a) G D (flip i) (flip j) := by
  fin_cases i <;> fin_cases j <;>
    simp [Ct,gam,sigMix,swapMat,flip,Fin.sum_univ_two,density,diameter] <;> ring

private theorem mixM_flip (s r a : ℝ) (G D : Fin 2 → Fin 2 → ℝ) (j : Fin 2) :
    mixM s (density r) (diameter a) (swapMat G) (swapMat D) j =
      mixM s (density r) (diameter a) G D (flip j) := by
  simp only [mixM,Wt_flip,Ct_flip]
  fin_cases j <;> simp [Fin.sum_univ_two,density,diameter,flip] <;> ring_nf <;> simp

private theorem mixN_flip (s r a : ℝ) (G D : Fin 2 → Fin 2 → ℝ) (j : Fin 2) :
    mixN s (density r) (diameter a) (swapMat G) (swapMat D) j =
      mixN s (density r) (diameter a) G D (flip j) := by
  simp only [mixN,Wt_flip,Ct_flip]
  fin_cases j <;> simp [Fin.sum_univ_two,density,diameter,flip] <;> ring

private theorem A_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (j : Fin 2) :
    amplitudeA z (density r) (diameter a) (swapAmp p).1 (swapAmp p).2 j =
      amplitudeA z (density r) (diameter a) p.1 p.2 (flip j) := by
  simp only [amplitudeA,mixDA,swapAmp,mixM_flip,mixN_flip,Qppphys,diameter]

private theorem Qp_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (i j : Fin 2) :
    amplitudeQp z (density r) (diameter a) (swapAmp p).1 (swapAmp p).2 i j =
      amplitudeQp z (density r) (diameter a) p.1 p.2 (flip i) (flip j) := by
  simp only [amplitudeQp,mixDqp,swapAmp,mixM_flip,mixN_flip,Qppphys,Q0phys,diameter]

omit [Fintype T] in
private theorem W_flip (z : T → ℝ) (r : ℝ) (p : Amp T) (u : T) (i j : Fin 2) :
    W z (density r) (swapAmp p).1 (swapAmp p).2 u i j =
      W z (density r) p.1 p.2 u (flip i) (flip j) := Wt_flip _ _ _ _ _ _

omit [Fintype T] in
private theorem C_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (u : T) (i j : Fin 2) :
    C z (density r) (diameter a) (swapAmp p).1 (swapAmp p).2 u i j =
      C z (density r) (diameter a) p.1 p.2 u (flip i) (flip j) := Ct_flip _ _ _ _ _ _ _

private theorem Qhat_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (s : ℝ) (i j : Fin 2) :
    dressedQhat z (density r) (diameter a) (swapAmp p).1 (swapAmp p).2 s i j =
      dressedQhat z (density r) (diameter a) p.1 p.2 s (flip i) (flip j) := by
  simp only [dressedQhat,Qhat,A_flip,Qp_flip,W_flip,C_flip,edgeLo,edgeHi,diameter]

/-- Exact equivariance of the ORIGINAL finite BH coefficient vector. -/
theorem coeff_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (i j : Fin 2) :
    coeff z r a (swapAmp p) i j = coeff z r a p (flip i) (flip j) := by
  funext b
  rcases b with b | (u | u)
  · fin_cases b <;> simp [coeff,bhCoefficient,coefficient,A_flip,Qp_flip]
  · simp [coeff,bhCoefficient,coefficient,W_flip]
  · simp [coeff,bhCoefficient,coefficient,C_flip]

private theorem first_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (u : T) (i j : Fin 2) :
    firstLHS z (density r) (diameter a) (swapAmp p).1 (swapAmp p).2 u i j =
      firstLHS z (density r) (diameter a) p.1 p.2 u (flip i) (flip j) := by
  simp only [firstLHS,Qhat_flip,edgeLo,diameter,density]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two,swapAmp,swapMat,flip] <;> ring

private theorem second_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (u : T) (i j : Fin 2) :
    secondLHS z (density r) (diameter a) (swapAmp p).1 (swapAmp p).2 u i j =
      secondLHS z (density r) (diameter a) p.1 p.2 u (flip i) (flip j) := by
  simp only [secondLHS,Qhat_flip,edgeLo,diameter,density]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two,swapAmp,swapMat,flip] <;> ring

private theorem source_flip (z : T → ℝ) (r a : ℝ) (p : Amp T) (u : T) (i j : Fin 2) :
    secondRHS z (density r) (diameter a) (swapAmp p).1 (swapAmp p).2 u i j =
      secondRHS z (density r) (diameter a) p.1 p.2 u (flip i) (flip j) := by
  simp only [secondRHS,A_flip,Qp_flip,C_flip]

/-- Relabelling the species preserves the TRUE root equations at fixed
exchange-symmetric strengths; no channel equations replace the residual. -/
theorem swapped_isRoot (z : T → ℝ) (r a : ℝ) (K : TailMatrix T 2)
    (hK : ∀ u, swapMat (K u) = K u) (p : Amp T)
    (hp : IsRoot z (density r) (diameter a) K p.1 p.2) :
    IsRoot z (density r) (diameter a) K (swapAmp p).1 (swapAmp p).2 := by
  constructor
  · intro u i j
    rw [first_flip,hp.1]
    have hk := congrFun (congrFun (hK u) i) j
    rw [show K u (flip i) (flip j) = K u i j from hk]
  · intro u i j
    rw [second_flip,source_flip,hp.2]

omit [Fintype T] in
theorem swapAmp_continuous : Continuous (swapAmp : Amp T → Amp T) := by
  unfold swapAmp swapMat
  fun_prop

/-- A fixed point of physical species exchange has exchange-symmetric
finite kernels. This concerns the exact nonlinear kernel coefficients. -/
theorem kernel_exchange_of_fixed (z : T → ℝ) (r a : ℝ) (p : Amp T)
    (hp : swapAmp p = p) : KernelExchange z r a p := by
  constructor
  · have h := coeff_flip z r a p 0 0
    simpa only [hp,flip,↓reduceIte] using h.symm
  · have h := coeff_flip z r a p 0 1
    simpa [hp,flip] using h.symm

/-- Same-seed canonical uniqueness propagates SPECIES symmetry along the
whole connected physical branch. Kernel symmetry is a conclusion. -/
theorem branch_fixed (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (r a : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (hv : vacMix (density r) (diameter a) ≠ 0)
    (K : TailMatrix T 2) (hK : ∀ u, swapMat (K u) = K u)
    (hKt : ∀ u i j, K u i j = K u j i)
    (p : ℝ → Amp T) (s : Set ℝ) (t₀ : ℝ) (hs : IsPreconnected s) (ht : t₀ ∈ s)
    (hp : ContinuousOn p s) (hseed : swapAmp (p t₀) = p t₀)
    (hroot : ∀ t ∈ s, IsRoot z (density r) (diameter a) (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ s, p t ∈ canonicalAmplitudes z (density r) (diameter a)) :
    ∀ t ∈ s, swapAmp (p t) = p t := by
  have he := ActualCanonicalBranch.actual_canonical_roots_eqOn_of_preconnected z hz
    (density r) (diameter a) (fun _ => ha) (fun _ => hr) K hKt hv
    p (fun t => swapAmp (p t)) s t₀ hs ht hp (swapAmp_continuous.comp_continuousOn hp) hseed.symm
    hroot (fun t ht => swapped_isRoot z r a (t • K)
      (fun u => by funext i j; exact congrArg (fun x : ℝ => t*x) (congrFun (congrFun (hK u) i) j))
      (p t) (hroot t ht)) hcanon
  exact fun t ht => (he ht).symm

private theorem zero_D_root_eq_seed (z : T → ℝ) (r a : ℝ)
    (hH : ∀ u, IsUnit (Matrix.det (baseSecond z (density r) (diameter a) u)))
    (G : TailMatrix T 2) (hp : IsRoot z (density r) (diameter a) 0 0 G) :
    G = baseSeed z (density r) (diameter a) := by
  have hres : residual z (density r) (diameter a) 0 (0,(0,G)) = 0 :=
    (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (by simpa only [zero_smul] using hp)
  rw [residual_zero_eq] at hres
  have he : (2*Real.pi) • rightBlock (baseSecond z (density r) (diameter a)) G =
      baseSource z (density r) (diameter a) := by
    simpa only [Prod.snd_zero,sub_eq_zero] using congrArg Prod.snd hres
  have hc := congrArg (fun q : TailMatrix T 2 => (2*Real.pi)⁻¹ •
    rightBlock (inverseBlocks (baseSecond z (density r) (diameter a))) q) he
  change G = (2*Real.pi)⁻¹ • rightBlock
    (inverseBlocks (baseSecond z (density r) (diameter a))) (baseSource z (density r) (diameter a))
  simpa only [map_smul,rightBlock_left_inverse _ hH,smul_smul,
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),one_smul] using hc

/-- The honest HS seed is a fixed point of species exchange, derived from
its actual linear second equation and the proved physical HS inverse. -/
theorem hs_seed_fixed (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ)
    (hr : 0 ≤ r) (ha : 0 < a) (hv : 0 < vacMix (density r) (diameter a)) :
    swapAmp (0,baseSeed z (density r) (diameter a)) =
      (0,baseSeed z (density r) (diameter a)) := by
  have hH := fun u => baseSecond_isUnit_det z (density r) (diameter a) hz hv
    (fun _ => hr) (fun _ => ha) u
  have hroot : IsRoot z (density r) (diameter a) 0 0 (baseSeed z (density r) (diameter a)) := by
    simpa only [zero_smul] using
      (residual_eq_zero_iff _ _ _ _ _ _ _).mp (residual_base z (density r) (diameter a) 0 hH)
  have hs := swapped_isRoot z r a 0 (fun _ => rfl) (0,baseSeed z (density r) (diameter a)) hroot
  apply Prod.ext
  · rfl
  · exact zero_D_root_eq_seed z r a hH _ hs

omit [Fintype T] in
/-- Every binary species-exchange invariant strength matrix is reciprocal. -/
theorem exchange_strength_symmetric (K : TailMatrix T 2)
    (hK : ∀ u, swapMat (K u) = K u) : ∀ u i j, K u i j = K u j i := by
  intro u i j
  have h := congrFun (congrFun (hK u) 0) 1
  fin_cases i <;> fin_cases j
  · rfl
  · simpa [swapMat,flip] using h.symm
  · simpa [swapMat,flip] using h
  · rfl

/-- Escape is excluded from the physical HS-seeded, species-exchange
symmetric binary branch. Symmetry of the actual kernel is DERIVED. -/
theorem hs_prefix_no_finite_escape (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (hv : 0 < vacMix (density r) (diameter a))
    (K : TailMatrix T 2) (hK : ∀ u, swapMat (K u) = K u)
    (p : ℝ → Amp T) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hseed : p 0 = (0, baseSeed z (density r) (diameter a)))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z (density r) (diameter a) (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z (density r) (diameter a)) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  have he := branch_fixed z hz r a hr.le ha hv.ne' K hK (exchange_strength_symmetric K hK) p (Ico 0 b) 0
    (convex_Ico 0 b).isPreconnected ⟨le_rfl,hb⟩ hp
    (by rw [hseed]; exact hs_seed_fixed z hz r a hr.le ha hv) hroot hcanon
  exact BinaryCanonicalProperness.no_finite_canonical_amplitude_escape z hz r a hr ha K p b hb
    hroot hcanon (fun t ht => kernel_exchange_of_fixed z r a (p t) (he t ht))

open FMSA.Convergence.MaximalCanonicalBranch FMSA.Convergence.MaximalMSAConvergence
open FMSA.Convergence.CanonicalEndpointContinuation FMSA.Paper.StableIntervalRadius

/-- From physical exchange-symmetric binary HS DATA alone, the constructed
maximal initial canonical branch has a physical Fourier-zero cluster at every
finite endpoint. The amplitude-escape disjunct is proved impossible. -/
theorem exists_hs_maximal_branch_with_finite_axis_cluster
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ) (hr : 0 < r) (ha : 0 < a)
    (hv : 0 < vacMix (density r) (diameter a))
    (K : TailMatrix T 2) (hK : ∀ u, swapMat (K u) = K u) :
    ∃ M : MaximalBranch z (density r) (diameter a) K (0,baseSeed z (density r) (diameter a)),
      M.bound = maximalBound z (density r) (diameter a) K (0,baseSeed z (density r) (diameter a)) ∧
      (M.bound ≠ ⊤ → 0 < M.bound.toReal ∧
        HasPhysicalEndpointCluster z (density r) (diameter a) K M.path M.bound.toReal) := by
  have hKt := exchange_strength_symmetric K hK
  obtain ⟨M,hM⟩ := MixtureHSCanonicity.exists_mixture_hs_maximal_branch z hz (density r)
    (diameter a) (fun _ => ha) (fun _ => hr.le) K hKt hv
  refine ⟨M,hM,?_⟩
  intro hfinite
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  have hroot : ∀ t ∈ Ico 0 M.bound.toReal,
      IsRoot z (density r) (diameter a) (t • K) (M.path t).1 (M.path t).2 :=
    by simpa only [hset] using M.roots
  have hcanon : ∀ t ∈ Ico 0 M.bound.toReal,
      M.path t ∈ canonicalAmplitudes z (density r) (diameter a) :=
    by simpa only [hset] using M.canonical
  have hp : ContinuousOn M.path (Ico 0 M.bound.toReal) :=
    by simpa only [hset] using M.analytic.continuousOn
  have hno := hs_prefix_no_finite_escape z hz r a hr ha hv K hK M.path M.bound.toReal hb
    hp M.at_seed hroot hcanon
  exact ⟨hb,(finite_nonextendable_prefix_boundary_obstruction z hz (density r) (diameter a)
    (fun _ => ha) (fun _ => hr.le) K hKt hv.ne' M.path M.bound.toReal hb hp hroot hcanon
    (maximal_branch_nonextendable z (density r) (diameter a) K _ M _ hb hbound)).resolve_left hno⟩

end FMSA.Convergence.BinaryExchangeSymmetry


/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.coeff_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.coeff_flip
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.swapped_isRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.swapped_isRoot
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.swapAmp_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.swapAmp_continuous
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.kernel_exchange_of_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.kernel_exchange_of_fixed
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.branch_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.branch_fixed
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.hs_seed_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.hs_seed_fixed
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.exchange_strength_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.exchange_strength_symmetric
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.hs_prefix_no_finite_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.hs_prefix_no_finite_escape
/-- info: 'FMSA.Convergence.BinaryExchangeSymmetry.exists_hs_maximal_branch_with_finite_axis_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryExchangeSymmetry.exists_hs_maximal_branch_with_finite_axis_cluster
