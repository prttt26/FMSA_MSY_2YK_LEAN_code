import MSAConvergence.ScalarKernelSource

/-! Honest symbols and compact observations of the full finite kernel space.
Neither redundant coefficients nor arbitrary pointwise samples define its norm. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.FiniteKernelLaplace
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ScalarKernelSource FMSA.Convergence.ActualLaplaceJets
open FMSA.Convergence.ActualSourceBoundary FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.CanonicalKernelEstimates
variable {T : Type*} [Fintype T]

def laplace (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (s : ℂ) : ℂ :=
  FMSA.causalComplexLaplace (field z sigma c) s

/-- Every coefficient combination has an honest integral on the WHOLE
closed right half-plane, including its origin. -/
theorem field_laplace_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T) (s : ℂ) (hs : 0 ≤ s.re) :
    IntegrableOn (fun t : ℝ => (field z sigma c t : ℂ)*Complex.exp (-s*t)) (Ioi 0) := by
  have hi (b : BasisIndex T) : IntegrableOn (fun t : ℝ =>
      (recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t : ℂ)*Complex.exp (-s*t)) (Ioi 0) := by
    simpa only [one_mul] using kernel_basis_laplace_closed_right z hz (fun _ : Fin 1 => 1)
      (fun _ => sigma) s hs b 0
  have he : (fun t : ℝ => (field z sigma c t : ℂ)*Complex.exp (-s*t)) =
      fun t => ∑ b, (c b : ℂ)*((recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t : ℂ)*Complex.exp (-s*t)) := by
    funext t
    simp only [field,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul,mul_assoc]
  rw [he]
  exact integrable_finsetSum _ (fun b _ => (hi b).const_mul (c b : ℂ))

/-- The honest symbol is exactly the finite sum after proving integrability. -/
theorem laplace_eq_sum (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T) (s : ℂ) (hs : 0 ≤ s.re) :
    laplace z sigma c s = ∑ b, (c b : ℂ)*
      FMSA.causalComplexLaplace (recenteredBasis z (fun _ : Fin 1 => sigma) b 0) s := by
  have hi (b : BasisIndex T) : IntegrableOn (fun t : ℝ =>
      (recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t : ℂ)*Complex.exp (-s*t)) (Ioi 0) := by
    simpa only [one_mul] using kernel_basis_laplace_closed_right z hz (fun _ : Fin 1 => 1)
      (fun _ => sigma) s hs b 0
  unfold laplace FMSA.causalComplexLaplace field
  have he : (fun t : ℝ => ((∑ b, c b*recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t : ℝ) : ℂ)*Complex.exp (-s*t)) =
      fun t => ∑ b, (c b : ℂ)*((recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t : ℂ)*Complex.exp (-s*t)) := by
    funext t
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul,mul_assoc]
  rw [he,finite_complex_integral _ _ _ hi]

/-- Every finite actual kernel field is genuinely L1 before damping. -/
theorem field_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (c : Coeff T) :
    IntegrableOn (field z sigma c) (Ioi 0) := by
  have hi (b : BasisIndex T) : IntegrableOn
      (recenteredBasis z (fun _ : Fin 1 => sigma) b 0) (Ioi 0) := by
    have h := kernel_basis_mass_integrable z hz (fun _ : Fin 1 => 1) (fun _ => sigma) b 0
    change Integrable (recenteredBasis z (fun _ : Fin 1 => sigma) b 0) (volume.restrict (Ioi (0 : ℝ)))
    simp only [IntegrableOn,one_mul] at h
    have hm : AEStronglyMeasurable (recenteredBasis z (fun _ : Fin 1 => sigma) b 0)
        (volume.restrict (Ioi (0 : ℝ))) := (recenteredBasis_continuous z (fun _ : Fin 1 => sigma) b 0).aestronglyMeasurable
    exact (integrable_norm_iff hm).mp (by simpa only [Real.norm_eq_abs] using h)
  unfold field
  exact integrable_finsetSum _ (fun b _ => (hi b).const_mul (c b))

/-- Genuine nonnegative real damping preserves L1. -/
theorem field_real_damped_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ => exp (-s*t)*field z sigma c t) (Ioi 0) := by
  apply (field_integrable z hz sigma c).norm.mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (field_continuous z sigma c)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖exp (-s*t)*field z sigma c t‖ ≤ ‖field z sigma c t‖
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
  apply mul_le_of_le_one_left (abs_nonneg _)
  exact exp_le_one_iff.mpr (by nlinarith [show 0<t from ht])

/-- Equal compact observations determine the ENTIRE honest Laplace symbol. -/
theorem laplace_eq_of_compact_eq (z : T → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (c d : Coeff T) (heq : compactKernel z sigma c = compactKernel z sigma d) (s : ℂ) :
    laplace z sigma c s = laplace z sigma d s := by
  unfold laplace FMSA.causalComplexLaplace
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [field_eq_of_compact_eq z sigma hsigma c d heq t ht.le]

/-- Uniform full-half-plane symbol control in a fixed coefficient norm. -/
theorem laplace_coefficient_norm_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖laplace z sigma c s‖ ≤ ‖c‖*∑ b : BasisIndex T,
      kernelBasisMass z (fun _ : Fin 1 => 1) (fun _ => sigma) b 0 := by
  rw [laplace_eq_sum z hz sigma c s hs,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [norm_mul,Complex.norm_real]
  have hm := kernel_basis_laplace_uniform_bound z hz (fun _ : Fin 1 => 1) (fun _ => sigma) b 0 s hs
  simp only [one_mul] at hm
  exact mul_le_mul (norm_le_pi_norm c b) hm (norm_nonneg _) (norm_nonneg _)

/-- Genuine compact kernel norm controls the symbol UNIFORMLY at every
closed-right frequency; it is not a redundant coefficient norm bound. -/
theorem laplace_bound_by_compact_kernel (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : Coeff T, ∀ s : ℂ, 0 ≤ s.re →
      ‖laplace z sigma c s‖ ≤ B*‖compactKernel z sigma c‖ := by
  let M := ∑ b : BasisIndex T, kernelBasisMass z (fun _ : Fin 1 => 1) (fun _ => sigma) b 0
  have hM : 0 ≤ M := Finset.sum_nonneg (fun b _ => kernel_basis_mass_nonneg _ _ _ b _)
  refine ⟨‖kernelSection z sigma‖*M,mul_nonneg (norm_nonneg _) hM,?_⟩
  intro c s hs
  let q : (compactKernel z sigma).range := ⟨compactKernel z sigma c,⟨c,rfl⟩⟩
  have he := laplace_eq_of_compact_eq z sigma hsigma (kernelSection z sigma q) c
    (kernel_section_rightInverse z sigma q) s
  rw [← he]
  calc
    _ ≤ ‖kernelSection z sigma q‖*M := laplace_coefficient_norm_bound z hz sigma _ s hs
    _ ≤ (‖kernelSection z sigma‖*‖compactKernel z sigma c‖)*M :=
      mul_le_mul_of_nonneg_right (kernel_section_norm_bound z sigma q) hM
    _ = _ := by ring

/-- No nonzero compact kernel can have identically zero honest Laplace
symbol on the open right half-plane. -/
theorem laplace_injective_on_compact (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T)
    (hzero : ∀ s : ℂ, 0 < s.re → laplace z sigma c s = 0) : compactKernel z sigma c = 0 := by
  have he := causalComplexLaplace_injective_continuous (field z sigma c) 0
    (field_continuous z sigma c) continuous_const
    (by simpa only [neg_one_mul] using field_real_damped_integrable z hz sigma c 1 zero_le_one)
    (by simp)
    (fun k => by simpa [laplace,FMSA.causalComplexLaplace] using hzero (1+Complex.I*(2*Real.pi*k)) (by simp))
  ext t
  exact he t t.property.1

/-- A nonzero compact actual field yields a nontrivial analytic-limit symbol. -/
theorem exists_nonzero_laplace_of_compact_ne_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T) (hc : compactKernel z sigma c ≠ 0) :
    ∃ s : ℂ, 0 < s.re ∧ laplace z sigma c s ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hc (laplace_injective_on_compact z hz sigma c hn)

/-- Positive real damping drives every honest L1 kernel symbol to zero.
This proves nontriviality of a constant-minus-Laplace limit. -/
theorem laplace_real_tendsto_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T) :
    Tendsto (fun s : ℝ => laplace z sigma c (s : ℂ)) atTop (𝓝 0) := by
  have hi := field_integrable z hz sigma c
  have hr : Tendsto (fun s : ℝ => ∫ t in Ioi (0 : ℝ), exp (-s*t)*field z sigma c t)
      atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun s t : ℝ => exp (-s*t)*field z sigma c t)
      (f := fun _ => (0 : ℝ)) (fun t => |field z sigma c t|)
      (Eventually.of_forall (fun s => ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (field_continuous z sigma c)).aestronglyMeasurable))
      (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
        exact mul_le_of_le_one_left (abs_nonneg _) (exp_le_one_iff.mpr (by nlinarith [show 0<t from ht])))
      (by simpa only [Real.norm_eq_abs] using hi.norm)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hmult : Tendsto (fun s : ℝ => s*t) atTop atTop := tendsto_id.atTop_mul_const (show 0<t from ht)
        simpa only [Function.comp_def,zero_mul,neg_mul] using
          (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmult).mul_const (field z sigma c t))
    simpa using h
  have he (s : ℝ) : laplace z sigma c (s : ℂ) =
      ((∫ t in Ioi (0 : ℝ), exp (-s*t)*field z sigma c t : ℝ) : ℂ) := by
    unfold laplace FMSA.causalComplexLaplace
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    simp only [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg]
    ring
  simpa only [Function.comp_def,← he,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hr

/-- The compact finite dictionary has its literal polynomial/exponential
real-space expression before a complex transform is invoked. -/
theorem field_eq_explicit (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (t : ℝ) :
    field z sigma c t = c (.inl 0)*(min t sigma-sigma)+c (.inl 1)/2*(min t sigma-sigma)^2+
      ∑ u, (c (.inr (.inl u))*exp (-z u*t)+c (.inr (.inr u))*exp (-z u*(max t sigma-sigma))) := by
  simp only [field,Fintype.sum_sum_type,Fin.sum_univ_two,recenteredBasis,
    basisQp,basisA,basisW,basisC,basisRate]
  simp only [Fin.isValue,show (0 : Fin 2) ≠ 1 by decide,show (1 : Fin 2) ≠ 0 by decide,
    if_true,if_false,zero_mul,one_mul,zero_div,add_zero,zero_add]
  rw [← Finset.sum_add_distrib]
  ring

/-- The free coefficient field is identified with the honest causal extension
of the ACTUAL finite q dictionary, including its tail. -/
theorem raw_q_eq_causalShift (z : T → ℝ) (sigma : ℝ) (c : Coeff T) :
    q z (fun _ : Fin 1 => sigma) (fun _ => c (.inl 1)) (fun _ _ => c (.inl 0))
      (fun u _ _ => c (.inr (.inl u))) (fun u _ _ => c (.inr (.inr u))) 0 0 =
      causalShift (field z sigma c) 0 := by
  funext t
  have hlo : MSAMixture.edgeLo (fun _ : Fin 1 => sigma) 0 0 = 0 := by simp [MSAMixture.edgeLo]
  have hhi : MSAMixture.edgeHi (fun _ : Fin 1 => sigma) 0 0 = sigma := by simp [MSAMixture.edgeHi]
  by_cases ht : t < 0
  · rw [causalShift_eq_zero_below _ _ _ ht]
    simp only [q,hlo,if_pos ht]
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    simp only [causalShift,causalFull,sub_zero,indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht0)]
    rw [field_eq_explicit]
    rcases le_or_gt t sigma with hs | hs
    · simp only [q,hlo,hhi,if_neg ht,if_pos hs,sub_zero,min_eq_left hs,max_eq_right hs,sub_self,
        mul_zero,exp_zero,mul_one]
    · simp only [q,hlo,hhi,if_neg ht,if_neg hs.not_ge,sub_zero,min_eq_right hs.le,max_eq_left hs.le,
        sub_self,mul_zero,zero_pow (by decide : 2 ≠ 0),zero_add]

/-- Honest generic kernel Laplace integrals equal the existing FREE finite
QhatComplex formula on the open right half-plane. -/
theorem laplace_eq_raw_formula (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (c : Coeff T) (s : ℂ) (hs : 0 < s.re) :
    laplace z sigma c s = QhatComplex z (fun _ : Fin 1 => sigma)
      (fun _ => c (.inl 1)) (fun _ _ => c (.inl 0))
      (fun u _ _ => c (.inr (.inl u))) (fun u _ _ => c (.inr (.inr u))) s 0 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have h := causalShift_complex_laplace (field z sigma c) 0 s
  rw [← raw_q_eq_causalShift z sigma c,
    full_q_integral_rate_domain z (fun _ : Fin 1 => sigma) _ _ _ _ (fun _ => hsigma)
      s hs0 (fun u => by linarith [hz u])] at h
  simpa only [Complex.ofReal_zero,mul_zero,neg_zero,Complex.exp_zero,one_mul,laplace] using h.symm

/-- The honest kernel symbol is holomorphic in the full OPEN right half-plane,
for arbitrary finite coefficient data, including repeated rates. -/
theorem laplace_analytic_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (c : Coeff T) :
    AnalyticOnNhd ℂ (laplace z sigma c) {s : ℂ | 0 < s.re} := by
  have hd : DifferentiableOn ℂ (laplace z sigma c) {s : ℂ | 0 < s.re} := by
    intro s hs
    change 0 < s.re at hs
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    have hzs (u : T) : s+(z u : ℂ) ≠ 0 :=
      FMSA.Convergence.CanonicalResolventAnalysis.rate_shift_ne_zero s (z u) (by linarith [hz u])
    have hformula : DifferentiableAt ℂ (fun w => QhatComplex z (fun _ : Fin 1 => sigma)
        (fun _ => c (.inl 1)) (fun _ _ => c (.inl 0))
        (fun u _ _ => c (.inr (.inl u))) (fun u _ _ => c (.inr (.inr u))) w 0 0) s := by
      unfold QhatComplex
      fun_prop (disch := aesop)
    apply hformula.differentiableWithinAt.congr
    · intro w hw
      exact laplace_eq_raw_formula z hz sigma hsigma c w hw
    · exact laplace_eq_raw_formula z hz sigma hsigma c s hs
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- The coefficient/frequency family of honest integrals is jointly
continuous inside the right half-plane, via its proved free formula. -/
theorem laplace_joint_continuousAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (c : Coeff T) (s : ℂ) (hs : 0 < s.re) :
    ContinuousAt (fun x : Coeff T × ℂ => laplace z sigma x.1 x.2) (c,s) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hzs (u : T) : s+(z u : ℂ) ≠ 0 :=
    FMSA.Convergence.CanonicalResolventAnalysis.rate_shift_ne_zero s (z u) (by linarith [hz u])
  have hraw : ContinuousAt (fun x : Coeff T × ℂ => QhatComplex z (fun _ : Fin 1 => sigma)
      (fun _ => x.1 (.inl 1)) (fun _ _ => x.1 (.inl 0))
      (fun u _ _ => x.1 (.inr (.inl u))) (fun u _ _ => x.1 (.inr (.inr u))) x.2 0 0) (c,s) := by
    unfold QhatComplex
    fun_prop (disch := aesop)
  apply hraw.congr_of_eventuallyEq
  have hnear : ∀ᶠ x : Coeff T × ℂ in 𝓝 (c,s), 0 < x.2.re :=
    continuousAt_const.eventually_lt (Complex.continuous_re.comp continuous_snd).continuousAt hs
  filter_upwards [hnear] with x hx
  exact laplace_eq_raw_formula z hz sigma hsigma x.1 x.2 hx

/-- At every fixed closed-right frequency, the honest symbol is continuous
in the ORIGINAL finite coefficient topology, by its integrable finite sum. -/
theorem laplace_continuous_coefficients (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (s : ℂ) (hs : 0 ≤ s.re) : Continuous (fun c : Coeff T => laplace z sigma c s) := by
  have he : (fun c : Coeff T => laplace z sigma c s) = fun c => ∑ b,
      (c b : ℂ)*FMSA.causalComplexLaplace (recenteredBasis z (fun _ : Fin 1 => sigma) b 0) s := by
    funext c
    exact laplace_eq_sum z hz sigma c s hs
  rw [he]
  apply continuous_finsetSum
  intro b _
  fun_prop

/-- A nonzero constant minus a genuine finite kernel symbol is nontrivial.
No high-frequency pole formula or assumed inverse is used. -/
theorem constant_sub_laplace_exists_nonzero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (c : Coeff T) (a : ℝ) (ha : a ≠ 0) :
    ∃ s : ℂ, 0 < s.re ∧ (a : ℂ)-laplace z sigma c s ≠ 0 := by
  have hlim : Tendsto (fun s : ℝ => (a : ℂ)-laplace z sigma c (s : ℂ)) atTop (𝓝 (a : ℂ)) :=
    by simpa only [sub_zero] using tendsto_const_nhds.sub (laplace_real_tendsto_zero z hz sigma c)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hne : ∀ᶠ s : ℝ in atTop, (a : ℂ)-laplace z sigma c (s : ℂ) ≠ 0 :=
    hlim.eventually (isOpen_ne.mem_nhds haC)
  obtain ⟨s,hs,hn⟩ := ((eventually_gt_atTop (0 : ℝ)).and hne).exists
  exact ⟨(s : ℂ),by simpa using hs,hn⟩

/-- The nontrivial closure principle for NORMALIZED finite kernel symbols.
A nonzero constant OR nonzero actual compact field suffices; no supplied
limit zero-freeness, source bound or extra mathematical axiom is assumed. -/
theorem normalized_symbol_zero_free_at_closure
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (p : ℝ × Coeff T)
    (hp : p ∈ closure {q : ℝ × Coeff T | ∀ s : ℂ, 0 < s.re →
      (q.1 : ℂ)-laplace z sigma q.2 s ≠ 0})
    (hnontrivial : p.1 ≠ 0 ∨ compactKernel z sigma p.2 ≠ 0) :
    ∀ s : ℂ, 0 < s.re → (p.1 : ℂ)-laplace z sigma p.2 s ≠ 0 := by
  let F := fun q : ℝ × Coeff T => fun s : ℂ => (q.1 : ℂ)-laplace z sigma q.2 s
  have hA (q : ℝ × Coeff T) : AnalyticOnNhd ℂ (F q) {s : ℂ | 0 < s.re} :=
    analyticOnNhd_const.sub (laplace_analytic_right z hz sigma hsigma q.2)
  have hnon : ∃ s ∈ {s : ℂ | 0 < s.re}, F p s ≠ 0 := by
    rcases ne_or_eq p.1 0 with ha | ha
    · exact constant_sub_laplace_exists_nonzero z hz sigma p.2 p.1 ha
    · have hc : compactKernel z sigma p.2 ≠ 0 := hnontrivial.resolve_left (not_not_intro ha)
      obtain ⟨s,hs,hn⟩ := exists_nonzero_laplace_of_compact_ne_zero z hz sigma p.2 hc
      exact ⟨s,hs,by simpa only [F,ha,Complex.ofReal_zero,zero_sub,neg_ne_zero] using hn⟩
  apply FMSA.Convergence.HolomorphicZeroPersistence.zero_free_at_closure F _ p
    {s : ℂ | 0 < s.re} (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected hp (hA p) hnon
  · intro s hs
    have hmap : ContinuousAt (fun x : (ℝ × Coeff T) × ℂ => (x.1.2,x.2)) (p,s) := by fun_prop
    exact ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).continuousAt).sub
      (ContinuousAt.comp (f := fun x : (ℝ × Coeff T) × ℂ => (x.1.2,x.2)) (x := (p,s))
        (laplace_joint_continuousAt z hz sigma hsigma p.2 s hs) hmap)
  · intro q _
    exact (hA q).differentiableOn
  · intro q hq s hs
    exact hq s hs

/-- The coefficient-space field equals the actual row-density kernel at
ALL real arguments, before any root premise or compact restriction. -/
theorem actual_kernel_field {N : ℕ} (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (t : ℝ) :
    field z (sigma i) (rho i • bhCoefficient z rho sigma p i j) t =
      nonlinearCausalKernel z rho sigma p.1 p.2 t i j := by
  simp only [field,Pi.smul_apply,smul_eq_mul,nonlinearCausalKernel,Matrix.of_apply,
    recentered_eq_basis,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [recenteredBasis]
  ring

/-- Honest generic and physical actual Laplace integrals are identical. -/
theorem actual_kernel_laplace {N : ℕ} (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (s : ℂ) :
    laplace z (sigma i) (rho i • bhCoefficient z rho sigma p i j) s =
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j := by
  unfold laplace rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [Matrix.of_apply]
  simp_rw [actual_kernel_field]

/-- One-species actual canonicity means the honest scalar factor is nonzero
at every closed-right frequency, including the origin. -/
theorem scalar_canonical_factor_ne_zero
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (p : TailMatrix T 1 × TailMatrix T 1)
    (hp : p ∈ canonicalAmplitudes z rho sigma) (s : ℂ) (hs : 0 ≤ s.re) :
    1-laplace z (sigma 0) (rho 0 • bhCoefficient z rho sigma p 0 0) s ≠ 0 := by
  rw [actual_kernel_laplace]
  have h := (Matrix.isUnit_iff_isUnit_det _).mp (hp s hs)
  rw [Matrix.det_fin_one] at h
  exact isUnit_iff_ne_zero.mp h

/-- Both ACTUAL scalar BH equations use the SAME honest kernel factor.
This is the bridge for the finite-escape argument, not assumed identities. -/
theorem scalar_bh_factor_equations
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (K : TailMatrix T 1)
    (p : TailMatrix T 1 × TailMatrix T 1) (hroot : IsRoot z rho sigma K p.1 p.2) (u : T) :
    (p.1 u 0 0 : ℂ)*(1-laplace z (sigma 0) (rho 0 • bhCoefficient z rho sigma p 0 0) (z u : ℂ)) =
      ((2*Real.pi*K u 0 0/z u : ℝ) : ℂ) ∧
    (2*(Real.pi : ℂ))*(p.2 u 0 0 : ℂ)*
        (1-laplace z (sigma 0) (rho 0 • bhCoefficient z rho sigma p 0 0) (z u : ℂ)) =
      (secondRHS z rho sigma p.1 p.2 u 0 0 : ℂ) := by
  have hL := congrFun (congrFun
    (FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_root_dictionary z hz rho sigma hsigma p u) 0) 0
  rw [← actual_kernel_laplace] at hL
  have hlap : laplace z (sigma 0) (rho 0 • bhCoefficient z rho sigma p 0 0) (z u : ℂ) =
      ((rho 0*dressedQhat z rho sigma p.1 p.2 (z u) 0 0 : ℝ) : ℂ) := by
    simpa [Matrix.diagonal_mul,FMSA.Convergence.ActualBHAmplitudeRecovery.rootTransformSymbol,
      nonlinearRootRecenteredTransform,MSAMixture.edgeLo] using hL
  have hd : p.1 u 0 0*(1-rho 0*dressedQhat z rho sigma p.1 p.2 (z u) 0 0) =
      2*Real.pi*K u 0 0/z u := by simpa [firstLHS,MSAMixture.edgeLo] using hroot.1 u 0 0
  have hg : 2*Real.pi*p.2 u 0 0*(1-rho 0*dressedQhat z rho sigma p.1 p.2 (z u) 0 0) =
      secondRHS z rho sigma p.1 p.2 u 0 0 := by simpa [secondLHS,MSAMixture.edgeLo,mul_assoc] using hroot.2 u 0 0
  rw [hlap]
  constructor
  · exact_mod_cast hd
  · exact_mod_cast hg

/-- Real scaling of the whole honest symbol, including zero frequency. -/
theorem laplace_smul (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ)
    (a : ℝ) (c : Coeff T) (s : ℂ) (hs : 0 ≤ s.re) :
    laplace z sigma (a • c) s = (a : ℂ)*laplace z sigma c s := by
  rw [laplace_eq_sum z hz sigma (a • c) s hs,laplace_eq_sum z hz sigma c s hs,Finset.mul_sum]
  simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,mul_assoc]

end FMSA.Convergence.FiniteKernelLaplace

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.field_laplace_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.field_laplace_integrable

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_eq_sum

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.field_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.field_integrable

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.field_real_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.field_real_damped_integrable

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_eq_of_compact_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_eq_of_compact_eq

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_coefficient_norm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_coefficient_norm_bound

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_bound_by_compact_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_bound_by_compact_kernel

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_injective_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_injective_on_compact

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.exists_nonzero_laplace_of_compact_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.exists_nonzero_laplace_of_compact_ne_zero

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_real_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_real_tendsto_zero

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.field_eq_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.field_eq_explicit

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.raw_q_eq_causalShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.raw_q_eq_causalShift

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_eq_raw_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_eq_raw_formula

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_analytic_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_analytic_right

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_joint_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_joint_continuousAt

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_continuous_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_continuous_coefficients

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.constant_sub_laplace_exists_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.constant_sub_laplace_exists_nonzero

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.normalized_symbol_zero_free_at_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.normalized_symbol_zero_free_at_closure

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.actual_kernel_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.actual_kernel_field

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.actual_kernel_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.actual_kernel_laplace

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.scalar_canonical_factor_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.scalar_canonical_factor_ne_zero

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.scalar_bh_factor_equations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.scalar_bh_factor_equations

/-- info: 'FMSA.Convergence.FiniteKernelLaplace.laplace_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteKernelLaplace.laplace_smul
