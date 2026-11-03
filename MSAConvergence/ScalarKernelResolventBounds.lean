import MSAConvergence.FiniteKernelLaplace

/-! Projective compactness of zero-free finite-kernel scalar factors.
The estimate supplies uniform inverse and linear-source control, with no
amplitude bound or special scalar BH coefficient formula as a premise. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.ScalarKernelResolventBounds
open FMSA.Convergence.ScalarKernelSource FMSA.Convergence.FiniteKernelLaplace
variable {T : Type*} [Fintype T]

abbrev KernelImage (z : T → ℝ) (sigma : ℝ) := (compactKernel z sigma).range
abbrev Frame (z : T → ℝ) (sigma : ℝ) := ℝ × KernelImage z sigma

def symbol (z : T → ℝ) (sigma : ℝ) (w : Frame z sigma) (s : ℂ) : ℂ :=
  (w.1 : ℂ)-laplace z sigma (kernelSection z sigma w.2) s

def Admissible (z : T → ℝ) (sigma : ℝ) : Set (Frame z sigma) :=
  {w | ‖w‖ = 1 ∧ ∀ s : ℂ, 0 < s.re → symbol z sigma w s ≠ 0}

theorem symbol_continuous (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ)
    (s : ℂ) (hs : 0 ≤ s.re) : Continuous (fun w : Frame z sigma => symbol z sigma w s) := by
  exact (Complex.continuous_ofReal.comp continuous_fst).sub
    ((laplace_continuous_coefficients z hz sigma s hs).comp
      ((kernelSection z sigma).continuous.comp continuous_snd))

theorem frame_nontrivial (z : T → ℝ) (sigma : ℝ) (w : Frame z sigma) (hw : ‖w‖ = 1) :
    w.1 ≠ 0 ∨ compactKernel z sigma (kernelSection z sigma w.2) ≠ 0 := by
  rcases ne_or_eq w.1 0 with ha|ha
  · exact Or.inl ha
  right
  intro hq
  have hw0 : w = 0 := by
    apply Prod.ext ha
    apply Subtype.ext
    exact (kernel_section_rightInverse z sigma w.2).symm.trans hq
  rw [hw0,norm_zero] at hw
  norm_num at hw

/-- Hurwitz closure applies after a genuine finite-kernel normalization.
The normalized frame's unit norm rules out the identically zero scalar. -/
theorem admissible_closed (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    IsClosed (Admissible z sigma) := by
  apply closure_subset_iff_isClosed.mp
  intro w hw
  have hn : ‖w‖ = 1 := (closure_minimal
    (fun _ h => h.1 : Admissible z sigma ⊆ {q : Frame z sigma | ‖q‖ = 1})
    (isClosed_eq continuous_norm continuous_const)) hw
  have hm : Continuous (fun q : Frame z sigma => (q.1,kernelSection z sigma q.2)) :=
    continuous_fst.prodMk ((kernelSection z sigma).continuous.comp continuous_snd)
  have hc : (w.1,kernelSection z sigma w.2) ∈ closure
      {q : ℝ × Coeff T | ∀ s : ℂ, 0 < s.re → (q.1 : ℂ)-laplace z sigma q.2 s ≠ 0} := by
    apply closure_mono _ (mem_closure_image hm.continuousAt hw)
    rintro _ ⟨v,hv,rfl⟩
    exact hv.2
  exact ⟨hn,normalized_symbol_zero_free_at_closure z hz sigma hsigma _ hc
    (frame_nontrivial z sigma w hn)⟩

theorem admissible_compact (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    IsCompact (Admissible z sigma) := by
  apply (isCompact_sphere (0 : Frame z sigma) 1).of_isClosed_subset
    (admissible_closed z hz sigma hsigma)
  intro w hw
  simpa only [Metric.mem_sphere,dist_zero_right] using hw.1

theorem admissible_nonempty (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) :
    (Admissible z sigma).Nonempty := by
  refine ⟨(1,0),?_,?_⟩
  · simp [Prod.norm_def]
  · intro s hs
    have hzero : laplace z sigma (0 : Coeff T) s = 0 := by
      rw [laplace_eq_sum z hz sigma 0 s hs.le]
      simp
    simpa only [symbol,map_zero,hzero,Complex.ofReal_one,sub_zero] using (one_ne_zero : (1 : ℂ) ≠ 0)

/-- Every fixed interior point has a positive common modulus on the entire
compact family, including limits of coefficients of arbitrarily large norm. -/
theorem uniform_normalized_modulus (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (s : ℂ) (hs : 0 < s.re) :
    ∃ e : ℝ, 0 < e ∧ ∀ w ∈ Admissible z sigma, e ≤ ‖symbol z sigma w s‖ := by
  obtain ⟨w,hw,hmin⟩ := (admissible_compact z hz sigma hsigma).exists_isMinOn
    (admissible_nonempty z hz sigma) (symbol_continuous z hz sigma s hs.le).norm.continuousOn
  exact ⟨‖symbol z sigma w s‖,norm_pos_iff.mpr (hw.2 s hs),hmin⟩

def frame (z : T → ℝ) (sigma : ℝ) (c : Coeff T) : Frame z sigma :=
  (1,⟨compactKernel z sigma c,⟨c,rfl⟩⟩)

def scale (z : T → ℝ) (sigma : ℝ) (c : Coeff T) : ℝ := ‖frame z sigma c‖⁻¹

def normalized (z : T → ℝ) (sigma : ℝ) (c : Coeff T) : Frame z sigma :=
  scale z sigma c • frame z sigma c

theorem frame_ne_zero (z : T → ℝ) (sigma : ℝ) (c : Coeff T) : frame z sigma c ≠ 0 := by
  intro h
  have hh := congrArg Prod.fst h
  simp [frame] at hh

theorem scale_pos (z : T → ℝ) (sigma : ℝ) (c : Coeff T) : 0 < scale z sigma c :=
  inv_pos.mpr (norm_pos_iff.mpr (frame_ne_zero z sigma c))

theorem normalized_norm (z : T → ℝ) (sigma : ℝ) (c : Coeff T) : ‖normalized z sigma c‖ = 1 := by
  rw [normalized,norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos z sigma c)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (frame_ne_zero z sigma c))

theorem normalized_symbol (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 < sigma)
    (c : Coeff T) (s : ℂ) (hs : 0 ≤ s.re) :
    symbol z sigma (normalized z sigma c) s = 
      (scale z sigma c : ℂ)*(1-laplace z sigma c s) := by
  have he : compactKernel z sigma (kernelSection z sigma (normalized z sigma c).2) = 
      compactKernel z sigma (scale z sigma c • c) := by
    rw [kernel_section_rightInverse,map_smul]
    rfl
  have hf : (normalized z sigma c).1 = scale z sigma c := by simp [normalized,frame]
  unfold symbol
  rw [hf,laplace_eq_of_compact_eq z sigma hsigma _ _ he s,laplace_smul z hz sigma _ _ s hs]
  ring

theorem normalized_admissible (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 < sigma)
    (c : Coeff T) (hc : ∀ s : ℂ, 0 < s.re → 1-laplace z sigma c s ≠ 0) :
    normalized z sigma c ∈ Admissible z sigma := by
  refine ⟨normalized_norm z sigma c,?_⟩
  intro s hs
  rw [normalized_symbol z hz sigma hsigma c s hs.le]
  exact mul_ne_zero (by exact_mod_cast (scale_pos z sigma c).ne') (hc s hs)

/-- Point evaluation is coercive on the zero-free scalar family in the
honest compact-kernel norm. No amplitude relation or bound is supplied. -/
theorem uniform_factor_coercivity (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (hsigma : 0 < sigma) (s : ℂ) (hs : 0 < s.re) :
    ∃ e : ℝ, 0 < e ∧ ∀ c : Coeff T,
      (∀ w : ℂ, 0 < w.re → 1-laplace z sigma c w ≠ 0) →
      e * ‖frame z sigma c‖ ≤ ‖1-laplace z sigma c s‖ := by
  obtain ⟨e,he,hbound⟩ := uniform_normalized_modulus z hz sigma hsigma.le s hs
  refine ⟨e,he,?_⟩
  intro c hc
  have h := hbound _ (normalized_admissible z hz sigma hsigma c hc)
  rw [normalized_symbol z hz sigma hsigma c s hs.le,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (scale_pos z sigma c)] at h
  have hn : 0 < ‖frame z sigma c‖ := norm_pos_iff.mpr (frame_ne_zero z sigma c)
  have hm := mul_le_mul_of_nonneg_left h hn.le
  have heq : ‖frame z sigma c‖ * (scale z sigma c * ‖1-laplace z sigma c s‖) =
      ‖1-laplace z sigma c s‖ := by
    rw [scale,← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
  rw [heq] at hm
  simpa only [mul_comm e] using hm

/-- Source resolvents are uniformly bounded on the entire zero-free scalar
family. This reusable estimate does not assume scalar physical amplitudes. -/
theorem uniform_inverse_source_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : ℝ) (hsigma : 0 < sigma) (s : ℝ) (hs : 0 < s) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ c : Coeff T,
      (∀ w : ℂ, 0 < w.re → 1-laplace z sigma c w ≠ 0) →
      ‖(1-laplace z sigma c (s : ℂ))⁻¹‖ ≤ C₀ ∧
      ‖(sourceMap z s c : ℂ)/(1-laplace z sigma c (s : ℂ))‖ ≤ C₁ := by
  obtain ⟨e,he,hfactor⟩ := uniform_factor_coercivity z hz sigma hsigma (s : ℂ) (by simpa using hs)
  obtain ⟨B,hB,hsource⟩ := source_map_bound_by_compact_kernel z hz sigma hsigma s hs
  refine ⟨e⁻¹,inv_pos.mpr he,B/e,div_nonneg hB he.le,?_⟩
  intro c hc
  have hF : 0 < ‖1-laplace z sigma c (s : ℂ)‖ := norm_pos_iff.mpr (hc _ (by simpa using hs))
  have hco := hfactor c hc
  have hN : 1 ≤ ‖frame z sigma c‖ := by
    change (1 : ℝ) ≤ max ‖(1 : ℝ)‖ ‖compactKernel z sigma c‖
    simpa only [norm_one] using le_max_left (1 : ℝ) ‖compactKernel z sigma c‖
  have hq : ‖compactKernel z sigma c‖ ≤ ‖frame z sigma c‖ := by
    change ‖compactKernel z sigma c‖ ≤ max ‖(1 : ℝ)‖ ‖compactKernel z sigma c‖
    simpa only [norm_one] using le_max_right (1 : ℝ) ‖compactKernel z sigma c‖
  constructor
  · rw [norm_inv]
    simpa only [one_div] using
      one_div_le_one_div_of_le he ((le_mul_of_one_le_right he.le hN).trans hco)
  · rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    apply (div_le_div_iff₀ hF he).mpr
    calc
      |sourceMap z s c| * e ≤ (B * ‖frame z sigma c‖)*e :=
        mul_le_mul_of_nonneg_right ((hsource c).trans (mul_le_mul_of_nonneg_left hq hB)) he.le
      _ = B*(e * ‖frame z sigma c‖) := by ring
      _ ≤ B * ‖1-laplace z sigma c (s : ℂ)‖ := mul_le_mul_of_nonneg_left hco hB

end FMSA.Convergence.ScalarKernelResolventBounds
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.symbol_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.symbol_continuous
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.frame_nontrivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.frame_nontrivial
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.admissible_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.admissible_closed
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.admissible_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.admissible_compact
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.admissible_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.admissible_nonempty
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.uniform_normalized_modulus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.uniform_normalized_modulus
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.frame_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.frame_ne_zero
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.scale_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.scale_pos
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.normalized_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.normalized_norm
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.normalized_symbol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.normalized_symbol
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.normalized_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.normalized_admissible
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.uniform_factor_coercivity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.uniform_factor_coercivity
/-- info: 'FMSA.Convergence.ScalarKernelResolventBounds.uniform_inverse_source_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarKernelResolventBounds.uniform_inverse_source_bounds
