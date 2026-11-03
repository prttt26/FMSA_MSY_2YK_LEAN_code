import MSAConvergence.FiniteKernelLaplace
import MSAConvergence.MaximalMSAConvergence

/-! Scalar canonical BH roots at bounded strength have bounded amplitudes.
Normalization is in the finite ACTUAL kernel image, never redundant coefficients. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ScalarCanonicalProperness
open FMSA.Paper FMSA.MatrixQ0 FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ScalarKernelSource FMSA.Convergence.FiniteKernelLaplace
open FMSA.Convergence.CanonicalNeighborhood
variable {T : Type*} [Fintype T]

abbrev KernelImage (z : T → ℝ) (sigma : ℝ) := (compactKernel z sigma).range

def actualKernelElement (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : KernelImage z (sigma 0) :=
  ⟨actualCompactKernel z rho sigma p 0 0,⟨rho 0 • bhCoefficient z rho sigma p 0 0,rfl⟩⟩

def frame (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : ℝ × KernelImage z (sigma 0) :=
  (1,actualKernelElement z rho sigma p)

def normalizer (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : ℝ := ‖frame z rho sigma p‖⁻¹

def normalizedFrame (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : ℝ × KernelImage z (sigma 0) :=
  normalizer z rho sigma p • frame z rho sigma p

def normalizedCoefficients (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : Coeff T :=
  kernelSection z (sigma 0) (normalizedFrame z rho sigma p).2

def normalizedFactor (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) (s : ℂ) : ℂ :=
  (normalizer z rho sigma p : ℂ)-laplace z (sigma 0) (normalizedCoefficients z rho sigma p) s

/-- The affine frame prevents a zero normalization denominator. -/
theorem frame_ne_zero (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : frame z rho sigma p ≠ 0 := by
  intro h
  have hh := congrArg Prod.fst h
  simp [frame] at hh

/-- The normalization is positive at every amplitude point. -/
theorem normalizer_pos (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : 0 < normalizer z rho sigma p :=
  inv_pos.mpr (norm_pos_iff.mpr (frame_ne_zero z rho sigma p))

/-- Normalized ACTUAL kernel frames lie on the compact unit sphere. -/
theorem normalized_frame_norm (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) : ‖normalizedFrame z rho sigma p‖ = 1 := by
  rw [normalizedFrame,norm_smul,Real.norm_eq_abs,abs_of_pos (normalizer_pos z rho sigma p)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (frame_ne_zero z rho sigma p))

/-- The first normalized frame coordinate is the positive scalar multiplier. -/
theorem normalized_frame_fst (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) :
    (normalizedFrame z rho sigma p).1 = normalizer z rho sigma p := by
  simp [normalizedFrame,frame]

/-- Reduced coefficients reproduce the ENTIRE scaled actual kernel. -/
theorem normalized_compact_kernel (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (p : TailMatrix T 1 × TailMatrix T 1) :
    compactKernel z (sigma 0) (normalizedCoefficients z rho sigma p) =
      compactKernel z (sigma 0) (normalizer z rho sigma p • (rho 0 • bhCoefficient z rho sigma p 0 0)) := by
  rw [normalizedCoefficients,kernel_section_rightInverse,map_smul]
  rfl

/-- The normalized symbol is exactly a positive multiple of the honest
actual scalar factor, not an asserted normalized zero-free family. -/
theorem normalized_factor_eq_actual
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ) (hsigma : 0 < sigma 0)
    (p : TailMatrix T 1 × TailMatrix T 1) (s : ℂ) (hs : 0 ≤ s.re) :
    normalizedFactor z rho sigma p s = (normalizer z rho sigma p : ℂ)*
      (1-laplace z (sigma 0) (rho 0 • bhCoefficient z rho sigma p 0 0) s) := by
  unfold normalizedFactor
  rw [laplace_eq_of_compact_eq z (sigma 0) hsigma _ _ (normalized_compact_kernel z rho sigma p) s,
    laplace_smul z hz (sigma 0) _ _ s hs]
  ring

/-- Actual canonicity gives true normalized zero-freeness throughout the
whole closed right half-plane. -/
theorem normalized_factor_ne_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ) (hsigma : 0 < sigma 0)
    (p : TailMatrix T 1 × TailMatrix T 1) (hp : p ∈ canonicalAmplitudes z rho sigma)
    (s : ℂ) (hs : 0 ≤ s.re) : normalizedFactor z rho sigma p s ≠ 0 := by
  rw [normalized_factor_eq_actual z hz rho sigma hsigma p s hs]
  exact mul_ne_zero (by exact_mod_cast (normalizer_pos z rho sigma p).ne')
    (scalar_canonical_factor_ne_zero z rho sigma p hp s hs)

/-- The normalized second source is derived from the actual BH source by
the proved compact-kernel factorization, retaining every tail index. -/
theorem normalized_source_eq_actual
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ) (hsigma : 0 < sigma 0)
    (p : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    sourceMap z (z u) (normalizedCoefficients z rho sigma p) =
      normalizer z rho sigma p*rho 0*secondRHS z rho sigma p.1 p.2 u 0 0 := by
  rw [source_map_eq_of_compact_eq z hz (sigma 0) hsigma (z u) (hz u) _ _
    (normalized_compact_kernel z rho sigma p),map_smul,map_smul,
    source_map_at_actual_rate z hz rho sigma p u 0 0]
  simp only [smul_eq_mul,mul_assoc]

/-- Both normalized BH equations are ACTUAL equalities, with the second
right side a continuous linear source of the normalized actual kernel. -/
theorem normalized_bh_equations
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ) (hsigma : ∀ i, 0 < sigma i)
    (K : TailMatrix T 1) (p : TailMatrix T 1 × TailMatrix T 1)
    (hroot : IsRoot z rho sigma K p.1 p.2) (u : T) :
    (p.1 u 0 0 : ℂ)*normalizedFactor z rho sigma p (z u : ℂ) =
      (normalizer z rho sigma p : ℂ)*((2*Real.pi*K u 0 0/z u : ℝ) : ℂ) ∧
    (p.2 u 0 0 : ℂ)*((rho 0 : ℂ)*(2*(Real.pi : ℂ))*normalizedFactor z rho sigma p (z u : ℂ)) =
      (sourceMap z (z u) (normalizedCoefficients z rho sigma p) : ℂ) := by
  obtain ⟨hD,hG⟩ := scalar_bh_factor_equations z hz rho sigma (fun i => (hsigma i).le) K p hroot u
  rw [normalized_factor_eq_actual z hz rho sigma (hsigma 0) p (z u : ℂ) (by simpa using (hz u).le)]
  constructor
  · linear_combination (normalizer z rho sigma p : ℂ)*hD
  · rw [normalized_source_eq_actual z hz rho sigma (hsigma 0) p u]
    push_cast
    linear_combination (rho 0 : ℂ)*(normalizer z rho sigma p : ℂ)*hG

set_option maxHeartbeats 600000 in
/-- Every sequence of ACTUAL scalar canonical roots with bounded finite
strengths has a convergent amplitude subsequence. Kernel normalization and
both BH equations discharge boundedness; no amplitude bound is supplied. -/
theorem canonical_root_sequence_has_convergent_subsequence
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : 0 < rho 0)
    (K : ℕ → TailMatrix T 1) (p : ℕ → TailMatrix T 1 × TailMatrix T 1)
    (B : ℝ) (hB : ∀ n, ‖K n‖ ≤ B)
    (hroot : ∀ n, IsRoot z rho sigma (K n) (p n).1 (p n).2)
    (hcanon : ∀ n, p n ∈ canonicalAmplitudes z rho sigma) :
    ∃ v : ℕ → ℕ, StrictMono v ∧ ∃ a : TailMatrix T 1 × TailMatrix T 1,
      Tendsto (fun n => p (v n)) atTop (𝓝 a) := by
  let V := KernelImage z (sigma 0)
  have hball (n : ℕ) : (K n,normalizedFrame z rho sigma (p n)) ∈
      Metric.closedBall (0 : TailMatrix T 1 × (ℝ × V)) (max B 1) := by
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,normalized_frame_norm]
    exact max_le_max (hB n) le_rfl
  obtain ⟨q,_hq,v,hv,hpair⟩ := (isCompact_closedBall (0 : TailMatrix T 1 × (ℝ × V)) (max B 1)).tendsto_subseq hball
  have hK : Tendsto (fun n => K (v n)) atTop (𝓝 q.1) := hpair.fst_nhds
  have hw : Tendsto (fun n => normalizedFrame z rho sigma (p (v n))) atTop (𝓝 q.2) := hpair.snd_nhds
  have hnorm : ‖q.2‖ = 1 := tendsto_nhds_unique hw.norm
    (by simpa only [normalized_frame_norm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  let a := q.2.1
  let c := kernelSection z (sigma 0) q.2.2
  let F := fun s : ℂ => (a : ℂ)-laplace z (sigma 0) c s
  let dstar := fun u : T => ((a : ℂ)*((2*Real.pi*q.1 u 0 0/z u : ℝ) : ℂ)/F (z u : ℂ)).re
  let gstar := fun u : T => ((sourceMap z (z u) c : ℂ)/
    ((rho 0 : ℂ)*(2*(Real.pi : ℂ))*F (z u : ℂ))).re
  have ha : Tendsto (fun n => normalizer z rho sigma (p (v n))) atTop (𝓝 a) := by
    simpa only [normalized_frame_fst] using hw.fst_nhds
  have hc : Tendsto (fun n => normalizedCoefficients z rho sigma (p (v n))) atTop (𝓝 c) :=
    (kernelSection z (sigma 0)).continuous.continuousAt.tendsto.comp hw.snd_nhds
  have hparam : Tendsto (fun n => (normalizer z rho sigma (p (v n)),
      normalizedCoefficients z rho sigma (p (v n)))) atTop (𝓝 (a,c)) := ha.prodMk_nhds hc
  have hclose : (a,c) ∈ closure {r : ℝ × Coeff T | ∀ s : ℂ, 0 < s.re →
      (r.1 : ℂ)-laplace z (sigma 0) r.2 s ≠ 0} := by
    apply mem_closure_of_tendsto hparam
    exact Eventually.of_forall (fun n s hs =>
      normalized_factor_ne_zero z hz rho sigma (hsigma 0) (p (v n)) (hcanon (v n)) s hs.le)
  have hnon : a ≠ 0 ∨ compactKernel z (sigma 0) c ≠ 0 := by
    rcases ne_or_eq a 0 with hn | he
    · exact Or.inl hn
    · right
      intro hc0
      have hq0 : q.2 = 0 := by
        apply Prod.ext he
        apply Subtype.ext
        exact (kernel_section_rightInverse z (sigma 0) q.2.2).symm.trans hc0
      rw [hq0,norm_zero] at hnorm
      norm_num at hnorm
  have hF : ∀ s : ℂ, 0 < s.re → F s ≠ 0 :=
    normalized_symbol_zero_free_at_closure z hz (sigma 0) (hsigma 0).le (a,c) hclose hnon
  have hFn (u : T) : Tendsto (fun n => normalizedFactor z rho sigma (p (v n)) (z u : ℂ))
      atTop (𝓝 (F (z u : ℂ))) := by
    have hL : Tendsto (fun n => laplace z (sigma 0) (normalizedCoefficients z rho sigma (p (v n))) (z u : ℂ))
        atTop (𝓝 (laplace z (sigma 0) c (z u : ℂ))) :=
      (laplace_continuous_coefficients z hz (sigma 0) (z u : ℂ) (by simpa using (hz u).le)).continuousAt.tendsto.comp hc
    have haC : Tendsto (fun n => (normalizer z rho sigma (p (v n)) : ℂ)) atTop (𝓝 (a : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp ha
    exact haC.sub hL
  have hD (u : T) : Tendsto (fun n => (p (v n)).1 u 0 0) atTop (𝓝 (dstar u)) := by
    have hR : Tendsto (fun n => ((2*Real.pi*K (v n) u 0 0/z u : ℝ) : ℂ))
        atTop (𝓝 ((2*Real.pi*q.1 u 0 0/z u : ℝ) : ℂ)) :=
      (show Continuous (fun k : TailMatrix T 1 => ((2*Real.pi*k u 0 0/z u : ℝ) : ℂ)) by fun_prop).continuousAt.tendsto.comp hK
    have hdiv := ((Complex.continuous_ofReal.continuousAt.tendsto.comp ha).mul hR).div
      (hFn u) (hF (z u : ℂ) (by simpa using hz u))
    have he (n : ℕ) : (normalizer z rho sigma (p (v n)) : ℂ)*
        ((2*Real.pi*K (v n) u 0 0/z u : ℝ) : ℂ)/normalizedFactor z rho sigma (p (v n)) (z u : ℂ) =
        ((p (v n)).1 u 0 0 : ℂ) := by
      symm
      apply (eq_div_iff (normalized_factor_ne_zero z hz rho sigma (hsigma 0) (p (v n))
        (hcanon (v n)) (z u : ℂ) (by simpa using (hz u).le))).mpr
      exact (normalized_bh_equations z hz rho sigma hsigma (K (v n)) (p (v n)) (hroot (v n)) u).1
    have hreal := Complex.continuous_re.continuousAt.tendsto.comp
      (hdiv.congr' (Eventually.of_forall he))
    simpa only [Function.comp_def,Complex.ofReal_re] using hreal
  have hG (u : T) : Tendsto (fun n => (p (v n)).2 u 0 0) atTop (𝓝 (gstar u)) := by
    have hsource : Tendsto (fun n => (sourceMap z (z u) (normalizedCoefficients z rho sigma (p (v n))) : ℂ))
        atTop (𝓝 (sourceMap z (z u) c : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((sourceMap z (z u)).continuous_of_finiteDimensional.continuousAt.tendsto.comp hc)
    have hden : (rho 0 : ℂ)*(2*(Real.pi : ℂ))*F (z u : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by exact_mod_cast hrho.ne')
        (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
        (hF (z u : ℂ) (by simpa using hz u))
    have hdiv := hsource.div ((hFn u).const_mul ((rho 0 : ℂ)*(2*(Real.pi : ℂ)))) hden
    have he (n : ℕ) : (sourceMap z (z u) (normalizedCoefficients z rho sigma (p (v n))) : ℂ)/
        ((rho 0 : ℂ)*(2*(Real.pi : ℂ))*normalizedFactor z rho sigma (p (v n)) (z u : ℂ)) =
        ((p (v n)).2 u 0 0 : ℂ) := by
      symm
      apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by exact_mod_cast hrho.ne')
        (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
        (normalized_factor_ne_zero z hz rho sigma (hsigma 0) (p (v n)) (hcanon (v n))
          (z u : ℂ) (by simpa using (hz u).le)))).mpr
      exact (normalized_bh_equations z hz rho sigma hsigma (K (v n)) (p (v n)) (hroot (v n)) u).2
    have hreal := Complex.continuous_re.continuousAt.tendsto.comp
      (hdiv.congr' (Eventually.of_forall he))
    simpa only [Function.comp_def,Complex.ofReal_re] using hreal
  refine ⟨v,hv,((fun u _ _ => dstar u),(fun u _ _ => gstar u)),?_⟩
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro u
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i
    fin_cases j
    exact hD u
  · apply tendsto_pi_nhds.mpr
    intro u
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i
    fin_cases j
    exact hG u

/-- At vacuum every actual root is the explicit affine finite-strength root.
No canonical or amplitude-bound premise is used. -/
theorem vacuum_root_sequence_has_convergent_subsequence
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : Fin 1 → ℝ)
    (K : ℕ → TailMatrix T 1) (p : ℕ → TailMatrix T 1 × TailMatrix T 1)
    (B : ℝ) (hB : ∀ n, ‖K n‖ ≤ B)
    (hroot : ∀ n, IsRoot z 0 sigma (K n) (p n).1 (p n).2) :
    ∃ v : ℕ → ℕ, StrictMono v ∧ ∃ a : TailMatrix T 1 × TailMatrix T 1,
      Tendsto (fun n => p (v n)) atTop (𝓝 a) := by
  let R := fun k : TailMatrix T 1 => (nonlinearZeroDensityDt z k,nonlinearZeroDensityG z sigma k)
  have hR : Continuous R := by unfold R nonlinearZeroDensityDt nonlinearZeroDensityG; fun_prop
  have he (n : ℕ) : p n = R (K n) := by
    obtain ⟨hD,hG⟩ := (nonlinearRoot_zero_density_iff z sigma (K n) (p n).1 (p n).2
      (fun u => (hz u).ne')).mp (hroot n)
    apply Prod.ext
    · funext u i j
      exact hD u i j
    · funext u i j
      exact hG u i j
  obtain ⟨k,_hk,v,hv,hKv⟩ := (isCompact_closedBall (0 : TailMatrix T 1) B).tendsto_subseq
    (fun n => by simpa only [Metric.mem_closedBall,dist_zero_right] using hB n)
  exact ⟨v,hv,R k,(hR.continuousAt.tendsto.comp hKv).congr' (Eventually.of_forall (fun n => (he (v n)).symm))⟩

/-- Scalar root-sequence compactness covers EVERY physical nonnegative
density, including the separate vacuum case. -/
theorem nonnegative_canonical_root_sequence_has_convergent_subsequence
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : ℕ → TailMatrix T 1) (p : ℕ → TailMatrix T 1 × TailMatrix T 1)
    (B : ℝ) (hB : ∀ n, ‖K n‖ ≤ B)
    (hroot : ∀ n, IsRoot z rho sigma (K n) (p n).1 (p n).2)
    (hcanon : ∀ n, p n ∈ canonicalAmplitudes z rho sigma) :
    ∃ v : ℕ → ℕ, StrictMono v ∧ ∃ a : TailMatrix T 1 × TailMatrix T 1,
      Tendsto (fun n => p (v n)) atTop (𝓝 a) := by
  by_cases hzero : rho 0 = 0
  · have hrzero : rho = 0 := by funext i; fin_cases i; exact hzero
    apply vacuum_root_sequence_has_convergent_subsequence z hz sigma K p B hB
    intro n
    simpa only [hrzero] using hroot n
  · exact canonical_root_sequence_has_convergent_subsequence z hz rho sigma hsigma
      (lt_of_le_of_ne (hrho 0) (Ne.symm hzero)) K p B hB hroot hcanon

/-- ACTUAL scalar canonical roots have a UNIFORM amplitude bound over EVERY
bounded finite-strength set. Original amplitude norm, arbitrary tail signs
and repeated rates, physical vacuum included; no root curve is supplied. -/
theorem canonical_roots_uniformly_bounded
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : TailMatrix T 1, ∀ p : TailMatrix T 1 × TailMatrix T 1,
      ‖K‖ ≤ B → IsRoot z rho sigma K p.1 p.2 → p ∈ canonicalAmplitudes z rho sigma → ‖p‖ ≤ C := by
  by_contra hn
  push Not at hn
  have hex (n : ℕ) : ∃ K : TailMatrix T 1, ∃ p : TailMatrix T 1 × TailMatrix T 1,
      ‖K‖ ≤ B ∧ IsRoot z rho sigma K p.1 p.2 ∧ p ∈ canonicalAmplitudes z rho sigma ∧ (n : ℝ) < ‖p‖ :=
    hn (n : ℝ) (Nat.cast_nonneg n)
  choose K p hK hroot hcanon hbig using hex
  obtain ⟨v,hv,a,hconv⟩ := nonnegative_canonical_root_sequence_has_convergent_subsequence z hz rho sigma hsigma hrho
    K p B hK hroot hcanon
  have hsmall : ∀ᶠ n in atTop, ‖p (v n)‖ < ‖a‖+1 :=
    hconv.norm.eventually (Iio_mem_nhds (by linarith : ‖a‖ < ‖a‖+1))
  have hnat : Tendsto (fun n => (v n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hv.tendsto_atTop
  obtain ⟨n,hnsmall,hnlarge⟩ := (hsmall.and (hnat.eventually (eventually_gt_atTop (‖a‖+1)))).exists
  have hp := hbig (v n)
  linarith

/-- Every finite scalar canonical root prefix is bounded, WITHOUT a supplied
amplitude bound or endpoint value. Continuity is not needed for this bound. -/
theorem canonical_prefix_uniformly_bounded
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (p : ℝ → TailMatrix T 1 × TailMatrix T 1) (b : ℝ)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico 0 b, ‖p t‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := canonical_roots_uniformly_bounded z hz rho sigma hsigma hrho (b*‖K‖)
  refine ⟨C,hC,?_⟩
  intro t ht
  apply hbound (t • K) (p t) _ (hroot t ht) (hcanon t ht)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)

/-- The finite amplitude-escape alternative is IMPOSSIBLE for one species,
for arbitrary physical nonnegative density and every finite tail-strength set. -/
theorem no_finite_canonical_amplitude_escape
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (p : ℝ → TailMatrix T 1 × TailMatrix T 1) (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  obtain ⟨C,_hC,hbound⟩ := canonical_prefix_uniformly_bounded z hz rho sigma hsigma hrho K p b hroot hcanon
  intro hescape
  obtain ⟨t,ht,_hc,hn⟩ := hescape C 0 hb
  exact (not_lt_of_ge (hbound t ht)) hn

open FMSA.Convergence.MaximalCanonicalBranch FMSA.Convergence.CanonicalEndpointContinuation
open FMSA.Convergence.MaximalMSAConvergence FMSA.Paper.StableIntervalRadius

/-- A finite constructed scalar maximal canonical branch is bounded up to
its excluded endpoint, without adding a physical boundedness premise. -/
theorem maximal_finite_prefix_bounded
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (seed : TailMatrix T 1 × TailMatrix T 1) (M : MaximalBranch z rho sigma K seed)
    (hfinite : M.bound ≠ ⊤) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 M.bound.toReal, ‖M.path t‖ ≤ B := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal := (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal :=
    (congrArg initialCouplings hbound).trans (initial_couplings_ofReal _ hb)
  apply canonical_prefix_uniformly_bounded z hz rho sigma hsigma hrho K M.path _
  · simpa only [hset] using M.roots
  · simpa only [hset] using M.canonical

/-- A finite constructed scalar maximal endpoint has a GENUINE approaching
actual root cluster with a physical Fourier zero. Escape is excluded, not
assumed away; no endpoint value, full limit or unique cluster is asserted. -/
theorem maximal_finite_endpoint_has_physical_cluster
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (hv : vacMix rho sigma ≠ 0) (seed : TailMatrix T 1 × TailMatrix T 1)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    HasPhysicalEndpointCluster z rho sigma K M.path M.bound.toReal := by
  have hK : ∀ u i j, K u i j = K u j i := by intro u i j; fin_cases i; fin_cases j; rfl
  obtain ⟨B,_hB,hbound⟩ := maximal_finite_prefix_bounded z hz rho sigma hsigma hrho K seed M hfinite
  obtain ⟨a,u,_ha,hu,ht,hpa,hr,hcl,hf⟩ := maximal_bounded_endpoint_cluster z hz rho sigma hsigma hrho K hK hv seed M hfinite B hbound
  exact ⟨a,u,hu,ht,hpa,hr,hcl,hf⟩

/-- At EVERY physical one-species HS state eta<1, construct the intrinsic
maximal initial canonical branch. Any FINITE endpoint has a true physical
Fourier-zero cluster; no root curve, inverse, maximality, amplitude bound or
endpoint limit is supplied. The complex Taylor lower-bound question remains. -/
theorem exists_hs_maximal_branch_with_finite_axis_cluster
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (hv : 0 < vacMix rho sigma)
    (K : TailMatrix T 1) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ → 0 < M.bound.toReal ∧
        HasPhysicalEndpointCluster z rho sigma K M.path M.bound.toReal) := by
  obtain ⟨M,hM⟩ := exists_scalar_hs_maximal_branch z hz rho sigma hsigma hrho K hv
  refine ⟨M,hM,fun hfinite => ⟨ENNReal.toReal_pos (ne_of_gt M.positive) hfinite,?_⟩⟩
  exact maximal_finite_endpoint_has_physical_cluster z hz rho sigma hsigma hrho K hv.ne' _ M hfinite

end FMSA.Convergence.ScalarCanonicalProperness

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.frame_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.frame_ne_zero

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalizer_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalizer_pos

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalized_frame_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalized_frame_norm

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalized_frame_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalized_frame_fst

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalized_compact_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalized_compact_kernel

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalized_factor_eq_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalized_factor_eq_actual

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalized_factor_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalized_factor_ne_zero

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalized_source_eq_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalized_source_eq_actual

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.normalized_bh_equations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.normalized_bh_equations

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.canonical_root_sequence_has_convergent_subsequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.canonical_root_sequence_has_convergent_subsequence

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.vacuum_root_sequence_has_convergent_subsequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.vacuum_root_sequence_has_convergent_subsequence

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.nonnegative_canonical_root_sequence_has_convergent_subsequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.nonnegative_canonical_root_sequence_has_convergent_subsequence

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.canonical_roots_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.canonical_roots_uniformly_bounded

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.canonical_prefix_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.canonical_prefix_uniformly_bounded

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.no_finite_canonical_amplitude_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.no_finite_canonical_amplitude_escape

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.maximal_finite_prefix_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.maximal_finite_prefix_bounded

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.maximal_finite_endpoint_has_physical_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.maximal_finite_endpoint_has_physical_cluster

/-- info: 'FMSA.Convergence.ScalarCanonicalProperness.exists_hs_maximal_branch_with_finite_axis_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalProperness.exists_hs_maximal_branch_with_finite_axis_cluster
