import MSAConvergence.BinaryCanonicalChannels
import MSAConvergence.ScalarKernelResolventBounds

/-! Actual binary escape exclusion under explicit exchange symmetry of the
finite BH kernel. No amplitude bound or channel inverse bound is supplied. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.BinaryCanonicalProperness
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ScalarKernelSource FMSA.Convergence.FiniteKernelLaplace
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.BinaryCanonicalChannels
variable {T : Type*} [Fintype T]

private theorem entry_le (K : TailMatrix T 2) (B : ℝ) (hB : ‖K‖ ≤ B)
    (u : T) (i j : Fin 2) : |K u i j| ≤ B := by
  exact ((norm_le_pi_norm (K u i) j).trans
    ((norm_le_pi_norm (K u) i).trans (norm_le_pi_norm K u))).trans hB

private theorem row_bound (v : Fin 2 → ℝ) (B : ℝ) (h : ∀ j, |v j| ≤ B) (b : Bool) :
    |rowMode v b| ≤ 2*B := by
  have hs : |sgn b| = 1 := by cases b <;> norm_num [sgn]
  calc
    |rowMode v b| ≤ |v 0|+|sgn b*v 1| := abs_add_le _ _
    _ = |v 0|+|v 1| := by rw [abs_mul,hs,one_mul]
    _ ≤ 2*B := by linarith [h 0,h 1]

/-- Uniform bounds for the actual first and second BH row channels at one
rate, over every bounded strength set and every exchange-symmetric canonical root. -/
theorem channel_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (B : ℝ) (u : T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : TailMatrix T 2, ∀ p : Amp T,
      ‖K‖ ≤ B → IsRoot z (density r) (diameter a) K p.1 p.2 →
      p ∈ canonicalAmplitudes z (density r) (diameter a) → KernelExchange z r a p →
      ∀ i : Fin 2, ∀ b : Bool, |rowMode (p.1 u i) b| ≤ C ∧ |rowMode (p.2 u i) b| ≤ C := by
  obtain ⟨C₀,hC₀,C₁,hC₁,hbound⟩ :=
    ScalarKernelResolventBounds.uniform_inverse_source_bounds z hz a ha (z u) (hz u)
  let CD := |2*Real.pi/z u| *(2*max B 0)*C₀
  let CG := C₁/(2*Real.pi*r)
  have hcr : 0 < 2*Real.pi*r := by positivity
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have hCG : 0 ≤ CG := div_nonneg hC₁ hcr.le
  refine ⟨CD+CG,add_nonneg hCD hCG,?_⟩
  intro K p hK hp hc he i b
  have hF := mode_factor_ne_zero z hz r a p he hc b (z u : ℂ) (by simpa using (hz u).le)
  have hb := hbound (modeCoeff z r a p b) (fun w hw =>
    mode_factor_ne_zero z hz r a p he hc b w hw.le)
  have hkm : |rowMode (K u i) b| ≤ 2*max B 0 :=
    row_bound _ _ (fun j => (entry_le K B hK u i j).trans (le_max_left _ _)) b
  have hD : |rowMode (p.1 u i) b| ≤ CD := by
    have hd := (eq_div_iff hF).mpr (first_mode_equation z hz r a ha.le K p hp he u i b)
    have hn := congrArg norm hd
    rw [norm_div,norm_mul] at hn
    simp only [Complex.norm_real,Real.norm_eq_abs] at hn
    rw [div_eq_mul_inv,← norm_inv] at hn
    rw [hn]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hkm (abs_nonneg _)) hb.1
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
  have hG : |rowMode (p.2 u i) b| ≤ CG := by
    have hg := (eq_div_iff hF).mpr (second_mode_equation z hz r a ha.le K p hp he u i b)
    have hs : ‖(sourceMap z (z u) (coeff z r a p i 0+sgn b • coeff z r a p i 1) : ℂ)/
        modeFactor z r a p b (z u : ℂ)‖ ≤ C₁ := by
      rw [row_coeff_mode z r a p he i b,map_smul]
      fin_cases i <;> cases b <;> simpa [sgn,smul_eq_mul,modeFactor] using hb.2
    have hn := congrArg norm hg
    rw [norm_mul] at hn
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hcr] at hn
    apply (le_div_iff₀ hcr).mpr
    calc
      |rowMode (p.2 u i) b| *(2*Real.pi*r) =
          ‖(sourceMap z (z u) (coeff z r a p i 0+sgn b • coeff z r a p i 1) : ℂ)/
            modeFactor z r a p b (z u : ℂ)‖ := by linarith [hn]
      _ ≤ C₁ := hs
  exact ⟨hD.trans (le_add_of_nonneg_right hCG),hG.trans (le_add_of_nonneg_left hCD)⟩

private theorem entries_of_channels (v : Fin 2 → ℝ) (C : ℝ)
    (hp : |rowMode v false| ≤ C) (hm : |rowMode v true| ≤ C) (j : Fin 2) : |v j| ≤ C := by
  simp only [rowMode,sgn,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hp hm
  rcases abs_le.mp hp with ⟨hp₁,hp₂⟩
  rcases abs_le.mp hm with ⟨hm₁,hm₂⟩
  fin_cases j
  · change |v 0| ≤ C
    apply abs_le.mpr
    constructor <;> linarith
  · change |v 1| ≤ C
    apply abs_le.mpr
    constructor <;> linarith

/-- The ORIGINAL product/Pi amplitude norm is uniformly bounded. The exchange
condition concerns the actual finite kernel, not a separately fitted model. -/
theorem canonical_roots_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : TailMatrix T 2, ∀ p : Amp T,
      ‖K‖ ≤ B → IsRoot z (density r) (diameter a) K p.1 p.2 →
      p ∈ canonicalAmplitudes z (density r) (diameter a) → KernelExchange z r a p → ‖p‖ ≤ C := by
  classical
  choose C hC hbound using channel_uniformly_bounded z hz r a hr ha B
  refine ⟨∑ u, C u,Finset.sum_nonneg (fun u _ => hC u),?_⟩
  intro K p hK hp hc he
  rw [Prod.norm_def,max_le_iff]
  constructor
  all_goals
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun u _ => hC u))).mpr
    intro u
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun u _ => hC u))).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun u _ => hC u))).mpr
    intro j
    rw [Real.norm_eq_abs]
  · exact (entries_of_channels _ _ (hbound u K p hK hp hc he i false).1
      (hbound u K p hK hp hc he i true).1 j).trans
        (Finset.single_le_sum (fun u _ => hC u) (Finset.mem_univ u))
  · exact (entries_of_channels _ _ (hbound u K p hK hp hc he i false).2
      (hbound u K p hK hp hc he i true).2 j).trans
        (Finset.single_le_sum (fun u _ => hC u) (Finset.mem_univ u))

/-- No finite canonical binary prefix can escape in amplitude while its
actual finite kernels retain exchange symmetry. No continuity or endpoint value is assumed. -/
theorem no_finite_canonical_amplitude_escape (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (K : TailMatrix T 2)
    (p : ℝ → Amp T) (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z (density r) (diameter a) (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z (density r) (diameter a))
    (hexchange : ∀ t ∈ Ico 0 b, KernelExchange z r a (p t)) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  obtain ⟨C,_hC,hbound⟩ := canonical_roots_uniformly_bounded z hz r a hr ha (b*‖K‖)
  intro hescape
  obtain ⟨t,ht,_hc,hn⟩ := hescape C 0 hb
  apply (not_lt_of_ge (hbound (t • K) (p t) _ (hroot t ht) (hcanon t ht) (hexchange t ht))) hn
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)

end FMSA.Convergence.BinaryCanonicalProperness
/-- info: 'FMSA.Convergence.BinaryCanonicalProperness.channel_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalProperness.channel_uniformly_bounded
/-- info: 'FMSA.Convergence.BinaryCanonicalProperness.canonical_roots_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalProperness.canonical_roots_uniformly_bounded
/-- info: 'FMSA.Convergence.BinaryCanonicalProperness.no_finite_canonical_amplitude_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalProperness.no_finite_canonical_amplitude_escape
