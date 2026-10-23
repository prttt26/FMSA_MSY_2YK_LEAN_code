import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPAmplitude
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitiveTangent

/-! Independent reduced double-propagator real-space construction.
The actual HS Q kernel and actual resolvent-dressed amplitudes are used.
Density factors are explicit on internal species indices. No equality with
the exact-BH primitive first variation is assumed or asserted. -/
noncomputable section
open MeasureTheory Real Set Filter
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def dpSeedQ (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  q z σ (amplitudeA z ρ σ 0 0) (amplitudeQp z ρ σ 0 0)
    (W z ρ 0 0) (C z ρ σ 0 0) i j r

def dpB (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  ∑ u, dpBareAmplitude z ρ σ K u i j *
    (Ici (edgeHi σ i j)).indicator (fun t => exp (-z u*(t-edgeHi σ i j))) r

theorem dpB_measurable (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) : Measurable (dpB z ρ σ K i j) := by
  unfold dpB
  have hm : MeasurableSet (Ici (edgeHi σ i j)) := measurableSet_Ici
  fun_prop

theorem dpB_bounded (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j : Fin N) :
    ∃ M : ℝ, ∀ r, |dpB z ρ σ K i j r| ≤ M := by
  refine ⟨∑ u, |dpBareAmplitude z ρ σ K u i j|, fun r => ?_⟩
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro u hu
  by_cases hr : r ∈ Ici (edgeHi σ i j)
  · rw [indicator_of_mem hr, abs_mul, abs_of_pos (exp_pos _)]
    apply mul_le_of_le_one_right (abs_nonneg _)
    apply exp_le_one_iff.mpr
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg (hz u).le (sub_nonneg.mpr hr))
  · simp only [indicator_of_notMem hr, mul_zero, abs_zero]
    exact abs_nonneg _

theorem dpB_symmetric (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) (r : ℝ) :
    dpB z ρ σ K i j r = dpB z ρ σ K j i r := by
  have he : edgeHi σ i j = edgeHi σ j i := by unfold edgeHi; ring
  unfold dpB
  apply Finset.sum_congr rfl
  intro u hu
  have h := congrFun (congrFun (dpBareAmplitude_symmetric z ρ σ K hK u) j) i
  simpa only [Matrix.transpose_apply, he] using congrArg
    (fun a => a * (Ici (edgeHi σ j i)).indicator (fun t => exp (-z u*(t-edgeHi σ j i))) r) h

def dpTriple (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j m n : Fin N) (r : ℝ) : ℝ :=
  ∫ u : ℝ, ∫ v : ℝ, dpSeedQ z ρ σ i m u * dpB z ρ σ K m n (r+u+v) * dpSeedQ z ρ σ j n v

theorem dpSingle_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (a b i j : Fin N) (r : ℝ) :
    Integrable (fun u => dpSeedQ z ρ σ a b u * dpB z ρ σ K i j (r+u)) := by
  have hq : Integrable (dpSeedQ z ρ σ a b) := q_integrable z hz σ _ _ _ _ hσ a b
  obtain ⟨M, hb⟩ := dpB_bounded z hz ρ σ K i j
  exact hq.mul_bdd ((dpB_measurable z ρ σ K i j).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hb (r+u)))

theorem dpTriple_inner_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (i j m n : Fin N) (r u : ℝ) :
    Integrable (fun v => dpSeedQ z ρ σ i m u * dpB z ρ σ K m n (r+u+v) * dpSeedQ z ρ σ j n v) := by
  convert (dpSingle_integrable z hz ρ σ hσ K j n m n (r+u)).const_mul (dpSeedQ z ρ σ i m u) using 1
  funext v
  ring

theorem dpTriple_joint_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (i j m n : Fin N) (r : ℝ) :
    Integrable (Function.uncurry (fun u v =>
      dpSeedQ z ρ σ i m u * dpB z ρ σ K m n (r+u+v) * dpSeedQ z ρ σ j n v))
      (volume.prod volume) := by
  have hi : Integrable (dpSeedQ z ρ σ i m) := q_integrable z hz σ _ _ _ _ hσ i m
  have hj : Integrable (dpSeedQ z ρ σ j n) := q_integrable z hz σ _ _ _ _ hσ j n
  obtain ⟨M, hb⟩ := dpB_bounded z hz ρ σ K m n
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => dpB z ρ σ K m n (r+p.1+p.2))
      (volume.prod volume) :=
    ((dpB_measurable z ρ σ K m n).comp (by fun_prop)).aestronglyMeasurable
  have h := (hi.mul_prod hj).mul_bdd hm
    (Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hb (r+p.1+p.2)))
  convert h using 1
  funext p
  dsimp only [Function.uncurry]
  ring

theorem dpTriple_outer_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (i j m n : Fin N) (r : ℝ) :
    Integrable (fun u => ∫ v : ℝ,
      dpSeedQ z ρ σ i m u * dpB z ρ σ K m n (r+u+v) * dpSeedQ z ρ σ j n v) := by
  simpa only [Function.uncurry] using
    (dpTriple_joint_integrable z hz ρ σ hσ K i j m n r).integral_prod_left

theorem dpTriple_swap (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j m n : Fin N) (r : ℝ) :
    dpTriple z ρ σ K i j m n r = dpTriple z ρ σ K j i n m r := by
  unfold dpTriple
  rw [integral_integral_swap (dpTriple_joint_integrable z hz ρ σ hσ K i j m n r)]
  apply integral_congr_ae (Eventually.of_forall _)
  intro v
  apply integral_congr_ae (Eventually.of_forall _)
  intro u
  rw [dpB_symmetric z ρ σ K hK m n]
  rw [show r+u+v=r+v+u by ring]
  ring

/-- The four independent DP convolution terms, with the two reflected HS
Q kernels changed to their original compact-support integration variables. -/
def dpW (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  dpB z ρ σ K i j r -
    (∑ n, ρ n * ∫ u : ℝ, dpSeedQ z ρ σ j n u * dpB z ρ σ K i n (r+u)) -
    (∑ m, ρ m * ∫ u : ℝ, dpSeedQ z ρ σ i m u * dpB z ρ σ K m j (r+u)) +
    ∑ m, ∑ n, ρ m*ρ n*dpTriple z ρ σ K i j m n r

theorem dpW_symmetric (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) (r : ℝ) :
    dpW z ρ σ K i j r = dpW z ρ σ K j i r := by
  have hB := dpB_symmetric z ρ σ K hK
  have ht : (∑ m, ∑ n, ρ m*ρ n*dpTriple z ρ σ K i j m n r) =
      ∑ m, ∑ n, ρ m*ρ n*dpTriple z ρ σ K j i m n r := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [dpTriple_swap z hz ρ σ hσ K hK i j m n r]
    ring
  unfold dpW
  rw [ht, hB i j r]
  have he : (∑ n, ρ n * ∫ u : ℝ, dpSeedQ z ρ σ j n u * dpB z ρ σ K i n (r+u)) =
      ∑ n, ρ n * ∫ u : ℝ, dpSeedQ z ρ σ j n u * dpB z ρ σ K n i (r+u) := by simp_rw [hB i]
  have hf : (∑ m, ρ m * ∫ u : ℝ, dpSeedQ z ρ σ i m u * dpB z ρ σ K m j (r+u)) =
      ∑ m, ρ m * ∫ u : ℝ, dpSeedQ z ρ σ i m u * dpB z ρ σ K j m (r+u) := by
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    apply integral_congr_ae (Eventually.of_forall _)
    intro u
    rw [hB m j]
  rw [he, hf]
  ring

def dpCorrelation (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ := (dpW z ρ σ K i j r - dpW z ρ σ K i j (-r))/(2*π*r)

theorem dpCorrelation_symmetric (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) (r : ℝ) :
    dpCorrelation z ρ σ K i j r = dpCorrelation z ρ σ K j i r := by
  simp only [dpCorrelation, dpW_symmetric z hz ρ σ hσ K hK i j]

theorem dpSeedQ_support (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ)
    (hr : dpSeedQ z ρ σ i j r ≠ 0) : r ∈ Icc (edgeLo σ i j) (edgeHi σ i j) := by
  constructor
  · by_contra h
    exact hr (by simp [dpSeedQ, q, lt_of_not_ge h])
  · by_contra h
    have hh : ¬r ≤ edgeHi σ i j := h
    by_cases hl : r < edgeLo σ i j
    · exact hr (by simp [dpSeedQ, q, hl])
    · exact hr (by simp [dpSeedQ, q, hl, hh, W, C, Wt, Ct])

theorem dpB_eq_zero_below (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : r < edgeHi σ i j) : dpB z ρ σ K i j r = 0 := by
  simp only [dpB, indicator_of_notMem (show r ∉ Ici (edgeHi σ i j) from not_le_of_gt hr),
    mul_zero, Finset.sum_const_zero]

theorem dpTriple_eq_zero_below (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j m n : Fin N) (r : ℝ) (hr : r < -edgeHi σ i j) :
    dpTriple z ρ σ K i j m n r = 0 := by
  unfold dpTriple
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  simp only [Pi.zero_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  simp only [Pi.zero_apply]
  by_cases hi : dpSeedQ z ρ σ i m u=0
  · simp only [hi, zero_mul]
  by_cases hj : dpSeedQ z ρ σ j n v=0
  · simp only [hj, mul_zero]
  have hu := (dpSeedQ_support z ρ σ i m u hi).2
  have hv := (dpSeedQ_support z ρ σ j n v hj).2
  have hb : r+u+v < edgeHi σ m n := by unfold edgeHi at *; linarith
  rw [dpB_eq_zero_below z ρ σ K m n _ hb, mul_zero, zero_mul]

theorem dpW_eq_zero_below (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (i j : Fin N) (r : ℝ)
    (hr : r < -edgeHi σ i j) : dpW z ρ σ K i j r = 0 := by
  have hb : r < edgeHi σ i j := by unfold edgeHi at *; linarith [hσ i, hσ j]
  have hl : ∀ n, (∫ u : ℝ, dpSeedQ z ρ σ j n u * dpB z ρ σ K i n (r+u))=0 := by
    intro n
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    simp only [Pi.zero_apply]
    by_cases hq : dpSeedQ z ρ σ j n u=0
    · simp only [hq, zero_mul]
    have hu := (dpSeedQ_support z ρ σ j n u hq).2
    have he : r+u < edgeHi σ i n := by unfold edgeHi at *; linarith [hσ i]
    rw [dpB_eq_zero_below z ρ σ K i n _ he, mul_zero]
  have hm : ∀ m, (∫ u : ℝ, dpSeedQ z ρ σ i m u * dpB z ρ σ K m j (r+u))=0 := by
    intro m
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    simp only [Pi.zero_apply]
    by_cases hq : dpSeedQ z ρ σ i m u=0
    · simp only [hq, zero_mul]
    have hu := (dpSeedQ_support z ρ σ i m u hq).2
    have he : r+u < edgeHi σ m j := by unfold edgeHi at *; linarith [hσ j]
    rw [dpB_eq_zero_below z ρ σ K m j _ he, mul_zero]
  simp only [dpW, dpB_eq_zero_below z ρ σ K i j r hb, hl, hm,
    dpTriple_eq_zero_below z ρ σ K _ _ _ _ r hr, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

end FMSA.ExactMSA.MultiTailMixture
