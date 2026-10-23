import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPKernelFourier

/-! Continuity of the independent DP convolutions. The closed contact
representative of the bare source is the only excluded radial point. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem realPlusConv_integrable_of_bounded (f g : ℝ → ℝ) (hf : Integrable f)
    (hg : Measurable g) (M : ℝ) (hb : ∀ t, ‖g t‖ ≤ M) (r : ℝ) :
    Integrable (fun u => f u*g (r+u)) :=
  hf.mul_bdd (hg.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun u => hb (r+u)))

theorem realPlusConv_bounded (f g : ℝ → ℝ) (hf : Integrable f)
    (hg : Measurable g) (M : ℝ) (hb : ∀ t, ‖g t‖ ≤ M) (r : ℝ) :
    ‖realPlusConv f g r‖ ≤ (∫ u : ℝ, ‖f u‖)*M := by
  unfold realPlusConv
  calc
    _ ≤ ∫ u : ℝ, ‖f u*g (r+u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, ‖f u‖*M := integral_mono_ae
      (realPlusConv_integrable_of_bounded f g hf hg M hb r).norm (hf.norm.mul_const M)
      (Eventually.of_forall (fun u => by
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb (r+u)) (norm_nonneg _)))
    _ = _ := integral_mul_const M _

theorem realPlusConv_continuous_of_ae_shift (f g : ℝ → ℝ) (hf : Integrable f)
    (hg : Measurable g) (M : ℝ) (hb : ∀ t, ‖g t‖ ≤ M)
    (hc : ∀ r, ∀ᵐ u : ℝ, ContinuousAt (fun x => g (x+u)) r) :
    Continuous (realPlusConv f g) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  unfold realPlusConv
  apply continuousAt_of_dominated (bound := fun u => ‖f u‖*M)
  · exact Eventually.of_forall (fun x =>
      (realPlusConv_integrable_of_bounded f g hf hg M hb x).aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => Eventually.of_forall (fun u => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb (x+u)) (norm_nonneg _)))
  · exact hf.norm.mul_const M
  · filter_upwards [hc r] with u hu
    exact continuousAt_const.mul hu

theorem dpB_continuousAt_off_contact (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j : Fin N) (r : ℝ) (hr : r ≠ edgeHi σ i j) :
    ContinuousAt (dpB z ρ σ K i j) r := by
  rcases lt_or_gt_of_ne hr with h | h
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) r).congr
    filter_upwards [eventually_lt_nhds h] with t ht
    simp [dpB, indicator_of_notMem (show t ∉ Ici (edgeHi σ i j) from not_le.mpr ht)]
  · have hc : Continuous (fun r => ∑ u, dpBareAmplitude z ρ σ K u i j *
        exp (-z u*(r-edgeHi σ i j))) := by fun_prop
    apply hc.continuousAt.congr
    filter_upwards [eventually_gt_nhds h] with t ht
    simp [dpB, indicator_of_mem (mem_Ici.mpr ht.le)]

theorem dpSingle_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (a b i j : Fin N) : Continuous (realPlusConv (dpSeedQ z ρ σ a b) (dpB z ρ σ K i j)) := by
  obtain ⟨M, hb⟩ := dpB_bounded z hz ρ σ K i j
  apply realPlusConv_continuous_of_ae_shift _ _ (q_integrable z hz σ _ _ _ _ hσ a b)
    (dpB_measurable z ρ σ K i j) M (by simpa only [Real.norm_eq_abs] using hb)
  intro r
  filter_upwards [volume.ae_ne (edgeHi σ i j-r)] with u hu
  have he : r+u ≠ edgeHi σ i j := by intro he; apply hu; linarith
  exact (dpB_continuousAt_off_contact z ρ σ K i j (r+u) he).comp
    (f := fun x => x+u) (by fun_prop)

theorem dpTriple_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (i j m n : Fin N) : Continuous (dpTriple z ρ σ K i j m n) := by
  have hc := dpSingle_continuous z hz ρ σ hσ K j n m n
  obtain ⟨M, hb⟩ := dpB_bounded z hz ρ σ K m n
  have hq : Integrable (dpSeedQ z ρ σ j n) := q_integrable z hz σ _ _ _ _ hσ j n
  have hi : Continuous (realPlusConv (dpSeedQ z ρ σ i m)
      (realPlusConv (dpSeedQ z ρ σ j n) (dpB z ρ σ K m n))) := by
    apply realPlusConv_continuous_of_ae_shift _ _ (q_integrable z hz σ _ _ _ _ hσ i m)
      hc.measurable ((∫ u : ℝ, ‖dpSeedQ z ρ σ j n u‖)*M)
      (realPlusConv_bounded _ _ hq (dpB_measurable z ρ σ K m n) M
        (by simpa only [Real.norm_eq_abs] using hb))
    intro r
    exact Eventually.of_forall (fun u => hc.continuousAt.comp
      (f := fun x => x+u) (by fun_prop))
  have he : dpTriple z ρ σ K i j m n = realPlusConv (dpSeedQ z ρ σ i m)
      (realPlusConv (dpSeedQ z ρ σ j n) (dpB z ρ σ K m n)) :=
    funext (dpTriple_eq_nested_plusConv z ρ σ K i j m n)
  rwa [he]

theorem dpW_continuousAt_off_contact (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : r ≠ edgeHi σ i j) :
    ContinuousAt (dpW z ρ σ K i j) r := by
  have hc (a b c d : Fin N) := dpSingle_continuous z hz ρ σ hσ K a b c d
  have hleft : Continuous (fun r => ∑ n, ρ n*realPlusConv (dpSeedQ z ρ σ j n)
      (dpB z ρ σ K i n) r) :=
    continuous_finsetSum _ (fun n _ => continuous_const.mul (hc j n i n))
  have hright : Continuous (fun r => ∑ m, ρ m*realPlusConv (dpSeedQ z ρ σ i m)
      (dpB z ρ σ K m j) r) :=
    continuous_finsetSum _ (fun m _ => continuous_const.mul (hc i m m j))
  have htriple : Continuous (fun r => ∑ m, ∑ n, ρ m*ρ n*dpTriple z ρ σ K i j m n r) :=
    continuous_finsetSum _ (fun m _ => continuous_finsetSum _ (fun n _ =>
      continuous_const.mul (dpTriple_continuous z hz ρ σ hσ K i j m n)))
  exact ((dpB_continuousAt_off_contact z ρ σ K i j r hr).sub hleft.continuousAt).sub
    hright.continuousAt |>.add htriple.continuousAt

end FMSA.ExactMSA.MultiTailMixture
