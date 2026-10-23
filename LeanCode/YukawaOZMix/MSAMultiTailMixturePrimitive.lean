import LeanCode.YukawaOZMix.MSAMultiTailMixtureBoundary

/-! The Q-side spectral coefficient is the transform of an actual full-line
Baxter primitive. This does not identify its derivative with the physical
radial DCF, or establish evenness/species reciprocity from the BH root. -/
noncomputable section
open MeasureTheory Set Filter
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture

/-- Actual weighted correlation is L1; no joint Fubini hypothesis remains. -/
theorem complex_corr_weighted_integrable (f g : ℝ → ℂ) (s : ℂ)
    (hf : Integrable (fun t => f t * Complex.exp (-s * t)))
    (hg : Integrable (fun t => g t * Complex.exp (s * t))) :
    Integrable (fun r : ℝ => (∫ t : ℝ, f t * g (t - r)) * Complex.exp (-s * r)) := by
  have hi := (complex_corr_joint_integrable f g s hf hg).integral_prod_right
  simpa only [Function.uncurry, integral_mul_const] using hi

variable {N : ℕ} {ι : Type*} [Fintype ι]

def qCrossCorr (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j l : Fin N) (r : ℝ) : ℂ :=
  ∫ t : ℝ, (q z σ A qp W C i l t : ℂ) * (q z σ A qp W C j l (t - r) : ℂ)

/-- Actual full-line Baxter primitive whose transform is the Q-product expression. -/
def baxterPrimitive (z : ι → ℝ) (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ) : ℂ :=
  (q z σ A qp W C i j r : ℂ) + (q z σ A qp W C j i (-r) : ℂ) -
    ∑ l, (ρ l : ℂ) * qCrossCorr z σ A qp W C i j l r

theorem qCrossCorr_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j l : Fin N) :
    Integrable (fun r => qCrossCorr z σ A qp W C i j l r * Complex.exp (-(Complex.I * k) * r)) := by
  have hf := q_complex_weighted_integrable z hz σ A qp W C hσ (Complex.I * k) (by simp) i l
  have hg := q_complex_weighted_integrable z hz σ A qp W C hσ (-(Complex.I * k)) (by simp) j l
  simp only [neg_neg] at hg
  have hi := complex_corr_weighted_integrable
    (fun t => (q z σ A qp W C i l t : ℂ))
    (fun t => (q z σ A qp W C j l t : ℂ)) (Complex.I * k) hf hg
  simpa only [qCrossCorr] using hi

theorem reflectedQ_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j : Fin N) :
    Integrable (fun r : ℝ => (q z σ A qp W C i j (-r) : ℂ) * Complex.exp (-(Complex.I * k) * r)) := by
  have hi := q_complex_weighted_integrable z hz σ A qp W C hσ (-(Complex.I * k)) (by simp) i j
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hi
  simpa only [Function.comp_def, Complex.ofReal_neg, neg_neg, mul_neg, neg_mul] using hn

theorem reflectedQ_fourier (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    (∫ r : ℝ, (q z σ A qp W C i j (-r) : ℂ) * Complex.exp (-(Complex.I * k) * r)) =
      fourierQ z σ A qp W C (-k) i j := by
  have he : (fun r : ℝ => (q z σ A qp W C i j (-r) : ℂ) * Complex.exp (-(Complex.I * k) * r)) =
      (fun r => (fun t : ℝ => (q z σ A qp W C i j t : ℂ) * Complex.exp ((Complex.I * k) * t)) (-r)) := by
    funext r
    simp only [Complex.ofReal_neg, mul_neg, neg_mul]
  rw [he]
  calc
    _ = ∫ t : ℝ, (q z σ A qp W C i j t : ℂ) * Complex.exp ((Complex.I * k) * t) :=
      integral_neg_eq_self _ volume
    _ = _ := by simp only [fourierQ, Complex.ofReal_neg, mul_neg, neg_neg]

theorem baxterPrimitive_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j : Fin N) :
    Integrable (fun r : ℝ => baxterPrimitive z ρ σ A qp W C i j r * Complex.exp (-(Complex.I * k) * r)) := by
  have he : (fun r : ℝ => baxterPrimitive z ρ σ A qp W C i j r * Complex.exp (-(Complex.I * k) * r)) =
      (fun r => (q z σ A qp W C i j r : ℂ) * Complex.exp (-(Complex.I * k) * r) +
        (q z σ A qp W C j i (-r) : ℂ) * Complex.exp (-(Complex.I * k) * r) -
        ∑ l, (ρ l : ℂ) * (qCrossCorr z σ A qp W C i j l r * Complex.exp (-(Complex.I * k) * r))) := by
    funext r
    unfold baxterPrimitive
    rw [sub_mul, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  exact ((q_complex_weighted_integrable z hz σ A qp W C hσ _ (by simp) i j).add
    (reflectedQ_axis_weighted_integrable z hz σ A qp W C hσ k j i)).sub
    (integrable_finsetSum _ (fun l _ =>
      (qCrossCorr_axis_weighted_integrable z hz σ A qp W C hσ k i j l).const_mul _))

/-- Actual full-line primitive integral equals C_Q, including zero k.
This is not the radial sine transform of the separately defined correlation. -/
theorem baxterPrimitive_fourier (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j : Fin N) :
    (∫ r : ℝ, baxterPrimitive z ρ σ A qp W C i j r * Complex.exp (-(Complex.I * k) * r)) =
      spectralBaxterC z ρ σ A qp W C k i j := by
  have hc : ∀ l, Integrable (fun r => (ρ l : ℂ) *
      (qCrossCorr z σ A qp W C i j l r * Complex.exp (-(Complex.I * k) * r))) :=
    fun l => (qCrossCorr_axis_weighted_integrable z hz σ A qp W C hσ k i j l).const_mul _
  have hf : Integrable (fun r => (q z σ A qp W C i j r : ℂ) * Complex.exp (-(Complex.I * k) * r)) :=
    q_complex_weighted_integrable z hz σ A qp W C hσ _ (by simp) i j
  have hg := reflectedQ_axis_weighted_integrable z hz σ A qp W C hσ k j i
  have hab : Integrable (fun r => (q z σ A qp W C i j r : ℂ) * Complex.exp (-(Complex.I * k) * r) +
      (q z σ A qp W C j i (-r) : ℂ) * Complex.exp (-(Complex.I * k) * r)) := hf.add hg
  have he : (fun r : ℝ => baxterPrimitive z ρ σ A qp W C i j r * Complex.exp (-(Complex.I * k) * r)) =
      (fun r => (q z σ A qp W C i j r : ℂ) * Complex.exp (-(Complex.I * k) * r) +
        (q z σ A qp W C j i (-r) : ℂ) * Complex.exp (-(Complex.I * k) * r) -
        ∑ l, (ρ l : ℂ) * (qCrossCorr z σ A qp W C i j l r * Complex.exp (-(Complex.I * k) * r))) := by
    funext r
    unfold baxterPrimitive
    rw [sub_mul, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_sub hab (integrable_finsetSum _ (fun l _ => hc l)), integral_add hf hg,
    reflectedQ_fourier, integral_finsetSum _ (fun l _ => hc l)]
  simp_rw [integral_const_mul]
  have ht : ∀ l, (∫ r : ℝ, qCrossCorr z σ A qp W C i j l r * Complex.exp (-(Complex.I * k) * r)) =
      fourierQ z σ A qp W C k i l * fourierQ z σ A qp W C (-k) j l :=
    fun l => (fourierQ_product_eq_corr z hz σ A qp W C hσ k i j l).symm
  simp_rw [ht, ← fourierQ_conj]
  unfold spectralBaxterC fourierQ
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The actual primitive has transpose/reflection parity, not automatic evenness. -/
theorem qCrossCorr_reflection (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j l : Fin N) (r : ℝ) :
    qCrossCorr z σ A qp W C j i l (-r) = qCrossCorr z σ A qp W C i j l r := by
  unfold qCrossCorr
  have he : (fun t : ℝ => (q z σ A qp W C j l t : ℂ) * (q z σ A qp W C i l (t - -r) : ℂ)) =
      (fun t => (fun v : ℝ => (q z σ A qp W C i l v : ℂ) *
        (q z σ A qp W C j l (v - r) : ℂ)) (t + r)) := by
    funext t
    simp only [sub_neg_eq_add, add_sub_cancel_right]
    ring
  rw [he]
  exact integral_add_right_eq_self
    (fun v : ℝ => (q z σ A qp W C i l v : ℂ) * (q z σ A qp W C j l (v - r) : ℂ)) r

theorem baxterPrimitive_reflection (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    baxterPrimitive z ρ σ A qp W C j i (-r) = baxterPrimitive z ρ σ A qp W C i j r := by
  unfold baxterPrimitive
  simp_rw [neg_neg, qCrossCorr_reflection]
  ring

theorem qCrossCorr_eq_ordered (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j l : Fin N) (r : ℝ) :
    qCrossCorr z σ A qp W C i j l r =
      ∫ t : ℝ, (q z σ A qp W C i l (t + r) : ℂ) * (q z σ A qp W C j l t : ℂ) := by
  unfold qCrossCorr
  have he : (fun t : ℝ => (q z σ A qp W C i l (t + r) : ℂ) * (q z σ A qp W C j l t : ℂ)) =
      (fun t => (fun v : ℝ => (q z σ A qp W C i l v : ℂ) *
        (q z σ A qp W C j l (v - r) : ℂ)) (t + r)) := by
    funext t
    simp only [add_sub_cancel_right]
  rw [he]
  exact (integral_add_right_eq_self
    (fun v : ℝ => (q z σ A qp W C i l v : ℂ) * (q z σ A qp W C j l (v - r) : ℂ)) r).symm

theorem baxterPrimitive_positive_of_order (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N)
    (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r) :
    baxterPrimitive z ρ σ A qp W C i j r = (q z σ A qp W C i j r : ℂ) -
      ∑ l, (ρ l : ℂ) * ∫ t : ℝ, (q z σ A qp W C i l (t + r) : ℂ) *
        (q z σ A qp W C j l t : ℂ) := by
  unfold baxterPrimitive
  rw [reflected_Q_zero_of_order z σ A qp W C i j horder r hr]
  simp only [Complex.ofReal_zero, add_zero]
  simp_rw [qCrossCorr_eq_ordered]

theorem qCrossCorr_star (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j l : Fin N) (r : ℝ) :
    star (qCrossCorr z σ A qp W C i j l r) = qCrossCorr z σ A qp W C i j l r := by
  unfold qCrossCorr
  simp only [Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp

/-- The actual primitive is real-valued, although its Fourier transform need
not be real without additional evenness/species reciprocity. -/
theorem baxterPrimitive_im_eq_zero (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    (baxterPrimitive z ρ σ A qp W C i j r).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  change star (baxterPrimitive z ρ σ A qp W C i j r) = baxterPrimitive z ρ σ A qp W C i j r
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := by intro x; simp
  unfold baxterPrimitive
  simp only [star_sub, star_add, star_sum, star_mul, hs, qCrossCorr_star]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

end FMSA.ExactMSA.MultiTailMixture
