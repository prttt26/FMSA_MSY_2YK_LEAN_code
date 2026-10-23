import LeanCode.YukawaOZMix.MSAMultiTailMixtureFourier
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.Analysis.Complex.Order

/-! Actual cross-correlation transform and the Gram matrix of actual finite-tail Q.
The spectral coefficient below is defined by Q products. Identification with
an actual radial DCF and physical matrix RDF/core closure are separate tasks. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture

/-- Joint L1 for the actual cross-correlation is derived by a measure-preserving
reflection/shear from the two marginal weighted L1 conditions. -/
theorem complex_corr_joint_integrable (f g : ℝ → ℂ) (s : ℂ)
    (hf : Integrable (fun t => f t * Complex.exp (-s * t)))
    (hg : Integrable (fun t => g t * Complex.exp (s * t))) :
    Integrable (Function.uncurry fun t u => f t * g (t - u) * Complex.exp (-s * u))
      (volume.prod volume) := by
  have hp := hf.mul_prod hg
  have hT : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 - p.2))
      (volume.prod volume) (volume.prod volume) := by
    convert ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))).comp
      (measurePreserving_prod_sub (volume : Measure ℝ) volume) using 1
    funext p
    simp [Prod.map]
  have hi := hT.integrable_comp_of_integrable hp
  convert hi using 1
  funext p
  change f p.1 * g (p.1 - p.2) * Complex.exp (-s * p.2) =
    (f p.1 * Complex.exp (-s * p.1)) *
      (g (p.1 - p.2) * Complex.exp (s * ((p.1 - p.2 : ℝ) : ℂ)))
  have he : Complex.exp (-s * (p.2 : ℂ)) =
      Complex.exp (-s * (p.1 : ℂ)) * Complex.exp (s * ((p.1 - p.2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem complex_corr_transform (f g : ℝ → ℂ) (s : ℂ)
    (hf : Integrable (fun t => f t * Complex.exp (-s * t)))
    (hg : Integrable (fun t => g t * Complex.exp (s * t))) :
    (∫ t, f t * Complex.exp (-s * t)) * (∫ t, g t * Complex.exp (s * t)) =
      ∫ u, (∫ t, f t * g (t - u)) * Complex.exp (-s * u) := by
  have hj1 := hf.mul_prod hg
  have hj2 := complex_corr_joint_integrable f g s hf hg
  simp only [neg_mul] at hj1 hj2 ⊢
  exact FMSA.MixtureBaxter.laplace_product_eq_corr_c f g s hj1 hj2

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- Actual Q cross-correlation, without a compact-support approximation. -/
theorem fourierQ_product_eq_corr (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j l : Fin N) :
    fourierQ z σ A qp W C k i l * fourierQ z σ A qp W C (-k) j l =
      ∫ u : ℝ, (∫ t : ℝ, (q z σ A qp W C i l t : ℂ) *
        (q z σ A qp W C j l (t - u) : ℂ)) * Complex.exp (-(Complex.I * k) * u) := by
  have hf := q_complex_weighted_integrable z hz σ A qp W C hσ (Complex.I * k) (by simp) i l
  have hg := q_complex_weighted_integrable z hz σ A qp W C hσ (-(Complex.I * k)) (by simp) j l
  have hphase : (fun t : ℝ => (q z σ A qp W C j l t : ℂ) *
      Complex.exp (-(-(Complex.I * k)) * t)) =
      (fun t => (q z σ A qp W C j l t : ℂ) * Complex.exp ((Complex.I * k) * t)) := by
    simp
  rw [hphase] at hg
  have hh := complex_corr_transform (fun t => (q z σ A qp W C i l t : ℂ))
    (fun t => (q z σ A qp W C j l t : ℂ)) (Complex.I * k) hf hg
  simpa only [fourierQ, Complex.ofReal_neg, mul_neg, neg_neg] using hh

/-- Density-weighted actual Baxter Fourier factor. -/
def fourierFactor (z : ι → ℝ) (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1 - Matrix.of (fun i j => (Real.sqrt (ρ i) : ℂ) * (Real.sqrt (ρ j) : ℂ) *
    fourierQ z σ A qp W C k i j)

/-- Q-side spectral coefficient. It is not defined as a radial DCF integral. -/
def spectralBaxterC (z : ι → ℝ) (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (k : ℝ) (i j : Fin N) : ℂ :=
  fourierQ z σ A qp W C k i j + star (fourierQ z σ A qp W C k j i) -
    ∑ l, (ρ l : ℂ) * fourierQ z σ A qp W C k i l * star (fourierQ z σ A qp W C k j l)

/-- Hermitian reciprocity of the Q-side spectral expression. -/
theorem spectralBaxterC_star_swap (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    star (spectralBaxterC z ρ σ A qp W C k j i) = spectralBaxterC z ρ σ A qp W C k i j := by
  have hr : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := by intro r; simp [Complex.star_def]
  unfold spectralBaxterC
  simp only [star_sub, star_add, star_sum, star_mul, star_star, hr]
  have hsum : (∑ l, fourierQ z σ A qp W C k i l *
      (star (fourierQ z σ A qp W C k j l) * (ρ l : ℂ))) =
      ∑ l, (ρ l : ℂ) * fourierQ z σ A qp W C k i l * star (fourierQ z σ A qp W C k j l) := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hsum]
  ring

/-- Hermitian is not sufficient for a real radial DCF. Reality of an entry
is equivalent to its equality with the species-swapped entry. This physical
reciprocity has not been inferred from an arbitrary BH root. -/
theorem spectralBaxterC_real_iff_symmetric (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    (spectralBaxterC z ρ σ A qp W C k i j).im = 0 ↔
      spectralBaxterC z ρ σ A qp W C k i j = spectralBaxterC z ρ σ A qp W C k j i := by
  have hs := spectralBaxterC_star_swap z ρ σ A qp W C k j i
  rw [Complex.star_def] at hs
  rw [← Complex.conj_eq_iff_im, hs]
  exact eq_comm

/-- Exact density/transposition convention for the Gram matrix. No radial DCF
identification is implicit in this algebraic identity. -/
theorem fourierFactor_gram_eq (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (k : ℝ) (hρ : ∀ i, 0 ≤ ρ i) :
    fourierFactor z ρ σ A qp W C k * (fourierFactor z ρ σ A qp W C k).conjTranspose =
      1 - Matrix.of (fun i j => (Real.sqrt (ρ i) : ℂ) * (Real.sqrt (ρ j) : ℂ) *
        spectralBaxterC z ρ σ A qp W C k i j) := by
  let B : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
    (Real.sqrt (ρ i) : ℂ) * (Real.sqrt (ρ j) : ℂ) * fourierQ z σ A qp W C k i j)
  have hprod : ∀ i j, (B * B.conjTranspose) i j =
      (Real.sqrt (ρ i) : ℂ) * (Real.sqrt (ρ j) : ℂ) *
        ∑ l, (ρ l : ℂ) * fourierQ z σ A qp W C k i l * star (fourierQ z σ A qp W C k j l) := by
    intro i j
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    have hsqrt : (Real.sqrt (ρ l) : ℂ) * (Real.sqrt (ρ l) : ℂ) = (ρ l : ℂ) := by
      norm_cast
      exact Real.mul_self_sqrt (hρ l)
    simp only [B, Matrix.of_apply, Matrix.conjTranspose_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
    calc
      _ = (Real.sqrt (ρ l) : ℂ) * (Real.sqrt (ρ l) : ℂ) *
          ((Real.sqrt (ρ i) : ℂ) * (Real.sqrt (ρ j) : ℂ) *
            fourierQ z σ A qp W C k i l * star (fourierQ z σ A qp W C k j l)) := by simp only [Complex.star_def]; ring
      _ = _ := by rw [hsqrt]; simp only [Complex.star_def]; ring
  change (1 - B) * (1 - B).conjTranspose = _
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.sub_apply, Matrix.of_apply]
  rw [hprod]
  simp only [B, Matrix.of_apply, Matrix.conjTranspose_apply, star_mul, Complex.star_def, Complex.conj_ofReal,
    spectralBaxterC]
  ring

theorem fourierFactor_gram_posSemidef (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (k : ℝ) :
    Matrix.PosSemidef (fourierFactor z ρ σ A qp W C k *
      (fourierFactor z ρ σ A qp W C k).conjTranspose) :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem fourierFactor_gram_posDef_of_isUnit (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (k : ℝ)
    (h : IsUnit (fourierFactor z ρ σ A qp W C k)) :
    Matrix.PosDef (fourierFactor z ρ σ A qp W C k *
      (fourierFactor z ρ σ A qp W C k).conjTranspose) := by
  have hi := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_conjTranspose (fourierFactor z ρ σ A qp W C k)).mpr h)
  have hp := (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin N) (Fin N) ℂ)).conjTranspose_mul_mul_same hi
  simpa using hp

end FMSA.ExactMSA.MultiTailMixture
