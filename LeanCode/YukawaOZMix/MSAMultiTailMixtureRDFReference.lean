import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFPhase
import LeanCode.YukawaOZMix.MSAMultiTailMixtureAEReciprocity

/-! The actual radial HS reference and the actual first-order radial DCF,
with their unweighted left/right density factor dictionary. Strictly positive
reference species densities are required by the existing HS certificate. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfReferenceC (z : ι → ℝ) (ρ σ : Fin N → ℝ) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier
    (orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j) k : ℂ))

def rdfFirstOrderC (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier
    (orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j) k : ℂ))

def rdfFirstOrderH (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier (rdfFirstOrderCausal z ρ σ K i j) k : ℂ))

def rdfReferenceT (z : ι → ℝ) (ρ σ : Fin N → ℝ) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1-rdfReferenceC z ρ σ k*Matrix.diagonal (fun i => (ρ i : ℂ))

theorem rdfReferenceC_neg (z : ι → ℝ) (ρ σ : Fin N → ℝ) (k : ℝ) :
    rdfReferenceC z ρ σ (-k) = rdfReferenceC z ρ σ k := by
  ext i j
  simp only [rdfReferenceC, Matrix.of_apply, FMSA.HardSphere.radial_fourier_neg]

theorem rdfReferenceC_symmetric (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (k : ℝ) (hk : k ≠ 0) :
    (rdfReferenceC z ρ σ k).transpose = rdfReferenceC z ρ σ k := by
  ext i j
  have he := spectralBaxterC_star_swap z ρ σ
    (amplitudeA z ρ σ 0 (baseSeed z ρ σ)) (amplitudeQp z ρ σ 0 (baseSeed z ρ σ))
    (W z ρ 0 (baseSeed z ρ σ)) (C z ρ σ 0 (baseSeed z ρ σ)) k i j
  rw [spectralBaxterC_zero_eq_ordered_radial z ρ σ hz hv hρ hσ k hk j i,
    spectralBaxterC_zero_eq_ordered_radial z ρ σ hz hv hρ hσ k hk i j] at he
  simpa only [rdfReferenceC, Matrix.transpose_apply, Matrix.of_apply, Complex.star_def,
    Complex.conj_ofReal] using he

theorem rdfReferenceT_factorization (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (k : ℝ) (hk : k ≠ 0) :
    rdfReferenceT z ρ σ k = complexHSRightFactor ρ σ (Complex.I*k)*
      (complexHSLeftFactor ρ σ (-(Complex.I*k))).transpose := by
  have hbase (w : ℝ) (hw : w ≠ 0) (a b : Fin N) :
      fourierQ z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ)) (amplitudeQp z ρ σ 0 (baseSeed z ρ σ))
        (W z ρ 0 (baseSeed z ρ σ)) (C z ρ σ 0 (baseSeed z ρ σ)) w a b =
        complexHSQ ρ σ (Complex.I*w) a b := by
    rw [fourierQ_eq_QhatComplex z hz σ _ _ _ _ (fun i => (hσ i).le) w hw,
      QhatComplex_zero_eq_phase_HS]
    rfl
  have hc : rdfReferenceC z ρ σ k = complexHSQ ρ σ (Complex.I*k)+
      (complexHSQ ρ σ (-(Complex.I*k))).transpose-
        complexHSQ ρ σ (Complex.I*k)*Matrix.diagonal (fun i => (ρ i : ℂ))*
          (complexHSQ ρ σ (-(Complex.I*k))).transpose := by
    ext i j
    rw [rdfReferenceC, Matrix.of_apply,
      ← spectralBaxterC_zero_eq_ordered_radial z ρ σ hz hv hρ hσ k hk i j]
    simp only [spectralBaxterC, fourierQ_conj]
    simp only [hbase k hk,
      hbase (-k) (neg_ne_zero.mpr hk), Complex.ofReal_neg, mul_neg,
      Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply]
    rw [Matrix.mul_apply (M := complexHSQ ρ σ (Complex.I*k)*Matrix.diagonal (fun i => (ρ i : ℂ)))]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  unfold rdfReferenceT complexHSRightFactor complexHSLeftFactor
  rw [hc]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.diagonal_transpose]
  noncomm_ring

theorem rdfReferenceT_phase (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (k : ℝ) (hk : k ≠ 0) :
    rdfReferenceT z ρ σ k*rdfPhase σ (Complex.I*k) =
      complexHSRightFactor ρ σ (-(Complex.I*k))*rdfPhase σ (Complex.I*k)*
        (rdfRecenteredFactor ρ σ (Complex.I*k)).transpose := by
  have hf := rdfReferenceT_factorization z hz ρ σ hv hρ hσ (-k) (neg_ne_zero.mpr hk)
  simp only [rdfReferenceT, rdfReferenceC_neg, Complex.ofReal_neg, mul_neg, neg_neg] at hf
  have he := congrArg Matrix.transpose (rdfHSLeftFactor_phase z hz ρ σ
    (fun i => (hσ i).le) k hk)
  simp only [Matrix.transpose_mul, rdfPhase, Matrix.diagonal_transpose] at he
  change (complexHSLeftFactor ρ σ (Complex.I*k)).transpose*rdfPhase σ (Complex.I*k) =
    rdfPhase σ (Complex.I*k)*(rdfRecenteredFactor ρ σ (Complex.I*k)).transpose at he
  rw [rdfReferenceT, hf, Matrix.mul_assoc, he, ← Matrix.mul_assoc]

theorem rdfFirstOrderC_eq_W_difference (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (k : ℝ) (hk : k ≠ 0) :
    rdfFirstOrderC z ρ σ K k = (1/(Complex.I*k)) •
      (Matrix.of (dpWFourier z ρ σ K (-k))-Matrix.of (dpWFourier z ρ σ K k)) := by
  ext i j
  have he := linearizedPrimitiveReal_fourier_eq_DP_W_difference z ρ σ K hz hv hρ hσ hK k hk i j
  rw [linearizedPrimitiveReal_fourier z hz ρ σ (fun i => (hσ i).le),
    linearizedSpectralPrimitive_eq_spectralC z hz ρ σ (fun i => (hσ i).le),
    linearizedSpectralC_eq_all_pairs_ordered_radial z ρ σ K hz hv hρ hσ hK i j k hk] at he
  simpa only [rdfFirstOrderC, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul, div_eq_mul_inv, mul_one, mul_comm] using he

theorem rdfFirstOrderH_eq_phase_difference (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (k : ℝ) (hk : k ≠ 0) :
    rdfFirstOrderH z ρ σ K k = (1/(Complex.I*k)) •
      (rdfPhase σ (-(Complex.I*k))*rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) (-(Complex.I*k))*
          rdfPhase σ (-(Complex.I*k))-
        rdfPhase σ (Complex.I*k)*rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) (Complex.I*k)*
          rdfPhase σ (Complex.I*k)) := by
  ext i j
  simp only [rdfFirstOrderH, rdfPhase, Matrix.of_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, smul_eq_mul]
  rw [rdfFirstOrderCausal_radial_fourier z ρ σ hσ K hU i j k hk]
  have hp := rdfPhase_contact_product σ (-(Complex.I*k)) i j
  have hm := rdfPhase_contact_product σ (Complex.I*k) i j
  simp only [neg_neg] at hp
  simp only [div_eq_mul_inv, mul_one]
  rw [← hp, ← hm]
  ring

end FMSA.ExactMSA.MultiTailMixture
