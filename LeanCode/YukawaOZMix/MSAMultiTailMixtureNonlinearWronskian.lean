import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearWronskianFinite
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearAbel

/-! The finite coefficient conditions imply the actual Q/source Wronskian,
with no supplied radial or Fourier OZ identity. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def nonlinearActualFourierQ (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (k : ℝ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fourierQ z σ
      (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) k)

def nonlinearActualFourierC (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (k : ℝ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of (spectralBaxterC z ρ σ
      (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) k)

theorem nonlinearActualFourierQ_eq_phaseQ (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (k : ℝ) (hk : k ≠ 0) :
    nonlinearActualFourierQ z ρ σ Dt G k=nonlinearPhaseQ σ
      (nonlinearComplexJ z ρ σ Dt G (Complex.I*k))
      (nonlinearComplexL z ρ σ Dt G (Complex.I*k)) (Complex.I*k) := by
  let s : ℂ := Complex.I*k
  have hs : s ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  ext i j
  rw [nonlinearPhaseQ_entry]
  have hq := nonlinearRecenteredQ_complex_laplace_rational z ρ σ Dt G hz hσ s hs (by simp [s]) i j
  have hrec : FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) s=
      (nonlinearComplexL z ρ σ Dt G s i j-
        Complex.exp (-s*(σ i : ℂ))*nonlinearComplexJ z ρ σ Dt G s i j)/s :=
    (eq_div_iff hs).mpr (by simpa only [mul_comm] using hq)
  have he0 : Complex.exp (-s*(edgeLo σ i j : ℂ))*Complex.exp (s*(edgeLo σ i j : ℂ))=1 := by
    rw [← Complex.exp_add]; simp
  have he1 : Complex.exp (-s*(edgeLo σ i j : ℂ))=
      Complex.exp (s*(σ i : ℂ)/2)*Complex.exp (-s*(σ j : ℂ)/2) := by
    rw [← Complex.exp_add]; congr 1; unfold edgeLo; push_cast; ring
  have he2 : Complex.exp (-s*(edgeLo σ i j : ℂ))*Complex.exp (-s*(σ i : ℂ))=
      Complex.exp (-s*(σ i : ℂ)/2)*Complex.exp (-s*(σ j : ℂ)/2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; unfold edgeLo; push_cast; ring
  calc
    _ = Complex.exp (-s*(edgeLo σ i j : ℂ))*
        FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) s := by
      rw [nonlinearRecenteredQ_actual_fourier, ← mul_assoc, he0, one_mul]; rfl
    _ = _ := by
      rw [hrec, ← mul_div_assoc, mul_sub, ← mul_assoc, he2, he1]
      dsimp only [s]
      ring_nf

theorem nonlinearActualFourierC_eq_Q_product (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (k : ℝ) :
    nonlinearActualFourierC z ρ σ Dt G k=
      nonlinearActualFourierQ z ρ σ Dt G k+(nonlinearActualFourierQ z ρ σ Dt G (-k)).transpose-
      nonlinearActualFourierQ z ρ σ Dt G k*Matrix.diagonal (fun i => (ρ i : ℂ))*
        (nonlinearActualFourierQ z ρ σ Dt G (-k)).transpose := by
  ext i j
  simp only [nonlinearActualFourierC, Matrix.of_apply, spectralBaxterC, fourierQ_conj,
    Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
    Matrix.mul_apply (M := nonlinearActualFourierQ z ρ σ Dt G k*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, nonlinearActualFourierQ, Matrix.of_apply, Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro m _; ring

theorem nonlinearActualFourierC_neg_transpose (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (k : ℝ) :
    nonlinearActualFourierC z ρ σ Dt G (-k)=(nonlinearActualFourierC z ρ σ Dt G k).transpose := by
  simp only [nonlinearActualFourierC_eq_Q_product, neg_neg, Matrix.transpose_sub,
    Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc, add_comm]

theorem nonlinear_actual_source_wronskian_of_finite_certificate
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hc : NonlinearFiniteWronskianCertificate z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    (1-nonlinearActualFourierQ z ρ σ Dt G k*Matrix.diagonal (fun i => (ρ i : ℂ)))*
        (rdfPhase σ (-(Complex.I*k))*(nonlinearComplexJ z ρ σ Dt G (-(Complex.I*k))).transpose*
          rdfPhase σ (-(Complex.I*k)))-
      (1-nonlinearActualFourierQ z ρ σ Dt G (-k)*Matrix.diagonal (fun i => (ρ i : ℂ)))*
        (rdfPhase σ (Complex.I*k)*(nonlinearComplexJ z ρ σ Dt G (Complex.I*k)).transpose*
          rdfPhase σ (Complex.I*k))=
      (Complex.I*k) • nonlinearActualFourierC z ρ σ Dt G k := by
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have hres := nonlinear_finite_wronskian_residuals_zero z ρ σ Dt G hz hc (Complex.I*k) hs (by simp)
  have he := nonlinear_phase_wronskian_residual σ (nonlinearComplexJ z ρ σ Dt G (Complex.I*k))
    (nonlinearComplexL z ρ σ Dt G (Complex.I*k)) (nonlinearComplexJ z ρ σ Dt G (-(Complex.I*k)))
    (nonlinearComplexL z ρ σ Dt G (-(Complex.I*k))) (fun i => (ρ i : ℂ)) (Complex.I*k) hs
  rw [hres.1, hres.2, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    sub_eq_zero] at he
  rw [nonlinearActualFourierQ_eq_phaseQ z ρ σ Dt G hz hσ k hk,
    nonlinearActualFourierQ_eq_phaseQ z ρ σ Dt G hz hσ (-k) (neg_ne_zero.mpr hk),
    nonlinearActualFourierC_eq_Q_product,
    nonlinearActualFourierQ_eq_phaseQ z ρ σ Dt G hz hσ k hk,
    nonlinearActualFourierQ_eq_phaseQ z ρ σ Dt G hz hσ (-k) (neg_ne_zero.mpr hk)]
  simpa only [Complex.ofReal_neg, mul_neg, neg_neg] using he

theorem nonlinear_finite_wronskian_actual_spectral_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hc : NonlinearFiniteWronskianCertificate z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    nonlinearActualFourierC z ρ σ Dt G k=(nonlinearActualFourierC z ρ σ Dt G k).transpose := by
  have hp := nonlinear_actual_source_wronskian_of_finite_certificate z ρ σ Dt G hz hσ hc k hk
  have hm := nonlinear_actual_source_wronskian_of_finite_certificate z ρ σ Dt G hz hσ hc (-k) (neg_ne_zero.mpr hk)
  simp only [Complex.ofReal_neg, mul_neg, neg_neg] at hm
  have he : (Complex.I*k) • nonlinearActualFourierC z ρ σ Dt G k=
      (Complex.I*k) • nonlinearActualFourierC z ρ σ Dt G (-k) := by
    rw [← hp]
    have hn := congrArg Neg.neg hm
    simpa only [neg_sub, neg_smul, neg_neg] using hn
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  rw [← nonlinearActualFourierC_neg_transpose]
  ext i j
  have hij := congrFun (congrFun he i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ hs hij

end FMSA.ExactMSA.MultiTailMixture
