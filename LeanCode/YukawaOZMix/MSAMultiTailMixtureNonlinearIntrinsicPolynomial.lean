import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearOriginPolynomial
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearIntrinsicHS

/-! Exact polynomial normalization of the actual unscaled BH kernels. -/
noncomputable section
open Real Polynomial MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearLowerQValue_origin_constant
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N) :
    nonlinearLowerQValue z ρ σ Dt G i j - nonlinearOriginWmoment z ρ Dt G 0 i j =
      nonlinearOriginCmoment z ρ σ Dt G 0 i j - σ i*nonlinearB z ρ σ Dt G j := by
  unfold nonlinearLowerQValue nonlinearOriginWmoment nonlinearOriginCmoment
  rw [amplitudeQp_nonlinear_rank_two]
  simp only [pow_zero, div_one, Finset.sum_add_distrib]
  ring

def intrinsicRatePairPolynomial (z : ι → ℝ) :=
  nonlinearDistinctRatePolynomial z * (nonlinearDistinctRatePolynomial z).comp (-X)

def intrinsicHNumerator (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ) :=
  Matrix.fromBlocks
    (fun i j => -nonlinearDistinctLNumerator z ρ σ Dt G i j *
      (nonlinearDistinctRatePolynomial z).comp (-X))
    (fun i j => -(nonlinearDistinctJNumerator z ρ σ Dt G i j).comp (-X) *
      nonlinearDistinctRatePolynomial z)
    (fun i j => nonlinearDistinctJNumerator z ρ σ Dt G i j *
      (nonlinearDistinctRatePolynomial z).comp (-X))
    (fun i j => (nonlinearDistinctLNumerator z ρ σ Dt G i j).comp (-X) *
      nonlinearDistinctRatePolynomial z)

def intrinsicHJet (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :=
  polyOriginH (originIntrinsicH3 z ρ σ Dt G) (originIntrinsicH2 z ρ σ Dt G)
    (originIntrinsicH1 z ρ σ Dt G) (originIntrinsicH0 z ρ σ Dt G)
    (originIntrinsicHp1 z ρ σ Dt G) (originIntrinsicHp2 z ρ σ Dt G)
    (originIntrinsicHp3 z ρ σ Dt G)

def intrinsicDPolynomial (ρ σ : Fin N → ℝ) :=
  polyOriginD (originIntrinsicD1 ρ σ) (originIntrinsicD2 ρ σ) (originIntrinsicD3 ρ σ)

def intrinsicHRemainder (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ) :=
  Matrix.fromBlocks
    (fun i j => -originWRemainderPolynomial z ρ Dt G i j *
      (nonlinearDistinctRatePolynomial z).comp (-X))
    (fun i j => -(originCRemainderPolynomial z ρ σ Dt G i j).comp (-X) *
      nonlinearDistinctRatePolynomial z)
    (fun i j => -originCRemainderPolynomial z ρ σ Dt G i j *
      (nonlinearDistinctRatePolynomial z).comp (-X))
    (fun i j => -(originWRemainderPolynomial z ρ Dt G i j).comp (-X) *
      nonlinearDistinctRatePolynomial z)

theorem intrinsicHJet_dictionary (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :
    intrinsicHJet z ρ σ Dt G = Matrix.fromBlocks
      (fun i j => -originLJet z ρ σ Dt G i j)
      (fun i j => -(originJJet z ρ σ Dt G i j).comp (-X))
      (originJJet z ρ σ Dt G)
      (fun i j => (originLJet z ρ σ Dt G i j).comp (-X)) := by
  have hl (i j : Fin N) : nonlinearLowerQValue z ρ σ Dt G i j =
      nonlinearOriginWmoment z ρ Dt G 0 i j + nonlinearOriginCmoment z ρ σ Dt G 0 i j -
        σ i*nonlinearB z ρ σ Dt G j := by
    linear_combination nonlinearLowerQValue_origin_constant z ρ σ Dt G i j
  apply Matrix.ext
  intro i j
  cases i <;> cases j
  all_goals
    apply Polynomial.funext
    intro s
    simp only [intrinsicHJet, polyOriginH, polyMatrixTerm, Matrix.add_apply,
      originIntrinsicH3, originIntrinsicH2, originIntrinsicH1, originIntrinsicH0,
      originIntrinsicHp1, originIntrinsicHp2, originIntrinsicHp3,
      originKernelMatrix, originLift, Matrix.fromBlocks, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, one_mul, mul_one]
    simp [originJJet, originLJet, originTaylor4, originJetH3, originJetH2, originJetH1,
      originJetH0, originJetHplus1, originJetHplus2, amplitudeQp_nonlinear_rank_two, hl]
    ring

theorem intrinsicHNumerator_origin_polynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) :
    intrinsicHNumerator z ρ σ Dt G =
      intrinsicRatePairPolynomial z • intrinsicHJet z ρ σ Dt G +
      (X^7 : Polynomial ℝ) • intrinsicHRemainder z ρ σ Dt G := by
  rw [intrinsicHJet_dictionary]
  apply Matrix.ext
  intro i j
  cases i <;> cases j
  all_goals
    simp only [intrinsicHNumerator, intrinsicHRemainder, intrinsicRatePairPolynomial,
      Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      nonlinearDistinctJNumerator_origin_polynomial z ρ σ Dt G hz,
      nonlinearDistinctLNumerator_origin_polynomial z ρ σ Dt G hz,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp, Polynomial.X_comp]
    ring

theorem intrinsic_normalized_jet_low_orders
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    (X^3 : Polynomial ℝ) • intrinsicDPolynomial ρ σ +
      (X^3 : Polynomial ℝ) • intrinsicHJet z ρ σ Dt G +
      intrinsicDPolynomial ρ σ * polyMatrixTerm 0 (originDensityMatrix ρ) *
        intrinsicHJet z ρ σ Dt G =
    polyMatrixTerm 5 (originIntrinsicResidue z ρ σ Dt G) +
    polyMatrixTerm 6 (originIntrinsicConstant z ρ σ Dt G) +
    polyMatrixTerm 7 (originIntrinsicHp1 z ρ σ Dt G +
      originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicHp2 z ρ σ Dt G +
      originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicHp3 z ρ σ Dt G) +
    polyMatrixTerm 8 (originIntrinsicHp2 z ρ σ Dt G +
      originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicHp3 z ρ σ Dt G) +
    polyMatrixTerm 9 (originIntrinsicHp3 z ρ σ Dt G) := by
  unfold intrinsicDPolynomial intrinsicHJet
  rw [polynomial_origin_affine_jet_product]
  have hh := originIntrinsic_highest_products_zero z ρ σ Dt G
  rw [hh.1, hh.2.1, hh.2.2, originIntrinsic_third_coefficient_zero z ρ σ Dt G hz hv,
    originIntrinsic_second_coefficient_zero z ρ σ Dt G hz hv,
    ← originIntrinsicResidue_expanded z ρ σ Dt G,
    ← originIntrinsicConstant_expanded z ρ σ Dt G]
  simp only [polyMatrixTerm_zero, zero_add]

def intrinsicNormalizedNumerator (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :=
  (X^3 : Polynomial ℝ) • (intrinsicRatePairPolynomial z • intrinsicDPolynomial ρ σ) +
    (X^3 : Polynomial ℝ) • intrinsicHNumerator z ρ σ Dt G +
    intrinsicDPolynomial ρ σ * polyMatrixTerm 0 (originDensityMatrix ρ) *
      intrinsicHNumerator z ρ σ Dt G

def intrinsicNormalizedReducedNumerator
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :=
  intrinsicRatePairPolynomial z •
    (polyMatrixTerm 0 (originIntrinsicResidue z ρ σ Dt G) +
      polyMatrixTerm 1 (originIntrinsicConstant z ρ σ Dt G) +
      polyMatrixTerm 2 (originIntrinsicHp1 z ρ σ Dt G +
        originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicHp2 z ρ σ Dt G +
        originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicHp3 z ρ σ Dt G) +
      polyMatrixTerm 3 (originIntrinsicHp2 z ρ σ Dt G +
        originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicHp3 z ρ σ Dt G) +
      polyMatrixTerm 4 (originIntrinsicHp3 z ρ σ Dt G)) +
    (X^2 : Polynomial ℝ) • ((X^3 : Polynomial ℝ) • intrinsicHRemainder z ρ σ Dt G +
      intrinsicDPolynomial ρ σ * polyMatrixTerm 0 (originDensityMatrix ρ) *
        intrinsicHRemainder z ρ σ Dt G)

theorem intrinsicNormalizedNumerator_origin_factor
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    intrinsicNormalizedNumerator z ρ σ Dt G =
      (X^5 : Polynomial ℝ) • intrinsicNormalizedReducedNumerator z ρ σ Dt G := by
  have he : intrinsicNormalizedNumerator z ρ σ Dt G =
      intrinsicRatePairPolynomial z •
        ((X^3 : Polynomial ℝ) • intrinsicDPolynomial ρ σ +
          (X^3 : Polynomial ℝ) • intrinsicHJet z ρ σ Dt G +
          intrinsicDPolynomial ρ σ * polyMatrixTerm 0 (originDensityMatrix ρ) *
            intrinsicHJet z ρ σ Dt G) +
      (X^7 : Polynomial ℝ) • ((X^3 : Polynomial ℝ) • intrinsicHRemainder z ρ σ Dt G +
        intrinsicDPolynomial ρ σ * polyMatrixTerm 0 (originDensityMatrix ρ) *
          intrinsicHRemainder z ρ σ Dt G) := by
    unfold intrinsicNormalizedNumerator
    rw [intrinsicHNumerator_origin_polynomial z ρ σ Dt G hz]
    simp only [smul_add, Matrix.mul_add, Matrix.mul_smul, smul_smul]
    module
  rw [he, intrinsic_normalized_jet_low_orders z ρ σ Dt G hz hv]
  unfold intrinsicNormalizedReducedNumerator
  have ht (d : ℕ) (A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
      polyMatrixTerm d A = (X^d : Polynomial ℝ) • A.map Polynomial.C := by
    apply Matrix.ext
    intro i j
    simp [polyMatrixTerm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [ht, smul_add, smul_smul]
  module

theorem intrinsicNormalizedReducedNumerator_origin_coefficients
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    (intrinsicNormalizedReducedNumerator z ρ σ Dt G).map (fun f => f.coeff 0) =
      (intrinsicRatePairPolynomial z).coeff 0 • originIntrinsicResidue z ρ σ Dt G ∧
    (intrinsicNormalizedReducedNumerator z ρ σ Dt G).map (fun f => f.coeff 1) =
      (intrinsicRatePairPolynomial z).coeff 0 • originIntrinsicConstant z ρ σ Dt G +
      (intrinsicRatePairPolynomial z).coeff 1 • originIntrinsicResidue z ρ σ Dt G := by
  constructor <;> apply Matrix.ext <;> intro i j <;>
    simp [intrinsicNormalizedReducedNumerator, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, polyMatrixTerm, Polynomial.mul_coeff_one] <;> ring

end FMSA.ExactMSA.MultiTailMixture
