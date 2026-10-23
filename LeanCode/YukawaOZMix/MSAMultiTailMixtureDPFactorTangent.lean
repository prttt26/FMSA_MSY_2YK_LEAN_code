import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPQTransform

/-! Matrix form of the actual Q tangent. Right density factors are retained,
so zero-density species require no cancellation or division by density. -/
noncomputable section
open Real Filter Topology MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def complexHSQ (ρ σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => Complex.exp (-s*(edgeLo σ i j : ℂ))*complexHSMoment ρ σ s i j)

def complexHSRightFactor (ρ σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1-complexHSQ ρ σ s*Matrix.diagonal (fun i => (ρ i : ℂ))

def phasedEdgeSlope (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (u : ι) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => Complex.exp (-s*(edgeLo σ i j : ℂ))*(dressedEdgeSlope z ρ σ K u i j : ℂ))

def contactEdgeSlope (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (u : ι) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => Complex.exp (-s*(edgeHi σ i j : ℂ))*(dressedEdgeSlope z ρ σ K u i j : ℂ))

theorem complexHSQ_phased_product (ρ σ : Fin N → ℝ) (s : ℂ) (i m j : Fin N) :
    Complex.exp (-s*(edgeLo σ i m : ℂ))*Complex.exp (-s*(edgeLo σ m j : ℂ)) =
      Complex.exp (-s*(edgeLo σ i j : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [edgeLo]
  push_cast
  ring

theorem complexHSQ_contact_product (ρ σ : Fin N → ℝ) (s : ℂ) (i m j : Fin N) :
    Complex.exp (-(-s)*(edgeLo σ i m : ℂ))*Complex.exp (-s*(edgeHi σ m j : ℂ)) =
      Complex.exp (-s*(edgeHi σ i j : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [edgeLo, edgeHi]
  push_cast
  ring

theorem complexHSRightFactor_mul_phased (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (u : ι) (s : ℂ) (i j : Fin N) :
    (complexHSRightFactor ρ σ s*phasedEdgeSlope z ρ σ K u s) i j =
      Complex.exp (-s*(edgeLo σ i j : ℂ))*
        ((dressedEdgeSlope z ρ σ K u i j : ℂ) -
          ∑ m, (ρ m : ℂ)*complexHSMoment ρ σ s i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)) := by
  rw [complexHSRightFactor, sub_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.mul_apply (M := complexHSQ ρ σ s*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, complexHSQ, phasedEdgeSlope, Matrix.of_apply]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have he := complexHSQ_phased_product ρ σ s i m j
  linear_combination (ρ m : ℂ)*complexHSMoment ρ σ s i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)*he

theorem complexHSRightFactor_mul_contact (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (u : ι) (s : ℂ) (i j : Fin N) :
    (complexHSRightFactor ρ σ (-s)*contactEdgeSlope z ρ σ K u s) i j =
      Complex.exp (-s*(edgeHi σ i j : ℂ))*
        ((dressedEdgeSlope z ρ σ K u i j : ℂ) -
          ∑ m, (ρ m : ℂ)*complexHSMoment ρ σ (-s) i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)) := by
  rw [complexHSRightFactor, sub_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.mul_apply (M := complexHSQ ρ σ (-s)*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, complexHSQ, contactEdgeSlope, Matrix.of_apply]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have he := complexHSQ_contact_product ρ σ s i m j
  linear_combination (ρ m : ℂ)*complexHSMoment ρ σ (-s) i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)*he

def singleFactorQ1 (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (u : ι) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (1/s) • (complexHSRightFactor ρ σ s*phasedEdgeSlope z ρ σ K u s) -
    ((z u : ℂ)/(s*(s+(z u : ℂ)))) •
      (complexHSRightFactor ρ σ (-s)*contactEdgeSlope z ρ σ K u s)

theorem hsFactorQ1_eq_matrix_sum (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (s : ℂ) :
    Matrix.of (hsFactorQ1 z ρ σ K s) = ∑ u, singleFactorQ1 z ρ σ K u s := by
  ext i j
  simp only [Matrix.of_apply, hsFactorQ1, Matrix.sum_apply, singleFactorQ1,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    complexHSRightFactor_mul_phased, complexHSRightFactor_mul_contact]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem phasedEdgeSlope_neg_transpose (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i) (u : ι) (s : ℂ) :
    (phasedEdgeSlope z ρ σ K u (-s)).transpose = phasedEdgeSlope z ρ σ K u s := by
  ext i j
  simp only [Matrix.transpose_apply, phasedEdgeSlope, Matrix.of_apply]
  rw [dressedEdgeSlope_symmetric z ρ σ K hK u j i]
  apply congrArg (fun e => Complex.exp e*(dressedEdgeSlope z ρ σ K u i j : ℂ))
  simp only [edgeLo]
  push_cast
  ring

theorem contactEdgeSlope_transpose (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i) (u : ι) (s : ℂ) :
    (contactEdgeSlope z ρ σ K u s).transpose = contactEdgeSlope z ρ σ K u s := by
  ext i j
  simp only [Matrix.transpose_apply, contactEdgeSlope, Matrix.of_apply]
  rw [dressedEdgeSlope_symmetric z ρ σ K hK u j i]
  apply congrArg (fun e => Complex.exp e*(dressedEdgeSlope z ρ σ K u i j : ℂ))
  simp only [edgeHi]
  push_cast
  ring

/-- Generic product cancellation. The cross term uses the phase-transposed
symmetry of L, while both surviving DP sandwiches have symmetric sources. -/
theorem dp_factor_product_cancel (s z : ℂ) (Fp Fm Lp Lm Mp Mm : Matrix (Fin N) (Fin N) ℂ)
    (hL : Lm.transpose=Lp) :
    ((1/s) • (Fp*Lp)-(z/(s*(s+z))) • (Fm*Mp))*Fm.transpose +
      Fp*((1/(-s)) • (Fm*Lm)-(z/((-s)*(-s+z))) • (Fp*Mm)).transpose =
    (z/(s*(z-s))) • (Fp*Mm.transpose*Fp.transpose) -
      (z/(s*(s+z))) • (Fm*Mp*Fm.transpose) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    hL, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  have hneg : (1/(-s) : ℂ) = -(1/s) := by simp
  have hminus : z/((-s)*(-s+z)) = -(z/(s*(z-s))) := by
    rw [neg_mul, div_neg]
    congr 2
    ring
  rw [hneg, hminus]
  simp only [neg_smul, ← Matrix.mul_assoc]
  module

theorem singleFactorQ1_product_DP (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i) (u : ι) (s : ℂ) :
    singleFactorQ1 z ρ σ K u s*(complexHSRightFactor ρ σ (-s)).transpose +
      complexHSRightFactor ρ σ s*(singleFactorQ1 z ρ σ K u (-s)).transpose =
    ((z u : ℂ)/(s*((z u : ℂ)-s))) •
      (complexHSRightFactor ρ σ s*contactEdgeSlope z ρ σ K u (-s)*(complexHSRightFactor ρ σ s).transpose) -
    ((z u : ℂ)/(s*(s+(z u : ℂ)))) •
      (complexHSRightFactor ρ σ (-s)*contactEdgeSlope z ρ σ K u s*(complexHSRightFactor ρ σ (-s)).transpose) := by
  unfold singleFactorQ1
  rw [neg_neg, dp_factor_product_cancel _ _ _ _ _ _ _ _ (phasedEdgeSlope_neg_transpose z ρ σ K hK u s),
    contactEdgeSlope_transpose z ρ σ K hK u (-s)]

def hsFactorC1 (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (hsFactorQ1 z ρ σ K s)*(complexHSRightFactor ρ σ (-s)).transpose +
    complexHSRightFactor ρ σ s*(Matrix.of (hsFactorQ1 z ρ σ K (-s))).transpose

theorem hsFactorC1_DP_sum (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i) (s : ℂ) :
    hsFactorC1 z ρ σ K s = ∑ u,
      (((z u : ℂ)/(s*((z u : ℂ)-s))) •
        (complexHSRightFactor ρ σ s*contactEdgeSlope z ρ σ K u (-s)*(complexHSRightFactor ρ σ s).transpose) -
      ((z u : ℂ)/(s*(s+(z u : ℂ)))) •
        (complexHSRightFactor ρ σ (-s)*contactEdgeSlope z ρ σ K u s*(complexHSRightFactor ρ σ (-s)).transpose)) := by
  rw [hsFactorC1, hsFactorQ1_eq_matrix_sum, hsFactorQ1_eq_matrix_sum, Matrix.transpose_sum,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  exact singleFactorQ1_product_DP z ρ σ K hK u s

/-- The actual Q-product tangent will be pair symmetric once identified
with this sum; no reciprocity assumption on the HS factor is necessary. -/
theorem hsFactorC1_transpose (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i) (s : ℂ) :
    (hsFactorC1 z ρ σ K s).transpose = hsFactorC1 z ρ σ K s := by
  rw [hsFactorC1_DP_sum z ρ σ K hK s, Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, contactEdgeSlope_transpose z ρ σ K hK]
  simp only [Matrix.mul_assoc]

theorem baxter_tangent_product_entry (Qp Qm Pp Pm : Matrix (Fin N) (Fin N) ℂ)
    (ρ : Fin N → ℝ) (i j : Fin N) :
    (Pp*(1-Qm*Matrix.diagonal (fun m => (ρ m : ℂ))).transpose +
      (1-Qp*Matrix.diagonal (fun m => (ρ m : ℂ)))*Pm.transpose) i j =
      Pp i j+Pm j i-∑ m, (ρ m : ℂ)*(Pp i m*Qm j m+Qp i m*Pm j m) := by
  have he : Pp*(1-Qm*Matrix.diagonal (fun m => (ρ m : ℂ))).transpose +
      (1-Qp*Matrix.diagonal (fun m => (ρ m : ℂ)))*Pm.transpose =
      Pp+Pm.transpose-(Pp*Matrix.diagonal (fun m => (ρ m : ℂ))*Qm.transpose+
        Qp*Matrix.diagonal (fun m => (ρ m : ℂ))*Pm.transpose) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.diagonal_transpose]
    noncomm_ring
  rw [he]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply]
  rw [Matrix.mul_apply (M := Pp*Matrix.diagonal (fun m => (ρ m : ℂ))),
    Matrix.mul_apply (M := Qp*Matrix.diagonal (fun m => (ρ m : ℂ)))]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, mul_add, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]

theorem linearizedSpectralC_eq_hsFactorC1 (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (k : ℝ) (hk : k ≠ 0) :
    Matrix.of (linearizedSpectralC z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k) =
      hsFactorC1 z ρ σ K (Complex.I*k) := by
  have hbase (w : ℝ) (hw : w ≠ 0) (a b : Fin N) :
      fourierQ z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ)) (amplitudeQp z ρ σ 0 (baseSeed z ρ σ))
        (W z ρ 0 (baseSeed z ρ σ)) (C z ρ σ 0 (baseSeed z ρ σ)) w a b =
        complexHSQ ρ σ (Complex.I*w) a b := by
    rw [fourierQ_eq_QhatComplex z hz σ _ _ _ _ (fun i => (hσ i).le) w hw,
      QhatComplex_zero_eq_phase_HS]
    rfl
  ext i j
  rw [hsFactorC1, complexHSRightFactor, complexHSRightFactor, baxter_tangent_product_entry]
  simp only [Matrix.of_apply, linearizedSpectralC]
  simp only [linearizedFourierQ_neg, fourierQ_conj]
  simp only [hbase k hk, hbase (-k) (neg_ne_zero.mpr hk),
    linearizedFourierQ_eq_hs_factor z ρ σ K hz hv hρ hσ k hk,
    linearizedFourierQ_eq_hs_factor z ρ σ K hz hv hρ hσ (-k) (neg_ne_zero.mpr hk),
    Complex.ofReal_neg, mul_neg]

/-- Same-radius species reciprocity of the actual full-space primitive
Fourier tangent, for every nonzero frequency and arbitrary finite species. -/
theorem linearizedSpectralC_symmetric (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j=K u j i) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    linearizedSpectralC z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k i j =
      linearizedSpectralC z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k j i := by
  have he := hsFactorC1_transpose z ρ σ K hK (Complex.I*k)
  rw [← linearizedSpectralC_eq_hsFactorC1 z ρ σ K hz hv hρ hσ k hk] at he
  exact congrFun (congrFun he j) i

end FMSA.ExactMSA.MultiTailMixture
