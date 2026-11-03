import MSAConvergence.WronskianJets
import MSAConvergence.PolynomialMatrixJets

/-! Actual tangent normalization, retaining origin and degree constraints
before the existing polynomial factor completion is applied. -/
noncomputable section
open Polynomial
open scoped BigOperators ContDiff

namespace FMSA.Convergence.NormalizedWronskianJets
open FMSA.Convergence.PolynomialJets FMSA.Convergence.PolynomialMatrixJets
open FMSA.Convergence.WronskianJets FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper.JacobianExterior FMSA.MatrixQ0 MSAMixture

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual intrinsic Wronskian has smooth coefficients in all four blocks. -/
theorem intrinsicWronskian_matrixSmooth (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    MatrixSmooth (fun a : TailMatrix T N × TailMatrix T N =>
      intrinsicWronskianMatrix z rho sigma a.1 a.2) := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact coeffSmooth_neg _ (coeffSmooth_comp (2 * (nonlinearDistinctRates z).card + 4)
        (fun a : TailMatrix T N × TailMatrix T N => nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j)
        (fun a => nonlinearDistinctVPolynomial_degree_le z rho sigma a.1 a.2 i j)
        ((actual_distinct_wronskian_coeffSmooth z rho sigma).2 i j) (-X))
    | inr j => exact (actual_distinct_wronskian_coeffSmooth z rho sigma).1 i j
  | inr i =>
    cases j with
    | inl j => exact coeffSmooth_neg _ ((actual_distinct_wronskian_coeffSmooth z rho sigma).1 j i)
    | inr j => exact (actual_distinct_wronskian_coeffSmooth z rho sigma).2 i j

/-- A single bound covers every intrinsic block, uniformly off-root. -/
theorem intrinsicWronskian_degree (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (a : TailMatrix T N × TailMatrix T N) :
    PolyMatrixDegreeLE (intrinsicWronskianMatrix z rho sigma a.1 a.2)
      (2 * (nonlinearDistinctRates z).card + 5) := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change (-((nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).comp (-X))).natDegree ≤ _
      rw [Polynomial.natDegree_neg]
      have h := (polynomial_comp_neg_X_degree_le _).trans
        (nonlinearDistinctVPolynomial_degree_le z rho sigma a.1 a.2 i j)
      omega
    | inr j => exact nonlinearDistinctUPolynomial_degree_le z rho sigma a.1 a.2 i j
  | inr i =>
    cases j with
    | inl j => simpa only [intrinsicWronskianMatrix, Matrix.fromBlocks_apply₂₁,
        Polynomial.natDegree_neg] using nonlinearDistinctUPolynomial_degree_le z rho sigma a.1 a.2 j i
    | inr j =>
      exact (nonlinearDistinctVPolynomial_degree_le z rho sigma a.1 a.2 i j).trans (by omega)

/-- Coefficient n+10 of the off-root transport gives normalized coefficient n.
This derives actual smoothness without expanding the normalized constructor. -/
theorem normalizedDefect_matrixSmooth (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix rho sigma ≠ 0) :
    MatrixSmooth (fun a : TailMatrix T N × TailMatrix T N =>
      intrinsicNormalizedDefect z rho sigma a.1 a.2) := by
  have hw := intrinsicWronskian_matrixSmooth z rho sigma
  have hr : MatrixSmooth (fun a : TailMatrix T N × TailMatrix T N =>
      intrinsicNormalizationMatrix rho sigma *
        (intrinsicRatePairPolynomial z • intrinsicWronskianMatrix z rho sigma a.1 a.2) *
      (intrinsicNormalizationMatrix rho sigma).transpose) :=
    matrixSmooth_mul _ _
      (matrixSmooth_mul _ _ (fun i j => coeffSmooth_const _)
        (matrixSmooth_smul _ _ hw)) (fun i j => coeffSmooth_const _)
  intro i j n
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
        (intrinsicNormalizedDefect z rho sigma a.1 a.2 i j).coeff n) =
      fun a => ((intrinsicNormalizationMatrix rho sigma *
        (intrinsicRatePairPolynomial z • intrinsicWronskianMatrix z rho sigma a.1 a.2) *
        (intrinsicNormalizationMatrix rho sigma).transpose) i j).coeff (n + 10) := by
    funext a
    have ht := congrArg (fun M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ) =>
      (M i j).coeff (n + 10)) (intrinsicNormalizedDefect_transport z rho sigma a.1 a.2 hz hv)
    simpa only [Matrix.smul_apply, smul_eq_mul, Polynomial.coeff_X_pow_mul] using ht
  rw [he]
  exact hr i j (n + 10)

def intrinsicTangent (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ) :=
  matrixVariation (2 * (nonlinearDistinctRates z).card + 5)
    (fun a => intrinsicWronskianMatrix z rho sigma a.1 a.2) p v

def normalizedTangent (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ) :=
  matrixVariation (4 * (nonlinearDistinctRates z).card + 1)
    (fun a => intrinsicNormalizedDefect z rho sigma a.1 a.2) p v

/-- Both the uniform and the sharper lower-block degrees survive the actual
coefficient derivative. -/
theorem normalizedTangent_degrees (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) :
    PolyMatrixDegreeLE (normalizedTangent z rho sigma p v) (4 * (nonlinearDistinctRates z).card + 1) ∧
    ∀ i j, (normalizedTangent z rho sigma p v (Sum.inr i) (Sum.inr j)).natDegree ≤
      4 * (nonlinearDistinctRates z).card := by
  constructor
  · intro i j
    exact variation_degree _ _ p v
  · intro i j
    exact matrixVariation_degree_le _ _
      (fun a : TailMatrix T N × TailMatrix T N => intrinsicNormalizedDefect z rho sigma a.1 a.2) p v
      (fun a => (intrinsicNormalizedDefect_degree z rho sigma a.1 a.2 hz hv).1)
      (Sum.inr i) (Sum.inr j)
      (fun a => (intrinsicNormalizedDefect_degree z rho sigma a.1 a.2 hz hv).2 i j)

/-- The full off-root X^10 normalization transport commutes with genuine
coefficientwise amplitude differentiation, in the original matrix order. -/
theorem actual_tangent_normalization_transport (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) :
    (X^10 : Polynomial ℝ) • normalizedTangent z rho sigma p v =
      intrinsicNormalizationMatrix rho sigma *
        (intrinsicRatePairPolynomial z • intrinsicTangent z rho sigma p v) *
        (intrinsicNormalizationMatrix rho sigma).transpose := by
  let m := (nonlinearDistinctRates z).card
  let WF := fun a : TailMatrix T N × TailMatrix T N => intrinsicWronskianMatrix z rho sigma a.1 a.2
  let NF := fun a : TailMatrix T N × TailMatrix T N => intrinsicNormalizedDefect z rho sigma a.1 a.2
  let A := intrinsicNormalizationMatrix rho sigma
  let q := intrinsicRatePairPolynomial z
  have hW : MatrixSmooth WF := intrinsicWronskian_matrixSmooth z rho sigma
  have hN : MatrixSmooth NF := normalizedDefect_matrixSmooth z rho sigma hz hv
  have hdW (a : TailMatrix T N × TailMatrix T N) : PolyMatrixDegreeLE (WF a) (2*m+5) :=
    intrinsicWronskian_degree z rho sigma a
  have hdN (a : TailMatrix T N × TailMatrix T N) : PolyMatrixDegreeLE (NF a) (4*m+1) :=
    (intrinsicNormalizedDefect_degree z rho sigma a.1 a.2 hz hv).1
  have hdA : PolyMatrixDegreeLE A 3 := (intrinsicNormalizationMatrix_degree rho sigma).1
  have hdQ : q.natDegree ≤ 2*m := le_of_eq (intrinsicRatePairPolynomial_degree z)
  have hdQW (a : TailMatrix T N × TailMatrix T N) : PolyMatrixDegreeLE (q • WF a) (4*m+5) := by
    have h := polyMatrix_degree_smul hdQ (hdW a)
    intro i j
    have := h i j
    omega
  have hdAQW (a : TailMatrix T N × TailMatrix T N) : PolyMatrixDegreeLE (A * (q • WF a)) (4*m+8) := by
    have h := polyMatrix_degree_mul hdA (hdQW a)
    intro i j
    have := h i j
    omega
  have hdR (a : TailMatrix T N × TailMatrix T N) :
      PolyMatrixDegreeLE (A * (q • WF a) * A.transpose) (4*m+11) := by
    have h := polyMatrix_degree_mul (hdAQW a) (polyMatrix_degree_transpose hdA)
    intro i j
    have := h i j
    omega
  have hdL (a : TailMatrix T N × TailMatrix T N) :
      PolyMatrixDegreeLE ((X^10 : Polynomial ℝ) • NF a) (4*m+11) := by
    have h := polyMatrix_degree_smul (show (X^10 : Polynomial ℝ).natDegree ≤ 10 by simp) (hdN a)
    intro i j
    have := h i j
    omega
  have hQW : MatrixSmooth (fun a => q • WF a) := matrixSmooth_smul q WF hW
  have hAQW : MatrixSmooth (fun a => A * (q • WF a)) :=
    matrixSmooth_mul _ _ (fun i j => coeffSmooth_const _) hQW
  have he : (fun a : TailMatrix T N × TailMatrix T N => (X^10 : Polynomial ℝ) • NF a) =
      fun a => A * (q • WF a) * A.transpose := by
    funext a
    exact intrinsicNormalizedDefect_transport z rho sigma a.1 a.2 hz hv
  have ht := congrArg (fun F => matrixVariation (4*m+11) F p v) he
  rw [matrixVariation_const_smul (4*m+1) (4*m+11) NF (X^10) p v hN hdN hdL,
    matrixVariation_const_right (4*m+8) (4*m+11) (fun a => A * (q • WF a)) A.transpose p v hAQW hdAQW hdR,
    matrixVariation_const_left (4*m+5) (4*m+8) (fun a => q • WF a) A p v hQW hdQW hdAQW,
    matrixVariation_const_smul (2*m+5) (4*m+5) WF q p v hW hdW hdQW] at ht
  exact ht

/-- The actual normalized tangent retains the zero origin coefficient,
Lagrangian projection and skew first coefficient. -/
theorem normalizedTangent_origin_constraints (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) :
    polyMatrixCoeff 0 (normalizedTangent z rho sigma p v) = 0 ∧
    completionU (1 : Matrix (Fin N) (Fin N) ℝ) *
      polyMatrixCoeff 1 (normalizedTangent z rho sigma p v) = 0 ∧
    (polyMatrixCoeff 1 (normalizedTangent z rho sigma p v)).transpose =
      -polyMatrixCoeff 1 (normalizedTangent z rho sigma p v) := by
  let NF := fun a : TailMatrix T N × TailMatrix T N => intrinsicNormalizedDefect z rho sigma a.1 a.2
  have hb (a : TailMatrix T N × TailMatrix T N) :
      PolyMatrixDegreeLE (NF a) (4 * (nonlinearDistinctRates z).card + 1) :=
    (intrinsicNormalizedDefect_degree z rho sigma a.1 a.2 hz hv).1
  have hsm : MatrixSmooth NF := normalizedDefect_matrixSmooth z rho sigma hz hv
  have hs (a : TailMatrix T N × TailMatrix T N) :
      (polyMatrixCoeff 1 (NF a)).transpose = -polyMatrixCoeff 1 (NF a) := by
    have hh := congrArg (polyMatrixCoeff 1) (intrinsicNormalizedDefect_skew z rho sigma a.1 a.2)
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun hh i) j
    simpa only [polyMatrixCoeff, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.neg_apply, Polynomial.coeff_neg] using hij
  exact ⟨matrixVariation_coeff_zero _ 0 NF p v hb
      (fun a => (intrinsicNormalizedDefect_origin_zero z rho sigma a.1 a.2 hz).1),
    matrixVariation_projected_coeff_zero _ 1 NF (completionU (1 : Matrix (Fin N) (Fin N) ℝ)) p v hsm hb
      (fun a => (intrinsicNormalizedDefect_origin_zero z rho sigma a.1 a.2 hz).2),
    matrixVariation_coeff_skew _ 1 NF p v hsm hb hs⟩

/-- Every intrinsic tangent entry evaluates to the actual amplitude derivative. -/
theorem intrinsicTangent_eval_fderiv (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N ⊕ Fin N) (s : ℝ) :
    (intrinsicTangent z rho sigma p v i j).eval s =
      fderiv ℝ (fun a => (intrinsicWronskianMatrix z rho sigma a.1 a.2 i j).eval s) p v := by
  exact variation_eval_fderiv (2 * (nonlinearDistinctRates z).card + 5)
    (fun a : TailMatrix T N × TailMatrix T N => intrinsicWronskianMatrix z rho sigma a.1 a.2 i j) p v
    (fun a => intrinsicWronskian_degree z rho sigma a i j)
    (fun n _ => ((intrinsicWronskian_matrixSmooth z rho sigma i j n).differentiable (by simp) p)) s

/-- The intrinsic coefficient tangent consists precisely of the already
identified actual U/V tangent polynomials, including reflected V. -/
theorem intrinsicTangent_blocks (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) :
    intrinsicTangent z rho sigma p v = Matrix.fromBlocks
      (fun i j => -(tangentV z rho sigma p v i j).comp (-X))
      (tangentU z rho sigma p v)
      (fun i j => -tangentU z rho sigma p v j i)
      (tangentV z rho sigma p v) := by
  have hn (f : (TailMatrix T N × TailMatrix T N) → ℝ) (hf : DifferentiableAt ℝ f p) :
      fderiv ℝ (fun a => -f a) p v = -fderiv ℝ f p v :=
    congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ => L v) hf.hasFDerivAt.neg.fderiv
  apply Matrix.ext
  intro i j
  cases i <;> cases j
  all_goals
    rename_i i j
    apply Polynomial.funext
    intro s
    rw [intrinsicTangent_eval_fderiv]
  · simp only [intrinsicWronskianMatrix, Matrix.fromBlocks_apply₁₁,
      Polynomial.eval_neg, Polynomial.eval_comp, Polynomial.eval_X]
    rw [hn (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval (-s))
      (((actual_distinct_eval_contDiff z rho sigma i j (-s)).2).differentiable (by simp) p),
      (tangent_eval_fderiv z rho sigma p v i j (-s)).2]
  · exact (tangent_eval_fderiv z rho sigma p v i j s).1.symm
  · simp only [intrinsicWronskianMatrix, Matrix.fromBlocks_apply₂₁, Polynomial.eval_neg]
    rw [hn (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 j i).eval s)
      (((actual_distinct_eval_contDiff z rho sigma j i s).1).differentiable (by simp) p),
      (tangent_eval_fderiv z rho sigma p v j i s).1]
  · exact (tangent_eval_fderiv z rho sigma p v i j s).2.symm

/-- The actual full intrinsic tangent contains the fixed reflected pole factor. -/
theorem actual_kernel_intrinsicTangent_factor
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) :
    ∃ W : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ),
      intrinsicTangent z rho sigma p v = nonlinearDistinctPoleFactor z • W := by
  classical
  have hd (i j : Fin N ⊕ Fin N) :
      nonlinearDistinctPoleFactor z ∣ intrinsicTangent z rho sigma p v i j := by
    rw [intrinsicTangent_blocks]
    cases i with
    | inl i =>
      cases j with
      | inl j => exact dvd_neg.mpr (nonlinearDistinctPoleFactor_dvd_reflection z _
          (actual_kernel_tangent_pole_factor z rho sigma K hK hz t p v hroot hk i j).2)
      | inr j => exact (actual_kernel_tangent_pole_factor z rho sigma K hK hz t p v hroot hk i j).1
    | inr i =>
      cases j with
      | inl j => exact dvd_neg.mpr (actual_kernel_tangent_pole_factor z rho sigma K hK hz t p v hroot hk j i).1
      | inr j => exact (actual_kernel_tangent_pole_factor z rho sigma K hK hz t p v hroot hk i j).2
  refine ⟨fun i j => Classical.choose (hd i j), ?_⟩
  apply Matrix.ext
  intro i j
  exact Classical.choose_spec (hd i j)

/-- Exact tangent transport carries the intrinsic reflected factor through
normalization and permits cancellation of the origin power. -/
theorem actual_kernel_normalizedTangent_factor
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) :
    ∃ F : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ),
      normalizedTangent z rho sigma p v =
        (intrinsicRatePairPolynomial z * nonlinearDistinctPoleFactor z) • F := by
  classical
  obtain ⟨W, hW⟩ := actual_kernel_intrinsicTangent_factor z rho sigma K hK hz t p v hroot hk
  have ht := actual_tangent_normalization_transport z rho sigma (fun u => (hz u).ne') hv p v
  rw [hW, smul_smul, Matrix.mul_smul, Matrix.smul_mul] at ht
  have hp0 : (intrinsicRatePairPolynomial z * nonlinearDistinctPoleFactor z).coeff 0 ≠ 0 := by
    rw [Polynomial.mul_coeff_zero]
    exact mul_ne_zero (intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz)
      (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using nonlinearDistinctPoleFactor_eval_zero_ne_zero z hz)
  have hd (i j : Fin N ⊕ Fin N) :
      intrinsicRatePairPolynomial z * nonlinearDistinctPoleFactor z ∣ normalizedTangent z rho sigma p v i j := by
    apply polynomial_cancel_origin_power_dvd _ _ 10 hp0
    refine ⟨(intrinsicNormalizationMatrix rho sigma * W * (intrinsicNormalizationMatrix rho sigma).transpose) i j, ?_⟩
    exact congrFun (congrFun ht i) j
  refine ⟨fun i j => Classical.choose (hd i j), ?_⟩
  apply Matrix.ext
  intro i j
  exact Classical.choose_spec (hd i j)

/-- The actual normalized tangent vanishes by degree/origin/projected-skew
factor completion. No Jacobian invertibility or root curve is assumed. -/
theorem actual_kernel_normalizedTangent_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) :
    normalizedTangent z rho sigma p v = 0 := by
  obtain ⟨F, hF⟩ := actual_kernel_normalizedTangent_factor z rho sigma K hK hz hv t p v hroot hk
  let q := intrinsicRatePairPolynomial z * nonlinearDistinctPoleFactor z
  have hq0 : q.coeff 0 ≠ 0 := by
    rw [Polynomial.mul_coeff_zero]
    exact mul_ne_zero (intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz)
      (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using nonlinearDistinctPoleFactor_eval_zero_ne_zero z hz)
  have hq : intrinsicRatePairPolynomial z ≠ 0 := by
    intro he
    have h := intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz
    simp [he] at h
  have hdeg : q.natDegree = 4 * (nonlinearDistinctRates z).card := by
    rw [Polynomial.natDegree_mul hq (nonlinearDistinctPoleFactor_monic z).ne_zero,
      intrinsicRatePairPolynomial_degree, nonlinearDistinctPoleFactor_degree z hz]
    omega
  have hd := normalizedTangent_degrees z rho sigma (fun u => (hz u).ne') hv p v
  have ho := normalizedTangent_origin_constraints z rho sigma (fun u => (hz u).ne') hv p v
  have hf0 : F = 0 := by
    apply polynomial_matrix_factor_completion (1 : Matrix (Fin N) (Fin N) ℝ) q F hq0
    · intro i j
      rw [← hdeg] at hd
      simpa only [hF, Matrix.smul_apply, smul_eq_mul] using hd.1 i j
    · intro i j
      simpa only [hF, Matrix.smul_apply, smul_eq_mul, hdeg] using hd.2 i j
    · simpa only [hF, polyMatrixCoeff] using ho.1
    · simpa only [hF, polyMatrixCoeff] using ho.2.1
    · simpa only [hF, polyMatrixCoeff] using ho.2.2
  rw [hF, hf0, smul_zero]

/-- Polynomial congruence cancellation recovers the full intrinsic tangent. -/
theorem actual_kernel_intrinsicTangent_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) :
    intrinsicTangent z rho sigma p v = 0 := by
  have hn := actual_kernel_normalizedTangent_zero z rho sigma K hK hz hv t p v hroot hk
  have ht := actual_tangent_normalization_transport z rho sigma (fun u => (hz u).ne') hv p v
  rw [hn, smul_zero] at ht
  have hE := polynomial_matrix_congruence_cancel _ _
    (intrinsicNormalizationMatrix_det_ne_zero rho sigma) ht.symm
  have hq : intrinsicRatePairPolynomial z ≠ 0 := by
    intro he
    have h := intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz
    simp [he] at h
  apply Matrix.ext
  intro i j
  have h := congrFun (congrFun hE i) j
  exact (mul_eq_zero.mp h).resolve_left hq

/-- The complete actual U/V tangent polynomials vanish; the degree-five/four
remainders from the preceding checkpoint are thereby fully eliminated. -/
theorem actual_kernel_tangent_polynomials_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    tangentU z rho sigma p v i j = 0 ∧ tangentV z rho sigma p v i j = 0 := by
  have h := actual_kernel_intrinsicTangent_zero z rho sigma K hK hz hv t p v hroot hk
  rw [intrinsicTangent_blocks] at h
  exact ⟨congrFun (congrFun h (Sum.inl i)) (Sum.inr j),
    congrFun (congrFun h (Sum.inr i)) (Sum.inr j)⟩

/-- Every actual U/V coefficient derivative vanishes in an actual BH kernel
vector. All coefficient derivative existence was discharged off-root. -/
theorem actual_kernel_wronskian_coefficients_fderiv_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) (n : ℕ) :
    fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).coeff n) p v = 0 ∧
    fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).coeff n) p v = 0 := by
  have hz0 := actual_kernel_tangent_polynomials_zero z rho sigma K hK hz hv t p v hroot hk i j
  have hc := tangent_coefficients z rho sigma p v i j n
  constructor
  · rw [← hc.1, hz0.1, Polynomial.coeff_zero]
  · rw [← hc.2, hz0.2, Polynomial.coeff_zero]

/-- Every real evaluation of the actual cleared U/V defects has zero genuine
amplitude derivative along the actual BH kernel, including at the origin. -/
theorem actual_kernel_wronskian_eval_fderiv_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) (s : ℝ) :
    fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval s) p v = 0 ∧
    fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval s) p v = 0 := by
  have hz0 := actual_kernel_tangent_polynomials_zero z rho sigma K hK hz hv t p v hroot hk i j
  have he := tangent_eval_fderiv z rho sigma p v i j s
  constructor
  · rw [← he.1, hz0.1, Polynomial.eval_zero]
  · rw [← he.2, hz0.2, Polynomial.eval_zero]

end FMSA.Convergence.NormalizedWronskianJets

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.intrinsicWronskian_matrixSmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.intrinsicWronskian_matrixSmooth

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.intrinsicWronskian_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.intrinsicWronskian_degree

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.normalizedDefect_matrixSmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.normalizedDefect_matrixSmooth

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.normalizedTangent_degrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.normalizedTangent_degrees

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_tangent_normalization_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_tangent_normalization_transport

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.normalizedTangent_origin_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.normalizedTangent_origin_constraints

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.intrinsicTangent_eval_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.intrinsicTangent_eval_fderiv

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.intrinsicTangent_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.intrinsicTangent_blocks

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_kernel_intrinsicTangent_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_kernel_intrinsicTangent_factor

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_kernel_normalizedTangent_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_kernel_normalizedTangent_factor

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_kernel_normalizedTangent_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_kernel_normalizedTangent_zero

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_kernel_intrinsicTangent_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_kernel_intrinsicTangent_zero

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_kernel_tangent_polynomials_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_kernel_tangent_polynomials_zero

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_kernel_wronskian_coefficients_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_kernel_wronskian_coefficients_fderiv_zero

/-- info: 'FMSA.Convergence.NormalizedWronskianJets.actual_kernel_wronskian_eval_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.NormalizedWronskianJets.actual_kernel_wronskian_eval_fderiv_zero
