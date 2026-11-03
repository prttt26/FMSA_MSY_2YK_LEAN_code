import MSAConvergence.PolynomialJets

/-! Actual coefficientwise polynomial-matrix variations commute with fixed
linear operations. No norm is imposed on the polynomial ring. -/
noncomputable section
open Polynomial
open scoped BigOperators ContDiff

namespace FMSA.Convergence.PolynomialMatrixJets
open FMSA.Convergence.PolynomialJets FMSA.ExactMSA.MultiTailMixture

variable {P I : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [Fintype I]

def MatrixSmooth (F : P → Matrix I I (Polynomial ℝ)) : Prop :=
  ∀ i j, CoeffSmooth (fun a => F a i j)

def matrixVariation (D : ℕ) (F : P → Matrix I I (Polynomial ℝ)) (p v : P) :
    Matrix I I (Polynomial ℝ) := fun i j => variation D (fun a => F a i j) p v

/-- Finite matrix multiplication preserves actual coefficient smoothness. -/
theorem matrixSmooth_mul (F G : P → Matrix I I (Polynomial ℝ))
    (hF : MatrixSmooth F) (hG : MatrixSmooth G) : MatrixSmooth (fun a => F a * G a) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact coeffSmooth_sum _ _ (fun k _ => coeffSmooth_mul _ _ (hF i k) (hG k j))

omit [Fintype I] in
/-- Fixed polynomial scalar multiplication preserves coefficient smoothness. -/
theorem matrixSmooth_smul (q : Polynomial ℝ) (F : P → Matrix I I (Polynomial ℝ))
    (hF : MatrixSmooth F) : MatrixSmooth (fun a => q • F a) := by
  intro i j
  exact coeffSmooth_mul _ _ (coeffSmooth_const q) (hF i j)

omit [Fintype I] in
/-- Every coefficient is a genuine derivative under the uniform bound. -/
theorem matrixVariation_coeff (D : ℕ) (F : P → Matrix I I (Polynomial ℝ)) (p v : P)
    (hb : ∀ a i j, (F a i j).natDegree ≤ D) (i j : I) (n : ℕ) :
    (matrixVariation D F p v i j).coeff n = fderiv ℝ (fun a => (F a i j).coeff n) p v :=
  variation_coeff D _ p v (fun a => hb a i j) n

/-- Fixed left matrix multiplication commutes with actual coefficient variation. -/
theorem matrixVariation_const_left (D B : ℕ) (F : P → Matrix I I (Polynomial ℝ))
    (A : Matrix I I (Polynomial ℝ)) (p v : P) (hF : MatrixSmooth F)
    (hb : ∀ a i j, (F a i j).natDegree ≤ D)
    (hc : ∀ a i j, ((A * F a) i j).natDegree ≤ B) :
    matrixVariation B (fun a => A * F a) p v = A * matrixVariation D F p v := by
  apply Matrix.ext
  intro i j
  apply Polynomial.ext
  intro n
  rw [matrixVariation_coeff B _ p v hc]
  simp only [Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul]
  have hout (k : I) (_ : k ∈ Finset.univ) : DifferentiableAt ℝ
      (fun a : P => ∑ ij ∈ Finset.antidiagonal n, (A i k).coeff ij.1 * (F a k j).coeff ij.2) p :=
    DifferentiableAt.fun_sum fun ij _ => ((hF k j ij.2).differentiable (by simp) p).const_mul _
  rw [fderiv_fun_sum hout]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_sum (fun ij _ =>
    ((hF k j ij.2).differentiable (by simp) p).const_mul _)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro ij _
  rw [matrixVariation_coeff D _ p v hb]
  rw [(((hF k j ij.2).differentiable (by simp) p).hasFDerivAt.const_mul ((A i k).coeff ij.1)).fderiv]
  rfl

/-- Fixed right matrix multiplication preserves multiplication order in the jet. -/
theorem matrixVariation_const_right (D B : ℕ) (F : P → Matrix I I (Polynomial ℝ))
    (A : Matrix I I (Polynomial ℝ)) (p v : P) (hF : MatrixSmooth F)
    (hb : ∀ a i j, (F a i j).natDegree ≤ D)
    (hc : ∀ a i j, ((F a * A) i j).natDegree ≤ B) :
    matrixVariation B (fun a => F a * A) p v = matrixVariation D F p v * A := by
  apply Matrix.ext
  intro i j
  apply Polynomial.ext
  intro n
  rw [matrixVariation_coeff B _ p v hc]
  simp only [Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul]
  have hout (k : I) (_ : k ∈ Finset.univ) : DifferentiableAt ℝ
      (fun a : P => ∑ ij ∈ Finset.antidiagonal n, (F a i k).coeff ij.1 * (A k j).coeff ij.2) p :=
    DifferentiableAt.fun_sum fun ij _ => ((hF i k ij.1).differentiable (by simp) p).mul_const _
  rw [fderiv_fun_sum hout]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_sum (fun ij _ => ((hF i k ij.1).differentiable (by simp) p).mul_const _)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro ij _
  rw [matrixVariation_coeff D _ p v hb]
  rw [(((hF i k ij.1).differentiable (by simp) p).hasFDerivAt.mul_const ((A k j).coeff ij.2)).fderiv]
  simp [mul_comm]

/-- A fixed polynomial scalar commutes with the coefficientwise derivative. -/
theorem matrixVariation_const_smul [DecidableEq I] (D B : ℕ) (F : P → Matrix I I (Polynomial ℝ))
    (q : Polynomial ℝ) (p v : P) (hF : MatrixSmooth F)
    (hb : ∀ a i j, (F a i j).natDegree ≤ D)
    (hc : ∀ a i j, ((q • F a) i j).natDegree ≤ B) :
    matrixVariation B (fun a => q • F a) p v = q • matrixVariation D F p v := by
  simpa only [Matrix.smul_mul, Matrix.one_mul] using
    matrixVariation_const_left D B F (q • (1 : Matrix I I (Polynomial ℝ))) p v hF hb
      (fun a i j => by simpa only [Matrix.smul_mul, Matrix.one_mul] using hc a i j)

omit [Fintype I] in
/-- Any sharper uniform degree bound survives coefficient differentiation. -/
theorem matrixVariation_degree_le (D d : ℕ) (F : P → Matrix I I (Polynomial ℝ)) (p v : P)
    (hb : ∀ a i j, (F a i j).natDegree ≤ D)
    (i j : I) (hs : ∀ a, (F a i j).natDegree ≤ d) :
    (matrixVariation D F p v i j).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [matrixVariation_coeff D F p v hb]
  have he : (fun a => (F a i j).coeff n) = fun _ : P => (0 : ℝ) := by
    funext a
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hs a).trans_lt hn)
  rw [he, fderiv_const_apply]
  rfl

omit [Fintype I] in
/-- An identically zero coefficient remains zero after the actual variation. -/
theorem matrixVariation_coeff_zero (D n : ℕ) (F : P → Matrix I I (Polynomial ℝ)) (p v : P)
    (hb : ∀ a i j, (F a i j).natDegree ≤ D)
    (hz : ∀ a, polyMatrixCoeff n (F a) = 0) :
    polyMatrixCoeff n (matrixVariation D F p v) = 0 := by
  apply Matrix.ext
  intro i j
  change (matrixVariation D F p v i j).coeff n = 0
  rw [matrixVariation_coeff D F p v hb]
  have he : (fun a => (F a i j).coeff n) = fun _ : P => (0 : ℝ) := by
    funext a
    exact congrFun (congrFun (hz a) i) j
  rw [he, fderiv_const_apply]
  rfl

/-- A fixed projected coefficient constraint survives actual differentiation. -/
theorem matrixVariation_projected_coeff_zero {J : Type*} (D n : ℕ) (F : P → Matrix I I (Polynomial ℝ))
    (A : Matrix J I ℝ) (p v : P) (hF : MatrixSmooth F)
    (hb : ∀ a i j, (F a i j).natDegree ≤ D)
    (hz : ∀ a, A * polyMatrixCoeff n (F a) = 0) :
    A * polyMatrixCoeff n (matrixVariation D F p v) = 0 := by
  apply Matrix.ext
  intro i j
  have he : (fun a => ∑ k, A i k * (F a k j).coeff n) = fun _ : P => (0 : ℝ) := by
    funext a
    have h := congrFun (congrFun (hz a) i) j
    simpa only [Matrix.mul_apply, polyMatrixCoeff, Matrix.map_apply, Matrix.zero_apply] using h
  have hd : HasFDerivAt (fun a : P => ∑ k, A i k * (F a k j).coeff n)
      (∑ k, A i k • fderiv ℝ (fun a => (F a k j).coeff n) p) p :=
    HasFDerivAt.fun_sum fun k _ =>
      (((hF k j n).differentiable (by simp) p).hasFDerivAt.const_mul (A i k))
  rw [he] at hd
  have hh := congrArg (fun L : P →L[ℝ] ℝ => L v) hd.fderiv
  simp only [fderiv_const_apply, zero_apply, sum_apply, smul_apply, smul_eq_mul] at hh
  change (∑ k, A i k * (matrixVariation D F p v k j).coeff n) = 0
  simp_rw [matrixVariation_coeff D F p v hb]
  exact hh.symm

omit [Fintype I] in
/-- Skew symmetry of a coefficient matrix is preserved by actual variation. -/
theorem matrixVariation_coeff_skew (D n : ℕ) (F : P → Matrix I I (Polynomial ℝ)) (p v : P)
    (hF : MatrixSmooth F) (hb : ∀ a i j, (F a i j).natDegree ≤ D)
    (hs : ∀ a, (polyMatrixCoeff n (F a)).transpose = -polyMatrixCoeff n (F a)) :
    (polyMatrixCoeff n (matrixVariation D F p v)).transpose =
      -polyMatrixCoeff n (matrixVariation D F p v) := by
  apply Matrix.ext
  intro i j
  change (matrixVariation D F p v j i).coeff n = -(matrixVariation D F p v i j).coeff n
  rw [matrixVariation_coeff D F p v hb, matrixVariation_coeff D F p v hb]
  have he : (fun a => (F a j i).coeff n) = fun a => -(F a i j).coeff n := by
    funext a
    exact congrFun (congrFun (hs a) i) j
  rw [he]
  exact congrArg (fun L : P →L[ℝ] ℝ => L v)
    (((hF i j n).differentiable (by simp) p).hasFDerivAt.neg).fderiv

end FMSA.Convergence.PolynomialMatrixJets

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixSmooth_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixSmooth_mul

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixSmooth_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixSmooth_smul

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_coeff

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_const_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_const_left

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_const_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_const_right

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_const_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_const_smul

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_degree_le

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_coeff_zero

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_projected_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_projected_coeff_zero

/-- info: 'FMSA.Convergence.PolynomialMatrixJets.matrixVariation_coeff_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialMatrixJets.matrixVariation_coeff_skew
