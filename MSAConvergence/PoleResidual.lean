import FMSAPaper.JacobianExterior
import FMSAPaper.ActualRadialIdentification

/-! Off-root finite-pole defects, factored through actual BH errors.
The identities retain the full matrix order and require no curve of roots. -/
noncomputable section
open Real
open scoped BigOperators

namespace FMSA.Convergence.PoleResidual
open FMSA.Paper FMSA.Paper.JacobianExterior
open FMSA.ExactMSA.MultiTailMixture

variable {N : ℕ}

/-- The four pole errors with an arbitrary second-block error `S`.
Only the density matrix is symmetric; none of the unknown matrices is. -/
theorem matrix_pole_errors {R : Type*} [CommRing R]
    (P E D H Q S : Matrix (Fin N) (Fin N) R) (hP : P.transpose = P) :
    let W := H * P * D
    let C := D - E * W
    let J := H * (1 - P * Q) + S
    let L := Q + E * J
    let A := (D * (1 - P * Q.transpose)).transpose - D * (1 - P * Q.transpose)
    let M := 1 - E * H * P
    (W.transpose - C * P * J.transpose - L * P * W.transpose =
      M * A * P * H.transpose - C * P * S.transpose - E * S * P * W.transpose) ∧
    (W - J * P * C.transpose - W * P * L.transpose =
      H * P * A.transpose * M.transpose - S * P * C.transpose - W * P * S.transpose * E.transpose) ∧
    (J * P * W.transpose - W * P * J.transpose =
      H * P * A * P * H.transpose + S * P * W.transpose - W * P * S.transpose) ∧
    (C - C.transpose + L * P * C.transpose - C * P * L.transpose =
      -(M * A * M.transpose) + E * S * P * C.transpose - C * P * S.transpose * E.transpose) := by
  dsimp only
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_transpose, Matrix.transpose_add, hP]
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  constructor <;> noncomm_ring

variable {T : Type*} [Fintype T]

/-- Normalized second BH error at arbitrary amplitudes. -/
theorem normalized_J_residual (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hz : ∀ u, 0 < z u) (u : T) :
    (z u)⁻¹ • nonlinearRationalJ z rho sigma p.1 p.2 (z u) =
      ((2 * π / z u) • Matrix.of (p.2 u)) *
        (1 - Matrix.diagonal rho * nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u) +
      (-(z u)⁻¹) • Matrix.of ((residual z rho sigma K (t, p)).2 u) := by
  have hj (i j : Fin N) : nonlinearRationalJ z rho sigma p.1 p.2 (z u) i j =
      secondRHS z rho sigma p.1 p.2 u i j := by
    simp only [nonlinearRationalJ, Matrix.of_apply, secondRHS]
    rw [add_div, add_div, Finset.sum_div]
    congr 1
    · field_simp [(hz u).ne']
    · apply Finset.sum_congr rfl
      intro v _
      field_simp [(hz u).ne']
  have hl (i j : Fin N) :
      (((2 * π / z u) • Matrix.of (p.2 u)) *
        (1 - Matrix.diagonal rho * nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u)) i j =
      (z u)⁻¹ * secondLHS z rho sigma p.1 p.2 u i j := by
    simp only [Matrix.mul_apply (M := (2 * π / z u) • Matrix.of (p.2 u)),
      Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.one_apply, Matrix.diagonal_mul, nonlinearRootRecenteredTransform,
      Matrix.of_apply, secondLHS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  ext i j
  change (z u)⁻¹ * nonlinearRationalJ z rho sigma p.1 p.2 (z u) i j =
    _ + (-(z u)⁻¹) * (residual z rho sigma K (t, p)).2 u i j
  rw [hj, hl]
  simp only [ExactMSA.MultiTailMixture.residual]
  ring

/-- Symmetric prescribed strengths cancel from the antisymmetric first block,
including away from the root set. -/
theorem first_skew_residual (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N) (u : T) :
    (Matrix.of (p.1 u) * (1 - Matrix.diagonal rho *
        (nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u).transpose)).transpose -
      Matrix.of (p.1 u) * (1 - Matrix.diagonal rho *
        (nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u).transpose) =
    (Matrix.of ((residual z rho sigma K (t, p)).1 u)).transpose -
      Matrix.of ((residual z rho sigma K (t, p)).1 u) := by
  rw [← nonlinearRoot_first_matrix]
  ext i j
  simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply, ExactMSA.MultiTailMixture.residual]
  rw [hK u j i]
  ring

/-- Four normalized finite-pole defects of the actual Baxter data. -/
def poleDefects (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) : Fin 4 → Matrix (Fin N) (Fin N) ℝ :=
  let P := Matrix.diagonal rho
  let W := Matrix.of (W z rho p.1 p.2 u)
  let C := Matrix.of (C z rho sigma p.1 p.2 u)
  let J := (z u)⁻¹ • nonlinearRationalJ z rho sigma p.1 p.2 (z u)
  let L := (z u)⁻¹ • nonlinearRationalL z rho sigma p.1 p.2 (z u)
  ![W.transpose - C * P * J.transpose - L * P * W.transpose,
    W - J * P * C.transpose - W * P * L.transpose,
    J * P * W.transpose - W * P * J.transpose,
    C - C.transpose + L * P * C.transpose - C * P * L.transpose]

/-- A polynomial lift in amplitudes and independent BH error data. Its value at
zero error vanishes identically in amplitudes. -/
def poleErrorLift (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p r : TailMatrix T N × TailMatrix T N) (u : T) : Fin 4 → Matrix (Fin N) (Fin N) ℝ :=
  let P := Matrix.diagonal rho
  let E := Matrix.diagonal (fun i => exp (-z u * sigma i))
  let H := (2 * π / z u) • Matrix.of (p.2 u)
  let W := Matrix.of (W z rho p.1 p.2 u)
  let C := Matrix.of (C z rho sigma p.1 p.2 u)
  let A := (Matrix.of (r.1 u)).transpose - Matrix.of (r.1 u)
  let S := (-(z u)⁻¹) • Matrix.of (r.2 u)
  let M := 1 - E * H * P
  ![M * A * P * H.transpose - C * P * S.transpose - E * S * P * W.transpose,
    H * P * A.transpose * M.transpose - S * P * C.transpose - W * P * S.transpose * E.transpose,
    H * P * A * P * H.transpose + S * P * W.transpose - W * P * S.transpose,
    -(M * A * M.transpose) + E * S * P * C.transpose - C * P * S.transpose * E.transpose]

/-- Full off-root factorization through the actual fixed-coupling residual. -/
theorem actual_pole_residual_factorization (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N) (hz : ∀ u, 0 < z u) (u : T) :
    poleDefects z rho sigma p u =
      poleErrorLift z rho sigma p (residual z rho sigma K (t, p)) u := by
  have h := matrix_pole_errors (Matrix.diagonal rho)
    (Matrix.diagonal (fun i => exp (-z u * sigma i))) (Matrix.of (p.1 u))
    ((2 * π / z u) • Matrix.of (p.2 u)) (nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u)
    ((-(z u)⁻¹) • Matrix.of ((residual z rho sigma K (t, p)).2 u))
    (Matrix.diagonal_transpose rho)
  dsimp only at h
  rw [← normalized_J_residual z rho sigma K t p hz u,
    ← nonlinearRoot_L_matrix z rho sigma p.1 p.2 hz u,
    ← nonlinearRoot_W_matrix z rho p.1 p.2 u,
    ← nonlinearRoot_C_matrix z rho sigma p.1 p.2 u,
    first_skew_residual z rho sigma K hK t p u] at h
  funext k
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

omit [Fintype T] in
/-- No root assumption: setting the independent BH error to zero annihilates
all four pole-error lifts. -/
theorem poleErrorLift_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) :
    poleErrorLift z rho sigma p 0 u = 0 := by
  funext k
  fin_cases k <;> simp [poleErrorLift]

/-- The unnormalized residue matrices used by the finite Wronskian
polynomials; the four components have exactly the frozen foundation's order. -/
def yukawaResidues (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) : Fin 4 → Matrix (Fin N) (Fin N) ℝ :=
  let P := Matrix.diagonal rho
  let W := Matrix.of (W z rho p.1 p.2 u)
  let C := Matrix.of (C z rho sigma p.1 p.2 u)
  let J := nonlinearRationalJ z rho sigma p.1 p.2 (z u)
  let L := nonlinearRationalL z rho sigma p.1 p.2 (z u)
  ![(z u) • W.transpose - C * P * J.transpose - L * P * W.transpose,
    (z u) • W - J * P * C.transpose - W * P * L.transpose,
    J * P * W.transpose - W * P * J.transpose,
    (z u) • (C - C.transpose) + L * P * C.transpose - C * P * L.transpose]

/-- Normalization is a fixed nonzero rate scaling, independent of amplitudes. -/
theorem yukawaResidues_eq_rate_smul (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) (hu : z u ≠ 0) :
    yukawaResidues z rho sigma p u = z u • poleDefects z rho sigma p u := by
  have hc : z u * (z u)⁻¹ = 1 := mul_inv_cancel₀ hu
  funext k
  fin_cases k <;>
    simp [yukawaResidues, poleDefects, smul_sub, smul_add, Matrix.transpose_smul,
      smul_smul, hc]

end FMSA.Convergence.PoleResidual

/-- info: 'FMSA.Convergence.PoleResidual.matrix_pole_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PoleResidual.matrix_pole_errors

/-- info: 'FMSA.Convergence.PoleResidual.normalized_J_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PoleResidual.normalized_J_residual

/-- info: 'FMSA.Convergence.PoleResidual.first_skew_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PoleResidual.first_skew_residual

/-- info: 'FMSA.Convergence.PoleResidual.actual_pole_residual_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PoleResidual.actual_pole_residual_factorization

/-- info: 'FMSA.Convergence.PoleResidual.poleErrorLift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PoleResidual.poleErrorLift_zero

/-- info: 'FMSA.Convergence.PoleResidual.yukawaResidues_eq_rate_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PoleResidual.yukawaResidues_eq_rate_smul
