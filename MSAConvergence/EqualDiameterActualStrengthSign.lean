import MSAConvergence.EqualDiameterCrossSign
import MSAConvergence.BHResidualPolynomials

set_option linter.style.header false

/-! The exact binary cross-sign criterion on the input strength type
`MultiTailMixture.TailMatrix`. Equal diameters enter when identifying
the density/concentration basis with the hard-sphere channel basis;
the algebraic input criterion itself does not depend on diameters. -/
noncomputable section
namespace FMSA.Convergence.EqualDiameterActualStrengthSign

open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.EqualDiameterCrossSign

variable {T : Type*}

/-- Bare density-weighted cross entry of an actual binary MSA tail. -/
def actualCross (ρ : Fin 2 → ℝ) (K : TailMatrix T 2) (u : T) : ℝ :=
  crossGeneral (Real.sqrt (ρ 0)) (Real.sqrt (ρ 1))
    (fun i j => K u i j)

/-- Exact cross entry in the actual MSA input strengths and densities. -/
theorem actual_cross_factorization
    (ρ : Fin 2 → ℝ) (K : TailMatrix T 2) (u : T)
    (hρ₀ : 0 ≤ ρ 0) (hρ₁ : 0 ≤ ρ 1)
    (hK : K u 1 0 = K u 0 1) :
    actualCross ρ K u = Real.sqrt (ρ 0) * Real.sqrt (ρ 1) *
      (-(ρ 0) * K u 0 0 + (ρ 0 - ρ 1) * K u 0 1 + ρ 1 * K u 1 1) := by
  simpa only [actualCross, Real.sq_sqrt hρ₀, Real.sq_sqrt hρ₁] using
    cross_general_factorization (Real.sqrt (ρ 0)) (Real.sqrt (ρ 1))
      (fun i j => K u i j) hK

/-- At positive densities, the actual bare cross entry has exactly
the sign of the linear density-strength bracket. -/
theorem actual_cross_neg_iff
    (ρ : Fin 2 → ℝ) (K : TailMatrix T 2) (u : T)
    (hρ₀ : 0 < ρ 0) (hρ₁ : 0 < ρ 1)
    (hK : K u 1 0 = K u 0 1) :
    actualCross ρ K u < 0 ↔
      -(ρ 0) * K u 0 0 + (ρ 0 - ρ 1) * K u 0 1 + ρ 1 * K u 1 1 < 0 := by
  simpa only [actualCross, Real.sq_sqrt hρ₀.le, Real.sq_sqrt hρ₁.le] using
    cross_general_neg_iff (Real.sqrt (ρ 0)) (Real.sqrt (ρ 1))
      (fun i j => K u i j) (Real.sqrt_pos.2 hρ₀) (Real.sqrt_pos.2 hρ₁) hK

/-- For two actual MSA tails, the opposite-sign class is precisely
the negative product of their affine density-strength brackets. -/
theorem actual_two_tails_opposite_iff
    (ρ : Fin 2 → ℝ) (K : TailMatrix T 2) (u v : T)
    (hρ₀ : 0 < ρ 0) (hρ₁ : 0 < ρ 1)
    (hKu : K u 1 0 = K u 0 1) (hKv : K v 1 0 = K v 0 1) :
    actualCross ρ K u * actualCross ρ K v < 0 ↔
      ((ρ 0) * (K u 0 1 - K u 0 0) +
        (ρ 1) * (K u 1 1 - K u 0 1)) *
      ((ρ 0) * (K v 0 1 - K v 0 0) +
        (ρ 1) * (K v 1 1 - K v 0 1)) < 0 := by
  simpa only [actualCross, Real.sq_sqrt hρ₀.le, Real.sq_sqrt hρ₁.le] using
    two_general_tails_opposite_iff
      (Real.sqrt (ρ 0)) (Real.sqrt (ρ 1))
      (fun i j => K u i j) (fun i j => K v i j)
      (Real.sqrt_pos.2 hρ₀) (Real.sqrt_pos.2 hρ₁) hKu hKv

/-- At an actual MSA root, the cross entry of the input strength is
exactly the cross entry extracted from the first Blum-Høye equation.
This is an algebraic identity and makes no claim about Taylor radii. -/
theorem actual_cross_eq_bh_first_forcing
    [Fintype T] (z : T → ℝ) (ρ σ : Fin 2 → ℝ)
    (K Dt G : TailMatrix T 2) (u : T)
    (hz : z u ≠ 0) (hroot : IsRoot z ρ σ K Dt G) :
    actualCross ρ K u =
      crossGeneral (Real.sqrt (ρ 0)) (Real.sqrt (ρ 1))
        (fun i j => z u * firstLHS z ρ σ Dt G u i j / (2 * Real.pi)) := by
  have hmatrix : (fun i j => K u i j) =
      (fun i j => z u * firstLHS z ρ σ Dt G u i j / (2 * Real.pi)) := by
    funext i j
    rw [hroot.1 u i j]
    field_simp [hz, Real.pi_ne_zero]
  exact congrArg (crossGeneral (Real.sqrt (ρ 0)) (Real.sqrt (ρ 1))) hmatrix

end FMSA.Convergence.EqualDiameterActualStrengthSign

/-- info: 'FMSA.Convergence.EqualDiameterActualStrengthSign.actual_cross_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterActualStrengthSign.actual_cross_factorization
/-- info: 'FMSA.Convergence.EqualDiameterActualStrengthSign.actual_cross_neg_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterActualStrengthSign.actual_cross_neg_iff
/-- info: 'FMSA.Convergence.EqualDiameterActualStrengthSign.actual_two_tails_opposite_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterActualStrengthSign.actual_two_tails_opposite_iff
/-- info: 'FMSA.Convergence.EqualDiameterActualStrengthSign.actual_cross_eq_bh_first_forcing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterActualStrengthSign.actual_cross_eq_bh_first_forcing
