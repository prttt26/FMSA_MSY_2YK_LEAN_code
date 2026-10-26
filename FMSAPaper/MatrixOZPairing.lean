import FMSAPaper.RadialZeroMode
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The positive matrix pairing in the linearized OZ argument.
This proves the noncommutative algebra and positivity steps. Spatial/Fourier
Parseval and the actual residual-to-OZ tangent bridge are separate. -/
noncomputable section
open MeasureTheory Set Real Filter Topology Matrix
open scoped BigOperators ComplexOrder Kronecker

namespace FMSA.Paper.MatrixOZPairing

variable {N : ℕ}

/-- Correct matrix order in the tangent OZ solution, with no commutation premise. -/
theorem linearized_OZ_solution (C H dC dH : Matrix (Fin N) (Fin N) ℂ)
    (hu : IsUnit (1 - C)) (hOZ : (1 + H) * (1 - C) = 1)
    (hd : dH * (1 - C) - (1 + H) * dC = 0) :
    dH = (1 - C)⁻¹ * dC * (1 - C)⁻¹ := by
  have hud : IsUnit (1 - C).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hS : 1 + H = (1 - C)⁻¹ := by
    calc
      _ = ((1 + H) * (1 - C)) * (1 - C)⁻¹ :=
        (Matrix.mul_nonsing_inv_cancel_right _ _ hud).symm
      _ = _ := by rw [hOZ, one_mul]
  calc
    _ = (dH * (1 - C)) * (1 - C)⁻¹ :=
      (Matrix.mul_nonsing_inv_cancel_right _ _ hud).symm
    _ = ((1 + H) * dC) * (1 - C)⁻¹ := by rw [sub_eq_zero.mp hd]
    _ = _ := by rw [hS]

/-- The real trace pairing used after linearizing OZ. -/
def energy (S D : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (D.conjTranspose * S * D * S).trace.re

/-- Vectorization converts the matrix pairing into the positive Kronecker form.
The transpose on the first factor is essential over complex matrices. -/
theorem energy_eq_kronecker (S D : Matrix (Fin N) (Fin N) ℂ) :
    energy S D = (star D.vec ⬝ᵥ ((S.transpose ⊗ₖ S) *ᵥ D.vec)).re := by
  rw [Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose, Matrix.star_vec_dotProduct_vec]
  simp only [energy, Matrix.mul_assoc]

theorem energy_of_hermitian (S D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsHermitian) :
    energy S D = (D * S * D * S).trace.re := by rw [energy, hD.eq]

theorem energy_nonneg (S D : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.PosSemidef) : 0 ≤ energy S D := by
  rw [energy_eq_kronecker S D]
  exact (hS.transpose.kronecker hS).re_dotProduct_nonneg _

theorem energy_pos (S D : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.PosDef) (hD0 : D ≠ 0) : 0 < energy S D := by
  rw [energy_eq_kronecker S D]
  apply (hS.transpose.kronecker hS).re_dotProduct_pos
  intro h
  exact hD0 (Matrix.vec_inj.mp h)

theorem energy_zero_iff (S D : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.PosDef) : energy S D = 0 ↔ D = 0 := by
  constructor
  · intro he
    by_contra hD0
    exact (ne_of_gt (energy_pos S D hS hD0)) he
  · intro he
    simp [energy, he]

/-- No uniform lower eigenvalue is needed for the a.e. cancellation step;
pointwise strict positivity and actual integrability suffice. -/
theorem ae_zero_of_integral_energy_zero {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (S D : X → Matrix (Fin N) (Fin N) ℂ)
    (hS : ∀ᵐ x ∂mu, (S x).PosDef)
    (hi : Integrable (fun x => energy (S x) (D x)) mu)
    (he : ∫ x, energy (S x) (D x) ∂mu = 0) : D =ᵐ[mu] 0 := by
  have hn : 0 ≤ᵐ[mu] fun x => energy (S x) (D x) := by
    filter_upwards [hS] with x hs
    exact energy_nonneg _ _ hs.posSemidef
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp he
  filter_upwards [hz, hS] with x hx hs
  exact (energy_zero_iff _ _ hs).mp hx

/-- Continuity upgrades the spectral a.e. conclusion to every real wave number. -/
theorem zero_of_integral_energy_zero (S D : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hS : ∀ x, (S x).PosDef)
    (hc : Continuous D) (hi : Integrable (fun x => energy (S x) (D x)))
    (he : ∫ x, energy (S x) (D x) = 0) : D = 0 := by
  exact (Continuous.ae_eq_iff_eq volume hc continuous_const).mp
    (ae_zero_of_integral_energy_zero volume S D (ae_of_all _ hS) hi he)

open ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture MatrixQ0
variable {T : Type*} [Fintype T]

/-- The actual physical radial denominator, using the continuous zero mode. -/
def radialDenominator (z : T → ℝ) (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1 - Matrix.of (fun i j => (sqrt (rho i) : ℂ) * (sqrt (rho j) : ℂ) *
    (RadialZeroMode.radialSymbol (orderedRadialCorrelation z rho sigma K Dt G i j) k : ℂ))

/-- The actual structure matrix, where the determinant condition is supplied
by a canonical factor. Its positivity is proved below, not postulated. -/
def structureMatrix (z : T → ℝ) (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (k : ℝ) : Matrix (Fin N) (Fin N) ℂ := (radialDenominator z rho sigma K Dt G k)⁻¹

theorem actual_radial_denominator_posDef (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (hr : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i) (k : ℝ)
    (hF : IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) k)) :
    (radialDenominator z rho sigma K Dt G k).PosDef := by
  rw [radialDenominator, ← RadialZeroMode.root_factor_gram_radial z rho sigma K Dt G hz hr hs hv hroot hK k]
  exact Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.mpr hF)

theorem actual_structure_matrix_posDef (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (hr : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i) (k : ℝ)
    (hF : IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) k)) :
    (structureMatrix z rho sigma K Dt G k).PosDef :=
  (actual_radial_denominator_posDef z hz rho sigma K Dt G hr hs hv hroot hK k hF).inv

end FMSA.Paper.MatrixOZPairing

/-- info: 'FMSA.Paper.MatrixOZPairing.linearized_OZ_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.linearized_OZ_solution

/-- info: 'FMSA.Paper.MatrixOZPairing.energy_eq_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.energy_eq_kronecker

/-- info: 'FMSA.Paper.MatrixOZPairing.energy_of_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.energy_of_hermitian

/-- info: 'FMSA.Paper.MatrixOZPairing.energy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.energy_nonneg

/-- info: 'FMSA.Paper.MatrixOZPairing.energy_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.energy_pos

/-- info: 'FMSA.Paper.MatrixOZPairing.energy_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.energy_zero_iff

/-- info: 'FMSA.Paper.MatrixOZPairing.ae_zero_of_integral_energy_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.ae_zero_of_integral_energy_zero

/-- info: 'FMSA.Paper.MatrixOZPairing.zero_of_integral_energy_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.zero_of_integral_energy_zero

/-- info: 'FMSA.Paper.MatrixOZPairing.actual_radial_denominator_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.actual_radial_denominator_posDef

/-- info: 'FMSA.Paper.MatrixOZPairing.actual_structure_matrix_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZPairing.actual_structure_matrix_posDef
