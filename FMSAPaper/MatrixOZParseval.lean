import FMSAPaper.MatrixOZPairing
import Mathlib.Analysis.Fourier.LpSpace

/-! Matrix Plancherel and positivity for the linearized OZ pairing.
This is an L2 theorem on any finite-dimensional real inner-product space,
including physical three-space and the one-dimensional odd radial lift.
Actual BH tangent L2 membership and spectral OZ identification are separate. -/
noncomputable section
open MeasureTheory Filter Topology Matrix FourierTransform
open scoped BigOperators ComplexInnerProductSpace ComplexOrder

namespace FMSA.Paper.MatrixOZParseval
open MatrixOZPairing
variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

abbrev MatrixL2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (N : ℕ) :=
  Fin N → Fin N → Lp ℂ 2 (volume : Measure V)

def spatialPair (U W : MatrixL2 V N) : ℝ :=
  (∑ i, ∑ j, inner ℂ (U i j) (W i j)).re

def fourierMatrix (U : MatrixL2 V N) (x : V) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => ((𝓕 (U i j) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x)

theorem trace_pair_eq_sum (D E : Matrix (Fin N) (Fin N) ℂ) :
    (D.conjTranspose * E).trace = ∑ i, ∑ j, star (D i j) * E i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem fourier_trace_pair_integrable (U W : MatrixL2 V N) :
    Integrable (fun x => ((fourierMatrix U x).conjTranspose * fourierMatrix W x).trace) := by
  simp_rw [trace_pair_eq_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  simpa only [fourierMatrix, Matrix.of_apply, RCLike.inner_apply', Complex.star_def] using
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (𝓕 (U i j)) (𝓕 (W i j)))

/-- Entrywise L2 Plancherel assembled as a full noncommutative matrix trace. -/
theorem integral_fourier_trace_pair (U W : MatrixL2 V N) :
    (∫ x, ((fourierMatrix U x).conjTranspose * fourierMatrix W x).trace) =
      ∑ i, ∑ j, inner ℂ (U i j) (W i j) := by
  have hi (i j : Fin N) : Integrable (fun x : V =>
      star (((𝓕 (U i j) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x) * ((𝓕 (W i j) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x) := by
    simpa only [RCLike.inner_apply', Complex.star_def] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (𝓕 (U i j)) (𝓕 (W i j)))
  simp_rw [trace_pair_eq_sum, fourierMatrix, Matrix.of_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Lp.inner_fourier_eq (U i j) (W i j), MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem integral_fourier_trace_pair_re (U W : MatrixL2 V N) :
    (∫ x, (((fourierMatrix U x).conjTranspose * fourierMatrix W x).trace).re) =
      spatialPair U W := by
  calc
    _ = (∫ x, ((fourierMatrix U x).conjTranspose * fourierMatrix W x).trace).re :=
      integral_re (fourier_trace_pair_integrable U W)
    _ = _ := by rw [integral_fourier_trace_pair]; rfl

/-- Orthogonality in physical space supplies the zero spatial pairing. -/
theorem spatialPair_zero_of_disjoint (U W : MatrixL2 V N)
    (h : ∀ i j, (fun x => star (U i j x) * W i j x) =ᵐ[volume] 0) : spatialPair U W = 0 := by
  unfold spatialPair
  have hz : ∀ i j, inner ℂ (U i j) (W i j) = 0 := by
    intro i j
    rw [MeasureTheory.L2.inner_def]
    have he : (fun x => inner ℂ (U i j x) (W i j x)) =ᵐ[volume] 0 := by
      simpa only [RCLike.inner_apply', Complex.star_def] using h i j
    rw [integral_congr_ae he]
    simp
  simp only [hz, Finset.sum_const_zero, Complex.zero_re]

/-- Matrix Parseval plus pointwise positive S eliminates every L2 null mode.
Neither S and delta-C nor their products are assumed to commute. -/
theorem positive_OZ_pairing_injective (S : V → Matrix (Fin N) (Fin N) ℂ)
    (U W : MatrixL2 V N) (hS : ∀ᵐ x ∂volume, (S x).PosDef)
    (hOZ : ∀ᵐ x ∂volume, fourierMatrix W x = S x * fourierMatrix U x * S x)
    (hp : spatialPair U W = 0) : ∀ i j, U i j = 0 := by
  have he : (fun x => energy (S x) (fourierMatrix U x)) =ᵐ[volume]
      fun x => (((fourierMatrix U x).conjTranspose * fourierMatrix W x).trace).re := by
    filter_upwards [hOZ] with x hx
    rw [hx]
    simp only [energy, Matrix.mul_assoc]
  have hi := (fourier_trace_pair_integrable U W).re.congr he.symm
  have hz : (∫ x, energy (S x) (fourierMatrix U x)) = 0 := by
    rw [integral_congr_ae he, integral_fourier_trace_pair_re, hp]
  have hzero := ae_zero_of_integral_energy_zero volume S (fourierMatrix U) hS hi hz
  intro i j
  have hf : 𝓕 (U i j) = 0 := by
    apply Lp.ext
    filter_upwards [hzero, Lp.coeFn_zero ℂ 2 (volume : Measure V)] with x hx hz
    have hh := congrFun (congrFun hx i) j
    rw [hz]
    exact hh
  apply norm_eq_zero.mp
  rw [← Lp.norm_fourier_eq (U i j), hf, norm_zero]

open ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture MatrixQ0
variable {T : Type*} [Fintype T]

/-- Actual physical structure-matrix specialization, including zero frequency.
The supplied L2 fields must still satisfy the actual tangent spectral OZ equation;
this theorem does not infer that equation from membership in a BH Jacobian kernel. -/
theorem actual_radial_OZ_pairing_injective (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (hr : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (hF : ∀ k : ℝ, IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) k))
    (U W : MatrixL2 ℝ N)
    (hOZ : ∀ᵐ k ∂volume, fourierMatrix W k = structureMatrix z rho sigma K Dt G k *
      fourierMatrix U k * structureMatrix z rho sigma K Dt G k)
    (hp : spatialPair U W = 0) : ∀ i j, U i j = 0 := by
  apply positive_OZ_pairing_injective (structureMatrix z rho sigma K Dt G) U W _ hOZ hp
  exact ae_of_all _ fun k => actual_structure_matrix_posDef z hz rho sigma K Dt G
    hr hs hv hroot hK k (hF k)

end FMSA.Paper.MatrixOZParseval

/-- info: 'FMSA.Paper.MatrixOZParseval.trace_pair_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZParseval.trace_pair_eq_sum

/-- info: 'FMSA.Paper.MatrixOZParseval.fourier_trace_pair_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZParseval.fourier_trace_pair_integrable

/-- info: 'FMSA.Paper.MatrixOZParseval.integral_fourier_trace_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZParseval.integral_fourier_trace_pair

/-- info: 'FMSA.Paper.MatrixOZParseval.integral_fourier_trace_pair_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZParseval.integral_fourier_trace_pair_re

/-- info: 'FMSA.Paper.MatrixOZParseval.spatialPair_zero_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZParseval.spatialPair_zero_of_disjoint

/-- info: 'FMSA.Paper.MatrixOZParseval.positive_OZ_pairing_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZParseval.positive_OZ_pairing_injective

/-- info: 'FMSA.Paper.MatrixOZParseval.actual_radial_OZ_pairing_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MatrixOZParseval.actual_radial_OZ_pairing_injective
