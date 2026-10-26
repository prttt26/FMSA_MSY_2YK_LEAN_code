import FMSAPaper.JacobianExterior
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFDCFRegularity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual arbitrary-amplitude DCF variations have bounded radial numerators.
Jacobian kernel directions therefore give compactly supported radial Lp fields.
No L2 membership or derivative/interchange premise is supplied by the caller. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Paper.JacobianL2
open ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture MatrixQ0
open PhysicalExteriorJets JacobianExterior
variable {N : ℕ} {T : Type*} [Fintype T]

abbrev NumeratorIndex (T : Type*) (N : ℕ) :=
  BasisIndex T ⊕ (Fin N × BasisIndex T × BasisIndex T)

def numeratorCoefficient (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : NumeratorIndex T N → ℝ
  | .inl b => -bhCoefficient z rho sigma p i j b
  | .inr (l, b, c) => rho l * (bhCoefficient z rho sigma p i l b * bhCoefficient z rho sigma p j l c)

def numeratorKernel (z : T → ℝ) (sigma : Fin N → ℝ) (i j : Fin N) :
    NumeratorIndex T N → ℝ → ℝ
  | .inl b => basisPrime z sigma b i j
  | .inr (l, b, c) => basisConvolution z sigma b c i j l

@[fun_prop]
theorem numeratorCoefficient_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (b : NumeratorIndex T N) :
    ContDiff ℝ ∞ (fun p => numeratorCoefficient z rho sigma p i j b) := by
  rcases b with b | ⟨l, b, c⟩ <;> dsimp only [numeratorCoefficient] <;> fun_prop

theorem correlation_eq_numerator (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    rootCorrelation z rho sigma p i j r =
      (∑ b : NumeratorIndex T N, numeratorCoefficient z rho sigma p i j b *
        numeratorKernel z sigma i j b r) / (2 * π * r) := by
  rw [rootCorrelation, correlation_eq_basis z hz rho sigma hs]
  congr 1
  symm
  rw [Fintype.sum_sum_type]
  simp only [numeratorCoefficient, numeratorKernel, Fintype.sum_prod_type,
    neg_mul, Finset.sum_neg_distrib, Finset.mul_sum, mul_assoc]

def numeratorVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  ∑ b : NumeratorIndex T N,
    (fderiv ℝ (fun a => numeratorCoefficient z rho sigma a i j b) p) v *
      numeratorKernel z sigma i j b r

theorem correlationVariation_eq_numerator (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    correlationVariation z rho sigma p v i j r = numeratorVariation z rho sigma p v i j r / (2 * π * r) := by
  have hd : HasFDerivAt
      (fun a => ∑ b : NumeratorIndex T N, numeratorCoefficient z rho sigma a i j b *
        numeratorKernel z sigma i j b r)
      (∑ b : NumeratorIndex T N, numeratorKernel z sigma i j b r •
        fderiv ℝ (fun a => numeratorCoefficient z rho sigma a i j b) p) p := by
    apply HasFDerivAt.fun_sum
    intro b _
    exact (((numeratorCoefficient_contDiff z rho sigma i j b).differentiable (by simp)).differentiableAt.hasFDerivAt).mul_const _
  unfold correlationVariation
  have he : (fun a => rootCorrelation z rho sigma a i j r) =
      fun a => (∑ b : NumeratorIndex T N, numeratorCoefficient z rho sigma a i j b *
        numeratorKernel z sigma i j b r) / (2 * π * r) := by
    funext a
    exact correlation_eq_numerator z hz rho sigma hs a i j r
  have hdiv := hd.mul_const ((2 * π * r)⁻¹)
  rw [he]
  simp only [div_eq_mul_inv]
  rw [hdiv.fderiv]
  simp only [smul_apply, sum_apply, smul_eq_mul,
    numeratorVariation, Finset.mul_sum, mul_comm]

theorem numeratorKernel_measurable (z : T → ℝ) (sigma : Fin N → ℝ)
    (i j : Fin N) (b : NumeratorIndex T N) : Measurable (numeratorKernel z sigma i j b) := by
  rcases b with b | ⟨l, b, c⟩
  · exact basisPrime_measurable z sigma b i j
  · exact basisConvolution_measurable z sigma b c i j l

theorem basisPrime_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (b : BasisIndex T) (i j : Fin N) :
    ∃ B : ℝ, ∀ r, |basisPrime z sigma b i j r| ≤ B :=
  baxterQ'_bounded (basisRate z b) (basisRate_pos z hz b) sigma _ _ _ _ i j hs

theorem basisConvolution_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (b c : BasisIndex T) (i j l : Fin N) :
    ∃ B : ℝ, ∀ r, |basisConvolution z sigma b c i j l r| ≤ B := by
  obtain ⟨M, hm⟩ := basisPrime_bounded z hz sigma hs b i l
  refine ⟨M * ∫ t, |basisQ z sigma c j l t|, fun r => ?_⟩
  have hi : Integrable (fun t => M * |basisQ z sigma c j l t|) :=
    (basisQ_integrable z hz sigma hs c j l).abs.const_mul _
  have he := norm_integral_le_of_norm_le hi (ae_of_all _ fun t => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hm (t + r)) (abs_nonneg _))
  simpa only [basisConvolution, Real.norm_eq_abs, integral_const_mul] using he

theorem numeratorKernel_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (i j : Fin N) (b : NumeratorIndex T N) :
    ∃ B : ℝ, ∀ r, |numeratorKernel z sigma i j b r| ≤ B := by
  rcases b with b | ⟨l, b, c⟩
  · exact basisPrime_bounded z hz sigma hs b i j
  · exact basisConvolution_bounded z hz sigma hs b c i j l

theorem numeratorVariation_measurable (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Measurable (numeratorVariation z rho sigma p v i j) := by
  unfold numeratorVariation
  exact Finset.measurable_sum _ fun b _ => (numeratorKernel_measurable z sigma i j b).const_mul _

theorem numeratorVariation_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, |numeratorVariation z rho sigma p v i j r| ≤ B := by
  choose M hM using numeratorKernel_bounded z hz sigma hs i j
  let d := fun b : NumeratorIndex T N => (fderiv ℝ (fun a => numeratorCoefficient z rho sigma a i j b) p) v
  have hm : ∀ b, 0 ≤ M b := fun b => (abs_nonneg _).trans (hM b 0)
  refine ⟨∑ b, |d b| * M b, Finset.sum_nonneg (fun b _ => mul_nonneg (abs_nonneg _) (hm b)), ?_⟩
  intro r
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM b r) (abs_nonneg _)

theorem correlationVariation_measurable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Measurable (correlationVariation z rho sigma p v i j) := by
  have he : correlationVariation z rho sigma p v i j =
      fun r => numeratorVariation z rho sigma p v i j r / (2 * π * r) := by
    funext r
    exact correlationVariation_eq_numerator z hz rho sigma hs p v i j r
  rw [he]
  exact (numeratorVariation_measurable z rho sigma p v i j).div (by fun_prop)

theorem correlationVariation_weighted_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, |r * correlationVariation z rho sigma p v i j r| ≤ B := by
  obtain ⟨B, hB, hb⟩ := numeratorVariation_bounded z hz rho sigma hs p v i j
  refine ⟨B / (2 * π), by positivity, fun r => ?_⟩
  by_cases hr : r = 0
  · simp only [hr, zero_mul, abs_zero]
    positivity
  · have he : r * correlationVariation z rho sigma p v i j r =
        numeratorVariation z rho sigma p v i j r / (2 * π) := by
      rw [correlationVariation_eq_numerator z hz rho sigma hs p v i j r]
      field_simp
    rw [he, abs_div, abs_of_pos (by positivity : 0 < 2 * π)]
    exact div_le_div_of_nonneg_right (hb r) (by positivity)

theorem orderedVariation_measurable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Measurable (orderedVariation z rho sigma K p v i j) := by
  unfold orderedVariation orderedRadialCorrelation
  by_cases h : sigma j ≤ sigma i
  · simp only [if_pos h]
    exact correlationVariation_measurable z hz rho sigma hs p v i j
  · simp only [if_neg h]
    exact correlationVariation_measurable z hz rho sigma hs p v j i

theorem orderedVariation_weighted_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, |r * orderedVariation z rho sigma K p v i j r| ≤ B := by
  unfold orderedVariation orderedRadialCorrelation
  by_cases h : sigma j ≤ sigma i
  · simp only [if_pos h]
    exact correlationVariation_weighted_bounded z hz rho sigma hs p v i j
  · simp only [if_neg h]
    exact correlationVariation_weighted_bounded z hz rho sigma hs p v j i

/-- Zero extension of the actual positive radial moment variation. -/
def positiveMoment (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun r => r * orderedVariation z rho sigma K p v i j r)

theorem positiveMoment_measurable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Measurable (positiveMoment z rho sigma K p v i j) :=
  (measurable_id.mul (orderedVariation_measurable z hz rho sigma hs K p v i j)).indicator measurableSet_Ioi

theorem kernel_positiveMoment_support (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    Function.support (positiveMoment z rho sigma K p v i j) ⊆ Icc (0 : ℝ) (edgeHi sigma i j) := by
  intro r hr
  apply kernel_positive_variation_support z hz rho sigma hs K t p v hv i j
  change (if 0 < r then orderedVariation z rho sigma K p v i j r else 0) ≠ 0
  change positiveMoment z rho sigma K p v i j r ≠ 0 at hr
  by_cases h : 0 < r
  · simp only [if_pos h]
    intro he
    exact hr (by simp [positiveMoment, h, he])
  · exact (hr (by simp [positiveMoment, h])).elim

theorem kernel_positiveMoment_hasCompactSupport (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    HasCompactSupport (positiveMoment z rho sigma K p v i j) := by
  change IsCompact (closure (Function.support (positiveMoment z rho sigma K p v i j)))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (kernel_positiveMoment_support z hz rho sigma hs K t p v hv i j) isClosed_Icc)

/-- Every positive radial kernel variation belongs to every Lp, including L2. -/
theorem kernel_positiveMoment_memLp (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) (q : ENNReal) :
    MemLp (positiveMoment z rho sigma K p v i j) q volume := by
  obtain ⟨B, hB, hb⟩ := orderedVariation_weighted_bounded z hz rho sigma hs K p v i j
  apply (kernel_positiveMoment_hasCompactSupport z hz rho sigma hs K t p v hv i j).memLp_of_bound
    (positiveMoment_measurable z hz rho sigma hs K p v i j).aestronglyMeasurable B
  exact ae_of_all _ fun r => by
    unfold positiveMoment
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hr, Real.norm_eq_abs]
      exact hb r
    · rw [indicator_of_notMem hr, norm_zero]
      exact hB

/-- Actual second radial square moment, with no supplied integrability premise. -/
theorem kernel_radial_square_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    IntegrableOn (fun r => r ^ 2 * (orderedVariation z rho sigma K p v i j r) ^ 2) (Ioi (0 : ℝ)) := by
  have hi := (kernel_positiveMoment_memLp z hz rho sigma hs K t p v hv i j 2).integrable_sq.integrableOn
    (s := Ioi (0 : ℝ))
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [positiveMoment, indicator_of_mem hr]
  ring

/-- The actual second radial moment is absolutely integrable as well, so the
continuous zero-frequency radial symbol of the variation is meaningful. -/
theorem kernel_radial_moment_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    IntegrableOn (fun r => r ^ 2 * orderedVariation z rho sigma K p v i j r) (Ioi (0 : ℝ)) := by
  let R := edgeHi sigma i j
  have hR : 0 ≤ R := by unfold R edgeHi; linarith [hs i, hs j]
  have hi := memLp_one_iff_integrable.mp (kernel_positiveMoment_memLp z hz rho sigma hs K t p v hv i j 1)
  have hb : ∀ᵐ r ∂volume, ‖(Icc (0 : ℝ) R).indicator id r‖ ≤ R := ae_of_all _ fun r => by
    by_cases hr : r ∈ Icc (0 : ℝ) R
    · rw [indicator_of_mem hr, id_eq, Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact hr.2
    · rw [indicator_of_notMem hr, norm_zero]
      exact hR
  have hp := hi.bdd_mul (measurable_id.indicator measurableSet_Icc).aestronglyMeasurable hb
  apply hp.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  dsimp only
  by_cases h : r ≤ R
  · rw [indicator_of_mem (show r ∈ Icc (0 : ℝ) R from ⟨hr.le, h⟩)]
    rw [positiveMoment, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
    simp only [id_eq]
    ring
  · rw [indicator_of_notMem (show r ∉ Icc (0 : ℝ) R from fun hh => h hh.2)]
    simp only [zero_mul, kernel_ordered_exterior_zero z hz rho sigma hs K t p v hv i j r (lt_of_not_ge h), mul_zero]

end FMSA.Paper.JacobianL2

/-- info: 'FMSA.Paper.JacobianL2.numeratorCoefficient_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.numeratorCoefficient_contDiff

/-- info: 'FMSA.Paper.JacobianL2.correlation_eq_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.correlation_eq_numerator

/-- info: 'FMSA.Paper.JacobianL2.correlationVariation_eq_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.correlationVariation_eq_numerator

/-- info: 'FMSA.Paper.JacobianL2.numeratorKernel_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.numeratorKernel_measurable

/-- info: 'FMSA.Paper.JacobianL2.basisPrime_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.basisPrime_bounded

/-- info: 'FMSA.Paper.JacobianL2.basisConvolution_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.basisConvolution_bounded

/-- info: 'FMSA.Paper.JacobianL2.numeratorKernel_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.numeratorKernel_bounded

/-- info: 'FMSA.Paper.JacobianL2.numeratorVariation_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.numeratorVariation_measurable

/-- info: 'FMSA.Paper.JacobianL2.numeratorVariation_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.numeratorVariation_bounded

/-- info: 'FMSA.Paper.JacobianL2.correlationVariation_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.correlationVariation_measurable

/-- info: 'FMSA.Paper.JacobianL2.correlationVariation_weighted_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.correlationVariation_weighted_bounded

/-- info: 'FMSA.Paper.JacobianL2.orderedVariation_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.orderedVariation_measurable

/-- info: 'FMSA.Paper.JacobianL2.orderedVariation_weighted_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.orderedVariation_weighted_bounded

/-- info: 'FMSA.Paper.JacobianL2.positiveMoment_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.positiveMoment_measurable

/-- info: 'FMSA.Paper.JacobianL2.kernel_positiveMoment_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.kernel_positiveMoment_support

/-- info: 'FMSA.Paper.JacobianL2.kernel_positiveMoment_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.kernel_positiveMoment_hasCompactSupport

/-- info: 'FMSA.Paper.JacobianL2.kernel_positiveMoment_memLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.kernel_positiveMoment_memLp

/-- info: 'FMSA.Paper.JacobianL2.kernel_radial_square_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.kernel_radial_square_integrable

/-- info: 'FMSA.Paper.JacobianL2.kernel_radial_moment_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianL2.kernel_radial_moment_integrable
