import FMSAPaper.JacobianL2
import FMSAPaper.FourierL1L2
import FMSAPaper.MatrixOZParseval
import LeanCode.Analysis.RadialOZReconstruction

/-! Actual odd radial DCF tangent fields in L2, with their exact representatives.
The density weighting is explicit; no unknown L2 field stands for delta-c. -/
noncomputable section
open MeasureTheory Set Real Filter Topology FourierTransform
open scoped BigOperators ComplexOrder

namespace FMSA.Paper.RadialVariationL2
open ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture MatrixQ0
open JacobianExterior JacobianL2 MatrixOZParseval
variable {N : ℕ} {T : Type*} [Fintype T]

def oddVariation (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ → ℂ :=
  HardSphere.oddRadialMoment (orderedVariation z rho sigma K p v i j)

theorem oddVariation_measurable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Measurable (oddVariation z rho sigma K p v i j) :=
  Complex.measurable_ofReal.comp (measurable_id.mul
    ((orderedVariation_measurable z hz rho sigma hs K p v i j).comp measurable_abs))

theorem oddVariation_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, ‖oddVariation z rho sigma K p v i j r‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := orderedVariation_weighted_bounded z hz rho sigma hs K p v i j
  refine ⟨B, hB, fun r => ?_⟩
  simpa only [oddVariation, HardSphere.oddRadialMoment, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_abs] using hb |r|

theorem kernel_oddVariation_support (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    Function.support (oddVariation z rho sigma K p v i j) ⊆
      Icc (-edgeHi sigma i j) (edgeHi sigma i j) := by
  intro r hr
  have he : |r| ≤ edgeHi sigma i j := by
    by_contra h
    have hzv := kernel_ordered_exterior_zero z hz rho sigma hs K t p v hv i j |r| (lt_of_not_ge h)
    change oddVariation z rho sigma K p v i j r ≠ 0 at hr
    exact hr (by simp only [oddVariation, HardSphere.oddRadialMoment, hzv, mul_zero, Complex.ofReal_zero])
  exact abs_le.mp he

theorem kernel_oddVariation_hasCompactSupport (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    HasCompactSupport (oddVariation z rho sigma K p v i j) := by
  change IsCompact (closure (Function.support (oddVariation z rho sigma K p v i j)))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (kernel_oddVariation_support z hz rho sigma hs K t p v hv i j) isClosed_Icc)

theorem kernel_oddVariation_memLp (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) (q : ENNReal) :
    MemLp (oddVariation z rho sigma K p v i j) q volume := by
  obtain ⟨B, _, hb⟩ := oddVariation_bounded z hz rho sigma hs K p v i j
  exact (kernel_oddVariation_hasCompactSupport z hz rho sigma hs K t p v hv i j).memLp_of_bound
    (oddVariation_measurable z hz rho sigma hs K p v i j).aestronglyMeasurable B (ae_of_all _ hb)

theorem kernel_oddVariation_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    Integrable (oddVariation z rho sigma K p v i j) :=
  memLp_one_iff_integrable.mp (kernel_oddVariation_memLp z hz rho sigma hs K t p v hv i j 1)

/-- The L2 element is built from the actual odd radial derivative. -/
def oddVariationLp (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) : Lp ℂ 2 (volume : Measure ℝ) :=
  (kernel_oddVariation_memLp z hz rho sigma hs K t p v hv i j 2).toLp
    (oddVariation z rho sigma K p v i j)

theorem oddVariationLp_coe (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    (oddVariationLp z hz rho sigma hs K t p v hv i j : ℝ → ℂ) =ᵐ[volume]
      oddVariation z rho sigma K p v i j :=
  MemLp.coeFn_toLp _

/-- Exact density weight used in the physical matrix OZ equation. -/
def densityWeight (rho : Fin N → ℝ) (i j : Fin N) : ℝ := sqrt (rho i) * sqrt (rho j)

def weightedOddVariation (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℂ :=
  (densityWeight rho i j : ℂ) * oddVariation z rho sigma K p v i j r

def weightedOddVariationLp (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) : MatrixL2 ℝ N := fun i j =>
  ((kernel_oddVariation_memLp z hz rho sigma hs K t p v hv i j 2).const_mul
    (densityWeight rho i j : ℂ)).toLp (weightedOddVariation z rho sigma K p v i j)

theorem weightedOddVariationLp_coe (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    (weightedOddVariationLp z hz rho sigma hs K t p v hv i j : ℝ → ℂ) =ᵐ[volume]
      weightedOddVariation z rho sigma K p v i j :=
  MemLp.coeFn_toLp _

/-- On active species pairs, a zero physical L2 field forces the actual DCF
variation to vanish almost everywhere on the positive radial axis. -/
theorem actual_variation_ae_zero_of_weightedLp_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N)
    (hi : 0 < rho i) (hj : 0 < rho j)
    (hzero : weightedOddVariationLp z hz rho sigma hs K t p v hv i j = 0) :
    orderedVariation z rho sigma K p v i j =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hc := weightedOddVariationLp_coe z hz rho sigma hs K t p v hv i j
  rw [hzero] at hc
  have he : weightedOddVariation z rho sigma K p v i j =ᵐ[volume] 0 :=
    hc.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioi] with r hr hs0
  change weightedOddVariation z rho sigma K p v i j r = 0 at hr
  change 0 < r at hs0
  simp only [weightedOddVariation, oddVariation, HardSphere.oddRadialMoment, abs_of_pos hs0] at hr
  have hw : densityWeight rho i j ≠ 0 := mul_ne_zero
    (sqrt_pos.mpr hi).ne' (sqrt_pos.mpr hj).ne'
  have heq : densityWeight rho i j * (r * orderedVariation z rho sigma K p v i j r) = 0 := by
    exact_mod_cast hr
  exact (mul_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hw)).resolve_left hs0.ne'

/-- Mathlib frequency w corresponds to physical wave number k=2*pi*w. -/
theorem oddVariation_integral_fourier (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) (w : ℝ) :
    𝓕 (oddVariation z rho sigma K p v i j) w =
      -(Complex.I * (w : ℂ)) * (RadialZeroMode.radialSymbol
        (orderedVariation z rho sigma K p v i j) (2 * π * w) : ℂ) := by
  have hodd : ∀ r : ℝ, oddVariation z rho sigma K p v i j (-r) =
      -oddVariation z rho sigma K p v i j r := by
    intro r
    simp only [oddVariation, HardSphere.oddRadialMoment, abs_neg, neg_mul, Complex.ofReal_neg]
  rw [fourier_of_odd _ hodd (kernel_oddVariation_integrable z hz rho sigma hs K t p v hv i j) w]
  have he : (∫ r in Ioi (0 : ℝ), (sin (2 * π * r * w) : ℂ) * oddVariation z rho sigma K p v i j r) =
      ((∫ r in Ioi (0 : ℝ), r * orderedVariation z rho sigma K p v i j r * sin ((2 * π * w) * r) : ℝ) : ℂ) := by
    unfold oddVariation HardSphere.oddRadialMoment
    rw [HardSphere.oddExt_fourier_integral_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    rw [show 2 * π * r * w = (2 * π * w) * r by ring]
  rw [he]
  by_cases hw : w = 0
  · simp only [hw, mul_zero, sin_zero, Complex.ofReal_zero, neg_zero, zero_mul, integral_zero]
  · rw [RadialZeroMode.radialSymbol_eq_radial_fourier _ _
      (mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) hw)]
    unfold HardSphere.radial_fourier
    generalize hA : (∫ r in Ioi (0 : ℝ), r * orderedVariation z rho sigma K p v i j r * sin ((2 * π * w) * r)) = A
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hw, Complex.ofReal_ne_zero.mpr pi_ne_zero]
    ring

/-- Actual L2 Fourier representatives have the physical radial integral formula a.e. -/
theorem oddVariationLp_fourier (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    ((𝓕 (oddVariationLp z hz rho sigma hs K t p v hv i j) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun w => -(Complex.I * (w : ℂ)) * (RadialZeroMode.radialSymbol
        (orderedVariation z rho sigma K p v i j) (2 * π * w) : ℂ) := by
  have h := FourierL1L2.L2_fourier_ae_integral (oddVariation z rho sigma K p v i j)
    (kernel_oddVariation_integrable z hz rho sigma hs K t p v hv i j)
    (kernel_oddVariation_memLp z hz rho sigma hs K t p v hv i j 2)
  exact h.trans (ae_of_all _ fun w => oddVariation_integral_fourier z hz rho sigma hs K t p v hv i j w)

theorem weightedOddVariationLp_fourier (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    ((𝓕 (weightedOddVariationLp z hz rho sigma hs K t p v hv i j) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun w => (densityWeight rho i j : ℂ) *
        (-(Complex.I * (w : ℂ)) * (RadialZeroMode.radialSymbol
          (orderedVariation z rho sigma K p v i j) (2 * π * w) : ℂ)) := by
  have h := FourierL1L2.L2_fourier_ae_integral (weightedOddVariation z rho sigma K p v i j)
    ((kernel_oddVariation_integrable z hz rho sigma hs K t p v hv i j).const_mul _)
    ((kernel_oddVariation_memLp z hz rho sigma hs K t p v hv i j 2).const_mul _)
  apply h.trans
  exact ae_of_all _ fun w => by
    have hm : 𝓕 (weightedOddVariation z rho sigma K p v i j) w =
        (densityWeight rho i j : ℂ) * 𝓕 (oddVariation z rho sigma K p v i j) w := by
      rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun r => by simp only [weightedOddVariation, smul_eq_mul]; ring
    rw [hm, oddVariation_integral_fourier z hz rho sigma hs K t p v hv i j w]

/-- The actual density-weighted radial DCF variation, in the physical k convention. -/
def radialVariationMatrix (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (densityWeight rho i j : ℂ) *
    (RadialZeroMode.radialSymbol (orderedVariation z rho sigma K p v i j) k : ℂ))

theorem actual_fourier_matrix (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) :
    fourierMatrix (weightedOddVariationLp z hz rho sigma hs K t p v hv) =ᵐ[volume]
      fun w => -(Complex.I * (w : ℂ)) • radialVariationMatrix z rho sigma K p v (2 * π * w) := by
  have he := eventually_all.mpr (fun i : Fin N => eventually_all.mpr (fun j : Fin N =>
    weightedOddVariationLp_fourier z hz rho sigma hs K t p v hv i j))
  filter_upwards [he] with w hw
  ext i j
  change _ = -(Complex.I * (w : ℂ)) * ((densityWeight rho i j : ℂ) * _)
  rw [show fourierMatrix (weightedOddVariationLp z hz rho sigma hs K t p v hv) w i j =
    (densityWeight rho i j : ℂ) * (-(Complex.I * (w : ℂ)) *
      (RadialZeroMode.radialSymbol (orderedVariation z rho sigma K p v i j) (2 * π * w) : ℂ)) from hw i j]
  ring

/-- The exact odd c/h product is zero away from the two contact points. -/
theorem actual_odd_pairing_ae_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    (fun r => star (weightedOddVariation z rho sigma K p v i j r) *
      ((densityWeight rho i j : ℂ) * HardSphere.oddRadialMoment (hVariation z rho sigma p v i j) r))
      =ᵐ[volume] 0 := by
  filter_upwards [volume.ae_ne (edgeHi sigma i j), volume.ae_ne (-edgeHi sigma i j)] with r hr hp
  by_cases hr0 : r = 0
  · simp [weightedOddVariation, oddVariation, HardSphere.oddRadialMoment, hr0]
  · have hR : |r| ≠ edgeHi sigma i j := by
      intro h
      rcases le_or_gt 0 r with hpos | hneg
      · rw [abs_of_nonneg hpos] at h
        exact hr h
      · rw [abs_of_neg hneg] at h
        exact hp (by linarith)
    have hzprod := kernel_pairing_zero_off_contact z hz rho sigma hs K t p v hv i j |r| (abs_pos.mpr hr0) hR
    have he : (densityWeight rho i j * (r * orderedVariation z rho sigma K p v i j |r|)) *
        (densityWeight rho i j * (r * hVariation z rho sigma p v i j |r|)) = 0 := by
      calc
        _ = (densityWeight rho i j) ^ 2 * r ^ 2 *
            (orderedVariation z rho sigma K p v i j |r| * hVariation z rho sigma p v i j |r|) := by ring
        _ = _ := by rw [hzprod, mul_zero]
    simpa only [weightedOddVariation, oddVariation, HardSphere.oddRadialMoment,
      ← Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_zero, Pi.zero_apply] using congrArg Complex.ofReal he

/-- The physical L2 spatial pairing is discharged internally when W is an L2
representation of the constructed h variation. Existence of such a W remains
a separate obligation. -/
theorem actual_spatialPair_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (W : MatrixL2 ℝ N)
    (hW : ∀ i j, (W i j : ℝ → ℂ) =ᵐ[volume] fun r =>
      (densityWeight rho i j : ℂ) * HardSphere.oddRadialMoment (hVariation z rho sigma p v i j) r) :
    spatialPair (weightedOddVariationLp z hz rho sigma hs K t p v hv) W = 0 := by
  apply spatialPair_zero_of_disjoint
  intro i j
  filter_upwards [weightedOddVariationLp_coe z hz rho sigma hs K t p v hv i j,
    hW i j, actual_odd_pairing_ae_zero z hz rho sigma hs K t p v hv i j] with r hc hh hp
  rw [hc, hh]
  exact hp

/-- Actual DCF variation cancellation after only the remaining h-L2 and tangent
spectral OZ identifications. The physical wave number is 2*pi*w, not w. -/
theorem actual_kernel_DCF_ae_zero_of_L2_OZ (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i) (hr : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (hfree : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hF : ∀ k : ℝ, IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k))
    (Q : MatrixL2 ℝ N)
    (hQ : ∀ i j, (Q i j : ℝ → ℂ) =ᵐ[volume] fun r =>
      (densityWeight rho i j : ℂ) * HardSphere.oddRadialMoment (hVariation z rho sigma p v i j) r)
    (hOZ : ∀ᵐ w ∂volume,
      fourierMatrix Q w = MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 (2 * π * w) *
        fourierMatrix (weightedOddVariationLp z hz rho sigma (fun i => (hs i).le) K t p v hv) w *
        MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 (2 * π * w)) :
    ∀ i j, 0 < rho i → 0 < rho j →
      orderedVariation z rho sigma K p v i j =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hscaled : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply, smul_eq_mul, hK u i j]
  have hpos : ∀ᵐ w ∂volume, (MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 (2 * π * w)).PosDef :=
    ae_of_all _ fun w => MatrixOZPairing.actual_structure_matrix_posDef z hz rho sigma (t • K) p.1 p.2
      hr hs hfree hroot hscaled (2 * π * w) (hF (2 * π * w))
  have he := positive_OZ_pairing_injective
    (fun w => MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 (2 * π * w))
    (weightedOddVariationLp z hz rho sigma (fun i => (hs i).le) K t p v hv) Q hpos hOZ
    (actual_spatialPair_zero z hz rho sigma (fun i => (hs i).le) K t p v hv Q hQ)
  intro i j hi hj
  exact actual_variation_ae_zero_of_weightedLp_zero z hz rho sigma (fun i => (hs i).le)
    K t p v hv i j hi hj (he i j)

/-- The actual variation symbol is continuous at every k, including zero;
its required radial moment bound is proved internally. -/
theorem actual_radialVariationMatrix_continuous (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) :
    Continuous (radialVariationMatrix z rho sigma K p v) := by
  apply continuous_matrix
  intro i j
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (RadialZeroMode.radialSymbol_continuous _
      (kernel_radial_moment_integrable z hz rho sigma hs K t p v hv i j)))

theorem radialSymbol_zero_of_ae_zero (f : ℝ → ℝ)
    (hf : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0) (k : ℝ) :
    RadialZeroMode.radialSymbol f k = 0 := by
  unfold RadialZeroMode.radialSymbol
  have he : (fun r => r ^ 2 * f r * sinc (k * r)) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
    filter_upwards [hf] with r hr
    simp only [hr, Pi.zero_apply, mul_zero, zero_mul]
  rw [integral_congr_ae he]
  simp

end FMSA.Paper.RadialVariationL2

/-- info: 'FMSA.Paper.RadialVariationL2.oddVariation_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.oddVariation_measurable

/-- info: 'FMSA.Paper.RadialVariationL2.oddVariation_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.oddVariation_bounded

/-- info: 'FMSA.Paper.RadialVariationL2.kernel_oddVariation_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.kernel_oddVariation_support

/-- info: 'FMSA.Paper.RadialVariationL2.kernel_oddVariation_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.kernel_oddVariation_hasCompactSupport

/-- info: 'FMSA.Paper.RadialVariationL2.kernel_oddVariation_memLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.kernel_oddVariation_memLp

/-- info: 'FMSA.Paper.RadialVariationL2.kernel_oddVariation_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.kernel_oddVariation_integrable

/-- info: 'FMSA.Paper.RadialVariationL2.oddVariationLp_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.oddVariationLp_coe

/-- info: 'FMSA.Paper.RadialVariationL2.weightedOddVariationLp_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.weightedOddVariationLp_coe

/-- info: 'FMSA.Paper.RadialVariationL2.actual_variation_ae_zero_of_weightedLp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.actual_variation_ae_zero_of_weightedLp_zero

/-- info: 'FMSA.Paper.RadialVariationL2.oddVariation_integral_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.oddVariation_integral_fourier

/-- info: 'FMSA.Paper.RadialVariationL2.oddVariationLp_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.oddVariationLp_fourier

/-- info: 'FMSA.Paper.RadialVariationL2.weightedOddVariationLp_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.weightedOddVariationLp_fourier

/-- info: 'FMSA.Paper.RadialVariationL2.actual_fourier_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.actual_fourier_matrix

/-- info: 'FMSA.Paper.RadialVariationL2.actual_odd_pairing_ae_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.actual_odd_pairing_ae_zero

/-- info: 'FMSA.Paper.RadialVariationL2.actual_spatialPair_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.actual_spatialPair_zero

/-- info: 'FMSA.Paper.RadialVariationL2.actual_kernel_DCF_ae_zero_of_L2_OZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.actual_kernel_DCF_ae_zero_of_L2_OZ

/-- info: 'FMSA.Paper.RadialVariationL2.actual_radialVariationMatrix_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.actual_radialVariationMatrix_continuous

/-- info: 'FMSA.Paper.RadialVariationL2.radialSymbol_zero_of_ae_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialVariationL2.radialSymbol_zero_of_ae_zero
