import FMSAPaper.BaxterWeakPrimitive
import FMSAPaper.ActualRadialIdentification

/-! The full reflected weak formula represents the actual radial DCF for
every species pair at a symmetric-strength MSA root. Test functions have
compact support in the positive radial axis. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.ActualRadialWeak
open ExactMSA.MultiTailMixture MSAMixture MatrixQ0
open BaxterSecondDerivative BaxterWeakPrimitive WeakDerivativePairing ActualRadialIdentification
variable {N : ℕ} {T : Type*} [Fintype T]

theorem ordered_root_primitive_weak (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (hroot : IsRoot z rho sigma K Dt G)
    (i j : Fin N) (horder : sigma j <= sigma i)
    (phi : ℝ → ℝ) (hp : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ Ioi (0 : ℝ)) :
    (∫ r : ℝ, realPrimitive z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j r * deriv phi r) =
      2 * π * ∫ r : ℝ, r * correlation z rho sigma (amplitudeA z rho sigma Dt G)
        (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j r * phi r := by
  let A := amplitudeA z rho sigma Dt G
  let qp := amplitudeQp z rho sigma Dt G
  let w := W z rho Dt G
  let c := C z rho sigma Dt G
  let P := rightPrimitiveReal z rho sigma A qp w c i j
  obtain ⟨L, hL⟩ := rightPrimitiveReal_lipschitz z hz rho sigma A qp w c hsigma i j
  have hi := (correlation_radius_integrable_of_root z hz rho sigma K Dt G hsigma hroot i j horder).const_mul (-2 * π)
  have h := weakDerivative_on_positive P (fun r => -2 * π * (r * correlation z rho sigma A qp w c i j r))
    {edgeHi sigma i j} (countable_singleton _) hL.continuous.continuousOn
    (fun r hr => by
      convert! rightPrimitiveReal_hasDerivAt_positive z hz rho sigma A qp w c hsigma i j horder r hr.1
        (by simpa using hr.2) using 1
      ring) hi phi hp hc hsupp
  have he : (∫ r : ℝ, realPrimitive z rho sigma A qp w c i j r * deriv phi r) =
      ∫ r : ℝ, P r * deriv phi r := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro r
    by_cases hr : 0 < r
    · dsimp only
      rw [realPrimitive_eq_re, baxterPrimitive_positive_eq_ofReal z rho sigma A qp w c i j horder r hr,
        Complex.ofReal_re, ← rightPrimitiveReal_eq_ordered_positive z rho sigma A qp w c i j horder r hr]
    · have hd : deriv phi r = 0 := by
        by_contra hn
        exact hr (hsupp (support_deriv_subset hn))
      simp only [hd, mul_zero]
  change (∫ r : ℝ, realPrimitive z rho sigma A qp w c i j r * deriv phi r) = _
  rw [he]
  simp only [mul_assoc, integral_const_mul] at h ⊢
  linarith

theorem root_primitive_weak (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) (phi : ℝ → ℝ) (hp : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hsupp : tsupport phi ⊆ Ioi (0 : ℝ)) :
    (∫ r : ℝ, realPrimitive z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j r * deriv phi r) =
      2 * π * ∫ r : ℝ, r * orderedRadialCorrelation z rho sigma K Dt G i j r * phi r := by
  by_cases ho : sigma j <= sigma i
  · simpa only [orderedRadialCorrelation, if_pos ho] using
      ordered_root_primitive_weak z hz rho sigma K Dt G hsigma hroot i j ho phi hp hc hsupp
  · have he : (∫ r : ℝ, realPrimitive z rho sigma (amplitudeA z rho sigma Dt G)
        (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j r * deriv phi r) =
        ∫ r : ℝ, realPrimitive z rho sigma (amplitudeA z rho sigma Dt G)
        (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) j i r * deriv phi r := by
      apply integral_congr_ae
      filter_upwards [root_primitive_reciprocity z rho sigma K Dt G hz hsigma hv hroot hK i j] with r hr
      simp only [realPrimitive_eq_re, hr]
    rw [he]
    simpa only [orderedRadialCorrelation, if_neg ho] using
      ordered_root_primitive_weak z hz rho sigma K Dt G hsigma hroot j i (not_le.mp ho).le phi hp hc hsupp

theorem root_second_weak (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) (phi : ℝ → ℝ) (hp : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hsupp : tsupport phi ⊆ Ioi (0 : ℝ)) :
    2 * π * (∫ r : ℝ, r * orderedRadialCorrelation z rho sigma K Dt G i j r * phi r) =
      (∫ r : ℝ, secondNumerator z rho sigma (amplitudeA z rho sigma Dt G)
        (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j r * phi r) -
      lowerValue sigma (amplitudeA z rho sigma Dt G) (amplitudeQp z rho sigma Dt G)
        (W z rho Dt G) (C z rho sigma Dt G) i j * phi (edgeLo sigma i j) +
      lowerValue sigma (amplitudeA z rho sigma Dt G) (amplitudeQp z rho sigma Dt G)
        (W z rho Dt G) (C z rho sigma Dt G) j i * phi (-edgeLo sigma j i) := by
  rw [← root_primitive_weak z hz rho sigma K Dt G hsigma hv hroot hK i j phi hp hc hsupp]
  exact fullPrimitive_weak_derivative z hz rho sigma _ _ _ _ hsigma i j phi hp hc

end FMSA.Paper.ActualRadialWeak

/-- info: 'FMSA.Paper.ActualRadialWeak.ordered_root_primitive_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialWeak.ordered_root_primitive_weak

/-- info: 'FMSA.Paper.ActualRadialWeak.root_primitive_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialWeak.root_primitive_weak

/-- info: 'FMSA.Paper.ActualRadialWeak.root_second_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialWeak.root_second_weak
