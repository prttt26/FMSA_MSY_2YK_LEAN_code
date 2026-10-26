import FMSAPaper.PhysicalExteriorJets
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearRDF

/-! Actual residual-kernel variations have disjoint DCF/RDF supports.
The exterior identity holds off-root; no kernel vector is assumed to
integrate to a curve of roots. The global OZ/Parseval bridge is separate. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Paper.JacobianExterior
open ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture MatrixQ0
open PhysicalExteriorJets
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual amplitude derivative of the full BH residual at fixed coupling. -/
def amplitudeJacobian (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N) :
    (TailMatrix T N × TailMatrix T N) →L[ℝ] (TailMatrix T N × TailMatrix T N) :=
  (fderiv ℝ (residual z rho sigma K) (t, p)).comp
    (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))

/-- Exterior evaluation of the first BH residual block. -/
def exteriorFunctional (z : T → ℝ) (sigma : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    TailMatrix T N →L[ℝ] ℝ :=
  ∑ u, (z u * exp (-z u * (r - edgeHi sigma i j)) / (2 * π * r)) • entry u i j

theorem exteriorFunctional_apply (z : T → ℝ) (sigma : Fin N → ℝ)
    (i j : Fin N) (r : ℝ) (D : TailMatrix T N) :
    exteriorFunctional z sigma i j r D =
      ∑ u, z u * exp (-z u * (r - edgeHi sigma i j)) / (2 * π * r) * D u i j := by
  simp [exteriorFunctional, entry]

/-- The actual DCF exterior factors through firstLHS even away from every root. -/
theorem exterior_factorization (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ)
    (hr : edgeHi sigma i j < r) :
    rootCorrelation z rho sigma p i j r =
      exteriorFunctional z sigma i j r (firstLHS z rho sigma p.1 p.2) := by
  have hS (u : T) (a b : Fin N) :
      exteriorAmplitude z sigma (W z rho p.1 p.2) (C z rho sigma p.1 p.2) u a b =
        p.1 u a b * exp (z u * edgeHi sigma a b) := W_add_C_exp z rho sigma p.1 p.2 u a b
  have hedge (u : T) (l : Fin N) : exp (z u * edgeHi sigma i l) =
      exp (z u * edgeHi sigma i j) * exp (z u * edgeLo sigma j l) := by
    rw [← exp_add]
    congr 1
    unfold edgeHi edgeLo
    ring
  have hb (u : T) :
      exteriorAmplitude z sigma (W z rho p.1 p.2) (C z rho sigma p.1 p.2) u i j -
        ∑ l, rho l * exteriorAmplitude z sigma (W z rho p.1 p.2) (C z rho sigma p.1 p.2) u i l *
          dressedQhat z rho sigma p.1 p.2 (z u) j l =
      exp (z u * edgeHi sigma i j) * firstLHS z rho sigma p.1 p.2 u i j := by
    simp_rw [hS]
    rw [firstLHS_eq, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro l _
      rw [hedge u l]
      ring
  unfold rootCorrelation correlation
  rw [correlation_numerator_exterior z hz rho sigma _ _ _ _ hs i j r hr]
  change (∑ u, z u * exp (-z u * r) *
    (exteriorAmplitude z sigma (W z rho p.1 p.2) (C z rho sigma p.1 p.2) u i j -
      ∑ l, rho l * exteriorAmplitude z sigma (W z rho p.1 p.2) (C z rho sigma p.1 p.2) u i l *
        dressedQhat z rho sigma p.1 p.2 (z u) j l)) / (2 * π * r) = _
  simp_rw [hb]
  rw [exteriorFunctional_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  rw [show -z u * (r - edgeHi sigma i j) = -z u * r + z u * edgeHi sigma i j by ring, exp_add]
  ring

/-- Exact exterior defect identity for arbitrary amplitudes, not just BH roots. -/
theorem exterior_residual_decomposition (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ)
    (hr : edgeHi sigma i j < r) :
    rootCorrelation z rho sigma p i j r =
      t * (∑ u, K u i j * exp (-z u * (r - edgeHi sigma i j)) / r) +
      exteriorFunctional z sigma i j r (residual z rho sigma K (t, p)).1 := by
  have hr0 : r ≠ 0 := by
    have hR : 0 ≤ edgeHi sigma i j := by unfold edgeHi; linarith [hs i, hs j]
    exact (hR.trans_lt hr).ne'
  have he : (residual z rho sigma K (t, p)).1 = firstLHS z rho sigma p.1 p.2 -
      t • (fun u i j => 2 * π * K u i j / z u) := by
    funext u i j
    simp only [ExactMSA.MultiTailMixture.residual, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsource : exteriorFunctional z sigma i j r (fun u i j => 2 * π * K u i j / z u) =
      ∑ u, K u i j * exp (-z u * (r - edgeHi sigma i j)) / r := by
    rw [exteriorFunctional_apply]
    apply Finset.sum_congr rfl
    intro u _
    field_simp [(hz u).ne', pi_ne_zero, hr0]
  rw [he, map_sub, map_smul, hsource, ← exterior_factorization z hz rho sigma hs p i j r hr]
  simp only [smul_eq_mul]
  ring

theorem residual_amplitudes_hasFDerivAt (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (t : ℝ) (p : TailMatrix T N × TailMatrix T N) :
    HasFDerivAt (fun a => residual z rho sigma K (t, a))
      (amplitudeJacobian z rho sigma K t p) p := by
  have hR := ((residual_contDiff z rho sigma K).differentiable (by simp)).differentiableAt.hasFDerivAt
    (x := (t, p))
  have hinc : HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N => (t, a))
      (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N)) p := by
    exact hasFDerivAt_prodMk_right t p
  exact hR.comp p hinc

/-- Actual exterior derivative, expressed through the full fixed-coupling Jacobian. -/
theorem exterior_hasFDerivAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ)
    (hr : edgeHi sigma i j < r) :
    HasFDerivAt (fun a => rootCorrelation z rho sigma a i j r)
      ((exteriorFunctional z sigma i j r).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (amplitudeJacobian z rho sigma K t p))) p := by
  have h := ((exteriorFunctional z sigma i j r).hasFDerivAt.comp p
    (residual_amplitudes_hasFDerivAt z rho sigma K t p).fst).const_add
      (t * (∑ u, K u i j * exp (-z u * (r - edgeHi sigma i j)) / r))
  have he : (fun a => rootCorrelation z rho sigma a i j r) =
      fun a => t * (∑ u, K u i j * exp (-z u * (r - edgeHi sigma i j)) / r) +
        exteriorFunctional z sigma i j r (residual z rho sigma K (t, a)).1 := by
    funext a
    exact exterior_residual_decomposition z hz rho sigma hs K t a i j r hr
  rw [he]
  exact h

/-- DCF variation in an arbitrary amplitude direction, not an assumed root curve. -/
def correlationVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  (fderiv ℝ (fun a => rootCorrelation z rho sigma a i j r) p) v

theorem exterior_variation (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ)
    (hr : edgeHi sigma i j < r) :
    correlationVariation z rho sigma p v i j r =
      exteriorFunctional z sigma i j r (amplitudeJacobian z rho sigma K t p v).1 := by
  unfold correlationVariation
  rw [(exterior_hasFDerivAt z hz rho sigma hs K t p i j r hr).fderiv]
  rfl

/-- Every kernel direction of the actual BH amplitude Jacobian fixes the exterior DCF. -/
theorem kernel_exterior_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (i j : Fin N) (r : ℝ) (hr : edgeHi sigma i j < r) :
    correlationVariation z rho sigma p v i j r = 0 := by
  rw [exterior_variation z hz rho sigma hs K t p v i j r hr, hv]
  exact map_zero _

/-- Ordered actual DCF variation; the strength argument is retained as in
orderedRadialCorrelation, whose value depends only on the amplitudes. -/
def orderedVariation (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
    orderedRadialCorrelation z rho sigma K a.1 a.2 i j r) p) v

theorem kernel_ordered_exterior_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (i j : Fin N) (r : ℝ) (hr : edgeHi sigma i j < r) :
    orderedVariation z rho sigma K p v i j r = 0 := by
  unfold orderedVariation orderedRadialCorrelation
  by_cases h : sigma j ≤ sigma i
  · simp only [if_pos h]
    exact kernel_exterior_zero z hz rho sigma hs K t p v hv i j r hr
  · simp only [if_neg h]
    apply kernel_exterior_zero z hz rho sigma hs K t p v hv j i r
    simpa only [edgeHi, add_comm] using hr

/-- The actual constructed h varies by zero inside the hard core for every
amplitude direction. This does not assert its global OZ identification. -/
theorem nonlinearH_core_hasFDerivAt (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ)
    (hr : 0 < r) (hR : r < edgeHi sigma i j) :
    HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearH z rho sigma a.1 a.2 i j r)
      (0 : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ) p := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearH z rho sigma a.1 a.2 i j r) = fun _ => (-1 : ℝ) := by
    funext a
    exact nonlinearH_hardcore z rho sigma a.1 a.2 i j r hr hR
  rw [he]
  exact hasFDerivAt_const _ _

def hVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
    nonlinearH z rho sigma a.1 a.2 i j r) p) v

theorem hVariation_core_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ)
    (hr : 0 < r) (hR : r < edgeHi sigma i j) :
    hVariation z rho sigma p v i j r = 0 := by
  unfold hVariation
  rw [(nonlinearH_core_hasFDerivAt z rho sigma p i j r hr hR).fderiv]
  rfl

/-- The actual kernel variations have zero pairing off contact. -/
theorem kernel_pairing_zero_off_contact (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (i j : Fin N) (r : ℝ) (hr : 0 < r) (hR : r ≠ edgeHi sigma i j) :
    orderedVariation z rho sigma K p v i j r * hVariation z rho sigma p v i j r = 0 := by
  rcases lt_or_gt_of_ne hR with h | h
  · rw [hVariation_core_zero z rho sigma p v i j r hr h, mul_zero]
  · rw [kernel_ordered_exterior_zero z hz rho sigma hs K t p v hv i j r h, zero_mul]

/-- Contact is a null set, so the physical radial pairing vanishes a.e. -/
theorem kernel_pairing_ae_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    (fun r => r ^ 2 * orderedVariation z rho sigma K p v i j r * hVariation z rho sigma p v i j r)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (volume.ae_ne (edgeHi sigma i j))] with r hr hR
  have he := kernel_pairing_zero_off_contact z hz rho sigma hs K t p v hv i j r hr hR
  change r ^ 2 * _ * _ = 0
  rw [mul_assoc, he, mul_zero]

/-- The complete density-weighted spatial side of the linearized pairing is zero.
No Parseval or spectral positivity is assumed or concluded here. -/
theorem kernel_spatial_pairing_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) :
    ∑ i, ∑ j, rho i * rho j * (∫ r in Ioi (0 : ℝ),
      r ^ 2 * orderedVariation z rho sigma K p v i j r * hVariation z rho sigma p v i j r) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [integral_congr_ae (kernel_pairing_ae_zero z hz rho sigma hs K t p v hv i j)]
  simp

/-- Every differentiable amplitude curve in a kernel direction has zero
exterior DCF derivative. The curve need not consist of roots. -/
theorem kernel_curve_exterior_hasDerivAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (curve : ℝ → TailMatrix T N × TailMatrix T N) (s : ℝ)
    (hc : HasDerivAt curve v s) (hp : curve s = p)
    (i j : Fin N) (r : ℝ) (hr : edgeHi sigma i j < r) :
    HasDerivAt (fun a => rootCorrelation z rho sigma (curve a) i j r) 0 s := by
  have h := exterior_hasFDerivAt z hz rho sigma hs K t p i j r hr
  rw [← hp] at h
  have he := h.comp_hasDerivAt s hc
  change HasDerivAt (fun a => rootCorrelation z rho sigma (curve a) i j r)
    (exteriorFunctional z sigma i j r (amplitudeJacobian z rho sigma K t (curve s) v).1) s at he
  rw [hp, hv] at he
  simpa using he

/-- Positive-axis DCF variations in kernel directions have compact support.
This is an actual parameter derivative of the existing ordered DCF. -/
theorem kernel_positive_variation_support (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    Function.support (fun r : ℝ => if 0 < r then orderedVariation z rho sigma K p v i j r else 0)
      ⊆ Icc (0 : ℝ) (edgeHi sigma i j) := by
  intro r hr
  have he : (if 0 < r then orderedVariation z rho sigma K p v i j r else 0) ≠ 0 := hr
  by_cases h : 0 < r
  · refine ⟨h.le, ?_⟩
    by_contra hR
    have hzv := kernel_ordered_exterior_zero z hz rho sigma hs K t p v hv i j r (lt_of_not_ge hR)
    exact he (by simp only [if_pos h, hzv])
  · exact (he (by simp only [if_neg h])).elim

end FMSA.Paper.JacobianExterior

/-- info: 'FMSA.Paper.JacobianExterior.exteriorFunctional_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.exteriorFunctional_apply

/-- info: 'FMSA.Paper.JacobianExterior.exterior_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.exterior_factorization

/-- info: 'FMSA.Paper.JacobianExterior.exterior_residual_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.exterior_residual_decomposition

/-- info: 'FMSA.Paper.JacobianExterior.residual_amplitudes_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.residual_amplitudes_hasFDerivAt

/-- info: 'FMSA.Paper.JacobianExterior.exterior_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.exterior_hasFDerivAt

/-- info: 'FMSA.Paper.JacobianExterior.exterior_variation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.exterior_variation

/-- info: 'FMSA.Paper.JacobianExterior.kernel_exterior_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.kernel_exterior_zero

/-- info: 'FMSA.Paper.JacobianExterior.kernel_ordered_exterior_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.kernel_ordered_exterior_zero

/-- info: 'FMSA.Paper.JacobianExterior.nonlinearH_core_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.nonlinearH_core_hasFDerivAt

/-- info: 'FMSA.Paper.JacobianExterior.hVariation_core_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.hVariation_core_zero

/-- info: 'FMSA.Paper.JacobianExterior.kernel_pairing_zero_off_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.kernel_pairing_zero_off_contact

/-- info: 'FMSA.Paper.JacobianExterior.kernel_pairing_ae_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.kernel_pairing_ae_zero

/-- info: 'FMSA.Paper.JacobianExterior.kernel_spatial_pairing_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.kernel_spatial_pairing_zero

/-- info: 'FMSA.Paper.JacobianExterior.kernel_curve_exterior_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.kernel_curve_exterior_hasDerivAt

/-- info: 'FMSA.Paper.JacobianExterior.kernel_positive_variation_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.JacobianExterior.kernel_positive_variation_support
