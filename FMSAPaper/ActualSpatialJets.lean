import FMSAPaper.MultirateSpatialMembership
import FMSAPaper.SpatialJets
import FMSAPaper.PhysicalExteriorJets

/-! Actual DCF Taylor coefficients retain the fixed spatial dictionary on
both ordered core pieces. Only local finite-order amplitude smoothness is needed. -/
noncomputable section
open MeasureTheory Filter Topology Set Real
open scoped ContDiff BigOperators

namespace FMSA.Paper.ActualSpatialJets

open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture MSAMixtureCoreUneq
open SpatialDictionary MultirateSpatialMembership PhysicalExteriorJets
variable {N : ℕ} {T : Type*} [Fintype T]

theorem weighted_correlation_hasForm (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (s : Set ℝ)
    (hr : ∀ r ∈ s, r ≠ 0)
    (hnum : HasForm z s (ActualBaxterSuperposition.numerator z rho sigma
      (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j)) :
    HasForm z s (fun r => r * rootCorrelation z rho sigma p i j r) := by
  apply (hnum.const_mul (1 / (2 * π))).congr
  intro r hrs
  unfold rootCorrelation correlation ActualBaxterSuperposition.numerator
    BaxterSuperposition.numerator BaxterSuperposition.cross
  field_simp [hr r hrs, Real.pi_ne_zero]

theorem core_jet_hasForm_of_numerator (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (s : Set ℝ) (hr : ∀ r ∈ s, r ≠ 0)
    (hnum : ∀ a : TailMatrix T N × TailMatrix T N,
      HasForm z s (ActualBaxterSuperposition.numerator z rho sigma
        (amplitudeA z rho sigma a.1 a.2) (amplitudeQp z rho sigma a.1 a.2)
        (W z rho a.1 a.2) (C z rho sigma a.1 a.2) i j))
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (hp : ContDiffAt ℝ n p 0) :
    HasForm z s (fun r => r * jet (fun t => rootCorrelation z rho sigma (p t) i j r) n) := by
  have h := SpatialJets.jet_hasForm_of_smooth_parameters z s
    (fun a r => r * rootCorrelation z rho sigma a i j r)
    (fun a => weighted_correlation_hasForm z rho sigma a i j s hr (hnum a))
    (fun r _ => contDiff_const.mul (correlation_contDiff_amplitudes z hz rho sigma hsigma i j r))
    p n hp
  apply h.congr
  intro r _
  simp only [jet, iteratedDeriv_const_mul_field]
  ring

theorem core_jet_inner_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u) (u0 : T)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (hj : 0 < sigma j) (horder : sigma j <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (hp : ContDiffAt ℝ n p 0) :
    HasForm z (Ioo (0 : ℝ) (lamA sigma i j))
      (fun r => r * jet (fun t => rootCorrelation z rho sigma (p t) i j r) n) := by
  apply core_jet_hasForm_of_numerator z hz rho sigma hsigma i j _ (fun r hr => hr.1.ne')
    _ p n hp
  intro a
  exact numerator_inner_hasForm z hz u0 rho sigma _ _ _ _ hsigma i j hj horder

theorem core_jet_outer_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u) (u0 : T)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (hj : 0 < sigma j) (horder : sigma j <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (hp : ContDiffAt ℝ n p 0) :
    HasForm z (Ioo (lamA sigma i j) (edgeHi sigma i j))
      (fun r => r * jet (fun t => rootCorrelation z rho sigma (p t) i j r) n) := by
  apply core_jet_hasForm_of_numerator z hz rho sigma hsigma i j _
    (fun r hr => (lt_of_le_of_lt (abs_nonneg _) hr.1).ne') _ p n hp
  intro a
  exact numerator_outer_hasForm z hz u0 rho sigma _ _ _ _ hsigma i j hj horder

theorem coefficient_contDiffOn_of_weighted (z : T → ℝ) (s : Set ℝ) (f : ℝ → ℝ)
    (hr : ∀ r ∈ s, r ≠ 0) (h : HasForm z s (fun r => r * f r)) :
    ContDiffOn ℝ ∞ f s := by
  have hd := h.contDiffOn.div contDiffOn_id hr
  apply hd.congr
  intro r hrs
  exact (mul_div_cancel_left₀ (f r) (hr r hrs)).symm

theorem core_jet_contDiffOn (z : T → ℝ) (hz : ∀ u, 0 < z u) (u0 : T)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (hj : 0 < sigma j) (horder : sigma j <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (hp : ContDiffAt ℝ n p 0) :
    ContDiffOn ℝ ∞ (fun r => jet (fun t => rootCorrelation z rho sigma (p t) i j r) n)
      (Ioo (0 : ℝ) (lamA sigma i j)) ∧
    ContDiffOn ℝ ∞ (fun r => jet (fun t => rootCorrelation z rho sigma (p t) i j r) n)
      (Ioo (lamA sigma i j) (edgeHi sigma i j)) := by
  constructor
  · exact coefficient_contDiffOn_of_weighted z _ _ (fun r hr => hr.1.ne')
      (core_jet_inner_hasForm z hz u0 rho sigma hsigma i j hj horder p n hp)
  · exact coefficient_contDiffOn_of_weighted z _ _
      (fun r hr => (lt_of_le_of_lt (abs_nonneg _) hr.1).ne')
      (core_jet_outer_hasForm z hz u0 rho sigma hsigma i j hj horder p n hp)

end FMSA.Paper.ActualSpatialJets

/-- info: 'FMSA.Paper.ActualSpatialJets.weighted_correlation_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualSpatialJets.weighted_correlation_hasForm

/-- info: 'FMSA.Paper.ActualSpatialJets.core_jet_hasForm_of_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualSpatialJets.core_jet_hasForm_of_numerator

/-- info: 'FMSA.Paper.ActualSpatialJets.core_jet_inner_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualSpatialJets.core_jet_inner_hasForm

/-- info: 'FMSA.Paper.ActualSpatialJets.core_jet_outer_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualSpatialJets.core_jet_outer_hasForm

/-- info: 'FMSA.Paper.ActualSpatialJets.coefficient_contDiffOn_of_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualSpatialJets.coefficient_contDiffOn_of_weighted

/-- info: 'FMSA.Paper.ActualSpatialJets.core_jet_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualSpatialJets.core_jet_contDiffOn
