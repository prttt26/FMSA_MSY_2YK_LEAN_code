import FMSAPaper.BaxterSecondIntegralJets
import FMSAPaper.ActualRadialWeak

/-! Actual radius-weighted radial DCF jets commute with compact test
integration. The finite representation handles the apparent division by r;
tests vanish at zero, and no derivative-under-integral premise is required. -/
noncomputable section
open MeasureTheory Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.RadialIntegralJets
open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture
open FiniteBasis FiniteIntegralJets WeakDerivativePairing BaxterIntegrationByParts
open BaxterWeakJetBasis BaxterSecondIntegralJets PhysicalExteriorJets
variable {N : ℕ} {T : Type*} [Fintype T]

theorem basisConvolution_radius_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (b c : BasisIndex T) (i j l : Fin N) :
    Integrable (basisConvolution z sigma b c i j l) := by
  have h := crossCorr_integrable _ _ (basisPrime_integrable z hz sigma hsigma b i l)
    (basisQ_integrable z hz sigma hsigma c j l)
  convert! h using 1
  funext r
  exact cross_integral_translate _ _ r

def radialBasis (z : T → ℝ) (sigma : Fin N → ℝ) (i j : Fin N) : Index T N → ℝ → ℝ
  | .inl b => fun r => -basisPrime z sigma b i j r
  | .inr (.inl _) => fun _ => 0
  | .inr (.inr (l,b,c)) => fun r => -basisConvolution z sigma b c i j l r

theorem radialBasis_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (k : Index T N) :
    Integrable (radialBasis z sigma i j k) := by
  rcases k with b | (b | ⟨l,b,c⟩)
  · exact (basisPrime_integrable z hz sigma hsigma b i j).neg
  · exact integrable_zero _ _ _
  · exact (basisConvolution_radius_integrable z hz sigma hsigma b c i j l).neg

theorem correlation_radius_eq_linear (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : r ≠ 0) :
    r * rootCorrelation z rho sigma p i j r =
      linear (coefficients z rho sigma p i j) (fun k => radialBasis z sigma i j k r) / (2*π) := by
  have he : (-qPrime z sigma (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r +
      ∑ l, rho l * ∫ t : ℝ,
        qPrime z sigma (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
          (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i l (t+r) *
        q z sigma (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
          (W z rho p.1 p.2) (C z rho sigma p.1 p.2) j l t) =
      linear (coefficients z rho sigma p i j) (fun k => radialBasis z sigma i j k r) := by
    simp only [convolution_eq_basis z hz sigma _ _ _ _ hsigma]
    simp only [qPrime_eq_basis, linear_index, coefficients, radialBasis, bhCoefficient]
    simp only [mul_zero, Finset.sum_const_zero, zero_add, Finset.mul_sum,
      mul_neg, neg_mul, neg_neg, mul_assoc, Finset.sum_neg_distrib]
  unfold rootCorrelation correlation
  rw [he]
  field_simp

theorem correlation_test_eq_linear (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (phi : ℝ → ℝ) (hzero : phi 0 = 0) (r : ℝ) :
    r * rootCorrelation z rho sigma p i j r * phi r =
      linear (coefficients z rho sigma p i j) (fun k => radialBasis z sigma i j k r * phi r / (2*π)) := by
  by_cases hr : r = 0
  · simp [hr, hzero, linear]
  · rw [correlation_radius_eq_linear z hz rho sigma hsigma p i j r hr]
    simp only [linear, Finset.sum_mul, Finset.sum_div, div_mul_eq_mul_div, mul_assoc, mul_div_assoc]

theorem correlation_test_jet_integral (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : Continuous phi)
    (hc : HasCompactSupport phi) (hzero : phi 0 = 0) :
    jet (fun s => ∫ r : ℝ, r * rootCorrelation z rho sigma (p s) i j r * phi r) n =
      ∫ r : ℝ, r * jet (fun s => rootCorrelation z rho sigma (p s) i j r) n * phi r := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hphi
  have ha (k : Index T N) : ContDiffAt ℝ n (fun s => coefficients z rho sigma (p s) i j k) 0 :=
    ((coefficients_contDiff z rho sigma i j k).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  have hb (k : Index T N) : Integrable (fun r => radialBasis z sigma i j k r * phi r / (2*π)) :=
    ((radialBasis_integrable z hz sigma hsigma i j k).mul_bdd
      hphi.aestronglyMeasurable (Eventually.of_forall hM)).div_const _
  have h := jet_integral_linear (fun s => coefficients z rho sigma (p s) i j)
    (fun k r => radialBasis z sigma i j k r * phi r / (2*π)) n ha hb
  simp only [← correlation_test_eq_linear z hz rho sigma hsigma _ i j phi hzero] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [jet, iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field]
  ring

theorem ordered_test_jet_integral (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (K : ℝ → TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0) (n : ℕ) (i j : Fin N)
    (phi : ℝ → ℝ) (hphi : Continuous phi) (hc : HasCompactSupport phi) (hzero : phi 0 = 0) :
    jet (fun s => ∫ r : ℝ, r * orderedRadialCorrelation z rho sigma (K s) (p s).1 (p s).2 i j r * phi r) n =
      ∫ r : ℝ, r * jet (fun s => orderedRadialCorrelation z rho sigma (K s) (p s).1 (p s).2 i j r) n * phi r := by
  by_cases ho : sigma j <= sigma i
  · simpa only [orderedRadialCorrelation, if_pos ho, rootCorrelation] using
      correlation_test_jet_integral z hz rho sigma hsigma p hp n i j phi hphi hc hzero
  · simpa only [orderedRadialCorrelation, if_neg ho, rootCorrelation] using
      correlation_test_jet_integral z hz rho sigma hsigma p hp n j i phi hphi hc hzero

end FMSA.Paper.RadialIntegralJets

/-- info: 'FMSA.Paper.RadialIntegralJets.basisConvolution_radius_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialIntegralJets.basisConvolution_radius_integrable

/-- info: 'FMSA.Paper.RadialIntegralJets.radialBasis_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialIntegralJets.radialBasis_integrable

/-- info: 'FMSA.Paper.RadialIntegralJets.correlation_radius_eq_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialIntegralJets.correlation_radius_eq_linear

/-- info: 'FMSA.Paper.RadialIntegralJets.correlation_test_eq_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialIntegralJets.correlation_test_eq_linear

/-- info: 'FMSA.Paper.RadialIntegralJets.correlation_test_jet_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialIntegralJets.correlation_test_jet_integral

/-- info: 'FMSA.Paper.RadialIntegralJets.ordered_test_jet_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialIntegralJets.ordered_test_jet_integral
