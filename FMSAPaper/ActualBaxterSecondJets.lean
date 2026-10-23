import FMSAPaper.BaxterSecondDerivative
import FMSAPaper.ActualBaxterBoundaryJets

/-! The second-factor Cauchy formula for the actual ordered radial DCF.
Every lower-edge atom of the differentiated factor is retained explicitly. -/
noncomputable section
open MeasureTheory Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.ActualBaxterSecondJets
open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture
open ActualBaxterJets ActualBaxterBoundaryJets FiniteBasis
open BaxterIntegrationByParts BaxterSecondDerivative BaxterNormalization PhysicalExteriorJets
variable {N : ℕ} {T : Type*} [Fintype T]

def actualSecondConvolution (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j l : Fin N) (r : ℝ) : ℝ :=
  secondConvolution z sigma (amplitudeA z rho sigma p.1 p.2)
    (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j l r

theorem first_eq_neg_second (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j l : Fin N)
    (horder : sigma j <= sigma i) (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ, factorPrime z rho sigma p i l (t+r) * factor z rho sigma p j l t) =
      -actualSecondConvolution z rho sigma p i j l r := by
  have hsep : edgeLo sigma i l < edgeLo sigma j l+r := by unfold edgeLo; linarith
  have h := product_integration_by_parts_of_lower_order z hz sigma
    (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) hsigma i j l r hsep
  have ht := cross_integral_translate
    (factor z rho sigma p i l) (factorPrime z rho sigma p j l) r
  change (∫ t : ℝ, factorPrime z rho sigma p i l (t+r) * factor z rho sigma p j l t) +
    (∫ t : ℝ, factor z rho sigma p i l (t+r) * factorPrime z rho sigma p j l t) =
      -factor z rho sigma p i l (edgeLo sigma j l+r) * lowerJump z rho sigma p j l at h
  rw [ht] at h
  change _ = -((∫ t : ℝ, factor z rho sigma p i l t * factorPrime z rho sigma p j l (t-r)) +
    factor z rho sigma p i l (edgeLo sigma j l+r) * lowerJump z rho sigma p j l)
  linarith

theorem second_convolution_jet_cauchy
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j l : Fin N) (r : ℝ) :
    jet (fun s => actualSecondConvolution z rho sigma (p s) i j l r) n =
      ∑ a ∈ Finset.range (n+1),
        ((∫ t : ℝ, jet (fun s => factor z rho sigma (p s) i l t) a *
          jet (fun s => factorPrime z rho sigma (p s) j l (t-r)) (n-a)) +
        jet (fun s => factor z rho sigma (p s) i l (edgeLo sigma j l+r)) a *
          jet (fun s => lowerJump z rho sigma (p s) j l) (n-a)) := by
  have hpn (k : ℕ) : ContDiffAt ℝ k p 0 := hp.of_le (by exact_mod_cast le_top)
  have h := convolution_with_lowerJump_jet z rho sigma hz hsigma p n (hpn n) j i l (-r)
  simp only [← sub_eq_add_neg, sub_neg_eq_add] at h
  change jet (fun s => actualSecondConvolution z rho sigma (p s) i j l r) n = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [lowerJump_eq_factor z rho sigma hsigma,
    factor_jet_basis z rho sigma p a (hpn a),
    factor_jet_basis z rho sigma p (n-a) (hpn (n-a)),
    factorPrime_jet_basis z rho sigma p (n-a) (hpn (n-a))]
  apply (integral_add_jump_expansion _ _
    (fun b t => basisQ z sigma b i l t) (fun c t => basisPrime z sigma c j l (t-r))
    (fun c => basisQ z sigma c j l (edgeLo sigma j l)) (edgeLo sigma j l+r) _).symm
  intro b c
  simpa only [← sub_eq_add_neg, mul_comm] using
    basisConvolution_integrable z hz sigma hsigma c b j i l (-r)

theorem correlation_second_jet_cauchy
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (horder : sigma j <= sigma i) (r : ℝ) (hr : 0 < r) :
    r * jet (fun s => rootCorrelation z rho sigma (p s) i j r) n =
      (-jet (fun s => factorPrime z rho sigma (p s) i j r) n +
        jet (fun s => factorPrime z rho sigma (p s) j i (-r)) n -
        ∑ l, rho l * ∑ a ∈ Finset.range (n+1),
          ((∫ t : ℝ, jet (fun s => factor z rho sigma (p s) i l t) a *
            jet (fun s => factorPrime z rho sigma (p s) j l (t-r)) (n-a)) +
          jet (fun s => factor z rho sigma (p s) i l (edgeLo sigma j l+r)) a *
            jet (fun s => lowerJump z rho sigma (p s) j l) (n-a))) / (2*π) := by
  have hzero : jet (fun s => factorPrime z rho sigma (p s) j i (-r)) n = 0 := by
    have hlt : -r < edgeLo sigma j i := by unfold edgeLo; linarith
    simp only [factorPrime, qPrime, if_pos hlt]
    simp [jet]
  have hj (l : Fin N) :
      jet (fun s => ∫ t : ℝ, factorPrime z rho sigma (p s) i l (t+r) *
        factor z rho sigma (p s) j l t) n =
        -jet (fun s => actualSecondConvolution z rho sigma (p s) i j l r) n := by
    simp_rw [first_eq_neg_second z hz rho sigma hsigma _ i j l horder r hr]
    simp only [jet, iteratedDeriv_fun_neg, neg_div]
  rw [correlation_jet_cauchy z hz rho sigma hsigma p hp n i j r hr.ne', hzero, add_zero]
  simp_rw [← convolution_jet_cauchy z rho sigma hz hsigma p hp n i j,
    hj, second_convolution_jet_cauchy z rho sigma hz hsigma p hp n i j,
    mul_neg, Finset.sum_neg_distrib]
  ring

/-- Paper normalization q = Q/(2*pi). The integral includes the ordinary
second-factor derivative; the following product is its lower-edge Dirac term. -/
theorem normalized_correlation_second_jet_cauchy
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (horder : sigma j <= sigma i) (r : ℝ) (hr : 0 < r) :
    r * jet (fun s => rootCorrelation z rho sigma (p s) i j r) n =
      -jet (fun s => factorPrime z rho sigma (p s) i j r / (2*π)) n +
        jet (fun s => factorPrime z rho sigma (p s) j i (-r) / (2*π)) n -
        2*π * ∑ l, rho l * ∑ a ∈ Finset.range (n+1),
          ((∫ t : ℝ, jet (fun s => factor z rho sigma (p s) i l t / (2*π)) a *
            jet (fun s => factorPrime z rho sigma (p s) j l (t-r) / (2*π)) (n-a)) +
          jet (fun s => factor z rho sigma (p s) i l (edgeLo sigma j l+r) / (2*π)) a *
            jet (fun s => lowerJump z rho sigma (p s) j l / (2*π)) (n-a)) := by
  rw [correlation_second_jet_cauchy z hz rho sigma hsigma p hp n i j horder r hr]
  simp_rw [jet_div_const, div_mul_div_comm, integral_div, ← add_div]
  simp only [← Finset.sum_div, ← mul_div_assoc]
  field_simp

/-- The derivative object is identified with the existing full complex Baxter
primitive in the paper normalization, for all species orders away from edges. -/
theorem normalizedPrimitive_second_hasDerivAt
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ)
    (hrL : r ≠ edgeLo sigma i j) (hrR : r ≠ edgeHi sigma i j)
    (hrnegR : -r ≠ edgeHi sigma j i) :
    HasDerivAt (normalizedPrimitive z rho sigma p i j)
      (-secondNumerator z rho sigma (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) i j r / (2*π)) r := by
  have h := (fullPrimitive_second_hasDerivAt z hz rho sigma
    (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) hsigma i j r hrL hrR hrnegR).div_const (2*π)
  convert! h using 1
  funext x
  simp only [realPrimitive_eq_re, normalizedPrimitive]

end FMSA.Paper.ActualBaxterSecondJets

/-- info: 'FMSA.Paper.ActualBaxterSecondJets.first_eq_neg_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSecondJets.first_eq_neg_second

/-- info: 'FMSA.Paper.ActualBaxterSecondJets.second_convolution_jet_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSecondJets.second_convolution_jet_cauchy

/-- info: 'FMSA.Paper.ActualBaxterSecondJets.correlation_second_jet_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSecondJets.correlation_second_jet_cauchy

/-- info: 'FMSA.Paper.ActualBaxterSecondJets.normalized_correlation_second_jet_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSecondJets.normalized_correlation_second_jet_cauchy

/-- info: 'FMSA.Paper.ActualBaxterSecondJets.normalizedPrimitive_second_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSecondJets.normalizedPrimitive_second_hasDerivAt
