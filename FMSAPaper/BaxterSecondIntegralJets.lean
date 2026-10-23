import FMSAPaper.BaxterWeakJetBasis
import FMSAPaper.ActualBaxterSecondJets

/-! The second-factor numerator, including its convolution lower-edge term,
has the same finite amplitude coefficients as the reflected primitive and a
fixed integrable spatial dictionary. -/
noncomputable section
open MeasureTheory Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.BaxterSecondIntegralJets
open ExactMSA.MultiTailMixture ExactMSA.BSource ExactMSA.Breakpoint MSAMixture
open FiniteBasis FiniteIntegralJets WeakDerivativePairing BaxterSecondDerivative
open BaxterWeakJetBasis ActualBaxterSecondJets BaxterWeakDerivative
variable {N : ℕ} {T : Type*} [Fintype T]

theorem basisPrime_eq_single_qPrime (z : T → ℝ) (sigma : Fin N → ℝ)
    (b : BasisIndex T) (i j : Fin N) (r : ℝ) :
    basisPrime z sigma b i j r =
      qPrime (fun _ : Fin 1 => basisRate z b) sigma (fun _ => basisA b) (fun _ _ => basisQp b)
        (fun _ _ _ => basisW b) (fun _ _ _ => basisC b) i j r := by
  have he : r-edgeLo sigma i j-sigma i = r-edgeHi sigma i j := by unfold edgeLo edgeHi; ring
  simp only [basisPrime, baxterQ', qPrime, Fin.sum_univ_one, he]

theorem basisPrime_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (b : BasisIndex T) (i j : Fin N) :
    Integrable (basisPrime z sigma b i j) := by
  have h := qPrime_integrable (fun _ : Fin 1 => basisRate z b) (fun _ => basisRate_pos z hz b)
    sigma (fun _ => basisA b) (fun _ _ => basisQp b)
    (fun _ _ _ => basisW b) (fun _ _ _ => basisC b) hsigma i j
  convert! h using 1
  funext r
  exact basisPrime_eq_single_qPrime z sigma b i j r

def secondBasis (z : T → ℝ) (sigma : Fin N → ℝ) (i j : Fin N) : Index T N → ℝ → ℝ
  | .inl b => fun r => -basisPrime z sigma b i j r
  | .inr (.inl b) => fun r => basisPrime z sigma b j i (-r)
  | .inr (.inr (l, b, c)) => fun r =>
      (∫ t : ℝ, basisQ z sigma b i l t * basisPrime z sigma c j l (t-r)) +
        basisQ z sigma b i l (edgeLo sigma j l+r) * basisQ z sigma c j l (edgeLo sigma j l)

def actualSecondNumerator (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ → ℝ :=
  secondNumerator z rho sigma (amplitudeA z rho sigma p.1 p.2)
    (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j

theorem secondBasis_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (k : Index T N) :
    Integrable (secondBasis z sigma i j k) := by
  rcases k with b | (b | ⟨l, b, c⟩)
  · exact (basisPrime_integrable z hz sigma hsigma b i j).neg
  · exact (basisPrime_integrable z hz sigma hsigma b j i).comp_neg
  · exact (crossCorr_integrable _ _ (basisQ_integrable z hz sigma hsigma b i l)
      (basisPrime_integrable z hz sigma hsigma c j l)).add
      (((basisQ_integrable z hz sigma hsigma b i l).comp_add_left (edgeLo sigma j l)).mul_const _)

theorem secondConvolution_eq_bilinear (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j l : Fin N) (r : ℝ) :
    actualSecondConvolution z rho sigma p i j l r =
      bilinear (fun b => bhCoefficient z rho sigma p i l b)
        (fun c => bhCoefficient z rho sigma p j l c)
        (fun b c => secondBasis z sigma i j (.inr (.inr (l,b,c))) r) := by
  unfold actualSecondConvolution secondConvolution
  rw [← q_at_lowerEdge z sigma _ _ _ _ hsigma j l]
  simp_rw [q_eq_basis, qPrime_eq_basis]
  apply integral_add_jump_expansion
  intro b c
  simpa only [sub_eq_add_neg, mul_comm] using
    basisConvolution_integrable z hz sigma hsigma c b j i l (-r)

theorem second_eq_linear (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    actualSecondNumerator z rho sigma p i j r =
      linear (coefficients z rho sigma p i j) (fun k => secondBasis z sigma i j k r) := by
  classical
  change -qPrime z sigma _ _ _ _ i j r + qPrime z sigma _ _ _ _ j i (-r) -
    ∑ l, rho l * actualSecondConvolution z rho sigma p i j l r = _
  simp only [secondConvolution_eq_bilinear z hz rho sigma hsigma]
  simp only [qPrime_eq_basis, linear_index,
    coefficients, secondBasis, bilinear, bhCoefficient]
  simp only [Finset.mul_sum, mul_neg, neg_mul, mul_assoc, Finset.sum_neg_distrib]
  ring

theorem second_test_eq_linear (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (phi : ℝ → ℝ) (r : ℝ) :
    actualSecondNumerator z rho sigma p i j r * phi r =
      linear (coefficients z rho sigma p i j) (fun k => secondBasis z sigma i j k r * phi r) := by
  rw [second_eq_linear z hz rho sigma hsigma p i j r]
  simp only [linear, Finset.sum_mul, mul_assoc]

theorem second_test_integral_contDiffAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (i j : Fin N) (phi : ℝ → ℝ) (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    ContDiffAt ℝ ∞ (fun s => ∫ r : ℝ, actualSecondNumerator z rho sigma (p s) i j r * phi r) 0 := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hphi
  simp_rw [second_test_eq_linear z hz rho sigma hsigma]
  apply integral_linear_contDiffAt
  · intro k
    exact (coefficients_contDiff z rho sigma i j k).contDiffAt.comp 0 hp
  · intro k
    exact (secondBasis_integrable z hz sigma hsigma i j k).mul_bdd
      hphi.aestronglyMeasurable (Eventually.of_forall hM)

theorem second_test_jet_integral (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    jet (fun s => ∫ r : ℝ, actualSecondNumerator z rho sigma (p s) i j r * phi r) n =
      ∫ r : ℝ, jet (fun s => actualSecondNumerator z rho sigma (p s) i j r) n * phi r := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hphi
  have ha (k : Index T N) : ContDiffAt ℝ n (fun s => coefficients z rho sigma (p s) i j k) 0 :=
    ((coefficients_contDiff z rho sigma i j k).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  have hb (k : Index T N) : Integrable (fun r => secondBasis z sigma i j k r * phi r) :=
    (secondBasis_integrable z hz sigma hsigma i j k).mul_bdd
      hphi.aestronglyMeasurable (Eventually.of_forall hM)
  have h := jet_integral_linear (fun s => coefficients z rho sigma (p s) i j)
    (fun k r => secondBasis z sigma i j k r * phi r) n ha hb
  simpa only [← second_test_eq_linear z hz rho sigma hsigma, jet_mul_const] using h

end FMSA.Paper.BaxterSecondIntegralJets

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.basisPrime_eq_single_qPrime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.basisPrime_eq_single_qPrime

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.basisPrime_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.basisPrime_integrable

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.secondBasis_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.secondBasis_integrable

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.secondConvolution_eq_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.secondConvolution_eq_bilinear

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.second_eq_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.second_eq_linear

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.second_test_eq_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.second_test_eq_linear

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.second_test_integral_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.second_test_integral_contDiffAt

/-- info: 'FMSA.Paper.BaxterSecondIntegralJets.second_test_jet_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondIntegralJets.second_test_jet_integral
