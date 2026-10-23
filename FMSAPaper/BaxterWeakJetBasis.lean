import FMSAPaper.FiniteIntegralJets
import FMSAPaper.BaxterWeakPrimitive
import FMSAPaper.ActualBaxterJets

/-! One fixed integrable dictionary for the full actual reflected primitive.
Its scalar coefficients contain every amplitude dependence, including the
quadratic cross-correlation. This permits exact integration of coupling jets. -/
noncomputable section
open MeasureTheory Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.BaxterWeakJetBasis
open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture
open FiniteBasis FiniteIntegralJets WeakDerivativePairing BaxterSecondDerivative
variable {N : ℕ} {T : Type*} [Fintype T]

abbrev Index (T : Type*) (N : ℕ) :=
  BasisIndex T ⊕ (BasisIndex T ⊕ (Fin N × (BasisIndex T × BasisIndex T)))

def coefficients (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : Index T N → ℝ
  | .inl b => bhCoefficient z rho sigma p i j b
  | .inr (.inl b) => bhCoefficient z rho sigma p j i b
  | .inr (.inr (l, b, c)) =>
      -rho l * bhCoefficient z rho sigma p i l b * bhCoefficient z rho sigma p j l c

def primitiveBasis (z : T → ℝ) (sigma : Fin N → ℝ) (i j : Fin N) : Index T N → ℝ → ℝ
  | .inl b => basisQ z sigma b i j
  | .inr (.inl b) => fun r => basisQ z sigma b j i (-r)
  | .inr (.inr (l, b, c)) => basisQQ z sigma b c i j l

def actualPrimitive (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ → ℝ :=
  realPrimitive z rho sigma (amplitudeA z rho sigma p.1 p.2)
    (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j

theorem linear_index (a b : Index T N → ℝ) :
    linear a b = (∑ k : BasisIndex T, a (.inl k) * b (.inl k)) +
      ((∑ k : BasisIndex T, a (.inr (.inl k)) * b (.inr (.inl k))) +
      ∑ l : Fin N, ∑ k : BasisIndex T, ∑ m : BasisIndex T,
        a (.inr (.inr (l,k,m))) * b (.inr (.inr (l,k,m)))) := by
  unfold linear
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Fintype.sum_prod_type]

theorem coefficients_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (k : Index T N) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N => coefficients z rho sigma p i j k) := by
  rcases k with b | (b | ⟨l, b, c⟩)
  · exact bhCoefficient_contDiff z rho sigma i j b
  · exact bhCoefficient_contDiff z rho sigma j i b
  · exact (contDiff_const.mul (bhCoefficient_contDiff z rho sigma i l b)).mul
      (bhCoefficient_contDiff z rho sigma j l c)

theorem primitiveBasis_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (k : Index T N) :
    Integrable (primitiveBasis z sigma i j k) := by
  rcases k with b | (b | ⟨l, b, c⟩)
  · exact basisQ_integrable z hz sigma hsigma b i j
  · exact (basisQ_integrable z hz sigma hsigma b j i).comp_neg
  · exact crossCorr_integrable _ _ (basisQ_integrable z hz sigma hsigma b i l)
      (basisQ_integrable z hz sigma hsigma c j l)

theorem primitive_eq_linear (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    actualPrimitive z rho sigma p i j r =
      linear (coefficients z rho sigma p i j) (fun k => primitiveBasis z sigma i j k r) := by
  classical
  rw [actualPrimitive, realPrimitive_eq_re,
    baxterPrimitive_eq_basis z hz rho sigma hsigma p i j r, Complex.ofReal_re]
  simp only [primitiveBasisReal, linear_index, coefficients, primitiveBasis]
  simp only [Finset.mul_sum, neg_mul, mul_assoc, Finset.sum_neg_distrib]
  ring

theorem primitive_test_eq_linear (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (phi : ℝ → ℝ) (r : ℝ) :
    actualPrimitive z rho sigma p i j r * phi r =
      linear (coefficients z rho sigma p i j) (fun k => primitiveBasis z sigma i j k r * phi r) := by
  rw [primitive_eq_linear z hz rho sigma hsigma p i j r]
  simp only [linear, Finset.sum_mul, mul_assoc]

theorem primitive_test_integral_contDiffAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (i j : Fin N) (phi : ℝ → ℝ) (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    ContDiffAt ℝ ∞ (fun s => ∫ r : ℝ, actualPrimitive z rho sigma (p s) i j r * phi r) 0 := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hphi
  simp_rw [primitive_test_eq_linear z hz rho sigma hsigma]
  apply integral_linear_contDiffAt
  · intro k
    exact (coefficients_contDiff z rho sigma i j k).contDiffAt.comp 0 hp
  · intro k
    exact (primitiveBasis_integrable z hz sigma hsigma i j k).mul_bdd
      hphi.aestronglyMeasurable (Eventually.of_forall hM)

theorem primitive_test_jet_integral (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    jet (fun s => ∫ r : ℝ, actualPrimitive z rho sigma (p s) i j r * phi r) n =
      ∫ r : ℝ, jet (fun s => actualPrimitive z rho sigma (p s) i j r) n * phi r := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hphi
  have ha (k : Index T N) : ContDiffAt ℝ n (fun s => coefficients z rho sigma (p s) i j k) 0 :=
    ((coefficients_contDiff z rho sigma i j k).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  have hb (k : Index T N) : Integrable (fun r => primitiveBasis z sigma i j k r * phi r) :=
    (primitiveBasis_integrable z hz sigma hsigma i j k).mul_bdd
      hphi.aestronglyMeasurable (Eventually.of_forall hM)
  have h := jet_integral_linear (fun s => coefficients z rho sigma (p s) i j)
    (fun k r => primitiveBasis z sigma i j k r * phi r) n ha hb
  simpa only [← primitive_test_eq_linear z hz rho sigma hsigma, jet_mul_const] using h

end FMSA.Paper.BaxterWeakJetBasis

/-- info: 'FMSA.Paper.BaxterWeakJetBasis.linear_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJetBasis.linear_index

/-- info: 'FMSA.Paper.BaxterWeakJetBasis.coefficients_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJetBasis.coefficients_contDiff

/-- info: 'FMSA.Paper.BaxterWeakJetBasis.primitiveBasis_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJetBasis.primitiveBasis_integrable

/-- info: 'FMSA.Paper.BaxterWeakJetBasis.primitive_eq_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJetBasis.primitive_eq_linear

/-- info: 'FMSA.Paper.BaxterWeakJetBasis.primitive_test_eq_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJetBasis.primitive_test_eq_linear

/-- info: 'FMSA.Paper.BaxterWeakJetBasis.primitive_test_integral_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJetBasis.primitive_test_integral_contDiffAt

/-- info: 'FMSA.Paper.BaxterWeakJetBasis.primitive_test_jet_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJetBasis.primitive_test_jet_integral
