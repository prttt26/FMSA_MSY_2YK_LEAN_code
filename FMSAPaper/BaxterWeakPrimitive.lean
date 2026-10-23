import FMSAPaper.WeakDerivativePairing
import FMSAPaper.BaxterSecondDerivative
import LeanCode.YukawaOZMix.MSAMultiTailMixtureTangentReciprocity

/-! Whole-line weak identities for the full reflected Baxter primitive.
The two linear lower-edge atoms and the second-factor convolution atom are
retained for arbitrary amplitudes and either species ordering. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.BaxterWeakPrimitive
open ExactMSA.MultiTailMixture MSAMixture BaxterSecondDerivative BaxterWeakDerivative
open WeakDerivativePairing
variable {N : ℕ} {T : Type*} [Fintype T]

theorem crossCorr_continuous (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N) :
    Continuous (fun r => ∫ t : ℝ, q z sigma A qp W C i l t * q z sigma A qp W C j l (t-r)) := by
  classical
  simp only [realQCrossCorr_eq_basis z hz sigma A qp W C hsigma]
  exact continuous_finsetSum _ (fun b _ => continuous_finsetSum _ (fun c _ =>
    continuous_const.mul (basisQQ_continuous z hz sigma hsigma b c i j l)))

theorem secondConvolution_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N) :
    Integrable (secondConvolution z sigma A qp W C i j l) := by
  exact (crossCorr_integrable _ _ (q_integrable z hz sigma A qp W C hsigma i l)
    (qPrime_integrable z hz sigma A qp W C hsigma j l)).add
    (((q_integrable z hz sigma A qp W C hsigma i l).comp_add_left
      (edgeLo sigma j l)).mul_const (lowerValue sigma A qp W C j l))

theorem crossCorr_weak_derivative (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N)
    (phi : ℝ → ℝ) (hp : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi) :
    (∫ r : ℝ, (∫ t : ℝ, q z sigma A qp W C i l t * q z sigma A qp W C j l (t-r)) * deriv phi r) =
      ∫ r : ℝ, secondConvolution z sigma A qp W C i j l r * phi r := by
  have h := weakDerivative_of_continuous _ (fun r => -secondConvolution z sigma A qp W C i j l r)
    {edgeLo sigma i l-edgeLo sigma j l} (countable_singleton _)
    (crossCorr_continuous z hz sigma A qp W C hsigma i j l)
    (fun r hr => crossCorr_second_hasDerivAt z hz sigma A qp W C hsigma i j l r
      (by simpa using hr))
    (secondConvolution_integrable z hz sigma A qp W C hsigma i j l).neg phi hp hc
  simpa only [neg_mul, integral_neg, neg_inj] using h

theorem reflected_q_weak_derivative (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N)
    (phi : ℝ → ℝ) (hp : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi) :
    (∫ r : ℝ, q z sigma A qp W C i j (-r) * deriv phi r) =
      (∫ r : ℝ, qPrime z sigma A qp W C i j (-r) * phi r) +
        lowerValue sigma A qp W C i j * phi (-edgeLo sigma i j) := by
  have h := q_weak_derivative z hz sigma A qp W C hsigma i j (fun r => phi (-r))
    (by fun_prop) (hc.comp_homeomorph (Homeomorph.neg ℝ))
  have hd (r : ℝ) : deriv (fun x => phi (-x)) r = -deriv phi (-r) := by
    have h := ((hp.differentiable (by norm_num) (-r)).hasDerivAt).comp r (hasDerivAt_neg r)
    convert! h.deriv using 1 <;> simp only [Function.comp_def, mul_neg_one]
  simp only [hd, mul_neg, integral_neg, neg_neg] at h
  have hleft := integral_neg_eq_self (fun r : ℝ => q z sigma A qp W C i j r * deriv phi (-r)) volume
  have hright := integral_neg_eq_self (fun r : ℝ => qPrime z sigma A qp W C i j r * phi (-r)) volume
  simp only [neg_neg] at hleft hright
  rw [hleft, hright]
  exact h

theorem fullPrimitive_weak_derivative (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N)
    (phi : ℝ → ℝ) (hp : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi) :
    (∫ r : ℝ, realPrimitive z rho sigma A qp W C i j r * deriv phi r) =
      (∫ r : ℝ, secondNumerator z rho sigma A qp W C i j r * phi r) -
        lowerValue sigma A qp W C i j * phi (edgeLo sigma i j) +
        lowerValue sigma A qp W C j i * phi (-edgeLo sigma j i) := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hp.continuous
  obtain ⟨Md, hMd⟩ := hc.deriv.exists_bound_of_continuous hp.continuous_deriv_one
  have ht (f : ℝ → ℝ) (hf : Integrable f) : Integrable (fun r => f r * phi r) :=
    hf.mul_bdd hp.continuous.aestronglyMeasurable (Eventually.of_forall hM)
  have hd (f : ℝ → ℝ) (hf : Integrable f) : Integrable (fun r => f r * deriv phi r) :=
    hf.mul_bdd hp.continuous_deriv_one.aestronglyMeasurable (Eventually.of_forall hMd)
  have hqi := hd _ (q_integrable z hz sigma A qp W C hsigma i j)
  have hqj := hd _ (q_integrable z hz sigma A qp W C hsigma j i).comp_neg
  have hpi := ht _ (qPrime_integrable z hz sigma A qp W C hsigma i j)
  have hpj := ht _ (qPrime_integrable z hz sigma A qp W C hsigma j i).comp_neg
  have hcorr (l : Fin N) := hd _ (crossCorr_integrable _ _
    (q_integrable z hz sigma A qp W C hsigma i l)
    (q_integrable z hz sigma A qp W C hsigma j l))
  have hsec (l : Fin N) := ht _ (secondConvolution_integrable z hz sigma A qp W C hsigma i j l)
  have heP : (∫ r : ℝ, realPrimitive z rho sigma A qp W C i j r * deriv phi r) =
      (∫ r : ℝ, q z sigma A qp W C i j r * deriv phi r) +
      (∫ r : ℝ, q z sigma A qp W C j i (-r) * deriv phi r) -
      ∑ l, rho l * ∫ r : ℝ,
        (∫ t : ℝ, q z sigma A qp W C i l t * q z sigma A qp W C j l (t-r)) * deriv phi r := by
    simp only [realPrimitive, sub_mul, add_mul, Finset.sum_mul, mul_assoc]
    rw [integral_sub]
    · rw [integral_add hqi hqj, integral_finsetSum]
      · simp only [integral_const_mul]
      · intro l _
        exact (hcorr l).const_mul (rho l)
    · exact hqi.add hqj
    · exact integrable_finsetSum Finset.univ (fun l _ => (hcorr l).const_mul (rho l))
  have heS : (∫ r : ℝ, secondNumerator z rho sigma A qp W C i j r * phi r) =
      -(∫ r : ℝ, qPrime z sigma A qp W C i j r * phi r) +
      (∫ r : ℝ, qPrime z sigma A qp W C j i (-r) * phi r) -
      ∑ l, rho l * ∫ r : ℝ, secondConvolution z sigma A qp W C i j l r * phi r := by
    simp only [secondNumerator, sub_mul, add_mul, Finset.sum_mul, mul_assoc, neg_mul]
    rw [integral_sub]
    · rw [integral_add, integral_finsetSum]
      · simp only [integral_neg, integral_const_mul]
      · intro l _
        exact (hsec l).const_mul (rho l)
      · exact hpi.neg
      · exact hpj
    · exact hpi.neg.add hpj
    · exact integrable_finsetSum Finset.univ (fun l _ => (hsec l).const_mul (rho l))
  rw [heP, heS]
  simp_rw [crossCorr_weak_derivative z hz sigma A qp W C hsigma i j _ phi hp hc]
  have hi := q_weak_derivative z hz sigma A qp W C hsigma i j phi hp hc
  have hj := reflected_q_weak_derivative z hz sigma A qp W C hsigma j i phi hp hc
  linarith

end FMSA.Paper.BaxterWeakPrimitive

/-- info: 'FMSA.Paper.BaxterWeakPrimitive.crossCorr_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakPrimitive.crossCorr_continuous

/-- info: 'FMSA.Paper.BaxterWeakPrimitive.secondConvolution_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakPrimitive.secondConvolution_integrable

/-- info: 'FMSA.Paper.BaxterWeakPrimitive.crossCorr_weak_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakPrimitive.crossCorr_weak_derivative

/-- info: 'FMSA.Paper.BaxterWeakPrimitive.reflected_q_weak_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakPrimitive.reflected_q_weak_derivative

/-- info: 'FMSA.Paper.BaxterWeakPrimitive.fullPrimitive_weak_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakPrimitive.fullPrimitive_weak_derivative
