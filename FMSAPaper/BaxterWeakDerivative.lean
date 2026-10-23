import FMSAPaper.BaxterIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Weak spatial derivative of the actual piecewise Baxter factor. The
lowerValue coefficient is proved to be its Dirac mass against every compactly
supported C1 test function; no atom appears at the continuous upper contact. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.BaxterWeakDerivative
open ExactMSA.MultiTailMixture MSAMixture BaxterIntegrationByParts
variable {N : ℕ} {T : Type*} [Fintype T]

theorem qPrime_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) :
    Integrable (qPrime z sigma A qp W C i j) := by
  have h := (qPrime_complex_weighted_integrable z hz sigma A qp W C hsigma 0 (by simp) i j).re
  simpa only [neg_zero, zero_mul, Complex.exp_zero, mul_one, RCLike.re_to_complex,
    Complex.ofReal_re] using h

theorem q_weak_derivative (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi) :
    -(∫ r : ℝ, q z sigma A qp W C i j r * deriv phi r) =
      (∫ r : ℝ, qPrime z sigma A qp W C i j r * phi r) +
        lowerValue sigma A qp W C i j * phi (edgeLo sigma i j) := by
  let f := fun x => qRight z sigma A qp W C i j x * phi x
  let g := fun x => qPrime z sigma A qp W C i j x * phi x +
    q z sigma A qp W C i j x * deriv phi x
  obtain ⟨L, hL⟩ := qRight_lipschitz z hz sigma A qp W C hsigma i j
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hphi.continuous
  have hint1 : Integrable (fun x => qPrime z sigma A qp W C i j x * phi x) :=
    (qPrime_integrable z hz sigma A qp W C hsigma i j).mul_bdd hphi.continuous.aestronglyMeasurable
      (Eventually.of_forall hM)
  obtain ⟨Md, hMd⟩ := hc.deriv.exists_bound_of_continuous hphi.continuous_deriv_one
  have hint2 : Integrable (fun x => q z sigma A qp W C i j x * deriv phi x) :=
    (q_integrable z hz sigma A qp W C hsigma i j).mul_bdd
      hphi.continuous_deriv_one.aestronglyMeasurable (Eventually.of_forall hMd)
  have hg : Integrable g := hint1.add hint2
  have hf : Tendsto f atTop (𝓝 0) := by
    have ht : Tendsto phi atTop (𝓝 0) := hc.is_zero_at_infty.mono_left atTop_le_cocompact
    simpa only [mul_zero, f] using (qRight_tendsto_zero z hz sigma A qp W C hsigma i j).mul ht
  have hd : ∀ x ∈ Ioi (edgeLo sigma i j) \ {edgeHi sigma i j}, HasDerivAt f (g x) x := by
    intro x hx
    have hlo : edgeLo sigma i j < x := hx.1
    have hhi : x ≠ edgeHi sigma i j := by simpa using hx.2
    have hq := qRight_hasDerivAt_off_edges z sigma A qp W C hsigma i j x hlo.ne' hhi
    have hp := (hphi.differentiable (by norm_num) x).hasDerivAt
    convert! hq.mul hp using 1
    simp only [g, qRight_eq_q z sigma A qp W C i j x hlo.le]
  have hFTC := integral_Ioi_off_countable f g (edgeLo sigma i j) 0 {edgeHi sigma i j}
    (countable_singleton _) (hL.continuous.mul hphi.continuous).continuousOn hd hg.integrableOn hf
  have he : (∫ x in Ioi (edgeLo sigma i j), g x) = ∫ x : ℝ, g x := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [volume.ae_ne (edgeLo sigma i j)] with x hx hn
    have hlt : x < edgeLo sigma i j := lt_of_le_of_ne (not_lt.mp hn) hx
    simp only [g, q, qPrime, if_pos hlt, zero_mul, add_zero]
  rw [he, integral_add hint1 hint2] at hFTC
  simp only [f, zero_sub, qRight_eq_q z sigma A qp W C i j _ le_rfl,
    q_at_lowerEdge z sigma A qp W C hsigma i j] at hFTC
  linarith

end FMSA.Paper.BaxterWeakDerivative

/-- info: 'FMSA.Paper.BaxterWeakDerivative.qPrime_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakDerivative.qPrime_integrable

/-- info: 'FMSA.Paper.BaxterWeakDerivative.q_weak_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakDerivative.q_weak_derivative
