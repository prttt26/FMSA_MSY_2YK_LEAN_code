import FMSAPaper.BaxterWeakDerivative
import Mathlib.Analysis.Convolution

/-! Test-function identities from continuous primitives with countably many
exceptional derivative points. All integration and boundary limits are proved. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped ContDiff
namespace FMSA.Paper.WeakDerivativePairing

theorem crossCorr_integrable (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun r => ∫ t : ℝ, f t * g (t-r)) := by
  have h := hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.comp_neg
  convert! h using 1
  funext r
  simp only [convolution_def, ContinuousLinearMap.mul_apply', neg_sub]

theorem weakDerivative_of_continuous (f g : ℝ → ℝ) (s : Set ℝ)
    (hs : s.Countable) (hf : Continuous f)
    (hd : ∀ x ∉ s, HasDerivAt f (g x) x) (hg : Integrable g)
    (phi : ℝ → ℝ) (hp : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi) :
    -(∫ x : ℝ, f x * deriv phi x) = ∫ x : ℝ, g x * phi x := by
  let F := fun x => f x * phi x
  let G := fun x => g x * phi x + f x * deriv phi x
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hp.continuous
  have hi1 : Integrable (fun x => g x * phi x) :=
    hg.mul_bdd hp.continuous.aestronglyMeasurable (Eventually.of_forall hM)
  have hi2 : Integrable (fun x => f x * deriv phi x) :=
    (hf.mul hp.continuous_deriv_one).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hG : Integrable G := hi1.add hi2
  have hFc : HasCompactSupport F := hc.mul_left
  have ht : Tendsto F atTop (𝓝 0) := hFc.is_zero_at_infty.mono_left atTop_le_cocompact
  have hb : Tendsto (fun x : ℝ => F (-x)) atTop (𝓝 0) :=
    (hFc.is_zero_at_infty.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot
  have hFTC (b : ℝ) : (∫ x in -b..b, G x) = F b - F (-b) := by
    apply integral_eq_of_hasDerivAt_off_countable F G hs (hf.mul hp.continuous).continuousOn
    · intro x hx
      exact (hd x hx.2).mul (hp.differentiable (by norm_num) x).hasDerivAt
    · exact hG.intervalIntegrable
  have hlim : Tendsto (fun b : ℝ => ∫ x in -b..b, G x) atTop (𝓝 0) := by
    simpa only [sub_zero, hFTC] using ht.sub hb
  have he : (∫ x : ℝ, G x) = 0 := tendsto_nhds_unique
    (intervalIntegral_tendsto_integral hG tendsto_neg_atTop_atBot tendsto_id) hlim
  rw [integral_add hi1 hi2] at he
  linarith

theorem weakDerivative_on_positive (f g : ℝ → ℝ) (s : Set ℝ)
    (hs : s.Countable) (hf : ContinuousOn f (Ici 0))
    (hd : ∀ x ∈ Ioi (0 : ℝ) \ s, HasDerivAt f (g x) x)
    (hg : IntegrableOn g (Ioi 0)) (phi : ℝ → ℝ)
    (hp : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ Ioi (0 : ℝ)) :
    -(∫ x : ℝ, f x * deriv phi x) = ∫ x : ℝ, g x * phi x := by
  have hp0 (x : ℝ) (hx : x ∉ Ioi (0 : ℝ)) : phi x = 0 := by
    by_contra hn
    exact hx (hsupp (subset_tsupport phi hn))
  have hd0 (x : ℝ) (hx : x ∉ Ioi (0 : ℝ)) : deriv phi x = 0 := by
    by_contra hn
    exact hx (hsupp (support_deriv_subset hn))
  let F := fun x => f x * phi x
  let G := fun x => g x * phi x + f x * deriv phi x
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hp.continuous
  have hi1 : IntegrableOn (fun x => g x * phi x) (Ioi 0) :=
    hg.mul_bdd hp.continuous.aestronglyMeasurable.restrict (Eventually.of_forall hM)
  have hi2 : IntegrableOn (fun x => f x * deriv phi x) (Ioi 0) := by
    have hcompact := hc.deriv.isCompact
    have hloc : ContinuousOn (fun x => f x * deriv phi x) (tsupport (deriv phi)) :=
      (hf.mono (fun x hx => show 0 <= x from
        le_of_lt (show 0 < x from hsupp (tsupport_deriv_subset hx)))).mul
        hp.continuous_deriv_one.continuousOn
    have hglobal : Integrable (fun x => f x * deriv phi x) :=
      (integrableOn_iff_integrable_of_support_subset
        (fun x hx => subset_tsupport (deriv phi) (fun he => hx (by simp [he])))).mp
        (hloc.integrableOn_compact hcompact)
    exact hglobal.integrableOn
  have hFc : HasCompactSupport F := hc.mul_left
  have ht : Tendsto F atTop (𝓝 0) := hFc.is_zero_at_infty.mono_left atTop_le_cocompact
  have hFTC := BaxterIntegrationByParts.integral_Ioi_off_countable F G 0 0 s hs
    (hf.mul hp.continuous.continuousOn)
    (fun x hx => (hd x hx).mul (hp.differentiable (by norm_num) x).hasDerivAt)
    (hi1.add hi2) ht
  have he1 : (∫ x in Ioi (0 : ℝ), g x * phi x) = ∫ x : ℝ, g x * phi x := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact Eventually.of_forall (fun x hx => by rw [hp0 x hx, mul_zero])
  have he2 : (∫ x in Ioi (0 : ℝ), f x * deriv phi x) = ∫ x : ℝ, f x * deriv phi x := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact Eventually.of_forall (fun x hx => by rw [hd0 x hx, mul_zero])
  dsimp only [G, F] at hFTC
  rw [integral_add hi1 hi2, he1, he2, hp0 0 (by simp), mul_zero, sub_zero] at hFTC
  linarith

end FMSA.Paper.WeakDerivativePairing

/-- info: 'FMSA.Paper.WeakDerivativePairing.crossCorr_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.WeakDerivativePairing.crossCorr_integrable

/-- info: 'FMSA.Paper.WeakDerivativePairing.weakDerivative_of_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.WeakDerivativePairing.weakDerivative_of_continuous

/-- info: 'FMSA.Paper.WeakDerivativePairing.weakDerivative_on_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.WeakDerivativePairing.weakDerivative_on_positive
