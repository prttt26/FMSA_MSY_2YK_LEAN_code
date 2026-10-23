import FMSAPaper.BaxterNormalization
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRadial

/-! Integration by parts for the actual Baxter factors, retaining the
lower-edge jump rather than treating the piecewise factor as globally smooth. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators

namespace FMSA.Paper.BaxterIntegrationByParts
open ExactMSA.MultiTailMixture MSAMixture

theorem integral_Ioi_off_countable (f g : ℝ → ℝ) (a m : ℝ) (s : Set ℝ)
    (hs : s.Countable) (hc : ContinuousOn f (Ici a))
    (hd : ∀ x ∈ Ioi a \ s, HasDerivAt f (g x) x)
    (hg : IntegrableOn g (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) :
    (∫ x in Ioi a, g x) = m - f a := by
  apply tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a hg tendsto_id)
  apply (hf.sub_const (f a)).congr'
  filter_upwards [Ioi_mem_atTop a] with b hb
  symm
  apply integral_eq_of_hasDerivAt_off_countable_of_le f g hb.le hs
    (hc.mono Icc_subset_Ici_self)
  · intro x hx
    exact hd x ⟨hx.1.1, hx.2⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
    exact hg.mono_set (fun _ hx => hx.1)

theorem cross_integral_translate (f g : ℝ → ℝ) (r : ℝ) :
    (∫ t : ℝ, f (t+r) * g t) = ∫ t : ℝ, f t * g (t-r) := by
  simpa only [add_sub_cancel_right] using
    integral_add_right_eq_self (fun t : ℝ => f t * g (t-r)) r

variable {N : ℕ} {T : Type*} [Fintype T]

theorem qRight_tendsto_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) :
    Tendsto (qRight z sigma A qp W C i j) atTop (𝓝 0) := by
  have ht := tendsto_finset_sum Finset.univ (fun u _ =>
    ((shiftedRealExp_tendsto (z u) (edgeLo sigma i j) (hz u)).const_mul (W u i j)).add
    ((shiftedRealExp_tendsto (z u) (edgeHi sigma i j) (hz u)).const_mul (C u i j)))
  simp only [mul_zero, add_zero, Finset.sum_const_zero] at ht
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (edgeHi sigma i j)] with x hx
  change edgeHi sigma i j < x at hx
  have he : edgeLo sigma i j <= edgeHi sigma i j := by
    unfold edgeLo edgeHi; linarith [hsigma i]
  rw [qRight_eq_q z sigma A qp W C i j x (he.trans hx.le)]
  simp only [q, if_neg (not_lt.mpr (he.trans hx.le)), if_neg (not_le.mpr hx)]

theorem second_convolution_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N) (r : ℝ) :
    Integrable (fun t => q z sigma A qp W C i l (t+r) * qPrime z sigma A qp W C j l t) := by
  have h := (convolution_integrable z hz sigma A qp W C hsigma j i l (-r)).comp_add_right r
  simpa only [add_neg_cancel_right, mul_comm] using h

theorem product_integration_by_parts_of_lower_order
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N)
    (r : ℝ) (hsep : edgeLo sigma i l < edgeLo sigma j l + r) :
    (∫ t : ℝ, qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t) +
      (∫ t : ℝ, q z sigma A qp W C i l (t+r) * qPrime z sigma A qp W C j l t) =
      -q z sigma A qp W C i l (edgeLo sigma j l + r) * lowerValue sigma A qp W C j l := by
  let f := fun t => qRight z sigma A qp W C i l (t+r) * qRight z sigma A qp W C j l t
  let g := fun t => qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t +
    q z sigma A qp W C i l (t+r) * qPrime z sigma A qp W C j l t
  have hfirst := convolution_integrable z hz sigma A qp W C hsigma i j l r
  have hsecond := second_convolution_integrable z hz sigma A qp W C hsigma i j l r
  have hg : Integrable g := hfirst.add hsecond
  obtain ⟨Li, hLi⟩ := qRight_lipschitz z hz sigma A qp W C hsigma i l
  obtain ⟨Lj, hLj⟩ := qRight_lipschitz z hz sigma A qp W C hsigma j l
  have hf : Tendsto f atTop (𝓝 0) := by
    have hi := (qRight_tendsto_zero z hz sigma A qp W C hsigma i l).comp
      (tendsto_atTop_add_const_right atTop r tendsto_id)
    convert! hi.mul (qRight_tendsto_zero z hz sigma A qp W C hsigma j l) using 1 <;>
      simp only [f, mul_zero, Function.comp_def, id_eq]
  have hd : ∀ t ∈ Ioi (edgeLo sigma j l) \ {edgeHi sigma i l - r, edgeHi sigma j l},
      HasDerivAt f (g t) t := by
    intro t ht
    have htl : edgeLo sigma j l < t := ht.1
    have hil : edgeLo sigma i l < t+r := by linarith
    have hiR : t+r ≠ edgeHi sigma i l := by
      intro h
      apply ht.2
      left
      linarith
    have hjR : t ≠ edgeHi sigma j l := by
      intro h
      exact ht.2 (by simp [h])
    have hi := (qRight_hasDerivAt_off_edges z sigma A qp W C hsigma i l (t+r) hil.ne' hiR).comp t
      ((hasDerivAt_id t).add_const r)
    have hj := qRight_hasDerivAt_off_edges z sigma A qp W C hsigma j l t htl.ne' hjR
    convert! hi.mul hj using 1
    simp only [g, Function.comp_def, id_eq, mul_one,
      qRight_eq_q z sigma A qp W C i l (t+r) hil.le,
      qRight_eq_q z sigma A qp W C j l t htl.le]
  have hFTC := integral_Ioi_off_countable f g (edgeLo sigma j l) 0
    {edgeHi sigma i l - r, edgeHi sigma j l} (by simp)
    ((hLi.continuous.comp (continuous_id.add continuous_const)).mul hLj.continuous).continuousOn
    hd hg.integrableOn hf
  have hrestrict : (∫ t in Ioi (edgeLo sigma j l), g t) = ∫ t : ℝ, g t := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [volume.ae_ne (edgeLo sigma j l)] with t ht hn
    have hlt : t < edgeLo sigma j l := lt_of_le_of_ne (not_lt.mp hn) ht
    simp only [g, q, qPrime, if_pos hlt, mul_zero, add_zero]
  rw [hrestrict, integral_add hfirst hsecond] at hFTC
  have hboundary : edgeLo sigma i l <= edgeLo sigma j l+r := hsep.le
  simpa only [f, zero_sub, neg_mul, qRight_eq_q z sigma A qp W C i l _ hboundary,
    qRight_eq_q z sigma A qp W C j l _ le_rfl,
    q_at_lowerEdge z sigma A qp W C hsigma j l] using hFTC

/-- Whole-line integration by parts with both actual lower-edge atoms. The
coincident-edge displacement is excluded, where a pointwise convention would
double-count the jump; the a.e. statement below removes that single point. -/
theorem product_integration_by_parts_with_lower_edges
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N)
    (r : ℝ) (hr : r ≠ edgeLo sigma i l - edgeLo sigma j l) :
    (∫ t : ℝ, qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t) +
      (∫ t : ℝ, q z sigma A qp W C i l (t+r) * qPrime z sigma A qp W C j l t) +
      lowerValue sigma A qp W C i l * q z sigma A qp W C j l (edgeLo sigma i l-r) +
      q z sigma A qp W C i l (edgeLo sigma j l+r) * lowerValue sigma A qp W C j l = 0 := by
  by_cases hsep : edgeLo sigma i l < edgeLo sigma j l+r
  · have h := product_integration_by_parts_of_lower_order z hz sigma A qp W C hsigma i j l r hsep
    have hzero : q z sigma A qp W C j l (edgeLo sigma i l-r) = 0 := by
      rw [q, if_pos (by linarith : edgeLo sigma i l-r < edgeLo sigma j l)]
    rw [hzero, mul_zero]
    linarith
  · have hsep' : edgeLo sigma j l < edgeLo sigma i l+(-r) := by
      have hne : edgeLo sigma i l ≠ edgeLo sigma j l+r := by
        intro he; apply hr; linarith
      have hgt := lt_of_le_of_ne (not_lt.mp hsep) (Ne.symm hne)
      linarith
    have h := product_integration_by_parts_of_lower_order z hz sigma A qp W C hsigma j i l (-r) hsep'
    rw [cross_integral_translate] at h
    have hshift : (∫ t : ℝ, q z sigma A qp W C j l (t+(-r)) * qPrime z sigma A qp W C i l t) =
        ∫ t : ℝ, q z sigma A qp W C j l t * qPrime z sigma A qp W C i l (t+r) := by
      simpa only [sub_neg_eq_add] using
        cross_integral_translate (q z sigma A qp W C j l) (qPrime z sigma A qp W C i l) (-r)
    rw [hshift] at h
    simp only [sub_neg_eq_add, ← sub_eq_add_neg] at h
    have hzero : q z sigma A qp W C i l (edgeLo sigma j l+r) = 0 := by
      rw [q, if_pos (by linarith : edgeLo sigma j l+r < edgeLo sigma i l)]
    rw [hzero, zero_mul]
    have hcomm1 : (∫ t : ℝ, qPrime z sigma A qp W C j l t * q z sigma A qp W C i l (t+r)) =
        ∫ t : ℝ, q z sigma A qp W C i l (t+r) * qPrime z sigma A qp W C j l t := by
      congr 1; funext t; ring
    have hcomm2 : (∫ t : ℝ, q z sigma A qp W C j l t * qPrime z sigma A qp W C i l (t+r)) =
        ∫ t : ℝ, qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t := by
      congr 1; funext t; ring
    rw [hcomm1, hcomm2] at h
    nlinarith

theorem product_integration_by_parts_ae
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N) :
    ∀ᵐ r : ℝ,
      (∫ t : ℝ, qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t) +
        (∫ t : ℝ, q z sigma A qp W C i l (t+r) * qPrime z sigma A qp W C j l t) +
        lowerValue sigma A qp W C i l * q z sigma A qp W C j l (edgeLo sigma i l-r) +
        q z sigma A qp W C i l (edgeLo sigma j l+r) * lowerValue sigma A qp W C j l = 0 := by
  filter_upwards [volume.ae_ne (edgeLo sigma i l - edgeLo sigma j l)] with r hr
  exact product_integration_by_parts_with_lower_edges z hz sigma A qp W C hsigma i j l r hr

end FMSA.Paper.BaxterIntegrationByParts

/-- info: 'FMSA.Paper.BaxterIntegrationByParts.integral_Ioi_off_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterIntegrationByParts.integral_Ioi_off_countable

/-- info: 'FMSA.Paper.BaxterIntegrationByParts.cross_integral_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterIntegrationByParts.cross_integral_translate

/-- info: 'FMSA.Paper.BaxterIntegrationByParts.qRight_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterIntegrationByParts.qRight_tendsto_zero

/-- info: 'FMSA.Paper.BaxterIntegrationByParts.second_convolution_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterIntegrationByParts.second_convolution_integrable

/-- info: 'FMSA.Paper.BaxterIntegrationByParts.product_integration_by_parts_of_lower_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterIntegrationByParts.product_integration_by_parts_of_lower_order

/-- info: 'FMSA.Paper.BaxterIntegrationByParts.product_integration_by_parts_with_lower_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterIntegrationByParts.product_integration_by_parts_with_lower_edges

/-- info: 'FMSA.Paper.BaxterIntegrationByParts.product_integration_by_parts_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterIntegrationByParts.product_integration_by_parts_ae
