import FMSAPaper.BaxterIntegrationByParts

/-! The full reflected Baxter primitive differentiated with respect to the
second convolution factor. The lower-edge contribution is explicit. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators
namespace FMSA.Paper.BaxterSecondDerivative
open ExactMSA.MultiTailMixture MSAMixture BaxterIntegrationByParts
variable {N : ℕ} {T : Type*} [Fintype T]

theorem crossCorr_hasDerivAt_of_lower_order (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N) (r : ℝ)
    (hsep : edgeLo sigma i l < edgeLo sigma j l + r) :
    HasDerivAt (fun x => ∫ t : ℝ, q z sigma A qp W C i l (t+x) * q z sigma A qp W C j l t)
      (∫ t : ℝ, qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t) r := by
  obtain ⟨L, hL⟩ := qRight_lipschitz z hz sigma A qp W C hsigma i l
  let F : ℝ → ℝ → ℝ := fun x t => qRight z sigma A qp W C i l (t+x) * q z sigma A qp W C j l t
  let F' : ℝ → ℝ := fun t => qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t
  let bound : ℝ → ℝ := fun t => (L : ℝ) * |q z sigma A qp W C j l t|
  have hm : ∀ᶠ x in 𝓝 r, AEStronglyMeasurable (F x) := by
    apply Eventually.of_forall
    intro x
    exact (qRight_product_integrable z hz sigma A qp W C hsigma i j l x).aestronglyMeasurable
  have hl : ∀ᵐ t : ℝ, LipschitzOnWith (Real.nnabs (bound t)) (fun x => F x t) univ := by
    apply Eventually.of_forall
    intro t
    have hs : LipschitzWith 1 (fun x : ℝ => x+t) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [Real.dist_eq, add_sub_add_right_eq_sub]
    have hc : LipschitzWith L (fun x => qRight z sigma A qp W C i l (x+t)) := by
      simpa only [Function.comp_def, mul_one] using hL.comp hs
    have hp := lipschitz_real_mul_const hc (q z sigma A qp W C j l t)
    have he : Real.nnabs (bound t) = Real.nnabs (q z sigma A qp W C j l t) * L := by
      ext
      simp [bound, abs_mul, abs_of_nonneg L.coe_nonneg, mul_comm]
    rw [he]
    convert! hp.lipschitzOnWith using 1
    funext x
    simp [F, Function.comp_def, add_comm, mul_comm]
  have hb : Integrable bound := (q_integrable z hz sigma A qp W C hsigma j l).abs.const_mul _
  have hdiff : ∀ᵐ t : ℝ, HasDerivAt (fun x => F x t) (F' t) r := by
    filter_upwards [volume.ae_ne (edgeLo sigma i l-r), volume.ae_ne (edgeHi sigma i l-r)] with t htL htR
    have htl : t+r ≠ edgeLo sigma i l := by intro h; apply htL; linarith
    have htr : t+r ≠ edgeHi sigma i l := by intro h; apply htR; linarith
    have h := (qRight_hasDerivAt_off_edges z sigma A qp W C hsigma i l (t+r) htl htr).comp r
      ((hasDerivAt_id r).const_add t)
    convert! h.mul_const (q z sigma A qp W C j l t) using 1 <;>
      simp [F, F', Function.comp_def, add_comm, id_eq]
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip
    (s := univ) (by simp) hm (qRight_product_integrable z hz sigma A qp W C hsigma i j l r)
    (convolution_integrable z hz sigma A qp W C hsigma i j l r).aestronglyMeasurable hl hb hdiff).2
  apply h.congr_of_eventuallyEq
  have hr : edgeLo sigma i l - edgeLo sigma j l < r := by linarith
  filter_upwards [eventually_gt_nhds hr] with x hx
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [F]
  by_cases ht : t < edgeLo sigma j l
  · simp only [q, if_pos ht, mul_zero]
  · rw [qRight_eq_q]
    have ht' := not_lt.mp ht
    linarith

def secondConvolution (z : T → ℝ) (sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N) (i j l : Fin N) (r : ℝ) : ℝ :=
  (∫ t : ℝ, q z sigma A qp W C i l t * qPrime z sigma A qp W C j l (t-r)) +
    q z sigma A qp W C i l (edgeLo sigma j l+r) * lowerValue sigma A qp W C j l

/-- The derivative on the second factor carries its actual Dirac contribution. -/
theorem crossCorr_second_hasDerivAt
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j l : Fin N)
    (r : ℝ) (hr : r ≠ edgeLo sigma i l-edgeLo sigma j l) :
    HasDerivAt (fun x => ∫ t : ℝ, q z sigma A qp W C i l t * q z sigma A qp W C j l (t-x))
      (-secondConvolution z sigma A qp W C i j l r) r := by
  by_cases hsep : edgeLo sigma i l < edgeLo sigma j l+r
  · have hd := crossCorr_hasDerivAt_of_lower_order z hz sigma A qp W C hsigma i j l r hsep
    have he : (fun x => ∫ t : ℝ, q z sigma A qp W C i l (t+x) * q z sigma A qp W C j l t) =
        (fun x => ∫ t : ℝ, q z sigma A qp W C i l t * q z sigma A qp W C j l (t-x)) := by
      funext x
      exact cross_integral_translate _ _ x
    rw [he] at hd
    have hc : (∫ t : ℝ, qPrime z sigma A qp W C i l (t+r) * q z sigma A qp W C j l t) =
        -secondConvolution z sigma A qp W C i j l r := by
      dsimp only [secondConvolution]
      rw [← cross_integral_translate]
      have hp' := product_integration_by_parts_of_lower_order z hz sigma A qp W C hsigma i j l r hsep
      linarith
    rwa [hc] at hd
  · have hsep' : edgeLo sigma j l < edgeLo sigma i l+(-r) := by
      have hne : edgeLo sigma i l ≠ edgeLo sigma j l+r := by intro he; apply hr; linarith
      have hgt := lt_of_le_of_ne (not_lt.mp hsep) (Ne.symm hne)
      linarith
    have hd := crossCorr_hasDerivAt_of_lower_order z hz sigma A qp W C hsigma j i l (-r) hsep'
    have hn := hd.comp r (hasDerivAt_neg r)
    have hzero : q z sigma A qp W C i l (edgeLo sigma j l+r) = 0 := by
      rw [q, if_pos (by linarith : edgeLo sigma j l+r < edgeLo sigma i l)]
    convert! hn using 1
    · funext x
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [Function.comp_def, ← sub_eq_add_neg, mul_comm]
    · dsimp only [secondConvolution]
      rw [hzero, zero_mul, add_zero]
      simp only [mul_neg_one, ← sub_eq_add_neg]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      ring

def realPrimitive (z : T → ℝ) (rho sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  q z sigma A qp W C i j r + q z sigma A qp W C j i (-r) -
    ∑ l, rho l * ∫ t : ℝ, q z sigma A qp W C i l t * q z sigma A qp W C j l (t-r)

def secondNumerator (z : T → ℝ) (rho sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  -qPrime z sigma A qp W C i j r + qPrime z sigma A qp W C j i (-r) -
    ∑ l, rho l * secondConvolution z sigma A qp W C i j l r

theorem realPrimitive_eq_re (z : T → ℝ) (rho sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N) (i j : Fin N) (r : ℝ) :
    realPrimitive z rho sigma A qp W C i j r =
      (baxterPrimitive z rho sigma A qp W C i j r).re := by
  have h : baxterPrimitive z rho sigma A qp W C i j r =
      (realPrimitive z rho sigma A qp W C i j r : ℂ) := by
    simp only [baxterPrimitive, qCrossCorr, realPrimitive, ← Complex.ofReal_mul,
      integral_complex_ofReal, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_sum]
  rw [h, Complex.ofReal_re]

theorem fullPrimitive_second_hasDerivAt
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (r : ℝ)
    (hrL : r ≠ edgeLo sigma i j) (hrR : r ≠ edgeHi sigma i j)
    (hrnegR : -r ≠ edgeHi sigma j i) :
    HasDerivAt (realPrimitive z rho sigma A qp W C i j)
      (-secondNumerator z rho sigma A qp W C i j r) r := by
  have hnL : -r ≠ edgeLo sigma j i := by
    intro he; apply hrL; unfold edgeLo at *; linarith
  have hi := q_hasDerivAt_off_edges z sigma A qp W C hsigma i j r hrL hrR
  have hj := (q_hasDerivAt_off_edges z sigma A qp W C hsigma j i (-r) hnL hrnegR).comp r
    (hasDerivAt_neg r)
  have hc (l : Fin N) := crossCorr_second_hasDerivAt z hz sigma A qp W C hsigma i j l r
    (by intro he; apply hrL; unfold edgeLo at *; linarith)
  have h := (hi.add hj).sub (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (hc l).const_mul (rho l)))
  convert! h using 1
  dsimp only [secondNumerator]
  simp only [mul_neg_one, mul_neg, Finset.sum_neg_distrib]
  ring

end FMSA.Paper.BaxterSecondDerivative

/-- info: 'FMSA.Paper.BaxterSecondDerivative.crossCorr_hasDerivAt_of_lower_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondDerivative.crossCorr_hasDerivAt_of_lower_order

/-- info: 'FMSA.Paper.BaxterSecondDerivative.crossCorr_second_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondDerivative.crossCorr_second_hasDerivAt

/-- info: 'FMSA.Paper.BaxterSecondDerivative.realPrimitive_eq_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondDerivative.realPrimitive_eq_re

/-- info: 'FMSA.Paper.BaxterSecondDerivative.fullPrimitive_second_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSecondDerivative.fullPrimitive_second_hasDerivAt
