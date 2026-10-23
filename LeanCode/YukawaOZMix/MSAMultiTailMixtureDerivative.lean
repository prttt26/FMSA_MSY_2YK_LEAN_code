import LeanCode.YukawaOZMix.MSAMultiTailMixtureRegularity
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitive

/-! Actual spatial derivative of the full-line Baxter primitive on the
ordered positive axis, away from contact. The lower-edge cancellation and
all Lipschitz/integrability premises are discharged internally. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem qCrossCorr_real_hasDerivAt_of_order (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun x => ∫ t : ℝ, q z σ A qp W C i l (t+x) * q z σ A qp W C j l t)
      (∫ t : ℝ, qPrime z σ A qp W C i l (t+r) * q z σ A qp W C j l t) r := by
  obtain ⟨L, hL⟩ := qRight_lipschitz z hz σ A qp W C hσ i l
  let F : ℝ → ℝ → ℝ := fun x t => qRight z σ A qp W C i l (t+x) * q z σ A qp W C j l t
  let F' : ℝ → ℝ := fun t => qPrime z σ A qp W C i l (t+r) * q z σ A qp W C j l t
  let bound : ℝ → ℝ := fun t => (L : ℝ) * |q z σ A qp W C j l t|
  have hm : ∀ᶠ x in 𝓝 r, AEStronglyMeasurable (F x) := by
    apply Eventually.of_forall
    intro x
    exact (qRight_product_integrable z hz σ A qp W C hσ i j l x).aestronglyMeasurable
  have hl : ∀ᵐ t : ℝ, LipschitzOnWith (Real.nnabs (bound t)) (fun x => F x t) univ := by
    apply Eventually.of_forall
    intro t
    have hs : LipschitzWith 1 (fun x : ℝ => x+t) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [Real.dist_eq, add_sub_add_right_eq_sub]
    have hc : LipschitzWith L (fun x => qRight z σ A qp W C i l (x+t)) := by
      simpa only [Function.comp_def, mul_one] using hL.comp hs
    have hp := lipschitz_real_mul_const hc (q z σ A qp W C j l t)
    have he : Real.nnabs (bound t) = Real.nnabs (q z σ A qp W C j l t) * L := by
      ext
      simp [bound, abs_mul, abs_of_nonneg L.coe_nonneg, mul_comm]
    rw [he]
    convert! hp.lipschitzOnWith using 1
    funext x
    simp [F, Function.comp_def, add_comm, mul_comm]
  have hb : Integrable bound := (q_integrable z hz σ A qp W C hσ j l).abs.const_mul _
  have hdiff : ∀ᵐ t : ℝ, HasDerivAt (fun x => F x t) (F' t) r := by
    filter_upwards [volume.ae_ne (edgeLo σ i l-r), volume.ae_ne (edgeHi σ i l-r)] with t htL htR
    have htl : t+r ≠ edgeLo σ i l := by intro h; apply htL; linarith
    have htr : t+r ≠ edgeHi σ i l := by intro h; apply htR; linarith
    have h := (qRight_hasDerivAt_off_edges z σ A qp W C hσ i l (t+r) htl htr).comp r
      ((hasDerivAt_id r).const_add t)
    convert! h.mul_const (q z σ A qp W C j l t) using 1 <;>
      simp [F, F', Function.comp_def, add_comm, id_eq]
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip
    (s := univ) (by simp) hm (qRight_product_integrable z hz σ A qp W C hσ i j l r)
    (convolution_integrable z hz σ A qp W C hσ i j l r).aestronglyMeasurable hl hb hdiff).2
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with x hx
  apply integral_congr_ae
  filter_upwards [] with t
  exact (qRight_product_eq_of_order z σ A qp W C i j l horder x hx t).symm

def orderedPrimitiveReal (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ) : ℝ :=
  q z σ A qp W C i j r - ∑ l, ρ l * ∫ t : ℝ,
    q z σ A qp W C i l (t+r) * q z σ A qp W C j l t

theorem baxterPrimitive_positive_eq_ofReal (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N)
    (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r) :
    baxterPrimitive z ρ σ A qp W C i j r = (orderedPrimitiveReal z ρ σ A qp W C i j r : ℂ) := by
  rw [baxterPrimitive_positive_of_order z ρ σ A qp W C i j horder r hr]
  unfold orderedPrimitiveReal
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [← integral_complex_ofReal]
  push_cast
  rfl

/-- The actual primitive derivative gives the ordered radial DCF on the
positive axis off contact. No BH-root, reciprocity, or derivative premise. -/
theorem orderedPrimitiveReal_hasDerivAt (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    HasDerivAt (orderedPrimitiveReal z ρ σ A qp W C i j)
      (-2*π*r*correlation z ρ σ A qp W C i j r) r := by
  have hrL : r ≠ edgeLo σ i j := by unfold edgeLo; linarith
  have h := (q_hasDerivAt_off_edges z σ A qp W C hσ i j r hrL hrR).sub
    (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      (qCrossCorr_real_hasDerivAt_of_order z hz σ A qp W C hσ i j l horder r hr).const_mul (ρ l)))
  convert! h using 1
  unfold correlation
  field_simp [hr.ne']
  ring

theorem baxterPrimitive_re_hasDerivAt (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    HasDerivAt (fun x => (baxterPrimitive z ρ σ A qp W C i j x).re)
      (-2*π*r*correlation z ρ σ A qp W C i j r) r := by
  apply (orderedPrimitiveReal_hasDerivAt z hz ρ σ A qp W C hσ i j horder r hr hrR).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with x hx
  rw [baxterPrimitive_positive_eq_ofReal z ρ σ A qp W C i j horder x hx]
  rfl

/-- The contact junction is continuous even when its two spatial derivatives
differ. Lower-edge support jumps are excluded by the actual positive order. -/
theorem orderedPrimitiveReal_continuousAt_positive (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) :
    ContinuousAt (orderedPrimitiveReal z ρ σ A qp W C i j) r := by
  obtain ⟨L, hL⟩ := qRight_lipschitz z hz σ A qp W C hσ i j
  have hrL : edgeLo σ i j < r := by unfold edgeLo; linarith
  have hq : ContinuousAt (q z σ A qp W C i j) r := by
    apply hL.continuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hrL] with x hx
    exact (qRight_eq_q z σ A qp W C i j x hx.le).symm
  have hc := (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    (qCrossCorr_real_hasDerivAt_of_order z hz σ A qp W C hσ i j l horder r hr).const_mul (ρ l))).continuousAt
  exact hq.sub hc

theorem baxterPrimitive_re_continuousAt_positive (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) :
    ContinuousAt (fun x => (baxterPrimitive z ρ σ A qp W C i j x).re) r := by
  apply (orderedPrimitiveReal_continuousAt_positive z hz ρ σ A qp W C hσ i j horder r hr).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with x hx
  rw [baxterPrimitive_positive_eq_ofReal z ρ σ A qp W C i j horder x hx]
  rfl

/-- Spatial bridge on the whole positive axis almost everywhere. The
contact exception is null; continuity through that contact was proved above. -/
theorem baxterPrimitive_re_hasDerivAt_ae_positive (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i) :
    ∀ᵐ r : ℝ, 0 < r →
      HasDerivAt (fun x => (baxterPrimitive z ρ σ A qp W C i j x).re)
        (-2*π*r*correlation z ρ σ A qp W C i j r) r := by
  filter_upwards [volume.ae_ne (edgeHi σ i j)] with r hrR hr
  exact baxterPrimitive_re_hasDerivAt z hz ρ σ A qp W C hσ i j horder r hr hrR

end FMSA.ExactMSA.MultiTailMixture
