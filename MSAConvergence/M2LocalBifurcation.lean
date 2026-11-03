import MSAConvergence.M2ContourCurvature
import MSAConvergence.LocalMinimumLevels

/-! Actual zero/one/two coupling zeros of the honest M2 zero mode on one
joint original BH root germ. No global root count or first loss is claimed. -/
noncomputable section
open Set Real Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.M2LocalBifurcation
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2TangencySystem
open FMSA.Convergence.M2ZeroMode FMSA.Convergence.M2JointZeroContour
open FMSA.Convergence.M2ContourCurvature FMSA.Convergence.LocalMinimumLevels
abbrev E := Fin 4 → ℝ
abbrev T := Fin 10 → ℝ
abbrev Params := ℝ × ℝ

/-- An exact local classification of zero-mode zeros and signs ON P.
Positive F0 is not asserted full canonicity or stability. -/
def BifurcationData (y : T) (P : Params → E) (δ ε : ℝ) : Prop :=
  0 < δ ∧ 0 < ε ∧
  (∀ t ∈ Ioo (y 4-δ) (y 4+δ), zeroMode (P (t,y 5)) = 0 ↔ t = y 4) ∧
  (∀ t ∈ Ioo (y 4-δ) (y 4+δ), t ≠ y 4 → 0 < zeroMode (P (t,y 5))) ∧
  (∀ w, |w-y 5| < ε → w < 0 ∧
    (∀ t ∈ Ioo (y 4-δ) (y 4+δ), 0 < t ∧
      IsRoot z rho sigma (t • strength w) (point (P (t,w))).1 (point (P (t,w))).2) ∧
    (w < y 5 → ∀ t ∈ Ioo (y 4-δ) (y 4+δ), 0 < zeroMode (P (t,w))) ∧
    (y 5 < w → ∃ l r : ℝ, l ∈ Ioo (y 4-δ) (y 4) ∧ r ∈ Ioo (y 4) (y 4+δ) ∧
      zeroMode (P (l,w)) = 0 ∧ zeroMode (P (r,w)) = 0 ∧
      (∀ t ∈ Ioo (y 4-δ) (y 4+δ), zeroMode (P (t,w)) = 0 ↔ t = l ∨ t = r) ∧
      (∀ t ∈ Ioo l r, zeroMode (P (t,w)) < 0) ∧
      (∀ t ∈ Ioo (y 4-δ) (y 4+δ), t < l ∨ r < t → 0 < zeroMode (P (t,w)))))

/-- The actual contour and true positive curvature construct the whole
local zero-mode picture, with all neighbourhood/root hypotheses discharged. -/
theorem contour_data_has_local_bifurcation (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (P : Params → E) (ψ : ℝ → ℝ) (kappa d : ℝ)
    (hC : ContourData y P ψ) (hD : CurvatureData y P ψ kappa d) :
    ∃ δ ε : ℝ, BifurcationData y P δ ε := by
  obtain ⟨_hP0,_hPa,hPR,hψ0,hψa,hψv,_hmin,hsign,_hcurve⟩ := hC
  obtain ⟨_hk,_hdlo,_hd,_hsecond,_hweight,_hcomplex,_heq,hψ2,hbound,_hq⟩ := hD
  have hkψ : 0 < -kappa/d := by linarith
  obtain ⟨hbpos,hwneg⟩ := M2TangencyData.parameter_signs y ⟨fun i => (hx i).1,fun i => (hx i).2⟩
  have hB : ∀ᶠ u in 𝓝 (y 4,y 5), 0 < u.1 :=
    (continuousAt_fst : ContinuousAt (fun u : Params => u.1) (y 4,y 5)).eventually (Ioi_mem_nhds hbpos)
  have hW : ∀ᶠ u in 𝓝 (y 4,y 5), u.2 < 0 :=
    (continuousAt_snd : ContinuousAt (fun u : Params => u.2) (y 4,y 5)).eventually (Iio_mem_nhds hwneg)
  have hgood : ∀ᶠ u in 𝓝 (y 4,y 5), 0 < u.1 ∧ u.2 < 0 ∧
      IsRoot z rho sigma (u.1 • strength u.2) (point (P u)).1 (point (P u)).2 ∧
      (0 < zeroMode (P u) ↔ u.2 < ψ u.1) ∧
      (zeroMode (P u) < 0 ↔ ψ u.1 < u.2) ∧
      (zeroMode (P u) = 0 ↔ u.2 = ψ u.1) := by
    filter_upwards [hB,hW,hPR,hsign] with u hbu hwu hru hsu
    exact ⟨hbu,hwu,hru,hsu⟩
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  obtain ⟨δ,ε,hdR,heR,hpicture⟩ := local_level_picture ψ (y 4) (-kappa/d) R hψa hψv hψ2 hkψ hR
  obtain ⟨hd,he,hbase,_hbelow,hcritical,habove⟩ := hpicture
  have hp (t w : ℝ) (ht : t ∈ Ioo (y 4-δ) (y 4+δ)) (hw : |w-y 5| < ε) :
      0 < t ∧ w < 0 ∧ IsRoot z rho sigma (t • strength w) (point (P (t,w))).1 (point (P (t,w))).2 ∧
      (0 < zeroMode (P (t,w)) ↔ w < ψ t) ∧
      (zeroMode (P (t,w)) < 0 ↔ ψ t < w) ∧
      (zeroMode (P (t,w)) = 0 ↔ w = ψ t) := by
    apply @hball (t,w)
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    refine max_lt ?_ (hw.trans heR)
    have hh : |t-y 4| < δ := abs_lt.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    exact hh.trans hdR
  have hbI : y 4 ∈ Ioo (y 4-δ) (y 4+δ) := ⟨by linarith,by linarith⟩
  have hw0 : |y 5-y 5| < ε := by rw [sub_self,abs_zero]; exact he
  have hcrit (t : ℝ) (ht : t ∈ Ioo (y 4-δ) (y 4+δ)) : ψ t = y 5 ↔ t = y 4 := by
    simpa only [hψ0] using hcritical t ht
  refine ⟨δ,ε,hd,he,?_,?_,?_⟩
  · intro t ht
    exact (hp t (y 5) ht hw0).2.2.2.2.2.trans
      ((eq_comm : y 5 = ψ t ↔ ψ t = y 5).trans (hcrit t ht))
  · intro t ht hne
    have hb : y 5 ≤ ψ t := by simpa only [hψ0] using hbase t ht
    have hlt : y 5 < ψ t := by
      by_contra hn
      have heq : ψ t = y 5 := le_antisymm (le_of_not_gt hn) hb
      exact hne ((hcrit t ht).mp heq)
    exact (hp t (y 5) ht hw0).2.2.2.1.mpr hlt
  · intro w hw
    refine ⟨(hp (y 4) w hbI hw).2.1,?_,?_,?_⟩
    · intro t ht
      exact ⟨(hp t w ht hw).1,(hp t w ht hw).2.2.1⟩
    · intro hwlo t ht
      have hb : y 5 ≤ ψ t := by simpa only [hψ0] using hbase t ht
      exact (hp t w ht hw).2.2.2.1.mpr (lt_of_lt_of_le hwlo hb)
    · intro hwlo
      have hwψ : ψ (y 4) < w := by simpa only [hψ0] using hwlo
      have hwup : w < ψ (y 4)+ε := by rw [hψ0]; linarith [(abs_lt.mp hw).2]
      obtain ⟨l,r,hl,hr,hlv,hrv,hzeros,hbetween,houtside⟩ := habove w hwψ hwup
      have hlI : l ∈ Ioo (y 4-δ) (y 4+δ) := ⟨hl.1,by linarith [hl.2]⟩
      have hrI : r ∈ Ioo (y 4-δ) (y 4+δ) := ⟨by linarith [hr.1],hr.2⟩
      refine ⟨l,r,hl,hr,?_,?_,?_,?_,?_⟩
      · exact (hp l w hlI hw).2.2.2.2.2.mpr hlv.symm
      · exact (hp r w hrI hw).2.2.2.2.2.mpr hrv.symm
      · intro t ht
        exact (hp t w ht hw).2.2.2.2.2.trans
          ((eq_comm : w = ψ t ↔ ψ t = w).trans (hzeros t ht))
      · intro t ht
        have htI : t ∈ Ioo (y 4-δ) (y 4+δ) := ⟨lt_trans hl.1 ht.1,lt_trans ht.2 hr.2⟩
        exact (hp t w htI hw).2.2.2.2.1.mpr (hbetween t ht)
      · intro t ht hout
        exact (hp t w ht hw).2.2.2.1.mpr (houtside t ht hout)

/-- The fixed physical data construct original roots, actual positive
contour curvature, and the exact local zero/one/two-zero-mode classification. -/
theorem exists_actual_local_bifurcation :
    ∃ (y : T) (P : Params → E) (ψ : ℝ → ℝ) (kappa d δ ε : ℝ),
      y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 ∧
      ContourData y P ψ ∧ CurvatureData y P ψ kappa d ∧ BifurcationData y P δ ε := by
  obtain ⟨y,P,ψ,kappa,d,hbox,hy,hC,hD⟩ := exists_actual_positive_contour_curvature
  obtain ⟨δ,ε,hB⟩ := contour_data_has_local_bifurcation y (fun i => ⟨hbox.1 i,hbox.2 i⟩) P ψ kappa d hC hD
  exact ⟨y,P,ψ,kappa,d,δ,ε,hbox,hy,hC,hD,hB⟩

end FMSA.Convergence.M2LocalBifurcation

/-- info: 'FMSA.Convergence.M2LocalBifurcation.contour_data_has_local_bifurcation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2LocalBifurcation.contour_data_has_local_bifurcation

/-- info: 'FMSA.Convergence.M2LocalBifurcation.exists_actual_local_bifurcation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2LocalBifurcation.exists_actual_local_bifurcation
