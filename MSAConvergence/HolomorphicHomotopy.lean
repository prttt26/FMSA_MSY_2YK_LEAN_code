import MSAConvergence.HolomorphicZeroPersistence
import Mathlib.Analysis.Complex.Convex

/-! Zero-free half-plane homotopies proved by compactness and reciprocal
maximum modulus. This supplies the statement of the frozen analysis axiom
without consuming that axiom or changing the foundation. -/
noncomputable section
open Filter Topology Set Metric
namespace FMSA.Convergence.HolomorphicHomotopy
open FMSA.Convergence.HolomorphicZeroPersistence

/-- A continuous entire homotopy with no real-axis zeros and a uniform escape
radius preserves zero-freeness of the open lower half-plane. This has exactly
the hypotheses and conclusion of the frozen pure-analysis homotopy axiom. -/
theorem zeroFree_lowerHalfPlane_of_homotopy
    {H : ℝ → ℂ → ℂ} {a b R : ℝ}
    (hab : a ≤ b) (hR : 0 < R)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2) (Icc a b ×ˢ (univ : Set ℂ)))
    (hholo : ∀ t ∈ Icc a b, Differentiable ℂ (H t))
    (hbound : ∀ t ∈ Icc a b, ∀ z : ℂ, z.im ≤ 0 → H t z = 0 → ‖z‖ < R)
    (hreal : ∀ t ∈ Icc a b, ∀ z : ℂ, z.im = 0 → H t z ≠ 0)
    (hbase : ∀ z : ℂ, z.im < 0 → H a z ≠ 0) :
    ∀ z : ℂ, z.im < 0 → H b z ≠ 0 := by
  let P := Icc a b
  letI : PreconnectedSpace P := Subtype.preconnectedSpace isPreconnected_Icc
  let G : Set P := {t | ∀ z : ℂ, z.im < 0 → H t z ≠ 0}
  have hC : Continuous (fun x : P × ℂ => H x.1 x.2) :=
    hcont.comp_continuous (by fun_prop : Continuous (fun x : P × ℂ => ((x.1 : ℝ),x.2)))
      (fun x => ⟨x.1.property,mem_univ _⟩)
  have ho : IsOpen G := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    let K : Set ℂ := closedBall 0 R ∩ {z : ℂ | z.im ≤ 0}
    have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_right
      (isClosed_le Complex.continuous_im continuous_const)
    have hK0 : ∀ z ∈ K, H p z ≠ 0 := by
      intro z hz
      have him : z.im ≤ 0 := hz.2
      rcases lt_or_eq_of_le him with hi | he
      · exact hp z hi
      · exact hreal p p.property z he
    have he : ∀ᶠ q : P in 𝓝 p, ∀ z ∈ K, H q z ≠ 0 := by
      apply hK.eventually_forall_of_forall_eventually
      intro z hz
      exact (hC.continuousAt (x := (p,z))).eventually_ne (hK0 z hz)
    filter_upwards [he] with q hq
    intro z hz
    by_cases hnorm : ‖z‖ ≤ R
    · exact hq z ⟨by simpa only [mem_closedBall,dist_zero_right] using hnorm,hz.le⟩
    · intro hzero
      exact hnorm (hbound q q.property z hz.le hzero).le
  have hc : IsClosed G := by
    apply isClosed_of_closure_subset
    intro p hp
    let U : Set ℂ := {z : ℂ | z.im < 0}
    have hU : IsOpen U := isOpen_lt Complex.continuous_im continuous_const
    have hconn : IsPreconnected U := (convex_halfSpace_im_lt 0).isPreconnected
    have hA : AnalyticOnNhd ℂ (H p) U :=
      ((hholo p p.property).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ U)
    have hn : ∃ w ∈ U, H p w ≠ 0 := by
      let w : ℂ := (-((R+1 : ℝ) : ℂ))*Complex.I
      have hw : w.im < 0 := by dsimp [w]; simp; linarith
      have hnorm : ‖w‖ = R+1 := by
        simp only [w,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
        exact abs_of_pos (by linarith)
      refine ⟨w,hw,?_⟩
      intro hz
      have hlt := hbound p p.property w hw.le hz
      rw [hnorm] at hlt
      linarith
    exact zero_free_at_closure (fun q : P => H q) G p U hU hconn hp hA hn
      (fun _ _ => hC.continuousAt)
      (fun q _ => (hholo q q.property).differentiableOn) (fun q hq => hq)
  have hall : G = univ := (show IsClopen G from ⟨hc,ho⟩).eq_univ
    ⟨⟨a,le_rfl,hab⟩,hbase⟩
  have hbG : (⟨b,hab,le_rfl⟩ : P) ∈ G := by rw [hall]; trivial
  exact hbG

end FMSA.Convergence.HolomorphicHomotopy

/-- info: 'FMSA.Convergence.HolomorphicHomotopy.zeroFree_lowerHalfPlane_of_homotopy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.HolomorphicHomotopy.zeroFree_lowerHalfPlane_of_homotopy
