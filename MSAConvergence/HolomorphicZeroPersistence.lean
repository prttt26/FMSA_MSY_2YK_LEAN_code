import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! A zero-free limit principle proved by reciprocal maximum modulus.
No Hurwitz/Rouche theorem or new mathematical axiom is assumed. -/
noncomputable section
open Filter Topology Set Metric
namespace FMSA.Convergence.HolomorphicZeroPersistence

/-- A nontrivial holomorphic limit of a continuous parameter family of
zero-free holomorphic functions stays zero-free on a connected open domain.
Compact-circle continuity and reciprocal maximum modulus replace Hurwitz. -/
theorem zero_free_at_closure
    {P : Type*} [TopologicalSpace P] (F : P → ℂ → ℂ) (G : Set P) (p : P)
    (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hp : p ∈ closure G) (hA : AnalyticOnNhd ℂ (F p) U)
    (hnonzero : ∃ w ∈ U, F p w ≠ 0)
    (hjoint : ∀ w ∈ U, ContinuousAt (fun x : P × ℂ => F x.1 x.2) (p,w))
    (hhol : ∀ q ∈ G, DifferentiableOn ℂ (F q) U)
    (hzero : ∀ q ∈ G, ∀ w ∈ U, F q w ≠ 0) : ∀ w ∈ U, F p w ≠ 0 := by
  intro w hw hfw
  have hpunct : ∀ᶠ z in 𝓝[≠] w, F p z ≠ 0 := by
    rcases (hA w hw).eventually_eq_zero_or_eventually_ne_zero with hz | hn
    · have hlocal : F p =ᶠ[𝓝 w] 0 := by filter_upwards [hz] with z hz; exact hz
      have hall := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hw hlocal
      obtain ⟨z,hz,hzn⟩ := hnonzero
      exact False.elim (hzn (hall hz))
    · exact hn
  have hmem : ∀ᶠ z in 𝓝 w, z ∈ U := hU.mem_nhds hw
  have hnon : ∀ᶠ z in 𝓝 w, z ≠ w → F p z ≠ 0 := by
    simpa only [mem_compl_singleton_iff] using eventually_nhdsWithin_iff.mp hpunct
  have hnear : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ≠ w → F p z ≠ 0) := hmem.and hnon
  obtain ⟨epsilon,heps,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := epsilon/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hre : r < epsilon := by dsimp [r]; linarith
  have hdisc : closedBall w r ⊆ U := by
    intro z hz
    exact (hball ((mem_closedBall.mp hz).trans_lt hre)).1
  have hsphere : ∀ z ∈ sphere w r, F p z ≠ 0 := by
    intro z hz
    have hd : dist z w = r := mem_sphere.mp hz
    have hn : z ≠ w := by intro he; rw [he,dist_self] at hd; linarith
    exact (hball (by rw [hd]; exact hre)).2 hn
  have hcompact : IsCompact (sphere w r) := isCompact_sphere w r
  have hcontinuous : ContinuousOn (fun z => ‖F p z‖) (sphere w r) :=
    hA.continuousOn.norm.mono (sphere_subset_closedBall.trans hdisc)
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_forall_le' hcontinuous
    (fun z hz => norm_pos_iff.mpr (hsphere z hz))
  have hm2 : 0 < m/2 := by linarith
  have hboundary : ∀ᶠ q in 𝓝 p, ∀ z ∈ sphere w r, m/2 < ‖F q z‖ := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro z hz
    exact continuousAt_const.eventually_lt (hjoint z (hdisc (sphere_subset_closedBall hz))).norm
      (by have h := hmin z hz; linarith)
  have hins : ContinuousAt (fun q : P => (q,w)) p := by fun_prop
  have hc0 : ContinuousAt (fun q => F q w) p := ContinuousAt.comp (f := fun q : P => (q,w)) (x := p) (hjoint w hw) hins
  have hsmall : ∀ᶠ q in 𝓝 p, ‖F q w‖ < m/2 :=
    hc0.norm.eventually_lt continuousAt_const (by rw [hfw,norm_zero]; exact hm2)
  obtain ⟨q,hq,hb,hc⟩ := ((mem_closure_iff_frequently.mp hp).and_eventually (hboundary.and hsmall)).exists
  have hdiff : DifferentiableOn ℂ (fun z => (F q z)⁻¹) U :=
    (hhol q hq).inv (hzero q hq)
  have hmax : ‖(F q w)⁻¹‖ ≤ (m/2)⁻¹ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdiff.diffContOnCl_ball hdisc)
    · intro z hz
      rw [norm_inv]
      have hzs : z ∈ sphere w r := frontier_ball_subset_sphere hz
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hzero q hq z (hdisc (sphere_subset_closedBall hzs)))) hm2).mpr
        (hb z hzs).le
    · exact subset_closure (mem_ball_self hr)
  rw [norm_inv] at hmax
  have hcentre := (inv_le_inv₀ (norm_pos_iff.mpr (hzero q hq w hw)) hm2).mp hmax
  exact (not_lt_of_ge hcentre) hc

end FMSA.Convergence.HolomorphicZeroPersistence

/-- info: 'FMSA.Convergence.HolomorphicZeroPersistence.zero_free_at_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.HolomorphicZeroPersistence.zero_free_at_closure
