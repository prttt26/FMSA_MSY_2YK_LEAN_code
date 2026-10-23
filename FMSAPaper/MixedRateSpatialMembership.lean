import FMSAPaper.ActualMixedRateCross
import FMSAPaper.SpatialDictionary

/-! Membership of actual cross-rate Baxter blocks in the paper's spatial space. -/
noncomputable section
open MeasureTheory Set Real

namespace FMSA.Paper.MixedRateSpatialMembership

open ExactMSA.Breakpoint MSAMixture MSAMixtureCoreUneq SpatialDictionary ActualMixedRateCross
variable {N : ℕ} {T : Type*} [Fintype T]

omit [Fintype T] in
theorem actual_cross_inner_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (W C V D : Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (u v : T) (i j l : Fin N) (horder : sigma j <= sigma i) :
    HasForm z (Ioo (0 : ℝ) (lamA sigma i j))
      (fun r => ∫ t : ℝ, baxterQ' (z u) sigma 0 0 W C i l (t + r) *
        baxterQ (z v) sigma 0 0 V D j l t) := by
  obtain ⟨cm, cp, hc⟩ := actual_cross_inner_fixed_span (z u) (z v) (hz u) (hz v)
    sigma W C V D hsigma i j l horder
  have hm := (dictionary_hasForm z (Ioo (0 : ℝ) (lamA sigma i j)) (.inr (.inl u))).const_mul cm
  have hp := (dictionary_hasForm z (Ioo (0 : ℝ) (lamA sigma i j)) (.inr (.inr v))).const_mul cp
  exact (hm.add hp).congr (fun r hr => (hc r hr).symm)

omit [Fintype T] in
theorem actual_cross_outer_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (W C V D : Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (u v : T) (i j l : Fin N) (horder : sigma j <= sigma i) :
    HasForm z (Ioo (lamA sigma i j) (edgeHi sigma i j))
      (fun r => ∫ t : ℝ, baxterQ' (z u) sigma 0 0 W C i l (t + r) *
        baxterQ (z v) sigma 0 0 V D j l t) := by
  obtain ⟨c0, cm, cp, hc⟩ := actual_cross_outer_fixed_span (z u) (z v) (hz u) (hz v)
    sigma W C V D hsigma i j l horder
  let s := Ioo (lamA sigma i j) (edgeHi sigma i j)
  have h0 : HasForm z s (fun _ => c0) := by
    simpa only [dictionary, Fin.val_zero, pow_zero, mul_one] using
      (dictionary_hasForm z s (.inl 0)).const_mul c0
  have hm := (dictionary_hasForm z s (.inr (.inl u))).const_mul cm
  have hp := (dictionary_hasForm z s (.inr (.inr v))).const_mul cp
  exact ((h0.add hm).add hp).congr (fun r hr => (hc r hr).symm)

end FMSA.Paper.MixedRateSpatialMembership

/-- info: 'FMSA.Paper.MixedRateSpatialMembership.actual_cross_inner_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateSpatialMembership.actual_cross_inner_hasForm

/-- info: 'FMSA.Paper.MixedRateSpatialMembership.actual_cross_outer_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateSpatialMembership.actual_cross_outer_hasForm
