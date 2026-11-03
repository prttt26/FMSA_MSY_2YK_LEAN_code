import MSAConvergence.PureFluidRSimplePoleUniqueness
import MSAConvergence.PureFluidRWeightPositivity

set_option linter.style.header false

/-! The candidate squarefree W weight has precisely the odd part
predicted by the formal r dispersion identity. -/
noncomputable section
namespace FMSA.Convergence.PureFluidRWeightOddPart
open FMSA.Convergence.PureFluidRPartialFraction
variable {T : Type*} [DecidableEq T]

def multilinearWeight (s : Finset T) (z : T → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, (z i / (x + z i)) *
    ∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2)

/-- The odd part of the proposed squarefree r coefficient is exactly
the product obtained from the formal U dispersion series. -/
theorem multilinearWeight_odd_part
    (s : Finset T) (z : T → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    multilinearWeight s z x - multilinearWeight s z (-x) =
      -x * (∏ i ∈ s, 2 * z i) *
        (∏ i ∈ s, (z i ^ 2 - x ^ 2))⁻¹ := by
  classical
  let P : ℝ := ∏ i ∈ s, 2 * z i
  have hterm (i : T) (hi : i ∈ s) :
      ((z i / (x + z i)) - (z i / (-x + z i))) *
        ∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2) =
      -x * P *
        ((∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
          (z i ^ 2 - x ^ 2)⁻¹) := by
    have hplus : x + z i ≠ 0 := (add_pos hx (hz i hi)).ne'
    have hminus : -x + z i ≠ 0 := by
      intro hzero
      exact hxn i hi (by linarith)
    have hlinear : z i / (x + z i) - z i / (-x + z i) =
        -x * (2 * z i) * (z i ^ 2 - x ^ 2)⁻¹ := by
      rw [div_sub_div _ _ hplus hminus]
      have hden : (x + z i) * (-x + z i) = z i ^ 2 - x ^ 2 := by ring_nf
      rw [hden]
      have hnum : z i * (-x + z i) - (x + z i) * z i =
          -x * (2 * z i) := by ring_nf
      rw [hnum, div_eq_mul_inv]
    have hprod : (∏ j ∈ s.erase i,
        (2 * z j) / (z j ^ 2 - z i ^ 2)) =
      (∏ j ∈ s.erase i, 2 * z j) *
        (∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.prod_mul_distrib]
    have hP : P = (2 * z i) * (∏ j ∈ s.erase i, 2 * z j) := by
      dsimp [P]
      exact (Finset.mul_prod_erase s (fun j => 2 * z j) hi).symm
    rw [hlinear, hprod, hP]
    ring_nf
  unfold multilinearWeight
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i ∈ s,
        ((z i / (x + z i)) *
            (∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2)) -
          (z i / (-x + z i)) *
            (∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2)))) =
      ∑ i ∈ s, -x * P *
        ((∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
          (z i ^ 2 - x ^ 2)⁻¹) := by
            apply Finset.sum_congr rfl
            intro i hi
            simpa only [sub_mul] using hterm i hi
    _ = -x * P *
      (∑ i ∈ s, (∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
        (z i ^ 2 - x ^ 2)⁻¹) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [← reciprocal_sq_diff_prod_eq_sum s z x hs hx hz hzinj hxn]

/-- The candidate odd-part formula holds on both sides of the real
axis, requiring only the two finite off-pole conditions. -/
theorem multilinearWeight_odd_part_off_poles
    (s : Finset T) (z : T → ℝ) (x : ℝ)
    (hs : s.Nonempty)
    (hz : ∀ i ∈ s, 0 < z i) (hzinj : Set.InjOn z s)
    (hplus : ∀ i ∈ s, x + z i ≠ 0)
    (hminus : ∀ i ∈ s, -x + z i ≠ 0) :
    multilinearWeight s z x - multilinearWeight s z (-x) =
      -x * (∏ i ∈ s, 2 * z i) *
        (∏ i ∈ s, (z i ^ 2 - x ^ 2))⁻¹ := by
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hy : 0 < -x := neg_pos.mpr hxneg
    have hyn : ∀ i ∈ s, -x ≠ z i := by
      intro i hi heq
      apply hplus i hi
      rw [← heq]
      ring_nf
    have h := multilinearWeight_odd_part s z (-x) hs hy hz hzinj hyn
    simp only [neg_neg, neg_sq] at h
    calc
      multilinearWeight s z x - multilinearWeight s z (-x) =
          -(multilinearWeight s z (-x) - multilinearWeight s z x) := by ring_nf
      _ = -(x * (∏ i ∈ s, 2 * z i) *
          (∏ i ∈ s, (z i ^ 2 - x ^ 2))⁻¹) := by rw [h]
      _ = _ := by ring_nf
  · subst x
    ring_nf
  · have hxn : ∀ i ∈ s, x ≠ z i := by
      intro i hi heq
      apply hminus i hi
      rw [← heq]
      ring_nf
    exact multilinearWeight_odd_part s z x hs hxpos hz hzinj hxn

end FMSA.Convergence.PureFluidRWeightOddPart

/-- info: 'FMSA.Convergence.PureFluidRWeightOddPart.multilinearWeight_odd_part' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightOddPart.multilinearWeight_odd_part
/-- info: 'FMSA.Convergence.PureFluidRWeightOddPart.multilinearWeight_odd_part_off_poles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightOddPart.multilinearWeight_odd_part_off_poles
