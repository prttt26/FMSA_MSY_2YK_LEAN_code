import FMSAPaper.ActualBaxterSuperposition

/-! The complete ordered multi-tail numerator belongs to the fixed spatial
dictionary, without a root or distinct-rate assumption. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.Paper.MultirateSpatialMembership

open ExactMSA.Breakpoint MSAMixture MSAMixtureCoreUneq SpatialDictionary
open ActualBaxterSuperposition SingleRateSpatialMembership MixedRateSpatialMembership
variable {N : ℕ} {T : Type*} [Fintype T]

omit [Fintype T] in
theorem sub_hasForm {z : T → ℝ} {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : HasForm z s f) (hg : HasForm z s g) : HasForm z s (fun r => f r - g r) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hg.const_mul (-1))

theorem numerator_hasForm_of_pieces (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : T → Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (s : Set ℝ)
    (hbase : HasForm z s (SingleRateSpatialMembership.numerator 1 rho sigma A qp 0 0 i j))
    (hsingle : ∀ u, HasForm z s
      (SingleRateSpatialMembership.numerator (z u) rho sigma A qp (W u) (C u) i j))
    (hcross : ∀ u v, HasForm z s (tailCross z rho sigma W C u v i j)) :
    HasForm z s (ActualBaxterSuperposition.numerator z rho sigma A qp W C i j) := by
  have hs := finite_sum_hasForm z s _ (fun u => sub_hasForm (hsingle u) hbase)
  have hc := finite_sum_hasForm z s _ (fun u => finite_sum_hasForm z s _ (hcross u))
  have hd := finite_sum_hasForm z s _ (fun u => hcross u u)
  apply (sub_hasForm ((hbase.add hs).add hc) hd).congr
  intro r _
  exact (actual_superposition z hz rho sigma A qp W C hsigma i j r).symm

theorem numerator_inner_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u) (u0 : T)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : T → Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (hj : 0 < sigma j) (horder : sigma j <= sigma i) :
    HasForm z (Ioo (0 : ℝ) (lamA sigma i j))
      (ActualBaxterSuperposition.numerator z rho sigma A qp W C i j) := by
  apply numerator_hasForm_of_pieces z hz rho sigma A qp W C hsigma i j
  · rw [polynomial_numerator_rate 1 (z u0)]
    exact single_inner_hasForm z u0 (hz u0) rho sigma A qp 0 0 hsigma i j hj horder
  · intro u
    exact single_inner_hasForm z u (hz u) rho sigma A qp (W u) (C u) hsigma i j hj horder
  · intro u v
    exact finite_sum_hasForm z _ _ (fun l =>
      (actual_cross_inner_hasForm z hz sigma (W u) (C u) (W v) (C v) hsigma u v i j l horder).const_mul (rho l))

theorem numerator_outer_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u) (u0 : T)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : T → Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (hj : 0 < sigma j) (horder : sigma j <= sigma i) :
    HasForm z (Ioo (lamA sigma i j) (edgeHi sigma i j))
      (ActualBaxterSuperposition.numerator z rho sigma A qp W C i j) := by
  apply numerator_hasForm_of_pieces z hz rho sigma A qp W C hsigma i j
  · rw [polynomial_numerator_rate 1 (z u0)]
    exact single_outer_hasForm z u0 (hz u0) rho sigma A qp 0 0 hsigma i j hj horder
  · intro u
    exact single_outer_hasForm z u (hz u) rho sigma A qp (W u) (C u) hsigma i j hj horder
  · intro u v
    exact finite_sum_hasForm z _ _ (fun l =>
      (actual_cross_outer_hasForm z hz sigma (W u) (C u) (W v) (C v) hsigma u v i j l horder).const_mul (rho l))

end FMSA.Paper.MultirateSpatialMembership

/-- info: 'FMSA.Paper.MultirateSpatialMembership.sub_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultirateSpatialMembership.sub_hasForm

/-- info: 'FMSA.Paper.MultirateSpatialMembership.numerator_hasForm_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultirateSpatialMembership.numerator_hasForm_of_pieces

/-- info: 'FMSA.Paper.MultirateSpatialMembership.numerator_inner_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultirateSpatialMembership.numerator_inner_hasForm

/-- info: 'FMSA.Paper.MultirateSpatialMembership.numerator_outer_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultirateSpatialMembership.numerator_outer_hasForm
