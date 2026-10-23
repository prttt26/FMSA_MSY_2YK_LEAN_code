import FMSAPaper.MixedRateSpatialMembership

/-! The proved single-rate numerator formulas embedded in a finite rate family. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.Paper.SingleRateSpatialMembership

open ExactMSA.Breakpoint MSAMixture MSAMixtureCoreUneq SpatialDictionary
variable {N : ℕ} {T : Type*}

def numerator (z : ℝ) (rho sigma A : Fin N → ℝ)
    (qp W C : Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  -baxterQ' z sigma A qp W C i j r + ∑ l, rho l *
    ∫ t : ℝ, baxterQ' z sigma A qp W C i l (t+r) * baxterQ z sigma A qp W C j l t

theorem gForm_hasForm (z : T → ℝ) (u : T) (s : Set ℝ)
    (c0 c1 c2 c3 c4 cm cp : ℝ) :
    HasForm z s (gForm c0 c1 c2 c3 c4 cm cp (z u)) := by
  have h0 := (dictionary_hasForm z s (.inl 0)).const_mul c0
  have h1 := (dictionary_hasForm z s (.inl 1)).const_mul c1
  have h2 := (dictionary_hasForm z s (.inl 2)).const_mul c2
  have h3 := (dictionary_hasForm z s (.inl 3)).const_mul c3
  have h4 := (dictionary_hasForm z s (.inl 4)).const_mul c4
  have hm := (dictionary_hasForm z s (.inr (.inl u))).const_mul cm
  have hp := (dictionary_hasForm z s (.inr (.inr u))).const_mul cp
  apply ((((((h0.add h1).add h2).add h3).add h4).add hm).add hp).congr
  intro r _
  simp [dictionary, gForm]

theorem single_inner_hasForm (z : T → ℝ) (u : T) (hz : 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp W C : Fin N → Fin N → ℝ)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (hj : 0 < sigma j)
    (horder : sigma j <= sigma i) :
    HasForm z (Ioo (0 : ℝ) (lamA sigma i j))
      (numerator (z u) rho sigma A qp W C i j) := by
  apply (gForm_hasForm z u _ _ _ _ _ _ _ _).congr
  intro r hr
  have hlo : edgeLo sigma i j <= r := by unfold edgeLo; linarith [hr.1]
  have hhi : r <= edgeHi sigma i j := by
    have h := hr.2
    rw [lamA_eq_of_le sigma i j horder] at h
    unfold edgeHi
    linarith [hsigma j]
  exact (numerator_inner (z u) hz rho sigma A qp W C i j r hsigma hj horder
    hr.1 hr.2 hlo hhi).symm

theorem single_outer_hasForm (z : T → ℝ) (u : T) (hz : 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp W C : Fin N → Fin N → ℝ)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (hj : 0 < sigma j)
    (horder : sigma j <= sigma i) :
    HasForm z (Ioo (lamA sigma i j) (edgeHi sigma i j))
      (numerator (z u) rho sigma A qp W C i j) := by
  apply (gForm_hasForm z u _ _ _ _ _ _ _ _).congr
  intro r hr
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg _) hr.1
  have hlo : edgeLo sigma i j <= r := by unfold edgeLo; linarith
  exact (numerator_outer (z u) hz rho sigma A qp W C i j r hsigma hj horder
    hr0 hr.1 hr.2 hlo hr.2.le).symm

end FMSA.Paper.SingleRateSpatialMembership

/-- info: 'FMSA.Paper.SingleRateSpatialMembership.gForm_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleRateSpatialMembership.gForm_hasForm

/-- info: 'FMSA.Paper.SingleRateSpatialMembership.single_inner_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleRateSpatialMembership.single_inner_hasForm

/-- info: 'FMSA.Paper.SingleRateSpatialMembership.single_outer_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleRateSpatialMembership.single_outer_hasForm
