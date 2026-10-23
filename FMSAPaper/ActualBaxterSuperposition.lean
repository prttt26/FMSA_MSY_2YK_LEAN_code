import FMSAPaper.BaxterSuperposition
import FMSAPaper.SingleRateSpatialMembership

/-! Superposition for the actual finite-tail Baxter numerator. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.Paper.ActualBaxterSuperposition

open ExactMSA.Breakpoint ExactMSA.MultiTailMixture MSAMixture MSAMixtureCoreUneq
variable {N : ℕ} {T : Type*} [Fintype T]

omit [Fintype T] in
theorem factor_split (z w : ℝ) (sigma A : Fin N → ℝ)
    (qp W C : Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    baxterQ z sigma A qp W C i j r =
      baxterQ w sigma A qp 0 0 i j r + baxterQ z sigma 0 0 W C i j r := by
  unfold baxterQ
  split_ifs <;> simp [sub_eq_add_neg, add_assoc]

omit [Fintype T] in
theorem prime_split (z w : ℝ) (sigma A : Fin N → ℝ)
    (qp W C : Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    baxterQ' z sigma A qp W C i j r =
      baxterQ' w sigma A qp 0 0 i j r + baxterQ' z sigma 0 0 W C i j r := by
  unfold baxterQ'
  split_ifs <;> simp [sub_eq_add_neg, add_assoc]

omit [Fintype T] in
theorem polynomial_numerator_rate (z w : ℝ) (rho sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (i j : Fin N) :
    SingleRateSpatialMembership.numerator z rho sigma A qp 0 0 i j =
      SingleRateSpatialMembership.numerator w rho sigma A qp 0 0 i j := by
  funext r
  simp only [SingleRateSpatialMembership.numerator, baxterQ, baxterQ', Pi.zero_apply,
    zero_mul, mul_zero, add_zero, sub_zero]

def numerator (z : T → ℝ) (rho sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : T → Fin N → Fin N → ℝ) (i j : Fin N) : ℝ → ℝ :=
  BaxterSuperposition.numerator rho (q z sigma A qp W C) (qPrime z sigma A qp W C) i j

def tailCross (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (W C : T → Fin N → Fin N → ℝ) (u v : T) (i j : Fin N) : ℝ → ℝ :=
  BaxterSuperposition.cross rho (baxterQ (z v) sigma 0 0 (W v) (C v))
    (baxterQ' (z u) sigma 0 0 (W u) (C u)) i j

theorem actual_superposition (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : T → Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j : Fin N) (r : ℝ) :
    numerator z rho sigma A qp W C i j r =
      SingleRateSpatialMembership.numerator 1 rho sigma A qp 0 0 i j r +
        (∑ u, (SingleRateSpatialMembership.numerator (z u) rho sigma A qp (W u) (C u) i j r -
          SingleRateSpatialMembership.numerator 1 rho sigma A qp 0 0 i j r)) +
        (∑ u, ∑ v, tailCross z rho sigma W C u v i j r) -
          ∑ u, tailCross z rho sigma W C u u i j r := by
  let P := baxterQ 1 sigma A qp 0 0
  let D := baxterQ' 1 sigma A qp 0 0
  let F := fun u => baxterQ (z u) sigma 0 0 (W u) (C u)
  let G := fun u => baxterQ' (z u) sigma 0 0 (W u) (C u)
  have hq : (fun a b t => P a b t + ∑ u, F u a b t) = q z sigma A qp W C := by
    funext a b t
    exact (q_decomposition z sigma A qp W C a b t).symm
  have hd : (fun a b t => D a b t + ∑ u, G u a b t) = qPrime z sigma A qp W C := by
    funext a b t
    exact (qPrime_decomposition z sigma A qp W C a b t).symm
  have hf (u : T) : (fun a b t => P a b t + F u a b t) =
      baxterQ (z u) sigma A qp (W u) (C u) := by
    funext a b t
    exact (factor_split (z u) 1 sigma A qp (W u) (C u) a b t).symm
  have hg (u : T) : (fun a b t => D a b t + G u a b t) =
      baxterQ' (z u) sigma A qp (W u) (C u) := by
    funext a b t
    exact (prime_split (z u) 1 sigma A qp (W u) (C u) a b t).symm
  have h := BaxterSuperposition.numerator_superposition rho P D F G i j r
    (fun l => crossRate_convolution_integrable 1 1 one_pos one_pos sigma A A qp qp
      0 0 0 0 hsigma i j l r)
    (fun u l => crossRate_convolution_integrable (z u) 1 (hz u) one_pos sigma 0 A 0 qp
      (W u) (C u) 0 0 hsigma i j l r)
    (fun v l => crossRate_convolution_integrable 1 (z v) one_pos (hz v) sigma A 0 qp 0
      0 0 (W v) (C v) hsigma i j l r)
    (fun u v l => crossRate_convolution_integrable (z u) (z v) (hz u) (hz v) sigma 0 0 0 0
      (W u) (C u) (W v) (C v) hsigma i j l r)
  rw [hq, hd] at h
  simp_rw [hf, hg] at h
  exact h

end FMSA.Paper.ActualBaxterSuperposition

/-- info: 'FMSA.Paper.ActualBaxterSuperposition.factor_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSuperposition.factor_split

/-- info: 'FMSA.Paper.ActualBaxterSuperposition.prime_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSuperposition.prime_split

/-- info: 'FMSA.Paper.ActualBaxterSuperposition.polynomial_numerator_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSuperposition.polynomial_numerator_rate

/-- info: 'FMSA.Paper.ActualBaxterSuperposition.actual_superposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterSuperposition.actual_superposition
