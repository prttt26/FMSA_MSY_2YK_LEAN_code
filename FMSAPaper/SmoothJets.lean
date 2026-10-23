import LeanCode.YukawaOZMix.MSAMixtureBHJetRecurrence
import Mathlib.Analysis.Analytic.Order

/-! Smooth germs with the same normalized Taylor coefficients remain equivalent
under the polynomial operations in the actual BH residual. -/
noncomputable section
open Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Paper.SmoothJets
open ExactMSA.BSource ExactMSA.MultiTailMixture

structure JetEq (f g : ℝ → ℝ) : Prop where
  left_smooth : ContDiffAt ℝ ∞ f 0
  right_smooth : ContDiffAt ℝ ∞ g 0
  coeff_eq : ∀ n, jet f n = jet g n

theorem JetEq.refl (f : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0) : JetEq f f :=
  ⟨hf, hf, fun _ => rfl⟩

theorem JetEq.const (c : ℝ) : JetEq (fun _ : ℝ => c) (fun _ => c) :=
  JetEq.refl _ contDiffAt_const

theorem JetEq.id : JetEq (fun t : ℝ => t) (fun t => t) :=
  JetEq.refl _ contDiffAt_id

theorem JetEq.add {f g u v : ℝ → ℝ} (h : JetEq f g) (k : JetEq u v) :
    JetEq (fun t => f t + u t) (fun t => g t + v t) := by
  refine ⟨h.left_smooth.add k.left_smooth, h.right_smooth.add k.right_smooth, ?_⟩
  intro n
  simp only [jet, iteratedDeriv_fun_add (h.left_smooth.of_le (by exact_mod_cast le_top))
      (k.left_smooth.of_le (by exact_mod_cast le_top)),
    iteratedDeriv_fun_add (h.right_smooth.of_le (by exact_mod_cast le_top))
      (k.right_smooth.of_le (by exact_mod_cast le_top)), add_div]
  exact congrArg₂ (· + ·) (h.coeff_eq n) (k.coeff_eq n)

theorem JetEq.sub {f g u v : ℝ → ℝ} (h : JetEq f g) (k : JetEq u v) :
    JetEq (fun t => f t - u t) (fun t => g t - v t) := by
  refine ⟨h.left_smooth.sub k.left_smooth, h.right_smooth.sub k.right_smooth, ?_⟩
  intro n
  simp only [jet, iteratedDeriv_fun_sub (h.left_smooth.of_le (by exact_mod_cast le_top))
      (k.left_smooth.of_le (by exact_mod_cast le_top)),
    iteratedDeriv_fun_sub (h.right_smooth.of_le (by exact_mod_cast le_top))
      (k.right_smooth.of_le (by exact_mod_cast le_top)), sub_div]
  exact congrArg₂ (· - ·) (h.coeff_eq n) (k.coeff_eq n)

theorem JetEq.mul {f g u v : ℝ → ℝ} (h : JetEq f g) (k : JetEq u v) :
    JetEq (fun t => f t * u t) (fun t => g t * v t) := by
  refine ⟨h.left_smooth.mul k.left_smooth, h.right_smooth.mul k.right_smooth, ?_⟩
  intro n
  rw [normalized_mul _ _ n (h.left_smooth.of_le (by exact_mod_cast le_top)) (k.left_smooth.of_le (by exact_mod_cast le_top)),
    normalized_mul _ _ n (h.right_smooth.of_le (by exact_mod_cast le_top)) (k.right_smooth.of_le (by exact_mod_cast le_top))]
  simp_rw [h.coeff_eq, k.coeff_eq]

theorem JetEq.div_const {f g : ℝ → ℝ} (h : JetEq f g) (c : ℝ) :
    JetEq (fun t => f t / c) (fun t => g t / c) := by
  simpa only [div_eq_mul_inv] using h.mul (JetEq.const c⁻¹)

theorem JetEq.neg {f g : ℝ → ℝ} (h : JetEq f g) :
    JetEq (fun t => -f t) (fun t => -g t) := by
  simpa only [neg_one_mul] using (JetEq.const (-1)).mul h

theorem JetEq.sum {I : Type*} [Fintype I] {f g : I → ℝ → ℝ}
    (h : ∀ i, JetEq (f i) (g i)) :
    JetEq (fun t => ∑ i, f i t) (fun t => ∑ i, g i t) := by
  refine ⟨ContDiffAt.sum (fun i _ => (h i).left_smooth),
    ContDiffAt.sum (fun i _ => (h i).right_smooth), ?_⟩
  intro n
  unfold jet
  rw [iteratedDeriv_fun_sum (fun i _ => (h i).left_smooth.of_le (by exact_mod_cast le_top)),
    iteratedDeriv_fun_sum (fun i _ => (h i).right_smooth.of_le (by exact_mod_cast le_top)),
    Finset.sum_div, Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => (h i).coeff_eq n)

variable {N : ℕ} {T : Type*} [Fintype T]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem actual_residual_jetEq (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (D G D' G' : ℝ → TailMatrix T N)
    (hD : ∀ u i j, JetEq (fun t => D t u i j) (fun t => D' t u i j))
    (hG : ∀ u i j, JetEq (fun t => G t u i j) (fun t => G' t u i j)) :
    (∀ u i j, JetEq
      (fun t => (residual z rho sigma K (t, (D t, G t))).1 u i j)
      (fun t => (residual z rho sigma K (t, (D' t, G' t))).1 u i j)) ∧
    (∀ u i j, JetEq
      (fun t => (residual z rho sigma K (t, (D t, G t))).2 u i j)
      (fun t => (residual z rho sigma K (t, (D' t, G' t))).2 u i j)) := by
  constructor <;> intro u i j
  all_goals simp only [ExactMSA.MultiTailMixture.residual, firstLHS, secondLHS,
    secondRHS, dressedQhat, Qhat, amplitudeA, amplitudeQp, W, C,
    MSAMixture.mixDA, MSAMixture.mixDqp, MSAMixture.mixM, MSAMixture.mixN,
    MSAMixture.Wt, MSAMixture.Ct, MSAMixture.gam]
  all_goals
    repeat' first
      | exact hD _ _ _
      | exact hG _ _ _
      | exact JetEq.const _
      | exact JetEq.id
      | apply JetEq.add
      | apply JetEq.sub
      | apply JetEq.mul
      | apply JetEq.div_const
      | apply JetEq.neg
      | apply JetEq.sum; intro

/-- An analytic scalar residual whose Taylor coefficients all vanish is zero
on a neighborhood. Smoothness without analyticity would not suffice. -/
theorem locally_zero_of_analytic_zero_jets (f : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hz : ∀ n, jet f n = 0) :
    f =ᶠ[𝓝 (0 : ℝ)] 0 := by
  apply analyticOrderAt_eq_top.mp
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr
  intro i _
  have hi := hz i
  have hn : (i.factorial : ℝ) ≠ 0 := by positivity
  exact (div_eq_zero_iff.mp hi).resolve_right hn

end FMSA.Paper.SmoothJets

/-- info: 'FMSA.Paper.SmoothJets.JetEq.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.refl

/-- info: 'FMSA.Paper.SmoothJets.JetEq.const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.const

/-- info: 'FMSA.Paper.SmoothJets.JetEq.id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.id

/-- info: 'FMSA.Paper.SmoothJets.JetEq.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.add

/-- info: 'FMSA.Paper.SmoothJets.JetEq.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.sub

/-- info: 'FMSA.Paper.SmoothJets.JetEq.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.mul

/-- info: 'FMSA.Paper.SmoothJets.JetEq.div_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.div_const

/-- info: 'FMSA.Paper.SmoothJets.JetEq.neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.neg

/-- info: 'FMSA.Paper.SmoothJets.JetEq.sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.JetEq.sum

/-- info: 'FMSA.Paper.SmoothJets.actual_residual_jetEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.actual_residual_jetEq

/-- info: 'FMSA.Paper.SmoothJets.locally_zero_of_analytic_zero_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SmoothJets.locally_zero_of_analytic_zero_jets
