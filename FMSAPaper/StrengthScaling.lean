import LeanCode.YukawaOZMix.MSAMixtureBHJetRecurrence
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# Actual BH strength rescaling and normalized jet scaling

The physical residual depends on coupling and strengths only through their
product. A local smooth root for K therefore supplies compatible roots for a*K,
whose n-th jets scale by a^n. This is a raywise homogeneity statement. It does
not yet prove that a globally chosen coefficient function of all strengths is
a homogeneous multivariate polynomial, nor identify arbitrary branch choices.
-/
noncomputable section
open Filter Topology
open scoped ContDiff

namespace FMSA.Paper.StrengthScaling

open ExactMSA.BSource ExactMSA.MultiTailMixture

/-- Scalar high derivatives commute with a linear change of coupling. Mathlib's
zero convention for undefined derivatives makes this identity unconditional. -/
theorem iteratedDeriv_rescale (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => f (a * t)) =
      fun t => a ^ n * iteratedDeriv n f (a * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, iteratedDeriv_succ, pow_succ]
    ring

theorem jet_rescale (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    jet (fun t => f (a * t)) n = a ^ n * jet f n := by
  simp only [jet, iteratedDeriv_rescale, mul_zero]
  ring

variable {N : ℕ} {T : Type*} [Fintype T]

theorem residual_strength_rescale (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (x : TailMatrix T N × TailMatrix T N) (a t : ℝ) :
    residual z rho sigma (a • K) (t, x) = residual z rho sigma K (a * t, x) := by
  apply Prod.ext <;> funext u i j
  · simp only [ExactMSA.MultiTailMixture.residual, Pi.smul_apply, smul_eq_mul]
    ring
  · rfl

/-- Rescaling is valid even at a=0 and for negative a; it needs no assumptions
on tail multiplicities, densities or diameter ordering. -/
theorem local_root_rescale (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N) (a : ℝ)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • (a • K)) (p (a * t)).1 (p (a * t)).2 := by
  have ht : Tendsto (fun t : ℝ => a * t) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => a * t) := by fun_prop
    simpa only [mul_zero] using hcont.tendsto (0 : ℝ)
  filter_upwards [ht.eventually hroot] with t h
  simpa only [smul_smul, mul_comm t a] using h

/-- The existing physical C-infinity branch yields a compatible family for
all scalar strength rescalings, with every entry of both amplitude jets
homogeneous along that ray. -/
theorem exists_actual_roots_with_scaled_jets
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hvac : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i) :
    ∃ p : ℝ → TailMatrix T N × TailMatrix T N,
      p 0 = (0, baseSeed z rho sigma) ∧ ContDiffAt ℝ ∞ p 0 ∧
      ∀ a : ℝ,
        (∀ᶠ t in 𝓝 (0 : ℝ),
          IsRoot z rho sigma (t • (a • K)) (p (a * t)).1 (p (a * t)).2) ∧
        ContDiffAt ℝ ∞ (fun t => p (a * t)) 0 ∧
        ∀ n u i j,
          jet (fun t => (p (a * t)).1 u i j) n =
            a ^ n * jet (fun t => (p t).1 u i j) n ∧
          jet (fun t => (p (a * t)).2 u i j) n =
            a ^ n * jet (fun t => (p t).2 u i j) n := by
  obtain ⟨p, hp, hroot, hc⟩ := exists_contDiffAt_root z rho sigma K hz hvac hrho hsigma
  refine ⟨p, hp, hc, fun a => ⟨local_root_rescale z rho sigma K p a hroot, ?_, ?_⟩⟩
  · have hc' : ContDiffAt ℝ ∞ p (a * 0) := by simpa using hc
    exact hc'.comp 0 (contDiffAt_const.mul contDiffAt_id)
  · intro n u i j
    exact ⟨jet_rescale (fun t => (p t).1 u i j) a n,
      jet_rescale (fun t => (p t).2 u i j) a n⟩

end FMSA.Paper.StrengthScaling

/-! Axiom-footprint gates for every theorem in this extension module. -/

/-- info: 'FMSA.Paper.StrengthScaling.iteratedDeriv_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StrengthScaling.iteratedDeriv_rescale

/-- info: 'FMSA.Paper.StrengthScaling.jet_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StrengthScaling.jet_rescale

/-- info: 'FMSA.Paper.StrengthScaling.residual_strength_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StrengthScaling.residual_strength_rescale

/-- info: 'FMSA.Paper.StrengthScaling.local_root_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StrengthScaling.local_root_rescale

/-- info: 'FMSA.Paper.StrengthScaling.exists_actual_roots_with_scaled_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StrengthScaling.exists_actual_roots_with_scaled_jets
