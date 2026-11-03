import MSAConvergence.SingleTailNegativeCouplingCounterexample
import FMSAPaper.StrengthScaling

set_option linter.style.header false

/-! The valid direction of the real-root/Taylor statement for the original
finite-mixture MSA equations. The physical strength is included in `K`, so
the evaluation coupling is one. Endpoint convergence may be conditional. -/
noncomputable section
namespace FMSA.Convergence.ActualSeriesRootImplication

open FMSA.Paper.TaylorRoot
open FMSA.Paper.FoldRadius
open FMSA.Paper.StrengthScaling
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ComplexPolynomialSystem
open scoped Topology ContDiff BigOperators

variable {T : Type*} [Fintype T] {N : ℕ}

/-- If the full original BH amplitude Taylor vector sums at its physical
strength, its sum is a real solution of the original Exact MSA equations.
The only branch assumption is a smooth local MSA root germ at the seed. -/
theorem summable_seed_series_implies_exact_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hs : Summable (branchCoefficients p)) :
    IsRoot z rho sigma K
      (∑' n, branchCoefficients p n).1
      (∑' n, branchCoefficients p n).2 := by
  let b : TailMatrix T N × TailMatrix T N := ∑' n, branchCoefficients p n
  have hD : ∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j)
      (b.1 u i j) := by
    intro u i j
    let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.fst ℝ _ _)
    simpa [l, b, entry] using l.hasSum hs.hasSum
  have hG : ∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j)
      (b.2 u i j) := by
    intro u i j
    let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.snd ℝ _ _)
    simpa [l, b, entry] using l.hasSum hs.hasSum
  exact (actual_endpoint_of_smooth_root z rho sigma K p b hp hroot hD hG).1

/-- Consequently, absence of any real Exact MSA root forces divergence of
the complete original BH amplitude Taylor vector at physical strength. -/
theorem no_real_root_implies_seed_series_not_summable
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hnoroot : ¬ ∃ D G : TailMatrix T N, IsRoot z rho sigma K D G) :
    ¬ Summable (branchCoefficients p) := by
  intro hs
  exact hnoroot ⟨(∑' n, branchCoefficients p n).1,
    (∑' n, branchCoefficients p n).2,
    summable_seed_series_implies_exact_root z rho sigma K p hp hroot hs⟩

omit [Fintype T] in
/-- Scaling the coupling scales every original BH amplitude Taylor
coefficient by the corresponding power, without a global smoothness
assumption on the root path. -/
theorem branchCoefficients_rescale
    (p : ℝ → TailMatrix T N × TailMatrix T N) (tau : ℝ) (n : ℕ) :
    branchCoefficients (fun t => p (tau * t)) n =
      tau ^ n • branchCoefficients p n := by
  apply Prod.ext <;> funext u i j
  · simp only [branchCoefficients, Pi.smul_apply, Prod.smul_fst, smul_eq_mul]
    exact jet_rescale (fun t => (p t).1 u i j) tau n
  · simp only [branchCoefficients, Pi.smul_apply, Prod.smul_snd, smul_eq_mul]
    exact jet_rescale (fun t => (p t).2 u i j) tau n

/-- At any real coupling, including a conditionally summable radius
endpoint, convergence of the complete HS-seeded BH amplitude series
produces a real solution of the original Exact MSA equations. -/
theorem summable_at_real_coupling_implies_exact_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (tau : ℝ)
    (hs : Summable (fun n => tau ^ n • branchCoefficients p n)) :
    IsRoot z rho sigma (tau • K)
      (∑' n, tau ^ n • branchCoefficients p n).1
      (∑' n, tau ^ n • branchCoefficients p n).2 := by
  let q := fun t => p (tau * t)
  have hq : ContDiffAt ℝ ∞ q 0 := by
    have hp' : ContDiffAt ℝ ∞ p (tau * 0) := by simpa using hp
    exact hp'.comp 0 (contDiffAt_const.mul contDiffAt_id)
  have hqr : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • (tau • K)) (q t).1 (q t).2 :=
    local_root_rescale z rho sigma K p tau hroot
  have hc : ∀ n, branchCoefficients q n = tau ^ n • branchCoefficients p n :=
    fun n => branchCoefficients_rescale p tau n
  have hqs : Summable (branchCoefficients q) := by
    convert hs using 1
    funext n
    exact hc n
  have heq : (fun n => tau ^ n • branchCoefficients p n) = branchCoefficients q := by
    funext n
    exact (hc n).symm
  have hsumEq : (∑' n, tau ^ n • branchCoefficients p n) =
      (∑' n, branchCoefficients q n) :=
    congrArg (fun a : ℕ → TailMatrix T N × TailMatrix T N => ∑' n, a n) heq
  rw [hsumEq]
  exact summable_seed_series_implies_exact_root z rho sigma (tau • K) q hq hqr hqs

/-- The surviving half of the proposed equivalence at every real
coupling: no real Exact MSA solution forces divergence of the entire
HS-seeded original-amplitude Taylor vector. -/
theorem no_real_root_at_real_coupling_implies_divergence
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (tau : ℝ)
    (hnoroot : ¬ ∃ D G : TailMatrix T N,
      IsRoot z rho sigma (tau • K) D G) :
    ¬ Summable (fun n => tau ^ n • branchCoefficients p n) := by
  intro hs
  exact hnoroot ⟨(∑' n, tau ^ n • branchCoefficients p n).1,
    (∑' n, tau ^ n • branchCoefficients p n).2,
    summable_at_real_coupling_implies_exact_root z rho sigma K p hp hroot tau hs⟩

/-- For every admissible finite-mixture state and physical strength matrix,
the genuine PY-seeded local MSA germ exists and satisfies the no-real-root
divergence implication at every real coupling. -/
theorem exists_physical_seed_with_no_root_divergence
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    ∃ p : ℝ → TailMatrix T N × TailMatrix T N,
      p 0 = (0, baseSeed z rho sigma) ∧
      ContDiffAt ℝ ∞ p 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      ∀ tau : ℝ,
        (¬ ∃ D G : TailMatrix T N, IsRoot z rho sigma (tau • K) D G) →
        ¬ Summable (fun n => tau ^ n • branchCoefficients p n) := by
  obtain ⟨p, hp0, hroot, hp⟩ :=
    exists_contDiffAt_root z rho sigma K hz hv hrho hsigma
  exact ⟨p, hp0, hp, hroot,
    fun tau hnoroot =>
      no_real_root_at_real_coupling_implies_divergence
        z rho sigma K p hp hroot tau hnoroot⟩

end FMSA.Convergence.ActualSeriesRootImplication

/-- info: 'FMSA.Convergence.ActualSeriesRootImplication.summable_seed_series_implies_exact_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualSeriesRootImplication.summable_seed_series_implies_exact_root
/-- info: 'FMSA.Convergence.ActualSeriesRootImplication.no_real_root_implies_seed_series_not_summable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualSeriesRootImplication.no_real_root_implies_seed_series_not_summable
/-- info: 'FMSA.Convergence.ActualSeriesRootImplication.branchCoefficients_rescale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualSeriesRootImplication.branchCoefficients_rescale
/-- info: 'FMSA.Convergence.ActualSeriesRootImplication.summable_at_real_coupling_implies_exact_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualSeriesRootImplication.summable_at_real_coupling_implies_exact_root
/-- info: 'FMSA.Convergence.ActualSeriesRootImplication.no_real_root_at_real_coupling_implies_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualSeriesRootImplication.no_real_root_at_real_coupling_implies_divergence
/-- info: 'FMSA.Convergence.ActualSeriesRootImplication.exists_physical_seed_with_no_root_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualSeriesRootImplication.exists_physical_seed_with_no_root_divergence
