import FMSAPaper.MultivariateStrength

/-! Homogeneous polynomial jets for every continuous PY-seeded actual root. -/
noncomputable section
open Filter Topology
open scoped ContDiff BigOperators

namespace FMSA.Paper.ActualStrengthJets

open ExactMSA.MultiTailMixture ExactMSA.BSource MultivariateStrength
variable {N : ℕ} {T : Type*} [Fintype T]

theorem strength_root_on_ray
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (v : TailMatrix T N → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ K in 𝓝 (0 : TailMatrix T N), IsRoot z rho sigma K (v K).1 (v K).2)
    (K : TailMatrix T N) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (v (t • K)).1 (v (t • K)).2 := by
  have ht : Tendsto (fun t : ℝ => t • K) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t • K) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  exact ht.eventually hroot

theorem seed_branch_eq_strength_ray
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i)
    (v : TailMatrix T N → TailMatrix T N × TailMatrix T N)
    (hv : ContDiffAt ℝ ∞ v 0) (hv0 : v 0 = (0, baseSeed z rho sigma))
    (hvr : ∀ᶠ K in 𝓝 (0 : TailMatrix T N), IsRoot z rho sigma K (v K).1 (v K).2)
    (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hpr : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    p =ᶠ[𝓝 (0 : ℝ)] (fun t => v (t • K)) := by
  refine LocalBranch.actual_seed_roots_eventuallyEq z rho sigma K hz hvac hrho hsigma
    p (fun t => v (t • K)) hp ?_ hp0 ?_ hpr (strength_root_on_ray z rho sigma v hvr K)
  · have hv' : ContinuousAt v ((0 : ℝ) • K) := by simpa using hv.continuousAt
    exact hv'.comp (f := fun t : ℝ => t • K) (by fun_prop)
  · simpa using hv0

/-- F1 homogeneity for actual roots, including arbitrary separately chosen
continuous branches at each strength vector. The coefficient table depends on
state and order, but is independent of K and of the chosen root branch. -/
theorem actual_jets_homogeneous_polynomial
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i)
    (n : ℕ) (u : T) (i j : Fin N) :
    ∃ cD cG : (Fin n → T × Fin N × Fin N) → ℝ,
      ∀ (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N),
        ContinuousAt p 0 → p 0 = (0, baseSeed z rho sigma) →
        (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) →
        jet (fun t => (p t).1 u i j) n =
          ∑ h : Fin n → T × Fin N × Fin N, cD h * ∏ k, K (h k).1 (h k).2.1 (h k).2.2 ∧
        jet (fun t => (p t).2 u i j) n =
          ∑ h : Fin n → T × Fin N × Fin N, cG h * ∏ k, K (h k).1 (h k).2.1 (h k).2.2 := by
  obtain ⟨v, hv0, hv, hvr⟩ := exists_smooth_strength_root z rho sigma hz hvac hrho hsigma
  obtain ⟨cD, cG, hc⟩ := component_ray_jet_polynomial v hv n u i j
  refine ⟨cD, cG, fun K p hp hp0 hpr => ?_⟩
  have he := seed_branch_eq_strength_ray z rho sigma hz hvac hrho hsigma v hv hv0 hvr
    K p hp hp0 hpr
  have heD : (fun t => (p t).1 u i j) =ᶠ[𝓝 (0 : ℝ)] (fun t => (v (t • K)).1 u i j) := by
    filter_upwards [he] with t ht
    rw [ht]
  have heG : (fun t => (p t).2 u i j) =ᶠ[𝓝 (0 : ℝ)] (fun t => (v (t • K)).2 u i j) := by
    filter_upwards [he] with t ht
    rw [ht]
  have hD := congrArg (fun a : ℝ => a / (n.factorial : ℝ)) (heD.iteratedDeriv_eq n)
  have hG := congrArg (fun a : ℝ => a / (n.factorial : ℝ)) (heG.iteratedDeriv_eq n)
  exact ⟨hD.trans (hc K).1, hG.trans (hc K).2⟩

end FMSA.Paper.ActualStrengthJets

/-- info: 'FMSA.Paper.ActualStrengthJets.strength_root_on_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualStrengthJets.strength_root_on_ray

/-- info: 'FMSA.Paper.ActualStrengthJets.seed_branch_eq_strength_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualStrengthJets.seed_branch_eq_strength_ray

/-- info: 'FMSA.Paper.ActualStrengthJets.actual_jets_homogeneous_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualStrengthJets.actual_jets_homogeneous_polynomial
