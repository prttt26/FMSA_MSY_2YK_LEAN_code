import MSAConvergence.EventuallySignedTaylor
import MSAConvergence.MaximalCanonicalBranch
import MSAConvergence.MixtureHSCanonicity

set_option linter.style.header false

/-! If an actual canonical MSA branch persists past the common Taylor radius,
some original amplitude coefficient has both signs arbitrarily far out. This
is the contrapositive of the proved eventual-sign Pringsheim interface. -/
noncomputable section
open Set
namespace FMSA.Convergence.MixedSignRadiusObstruction
open FMSA.Paper FMSA.Paper.FoldRadius FMSA.Paper.TaylorRoot
open FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.EventuallySignedTaylor
open FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.MixtureHSCanonicity
open FMSA.ExactMSA.MultiTailMixture
open FMSA.MatrixQ0
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Both signs occur arbitrarily late in a real coefficient sequence. -/
def Oscillates (a : ℕ → ℝ) : Prop :=
  (∀ m, ∃ n, m ≤ n ∧ 0 < a n) ∧
  (∀ m, ∃ n, m ≤ n ∧ a n < 0)

/-- A real sequence either has one eventual weak sign or oscillates in the
strong sense above. This includes sequences with infinitely many zeros. -/
theorem eventually_signed_or_oscillates (a : ℕ → ℝ) :
    (∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ, ∀ n, m ≤ n → 0 ≤ s * a n) ∨ Oscillates a := by
  classical
  by_cases hnonneg : ∃ m : ℕ, ∀ n, m ≤ n → 0 ≤ a n
  · obtain ⟨m, hm⟩ := hnonneg
    exact Or.inl ⟨1, by norm_num, m, by simpa using hm⟩
  by_cases hnonpos : ∃ m : ℕ, ∀ n, m ≤ n → a n ≤ 0
  · obtain ⟨m, hm⟩ := hnonpos
    refine Or.inl ⟨-1, by norm_num, m, ?_⟩
    intro n hn
    nlinarith [hm n hn]
  right
  unfold Oscillates
  push Not at hnonneg hnonpos
  exact ⟨hnonpos, hnonneg⟩

/-- If a real-analytic original amplitude branch extends beyond its common
Taylor radius, at least one ORIGINAL D or G coordinate has both positive and
negative Taylor coefficients at arbitrarily high orders. -/
theorem oscillating_original_component_of_radius_lt_interval
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : AnalyticOnNhd ℝ p (Ico 0 b))
    (hr : amplitudeRadius (branchCoefficients p) < ENNReal.ofReal b) :
    ∃ u : T, ∃ i j : Fin N,
      Oscillates (fun n => (branchCoefficients p n).1 u i j) ∨
      Oscillates (fun n => (branchCoefficients p n).2 u i j) := by
  classical
  by_contra hnone
  have hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 ≤ s * (branchCoefficients p n).1 u i j := by
    intro u i j
    rcases eventually_signed_or_oscillates
        (fun n => (branchCoefficients p n).1 u i j) with h | h
    · exact h
    · exact False.elim (hnone ⟨u, i, j, Or.inl h⟩)
  have hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 ≤ s * (branchCoefficients p n).2 u i j := by
    intro u i j
    rcases eventually_signed_or_oscillates
        (fun n => (branchCoefficients p n).2 u i j) with h | h
    · exact h
    · exact False.elim (hnone ⟨u, i, j, Or.inr h⟩)
  exact (not_lt_of_ge
    (le_amplitudeRadius_of_eventually_signed_analytic_branch p b hb hp hD hG)) hr

/-- At any ACTUAL canonical real MSA state strictly beyond the original
common Taylor radius, one D or G coefficient sequence has both signs
arbitrarily late. The maximal endpoint may be finite or infinite. -/
theorem canonical_state_beyond_radius_has_oscillating_component
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed)
    (b : ℝ) (hb : 0 < b) (hbM : b ∈ initialCouplings M.bound)
    (hr : amplitudeRadius (branchCoefficients M.path) < ENNReal.ofReal b) :
    ∃ u : T, ∃ i j : Fin N,
      Oscillates (fun n => (branchCoefficients M.path n).1 u i j) ∨
      Oscillates (fun n => (branchCoefficients M.path n).2 u i j) := by
  have hsub : Ico (0 : ℝ) b ⊆ initialCouplings M.bound := by
    intro t ht
    exact ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hb).mpr ht.2).trans hbM.2⟩
  exact oscillating_original_component_of_radius_lt_interval M.path b hb
    (M.analytic.mono hsub) hr

/-- The obstruction applies directly to the ORIGINAL coefficients of a
constructed maximal canonical MSA branch. A strict radius shortfall cannot
be attributed to finite real-axis amplitude escape. -/
theorem maximal_branch_oscillating_original_component
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤)
    (hr : amplitudeRadius (branchCoefficients M.path) < M.bound) :
    ∃ u : T, ∃ i j : Fin N,
      Oscillates (fun n => (branchCoefficients M.path n).1 u i j) ∨
      Oscillates (fun n => (branchCoefficients M.path n).2 u i j) := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hbound : M.bound = ENNReal.ofReal M.bound.toReal :=
    (ENNReal.ofReal_toReal hfinite).symm
  have hset : initialCouplings M.bound = Ico (0 : ℝ) M.bound.toReal := by
    calc
      initialCouplings M.bound = initialCouplings (ENNReal.ofReal M.bound.toReal) :=
        congrArg initialCouplings hbound
      _ = Ico (0 : ℝ) M.bound.toReal := initial_couplings_ofReal _ hb
  have hanalytic : AnalyticOnNhd ℝ M.path (Ico 0 M.bound.toReal) := by
    rw [← hset]
    exact M.analytic
  rw [hbound] at hr
  exact oscillating_original_component_of_radius_lt_interval M.path M.bound.toReal hb
    hanalytic hr

/-- Physical finite-mixture data construct the HS-seeded ACTUAL branch with
the preceding radius-shortfall obstruction at every canonical real state.
The strict radius inequality remains a premise for each state. -/
theorem exists_hs_branch_with_radius_shortfall_obstruction
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : 0 < vacMix rho sigma)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ M : MaximalBranch z rho sigma K (0, baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0, baseSeed z rho sigma) ∧
      ∀ b : ℝ, 0 < b → b ∈ initialCouplings M.bound →
        amplitudeRadius (branchCoefficients M.path) < ENNReal.ofReal b →
        ∃ u : T, ∃ i j : Fin N,
          Oscillates (fun n => (branchCoefficients M.path n).1 u i j) ∨
          Oscillates (fun n => (branchCoefficients M.path n).2 u i j) := by
  obtain ⟨M, hM⟩ := exists_mixture_hs_maximal_branch
    z hz rho sigma hσ hρ K hK hv
  exact ⟨M, hM, fun b hb hbM hr =>
    canonical_state_beyond_radius_has_oscillating_component
      z rho sigma K _ M b hb hbM hr⟩

end FMSA.Convergence.MixedSignRadiusObstruction
/-- info: 'FMSA.Convergence.MixedSignRadiusObstruction.eventually_signed_or_oscillates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixedSignRadiusObstruction.eventually_signed_or_oscillates
/-- info: 'FMSA.Convergence.MixedSignRadiusObstruction.oscillating_original_component_of_radius_lt_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixedSignRadiusObstruction.oscillating_original_component_of_radius_lt_interval
/-- info: 'FMSA.Convergence.MixedSignRadiusObstruction.canonical_state_beyond_radius_has_oscillating_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixedSignRadiusObstruction.canonical_state_beyond_radius_has_oscillating_component
/-- info: 'FMSA.Convergence.MixedSignRadiusObstruction.maximal_branch_oscillating_original_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixedSignRadiusObstruction.maximal_branch_oscillating_original_component
/-- info: 'FMSA.Convergence.MixedSignRadiusObstruction.exists_hs_branch_with_radius_shortfall_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixedSignRadiusObstruction.exists_hs_branch_with_radius_shortfall_obstruction
