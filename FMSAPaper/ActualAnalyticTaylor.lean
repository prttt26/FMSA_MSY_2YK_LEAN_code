import FMSAPaper.ActualAnalyticBranch
import FMSAPaper.AnalyticTaylor
import FMSAPaper.FoldRadius
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Actual MSA Taylor radii. The physical seed has positive common radius.
For a regular branch ending in a transverse fold, the all-order componentwise
sign hypothesis forces that radius to equal the fold coupling. -/
noncomputable section
open Filter Topology
open scoped ContDiff

namespace FMSA.Paper.ActualAnalyticTaylor
open ExactMSA.MultiTailMixture TaylorRoot FoldRadius AnalyticTaylor ActualAnalyticBranch
variable {N : ℕ} {T : Type*} [Fintype T]

theorem analyticAt_components (p : ℝ → TailMatrix T N × TailMatrix T N) (t : ℝ)
    (hp : AnalyticAt ℝ p t) :
    (∀ u i j, AnalyticAt ℝ (fun x => (p x).1 u i j) t) ∧
    (∀ u i j, AnalyticAt ℝ (fun x => (p x).2 u i j) t) := by
  constructor
  · have h : AnalyticAt ℝ (fun x => (p x).1) t := analyticAt_fst.comp hp
    intro u i j
    have hu := analyticAt_pi_iff.mp h u
    have hi := analyticAt_pi_iff.mp hu i
    exact analyticAt_pi_iff.mp hi j
  · have h : AnalyticAt ℝ (fun x => (p x).2) t := analyticAt_snd.comp hp
    intro u i j
    have hu := analyticAt_pi_iff.mp h u
    have hi := analyticAt_pi_iff.mp hu i
    exact analyticAt_pi_iff.mp hi j

theorem amplitudeRadius_pos (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : AnalyticAt ℝ p 0) : 0 < amplitudeRadius (branchCoefficients p) := by
  obtain ⟨hD, hG⟩ := analyticAt_components p 0 hp
  apply bot_lt_iff_ne_bot.mpr
  apply iInf_ne_bot
  intro u
  apply iInf_ne_bot
  intro i
  apply iInf_ne_bot
  intro j
  exact (lt_min (jet_radius_pos _ (hD u i j)) (jet_radius_pos _ (hG u i j))).ne'

theorem actual_seed_radius_pos
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hv : 0 < MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    0 < amplitudeRadius (branchCoefficients p) :=
  amplitudeRadius_pos p (actual_seed_root_analyticAt z rho sigma K hz hv hrho hsigma p hp hp0 hroot)

theorem exists_analytic_seed_positive_radius
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hv : 0 < MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i) :
    ∃ p : ℝ → TailMatrix T N × TailMatrix T N,
      p 0 = (0, baseSeed z rho sigma) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      AnalyticAt ℝ p 0 ∧ 0 < amplitudeRadius (branchCoefficients p) := by
  obtain ⟨p, hp0, hroot, hp⟩ := exists_contDiffAt_root z rho sigma K hz hv hrho hsigma
  have ha := actual_seed_root_analyticAt z rho sigma K hz hv hrho hsigma p
    hp.continuousAt hp0 hroot
  exact ⟨p, hp0, hroot, ha, amplitudeRadius_pos p ha⟩

theorem le_amplitudeRadius_of_signed_analytic_branch
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : AnalyticOnNhd ℝ p (Set.Ico 0 b))
    (hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).1 u i j)
    (hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).2 u i j) :
    ENNReal.ofReal b <= amplitudeRadius (branchCoefficients p) := by
  apply le_iInf
  intro u
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_min
  · obtain ⟨s, hs, ha⟩ := hD u i j
    exact le_jet_radius_of_signed_analytic_branch _ b hb
      (fun t ht => (analyticAt_components p t (hp t ht)).1 u i j) s hs ha
  · obtain ⟨s, hs, ha⟩ := hG u i j
    exact le_jet_radius_of_signed_analytic_branch _ b hb
      (fun t ht => (analyticAt_components p t (hp t ht)).2 u i j) s hs ha

/-- Conditional fold equality for the actual polynomial MSA residual. The
all-order sign premises remain mathematical hypotheses, not numerical certificates.
No conclusion about convergence exactly at the fold is asserted. -/
theorem actual_radius_eq_fold
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0)
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (f : ℝ) (hf : 0 < f) (hpcont : ContinuousOn p (Set.Icc 0 f))
    (hproot : ∀ t ∈ Set.Ico 0 f, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ Set.Ico 0 f,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible)
    (htransverse : (fderiv ℝ (residual z rho sigma K) (f, p f)) (1, 0) ∉
      Set.range (fun w => (fderiv ℝ (residual z rho sigma K) (f, p f)) (0, w)))
    (hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).1 u i j)
    (hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).2 u i j) :
    amplitudeRadius (branchCoefficients p) = ENNReal.ofReal f := by
  have ha := actual_regular_branch_analyticOnNhd z rho sigma K p f hp hpcont hlocal hproot hinv
  apply le_antisymm
  · exact actual_radius_le_fold z rho sigma K p (ha 0 ⟨le_rfl, hf⟩).contDiffAt
      hlocal f hf hpcont hproot hinv htransverse
  · exact le_amplitudeRadius_of_signed_analytic_branch p f hf ha hD hG

theorem hasSum_of_signed_analytic_branch
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : AnalyticOnNhd ℝ p (Set.Ico 0 b))
    (hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).1 u i j)
    (hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).2 u i j)
    (t : ℝ) (ht : t ∈ Set.Ico 0 b) :
    (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j * t ^ n) ((p t).1 u i j)) ∧
    (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j * t ^ n) ((p t).2 u i j)) := by
  have htb : ENNReal.ofReal t < ENNReal.ofReal b :=
    (ENNReal.ofReal_lt_ofReal_iff hb).mpr ht.2
  constructor <;> intro u i j
  · obtain ⟨s, hs, ha⟩ := hD u i j
    have hc := fun x hx => (analyticAt_components p x (hp x hx)).1 u i j
    exact hasSum_jet_on_interval _ b hc t ht
      (htb.trans_le (le_jet_radius_of_signed_analytic_branch _ b hb hc s hs ha))
  · obtain ⟨s, hs, ha⟩ := hG u i j
    have hc := fun x hx => (analyticAt_components p x (hp x hx)).2 u i j
    exact hasSum_jet_on_interval _ b hc t ht
      (htb.trans_le (le_jet_radius_of_signed_analytic_branch _ b hb hc s hs ha))

/-- The actual branch values are the Taylor sums before a regular positive
endpoint. A fold at the endpoint is unnecessary for this direction. -/
theorem actual_hasSum_before_endpoint
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : ContinuousAt p 0) (hp : ContinuousOn p (Set.Icc 0 b))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hroot : ∀ t ∈ Set.Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ Set.Ico 0 b,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible)
    (hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).1 u i j)
    (hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧
      ∀ n, 0 < n → 0 <= s * (branchCoefficients p n).2 u i j)
    (t : ℝ) (ht : t ∈ Set.Ico 0 b) :
    (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j * t ^ n) ((p t).1 u i j)) ∧
    (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j * t ^ n) ((p t).2 u i j)) :=
  hasSum_of_signed_analytic_branch p b hb
    (actual_regular_branch_analyticOnNhd z rho sigma K p b hp0 hp hlocal hroot hinv) hD hG t ht

end FMSA.Paper.ActualAnalyticTaylor

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.analyticAt_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.analyticAt_components

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.amplitudeRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.amplitudeRadius_pos

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.actual_seed_radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.actual_seed_radius_pos

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.exists_analytic_seed_positive_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.exists_analytic_seed_positive_radius

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.le_amplitudeRadius_of_signed_analytic_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.le_amplitudeRadius_of_signed_analytic_branch

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.actual_radius_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.actual_radius_eq_fold

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.hasSum_of_signed_analytic_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.hasSum_of_signed_analytic_branch

/-- info: 'FMSA.Paper.ActualAnalyticTaylor.actual_hasSum_before_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticTaylor.actual_hasSum_before_endpoint
