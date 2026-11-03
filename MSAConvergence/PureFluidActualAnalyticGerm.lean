import MSAConvergence.PureFluidActualNodeGerm
import LeanCode.YukawaOZ.MSAMultiTailFamily
import FMSAPaper.ActualAnalyticBranch

set_option linter.style.header false
/-! The ORIGINAL pure-fluid multi-tail BH residual is real analytic.
The frozen smooth IFT root germ is therefore analytic at the hard-sphere
seed and satisfies the finite H-function dressing locally. -/
noncomputable section
open Real Filter Topology
open scoped ContDiff BigOperators
namespace FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidNodeClosedForm
variable {T : Type*} [Fintype T]

theorem residual_analyticAt (xi : ℝ) (z K : T → ℝ)
    (x : ℝ × ((T → ℝ) × (T → ℝ))) :
    AnalyticAt ℝ (MultiTail.residual xi z K) x := by
  have hD : ∀ u, AnalyticAt ℝ
      (fun y : ℝ × ((T → ℝ) × (T → ℝ)) => y.2.1 u) x := by
    intro u
    have h : AnalyticAt ℝ
        (fun y : ℝ × ((T → ℝ) × (T → ℝ)) => y.2.1) x :=
      analyticAt_fst.comp analyticAt_snd
    exact analyticAt_pi_iff.mp h u
  have hG : ∀ u, AnalyticAt ℝ
      (fun y : ℝ × ((T → ℝ) × (T → ℝ)) => y.2.2 u) x := by
    intro u
    have h : AnalyticAt ℝ
        (fun y : ℝ × ((T → ℝ) × (T → ℝ)) => y.2.2) x :=
      analyticAt_snd.comp analyticAt_snd
    exact analyticAt_pi_iff.mp h u
  have ht : AnalyticAt ℝ
      (fun y : ℝ × ((T → ℝ) × (T → ℝ)) => y.1) x :=
    analyticAt_fst
  unfold MultiTail.residual MultiTail.factor MultiTail.Qhat
    MultiTail.secondRHS MultiTail.amplitudeA MultiTail.amplitudeQp
    MultiTail.momentM MultiTail.momentN MultiTail.W MultiTail.C
    Mtil Ntil gam
  apply AnalyticAt.prod
  all_goals apply analyticAt_pi_iff.mpr; intro u
  all_goals fun_prop

theorem actual_seed_root_analyticAt (xi : ℝ) (z K : T → ℝ)
    (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) (hz : ∀ u, 0 < z u)
    (p : ℝ → (T → ℝ) × (T → ℝ))
    (hp0 : p 0 = (0,fun u => G0 xi (z u)))
    (hp : ContinuousAt p 0)
    (hroot : ∀ᶠ tau : ℝ in 𝓝 0,
      MultiTail.IsRoot xi z (fun u => tau*K u) (p tau).1 (p tau).2) :
    AnalyticAt ℝ p 0 := by
  have hresroot : ∀ᶠ tau : ℝ in 𝓝 0,
      MultiTail.residual xi z K (tau,p tau)=0 := by
    filter_upwards [hroot] with tau hr
    apply Prod.ext
    · ext u
      change (p tau).1 u*MultiTail.factor xi z (p tau).1 (p tau).2 (z u)-
        2*Real.pi*tau*K u/z u=0
      have h := hr.1 u
      dsimp at h
      linear_combination h
    · ext u
      change 2*Real.pi*(p tau).2 u*MultiTail.factor xi z (p tau).1 (p tau).2 (z u)-
        MultiTail.secondRHS xi z (p tau).1 (p tau).2 (z u)=0
      exact sub_eq_zero.mpr (hr.2 u)
  let P := (T → ℝ) × (T → ℝ)
  let p0 : P := (0,fun u => G0 xi (z u))
  have hF (u : T) : F0 xi (z u) ≠ 0 := by
    have h := bhF_base_ne_zero hxi (hz u)
    simpa [bhF,F0] using h
  have hinv : ((fderiv ℝ (MultiTail.residual xi z K) (0,p0)).comp
      (ContinuousLinearMap.inr ℝ ℝ P)).IsInvertible := by
    rw [MultiTail.residual_partial_triangular]
    exact MultiTail.triangular_isInvertible _ hF _
  have ha := FMSA.Paper.ActualAnalyticBranch.continuous_regular_root_analyticAt
    (MultiTail.residual xi z K) p 0
    (residual_analyticAt xi z K _) hp hresroot (by simpa only [hp0] using hinv)
  exact ha

/-- Physical pure-fluid data construct an ANALYTIC original BH root germ
whose actual factor has the finite H-function candidate form near zero.
The conclusion is local and does not assert coefficient positivity. -/
theorem exists_analytic_hs_root_germ_with_candidate_identification
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ u, 0 < z u) :
    ∃ p : ℝ → (T → ℝ) × (T → ℝ),
      p 0 = ((fun _ => 0),fun u => G0 xi (z u)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun u => tau*K u) (p tau).1 (p tau).2) ∧
      ∀ᶠ tau : ℝ in 𝓝 0,
        nodeRLinearEquation z
          (actualWeight xi z (p tau).1 (p tau).2)
          (actualNodeR xi z (p tau).1 (p tau).2) ∧
        ∀ s : ℝ, s ≠ 0 → (∀ u, s+z u ≠ 0) →
          MultiTail.factor xi z (p tau).1 (p tau).2 s =
            hardDressedFactor xi s
              (candidateU z (actualWeight xi z (p tau).1 (p tau).2) s)
              (candidateG z (actualWeight xi z (p tau).1 (p tau).2)
                (actualNodeR xi z (p tau).1 (p tau).2) s) := by
  obtain ⟨p,hp0,hsmooth,hroot,hcand⟩ :=
    exists_actual_hs_root_germ_with_candidate_identification
      xi hxi0 hxi1 z K hz
  have hzero : (0 : T → ℝ) = (fun _ => 0) := by
    funext u
    rfl
  have hp0' : p 0 = (0,fun u => G0 xi (z u)) := by
    simpa only [hzero] using hp0
  exact ⟨p,hp0,
    actual_seed_root_analyticAt xi z K ⟨hxi0,hxi1⟩ hz p hp0'
      hsmooth.continuousAt hroot,
    hroot,hcand⟩

end FMSA.Convergence.PureFluidActualAnalyticGerm
/-- info: 'FMSA.Convergence.PureFluidActualAnalyticGerm.residual_analyticAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualAnalyticGerm.residual_analyticAt
/-- info: 'FMSA.Convergence.PureFluidActualAnalyticGerm.actual_seed_root_analyticAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualAnalyticGerm.actual_seed_root_analyticAt
/-- info: 'FMSA.Convergence.PureFluidActualAnalyticGerm.exists_analytic_hs_root_germ_with_candidate_identification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualAnalyticGerm.exists_analytic_hs_root_germ_with_candidate_identification
