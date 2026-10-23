import LeanCode.YukawaOZMix.MSAMultiTailMixtureSystem
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Abel endpoint transfer to the actual finite-mixture MSA residual

The final theorems need the root identity only near zero. Endpoint convergence
implies interior analyticity; the identity theorem propagates the actual
polynomial residual identity, and Abel transfers it to the endpoint. Identifying
the Taylor series with the PY-seeded branch locally remains an explicit
obligation. No positivity, uniqueness among all roots, or converse is claimed.
-/
noncomputable section
open Filter Topology
open scoped BigOperators

namespace FMSA.Paper.Abel

variable {I : Type*}

/-- Componentwise Abel convergence includes conditional endpoint convergence. -/
theorem coordinatewise_abel (a : ℕ → I → ℝ) (b : I → ℝ)
    (h : ∀ i, HasSum (fun n => a n i) (b i)) :
    Tendsto (fun t i => ∑' n, a n i * t ^ n) (𝓝[<] (1 : ℝ)) (𝓝 b) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt (h i).tendsto_sum_nat

/-- Endpoint convergence implies analyticity at every real point strictly
inside the unit interval, even when the endpoint convergence is conditional. -/
theorem powerSeries_analytic_of_hasSum (a : ℕ → ℝ) (b : ℝ) (h : HasSum a b) :
    AnalyticOnNhd ℝ (fun t => ∑' n, a n * t ^ n) (Set.Ioo (-1 : ℝ) 1) := by
  let p := FormalMultilinearSeries.ofScalars ℝ a
  have hr : (1 : ENNReal) <= p.radius := by
    have ht := h.summable.tendsto_atTop_zero.norm
    have ht' : Tendsto (fun n => ‖p n‖ * ((1 : NNReal) : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [p, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one,
        one_pow, mul_one, norm_zero] using ht
    exact p.le_radius_of_tendsto ht'
  intro t ht
  have hnorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact abs_lt.mpr ht
  have he : (↑‖t‖₊ : ENNReal) < 1 := by exact_mod_cast hnorm
  have hm : t ∈ Metric.eball (0 : ℝ) p.radius := by
    rw [mem_eball_zero_iff]
    exact he.trans_le hr
  have ha := p.analyticOnNhd t hm
  change AnalyticAt ℝ (FormalMultilinearSeries.ofScalarsSum a) t at ha
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using ha

theorem residual_at_limit {E F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [T2Space F] [Zero F]
    (R : ℝ × E → F) (u : ℝ → E) (b : E)
    (hR : ContinuousAt R (1, b))
    (hu : Tendsto u (𝓝[<] (1 : ℝ)) (𝓝 b))
    (hroot : (fun t => R (t, u t)) =ᶠ[𝓝[<] (1 : ℝ)] (fun _ => 0)) :
    R (1, b) = 0 := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hp := ht.prodMk_nhds hu
  exact tendsto_nhds_unique (hR.tendsto.comp hp)
    (tendsto_const_nhds.congr' hroot.symm)

open ExactMSA.MultiTailMixture

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual residual is polynomial in the amplitudes and coupling; all
denominators and exponential factors depend only on the fixed state data. -/
theorem actual_residual_analytic (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (D G : ℝ → TailMatrix T N) (t : ℝ)
    (hD : ∀ u i j, AnalyticAt ℝ (fun s => D s u i j) t)
    (hG : ∀ u i j, AnalyticAt ℝ (fun s => G s u i j) t) :
    AnalyticAt ℝ (fun s => residual z rho sigma K (s, (D s, G s))) t := by
  unfold ExactMSA.MultiTailMixture.residual
  apply AnalyticAt.prod
  all_goals apply analyticAt_pi_iff.mpr; intro u
  all_goals apply analyticAt_pi_iff.mpr; intro i
  all_goals apply analyticAt_pi_iff.mpr; intro j
  all_goals simp only [firstLHS, secondLHS, secondRHS, dressedQhat, Qhat,
    amplitudeA, amplitudeQp, W, C, MSAMixture.mixDA, MSAMixture.mixDqp,
    MSAMixture.mixM, MSAMixture.mixN, MSAMixture.Wt, MSAMixture.Ct, MSAMixture.gam]
  all_goals fun_prop

def amplitudeSeries (a : ℕ → TailMatrix T N × TailMatrix T N) (t : ℝ) :
    TailMatrix T N × TailMatrix T N :=
  ((fun u i j => ∑' n, (a n).1 u i j * t ^ n),
   (fun u i j => ∑' n, (a n).2 u i j * t ^ n))

omit [Fintype T] in
theorem amplitudeSeries_abel (a : ℕ → TailMatrix T N × TailMatrix T N)
    (b : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum (fun n => (a n).1 u i j) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (a n).2 u i j) (b.2 u i j)) :
    Tendsto (amplitudeSeries a) (𝓝[<] (1 : ℝ)) (𝓝 b) := by
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro u
    apply tendsto_pi_nhds.mpr
    intro i
    exact coordinatewise_abel _ _ (hD u i)
  · apply tendsto_pi_nhds.mpr
    intro u
    apply tendsto_pi_nhds.mpr
    intro i
    exact coordinatewise_abel _ _ (hG u i)

/-- Convergence at physical coupling transfers the actual BH root identity to
the endpoint. The identity just below the endpoint is an explicit premise. -/
theorem actual_msa_root_of_endpoint_convergence
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (a : ℕ → TailMatrix T N × TailMatrix T N)
    (b : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum (fun n => (a n).1 u i j) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (a n).2 u i j) (b.2 u i j))
    (hroot : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      IsRoot z rho sigma (t • K) (amplitudeSeries a t).1 (amplitudeSeries a t).2) :
    IsRoot z rho sigma K b.1 b.2 := by
  have hr : (fun t => residual z rho sigma K (t, amplitudeSeries a t))
      =ᶠ[𝓝[<] (1 : ℝ)] (fun _ => 0) := by
    filter_upwards [hroot] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mpr ht
  have hend := residual_at_limit (residual z rho sigma K) (amplitudeSeries a) b
    (residual_contDiff z rho sigma K).continuous.continuousAt
    (amplitudeSeries_abel a b hD hG) hr
  simpa only [one_smul] using (residual_eq_zero_iff z rho sigma K b.1 b.2 1).mp hend

/-- The valid contrapositive: if no real BH root exists, the interior root
series cannot have a finite real endpoint sum in every component. -/
theorem not_endpoint_convergence_of_no_real_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (a : ℕ → TailMatrix T N × TailMatrix T N)
    (hnoroot : ¬ ∃ D G, IsRoot z rho sigma K D G)
    (hroot : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      IsRoot z rho sigma (t • K) (amplitudeSeries a t).1 (amplitudeSeries a t).2) :
    ¬ ∃ b : TailMatrix T N × TailMatrix T N,
      (∀ u i j, HasSum (fun n => (a n).1 u i j) (b.1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (a n).2 u i j) (b.2 u i j)) := by
  rintro ⟨b, hD, hG⟩
  exact hnoroot ⟨b.1, b.2,
    actual_msa_root_of_endpoint_convergence z rho sigma K a b hD hG hroot⟩

/-- A root identity only near zero propagates throughout the open real unit
interval. Endpoint convergence supplies the analyticity needed for the identity
theorem; no assumption about roots near t=1 is required. -/
theorem actual_msa_root_inside_of_local_identity
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (a : ℕ → TailMatrix T N × TailMatrix T N)
    (b : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum (fun n => (a n).1 u i j) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (a n).2 u i j) (b.2 u i j))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • K) (amplitudeSeries a t).1 (amplitudeSeries a t).2) :
    ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      IsRoot z rho sigma (t • K) (amplitudeSeries a t).1 (amplitudeSeries a t).2 := by
  have ha : AnalyticOnNhd ℝ
      (fun t => residual z rho sigma K (t, amplitudeSeries a t)) (Set.Ioo (-1 : ℝ) 1) := by
    intro t ht
    exact actual_residual_analytic z rho sigma K
      (fun t => (amplitudeSeries a t).1) (fun t => (amplitudeSeries a t).2) t
      (fun u i j => powerSeries_analytic_of_hasSum _ _ (hD u i j) t ht)
      (fun u i j => powerSeries_analytic_of_hasSum _ _ (hG u i j) t ht)
  have hzero : (fun t => residual z rho sigma K (t, amplitudeSeries a t))
      =ᶠ[𝓝 (0 : ℝ)] 0 := by
    filter_upwards [hlocal] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mpr ht
  have he := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_Ioo (-1 : ℝ) 1).isPreconnected (by norm_num) hzero
  intro t ht
  exact (residual_eq_zero_iff _ _ _ _ _ _ _).mp (he ht)

/-- The actual MSA version of the valid convergence implication: a locally
identified root series that converges at one continues as real solutions on
(-1,1), tends to its endpoint sum, and that sum solves the exact residual.
This asserts neither positivity nor uniqueness among all real solutions. -/
theorem actual_msa_endpoint_of_local_identity
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (a : ℕ → TailMatrix T N × TailMatrix T N)
    (b : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum (fun n => (a n).1 u i j) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (a n).2 u i j) (b.2 u i j))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • K) (amplitudeSeries a t).1 (amplitudeSeries a t).2) :
    IsRoot z rho sigma K b.1 b.2 ∧
      Tendsto (amplitudeSeries a) (𝓝[<] (1 : ℝ)) (𝓝 b) ∧
      ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        IsRoot z rho sigma (t • K) (amplitudeSeries a t).1 (amplitudeSeries a t).2 := by
  have hi := actual_msa_root_inside_of_local_identity z rho sigma K a b hD hG hlocal
  refine ⟨actual_msa_root_of_endpoint_convergence z rho sigma K a b hD hG ?_,
    amplitudeSeries_abel a b hD hG, hi⟩
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with t ht
  exact hi t ht

theorem not_endpoint_convergence_of_local_identity_and_no_real_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (a : ℕ → TailMatrix T N × TailMatrix T N)
    (hnoroot : ¬ ∃ D G, IsRoot z rho sigma K D G)
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsRoot z rho sigma (t • K) (amplitudeSeries a t).1 (amplitudeSeries a t).2) :
    ¬ ∃ b : TailMatrix T N × TailMatrix T N,
      (∀ u i j, HasSum (fun n => (a n).1 u i j) (b.1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (a n).2 u i j) (b.2 u i j)) := by
  rintro ⟨b, hD, hG⟩
  exact hnoroot ⟨b.1, b.2,
    (actual_msa_endpoint_of_local_identity z rho sigma K a b hD hG hlocal).1⟩

end FMSA.Paper.Abel

/-! Axiom-footprint gates for every theorem in this extension module. -/

/-- info: 'FMSA.Paper.Abel.coordinatewise_abel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.coordinatewise_abel

/-- info: 'FMSA.Paper.Abel.powerSeries_analytic_of_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.powerSeries_analytic_of_hasSum

/-- info: 'FMSA.Paper.Abel.residual_at_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.residual_at_limit

/-- info: 'FMSA.Paper.Abel.actual_residual_analytic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.actual_residual_analytic

/-- info: 'FMSA.Paper.Abel.amplitudeSeries_abel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.amplitudeSeries_abel

/-- info: 'FMSA.Paper.Abel.actual_msa_root_of_endpoint_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.actual_msa_root_of_endpoint_convergence

/-- info: 'FMSA.Paper.Abel.not_endpoint_convergence_of_no_real_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.not_endpoint_convergence_of_no_real_root

/-- info: 'FMSA.Paper.Abel.actual_msa_root_inside_of_local_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.actual_msa_root_inside_of_local_identity

/-- info: 'FMSA.Paper.Abel.actual_msa_endpoint_of_local_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.actual_msa_endpoint_of_local_identity

/-- info: 'FMSA.Paper.Abel.not_endpoint_convergence_of_local_identity_and_no_real_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Abel.not_endpoint_convergence_of_local_identity_and_no_real_root
