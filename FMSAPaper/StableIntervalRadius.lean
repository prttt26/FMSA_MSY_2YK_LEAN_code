import FMSAPaper.ActualAnalyticTaylor

/-! Taylor convergence on the initial stable coupling interval is equivalent
to its endpoint not exceeding the common radius. Endpoints may be infinite;
equality is allowed because the unstable endpoint is excluded. Analyticity
of the selected branch, or explicit actual-root regularity, remains stated. -/
noncomputable section
open Filter Topology
open scoped ContDiff
namespace FMSA.Paper.StableIntervalRadius
open FormalMultilinearSeries ExactMSA.BSource ExactMSA.MultiTailMixture
open TaylorRoot FoldRadius AnalyticTaylor ActualAnalyticTaylor ActualAnalyticBranch

def initialCouplings (bound : ENNReal) : Set ℝ :=
  {r | 0 <= r ∧ ENNReal.ofReal r < bound}

def ScalarSummableBefore (a : ℕ → ℝ) (bound : ENNReal) : Prop :=
  ∀ r ∈ initialCouplings bound, Summable (fun n => a n * r ^ n)

theorem radius_bound_of_summable_at (a : ℕ → ℝ) (r : ℝ) (hr : 0 <= r)
    (hs : Summable (fun n => a n * r ^ n)) :
    ENNReal.ofReal r <= (ofScalars ℝ a).radius := by
  let p := ofScalars ℝ a
  let q : NNReal := NNReal.mk r hr
  have ht : Tendsto (fun n => ‖p n‖ * (q : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [p, q, NNReal.coe_mk, ofScalars_norm, norm_mul, norm_pow,
      Real.norm_of_nonneg hr, norm_zero] using hs.tendsto_atTop_zero.norm
  have h := p.le_radius_of_tendsto ht
  change ENNReal.ofReal r <= p.radius
  rw [ENNReal.ofReal_eq_coe_nnreal hr]
  exact h

theorem scalar_summable_before_iff (a : ℕ → ℝ) (bound : ENNReal) :
    ScalarSummableBefore a bound ↔ bound <= (ofScalars ℝ a).radius := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨r, hr, hlt, hrb⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    exact (not_le_of_gt hlt) (radius_bound_of_summable_at a r hr (h r ⟨hr, hrb⟩))
  · intro h r hr
    have hm : r ∈ Metric.eball (0 : ℝ) (ofScalars ℝ a).radius := by
      rw [mem_eball_zero_iff, ← ofReal_norm, Real.norm_of_nonneg hr.1]
      exact hr.2.trans_le h
    simpa only [ofScalars_apply_eq, smul_eq_mul] using (ofScalars ℝ a).summable hm

theorem scalar_all_nonneg_summable_iff (a : ℕ → ℝ) :
    (∀ r : ℝ, 0 <= r → Summable (fun n => a n * r ^ n)) ↔
      (ofScalars ℝ a).radius = ⊤ := by
  simpa [ScalarSummableBefore, initialCouplings] using scalar_summable_before_iff a ⊤

theorem scalar_hasSum_jet_before (f : ℝ → ℝ) (bound : ENNReal)
    (hf : AnalyticOnNhd ℝ f (initialCouplings bound))
    (r : ℝ) (hr : r ∈ initialCouplings bound)
    (hrad : ENNReal.ofReal r < (ofScalars ℝ (jet f)).radius) :
    HasSum (fun n => jet f n * r ^ n) (f r) := by
  have hb : (0 : ENNReal) < bound := bot_le.trans_lt hr.2
  have hf0 : AnalyticAt ℝ f 0 := hf 0 ⟨le_rfl, by simpa using hb⟩
  have hfa : AnalyticOnNhd ℝ f (Set.Icc 0 r) := by
    apply hf.mono
    intro x hx
    exact ⟨hx.1, (ENNReal.ofReal_le_ofReal hx.2).trans_lt hr.2⟩
  have hsa : AnalyticOnNhd ℝ (ofScalars ℝ (jet f)).sum (Set.Icc 0 r) := by
    intro x hx
    apply (ofScalars ℝ (jet f)).analyticOnNhd x
    rw [mem_eball_zero_iff, ← ofReal_norm, Real.norm_of_nonneg hx.1]
    exact (ENNReal.ofReal_le_ofReal hx.2).trans_lt hrad
  have he : f r = (ofScalars ℝ (jet f)).sum r :=
    hfa.eqOn_of_preconnected_of_eventuallyEq hsa
      (convex_Icc (0 : ℝ) r).isPreconnected ⟨le_rfl, hr.1⟩
      (eventually_eq_jet_sum f hf0) ⟨hr.1, le_rfl⟩
  rw [he]
  have hm : r ∈ Metric.eball (0 : ℝ) (ofScalars ℝ (jet f)).radius := by
    rw [mem_eball_zero_iff, ← ofReal_norm, Real.norm_of_nonneg hr.1]
    exact hrad
  simpa only [ofScalars_apply_eq, smul_eq_mul, FormalMultilinearSeries.sum] using
    ((ofScalars ℝ (jet f)).summable hm).hasSum

variable {N : ℕ} {T : Type*} [Fintype T]

def AmplitudeSummableBefore (a : ℕ → TailMatrix T N × TailMatrix T N) (bound : ENNReal) : Prop :=
  ∀ r ∈ initialCouplings bound,
    (∀ u i j, Summable (fun n => (a n).1 u i j * r ^ n)) ∧
    (∀ u i j, Summable (fun n => (a n).2 u i j * r ^ n))

def AmplitudeHasSumBefore (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal) : Prop :=
  ∀ r ∈ initialCouplings bound,
    (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j * r ^ n) ((p r).1 u i j)) ∧
    (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j * r ^ n) ((p r).2 u i j))

omit [Fintype T] in
theorem amplitude_summable_before_iff
    (a : ℕ → TailMatrix T N × TailMatrix T N) (bound : ENNReal) :
    AmplitudeSummableBefore a bound ↔ bound <= amplitudeRadius a := by
  constructor
  · intro h
    apply le_iInf
    intro u
    apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_min
    · apply (scalar_summable_before_iff _ bound).mp
      exact fun r hr => (h r hr).1 u i j
    · apply (scalar_summable_before_iff _ bound).mp
      exact fun r hr => (h r hr).2 u i j
  · intro h r hr
    obtain ⟨hD, hG⟩ := hasSum_inside_amplitudeRadius a r hr.1 (hr.2.trans_le h)
    exact ⟨fun u i j => (hD u i j).summable, fun u i j => (hG u i j).summable⟩

omit [Fintype T] in
theorem nonconvergence_witness_before
    (a : ℕ → TailMatrix T N × TailMatrix T N) (bound : ENNReal)
    (hlt : amplitudeRadius a < bound) :
    ∃ r : ℝ, r ∈ initialCouplings bound ∧ amplitudeRadius a < ENNReal.ofReal r ∧
      ¬ ((∀ u i j, Summable (fun n => (a n).1 u i j * r ^ n)) ∧
        (∀ u i j, Summable (fun n => (a n).2 u i j * r ^ n))) := by
  obtain ⟨r, hr, hR, hb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  refine ⟨r, ⟨hr, hb⟩, hR, ?_⟩
  intro hs
  have hle : ENNReal.ofReal r <= amplitudeRadius a := by
    apply le_iInf
    intro u
    apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_min
    · exact radius_bound_of_summable_at _ r hr (hs.1 u i j)
    · exact radius_bound_of_summable_at _ r hr (hs.2 u i j)
  exact (not_le_of_gt hR) hle

theorem analytic_branch_converges_before_iff
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal)
    (hp : AnalyticOnNhd ℝ p (initialCouplings bound)) :
    AmplitudeHasSumBefore p bound ↔ bound <= amplitudeRadius (branchCoefficients p) := by
  constructor
  · intro h
    apply (amplitude_summable_before_iff _ bound).mp
    intro r hr
    exact ⟨fun u i j => ((h r hr).1 u i j).summable,
      fun u i j => ((h r hr).2 u i j).summable⟩
  · intro h r hr
    have hbound (u : T) (i j : Fin N) : amplitudeRadius (branchCoefficients p) <= min
        (ofScalars ℝ (fun n => (branchCoefficients p n).1 u i j)).radius
        (ofScalars ℝ (fun n => (branchCoefficients p n).2 u i j)).radius :=
      iInf_le_of_le u (iInf_le_of_le i (iInf_le_of_le j le_rfl))
    constructor <;> intro u i j
    · exact scalar_hasSum_jet_before _ bound
        (fun x hx => (analyticAt_components p x (hp x hx)).1 u i j) r hr
        (hr.2.trans_le (h.trans ((hbound u i j).trans (min_le_left _ _))))
    · exact scalar_hasSum_jet_before _ bound
        (fun x hx => (analyticAt_components p x (hp x hx)).2 u i j) r hr
        (hr.2.trans_le (h.trans ((hbound u i j).trans (min_le_right _ _))))

theorem analytic_branch_entire_iff
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : AnalyticOnNhd ℝ p (initialCouplings ⊤)) :
    AmplitudeHasSumBefore p ⊤ ↔ amplitudeRadius (branchCoefficients p) = ⊤ := by
  simpa only [top_le_iff] using analytic_branch_converges_before_iff p ⊤ hp

theorem actual_regular_branch_analytic_before
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal)
    (hp0 : ContinuousAt p 0) (hp : ContinuousOn p (initialCouplings bound))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hroot : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ initialCouplings bound,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible) :
    AnalyticOnNhd ℝ p (initialCouplings bound) := by
  intro t ht
  by_cases hz : t = 0
  · subst t
    exact actual_regular_root_analyticAt z rho sigma K p 0 hp0 hlocal (hinv 0 ht)
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
    have ho : IsOpen {x : ℝ | ENNReal.ofReal x < bound} :=
      isOpen_lt ENNReal.continuous_ofReal continuous_const
    have hI : initialCouplings bound ∈ 𝓝 t := by
      filter_upwards [isOpen_Ioi.mem_nhds ht0, ho.mem_nhds ht.2] with x hx hx'
      exact ⟨hx.le, hx'⟩
    apply actual_regular_root_analyticAt z rho sigma K p t (hp.continuousAt hI) _ (hinv t ht)
    filter_upwards [hI] with x hx
    exact hroot x hx

/-- Actual BH interface: branch continuity, roots and invertible amplitude
Jacobians imply the radius criterion. The identification of bound with the
physical first canonicity loss is an external obligation, not an axiom here. -/
theorem actual_regular_branch_converges_before_iff
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal)
    (hp0 : ContinuousAt p 0) (hp : ContinuousOn p (initialCouplings bound))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hroot : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ initialCouplings bound,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible) :
    AmplitudeHasSumBefore p bound ↔ bound <= amplitudeRadius (branchCoefficients p) :=
  analytic_branch_converges_before_iff p bound
    (actual_regular_branch_analytic_before z rho sigma K p bound hp0 hp hlocal hroot hinv)

end FMSA.Paper.StableIntervalRadius

/-- info: 'FMSA.Paper.StableIntervalRadius.radius_bound_of_summable_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.radius_bound_of_summable_at

/-- info: 'FMSA.Paper.StableIntervalRadius.scalar_summable_before_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.scalar_summable_before_iff

/-- info: 'FMSA.Paper.StableIntervalRadius.scalar_all_nonneg_summable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.scalar_all_nonneg_summable_iff

/-- info: 'FMSA.Paper.StableIntervalRadius.scalar_hasSum_jet_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.scalar_hasSum_jet_before

/-- info: 'FMSA.Paper.StableIntervalRadius.amplitude_summable_before_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.amplitude_summable_before_iff

/-- info: 'FMSA.Paper.StableIntervalRadius.nonconvergence_witness_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.nonconvergence_witness_before

/-- info: 'FMSA.Paper.StableIntervalRadius.analytic_branch_converges_before_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.analytic_branch_converges_before_iff

/-- info: 'FMSA.Paper.StableIntervalRadius.analytic_branch_entire_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.analytic_branch_entire_iff

/-- info: 'FMSA.Paper.StableIntervalRadius.actual_regular_branch_analytic_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.actual_regular_branch_analytic_before

/-- info: 'FMSA.Paper.StableIntervalRadius.actual_regular_branch_converges_before_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.StableIntervalRadius.actual_regular_branch_converges_before_iff
