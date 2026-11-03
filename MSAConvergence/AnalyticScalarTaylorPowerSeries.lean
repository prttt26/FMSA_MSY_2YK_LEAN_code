import MSAConvergence.PureFluidHPathFormalSubstitution
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option linter.style.header false

/-! Transfer a real analytic germ at zero to a one-variable algebraic
power series, with a verified coefficient interface. -/
noncomputable section
open Filter Topology
namespace FMSA.Convergence.AnalyticScalarTaylorPowerSeries

/-- An analytic real germ represented by a formal algebraic power series.
The witness is Mathlib's convergent scalar formal multilinear series. -/
def HasTaylorPowerSeriesAt (f : ℝ → ℝ) (S : PowerSeries ℝ) : Prop :=
  ∃ p : FormalMultilinearSeries ℝ ℝ ℝ,
    HasFPowerSeriesAt f p 0 ∧
    ∀ n, p.coeff n = PowerSeries.coeff n S

/-- Every real analytic germ at zero admits an algebraic Taylor series. -/
theorem exists_taylorPowerSeries (f : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) :
    ∃ S : PowerSeries ℝ, HasTaylorPowerSeriesAt f S := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨PowerSeries.mk (fun n => p.coeff n), p, hp, ?_⟩
  intro n
  simp

/-- The algebraic Taylor series of a real analytic germ is unique. -/
theorem taylorPowerSeries_unique (f : ℝ → ℝ)
    (S R : PowerSeries ℝ)
    (hS : HasTaylorPowerSeriesAt f S)
    (hR : HasTaylorPowerSeriesAt f R) : S = R := by
  obtain ⟨p, hp, hpS⟩ := hS
  obtain ⟨q, hq, hqR⟩ := hR
  have hpq := hp.eq_formalMultilinearSeries hq
  ext n
  rw [← hpS n, ← hqR n, hpq]

/-- Eventual equality of real analytic germs preserves their Taylor series. -/
theorem taylorPowerSeries_eq_of_eventually
    (f g : ℝ → ℝ) (S R : PowerSeries ℝ)
    (hS : HasTaylorPowerSeriesAt f S)
    (hR : HasTaylorPowerSeriesAt g R)
    (hfg : f =ᶠ[𝓝 0] g) : S = R := by
  obtain ⟨p, hp, hpS⟩ := hS
  obtain ⟨q, hq, hqR⟩ := hR
  have hpq := hp.eq_formalMultilinearSeries_of_eventually hq hfg
  ext n
  rw [← hpS n, ← hqR n, hpq]

/-- The Taylor transfer preserves a constant germ. -/
theorem taylor_const (a : ℝ) :
    HasTaylorPowerSeriesAt (fun _ : ℝ => a) (PowerSeries.C a) := by
  refine ⟨constFormalMultilinearSeries ℝ ℝ a,
    hasFPowerSeriesAt_const, ?_⟩
  intro n
  cases n with
  | zero => simp [FormalMultilinearSeries.coeff]
  | succ n => simp [FormalMultilinearSeries.coeff]

/-- The Taylor transfer preserves sums of analytic real germs. -/
theorem HasTaylorPowerSeriesAt.add
    {f g : ℝ → ℝ} {S R : PowerSeries ℝ}
    (hf : HasTaylorPowerSeriesAt f S)
    (hg : HasTaylorPowerSeriesAt g R) :
    HasTaylorPowerSeriesAt (f + g) (S + R) := by
  obtain ⟨p, hp, hpS⟩ := hf
  obtain ⟨q, hq, hqR⟩ := hg
  refine ⟨p + q, hp.add hq, ?_⟩
  intro n
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.add_apply,
    ContinuousMultilinearMap.add_apply, map_add]
  exact congrArg₂ (· + ·) (hpS n) (hqR n)

/-- The Cauchy product of two analytic scalar expansions is again the
local expansion of their pointwise product. -/
theorem hasFPowerSeriesAt_mul_ofScalars
    {f g : ℝ → ℝ} {p q : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt f p 0)
    (hq : HasFPowerSeriesAt g q 0) :
    HasFPowerSeriesAt (fun x => f x * g x)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n => ∑ kl ∈ Finset.antidiagonal n,
          p.coeff kl.1 * q.coeff kl.2)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  have hpe := hasFPowerSeriesAt_iff.mp hp
  have hqe := hasFPowerSeriesAt_iff.mp hq
  have hpb : ∀ᶠ x : ℝ in 𝓝 0,
      x ∈ Metric.eball (0 : ℝ) p.radius :=
    Metric.eball_mem_nhds 0 hp.radius_pos
  have hqb : ∀ᶠ x : ℝ in 𝓝 0,
      x ∈ Metric.eball (0 : ℝ) q.radius :=
    Metric.eball_mem_nhds 0 hq.radius_pos
  filter_upwards [hpe, hqe, hpb, hqb] with x hpx hqx hxp hxq
  have hpn : Summable (fun n => ‖x ^ n * p.coeff n‖) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
      using p.summable_norm_apply hxp
  have hqn : Summable (fun n => ‖x ^ n * q.coeff n‖) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
      using q.summable_norm_apply hxq
  have hconv :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hpn hqn).of_norm.hasSum
  have hmul := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hpn hqn
  simp only [zero_add, smul_eq_mul] at hpx hqx
  rw [← hmul, hpx.tsum_eq, hqx.tsum_eq] at hconv
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add,
    smul_eq_mul] using hconv.congr_fun (by
      intro n
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro kl hkl
      have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
      rw [← hsum, pow_add]
      ring)

/-- The Taylor transfer preserves products of analytic real germs. -/
theorem HasTaylorPowerSeriesAt.mul
    {f g : ℝ → ℝ} {S R : PowerSeries ℝ}
    (hf : HasTaylorPowerSeriesAt f S)
    (hg : HasTaylorPowerSeriesAt g R) :
    HasTaylorPowerSeriesAt (f * g) (S * R) := by
  obtain ⟨p, hp, hpS⟩ := hf
  obtain ⟨q, hq, hqR⟩ := hg
  refine ⟨FormalMultilinearSeries.ofScalars ℝ
      (fun n => ∑ kl ∈ Finset.antidiagonal n,
        p.coeff kl.1 * q.coeff kl.2),
    hasFPowerSeriesAt_mul_ofScalars hp hq, ?_⟩
  intro n
  rw [FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro kl _
  rw [hpS kl.1, hqR kl.2]

/-- The constant coefficient is the value of the analytic germ at zero. -/
theorem HasTaylorPowerSeriesAt.constantCoeff
    {f : ℝ → ℝ} {S : PowerSeries ℝ}
    (hf : HasTaylorPowerSeriesAt f S) :
    PowerSeries.constantCoeff S = f 0 := by
  obtain ⟨p, hp, hpS⟩ := hf
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hpS 0]
  exact hp.coeff_zero (fun _ => 1)

/-- The Taylor transfer preserves finite sums. -/
theorem HasTaylorPowerSeriesAt.sum
    {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (S : ι → PowerSeries ℝ)
    (h : ∀ i ∈ s, HasTaylorPowerSeriesAt (f i) (S i)) :
    HasTaylorPowerSeriesAt (∑ i ∈ s, f i) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change HasTaylorPowerSeriesAt (fun _ : ℝ => 0) (0 : PowerSeries ℝ)
    simpa using taylor_const 0
  | @insert i s hi ih =>
    have hfi := h i (Finset.mem_insert_self _ _)
    have hrest : ∀ j ∈ s, HasTaylorPowerSeriesAt (f j) (S j) := by
      intro j hj
      exact h j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi] using hfi.add (ih hrest)

/-- The represented algebraic Taylor series actually sums to its
analytic germ throughout some neighborhood of zero. -/
theorem HasTaylorPowerSeriesAt.eventually_hasSum
    {f : ℝ → ℝ} {S : PowerSeries ℝ}
    (hf : HasTaylorPowerSeriesAt f S) :
    ∀ᶠ x : ℝ in 𝓝 0,
      HasSum (fun n => PowerSeries.coeff n S * x ^ n) (f x) := by
  obtain ⟨p, hp, hpS⟩ := hf
  filter_upwards [hasFPowerSeriesAt_iff.mp hp] with x hx
  simpa only [zero_add, smul_eq_mul, mul_comm, hpS] using hx

end FMSA.Convergence.AnalyticScalarTaylorPowerSeries

/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.exists_taylorPowerSeries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.exists_taylorPowerSeries
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.taylorPowerSeries_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.taylorPowerSeries_unique
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.taylorPowerSeries_eq_of_eventually' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.taylorPowerSeries_eq_of_eventually
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.taylor_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.taylor_const
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.add
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.hasFPowerSeriesAt_mul_ofScalars' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.hasFPowerSeriesAt_mul_ofScalars
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.mul
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.constantCoeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.constantCoeff
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.sum
/-- info: 'FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.eventually_hasSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.AnalyticScalarTaylorPowerSeries.HasTaylorPowerSeriesAt.eventually_hasSum
