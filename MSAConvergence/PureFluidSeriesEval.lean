import Mathlib

set_option linter.style.header false

/-! Evaluating one-variable power series at a point of absolute convergence, as a ring
homomorphism on the absolutely convergent ones, with monotonicity and continuity for series with
nonnegative coefficients. -/

noncomputable section
open Finset PowerSeries
namespace FMSA.Convergence.PureFluidSeriesEval

/-- Absolute convergence at `τ`. -/
def Abs (τ : ℝ) (S : PowerSeries ℝ) : Prop := Summable fun n => ‖coeff n S * τ ^ n‖

/-- The sum at `τ`. -/
def ev (τ : ℝ) (S : PowerSeries ℝ) : ℝ := ∑' n, coeff n S * τ ^ n

/-- Nonnegative coefficients. -/
def CN (S : PowerSeries ℝ) : Prop := ∀ n, 0 ≤ coeff n S

theorem Abs.summable {τ : ℝ} {S : PowerSeries ℝ} (h : Abs τ S) :
    Summable fun n => coeff n S * τ ^ n := h.of_norm

theorem coeff_mul_pow (S S' : PowerSeries ℝ) (τ : ℝ) (n : ℕ) :
    coeff n (S * S') * τ ^ n =
      ∑ kl ∈ antidiagonal n, (coeff kl.1 S * τ ^ kl.1) * (coeff kl.2 S' * τ ^ kl.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine sum_congr rfl fun kl hkl => ?_
  rw [← mem_antidiagonal.mp hkl, pow_add]
  ring

theorem Abs.mul {τ : ℝ} {S S' : PowerSeries ℝ} (h : Abs τ S) (h' : Abs τ S') : Abs τ (S * S') := by
  have := summable_norm_sum_mul_antidiagonal_of_summable_norm h h'
  refine this.congr fun n => ?_
  rw [coeff_mul_pow]

theorem ev_mul {τ : ℝ} {S S' : PowerSeries ℝ} (h : Abs τ S) (h' : Abs τ S') :
    ev τ (S * S') = ev τ S * ev τ S' := by
  have := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h h'
  simp only [ev]
  rw [this]
  exact tsum_congr fun n => coeff_mul_pow S S' τ n

theorem Abs.add {τ : ℝ} {S S' : PowerSeries ℝ} (h : Abs τ S) (h' : Abs τ S') : Abs τ (S + S') := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (Summable.add h h')
  rw [map_add, add_mul]
  exact norm_add_le _ _

theorem ev_add {τ : ℝ} {S S' : PowerSeries ℝ} (h : Abs τ S) (h' : Abs τ S') :
    ev τ (S + S') = ev τ S + ev τ S' := by
  simp only [ev, map_add, add_mul]
  exact h.summable.tsum_add h'.summable

theorem coeff_C_mul_pow (a τ : ℝ) (n : ℕ) :
    coeff n (C a : PowerSeries ℝ) * τ ^ n = if n = 0 then a else 0 := by
  rw [PowerSeries.coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem abs_C (τ a : ℝ) : Abs τ (C a) := by
  have : (fun n => ‖coeff n (C a : PowerSeries ℝ) * τ ^ n‖) = fun n => if n = 0 then ‖a‖ else 0 := by
    funext n; rw [coeff_C_mul_pow]; split_ifs <;> simp
  unfold Abs; rw [this]
  exact summable_of_ne_finset_zero (s := {0}) fun n hn => by simp at hn; simp [hn]

theorem ev_C (τ a : ℝ) : ev τ (C a) = a := by
  simp only [ev]
  rw [tsum_eq_single 0 (fun n hn => by rw [coeff_C_mul_pow, if_neg hn])]
  rw [coeff_C_mul_pow, if_pos rfl]

theorem abs_one (τ : ℝ) : Abs τ (1 : PowerSeries ℝ) := by
  simpa using abs_C τ 1

theorem ev_one (τ : ℝ) : ev τ (1 : PowerSeries ℝ) = 1 := by
  simpa using ev_C τ 1

theorem abs_X (τ : ℝ) : Abs τ (X : PowerSeries ℝ) := by
  unfold Abs
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  simp at hn
  simp [PowerSeries.coeff_X, hn]

theorem ev_X (τ : ℝ) : ev τ (X : PowerSeries ℝ) = τ := by
  simp only [ev]
  rw [tsum_eq_single 1 (fun n hn => by simp [PowerSeries.coeff_X, hn])]
  simp [PowerSeries.coeff_X]

theorem Abs.neg {τ : ℝ} {S : PowerSeries ℝ} (h : Abs τ S) : Abs τ (-S) := by
  refine h.congr fun n => ?_
  simp [neg_mul]

theorem ev_neg {τ : ℝ} (S : PowerSeries ℝ) : ev τ (-S) = -ev τ S := by
  simp only [ev, map_neg, neg_mul]
  exact tsum_neg

theorem Abs.sub {τ : ℝ} {S S' : PowerSeries ℝ} (h : Abs τ S) (h' : Abs τ S') : Abs τ (S - S') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem ev_sub {τ : ℝ} {S S' : PowerSeries ℝ} (h : Abs τ S) (h' : Abs τ S') :
    ev τ (S - S') = ev τ S - ev τ S' := by
  rw [sub_eq_add_neg, ev_add h h'.neg, ev_neg, sub_eq_add_neg]

theorem abs_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) {τ : ℝ}
    (h : ∀ i ∈ s, Abs τ (f i)) : Abs τ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using abs_C τ 0
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem ev_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) {τ : ℝ}
    (h : ∀ i ∈ s, Abs τ (f i)) : ev τ (∑ i ∈ s, f i) = ∑ i ∈ s, ev τ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ev_C τ 0
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha,
      ev_add (h a (mem_insert_self a s)) (abs_sum s f fun i hi => h i (mem_insert_of_mem hi)),
      ih fun i hi => h i (mem_insert_of_mem hi)]

theorem ev_zero_point (S : PowerSeries ℝ) : ev 0 S = coeff 0 S := by
  simp only [ev]
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- Absolute convergence passes to smaller points. -/
theorem Abs.mono {τ τ' : ℝ} {S : PowerSeries ℝ} (h : Abs τ' S) (hle : |τ| ≤ |τ'|) : Abs τ S := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h
  simp only [norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hle n) (abs_nonneg _)

/-- Nonnegative coefficients make the sum monotone on the nonnegative ray. -/
theorem ev_mono {S : PowerSeries ℝ} (hS : CN S) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : Abs b S) : ev a S ≤ ev b S := by
  have hA : Abs a S := hb.mono (by rw [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]; exact hab)
  exact hA.summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab n) (hS n)) hb.summable

theorem ev_nonneg {S : PowerSeries ℝ} (hS : CN S) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ ev a S :=
  tsum_nonneg fun n => mul_nonneg (hS n) (pow_nonneg ha n)

/-- A single term is below the sum. -/
theorem coeff_mul_pow_le_ev {S : PowerSeries ℝ} (hS : CN S) {a : ℝ} (ha : 0 ≤ a) (h : Abs a S)
    (n : ℕ) : coeff n S * a ^ n ≤ ev a S :=
  h.summable.le_tsum n fun m _ => mul_nonneg (hS m) (pow_nonneg ha m)

/-- Continuity on the part of the ray below a point of absolute convergence. -/
theorem ev_continuousOn_Icc {S : PowerSeries ℝ} {b : ℝ} (hb0 : 0 ≤ b) (hb : Abs b S) :
    ContinuousOn (fun τ => ev τ S) (Set.Icc 0 b) := by
  have hcont : ContinuousOn (fun τ => ∑' n, coeff n S * τ ^ n) (Set.Icc 0 b) := by
    refine continuousOn_tsum (u := fun n => ‖coeff n S * b ^ n‖)
      (fun n => (continuous_const.mul (continuous_pow n)).continuousOn) hb ?_
    intro n τ hτ
    simp only [norm_mul, norm_pow, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ?_ n) (abs_nonneg _)
    rw [abs_of_nonneg hτ.1, abs_of_nonneg hb0]; exact hτ.2
  exact hcont

theorem ev_continuousOn_Ico {S : PowerSeries ℝ} {R : ℝ} (hab : ∀ τ ∈ Set.Ico 0 R, Abs τ S) :
    ContinuousOn (fun τ => ev τ S) (Set.Ico 0 R) := by
  intro τ hτ
  obtain ⟨b, hb1, hb2⟩ := exists_between hτ.2
  have h0b : 0 ≤ b := hτ.1.trans hb1.le
  have hc := (ev_continuousOn_Icc h0b (hab b ⟨h0b, hb2⟩)) τ ⟨hτ.1, hb1.le⟩
  have hmem : Set.Icc 0 b ∈ nhdsWithin τ (Set.Ico 0 R) := by
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ (Iic_mem_nhds hb1)) ?_
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.1, hx2⟩
  exact (hc.mono_of_mem_nhdsWithin hmem)

/-- Bounded sums below `R` give summability at `R`, for nonnegative coefficients. -/
theorem summable_at_endpoint {S : PowerSeries ℝ} (hS : CN S) {R B : ℝ} (hR : 0 < R)
    (hab : ∀ τ ∈ Set.Ico 0 R, Abs τ S) (hB : ∀ τ ∈ Set.Ico 0 R, ev τ S ≤ B) :
    Summable fun n => coeff n S * R ^ n := by
  refine summable_of_sum_range_le (c := B) (fun n => mul_nonneg (hS n) (pow_nonneg hR.le n)) ?_
  intro N
  have hlim : Filter.Tendsto (fun τ => ∑ n ∈ range N, coeff n S * τ ^ n)
      (nhdsWithin R (Set.Iio R)) (nhds (∑ n ∈ range N, coeff n S * R ^ n)) := by
    apply Continuous.tendsto' (by fun_prop) R _ rfl |>.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  have hev : ∀ᶠ τ in nhdsWithin R (Set.Iio R), τ ∈ Set.Ico 0 R := by
    filter_upwards [Ioo_mem_nhdsLT hR] with τ hτ using ⟨hτ.1.le, hτ.2⟩
  filter_upwards [hev] with τ hτ
  have hsum := (hab τ hτ).summable.sum_le_tsum (range N)
    (fun n _ => mul_nonneg (hS n) (pow_nonneg hτ.1 n))
  exact hsum.trans (hB τ hτ)

end FMSA.Convergence.PureFluidSeriesEval

/-- info: 'FMSA.Convergence.PureFluidSeriesEval.Abs.summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.Abs.summable
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.coeff_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.coeff_mul_pow
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.Abs.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.Abs.mul
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_mul
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.Abs.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.Abs.add
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_add
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.coeff_C_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.coeff_C_mul_pow
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.abs_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.abs_C
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_C
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.abs_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.abs_one
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_one
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.abs_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.abs_X
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_X
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.Abs.neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.Abs.neg
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_neg
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.Abs.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.Abs.sub
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_sub
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.abs_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.abs_sum
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_sum
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_zero_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_zero_point
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.Abs.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.Abs.mono
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_mono
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_nonneg
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.coeff_mul_pow_le_ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.coeff_mul_pow_le_ev
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_continuousOn_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_continuousOn_Icc
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.ev_continuousOn_Ico' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.ev_continuousOn_Ico
/-- info: 'FMSA.Convergence.PureFluidSeriesEval.summable_at_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidSeriesEval.summable_at_endpoint
