import FMSAPaper.Pringsheim
import Mathlib.Analysis.Analytic.Constructions

/-! Pringsheim with unrestricted constant term and a fixed sign for all
positive-order coefficients. Finite sign samples do not establish this premise. -/
noncomputable section
open Filter Topology
open scoped BigOperators NNReal ENNReal

namespace FMSA.Paper.SignedPringsheim

open FormalMultilinearSeries

def normalizedCoefficients (a : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else s * a n

theorem radius_add_entire (p q : FormalMultilinearSeries ℝ ℝ ℝ) (hq : q.radius = ⊤) :
    (p + q).radius = p.radius := by
  apply le_antisymm
  · have h := (p + q).min_radius_le_radius_add (-q)
    simpa only [radius_neg, hq, min_eq_left le_top, add_neg_cancel_right] using h
  · simpa only [hq, min_eq_left le_top] using p.min_radius_le_radius_add q

theorem normalized_series_eq (a : ℕ → ℝ) (s : ℝ) :
    ofScalars ℝ (normalizedCoefficients a s) =
      s • ofScalars ℝ a + constFormalMultilinearSeries ℝ ℝ (-s * a 0) := by
  ext n
  cases n with
  | zero => simp [normalizedCoefficients, ofScalars, smul_eq_mul]
  | succ n => simp [normalizedCoefficients, ofScalars, smul_eq_mul]

theorem normalized_radius (a : ℕ → ℝ) (s : ℝ) (hs : s ≠ 0) :
    (ofScalars ℝ (normalizedCoefficients a s)).radius = (ofScalars ℝ a).radius := by
  rw [normalized_series_eq, radius_add_entire _ _ constFormalMultilinearSeries_radius,
    radius_smul_eq _ hs]

theorem normalized_sum (a : ℕ → ℝ) (s x : ℝ)
    (hx : (‖x‖₊ : ENNReal) < (ofScalars ℝ a).radius) :
    (ofScalars ℝ (normalizedCoefficients a s)).sum x = s * ((ofScalars ℝ a).sum x - a 0) := by
  let p := ofScalars ℝ a
  have hc : HasFPowerSeriesOnBall (fun _ : ℝ => -s * a 0)
      (constFormalMultilinearSeries ℝ ℝ (-s * a 0)) 0 p.radius :=
    hasFPowerSeriesOnBall_const.mono hx.pos le_top
  have h := ((p.hasFPowerSeriesOnBall hx.pos).const_smul (c := s)).add hc
  rw [normalized_series_eq]
  have he := h.sum (mem_eball_zero_iff.mpr hx)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add,
    sub_eq_add_neg, mul_add, mul_neg, neg_mul, p] using he.symm

/-- Only positive orders must have one sign. The zero-order coefficient is
removed, and a nonzero scalar can reverse the sign without changing the radius. -/
theorem not_analyticAt_endpoint (a : ℕ → ℝ) (s : ℝ) (hs : s ≠ 0)
    (ha : ∀ n, 0 < n → 0 <= s * a n)
    (R : ℝ) (hR : 0 < R) (hradius : (ofScalars ℝ a).radius = ENNReal.ofReal R)
    (f : ℝ → ℝ) (he : ∀ t ∈ Set.Ioo (0 : ℝ) R, f t = (ofScalars ℝ a).sum t) :
    ¬ AnalyticAt ℝ f R := by
  intro hf
  have hb : ∀ n, 0 <= normalizedCoefficients a s n := by
    intro n
    by_cases hn : n = 0
    · simp [normalizedCoefficients, hn]
    · simpa only [normalizedCoefficients, if_neg hn] using ha n (Nat.pos_of_ne_zero hn)
  apply Pringsheim.not_analyticAt_endpoint (normalizedCoefficients a s) hb R hR
    (by rw [normalized_radius a s hs, hradius]) (fun t => s * (f t - a 0)) _ (by fun_prop)
  intro t ht
  rw [he t ht, normalized_sum]
  rw [hradius, ENNReal.coe_nnreal_eq ‖t‖₊, coe_nnnorm, Real.norm_of_nonneg ht.1.le]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr ht.2

/-- Analytic continuation along a positive interval gives a radius lower
bound under the all-order sign condition and a positive initial radius.
The initial-radius and continuation premises remain explicit. -/
theorem le_radius_of_analytic_continuation (a : ℕ → ℝ) (s : ℝ) (hs : s ≠ 0)
    (ha : ∀ n, 0 < n → 0 <= s * a n)
    (hpos : 0 < (ofScalars ℝ a).radius)
    (b : ℝ) (hb : 0 < b) (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f (Set.Ioo (0 : ℝ) b))
    (he : ∀ t ∈ Set.Ioo (0 : ℝ) b, ENNReal.ofReal t < (ofScalars ℝ a).radius →
      f t = (ofScalars ℝ a).sum t) :
    ENNReal.ofReal b <= (ofScalars ℝ a).radius := by
  by_contra h
  have hlt : (ofScalars ℝ a).radius < ENNReal.ofReal b := lt_of_not_ge h
  have hfinite : (ofScalars ℝ a).radius ≠ ⊤ := ne_top_of_lt hlt
  let R := (ofScalars ℝ a).radius.toReal
  have hR : 0 < R := ENNReal.toReal_pos hpos.ne' hfinite
  have hradius : (ofScalars ℝ a).radius = ENNReal.ofReal R := (ENNReal.ofReal_toReal hfinite).symm
  have hRb : R < b := (ENNReal.ofReal_lt_ofReal_iff hb).mp (by rwa [← hradius])
  apply not_analyticAt_endpoint a s hs ha R hR hradius f _ (hf R ⟨hR, hRb⟩)
  intro t ht
  apply he t ⟨ht.1, ht.2.trans hRb⟩
  rw [hradius]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr ht.2

end FMSA.Paper.SignedPringsheim

/-- info: 'FMSA.Paper.SignedPringsheim.radius_add_entire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SignedPringsheim.radius_add_entire

/-- info: 'FMSA.Paper.SignedPringsheim.normalized_series_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SignedPringsheim.normalized_series_eq

/-- info: 'FMSA.Paper.SignedPringsheim.normalized_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SignedPringsheim.normalized_radius

/-- info: 'FMSA.Paper.SignedPringsheim.normalized_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SignedPringsheim.normalized_sum

/-- info: 'FMSA.Paper.SignedPringsheim.not_analyticAt_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SignedPringsheim.not_analyticAt_endpoint

/-- info: 'FMSA.Paper.SignedPringsheim.le_radius_of_analytic_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SignedPringsheim.le_radius_of_analytic_continuation
