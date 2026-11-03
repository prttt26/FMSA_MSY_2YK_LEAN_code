import MSAConvergence.BHPolynomialJacobian

/-! Small ordinary-kernel rules for proof-carrying REAL interval arithmetic.
Endpoints may be rationals, but every arithmetic corner comparison is a proof
argument. No external interval evaluator or PASS flag is trusted. -/
noncomputable section
namespace FMSA.Convergence.RealIntervalCertificates

/-- Bilinear upper bounds reduce to the four rectangle corners, with NO
sign assumptions on the interval or the enclosed point. -/
theorem mul_upper {x y a b c d u : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : a*c ≤ u) (had : a*d ≤ u) (hbc : b*c ≤ u) (hbd : b*d ≤ u) : x*y ≤ u := by
  by_cases hx0 : 0 ≤ x
  · have hxy : x*y ≤ x*d := mul_le_mul_of_nonneg_left hy.2 hx0
    by_cases hd0 : 0 ≤ d
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hd0).trans hbd)
    · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hd0)).trans had)
  · have hxy : x*y ≤ x*c := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hx0)
    by_cases hc0 : 0 ≤ c
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hc0).trans hbc)
    · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hc0)).trans hac)

/-- Every lower and upper corner comparison is explicit. This also permits
rigorous outward rounding of the candidate interval after each operation. -/
theorem mul_interval {x y a b c d l u : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hlo : l ≤ a*c ∧ l ≤ a*d ∧ l ≤ b*c ∧ l ≤ b*d)
    (hhi : a*c ≤ u ∧ a*d ≤ u ∧ b*c ≤ u ∧ b*d ≤ u) : l ≤ x*y ∧ x*y ≤ u := by
  refine ⟨?_,mul_upper hx hy hhi.1 hhi.2.1 hhi.2.2.1 hhi.2.2.2⟩
  have hn : -b ≤ -x ∧ -x ≤ -a := ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
  have h := mul_upper hn hy
    (by nlinarith [hlo.2.2.1] : (-b)*c ≤ -l)
    (by nlinarith [hlo.2.2.2] : (-b)*d ≤ -l)
    (by nlinarith [hlo.1] : (-a)*c ≤ -l)
    (by nlinarith [hlo.2.1] : (-a)*d ≤ -l)
  nlinarith

/-- Addition with explicitly checked outward-rounded endpoints. -/
theorem add_interval {x y a b c d l u : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : l ≤ a+c) (hu : b+d ≤ u) : l ≤ x+y ∧ x+y ≤ u :=
  ⟨hl.trans (add_le_add hx.1 hy.1),(add_le_add hx.2 hy.2).trans hu⟩

/-- Negation with explicitly checked outward-rounded endpoints. -/
theorem neg_interval {x a b l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hl : l ≤ -b) (hu : -a ≤ u) : l ≤ -x ∧ -x ≤ u :=
  ⟨hl.trans (neg_le_neg hx.2),(neg_le_neg hx.1).trans hu⟩

/-- Signed interval bounds give a proved absolute-value bound. -/
theorem abs_bound {x a b r : ℝ} (hx : a ≤ x ∧ x ≤ b) (hl : -r ≤ a) (hu : b ≤ r) :
    |x| ≤ r := abs_le.mpr ⟨hl.trans hx.1,hx.2.trans hu⟩

end FMSA.Convergence.RealIntervalCertificates

/-- info: 'FMSA.Convergence.RealIntervalCertificates.mul_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RealIntervalCertificates.mul_upper

/-- info: 'FMSA.Convergence.RealIntervalCertificates.mul_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RealIntervalCertificates.mul_interval

/-- info: 'FMSA.Convergence.RealIntervalCertificates.add_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RealIntervalCertificates.add_interval

/-- info: 'FMSA.Convergence.RealIntervalCertificates.neg_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RealIntervalCertificates.neg_interval

/-- info: 'FMSA.Convergence.RealIntervalCertificates.abs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RealIntervalCertificates.abs_bound
