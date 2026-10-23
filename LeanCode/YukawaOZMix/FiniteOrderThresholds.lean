import LeanCode.YukawaOZMix.FiniteOrderThermo

/-!
# Order thresholds: sign reentry for the scalar attractive one-Yukawa jet

The coefficient formulas below are obtained from the scalar PY/BH residual by
exact symbolic coefficient arithmetic in `msa_order_threshold_symbolic.py`.
Lean proves their signs for all `0 < eta < 1` and `z > 0`, and the resulting
first and second order sign behavior. It does not formalize the identification of
these formulas with derivatives of the physical OZ/MSA solution. In particular,
strong-coupling reentry is not asserted to be a correct physical phase.
-/

namespace FMSA.ExactMSA.FiniteOrderThresholds

noncomputable section

def jKernel (z : ℝ) := z - 2 + (z + 2) * Real.exp (-z)
def kKernel (z : ℝ) := 2 - (z ^ 2 + 2 * z + 2) * Real.exp (-z)
def hKernel (z : ℝ) := z ^ 2 - 2 + 2 * (z + 1) * Real.exp (-z)

private theorem positive_of_positive_derivative {f f' : ℝ → ℝ}
    (hzero : f 0 = 0) (hc : Continuous f)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hp : ∀ x, 0 < x → 0 < f' x)
    {z : ℝ} (hz : 0 < z) : 0 < f z := by
  have hm : StrictMonoOn f (Set.Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn fun x hx => by
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hd x).deriv]
      exact hp x hx
  simpa [hzero] using hm (by simp) (by simp; linarith) hz

theorem jKernel_pos {z : ℝ} (hz : 0 < z) : 0 < jKernel z := by
  apply positive_of_positive_derivative (f' := fun x => 1 - (x + 1) * Real.exp (-x))
  · norm_num [jKernel]
  · unfold jKernel; fun_prop
  · intro x
    unfold jKernel
    convert ((hasDerivAt_id x).sub_const 2).add
      (((hasDerivAt_id x).add_const 2).mul
        ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg)) using 1
    <;> (try ext y) <;> dsimp <;> ring
  · intro x hx
    have he := Real.add_one_lt_exp (ne_of_gt hx)
    have hm := mul_lt_mul_of_pos_right he (Real.exp_pos (-x))
    rw [← Real.exp_add] at hm
    simp only [add_neg_cancel, Real.exp_zero] at hm
    linarith
  · exact hz

theorem kKernel_pos {z : ℝ} (hz : 0 < z) : 0 < kKernel z := by
  apply positive_of_positive_derivative (f' := fun x => x ^ 2 * Real.exp (-x))
  · norm_num [kKernel]
  · unfold kKernel; fun_prop
  · intro x
    unfold kKernel
    convert (hasDerivAt_const x (2 : ℝ)).sub
      ((((hasDerivAt_id x).pow 2).add
        ((hasDerivAt_id x).const_mul 2) |>.add_const 2).mul
        ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg)) using 1
    <;> (try ext y) <;> dsimp <;> ring
  · intro x hx
    exact mul_pos (sq_pos_of_pos hx) (Real.exp_pos (-x))
  · exact hz

theorem hKernel_decomposition (z : ℝ) :
    hKernel z = (z + 2) * jKernel z + kKernel z := by
  unfold hKernel jKernel kKernel
  ring

theorem hKernel_pos {z : ℝ} (hz : 0 < z) : 0 < hKernel z := by
  rw [hKernel_decomposition]
  exact add_pos (mul_pos (by linarith) (jKernel_pos hz)) (kKernel_pos hz)

/-- A stronger kernel bound used to exclude extra first-order pressure loops. -/
theorem hKernel_lower_bound {z : ℝ} (hz : 0 < z) :
    (2 / 3 : ℝ) * z ^ 3 < (z + 1) * hKernel z := by
  have hg : 0 < (z + 1) * hKernel z - (2 / 3 : ℝ) * z ^ 3 := by
    apply positive_of_positive_derivative
      (f := fun x => (x + 1) * hKernel x - (2 / 3 : ℝ) * x ^ 3)
      (f' := fun x => hKernel x + 2 * x * (1 - (x + 1) * Real.exp (-x)))
    · norm_num [hKernel]
    · unfold hKernel; fun_prop
    · intro x
      unfold hKernel
      convert (((hasDerivAt_id x).add_const 1).mul
        ((((hasDerivAt_id x).pow 2).sub_const 2).add
          ((((hasDerivAt_id x).add_const 1).mul
            ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg)).const_mul 2))).sub
        (((hasDerivAt_id x).pow 3).const_mul (2 / 3 : ℝ)) using 1
      <;> (try ext y) <;> dsimp <;> ring
    · intro x hx
      have he := Real.add_one_lt_exp (ne_of_gt hx)
      have hm := mul_lt_mul_of_pos_right he (Real.exp_pos (-x))
      rw [← Real.exp_add] at hm
      simp only [add_neg_cancel, Real.exp_zero] at hm
      have hb : 0 < 1 - (x + 1) * Real.exp (-x) := by linarith
      exact add_pos (hKernel_pos hx) (mul_pos (by positivity) hb)
    · exact hz
  linarith

def firstOrderDerivativeQ2 (z : ℝ) :=
  3 * z ^ 3 * (3 - z) - 48 * (z + 1) * hKernel z -
    54 * (z + 1) * jKernel z

theorem firstOrderDerivativeQ2_neg {z : ℝ} (hz : 0 < z) :
    firstOrderDerivativeQ2 z < 0 := by
  have hb := hKernel_lower_bound hz
  have hj : 0 < (z + 1) * jKernel z := mul_pos (by linarith) (jKernel_pos hz)
  have hz3 : 0 < z ^ 3 := by positivity
  have hz4 : 0 < z ^ 4 := by positivity
  unfold firstOrderDerivativeQ2
  nlinarith [hb]

/-- A derivative numerator with this sign pattern has at most one positive
root: divide it by t, then every nonconstant term strictly decreases. -/
def dividedDerivative (q0 q1 q2 q3 q4 q5 t : ℝ) :=
  q0 / t + q1 + q2 * t + q3 * t ^ 2 + q4 * t ^ 3 + q5 * t ^ 4

theorem dividedDerivative_strictAnti {q0 q1 q2 q3 q4 q5 t u : ℝ}
    (h0 : 0 < q0) (h2 : q2 ≤ 0) (h3 : q3 ≤ 0) (h4 : q4 ≤ 0)
    (h5 : q5 ≤ 0) (ht : 0 < t) (htu : t < u) :
    dividedDerivative q0 q1 q2 q3 q4 q5 u <
      dividedDerivative q0 q1 q2 q3 q4 q5 t := by
  have hd : q0 / u < q0 / t := div_lt_div_of_pos_left h0 ht htu
  have hp2 := pow_le_pow_left₀ (le_of_lt ht) (le_of_lt htu) 2
  have hp3 := pow_le_pow_left₀ (le_of_lt ht) (le_of_lt htu) 3
  have hp4 := pow_le_pow_left₀ (le_of_lt ht) (le_of_lt htu) 4
  have hm2 := mul_le_mul_of_nonpos_left (le_of_lt htu) h2
  have hm3 := mul_le_mul_of_nonpos_left hp2 h3
  have hm4 := mul_le_mul_of_nonpos_left hp3 h4
  have hm5 := mul_le_mul_of_nonpos_left hp4 h5
  unfold dividedDerivative
  linarith

def firstOrderDividedDerivative (z t : ℝ) :=
  dividedDerivative (z ^ 3 * (z + 1))
    (6 * z ^ 3 - 6 * hKernel z * (z + 1)) (firstOrderDerivativeQ2 z)
    (-54 * hKernel z * (z + 1) - 72 * hKernel z -
      288 * jKernel z * (z + 1) - 108 * jKernel z)
    (-3 * (36 * hKernel z + 90 * jKernel z * (z + 1) + 216 * jKernel z))
    (-648 * jKernel z) t

theorem firstOrderDividedDerivative_strictAnti {z t u : ℝ}
    (hz : 0 < z) (ht : 0 < t) (htu : t < u) :
    firstOrderDividedDerivative z u < firstOrderDividedDerivative z t := by
  have hh := hKernel_pos hz
  have hj := jKernel_pos hz
  have hz1 : 0 < z + 1 := by linarith
  unfold firstOrderDividedDerivative
  apply dividedDerivative_strictAnti
  · positivity
  · exact le_of_lt (firstOrderDerivativeQ2_neg hz)
  · have : 0 < 54 * hKernel z * (z + 1) + 72 * hKernel z +
        288 * jKernel z * (z + 1) + 108 * jKernel z := by positivity
    linarith
  · have : 0 < 3 * (36 * hKernel z + 90 * jKernel z * (z + 1) +
        216 * jKernel z) := by positivity
    linarith
  · linarith
  · exact ht
  · exact htu

theorem firstOrderDerivative_atMostOne_positiveRoot {z t u : ℝ}
    (hz : 0 < z) (ht : 0 < t) (hu : 0 < u)
    (hroot_t : firstOrderDividedDerivative z t = 0)
    (hroot_u : firstOrderDividedDerivative z u = 0) : t = u := by
  rcases lt_trichotomy t u with h | h | h
  · have := firstOrderDividedDerivative_strictAnti hz ht h
    rw [hroot_t, hroot_u] at this
    exact False.elim (lt_irrefl _ this)
  · exact h
  · have := firstOrderDividedDerivative_strictAnti hz hu h
    rw [hroot_t, hroot_u] at this
    exact False.elim (lt_irrefl _ this)

def hsDenominator (η z : ℝ) :=
  z ^ 3 * (1 - η) ^ 2 + 6 * η * (1 - η) * hKernel z + 18 * η ^ 2 * jKernel z
def hsLinear (η z : ℝ) := (1 - η) * z + 1 + 2 * η
def hsQuadraticKernel (η z : ℝ) := (1 - η) * hKernel z + 6 * η * jKernel z

def discriminantKernel (η z : ℝ) :=
  z ^ 3 * (1 + 2 * (z + 1) * (1 - Real.exp (-z))) * (1 - η) ^ 4 +
  6 * ((3 + 5 * z + 2 * z ^ 2) * kKernel z +
    (z ^ 3 + 7 * z ^ 2 + 9 * z + 4) * jKernel z) * η * (1 - η) ^ 3 +
  9 * ((6 + 5 * z) * hKernel z + (2 * z + 2 * z ^ 2) * jKernel z) *
    η ^ 2 * (1 - η) ^ 2 +
  54 * (hKernel z + 2 * (z + 1) * jKernel z) * η ^ 3 * (1 - η) +
  162 * jKernel z * η ^ 4

theorem discriminantKernel_identity (η z : ℝ) :
    discriminantKernel η z = (hsLinear η z) ^ 2 * hsDenominator η z -
      z ^ 3 * (1 - η) ^ 3 * hsQuadraticKernel η z := by
  unfold discriminantKernel hsLinear hsDenominator hsQuadraticKernel
    hKernel jKernel kKernel
  ring

theorem hsDenominator_pos {η z : ℝ} (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) :
    0 < hsDenominator η z := by
  unfold hsDenominator
  have hw : 0 < 1 - η := by linarith
  have hh := hKernel_pos hz
  have hj := jKernel_pos hz
  positivity

theorem hsQuadraticKernel_pos {η z : ℝ} (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) :
    0 < hsQuadraticKernel η z := by
  unfold hsQuadraticKernel
  have hw : 0 < 1 - η := by linarith
  have hh := hKernel_pos hz
  have hj := jKernel_pos hz
  positivity

theorem discriminantKernel_pos {η z : ℝ} (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) :
    0 < discriminantKernel η z := by
  unfold discriminantKernel
  have hw : 0 < 1 - η := by linarith
  have hh := hKernel_pos hz
  have hj := jKernel_pos hz
  have hk := kKernel_pos hz
  have he : 0 < 1 - Real.exp (-z) := by
    have := Real.exp_lt_exp.mpr (show -z < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  positivity

def c0 (η : ℝ) := ((1 + 2 * η) / (1 - η) ^ 2) ^ 2
def c1 (η z : ℝ) :=
  -(24 * η * z ^ 4 * (1 + 2 * η) * hsLinear η z) / (hsDenominator η z) ^ 2
def c2 (η z : ℝ) :=
  144 * η ^ 2 * z ^ 11 * (1 - η) ^ 7 * hsQuadraticKernel η z /
    (hsDenominator η z) ^ 5

theorem c0_pos {η : ℝ} (hη : 0 < η) (hη1 : η < 1) : 0 < c0 η := by
  unfold c0
  have hw : 0 < 1 - η := by linarith
  positivity

theorem c1_neg {η z : ℝ} (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) : c1 η z < 0 := by
  have hp := hsDenominator_pos hη hη1 hz
  have hw : 0 < 1 - η := by linarith
  have hl : 0 < hsLinear η z := by unfold hsLinear; positivity
  unfold c1
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

theorem c2_pos {η z : ℝ} (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) : 0 < c2 η z := by
  have hp := hsDenominator_pos hη hη1 hz
  have hh := hsQuadraticKernel_pos hη hη1 hz
  have hw : 0 < 1 - η := by linarith
  unfold c2
  positivity

theorem discriminant_identity {η z : ℝ} (hw : 1 - η ≠ 0)
    (hp : hsDenominator η z ≠ 0) :
    (c1 η z) ^ 2 - 4 * c0 η * c2 η z =
      576 * η ^ 2 * z ^ 8 * (1 + 2 * η) ^ 2 * discriminantKernel η z /
        (hsDenominator η z) ^ 5 := by
  rw [discriminantKernel_identity]
  unfold c0 c1 c2
  field_simp [hw, hp]
  <;> ring

theorem discriminant_pos {η z : ℝ} (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) :
    0 < (c1 η z) ^ 2 - 4 * c0 η * c2 η z := by
  have hw : 0 < 1 - η := by linarith
  have hp := hsDenominator_pos hη hη1 hz
  rw [discriminant_identity (ne_of_gt hw) (ne_of_gt hp)]
  have hv := discriminantKernel_pos hη hη1 hz
  positivity

theorem firstOrder_no_reentry {a0 a1 τ₁ τ₂ : ℝ} (hslope : a1 ≤ 0)
    (hτ : τ₁ ≤ τ₂) (hnegative : a0 + a1 * τ₁ < 0) : a0 + a1 * τ₂ < 0 := by
  have := mul_le_mul_of_nonpos_left hτ hslope
  linarith

theorem affine_negative_iff_crossing {a0 a1 τ : ℝ} (h1 : a1 < 0) :
    a0 + a1 * τ < 0 ↔ -a0 / a1 < τ := by
  rw [div_lt_iff_of_neg h1]
  constructor <;> intro h <;> nlinarith

/-- Zeroth order cannot have a negative scalar spectrum if it is represented
by a real-wavevector Baxter modulus square. Zeros are not excluded. -/
theorem zerothOrder_spectral_nonnegative (F0 : ℂ) : 0 ≤ Complex.normSq F0 :=
  Complex.normSq_nonneg F0

/-- Pointwise positivity survives sufficiently small coupling at every
finite order. This is not uniform in density, order, or wavevector. -/
theorem positive_near_zero {f : ℝ → ℝ} (hc : ContinuousAt f 0) (h0 : 0 < f 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, |τ| < δ → 0 < f τ := by
  obtain ⟨δ, hδ, hf⟩ := Metric.continuousAt_iff.mp hc (f 0 / 2) (half_pos h0)
  refine ⟨δ, hδ, fun τ hτ => ?_⟩
  have hdist : dist τ 0 < δ := by simpa [Real.dist_eq] using hτ
  have h := hf hdist
  rw [Real.dist_eq] at h
  have hl := neg_le_abs (f τ - f 0)
  linarith

theorem finite_order_positive_near_zero (c : ℕ → ℝ) (N : ℕ)
    (h0 : 0 < FMSA.ExactMSA.FiniteOrderThermo.amplitudeJet c N 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, |τ| < δ →
      0 < FMSA.ExactMSA.FiniteOrderThermo.amplitudeJet c N τ :=
  positive_near_zero
    (FMSA.ExactMSA.FiniteOrderThermo.amplitudeJet_continuous c N).continuousAt h0

def quadratic (a0 a1 a2 τ : ℝ) := a0 + a1 * τ + a2 * τ ^ 2

theorem quadratic_vertex_value {a0 a1 a2 : ℝ} (h2 : a2 ≠ 0) :
    quadratic a0 a1 a2 (-a1 / (2 * a2)) = -(a1 ^ 2 - 4 * a0 * a2) / (4 * a2) := by
  unfold quadratic
  field_simp
  <;> ring

theorem quadratic_balance_value {a0 a1 a2 : ℝ} (h2 : a2 ≠ 0) :
    quadratic a0 a1 a2 (-a1 / a2) = a0 := by
  unfold quadratic
  field_simp
  <;> ring

/-- Constructive fixed-density reentry: a negative value precedes a positive
value at larger positive coupling. No claim of two global binodals. -/
theorem quadratic_reentry {a0 a1 a2 : ℝ} (h0 : 0 < a0) (h1 : a1 < 0)
    (h2 : 0 < a2) (hdisc : 0 < a1 ^ 2 - 4 * a0 * a2) :
    ∃ τ₁ τ₂ : ℝ, 0 < τ₁ ∧ τ₁ < τ₂ ∧
      quadratic a0 a1 a2 τ₁ < 0 ∧ 0 < quadratic a0 a1 a2 τ₂ := by
  refine ⟨-a1 / (2 * a2), -a1 / a2, ?_, ?_, ?_, ?_⟩
  · exact div_pos (neg_pos.mpr h1) (by positivity)
  · have he : -a1 / a2 = 2 * (-a1 / (2 * a2)) := by field_simp
    rw [he]
    have : 0 < -a1 / (2 * a2) := div_pos (neg_pos.mpr h1) (by positivity)
    linarith
  · rw [quadratic_vertex_value (ne_of_gt h2)]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hdisc) (by positivity)
  · rw [quadratic_balance_value (ne_of_gt h2)]
    exact h0

theorem attractive_oneYukawa_secondOrder_reentry {η z : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) :
    ∃ τ₁ τ₂ : ℝ, 0 < τ₁ ∧ τ₁ < τ₂ ∧
      quadratic (c0 η) (c1 η z) (c2 η z) τ₁ < 0 ∧
      0 < quadratic (c0 η) (c1 η z) (c2 η z) τ₂ :=
  quadratic_reentry (c0_pos hη hη1) (c1_neg hη hη1 hz)
    (c2_pos hη hη1 hz) (discriminant_pos hη hη1 hz)

end

end FMSA.ExactMSA.FiniteOrderThresholds
