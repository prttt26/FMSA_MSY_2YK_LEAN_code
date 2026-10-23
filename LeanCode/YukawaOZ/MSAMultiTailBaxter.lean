import LeanCode.YukawaOZ.MSAMultiTailSystem
import LeanCode.YukawaOZMix.MSAMixtureBreakpointConvDirect

/-!
# Finite-tail real-space Baxter function and its exterior closure

The core is defined by the real-space Baxter convolution, independently of any
spectral square. Integrals are split at the unit hard-core diameter. Positive
rates, including repeated rates, make every tail-pair integral convergent.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def qCore (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  amplitudeQp xi z Dt G * (r - 1) + amplitudeA xi z Dt G / 2 * (r - 1) ^ 2 +
    ∑ t, (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t)

def qTail (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ t, (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t * exp (-z t * (r - 1)))

def q (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  if r < 0 then 0 else if r ≤ 1 then qCore xi z Dt G r else qTail xi z Dt G r

def qPrimeCore (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  amplitudeQp xi z Dt G + amplitudeA xi z Dt G * (r - 1) -
    ∑ t, z t * W xi z Dt G t * exp (-z t * r)

def qPrimeTail (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ t, (-z t * (W xi z Dt G t * exp (-z t * r) +
    C xi z Dt G t * exp (-z t * (r - 1))))

def qPrime (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  if r < 0 then 0 else if r ≤ 1 then qPrimeCore xi z Dt G r else qPrimeTail xi z Dt G r

/-- Genuine Laplace integral, split into its bounded core and improper tail. -/
def laplaceQ (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, qCore xi z Dt G r * exp (-s * r)) +
    ∫ r in Ioi (1 : ℝ), qTail xi z Dt G r * exp (-s * r)

def convolution (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, qPrime xi z Dt G (t + r) * qCore xi z Dt G t) +
    ∫ t in Ioi (1 : ℝ), qPrime xi z Dt G (t + r) * qTail xi z Dt G t

/-- Real-space direct correlation recovered from the Baxter convolution.
Its Fourier identification and the OZ/hard-core conditions are separate obligations. -/
def correlation (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  (-qPrime xi z Dt G r + rhoOf xi * convolution xi z Dt G r) / (2 * π * r)

theorem q_contact (xi : ℝ) (z Dt G : ι → ℝ) :
    qCore xi z Dt G 1 = qTail xi z Dt G 1 := by
  simp [qCore, qTail]

theorem qPrimeTail_eq (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) :
    qPrimeTail xi z Dt G r = ∑ t, -z t * Dt t * exp (z t) * exp (-z t * r) := by
  apply Finset.sum_congr rfl
  intro t _
  have he : exp (-z t * (r - 1)) = exp (z t) * exp (-z t * r) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  have hw := W_add_C_exp xi z Dt G t
  linear_combination (-z t * exp (-z t * r)) * hw

theorem qPrime_tail {xi r : ℝ} {z Dt G : ι → ℝ} (hr : 1 < r) :
    qPrime xi z Dt G r = ∑ t, -z t * Dt t * exp (z t) * exp (-z t * r) := by
  rw [qPrime, if_neg (by linarith), if_neg (not_le.mpr hr), qPrimeTail_eq]

omit [Fintype ι] in
theorem tailPair_integral (a b U V c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi c, U * exp (-a * x) * (V * exp (-b * x))) =
      U * V * exp (-(a + b) * c) / (a + b) := by
  have he : (fun x : ℝ => U * exp (-a * x) * (V * exp (-b * x))) =
      (fun x => U * V * exp (-(a + b) * x)) := by
    funext x
    rw [show -(a + b) * x = -a * x + -b * x by ring, exp_add]
    ring
  rw [he, integral_const_mul, integral_exp_mul_Ioi (by linarith : -(a + b) < 0)]
  field_simp

private theorem tailWeight_integrable (xi : ℝ) (z Dt G : ι → ℝ)
    (hz : ∀ t, 0 < z t) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun r => qTail xi z Dt G r * exp (-s * r)) (Ioi (1 : ℝ)) := by
  have he : (fun r => qTail xi z Dt G r * exp (-s * r)) =
      (fun r => ∑ t, (W xi z Dt G t + C xi z Dt G t * exp (z t)) *
        exp (-(s + z t) * r)) := by
    funext r
    simp only [qTail, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [show -z t * (r - 1) = z t + -z t * r by ring, exp_add,
      show -(s + z t) * r = -z t * r + -s * r by ring, exp_add]
    ring
  rw [he]
  apply integrable_finsetSum
  intro t _
  exact (integrableOn_exp_mul_Ioi (by linarith [hz t] : -(s + z t) < 0) 1).const_mul _

private theorem coreWeight_continuous (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) :
    Continuous (fun r => qCore xi z Dt G r * exp (-s * r)) := by
  unfold qCore
  fun_prop

private theorem poly_laplace (A qp s : ℝ) (hs : s ≠ 0) :
    (∫ r in (0 : ℝ)..1, (qp * (r - 1) + A / 2 * (r - 1) ^ 2) * exp (-s * r)) =
      phi1 s * qp + phi2 s * A := by
  have he : (fun r : ℝ => (qp * (r - 1) + A / 2 * (r - 1) ^ 2) * exp (-s * r)) =
      (fun r => A / 2 * (r ^ 2 * exp (-s * r)) +
        (qp - A) * (r * exp (-s * r)) + (A / 2 - qp) * exp (-s * r)) := by
    funext r
    ring
  have hsq : IntervalIntegrable (fun r : ℝ => r ^ 2 * exp (-s * r)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hid : IntervalIntegrable (fun r : ℝ => r * exp (-s * r)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hex : IntervalIntegrable (fun r : ℝ => exp (-s * r)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [he, intervalIntegral.integral_add ((hsq.const_mul _).add (hid.const_mul _))
    (hex.const_mul _), intervalIntegral.integral_add (hsq.const_mul _) (hid.const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [Breakpoint.integral_sq_mul_exp 0 1 (-s) (neg_ne_zero.mpr hs),
    Breakpoint.integral_id_mul_exp 0 1 (-s) (neg_ne_zero.mpr hs),
    Breakpoint.integral_exp_linear 0 1 (-s) (neg_ne_zero.mpr hs)]
  simp only [mul_one, mul_zero, exp_zero, phi1, phi2]
  field_simp
  ring

theorem laplaceQ_eq_Qhat (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {s : ℝ} (hs : 0 < s) : laplaceQ xi z Dt G s = Qhat xi z Dt G s := by
  have hcore : ∀ t : ι, IntervalIntegrable (fun r : ℝ =>
      (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t) * exp (-s * r)) volume 0 1 := by
    intro t
    apply Continuous.intervalIntegrable
    fun_prop
  have hpoly : IntervalIntegrable (fun r : ℝ =>
      (amplitudeQp xi z Dt G * (r - 1) + amplitudeA xi z Dt G / 2 * (r - 1) ^ 2) *
        exp (-s * r)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have ht : ∀ t : ι, IntegrableOn (fun r : ℝ =>
      (W xi z Dt G t + C xi z Dt G t * exp (z t)) * exp (-(s + z t) * r)) (Ioi 1) := by
    intro t
    exact (integrableOn_exp_mul_Ioi (by linarith [hz t] : -(s + z t) < 0) 1).const_mul _
  have het : (fun r => qTail xi z Dt G r * exp (-s * r)) =
      (fun r => ∑ t, (W xi z Dt G t + C xi z Dt G t * exp (z t)) *
        exp (-(s + z t) * r)) := by
    funext r
    simp only [qTail, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [show -z t * (r - 1) = z t + -z t * r by ring, exp_add,
      show -(s + z t) * r = -z t * r + -s * r by ring, exp_add]
    ring
  unfold laplaceQ
  have hecore : (fun r => qCore xi z Dt G r * exp (-s * r)) =
      (fun r => (amplitudeQp xi z Dt G * (r - 1) + amplitudeA xi z Dt G / 2 * (r - 1) ^ 2) *
        exp (-s * r) + ∑ t, (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t) * exp (-s * r)) := by
    funext r
    rw [qCore, add_mul, Finset.sum_mul]
  have hsum : IntervalIntegrable (fun r => ∑ t,
      (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t) * exp (-s * r)) volume 0 1 := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun t _ => hcore t)
  rw [hecore, intervalIntegral.integral_add hpoly hsum,
    intervalIntegral.integral_finsetSum (fun t _ => hcore t),
    poly_laplace _ _ s hs.ne', het, integral_finsetSum _ (fun t _ => ht t)]
  unfold Qhat
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have hc : (∫ r in (0 : ℝ)..1,
      (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t) * exp (-s * r)) =
      W xi z Dt G t * ((1 - exp (-(s + z t))) / (s + z t)) +
        C xi z Dt G t * ((1 - exp (-s)) / s) := by
    have he : (fun r : ℝ =>
        (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t) * exp (-s * r)) =
        (fun r => W xi z Dt G t * exp (-(s + z t) * r) +
          C xi z Dt G t * exp (-s * r)) := by
      funext r
      rw [show -(s + z t) * r = -z t * r + -s * r by ring, exp_add]
      ring
    have hi1 : IntervalIntegrable (fun r : ℝ => W xi z Dt G t * exp (-(s + z t) * r)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hi2 : IntervalIntegrable (fun r : ℝ => C xi z Dt G t * exp (-s * r)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [he, intervalIntegral.integral_add hi1 hi2]
    simp only [intervalIntegral.integral_const_mul]
    rw [Breakpoint.integral_exp_linear 0 1 (-(s + z t)) (by linarith [hz t]),
      Breakpoint.integral_exp_linear 0 1 (-s) (neg_ne_zero.mpr hs.ne')]
    simp only [mul_one, mul_zero, exp_zero]
    field_simp [hs.ne', (add_pos hs (hz t)).ne']
    ring
  rw [hc, integral_const_mul, integral_exp_mul_Ioi (by linarith [hz t] : -(s + z t) < 0)]
  have he : exp (z t) * exp (-(s + z t)) = exp (-s) := by
    rw [← exp_add]
    congr 1
    ring
  simp only [mul_one]
  field_simp [hs.ne', (add_pos hs (hz t)).ne']
  linear_combination s * C xi z Dt G t * he

theorem qPrime_shift_exterior {xi r x : ℝ} {z Dt G : ι → ℝ}
    (hr : 1 < r) (hx : 0 ≤ x) :
    qPrime xi z Dt G (x + r) =
      ∑ t, (-z t * Dt t * exp (z t) * exp (-z t * r)) * exp (-z t * x) := by
  rw [qPrime_tail (by linarith : 1 < x + r)]
  apply Finset.sum_congr rfl
  intro t _
  rw [show -z t * (x + r) = -z t * r + -z t * x by ring, exp_add]
  ring

/-- The exterior convolution is derived from the actual Laplace integrals,
not from a prescribed Yukawa closure. -/
theorem convolution_exterior (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {r : ℝ} (hr : 1 < r) :
    convolution xi z Dt G r = ∑ t,
      (-z t * Dt t * exp (z t) * exp (-z t * r)) * Qhat xi z Dt G (z t) := by
  let H : ι → ℝ := fun t => -z t * Dt t * exp (z t) * exp (-z t * r)
  have hi : ∀ t : ι, IntervalIntegrable
      (fun x => H t * (qCore xi z Dt G x * exp (-z t * x))) volume 0 1 := by
    intro t
    exact (coreWeight_continuous xi z Dt G (z t)).intervalIntegrable 0 1 |>.const_mul _
  have ht : ∀ t : ι, IntegrableOn
      (fun x => H t * (qTail xi z Dt G x * exp (-z t * x))) (Ioi 1) := by
    intro t
    exact (tailWeight_integrable xi z Dt G hz (hz t)).const_mul _
  have hpt : ∀ x : ℝ, 0 ≤ x → ∀ Q : ℝ,
      qPrime xi z Dt G (x + r) * Q = ∑ t, H t * (Q * exp (-z t * x)) := by
    intro x hx Q
    rw [qPrime_shift_exterior hr hx, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    dsimp [H]
    ring
  have hcore : (∫ x in (0 : ℝ)..1, qPrime xi z Dt G (x + r) * qCore xi z Dt G x) =
      ∑ t, H t * (∫ x in (0 : ℝ)..1, qCore xi z Dt G x * exp (-z t * x)) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, ∑ t, H t * (qCore xi z Dt G x * exp (-z t * x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hpt x (by simpa using hx.1) _
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum (fun t _ => hi t)]
        simp only [intervalIntegral.integral_const_mul]
  have htail : (∫ x in Ioi (1 : ℝ), qPrime xi z Dt G (x + r) * qTail xi z Dt G x) =
      ∑ t, H t * (∫ x in Ioi (1 : ℝ), qTail xi z Dt G x * exp (-z t * x)) := by
    calc
      _ = ∫ x in Ioi (1 : ℝ), ∑ t, H t * (qTail xi z Dt G x * exp (-z t * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change 1 < x at hx
        exact hpt x (by linarith [hx]) _
      _ = _ := by
        rw [integral_finsetSum _ (fun t _ => ht t)]
        simp only [integral_const_mul]
  rw [convolution, hcore, htail, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← mul_add, ← laplaceQ, laplaceQ_eq_Qhat xi z Dt G hz (hz t)]

/-- All finite-tail exterior Yukawa equations follow from the first BH residuals.
The second residuals are still needed for the separate RDF/hard-core problem. -/
theorem correlation_exterior (xi : ℝ) (z K Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    (h29 : ∀ t, Dt t * factor xi z Dt G (z t) = 2 * π * K t / z t)
    {r : ℝ} (hr : 1 < r) :
    correlation xi z Dt G r = ∑ t, K t * exp (-z t * (r - 1)) / r := by
  have hnum : -qPrime xi z Dt G r + rhoOf xi * convolution xi z Dt G r =
      ∑ t, 2 * π * K t * exp (-z t * (r - 1)) := by
    rw [qPrime_tail hr, convolution_exterior xi z Dt G hz hr,
      ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    have he : exp (-z t * (r - 1)) = exp (z t) * exp (-z t * r) := by
      rw [← exp_add]
      congr 1
      ring
    have hh := h29 t
    unfold factor at hh
    have hh' : z t * (Dt t * (1 - rhoOf xi * Qhat xi z Dt G (z t))) = 2 * π * K t := by
      rw [hh, mul_div_cancel₀ _ (hz t).ne']
    rw [he]
    linear_combination (exp (z t) * exp (-z t * r)) * hh'
  rw [correlation, hnum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  field_simp

theorem correlation_exterior_of_root (xi : ℝ) (z K Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    (hroot : IsRoot xi z K Dt G) {r : ℝ} (hr : 1 < r) :
    correlation xi z Dt G r = ∑ t, K t * exp (-z t * (r - 1)) / r :=
  correlation_exterior xi z K Dt G hz hroot.1 hr

/-- The split transform is the ordinary half-line Laplace integral. -/
theorem laplaceQ_eq_integral (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {s : ℝ} (hs : 0 < s) :
    laplaceQ xi z Dt G s = ∫ r in Ioi (0 : ℝ), q xi z Dt G r * exp (-s * r) := by
  have hcore : ∀ r ∈ Set.uIcc (0 : ℝ) 1,
      q xi z Dt G r = qCore xi z Dt G r := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa using hr
    rw [q, if_neg (not_lt.mpr hr'.1), if_pos hr'.2]
  have htail : ∀ r ∈ Ioi (1 : ℝ), q xi z Dt G r = qTail xi z Dt G r := by
    intro r hr
    change 1 < r at hr
    rw [q, if_neg (by linarith), if_neg (not_le.mpr hr)]
  have hb : IntervalIntegrable (fun r => q xi z Dt G r * exp (-s * r)) volume 0 1 :=
    ((coreWeight_continuous xi z Dt G s).intervalIntegrable 0 1).congr
      (fun r hr => by rw [hcore r (uIoc_subset_uIcc hr)])
  have ht : IntegrableOn (fun r => q xi z Dt G r * exp (-s * r)) (Ioi 1) :=
    (tailWeight_integrable xi z Dt G hz hs).congr_fun
      (fun r hr => by rw [htail r hr]) measurableSet_Ioi
  rw [← intervalIntegral.integral_interval_add_Ioi' hb ht, laplaceQ]
  congr 1
  · exact intervalIntegral.integral_congr (fun r hr => by rw [hcore r hr])
  · exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [htail r hr])

theorem q_hasDerivAt_core (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) : HasDerivAt (q xi z Dt G) (qPrimeCore xi z Dt G r) r := by
  have he : q xi z Dt G =ᶠ[𝓝 r] qCore xi z Dt G := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with x hx
    rw [q, if_neg (not_lt.mpr hx.1.le), if_pos hx.2.le]
  have hpoly : HasDerivAt (fun x => amplitudeQp xi z Dt G * (x - 1) +
      amplitudeA xi z Dt G / 2 * (x - 1) ^ 2)
      (amplitudeQp xi z Dt G + amplitudeA xi z Dt G * (r - 1)) r := by
    have hl : HasDerivAt (fun x : ℝ => x - 1) 1 r := (hasDerivAt_id r).sub_const 1
    have hq : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (r - 1)) r := by
      convert hl.mul hl using 1 <;> first | rfl | (ext x; dsimp; ring) | ring
    exact ((hl.const_mul (amplitudeQp xi z Dt G)).add
      (hq.const_mul (amplitudeA xi z Dt G / 2))).congr_deriv (by ring)
  have hsum : HasDerivAt (fun x => ∑ t, (W xi z Dt G t * exp (-z t * x) + C xi z Dt G t))
      (∑ t, -z t * W xi z Dt G t * exp (-z t * r)) r := by
    apply HasDerivAt.fun_sum
    intro t _
    convert (((Real.hasDerivAt_exp (-z t * r)).comp r
      ((hasDerivAt_id r).const_mul (-z t))).const_mul (W xi z Dt G t)).add_const
      (C xi z Dt G t) using 1 <;> (try simp only [Function.comp_def, mul_one]) <;> ring
  have h : HasDerivAt (qCore xi z Dt G) (qPrimeCore xi z Dt G r) r := by
    apply (hpoly.add hsum).congr_deriv
    simp only [qPrimeCore, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  exact h.congr_of_eventuallyEq he

end FMSA.ExactMSA.MultiTail
