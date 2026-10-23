import LeanCode.YukawaOZ.MSAMultiTailBaxter
import LeanCode.YukawaOZMix.MSAMultiTailMixtureBaxter

/-!
# Closed finite-tail pure-fluid Baxter core from the actual convolution

No tail-count-specific polynomial is expanded. The two bounded regions use
`FiniteYukawa.integral_branchProduct`; the improper region is a finite sum with
denominators `z u + z t`. This recovers the convolution core, not yet the full
OZ/RDF hard-core condition or its physical Fourier identification.
-/

noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
open scoped ContDiff

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def V (z Dt : ι → ℝ) (t : ι) : ℝ := Dt t * exp (z t)

def b0 (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  amplitudeA xi z Dt G / 2 - amplitudeQp xi z Dt G + ∑ t, C xi z Dt G t

def b1 (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  amplitudeQp xi z Dt G - amplitudeA xi z Dt G

def b2 (xi : ℝ) (z Dt G : ι → ℝ) : ℝ := amplitudeA xi z Dt G / 2

theorem qCore_expPoly (xi : ℝ) (z Dt G : ι → ℝ) (x : ℝ) :
    qCore xi z Dt G x = (b0 xi z Dt G + b1 xi z Dt G * x + b2 xi z Dt G * x ^ 2) +
      ∑ t, W xi z Dt G t * exp (-z t * x) := by
  simp only [qCore, b0, b1, b2, Finset.sum_add_distrib]
  ring

theorem qTail_expPoly (xi : ℝ) (z Dt G : ι → ℝ) (x : ℝ) :
    qTail xi z Dt G x = ∑ t, V z Dt t * exp (-z t * x) := by
  unfold qTail
  apply Finset.sum_congr rfl
  intro t _
  rw [show -z t * (x - 1) = z t + -z t * x by ring, exp_add]
  have hh := W_add_C_exp xi z Dt G t
  dsimp [V]
  linear_combination exp (-z t * x) * hh

def coreDerivativeExp (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) (t : ι) : ℝ :=
  -z t * W xi z Dt G t * exp (-z t * r)

def tailDerivativeExp (z Dt : ι → ℝ) (r : ℝ) (t : ι) : ℝ :=
  -z t * V z Dt t * exp (-z t * r)

theorem qPrimeCore_expPoly (xi : ℝ) (z Dt G : ι → ℝ) (r x : ℝ) :
    qPrimeCore xi z Dt G (x + r) =
      (amplitudeQp xi z Dt G + amplitudeA xi z Dt G * (r - 1) + amplitudeA xi z Dt G * x) +
        ∑ t, coreDerivativeExp xi z Dt G r t * exp (-z t * x) := by
  simp only [qPrimeCore, coreDerivativeExp,
    show ∀ t : ι, -z t * (x + r) = -z t * r + -z t * x by intro t; ring,
    exp_add, ← Finset.sum_neg_distrib]
  have hh : (∑ t, -(z t * W xi z Dt G t * (exp (-z t * r) * exp (-z t * x)))) =
      ∑ t, -z t * W xi z Dt G t * exp (-z t * r) * exp (-z t * x) := by
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, hh]
  ring

private theorem pure_mixture_q (xi : ℝ) (z Dt G : ι → ℝ) (x : ℝ) :
    q xi z Dt G x = MultiTailMixture.q z (fun _ : Fin 1 => 1)
      (fun _ => amplitudeA xi z Dt G) (fun _ _ => amplitudeQp xi z Dt G)
      (fun t _ _ => W xi z Dt G t) (fun t _ _ => C xi z Dt G t) 0 0 x := by
  simp only [q, qCore, qTail, MultiTailMixture.q, MSAMixture.edgeLo, MSAMixture.edgeHi]
  norm_num

private theorem pure_mixture_qPrime (xi : ℝ) (z Dt G : ι → ℝ) (x : ℝ) :
    qPrime xi z Dt G x = MultiTailMixture.qPrime z (fun _ : Fin 1 => 1)
      (fun _ => amplitudeA xi z Dt G) (fun _ _ => amplitudeQp xi z Dt G)
      (fun t _ _ => W xi z Dt G t) (fun t _ _ => C xi z Dt G t) 0 0 x := by
  simp only [qPrime, qPrimeCore, qPrimeTail, MultiTailMixture.qPrime,
    MSAMixture.edgeLo, MSAMixture.edgeHi]
  norm_num
  split_ifs <;> simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem convolutionIntegrand_integrable (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t) (r : ℝ) :
    Integrable (fun t => qPrime xi z Dt G (t + r) * q xi z Dt G t) := by
  simp_rw [pure_mixture_q, pure_mixture_qPrime]
  exact MultiTailMixture.convolution_integrable z hz _ _ _ _ _ (fun _ => zero_le_one) 0 0 0 r

/-- Primitive value of a general bounded branch product (no remaining integral). -/
def branchValue (z : ι → ℝ) (a0 a1 b0 b1 b2 : ℝ) (U W : ι → ℝ) (x : ℝ) : ℝ :=
  FiniteYukawa.primitive z z (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1) (a1 * b2)
    (fun u => U u * b0) (fun u => U u * b1) (fun u => U u * b2)
    (fun t => a0 * W t) (fun t => a1 * W t) (fun _ => 0) (fun u t => U u * W t) x

def coreCoreValue (xi : ℝ) (z Dt G : ι → ℝ) (r x : ℝ) : ℝ :=
  branchValue z (amplitudeQp xi z Dt G + amplitudeA xi z Dt G * (r - 1))
    (amplitudeA xi z Dt G) (b0 xi z Dt G) (b1 xi z Dt G) (b2 xi z Dt G)
    (coreDerivativeExp xi z Dt G r) (W xi z Dt G) x

def tailCoreValue (xi : ℝ) (z Dt G : ι → ℝ) (r x : ℝ) : ℝ :=
  branchValue z 0 0 (b0 xi z Dt G) (b1 xi z Dt G) (b2 xi z Dt G)
    (tailDerivativeExp z Dt r) (W xi z Dt G) x

def tailTailValue (z Dt : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ u, ∑ t, tailDerivativeExp z Dt r u * V z Dt t * exp (-(z u + z t)) / (z u + z t)

def closedConvolution (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  coreCoreValue xi z Dt G r (1 - r) - coreCoreValue xi z Dt G r 0 +
    (tailCoreValue xi z Dt G r 1 - tailCoreValue xi z Dt G r (1 - r)) + tailTailValue z Dt r

theorem qPrime_shift_tail_expPoly (xi : ℝ) (z Dt G : ι → ℝ) {r x : ℝ}
    (hxr : 1 < x + r) :
    qPrime xi z Dt G (x + r) = ∑ t, tailDerivativeExp z Dt r t * exp (-z t * x) := by
  rw [qPrime_tail hxr]
  apply Finset.sum_congr rfl
  intro t _
  rw [show -z t * (x + r) = -z t * r + -z t * x by ring, exp_add]
  dsimp [tailDerivativeExp, V]
  ring

private theorem tailTail_integral (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (1 : ℝ), qPrime xi z Dt G (x + r) * qTail xi z Dt G x) =
      tailTailValue z Dt r := by
  let H : ι → ι → ℝ := fun u t => tailDerivativeExp z Dt r u * V z Dt t
  have hi (u t : ι) : IntegrableOn (fun x => H u t * exp (-(z u + z t) * x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by linarith [hz u, hz t] : -(z u + z t) < 0) 1).const_mul _
  have he : (∫ x in Ioi (1 : ℝ), qPrime xi z Dt G (x + r) * qTail xi z Dt G x) =
      ∫ x in Ioi (1 : ℝ), ∑ u, ∑ t, H u t * exp (-(z u + z t) * x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change 1 < x at hx
    dsimp only
    rw [qPrime_shift_tail_expPoly xi z Dt G (by linarith : 1 < x + r),
      qTail_expPoly, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro t _
    rw [show -(z u + z t) * x = -z u * x + -z t * x by ring, exp_add]
    dsimp [H]
    ring
  rw [he, integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun t _ => hi u t))]
  unfold tailTailValue
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_finsetSum _ (fun t _ => hi u t)]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [hz u, hz t] : -(z u + z t) < 0)]
  dsimp [H]
  simp only [mul_one]
  field_simp [(add_pos (hz u) (hz t)).ne'] <;> ring

/-- Complete finite closed form of the actual pure-fluid core convolution.
This theorem is uniform in the number of tails and in their signs and coincidences. -/
theorem convolution_eq_closed (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    convolution xi z Dt G r = closedConvolution xi z Dt G r := by
  have hm0 : 0 ≤ 1 - r := by linarith
  have hm1 : 1 - r ≤ 1 := by linarith
  have hb : IntervalIntegrable (fun x => qPrime xi z Dt G (x + r) * qCore xi z Dt G x)
      volume 0 1 := by
    apply ((convolutionIntegrand_integrable xi z Dt G hz r).intervalIntegrable).congr
    intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) 1 := by simpa using hx
    dsimp only
    rw [q, if_neg (by linarith [hx'.1]), if_pos hx'.2]
  have hb1 : IntervalIntegrable (fun x => qPrime xi z Dt G (x + r) * qCore xi z Dt G x)
      volume 0 (1 - r) := by
    apply hb.mono_set
    intro x hx
    simp only [uIcc_of_le hm0, uIcc_of_le zero_le_one, mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hm1⟩
  have hb2 : IntervalIntegrable (fun x => qPrime xi z Dt G (x + r) * qCore xi z Dt G x)
      volume (1 - r) 1 := by
    apply hb.mono_set
    intro x hx
    simp only [uIcc_of_le hm1, uIcc_of_le zero_le_one, mem_Icc] at hx ⊢
    exact ⟨hm0.trans hx.1, hx.2⟩
  have hc : (∫ x in (0 : ℝ)..(1 - r), qPrime xi z Dt G (x + r) * qCore xi z Dt G x) =
      coreCoreValue xi z Dt G r (1 - r) - coreCoreValue xi z Dt G r 0 := by
    calc
      _ = ∫ x in (0 : ℝ)..(1 - r),
          ((amplitudeQp xi z Dt G + amplitudeA xi z Dt G * (r - 1) + amplitudeA xi z Dt G * x) +
            ∑ t, coreDerivativeExp xi z Dt G r t * exp (-z t * x)) *
          ((b0 xi z Dt G + b1 xi z Dt G * x + b2 xi z Dt G * x ^ 2) +
            ∑ t, W xi z Dt G t * exp (-z t * x)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm0
        intro x hx
        dsimp only
        rw [qPrime, if_neg (by linarith [hx.1]), if_pos (by linarith [hx.2]),
          qPrimeCore_expPoly, qCore_expPoly]
      _ = _ := FiniteYukawa.integral_branchProduct z z hz hz _ _ _ _ _ _ _ 0 (1 - r)
  have ht : (∫ x in (1 - r)..(1 : ℝ), qPrime xi z Dt G (x + r) * qCore xi z Dt G x) =
      tailCoreValue xi z Dt G r 1 - tailCoreValue xi z Dt G r (1 - r) := by
    calc
      _ = ∫ x in (1 - r)..(1 : ℝ),
          ((0 + 0 * x) + ∑ t, tailDerivativeExp z Dt r t * exp (-z t * x)) *
          ((b0 xi z Dt G + b1 xi z Dt G * x + b2 xi z Dt G * x ^ 2) +
            ∑ t, W xi z Dt G t * exp (-z t * x)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm1
        intro x hx
        dsimp only
        rw [qPrime_shift_tail_expPoly xi z Dt G (by linarith [hx.1]), qCore_expPoly]
        simp only [zero_mul, zero_add]
      _ = _ := FiniteYukawa.integral_branchProduct z z hz hz 0 0 _ _ _ _ _ (1 - r) 1
  rw [convolution, ← intervalIntegral.integral_add_adjacent_intervals hb1 hb2,
    hc, ht, tailTail_integral xi z Dt G hz hr0]
  rfl

def closedCorrelation (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  (-qPrimeCore xi z Dt G r + rhoOf xi * closedConvolution xi z Dt G r) / (2 * π * r)

theorem correlation_core_eq_closed (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    correlation xi z Dt G r = closedCorrelation xi z Dt G r := by
  rw [correlation, qPrime, if_neg (not_lt.mpr hr0.le), if_pos hr1.le,
    convolution_eq_closed xi z Dt G hz hr0 hr1]
  rfl

theorem closedConvolution_contDiff (xi : ℝ) (z Dt G : ι → ℝ) :
    ContDiff ℝ ∞ (closedConvolution xi z Dt G) := by
  unfold closedConvolution coreCoreValue tailCoreValue tailTailValue branchValue
    FiniteYukawa.primitive FiniteYukawa.polyPrimitive FiniteYukawa.expPrimitive
    coreDerivativeExp tailDerivativeExp
  fun_prop

/-- The actual multi-tail core has no interior geometric junction for a pure fluid.
This is a spatial statement, not a claim about a global thermodynamic root branch. -/
theorem correlation_contDiffOn_core (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t) :
    ContDiffOn ℝ ∞ (correlation xi z Dt G) (Ioo (0 : ℝ) 1) := by
  have hn : ContDiff ℝ ∞ (fun r => -qPrimeCore xi z Dt G r +
      rhoOf xi * closedConvolution xi z Dt G r) := by
    apply ContDiff.add
    · unfold qPrimeCore
      fun_prop
    · exact contDiff_const.mul (closedConvolution_contDiff xi z Dt G)
  have hc : ContDiffOn ℝ ∞ (closedCorrelation xi z Dt G) (Ioo (0 : ℝ) 1) :=
    hn.contDiffOn.div (by fun_prop) (fun r hr => mul_ne_zero
      (mul_ne_zero two_ne_zero pi_ne_zero) hr.1.ne')
  apply hc.congr
  intro r hr
  exact correlation_core_eq_closed xi z Dt G hz hr.1 hr.2

end FMSA.ExactMSA.MultiTail
