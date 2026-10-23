import LeanCode.YukawaOZ.MSAMultiTailBlockFourier

/-! Actual finite-tail convolution Fourier transform, with all cross terms. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def Qre (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) : ℝ :=
  Blocks.polyRe (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) k +
    ∑ t, Blocks.tailRe (z t) (W xi z Dt G t) (C xi z Dt G t) k

def Qim (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) : ℝ :=
  Blocks.polyIm (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) k +
    ∑ t, Blocks.tailIm (z t) (W xi z Dt G t) (C xi z Dt G t) k

def convolutionSine (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, convolution xi z Dt G r * sin (k * r)) +
    ∫ r in Ioi (1 : ℝ), convolution xi z Dt G r * sin (k * r)

private def coreConvolutionFn (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  Blocks.polynomialCore (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) r +
    (∑ u, Blocks.mixedCore (z u) (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G)
      (W xi z Dt G u) (C xi z Dt G u) r) +
    ∑ u, ∑ t, Blocks.pairCore (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
      (W xi z Dt G t) (C xi z Dt G t) r

private def tailConvolutionFn (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  (∑ u, Blocks.mixedExterior (z u) (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G)
    (W xi z Dt G u) (C xi z Dt G u) r) +
  ∑ u, ∑ t, Blocks.pairExterior (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
    (W xi z Dt G t) (C xi z Dt G t) r

theorem convolution_sine_intervalIntegrable (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) :
    IntervalIntegrable (fun r => convolution xi z Dt G r * sin (k * r)) volume 0 1 := by
  have hc : Continuous (fun r => coreConvolutionFn xi z Dt G r * sin (k * r)) := by
    unfold coreConvolutionFn
    fun_prop
  apply (hc.intervalIntegrable 0 1).congr
  intro r hr
  have hr' : r ∈ Ioc (0 : ℝ) 1 := by simpa using hr
  dsimp only
  rw [convolution_eq_blocks xi z Dt G hz hr'.1.le hr'.2]
  rfl

theorem convolution_sine_tailIntegrable (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) :
    IntegrableOn (fun r => convolution xi z Dt G r * sin (k * r)) (Ioi 1) := by
  have hc : IntegrableOn (fun r => tailConvolutionFn xi z Dt G r * sin (k * r)) (Ioi 1) := by
    unfold tailConvolutionFn
    simp_rw [add_mul, Finset.sum_mul]
    exact (integrable_finsetSum _ (fun u _ => Blocks.mixedExterior_sine_integrable
      (z u) _ _ _ _ k (hz u))).add
      (integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun t _ =>
        Blocks.pairExterior_sine_integrable (z u) (z t) _ _ _ _ k (hz u))))
  apply hc.congr_fun _ measurableSet_Ioi
  intro r hr
  dsimp only
  rw [convolution_exterior_eq_blocks xi z Dt G hz hr]
  rfl

theorem convolution_sine_integrable (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) :
    IntegrableOn (fun r => convolution xi z Dt G r * sin (k * r)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]
  exact ((convolution_sine_intervalIntegrable xi z Dt G k hz).1).union
    (convolution_sine_tailIntegrable xi z Dt G k hz)

theorem convolutionSine_eq_integral (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) :
    convolutionSine xi z Dt G k =
      ∫ r in Ioi (0 : ℝ), convolution xi z Dt G r * sin (k * r) := by
  exact intervalIntegral.integral_interval_add_Ioi'
    (convolution_sine_intervalIntegrable xi z Dt G k hz)
    (convolution_sine_tailIntegrable xi z Dt G k hz)

theorem convolutionSine_eq_blocks (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) :
    convolutionSine xi z Dt G k =
      (∫ r in (0 : ℝ)..1, Blocks.polynomialCore (amplitudeA xi z Dt G)
        (amplitudeQp xi z Dt G) r * sin (k * r)) +
      (∑ u, Blocks.mixedSine (z u) (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G)
        (W xi z Dt G u) (C xi z Dt G u) k) +
      ∑ u, ∑ t, Blocks.pairSine (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
        (W xi z Dt G t) (C xi z Dt G t) k := by
  have hc : (∫ r in (0 : ℝ)..1, convolution xi z Dt G r * sin (k * r)) =
      ∫ r in (0 : ℝ)..1, coreConvolutionFn xi z Dt G r * sin (k * r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa using hr
    dsimp only
    rw [convolution_eq_blocks xi z Dt G hz hr'.1 hr'.2]
    rfl
  have ht : (∫ r in Ioi (1 : ℝ), convolution xi z Dt G r * sin (k * r)) =
      ∫ r in Ioi (1 : ℝ), tailConvolutionFn xi z Dt G r * sin (k * r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [convolution_exterior_eq_blocks xi z Dt G hz hr]
    rfl
  unfold convolutionSine
  rw [hc, ht]
  unfold coreConvolutionFn tailConvolutionFn
  simp_rw [add_mul, Finset.sum_mul]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) 0 1),
    intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) 0 1)]
  have hi (u : ι) : (∫ r in (0 : ℝ)..1, ∑ t,
      Blocks.pairCore (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
        (W xi z Dt G t) (C xi z Dt G t) r * sin (k * r)) =
      ∑ t, ∫ r in (0 : ℝ)..1, Blocks.pairCore (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
        (W xi z Dt G t) (C xi z Dt G t) r * sin (k * r) :=
    intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) 0 1)
  simp_rw [hi]
  rw [integral_add (integrable_finsetSum _ (fun u _ => Blocks.mixedExterior_sine_integrable
    (z u) _ _ _ _ k (hz u))) (integrable_finsetSum _ (fun u _ => integrable_finsetSum _
      (fun t _ => Blocks.pairExterior_sine_integrable (z u) (z t) _ _ _ _ k (hz u)))),
    integral_finsetSum _ (fun u _ => Blocks.mixedExterior_sine_integrable (z u) _ _ _ _ k (hz u)),
    integral_finsetSum _ (fun u _ => integrable_finsetSum _
      (fun t _ => Blocks.pairExterior_sine_integrable (z u) (z t) _ _ _ _ k (hz u)))]
  simp_rw [integral_finsetSum _ (fun t _ =>
    Blocks.pairExterior_sine_integrable (z _) (z t) _ _ _ _ k (hz _))]
  unfold Blocks.mixedSine Blocks.pairSine
  simp only [Finset.sum_add_distrib]
  ring

private theorem double_sum_dot (a b : ι → ℝ) :
    (∑ u, ∑ t, (a u * a t + b u * b t)) = (∑ u, a u) ^ 2 + (∑ u, b u) ^ 2 := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The actual convolution sine integral, including every diagonal and cross-rate tail pair. -/
theorem convolutionSine_product (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) (hk : k ≠ 0) :
    convolutionSine xi z Dt G k = -k / 2 * (Qre xi z Dt G k ^ 2 + Qim xi z Dt G k ^ 2) := by
  let A := amplitudeA xi z Dt G
  let qp := amplitudeQp xi z Dt G
  let a := fun u => Blocks.tailRe (z u) (W xi z Dt G u) (C xi z Dt G u) k
  let b := fun u => Blocks.tailIm (z u) (W xi z Dt G u) (C xi z Dt G u) k
  let f := fun u t => Blocks.pairSine (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
    (W xi z Dt G t) (C xi z Dt G t) k
  have hpair : (∑ u, ∑ t, f u t) = -k / 2 * ((∑ u, a u) ^ 2 + (∑ u, b u) ^ 2) := by
    have hswap : (∑ u, ∑ t, f t u) = ∑ u, ∑ t, f u t := Finset.sum_comm
    have hh : (∑ u, ∑ t, (f u t + f t u)) = 2 * ∑ u, ∑ t, f u t := by
      simp only [Finset.sum_add_distrib]
      rw [hswap]
      ring
    have hp (u t : ι) : f u t + f t u = -k * (a u * a t + b u * b t) :=
      Blocks.pairSine_product (z u) (z t) _ _ _ _ k (hz u) (hz t) hk
    simp_rw [hp, ← Finset.mul_sum] at hh
    rw [double_sum_dot] at hh
    linarith
  rw [convolutionSine_eq_blocks xi z Dt G k hz, Blocks.polynomialCore_sine_product _ _ k hk]
  have hm : (∑ u, Blocks.mixedSine (z u) A qp (W xi z Dt G u) (C xi z Dt G u) k) =
      -k * (Blocks.polyRe A qp k * (∑ u, a u) + Blocks.polyIm A qp k * (∑ u, b u)) := by
    simp_rw [Blocks.mixedSine_product _ _ _ _ _ k (hz _) hk]
    simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    rfl
  change _ + (∑ u, Blocks.mixedSine (z u) A qp _ _ k) + (∑ u, ∑ t, f u t) = _
  rw [hm, hpair]
  unfold Qre Qim
  dsimp only [a, b, A, qp]
  ring

end FMSA.ExactMSA.MultiTail
