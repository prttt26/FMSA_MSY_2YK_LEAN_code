import LeanCode.YukawaOZ.MSAMultiTailConvolutionBlocks

/-! Actual finite-tail Baxter convolution assembled from the three elementary blocks. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

private theorem integral_bilinear (P Q : ℝ → ℝ) (U V : ι → ℝ → ℝ)
    (hP : Continuous P) (hQ : Continuous Q) (hU : ∀ u, Continuous (U u))
    (hV : ∀ t, Continuous (V t)) (a b : ℝ) :
    (∫ x in a..b, (P x + ∑ u, U u x) * (Q x + ∑ t, V t x)) =
      (∫ x in a..b, P x * Q x) + (∑ u, ∫ x in a..b, U u x * Q x) +
      (∑ t, ∫ x in a..b, P x * V t x) + ∑ u, ∑ t, ∫ x in a..b, U u x * V t x := by
  simp_rw [FiniteYukawa.finite_bilinear]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_finsetSum (f := fun u x => U u x * Q x)
      (fun u _ => ((hU u).mul hQ).intervalIntegrable a b),
    intervalIntegral.integral_finsetSum (f := fun t x => P x * V t x)
      (fun t _ => (hP.mul (hV t)).intervalIntegrable a b),
    intervalIntegral.integral_finsetSum (f := fun u x => ∑ t, U u x * V t x) (fun u _ =>
      Continuous.intervalIntegrable (by fun_prop) a b)]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact intervalIntegral.integral_finsetSum (f := fun t x => U u x * V t x)
    (fun t _ => ((hU u).mul (hV t)).intervalIntegrable a b)

def coreU (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) (u : ι) : ℝ :=
  -z u * W xi z Dt G u * exp (-z u * r)

def tailU (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) (u : ι) : ℝ :=
  -z u * (W xi z Dt G u + C xi z Dt G u * exp (z u)) * exp (-z u * r)

def coreQ (xi : ℝ) (z Dt G : ι → ℝ) (u : ι) (x : ℝ) : ℝ :=
  W xi z Dt G u * exp (-z u * x) + C xi z Dt G u

def tailQ (xi : ℝ) (z Dt G : ι → ℝ) (u : ι) (x : ℝ) : ℝ :=
  (W xi z Dt G u + C xi z Dt G u * exp (z u)) * exp (-z u * x)

theorem tailU_eq (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) (u : ι) :
    tailU xi z Dt G r u = tailDerivativeExp z Dt r u := by
  unfold tailU tailDerivativeExp V
  rw [W_add_C_exp]

theorem qCore_decomposition (xi : ℝ) (z Dt G : ι → ℝ) (x : ℝ) :
    qCore xi z Dt G x = Blocks.poly (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) x +
      ∑ u, coreQ xi z Dt G u x := rfl

theorem qPrimeCore_decomposition (xi : ℝ) (z Dt G : ι → ℝ) (r x : ℝ) :
    qPrimeCore xi z Dt G (x + r) =
      Blocks.polyPrime (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) (x + r) +
        ∑ u, coreU xi z Dt G r u * exp (-z u * x) := by
  rw [qPrimeCore_expPoly]
  unfold coreDerivativeExp coreU Blocks.polyPrime
  ring

theorem qTail_decomposition (xi : ℝ) (z Dt G : ι → ℝ) (x : ℝ) :
    qTail xi z Dt G x = ∑ u, tailQ xi z Dt G u x := by
  unfold qTail tailQ
  apply Finset.sum_congr rfl
  intro u _
  rw [show -z u * (x - 1) = z u + -z u * x by ring, exp_add]
  ring

theorem qPrimeTail_decomposition (xi : ℝ) (z Dt G : ι → ℝ) {r x : ℝ}
    (hxr : 1 < x + r) :
    qPrime xi z Dt G (x + r) = ∑ u, tailU xi z Dt G r u * exp (-z u * x) := by
  simp_rw [tailU_eq]
  exact qPrime_shift_tail_expPoly xi z Dt G hxr

private theorem pairTail_integrable (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    (r : ℝ) (u t : ι) : IntegrableOn
      (fun x => tailU xi z Dt G r u * exp (-z u * x) * tailQ xi z Dt G t x) (Ioi 1) := by
  have he : (fun x => tailU xi z Dt G r u * exp (-z u * x) * tailQ xi z Dt G t x) =
      fun x => tailU xi z Dt G r u * (W xi z Dt G t + C xi z Dt G t * exp (z t)) *
        exp (-(z u + z t) * x) := by
    funext x
    unfold tailQ
    rw [show -(z u + z t) * x = -z u * x + -z t * x by ring, exp_add]
    ring
  rw [he]
  exact (integrableOn_exp_mul_Ioi (by linarith [hz u, hz t] : -(z u + z t) < 0) 1).const_mul _

/-- Actual convolution as a polynomial block, a finite sum of mixed blocks, and
an ordered finite double sum of cross-rate tail-pair blocks. -/
theorem convolution_eq_blocks (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    convolution xi z Dt G r =
      Blocks.polynomialCore (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) r +
      (∑ u, Blocks.mixedCore (z u) (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G)
        (W xi z Dt G u) (C xi z Dt G u) r) +
      ∑ u, ∑ t, Blocks.pairCore (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
        (W xi z Dt G t) (C xi z Dt G t) r := by
  let A := amplitudeA xi z Dt G
  let qp := amplitudeQp xi z Dt G
  let P := Blocks.poly A qp
  let P' := fun x => Blocks.polyPrime A qp (x + r)
  let U := fun u x => coreU xi z Dt G r u * exp (-z u * x)
  let T := fun u x => tailU xi z Dt G r u * exp (-z u * x)
  let Q := coreQ xi z Dt G
  have hP : Continuous P := by unfold P Blocks.poly; fun_prop
  have hP' : Continuous P' := by unfold P' Blocks.polyPrime; fun_prop
  have hU : ∀ u, Continuous (U u) := by intro u; dsimp [U]; fun_prop
  have hT : ∀ u, Continuous (T u) := by intro u; dsimp [T]; fun_prop
  have hQ : ∀ u, Continuous (Q u) := by intro u; unfold Q coreQ; fun_prop
  have hm0 : 0 ≤ 1 - r := by linarith
  have hm1 : 1 - r ≤ 1 := by linarith
  have hb : IntervalIntegrable (fun x => qPrime xi z Dt G (x + r) * qCore xi z Dt G x)
      volume 0 1 := by
    apply ((convolutionIntegrand_integrable xi z Dt G hz r).intervalIntegrable).congr
    intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) 1 := by simpa using hx
    dsimp only
    rw [q, if_neg (by linarith [hx'.1]), if_pos hx'.2]
  have hb1 := hb.mono_set (show Set.uIcc (0 : ℝ) (1 - r) ⊆ Set.uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hm0, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hm1)
  have hb2 := hb.mono_set (show Set.uIcc (1 - r) (1 : ℝ) ⊆ Set.uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hm1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hm0 le_rfl)
  have hc : (∫ x in (0 : ℝ)..(1 - r), qPrime xi z Dt G (x + r) * qCore xi z Dt G x) =
      ∫ x in (0 : ℝ)..(1 - r), (P' x + ∑ u, U u x) * (P x + ∑ t, Q t x) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hm0
    intro x hx
    dsimp only
    rw [qPrime, if_neg (by linarith [hx.1]), if_pos (by linarith [hx.2]),
      qPrimeCore_decomposition, qCore_decomposition]
  have ht : (∫ x in (1 - r)..(1 : ℝ), qPrime xi z Dt G (x + r) * qCore xi z Dt G x) =
      ∫ x in (1 - r)..(1 : ℝ), (0 + ∑ u, T u x) * (P x + ∑ t, Q t x) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hm1
    intro x hx
    dsimp only
    rw [qPrimeTail_decomposition xi z Dt G (by linarith [hx.1]), qCore_decomposition]
    simp only [zero_add]
    rfl
  have he : (∫ x in Ioi (1 : ℝ), qPrime xi z Dt G (x + r) * qTail xi z Dt G x) =
      ∑ u, ∑ t, ∫ x in Ioi (1 : ℝ), T u x * tailQ xi z Dt G t x := by
    calc
      _ = ∫ x in Ioi (1 : ℝ), ∑ u, ∑ t, T u x * tailQ xi z Dt G t x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change 1 < x at hx
        dsimp only
        rw [qPrimeTail_decomposition xi z Dt G (by linarith [hx]), qTail_decomposition,
          Finset.sum_mul]
        simp only [Finset.mul_sum]
        rfl
      _ = _ := by
        rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _
          (fun t _ => pairTail_integrable xi z Dt G hz r u t))]
        simp_rw [integral_finsetSum _ (fun t _ => pairTail_integrable xi z Dt G hz r _ t)]
        rfl
  rw [convolution, ← intervalIntegral.integral_add_adjacent_intervals hb1 hb2, hc, ht, he,
    integral_bilinear P' P U Q hP' hP hU hQ,
    integral_bilinear (fun _ => 0) P T Q continuous_const hP hT hQ]
  simp only [zero_mul, intervalIntegral.integral_zero, Finset.sum_const_zero, add_zero, zero_add]
  have hm (u : ι) : Blocks.mixedIntegral (z u) A qp (W xi z Dt G u) (C xi z Dt G u) r =
      (∫ x in (0 : ℝ)..(1 - r), P' x * Q u x) +
      (∫ x in (0 : ℝ)..(1 - r), U u x * P x) +
      (∫ x in (1 - r)..(1 : ℝ), T u x * P x) := by
    unfold Blocks.mixedIntegral
    dsimp [P', P, Q, U, T, coreQ, coreU, tailU]
    simp only [mul_assoc]
  have hp (u t : ι) : Blocks.pairIntegral (z u) (z t)
      (W xi z Dt G u) (C xi z Dt G u) (W xi z Dt G t) (C xi z Dt G t) r =
      (∫ x in (0 : ℝ)..(1 - r), U u x * Q t x) +
      (∫ x in (1 - r)..(1 : ℝ), T u x * Q t x) +
      (∫ x in Ioi (1 : ℝ), T u x * tailQ xi z Dt G t x) := by
    unfold Blocks.pairIntegral
    dsimp [Q, U, T, coreQ, coreU, tailU, tailQ]
    simp only [mul_assoc]
  rw [Blocks.polynomialCore_integral]
  have hm' : (∑ u, Blocks.mixedCore (z u) A qp (W xi z Dt G u) (C xi z Dt G u) r) =
      (∑ u, ∫ x in (0 : ℝ)..(1 - r), P' x * Q u x) +
      (∑ u, ∫ x in (0 : ℝ)..(1 - r), U u x * P x) +
      (∑ u, ∫ x in (1 - r)..(1 : ℝ), T u x * P x) := by
    simp_rw [← Blocks.mixedIntegral_eq _ _ _ _ _ r (hz _), hm, Finset.sum_add_distrib]
  have hp' : (∑ u, ∑ t, Blocks.pairCore (z u) (z t)
      (W xi z Dt G u) (C xi z Dt G u) (W xi z Dt G t) (C xi z Dt G t) r) =
      (∑ u, ∑ t, ∫ x in (0 : ℝ)..(1 - r), U u x * Q t x) +
      (∑ u, ∑ t, ∫ x in (1 - r)..(1 : ℝ), T u x * Q t x) +
      (∑ u, ∑ t, ∫ x in Ioi (1 : ℝ), T u x * tailQ xi z Dt G t x) := by
    simp_rw [← Blocks.pairIntegral_eq _ _ _ _ _ _ r (hz _) (hz _), hp, Finset.sum_add_distrib]
  change _ = Blocks.polynomialCore A qp r + _ + _
  rw [hm', hp']
  ring

theorem Qhat_eq_blocks (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) :
    Qhat xi z Dt G s =
      Blocks.polyLaplace s (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) +
      ∑ t, Blocks.tailLaplace s (z t) (W xi z Dt G t) (C xi z Dt G t) := by
  unfold Qhat Blocks.polyLaplace Blocks.tailLaplace
  apply congrArg₂ (· + ·)
  · simp only [phi1, phi2]
    ring
  · apply Finset.sum_congr rfl
    intro t _
    ring

theorem convolution_exterior_eq_blocks (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {r : ℝ} (hr : 1 < r) :
    convolution xi z Dt G r =
      (∑ u, Blocks.mixedExterior (z u) (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G)
        (W xi z Dt G u) (C xi z Dt G u) r) +
      ∑ u, ∑ t, Blocks.pairExterior (z u) (z t) (W xi z Dt G u) (C xi z Dt G u)
        (W xi z Dt G t) (C xi z Dt G t) r := by
  rw [convolution_exterior xi z Dt G hz hr]
  simp_rw [Qhat_eq_blocks, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro u _
    unfold Blocks.mixedExterior
    rw [W_add_C_exp]
    ring
  · apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro t _
    unfold Blocks.pairExterior
    rw [W_add_C_exp]
    ring

end FMSA.ExactMSA.MultiTail
