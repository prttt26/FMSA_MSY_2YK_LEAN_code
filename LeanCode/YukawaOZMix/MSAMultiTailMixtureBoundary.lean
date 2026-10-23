import LeanCode.YukawaOZMix.MSAMultiTailMixtureSpectral

/-! Actual lower-edge terms in the finite-tail unequal-diameter Baxter relation.
The ordinary piecewise qPrime is not the distributional derivative across
its lower-edge jump. The boundary term is explicit, not silently discarded. -/
noncomputable section
open MeasureTheory Set Filter Real
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def lowerValue (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j : Fin N) : ℝ :=
  -qp i j * σ i + A j / 2 * (σ i) ^ 2 + ∑ u, (W u i j + C u i j)

theorem q_at_lowerEdge (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    q z σ A qp W C i j (edgeLo σ i j) = lowerValue σ A qp W C i j := by
  have hle : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
  simp only [q, lt_self_iff_false, if_false, if_pos hle, sub_self, mul_zero, exp_zero, mul_one]
  have he : edgeLo σ i j - edgeHi σ i j = -σ i := by unfold edgeLo edgeHi; ring
  rw [he]
  unfold lowerValue
  ring

/-- Correct ordered row convention annihilates every lower-edge jump term
in the positive-r cross-correlation derivative. -/
theorem lowerEdge_partner_zero (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j l : Fin N)
    (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r) :
    q z σ A qp W C j l (edgeLo σ i l - r) = 0 := by
  have he : edgeLo σ i l - r < edgeLo σ j l := by unfold edgeLo; linarith
  simp only [q, if_pos he]

theorem lowerEdge_jump_product_zero (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j l : Fin N)
    (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r) :
    lowerValue σ A qp W C i l * q z σ A qp W C j l (edgeLo σ i l - r) = 0 := by
  rw [lowerEdge_partner_zero z σ A qp W C i j l horder r hr, mul_zero]

theorem reflected_Q_zero_of_order (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N)
    (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r) :
    q z σ A qp W C j i (-r) = 0 := by
  have he : -r < edgeLo σ j i := by unfold edgeLo; linarith
  simp only [q, if_pos he]

def qPrimeComplexPoly (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (s : ℂ) (i j : Fin N) (r : ℝ) : ℂ :=
  ((qp i j + A j * (r - edgeHi σ i j) : ℝ) : ℂ) * Complex.exp (-s * r)

def qPrimeComplexRow (z : ι → ℝ) (σ : Fin N → ℝ) (W C : TailMatrix ι N)
    (s : ℂ) (i j : Fin N) (u : ι) (r : ℝ) : ℂ :=
  ((-z u * W u i j : ℝ) : ℂ) * (Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s) r +
    ((-z u * C u i j : ℝ) : ℂ) * (Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s) r

theorem qPrime_complex_decomposition (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℂ) (i j : Fin N) :
    (fun r => (qPrime z σ A qp W C i j r : ℂ) * Complex.exp (-s * r)) =
      (fun r => (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
        (qPrimeComplexPoly σ A qp s i j) r + ∑ u, qPrimeComplexRow z σ W C s i j u r) := by
  funext r
  have hle : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
  by_cases hl : r < edgeLo σ i j
  · have h1 : r ∉ Icc (edgeLo σ i j) (edgeHi σ i j) := fun h => not_le_of_gt hl h.1
    have h2 : r ∉ Ici (edgeLo σ i j) := not_le_of_gt hl
    have h3 : r ∉ Ioi (edgeHi σ i j) := by intro h; change edgeHi σ i j < r at h; linarith
    simp only [qPrime, if_pos hl, qPrimeComplexRow, indicator_of_notMem h1, indicator_of_notMem h2,
      indicator_of_notMem h3, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  · have hlo : r ∈ Ici (edgeLo σ i j) := le_of_not_gt hl
    by_cases hh : r ≤ edgeHi σ i j
    · have h1 : r ∈ Icc (edgeLo σ i j) (edgeHi σ i j) := ⟨hlo, hh⟩
      have h3 : r ∉ Ioi (edgeHi σ i j) := not_lt_of_ge hh
      simp only [qPrime, if_neg hl, if_pos hh, qPrimeComplexRow, qPrimeComplexPoly, shiftedExpComplex,
        indicator_of_mem h1, indicator_of_mem hlo, indicator_of_notMem h3, mul_zero, add_zero]
      push_cast
      rw [sub_mul, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      ring
    · have h1 : r ∉ Icc (edgeLo σ i j) (edgeHi σ i j) := fun h => hh h.2
      have h3 : r ∈ Ioi (edgeHi σ i j) := lt_of_not_ge hh
      simp only [qPrime, if_neg hl, if_neg hh, qPrimeComplexRow, shiftedExpComplex,
        indicator_of_notMem h1, indicator_of_mem hlo, indicator_of_mem h3, mul_zero, add_zero, zero_add]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      ring

theorem qPrimeComplexPoly_integrable (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (s : ℂ) (i j : Fin N) :
    Integrable ((Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
      (qPrimeComplexPoly σ A qp s i j)) := by
  have hc : Continuous (qPrimeComplexPoly σ A qp s i j) := by unfold qPrimeComplexPoly; fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem qPrimeComplexRow_integrable (z : ι → ℝ) (σ : Fin N → ℝ) (W C : TailMatrix ι N)
    (s : ℂ) (i j : Fin N) (u : ι) (h : 0 < s.re + z u) :
    Integrable (qPrimeComplexRow z σ W C s i j u) := by
  have hW : Integrable ((Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (shiftedExpComplex_integrable (z u) (edgeLo σ i j) s h)).integrable_indicator measurableSet_Ici
  have hT : Integrable ((Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s)) :=
    (shiftedExpComplex_integrable (z u) (edgeHi σ i j) s h).integrable_indicator measurableSet_Ioi
  exact (hW.const_mul _).add (hT.const_mul _)

theorem qPrime_complex_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (s : ℂ) (hsre : 0 ≤ s.re) (i j : Fin N) :
    Integrable (fun r : ℝ => (qPrime z σ A qp W C i j r : ℂ) * Complex.exp (-s * r)) := by
  rw [qPrime_complex_decomposition z σ A qp W C hσ s i j]
  exact (qPrimeComplexPoly_integrable σ A qp s i j).add
    (integrable_finsetSum _ (fun u _ => qPrimeComplexRow_integrable z σ W C s i j u
      (add_pos_of_nonneg_of_pos hsre (hz u))))

/-- Compact polynomial integration by parts, with the lower endpoint retained. -/
theorem qPrimeComplexPoly_integral (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (s : ℂ) (i j : Fin N) (hσ : 0 ≤ σ i) :
    (∫ r, (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator (qPrimeComplexPoly σ A qp s i j) r) =
      s * (∫ r, (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator (qComplexPoly σ A qp s i j) r) -
        ((-qp i j * σ i + A j / 2 * (σ i)^2 : ℝ) : ℂ) * Complex.exp (-s * (edgeLo σ i j : ℂ)) := by
  have hle : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith
  simp only [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  let P : ℝ → ℂ := fun r => (qp i j : ℂ) * ((r : ℂ) - (edgeHi σ i j : ℂ)) +
    (A j : ℂ) / 2 * ((r : ℂ) - (edgeHi σ i j : ℂ))^2
  have hd : ∀ r, HasDerivAt (qComplexPoly σ A qp s i j)
      (qPrimeComplexPoly σ A qp s i j r - s * qComplexPoly σ A qp s i j r) r := by
    intro r
    have h0 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := Complex.ofRealCLM.hasDerivAt
    have h1 := h0.sub_const (edgeHi σ i j : ℂ)
    have hP := (h1.const_mul (qp i j : ℂ)).add ((h1.pow 2).const_mul ((A j : ℂ) / 2))
    have hE := (h0.const_mul (-s)).cexp
    convert! (hP.mul hE) using 1
    · funext x
      unfold qComplexPoly
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
      push_cast
      ring
    · unfold qPrimeComplexPoly qComplexPoly
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
      push_cast
      ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (show IntervalIntegrable (fun r => qPrimeComplexPoly σ A qp s i j r -
      s * qComplexPoly σ A qp s i j r) volume (edgeLo σ i j) (edgeHi σ i j) by
      apply Continuous.intervalIntegrable
      unfold qPrimeComplexPoly qComplexPoly
      fun_prop)
  have hip : IntervalIntegrable (qPrimeComplexPoly σ A qp s i j) volume
      (edgeLo σ i j) (edgeHi σ i j) := by
    apply Continuous.intervalIntegrable
    unfold qPrimeComplexPoly
    fun_prop
  have his : IntervalIntegrable (fun r => s * qComplexPoly σ A qp s i j r) volume
      (edgeLo σ i j) (edgeHi σ i j) := by
    apply Continuous.intervalIntegrable
    unfold qComplexPoly
    fun_prop
  rw [intervalIntegral.integral_sub hip his, intervalIntegral.integral_const_mul] at hh
  have hb : qComplexPoly σ A qp s i j (edgeHi σ i j) = 0 := by simp [qComplexPoly]
  have ha : qComplexPoly σ A qp s i j (edgeLo σ i j) =
      ((-qp i j * σ i + A j / 2 * (σ i)^2 : ℝ) : ℂ) * Complex.exp (-s * (edgeLo σ i j : ℂ)) := by
    have he : edgeLo σ i j - edgeHi σ i j = -σ i := by unfold edgeLo edgeHi; ring
    unfold qComplexPoly
    rw [he]
    push_cast
    ring
  rw [hb, ha, zero_sub] at hh
  linear_combination hh

/-- Each exponential/constant tail block obeys the same endpoint identity. -/
theorem qPrimeComplexRow_integral (z : ι → ℝ) (σ : Fin N → ℝ) (W C : TailMatrix ι N)
    (s : ℂ) (i j : Fin N) (u : ι) (h : 0 < s.re + z u) (hs : s ≠ 0) (hσ : 0 ≤ σ i) :
    (∫ r, qPrimeComplexRow z σ W C s i j u r) =
      s * (∫ r, qComplexRow z σ W C s i j u r) -
        ((W u i j + C u i j : ℝ) : ℂ) * Complex.exp (-s * (edgeLo σ i j : ℂ)) := by
  have hW : Integrable ((Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (shiftedExpComplex_integrable (z u) (edgeLo σ i j) s h)).integrable_indicator measurableSet_Ici
  have hT : Integrable ((Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s)) :=
    (shiftedExpComplex_integrable (z u) (edgeHi σ i j) s h).integrable_indicator measurableSet_Ioi
  have ha : Integrable (fun r => ((-z u * W u i j : ℝ) : ℂ) * (Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s) r) := hW.const_mul _
  have hb : Integrable (fun r => ((-z u * C u i j : ℝ) : ℂ) * (Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s) r) := hT.const_mul _
  unfold qPrimeComplexRow
  rw [integral_add ha hb, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    shiftedExpComplex_integral _ _ _ h, integral_indicator measurableSet_Ioi,
    shiftedExpComplex_integral _ _ _ h, qComplexRow_integral z σ W C s i j u h hs hσ]
  have hden : s + (z u : ℂ) ≠ 0 := by
    intro h0
    have hh := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hh
    linarith
  push_cast
  field_simp [hs, hden]
  ring

/-- Actual full-line transform of the ordinary piecewise derivative Q'.
The lower-edge jump is explicitly retained. -/
theorem qPrime_integral_boundary (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    (∫ r : ℝ, (qPrime z σ A qp W C i j r : ℂ) * Complex.exp (-s * r)) =
      s * (∫ r : ℝ, (q z σ A qp W C i j r : ℂ) * Complex.exp (-s * r)) -
        (lowerValue σ A qp W C i j : ℂ) * Complex.exp (-s * (edgeLo σ i j : ℂ)) := by
  have ht : ∀ u, 0 < s.re + z u := fun u => add_pos_of_nonneg_of_pos hsre (hz u)
  rw [qPrime_complex_decomposition z σ A qp W C hσ s i j,
    q_complex_decomposition z σ A qp W C hσ s i j,
    integral_add (qPrimeComplexPoly_integrable σ A qp s i j)
      (integrable_finsetSum _ (fun u _ => qPrimeComplexRow_integrable z σ W C s i j u (ht u))),
    integral_add (qComplexPoly_integrable σ A qp s i j)
      (integrable_finsetSum _ (fun u _ => qComplexRow_integrable z σ W C s i j u (ht u))),
    integral_finsetSum _ (fun u _ => qPrimeComplexRow_integrable z σ W C s i j u (ht u)),
    integral_finsetSum _ (fun u _ => qComplexRow_integrable z σ W C s i j u (ht u)),
    qPrimeComplexPoly_integral σ A qp s i j (hσ i)]
  simp_rw [qPrimeComplexRow_integral z σ W C s i j _ (ht _) hs (hσ i)]
  unfold lowerValue
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end FMSA.ExactMSA.MultiTailMixture
