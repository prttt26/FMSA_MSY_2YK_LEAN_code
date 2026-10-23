import LeanCode.YukawaOZMix.MSAMultiTailMixtureTransform
import LeanCode.YukawaOZMix.MixtureRowSum

/-! Actual complex transform of the unequal-diameter finite-tail matrix Q.
The support edge may be negative; no causal zero-extension at r=0 is imposed.
This is an integral identification, not a matrix DCF/core certificate. -/
noncomputable section
open MeasureTheory Set Filter Real
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def QhatComplex (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (s : ℂ) (i j : Fin N) : ℂ :=
  Complex.exp (-s * (edgeLo σ i j : ℂ)) *
    ((1 - s * (σ i : ℂ) - Complex.exp (-s * (σ i : ℂ))) / s ^ 2 * (qp i j : ℂ) +
      (1 - s * (σ i : ℂ) + (s * (σ i : ℂ)) ^ 2 / 2 - Complex.exp (-s * (σ i : ℂ))) /
        s ^ 3 * (A j : ℂ) +
      ∑ t, ((W t i j : ℂ) / (s + (z t : ℂ)) +
        (C t i j : ℂ) * (1 - Complex.exp (-s * (σ i : ℂ))) / s)) +
    ∑ t, (C t i j : ℂ) * Complex.exp (-s * (edgeHi σ i j : ℂ)) / (s + (z t : ℂ))

def shiftedExpComplex (z b : ℝ) (s : ℂ) (r : ℝ) : ℂ :=
  (exp (-z * (r - b)) : ℂ) * Complex.exp (-s * r)

theorem shiftedExpComplex_eq (z b : ℝ) (s : ℂ) (r : ℝ) :
    shiftedExpComplex z b s r =
      Complex.exp ((z : ℂ) * b) * Complex.exp (-(s + (z : ℂ)) * r) := by
  unfold shiftedExpComplex
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem shiftedExpComplex_integrable (z b : ℝ) (s : ℂ) (h : 0 < s.re + z) :
    IntegrableOn (shiftedExpComplex z b s) (Ioi b) := by
  change IntegrableOn (fun r => shiftedExpComplex z b s r) (Ioi b)
  simp_rw [shiftedExpComplex_eq]
  exact (integrableOn_exp_mul_complex_Ioi (a := -(s + (z : ℂ))) (by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]; linarith) b).const_mul _

theorem shiftedExpComplex_integral (z b : ℝ) (s : ℂ) (h : 0 < s.re + z) :
    (∫ r in Ioi b, shiftedExpComplex z b s r) = Complex.exp (-s * b) / (s + (z : ℂ)) := by
  simp_rw [shiftedExpComplex_eq]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (a := -(s + (z : ℂ))) (by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]; linarith)]
  simp only [div_neg, neg_div, neg_neg]
  rw [← mul_div_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem q_indicator_decomposition (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) (r : ℝ) :
    q z σ A qp W C i j r =
      (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
        (fun r => qp i j * (r - edgeHi σ i j) + A j / 2 * (r - edgeHi σ i j) ^ 2) r +
      ∑ t, (W t i j * (Ici (edgeLo σ i j)).indicator (fun r => exp (-z t * (r - edgeLo σ i j))) r +
        C t i j * (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator (fun _ => 1) r +
        C t i j * (Ioi (edgeHi σ i j)).indicator (fun r => exp (-z t * (r - edgeHi σ i j))) r) := by
  have hle : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
  unfold q
  by_cases hl : r < edgeLo σ i j
  · have h1 : r ∉ Icc (edgeLo σ i j) (edgeHi σ i j) := fun h => not_le_of_gt hl h.1
    have h2 : r ∉ Ici (edgeLo σ i j) := not_le_of_gt hl
    have h3 : r ∉ Ioi (edgeHi σ i j) := by intro h; change edgeHi σ i j < r at h; linarith
    simp only [if_pos hl, indicator_of_notMem h1, indicator_of_notMem h2, indicator_of_notMem h3,
      mul_zero, add_zero, Finset.sum_const_zero]
  · rw [if_neg hl]
    have hlo : r ∈ Ici (edgeLo σ i j) := le_of_not_gt hl
    by_cases hh : r ≤ edgeHi σ i j
    · have h1 : r ∈ Icc (edgeLo σ i j) (edgeHi σ i j) := ⟨hlo, hh⟩
      have h3 : r ∉ Ioi (edgeHi σ i j) := not_lt_of_ge hh
      simp only [if_pos hh, indicator_of_mem h1, indicator_of_mem hlo, indicator_of_notMem h3,
        mul_one, mul_zero, add_zero]
    · have h1 : r ∉ Icc (edgeLo σ i j) (edgeHi σ i j) := fun h => hh h.2
      have h3 : r ∈ Ioi (edgeHi σ i j) := lt_of_not_ge hh
      simp only [if_neg hh, indicator_of_notMem h1, indicator_of_mem hlo, indicator_of_mem h3,
        mul_zero, add_zero, zero_add]

theorem QhatComplex_ofReal (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (s : ℝ) (i j : Fin N) :
    QhatComplex z σ A qp W C (s : ℂ) i j = (Qhat z σ A qp W C s i j : ℂ) := by
  unfold QhatComplex Qhat
  push_cast
  rfl

theorem QhatComplex_conj (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (s : ℂ) (i j : Fin N) :
    star (QhatComplex z σ A qp W C s i j) = QhatComplex z σ A qp W C (star s) i j := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    simp
  unfold QhatComplex
  simp only [map_add, map_mul, map_div₀, map_sub, map_pow, map_sum, star_ofNat,
    Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, htwo]
  simp

def qComplexPoly (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (s : ℂ) (i j : Fin N) (r : ℝ) : ℂ :=
  ((qp i j * (r - edgeHi σ i j) + A j / 2 * (r - edgeHi σ i j) ^ 2 : ℝ) : ℂ) *
    Complex.exp (-s * r)

def qComplexRow (z : ι → ℝ) (σ : Fin N → ℝ) (W C : TailMatrix ι N)
    (s : ℂ) (i j : Fin N) (u : ι) (r : ℝ) : ℂ :=
  (W u i j : ℂ) * (Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s) r +
    (C u i j : ℂ) * (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
      (fun r => Complex.exp (-s * r)) r +
    (C u i j : ℂ) * (Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s) r

theorem qComplexPoly_integrable (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (s : ℂ) (i j : Fin N) :
    Integrable ((Icc (edgeLo σ i j) (edgeHi σ i j)).indicator (qComplexPoly σ A qp s i j)) := by
  have hc : Continuous (qComplexPoly σ A qp s i j) := by unfold qComplexPoly; fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem qComplexRow_integrable (z : ι → ℝ) (σ : Fin N → ℝ) (W C : TailMatrix ι N)
    (s : ℂ) (i j : Fin N) (u : ι) (h : 0 < s.re + z u) :
    Integrable (qComplexRow z σ W C s i j u) := by
  have hW : Integrable ((Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (shiftedExpComplex_integrable (z u) (edgeLo σ i j) s h)).integrable_indicator measurableSet_Ici
  have hC : Integrable ((Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
      (fun r => Complex.exp (-s * r))) :=
    (by fun_prop : Continuous (fun r : ℝ => Complex.exp (-s * r))).integrableOn_Icc.integrable_indicator
      measurableSet_Icc
  have hT : Integrable ((Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s)) :=
    (shiftedExpComplex_integrable (z u) (edgeHi σ i j) s h).integrable_indicator measurableSet_Ioi
  exact ((hW.const_mul _).add (hC.const_mul _)).add (hT.const_mul _)

theorem q_complex_decomposition (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℂ) (i j : Fin N) :
    (fun r => (q z σ A qp W C i j r : ℂ) * Complex.exp (-s * r)) =
      (fun r => (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator (qComplexPoly σ A qp s i j) r +
        ∑ u, qComplexRow z σ W C s i j u r) := by
  funext r
  have hle : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
  by_cases hl : r < edgeLo σ i j
  · have h1 : r ∉ Icc (edgeLo σ i j) (edgeHi σ i j) := fun h => not_le_of_gt hl h.1
    have h2 : r ∉ Ici (edgeLo σ i j) := not_le_of_gt hl
    have h3 : r ∉ Ioi (edgeHi σ i j) := by intro h; change edgeHi σ i j < r at h; linarith
    simp only [q, if_pos hl, qComplexRow, indicator_of_notMem h1, indicator_of_notMem h2,
      indicator_of_notMem h3, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  · have hlo : r ∈ Ici (edgeLo σ i j) := le_of_not_gt hl
    by_cases hh : r ≤ edgeHi σ i j
    · have h1 : r ∈ Icc (edgeLo σ i j) (edgeHi σ i j) := ⟨hlo, hh⟩
      have h3 : r ∉ Ioi (edgeHi σ i j) := not_lt_of_ge hh
      simp only [q, if_neg hl, if_pos hh, qComplexRow, qComplexPoly, shiftedExpComplex,
        indicator_of_mem h1, indicator_of_mem hlo, indicator_of_notMem h3, mul_zero, add_zero]
      push_cast
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro u _; ring
    · have h1 : r ∉ Icc (edgeLo σ i j) (edgeHi σ i j) := fun h => hh h.2
      have h3 : r ∈ Ioi (edgeHi σ i j) := lt_of_not_ge hh
      simp only [q, if_neg hl, if_neg hh, qComplexRow, shiftedExpComplex,
        indicator_of_notMem h1, indicator_of_mem hlo, indicator_of_mem h3, mul_zero, add_zero, zero_add]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _; ring

theorem expComplex_interval (s : ℂ) (a b : ℝ) (hs : s ≠ 0) :
    (∫ r in a..b, Complex.exp (-s * r)) =
      (Complex.exp (-s * a) - Complex.exp (-s * b)) / s := by
  rw [integral_exp_mul_complex (neg_ne_zero.mpr hs)]
  ring

theorem qComplexPoly_integral (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (s : ℂ) (i j : Fin N) (hs : s ≠ 0) (hσ : 0 ≤ σ i) :
    (∫ r, (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator (qComplexPoly σ A qp s i j) r) =
      Complex.exp (-s * (edgeLo σ i j : ℂ)) *
        ((1 - s * (σ i : ℂ) - Complex.exp (-s * (σ i : ℂ))) / s ^ 2 * (qp i j : ℂ) +
          (1 - s * (σ i : ℂ) + (s * (σ i : ℂ)) ^ 2 / 2 - Complex.exp (-s * (σ i : ℂ))) /
            s ^ 3 * (A j : ℂ)) := by
  have he : edgeHi σ i j = edgeLo σ i j + σ i := by unfold edgeHi edgeLo; ring
  have hle : edgeLo σ i j ≤ edgeHi σ i j := by rw [he]; linarith
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  have hc : (∫ r in (edgeLo σ i j)..(edgeHi σ i j), qComplexPoly σ A qp s i j r) =
      ∫ r in (edgeLo σ i j)..(edgeLo σ i j + σ i), Complex.exp (-(s * r)) *
        ((qp i j : ℂ) * ((r : ℂ) - ((edgeLo σ i j + σ i : ℝ) : ℂ)) +
          (A j : ℂ) * ((r : ℂ) - ((edgeLo σ i j + σ i : ℝ) : ℂ)) ^ 2 / 2) := by
    rw [he]
    apply intervalIntegral.integral_congr
    intro r _
    unfold qComplexPoly
    rw [he]
    push_cast
    ring
  rw [hc, FMSA.MixtureBaxter.laplace_baxter_quad_c s (edgeLo σ i j) (σ i) (qp i j) (A j) hs]
  ring

theorem qComplexRow_integral (z : ι → ℝ) (σ : Fin N → ℝ) (W C : TailMatrix ι N)
    (s : ℂ) (i j : Fin N) (u : ι) (h : 0 < s.re + z u) (hs : s ≠ 0) (hσ : 0 ≤ σ i) :
    (∫ r, qComplexRow z σ W C s i j u r) =
      (W u i j : ℂ) * Complex.exp (-s * (edgeLo σ i j : ℂ)) / (s + (z u : ℂ)) +
        (C u i j : ℂ) * (Complex.exp (-s * (edgeLo σ i j : ℂ)) -
          Complex.exp (-s * (edgeHi σ i j : ℂ))) / s +
        (C u i j : ℂ) * Complex.exp (-s * (edgeHi σ i j : ℂ)) / (s + (z u : ℂ)) := by
  have hW : Integrable ((Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (shiftedExpComplex_integrable (z u) (edgeLo σ i j) s h)).integrable_indicator measurableSet_Ici
  have hC : Integrable ((Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
      (fun r => Complex.exp (-s * r))) :=
    (by fun_prop : Continuous (fun r : ℝ => Complex.exp (-s * r))).integrableOn_Icc.integrable_indicator
      measurableSet_Icc
  have hT : Integrable ((Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s)) :=
    (shiftedExpComplex_integrable (z u) (edgeHi σ i j) s h).integrable_indicator measurableSet_Ioi
  have ha : Integrable (fun r => (W u i j : ℂ) * (Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s) r) := hW.const_mul _
  have hb : Integrable (fun r => (C u i j : ℂ) * (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
      (fun r => Complex.exp (-s * r)) r) := hC.const_mul _
  have hc : Integrable (fun r => (C u i j : ℂ) * (Ioi (edgeHi σ i j)).indicator
      (shiftedExpComplex (z u) (edgeHi σ i j) s) r) := hT.const_mul _
  have hab : Integrable (fun r => (W u i j : ℂ) * (Ici (edgeLo σ i j)).indicator
      (shiftedExpComplex (z u) (edgeLo σ i j) s) r +
      (C u i j : ℂ) * (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
      (fun r => Complex.exp (-s * r)) r) := ha.add hb
  unfold qComplexRow
  rw [integral_add hab hc,
    integral_add ha hb, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    shiftedExpComplex_integral _ _ _ h, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show edgeLo σ i j ≤ edgeHi σ i j by
      unfold edgeLo edgeHi; linarith), expComplex_interval s _ _ hs,
    integral_indicator measurableSet_Ioi, shiftedExpComplex_integral _ _ _ h]
  ring

/-- Actual complex-weighted Q is integrable on the full line. -/
theorem q_complex_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (s : ℂ) (hsre : 0 ≤ s.re) (i j : Fin N) :
    Integrable (fun r : ℝ => (q z σ A qp W C i j r : ℂ) * Complex.exp (-s * r)) := by
  rw [q_complex_decomposition z σ A qp W C hσ s i j]
  exact (qComplexPoly_integrable σ A qp s i j).add
    (integrable_finsetSum _ (fun u _ => qComplexRow_integrable z σ W C s i j u
      (add_pos_of_nonneg_of_pos hsre (hz u))))

/-- The dictionary is the actual full-line transform, including negative
support edges. On the imaginary axis it is the actual matrix Fourier Q. -/
theorem complexQ_integral_eq_Qhat (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    (∫ r : ℝ, (q z σ A qp W C i j r : ℂ) * Complex.exp (-s * r)) =
      QhatComplex z σ A qp W C s i j := by
  have ht : ∀ u, 0 < s.re + z u := fun u => add_pos_of_nonneg_of_pos hsre (hz u)
  rw [q_complex_decomposition z σ A qp W C hσ s i j,
    integral_add (qComplexPoly_integrable σ A qp s i j)
      (integrable_finsetSum _ (fun u _ => qComplexRow_integrable z σ W C s i j u (ht u))),
    integral_finsetSum _ (fun u _ => qComplexRow_integrable z σ W C s i j u (ht u)),
    qComplexPoly_integral σ A qp s i j hs (hσ i)]
  simp_rw [qComplexRow_integral z σ W C s i j _ (ht _) hs (hσ i)]
  have he : Complex.exp (-s * (edgeHi σ i j : ℂ)) =
      Complex.exp (-s * (edgeLo σ i j : ℂ)) * Complex.exp (-s * (σ i : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold edgeHi edgeLo
    push_cast
    ring
  have hrows :
      (∑ u, ((W u i j : ℂ) * Complex.exp (-s * (edgeLo σ i j : ℂ)) / (s + (z u : ℂ)) +
        (C u i j : ℂ) * (Complex.exp (-s * (edgeLo σ i j : ℂ)) -
          Complex.exp (-s * (edgeHi σ i j : ℂ))) / s +
        (C u i j : ℂ) * Complex.exp (-s * (edgeHi σ i j : ℂ)) / (s + (z u : ℂ)))) =
      Complex.exp (-s * (edgeLo σ i j : ℂ)) *
        (∑ u, ((W u i j : ℂ) / (s + (z u : ℂ)) +
          (C u i j : ℂ) * (1 - Complex.exp (-s * (σ i : ℂ))) / s)) +
        ∑ u, (C u i j : ℂ) * Complex.exp (-s * (edgeHi σ i j : ℂ)) / (s + (z u : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [he]
    ring
  rw [hrows]
  unfold QhatComplex
  ring

/-- Actual Fourier Q, with phase exp(-i*k*r), including k=0. -/
def fourierQ (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (k : ℝ) (i j : Fin N) : ℂ :=
  ∫ r : ℝ, (q z σ A qp W C i j r : ℂ) * Complex.exp (-(Complex.I * k) * r)

theorem fourierQ_eq_QhatComplex (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    fourierQ z σ A qp W C k i j = QhatComplex z σ A qp W C (Complex.I * k) i j := by
  exact complexQ_integral_eq_Qhat z hz σ A qp W C hσ _
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)) (by simp) i j

theorem fourierQ_conj (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    star (fourierQ z σ A qp W C k i j) = fourierQ z σ A qp W C (-k) i j := by
  unfold fourierQ
  simp only [Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with r
  simp [Complex.star_def, ← Complex.exp_conj]

end FMSA.ExactMSA.MultiTailMixture
