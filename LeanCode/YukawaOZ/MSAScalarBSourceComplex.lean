import LeanCode.YukawaOZ.MSAScalarBSource
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFMoment

/-! Complex one-sided numerator, contact/density normalization, and an exact
Fourier zero obstruction. A physical zero exhibited numerically is not
represented as a Lean-certified existence theorem. -/
noncomputable section
open MeasureTheory Set Real
namespace FMSA.ExactMSA.ScalarBSource

theorem tailW_contact_identity (xi z D G : ℝ) :
    tailW xi z D G = D * exp z - tailC xi z D G * exp z := by
  have he : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  simp only [tailW, tailC, gam]
  calc
    _ = (2 * π * rhoOf xi * G * D / z) * (exp (-z) * exp z) := by rw [he]; ring
    _ = _ := by ring

/-- This is the actual BH Baxter integral, including its continuity term.
It is not the simpler hard-sphere-plus-undressed-tail surrogate. -/
theorem actualQ_real_integral (xi z D G s : ℝ) (hs : s ≠ 0) (hsz : 0 < s + z) :
    actualQ xi z D G s =
      1 - (∫ r in Ioi (0: ℝ), bhBaxterFn xi z D G r * exp (-s * r)) := by
  rw [bhBaxter_transform xi z D G s hs hsz]
  have he : exp (-(s + z))=exp (-s) * exp (-z) := by rw [← exp_add]; congr 1; ring
  have hzexp : exp z * exp (-z)=1 := by rw [← exp_add]; simp
  have ht : (-gam xi z G * D * exp z)*
      ((1 - exp (-(s + z))) / (s + z) - exp (-z) * ((1 - exp (-s)) / s))+
      D * exp z * (1 / (s + z)) =
      tailW xi z D G / (s + z) + tailC xi z D G * (1 - exp (-s)) / s+
        tailC xi z D G * exp (-s) / (s + z) := by
    rw [he, tailW_contact_identity]
    unfold tailC
    have hid : (-gam xi z G * D * exp z)*
        ((1 - exp (-s) * exp (-z)) / (s + z) - exp (-z) * ((1 - exp (-s)) / s))+
        D * exp z * (1 / (s + z)) =
        (D * exp z - gam xi z G * D * exp z) / (s + z)+
          (gam xi z G * D) * (exp z * exp (-z)) * (1 - exp (-s)) / s+
          (gam xi z G * D) * (exp z * exp (-z)) * exp (-s) / (s + z) := by ring
    rw [hid, hzexp]
    ring
  unfold actualQ qMoment
  linear_combination (rhoOf xi) * ht

theorem actualQ_at_tail_rate (xi z D G : ℝ) (hz : 0 < z) (hv : 1 - xi ≠ 0) :
    actualQ xi z D G z = bhF xi z (D, G) := by
  rw [actualQ_real_integral xi z D G z hz.ne' (by linarith),
    bhBaxter_transform_at_z xi z D G hz hv]
  ring

def complexQ (xi z D G : ℝ) (s : ℂ) : ℂ :=
  1 - (rhoOf xi : ℂ) * qMoment (msaQp xi z D G : ℂ) (msaA xi z D G : ℂ)
    (tailW xi z D G : ℂ) (tailC xi z D G : ℂ) z s (Complex.exp (-s))
def complexF (xi z D G : ℝ) (s : ℂ) : ℂ :=
  sourceJ (msaA xi z D G : ℂ) (msaQp xi z D G : ℂ) (tailC xi z D G : ℂ) z s / (2 * π)

theorem actual_complex_source_cancellation (xi z D G : ℝ) (s : ℂ)
    (hz : z ≠ 0) (hv : 1 - xi ≠ 0) (hs : s ≠ 0) (hsz : s + (z: ℂ) ≠ 0) :
    complexQ xi z 0 G s * (complexF xi z D G s - complexF xi z 0 G s)-
      complexF xi z 0 G s * (complexQ xi z D G s - complexQ xi z 0 G s) =
        (kappa xi z D G : ℂ) / (2 * π * (s + (z: ℂ))) := by
  have h1 := background_first xi z D G hz hv
  have h2 := background_second xi z D G hz hv
  have h := symbol_cancellation (rhoOf xi : ℂ) (qp0 xi : ℂ) (bA0 xi : ℂ)
    (deltaA xi z D G : ℂ) (deltaQp xi z D G : ℂ) (tailW xi z D G : ℂ)
    (tailC xi z D G : ℂ) (z: ℂ) s (Complex.exp (-s)) hs (by exact_mod_cast hz) hsz
    (by exact_mod_cast h1) (by exact_mod_cast h2)
  simp only [complexQ, complexF, qMoment, sourceJ, deltaA, deltaQp, tailW, tailC,
    msaA, msaQp, kappa, mul_zero, zero_mul, add_zero, sub_zero, zero_div] at h ⊢
  push_cast at h ⊢
  convert congrArg (fun x : ℂ => x / (2 * π)) h using 1 <;> field_simp <;> ring

theorem sourceKernel_complex_laplace (xi z D G : ℝ) (s : ℂ)
    (hsz : 0 < s.re + z) :
    FMSA.causalComplexLaplace (sourceKernel xi z D G) s =
      (kappa xi z D G : ℂ) / (2 * π * (s + (z: ℂ))) := by
  have he : (fun r : ℝ => (sourceKernel xi z D G r : ℂ) * Complex.exp (-s * r)) =
      fun r : ℝ => ((kappa xi z D G / (2 * π) : ℝ) : ℂ) * Complex.exp (-(s + (z: ℂ)) * r) := by
    funext r
    unfold sourceKernel
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold FMSA.causalComplexLaplace
  rw [he, integral_const_mul, integral_exp_mul_complex_Ioi
    (by simpa using (neg_neg_of_pos hsz))]
  push_cast
  simp only [mul_zero, Complex.exp_zero, neg_div_neg_eq]
  field_simp

def contactSource (xi z D G : ℝ) : ℝ → ℝ :=
  MultiTailMixture.causalShift (fun r => rhoOf xi * kappa xi z D G * exp (-z * r)) 1

theorem contactSource_support (xi z D G r : ℝ) (hr : r < 1) :
    contactSource xi z D G r = 0 :=
  MultiTailMixture.causalShift_eq_zero_below _ _ _ hr

theorem contactSource_complex_laplace (xi z D G : ℝ) (s : ℂ)
    (hsz : 0 < s.re + z) :
    FMSA.causalComplexLaplace (contactSource xi z D G) s =
      (rhoOf xi : ℂ) * Complex.exp (-s) * (kappa xi z D G : ℂ) / (s + (z: ℂ)) := by
  have he : (fun r => rhoOf xi * kappa xi z D G * exp (-z * r)) =
      fun r => (2 * π * rhoOf xi) * sourceKernel xi z D G r := by
    funext r
    unfold sourceKernel
    field_simp
  have hi : FMSA.causalComplexLaplace (fun r => (2 * π * rhoOf xi) * sourceKernel xi z D G r) s =
      (2 * π * (rhoOf xi : ℂ)) * FMSA.causalComplexLaplace (sourceKernel xi z D G) s := by
    unfold FMSA.causalComplexLaplace
    simp only [Complex.ofReal_mul]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    push_cast
    ring
  unfold contactSource FMSA.causalComplexLaplace
  rw [MultiTailMixture.causalShift_positive_complex_laplace _ 1 one_pos s, he, hi,
    sourceKernel_complex_laplace xi z D G s hsz]
  simp only [Complex.ofReal_one, mul_one]
  field_simp

def paperB1 (rho K F0 z : ℝ) (s : ℂ) : ℂ :=
  2 * π * (rho: ℂ) * K * Complex.exp (-s) / ((F0: ℂ) ^ 2 * (s + (z: ℂ)))

theorem first_contact_source_paper (xi z K G D1 : ℝ) (s : ℂ)
    (hz : z ≠ 0) (hv : 1 - xi ≠ 0) (hF : F0 xi z ≠ 0)
    (hbase : 2 * π * G * F0 xi z = bhP0 xi z)
    (hD1 : D1 = 2 * π * K / (z * F0 xi z)) :
    (rhoOf xi : ℂ) * Complex.exp (-s) * ((kappa xi z 1 G * D1 : ℝ): ℂ) / (s + (z: ℂ)) =
      paperB1 (rhoOf xi) K (F0 xi z) z s := by
  rw [first_source_amplitude xi z K G D1 hz hv hF hbase hD1]
  unfold paperB1
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def firstRadialDCF (Q : ℂ → ℂ) (B : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Q s ^ 2 * B (-s) - Q (-s) ^ 2 * B s) / s

/-- Exact boundary criterion: a zero of Q_- produces a nonremovable Fourier
numerator whenever Q_+ and the one-sided source at -s are nonzero. -/
theorem actual_first_fourier_zero_obstruction (Q B : ℂ → ℂ) (s : ℂ)
    (hs : s ≠ 0) (hminus : Q (-s) = 0) (hplus : Q s ≠ 0) (hB : B (-s) ≠ 0) :
    ∀ Beff : ℂ, firstRadialDCF Q B s ≠ Q (-s) ^ 2 * Beff := by
  intro Beff
  apply BSource.fourier_zero_obstruction _ _ _ hminus
  simp only [firstRadialDCF, hminus, zero_pow (by norm_num : 2 ≠ 0), zero_mul, sub_zero]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hplus) hB) hs

end FMSA.ExactMSA.ScalarBSource
