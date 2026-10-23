import LeanCode.YukawaOZ.MSAMultiTailRDFSpectral

/-! Identification of the meromorphic BH RDF factor on the actual Fourier axis. -/
noncomputable section
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

theorem imaginary_nonzero {k : ℝ} (hk : k ≠ 0) : (k : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero

theorem imaginary_rate_nonzero (z k : ℝ) (hz : 0 < z) : (k : ℂ) * Complex.I + (z : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith

theorem axis_exp (k : ℝ) : Complex.exp (-((k : ℂ) * Complex.I)) =
    (Real.cos k : ℂ) - (Real.sin k : ℂ) * Complex.I := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I]
  simp [sub_eq_add_neg]

set_option maxHeartbeats 800000 in
theorem axis_poly_block (A qp k : ℝ) (hk : k ≠ 0) :
    (1 - (k : ℂ) * Complex.I - Complex.exp (-((k : ℂ) * Complex.I))) /
        ((k : ℂ) * Complex.I) ^ 2 * (qp : ℂ) +
      (1 - (k : ℂ) * Complex.I + ((k : ℂ) * Complex.I) ^ 2 / 2 -
        Complex.exp (-((k : ℂ) * Complex.I))) / ((k : ℂ) * Complex.I) ^ 3 * (A : ℂ) =
      (Blocks.polyRe A qp k : ℂ) + (Blocks.polyIm A qp k : ℂ) * Complex.I := by
  rw [axis_exp]
  unfold Blocks.polyRe Blocks.polyIm
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, Complex.mul_re, Complex.mul_im,
      pow_succ, Complex.I_re, Complex.I_im] <;>
    field_simp [hk] <;> ring

set_option maxHeartbeats 800000 in
theorem axis_tail_block (z W C k : ℝ) (hz : 0 < z) (hk : k ≠ 0) :
    ((W : ℂ) + (C : ℂ) * Complex.exp (-((k : ℂ) * Complex.I))) /
        ((k : ℂ) * Complex.I + (z : ℂ)) +
      (C : ℂ) * (1 - Complex.exp (-((k : ℂ) * Complex.I))) / ((k : ℂ) * Complex.I) =
      (Blocks.tailRe z W C k : ℂ) + (Blocks.tailIm z W C k : ℂ) * Complex.I := by
  rw [axis_exp]
  unfold Blocks.tailRe Blocks.tailIm
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, Complex.mul_re, Complex.mul_im,
      pow_succ, Complex.I_re, Complex.I_im] <;>
    field_simp [hk, show z ^ 2 + k ^ 2 ≠ 0 by positivity] <;> ring

theorem dictionary_scaling (ρ a h E s : ℂ) (z w c : ι → ℂ) :
    RDFAlgebra.dictionary (ρ * a) (ρ * h) z (fun u => ρ * w u) (fun u => ρ * c u) E s =
      ρ * RDFAlgebra.dictionary a h z w c E s := by
  have he : (∑ u, ((ρ * w u + ρ * c u * E) / (s + z u) + ρ * c u * (1 - E) / s)) =
      ρ * ∑ u, ((w u + c u * E) / (s + z u) + c u * (1 - E) / s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _; ring
  unfold RDFAlgebra.dictionary
  rw [he]
  ring

theorem dictionary_axis (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    RDFAlgebra.dictionary (amplitudeA xi z Dt G : ℂ) (amplitudeQp xi z Dt G : ℂ)
      (fun u => (z u : ℂ)) (fun u => (W xi z Dt G u : ℂ)) (fun u => (C xi z Dt G u : ℂ))
      (Complex.exp (-((k : ℂ) * Complex.I))) ((k : ℂ) * Complex.I) =
        (Qre xi z Dt G k : ℂ) + (Qim xi z Dt G k : ℂ) * Complex.I := by
  unfold RDFAlgebra.dictionary
  rw [axis_poly_block _ _ k hk]
  simp_rw [axis_tail_block _ _ _ k (hz _) hk]
  unfold Qre Qim
  push_cast
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  ring

theorem reconstructedFactor_dictionary (xi : ℝ) (z Dt G : ι → ℝ) {s : ℂ}
    (hs : s ≠ 0) (hp : ∀ u, s + (z u : ℂ) ≠ 0) :
    reconstructedFactor xi z Dt G s = 1 -
      RDFAlgebra.dictionary (normA xi z Dt G : ℂ) (normQp xi z Dt G : ℂ)
        (fun u => (z u : ℂ)) (fun u => (normW xi z Dt G u : ℂ))
        (fun u => (normC xi z Dt G u : ℂ)) (Complex.exp (-s)) s := by
  have ho : (normOffset xi z Dt G : ℂ) = (normQp xi z Dt G : ℂ) - (normA xi z Dt G : ℂ) / 2 -
      ∑ u, ((normW xi z Dt G u : ℂ) + (normC xi z Dt G u : ℂ)) := by simp [normOffset]
  have h := RDFAlgebra.recenter_identity (normA xi z Dt G : ℂ) (normQp xi z Dt G : ℂ)
    (Complex.exp (-s)) s (fun u => (z u : ℂ)) (fun u => (normW xi z Dt G u : ℂ))
      (fun u => (normC xi z Dt G u : ℂ)) hs hp
  rw [← ho] at h
  change complexT xi z Dt G s = s - s * _ - Complex.exp (-s) * complexP xi z Dt G s at h
  unfold reconstructedFactor
  rw [h]
  field_simp [hs]
  ring

theorem reconstructedFactor_axis (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    reconstructedFactor xi z Dt G ((k : ℂ) * Complex.I) =
      (1 - rhoOf xi * Qre xi z Dt G k : ℝ) - (rhoOf xi * Qim xi z Dt G k : ℝ) * Complex.I := by
  rw [reconstructedFactor_dictionary xi z Dt G (imaginary_nonzero hk)
    (fun u => imaginary_rate_nonzero (z u) k (hz u))]
  unfold normA normQp normW normC
  push_cast
  rw [dictionary_scaling, dictionary_axis xi z Dt G hz hk]
  push_cast
  ring

theorem Qre_neg (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) : Qre xi z Dt G (-k) = Qre xi z Dt G k := by
  rw [Qre_eq_integral xi z Dt G hz (neg_ne_zero.mpr hk), Qre_eq_integral xi z Dt G hz hk]
  simp [neg_mul, MeasureTheory.integral_neg]

theorem Qim_neg (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) : Qim xi z Dt G (-k) = -Qim xi z Dt G k := by
  rw [Qim_eq_neg_integral xi z Dt G hz (neg_ne_zero.mpr hk), Qim_eq_neg_integral xi z Dt G hz hk]
  simp [neg_mul, MeasureTheory.integral_neg]

theorem reconstructedFactor_axis_product (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    reconstructedFactor xi z Dt G ((k : ℂ) * Complex.I) *
      reconstructedFactor xi z Dt G (-((k : ℂ) * Complex.I)) =
      (((1 - rhoOf xi * Qre xi z Dt G k) ^ 2 + (rhoOf xi * Qim xi z Dt G k) ^ 2 : ℝ) : ℂ) := by
  rw [show -((k : ℂ) * Complex.I) = ((-k : ℝ) : ℂ) * Complex.I by push_cast; ring,
    reconstructedFactor_axis xi z Dt G hz hk,
    reconstructedFactor_axis xi z Dt G hz (neg_ne_zero.mpr hk), Qre_neg xi z Dt G hz hk,
    Qim_neg xi z Dt G hz hk]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> ring

end FMSA.ExactMSA.MultiTail
