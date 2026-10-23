import LeanCode.YukawaOZ.MSAMultiTailRDFFourier

/-! Actual RDF Fourier OZ identity, rather than a meromorphic symbol identity.
The constructed hard core is checked together with this equation. -/
noncomputable section
open MeasureTheory Set Filter Topology
open FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

theorem complexP_conj (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) :
    star (complexP xi z Dt G s) = complexP xi z Dt G (star s) := by
  simp [complexP, RDFAlgebra.P, RDFAlgebra.polyP, RDFAlgebra.tailP, map_sum]

theorem reconstructedFactor_axis_conj (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    star (reconstructedFactor xi z Dt G ((k : ℂ) * Complex.I)) =
      reconstructedFactor xi z Dt G (-((k : ℂ) * Complex.I)) := by
  rw [show -((k : ℂ) * Complex.I) = ((-k : ℝ) : ℂ) * Complex.I by push_cast; ring,
    reconstructedFactor_axis xi z Dt G hz hk,
    reconstructedFactor_axis xi z Dt G hz (neg_ne_zero.mpr hk), Qre_neg xi z Dt G hz hk,
    Qim_neg xi z Dt G hz hk]
  simp

theorem shiftedMomentSymbol_transfer (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) {k : ℝ} (hk : k ≠ 0) :
    (2 * Real.pi * rhoOf xi : ℂ) * shiftedMomentSymbol xi z Dt G ((k : ℂ) * Complex.I) *
        reconstructedFactor xi z Dt G ((k : ℂ) * Complex.I) =
      Complex.exp (-((k : ℂ) * Complex.I)) * complexP xi z Dt G ((k : ℂ) * Complex.I) := by
  have h := causalMoment_abel_transfer xi z Dt G hz he (s := (k : ℂ) * Complex.I)
    (by simp) (imaginary_nonzero hk) (fun u => imaginary_rate_nonzero (z u) k (hz u))
  rw [actualFactor_axis xi z Dt G hz hk] at h
  unfold shiftedMomentSymbol
  linear_combination Complex.exp (-((k : ℂ) * Complex.I)) * h

def axisDenominator (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) : ℝ :=
  (1 - rhoOf xi * Qre xi z Dt G k) ^ 2 + (rhoOf xi * Qim xi z Dt G k) ^ 2

/-- A real BH root plus integrable excess gives the Fourier OZ equation for
the actual constructed h, with no RDF/hard-core/OZ conclusion as a premise. -/
theorem reconstructedH_fourier_oz (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    (hρ : rhoOf xi ≠ 0) (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0))
    {k : ℝ} (hk : k ≠ 0) :
    radial_fourier (reconstructedH xi z Dt G) k = radial_fourier (correlation xi z Dt G) k +
      rhoOf xi * radial_fourier (correlation xi z Dt G) k * radial_fourier (reconstructedH xi z Dt G) k := by
  let s : ℂ := (k : ℂ) * Complex.I
  let F := reconstructedFactor xi z Dt G s
  let Fm := reconstructedFactor xi z Dt G (-s)
  let U := shiftedMomentSymbol xi z Dt G s
  let p := complexP xi z Dt G s
  let D := axisDenominator xi z Dt G k
  have hs : s ≠ 0 := imaginary_nonzero hk
  have hprod : F * Fm = (D : ℂ) := reconstructedFactor_axis_product xi z Dt G hz hk
  have hFc : star F = Fm := reconstructedFactor_axis_conj xi z Dt G hz hk
  have hsc : star s = -s := by simp [s, star_mul]; ring
  have hpc : star p = complexP xi z Dt G (-s) := by
    rw [complexP_conj, hsc]
  have hExp : star (Complex.exp (-s)) = Complex.exp s := by
    rw [show star (Complex.exp (-s)) = Complex.exp (star (-s)) from (Complex.exp_conj (-s)).symm,
      star_neg, hsc, neg_neg]
  have hsym : s * ((D : ℂ) - 1) =
      Complex.exp (-s) * p * Fm - Complex.exp s * complexP xi z Dt G (-s) * F := by
    have hh := rdf_symbol_product_identity xi z K Dt G hxi hz hroot hs
      (fun u => imaginary_rate_nonzero (z u) k (hz u))
      (fun u => by
        intro h
        have hr := congrArg Complex.re h
        simp [s] at hr
        linarith [hz u])
    change s * (F * Fm - 1) = _ at hh
    rwa [hprod] at hh
  have ht : (2 * Real.pi * rhoOf xi : ℂ) * U * F = Complex.exp (-s) * p :=
    shiftedMomentSymbol_transfer xi z Dt G hz he hk
  have hfirst : Complex.exp (-s) * p * Fm = (2 * Real.pi * rhoOf xi : ℂ) * U * (D : ℂ) := by
    rw [← ht]
    calc
      _ = ((2 * Real.pi * rhoOf xi : ℂ) * U) * (F * Fm) := by ring
      _ = _ := by rw [hprod]
  have hsecond : Complex.exp s * complexP xi z Dt G (-s) * F = star (Complex.exp (-s) * p * Fm) := by
    rw [star_mul, star_mul, hExp, hpc, ← hFc, star_star]
    ring
  rw [hsecond, hfirst] at hsym
  have him := congrArg Complex.im hsym
  simp only [s, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.conj_im, mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero] at him
  norm_num at him
  have hH := reconstructedH_fourier xi z Dt G he hk
  change radial_fourier (reconstructedH xi z Dt G) k = -(4 * Real.pi / k) * U.im at hH
  have hD : D = 1 - rhoOf xi * radial_fourier (correlation xi z Dt G) k :=
    (factorization xi z Dt G k hz hk).symm
  have heq : rhoOf xi * radial_fourier (reconstructedH xi z Dt G) k * D = 1 - D := by
    field_simp [hk] at hH
    apply mul_right_cancel₀ hk
    linear_combination rhoOf xi * D * hH + him
  rw [hD] at heq
  apply mul_left_cancel₀ hρ
  linear_combination heq

end FMSA.ExactMSA.MultiTail
