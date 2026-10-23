import LeanCode.YukawaOZ.MSAMultiTailRDFNormalization

/-! Complex rational RDF identity at an actual finite-tail real BH root. -/
noncomputable section
open Complex Real
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def complexT (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) : ℂ :=
  RDFAlgebra.T (normA xi z Dt G : ℂ) (normQp xi z Dt G : ℂ) (normOffset xi z Dt G : ℂ)
    (fun u => (z u : ℂ)) (fun u => (normW xi z Dt G u : ℂ)) s
def complexP (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) : ℂ :=
  RDFAlgebra.P (normA xi z Dt G : ℂ) (normQp xi z Dt G : ℂ)
    (fun u => (z u : ℂ)) (fun u => (normC xi z Dt G u : ℂ)) s

theorem complexT_ofReal (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) :
    complexT xi z Dt G (s : ℂ) = (rationalT xi z Dt G s : ℂ) := by
  simp [complexT, rationalT, RDFAlgebra.T, RDFAlgebra.polyT, RDFAlgebra.tailT]

theorem complexP_ofReal (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) :
    complexP xi z Dt G (s : ℂ) = (rationalP xi z Dt G s : ℂ) := by
  simp [complexP, rationalP, RDFAlgebra.P, RDFAlgebra.polyP, RDFAlgebra.tailP]

/-- The identity is valid off the finitely many rational poles in the complex
plane. Positive, repeated rates require no distinctness hypothesis. -/
theorem rdf_complex_identity_of_root (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    {s : ℂ} (hs : s ≠ 0) (hp : ∀ u, s + (z u : ℂ) ≠ 0)
    (hm : ∀ u, s - (z u : ℂ) ≠ 0) :
    complexT xi z Dt G s * complexT xi z Dt G (-s) -
      complexP xi z Dt G s * complexP xi z Dt G (-s) = -s ^ 2 := by
  have hzr (u : ι) : (z u : ℂ) ≠ 0 := by exact_mod_cast (hz u).ne'
  have hsum (u t : ι) : (z u : ℂ) + (z t : ℂ) ≠ 0 := by
    exact_mod_cast (add_pos (hz u) (hz t)).ne'
  have he := RDFAlgebra.sum_identity (normA xi z Dt G : ℂ) (normQp xi z Dt G : ℂ)
    (normOffset xi z Dt G : ℂ) s (fun u => (z u : ℂ))
    (fun u => (normW xi z Dt G u : ℂ)) (fun u => (normC xi z Dt G u : ℂ))
    hs hzr hp hm hsum
  have hn := rdf_core_normalization xi z Dt G hxi (fun u => (hz u).ne')
  dsimp only at hn
  have hconst : ((normOffset xi z Dt G : ℂ) + ∑ u, (normW xi z Dt G u : ℂ)) ^ 2 -
      (∑ u, (normC xi z Dt G u : ℂ)) ^ 2 -
      2 * ((normA xi z Dt G : ℂ) - (normQp xi z Dt G : ℂ)) *
        (1 - ∑ u, (normW xi z Dt G u : ℂ) / (z u : ℂ)) -
      2 * (normA xi z Dt G : ℂ) * (∑ u, ((normW xi z Dt G u : ℂ) +
        (normC xi z Dt G u : ℂ)) / (z u : ℂ) ^ 2) -
      2 * (normQp xi z Dt G : ℂ) * (∑ u, (normC xi z Dt G u : ℂ) / (z u : ℂ)) = 0 := by
    exact_mod_cast hn.1
  have hpole : -(normA xi z Dt G : ℂ) ^ 2 + 2 * (normA xi z Dt G : ℂ) * (normQp xi z Dt G : ℂ) -
      2 * (normA xi z Dt G : ℂ) * (normOffset xi z Dt G : ℂ) -
      2 * (normA xi z Dt G : ℂ) * (∑ u, ((normW xi z Dt G u : ℂ) + (normC xi z Dt G u : ℂ))) = 0 := by
    exact_mod_cast hn.2
  rw [hconst, hpole, zero_div, add_zero] at he
  have hr (u : ι) : (normW xi z Dt G u : ℂ) * complexT xi z Dt G (z u : ℂ) -
      (normC xi z Dt G u : ℂ) * complexP xi z Dt G (z u : ℂ) = 0 := by
    rw [complexT_ofReal, complexP_ofReal]
    have h := rational_residue xi z Dt G hz u
    rw [hroot.2 u, sub_self, mul_zero] at h
    exact_mod_cast h
  change complexT xi z Dt G s * complexT xi z Dt G (-s) -
    complexP xi z Dt G s * complexP xi z Dt G (-s) + s ^ 2 +
    (∑ u, 2 * s ^ 2 / (s ^ 2 - (z u : ℂ) ^ 2) *
      ((normW xi z Dt G u : ℂ) * complexT xi z Dt G (z u : ℂ) -
        (normC xi z Dt G u : ℂ) * complexP xi z Dt G (z u : ℂ))) = 0 at he
  simp_rw [hr, mul_zero] at he
  simp only [Finset.sum_const_zero, add_zero] at he
  linear_combination he

def reconstructedFactor (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) : ℂ :=
  (complexT xi z Dt G s + Complex.exp (-s) * complexP xi z Dt G s) / s

/-- The reconstructed meromorphic symbol agrees with the actual Baxter
Laplace factor on the positive real axis (and wherever the real formula is regular). -/
theorem reconstructedFactor_ofReal (xi : ℝ) (z Dt G : ι → ℝ) {s : ℝ}
    (hs : s ≠ 0) (hp : ∀ u, s + z u ≠ 0) :
    reconstructedFactor xi z Dt G (s : ℂ) = (factor xi z Dt G s : ℂ) := by
  unfold reconstructedFactor
  rw [complexT_ofReal, complexP_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  norm_cast
  rw [rationalT_recenter xi z Dt G hs hp]
  field_simp [hs]
  ring

/-- The g-side source transfer and c-side Baxter factor satisfy the OZ
meromorphic identity. This is separate from actual RDF inverse-transform existence. -/
theorem rdf_symbol_product_identity (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    {s : ℂ} (hs : s ≠ 0) (hp : ∀ u, s + (z u : ℂ) ≠ 0)
    (hm : ∀ u, s - (z u : ℂ) ≠ 0) :
    s * (reconstructedFactor xi z Dt G s * reconstructedFactor xi z Dt G (-s) - 1) =
      Complex.exp (-s) * complexP xi z Dt G s * reconstructedFactor xi z Dt G (-s) -
      Complex.exp s * complexP xi z Dt G (-s) * reconstructedFactor xi z Dt G s := by
  have h := rdf_complex_identity_of_root xi z K Dt G hxi hz hroot hs hp hm
  have he : Complex.exp s * Complex.exp (-s) = 1 := by rw [← Complex.exp_add]; simp
  unfold reconstructedFactor
  have halg : s * (((complexT xi z Dt G s + Complex.exp (-s) * complexP xi z Dt G s) / s) *
      ((complexT xi z Dt G (-s) + Complex.exp s * complexP xi z Dt G (-s)) / (-s)) - 1) -
      (Complex.exp (-s) * complexP xi z Dt G s *
        ((complexT xi z Dt G (-s) + Complex.exp s * complexP xi z Dt G (-s)) / (-s)) -
      Complex.exp s * complexP xi z Dt G (-s) *
        ((complexT xi z Dt G s + Complex.exp (-s) * complexP xi z Dt G s) / s)) =
      -(complexT xi z Dt G s * complexT xi z Dt G (-s) -
        complexP xi z Dt G s * complexP xi z Dt G (-s) + s ^ 2) / s := by
    field_simp [hs]
    linear_combination complexP xi z Dt G s * complexP xi z Dt G (-s) * he
  simp only [neg_neg]
  apply sub_eq_zero.mp
  rw [halg, h]
  ring

end FMSA.ExactMSA.MultiTail
