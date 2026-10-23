import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearBoundary
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearAdmissibilityReduction

/-! Automatic finite admissibility for symmetric finite-tail amplitudes at
zero density, including nonzero coupling. Passing this structural test does
not imply RDF nonnegativity. Positive-density branch admissibility is separate. -/
noncomputable section
open MeasureTheory Set Real Polynomial FMSA.MatrixQ0 MSAMixture FMSA.HardSphere
open FMSA.ExactMSA.Breakpoint
open scoped BigOperators ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem nonlinearDilute_lower_value (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    nonlinearLowerQValue z 0 σ Dt G i j = -π*σ i*σ j+∑ u, Dt u i j := by
  simp only [nonlinearLowerQValue, nonlinearA_zero_density,
    nonlinearQp_zero_density, nonlinearW_zero_density, nonlinearC_zero_density,
    zero_add, edgeHi]
  ring

theorem nonlinearDilute_numerator_dictionary (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    nonlinearLNumerator z 0 σ Dt G i j =
      (Polynomial.C (2*π)+Polynomial.C (π*(σ j-σ i))*X+
        Polynomial.C (-π*σ i*σ j+∑ u, Dt u i j)*X^2)*nonlinearRatePolynomial z := by
  simp only [nonlinearLNumerator, nonlinearA_zero_density,
    nonlinearQp_zero_density, nonlinearW_zero_density, nonlinearDilute_lower_value,
    mul_zero, Polynomial.C_0, zero_mul, Finset.sum_const_zero, sub_zero]
  have he : 2*π*edgeHi σ i j-σ i*(2*π)=π*(σ j-σ i) := by
    unfold edgeHi
    ring
  rw [he]

theorem nonlinearDilute_JNumerator_reciprocal (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hDt : ∀ u i j, Dt u i j=Dt u j i) (i j : Fin N) :
    nonlinearJNumerator z 0 σ Dt G i j = nonlinearJNumerator z 0 σ Dt G j i := by
  simp only [nonlinearJNumerator, nonlinearA_zero_density,
    nonlinearQp_zero_density, nonlinearC_zero_density]
  have hR : edgeHi σ i j=edgeHi σ j i := by unfold edgeHi; ring
  simp_rw [hR, hDt]

theorem nonlinearDilute_LNumerator_neg_transpose (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hDt : ∀ u i j, Dt u i j=Dt u j i) (i j : Fin N) :
    (nonlinearLNumerator z 0 σ Dt G j i).comp (-X) =
      (Polynomial.C (2*π)+Polynomial.C (π*(σ j-σ i))*X+
        Polynomial.C (-π*σ i*σ j+∑ u, Dt u i j)*X^2)*
          (nonlinearRatePolynomial z).comp (-X) := by
  rw [nonlinearDilute_numerator_dictionary]
  simp only [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.C_comp,
    Polynomial.X_comp, Polynomial.pow_comp, neg_sq, mul_neg]
  simp_rw [← hDt]
  have he : -π*σ j*σ i+∑ u, Dt u i j = -π*σ i*σ j+∑ u, Dt u i j := by ring
  rw [he]
  have hc : Polynomial.C (π*(σ i-σ j)) = -Polynomial.C (π*(σ j-σ i)) := by
    rw [← map_neg]
    congr 1
    ring
  rw [hc]
  ring

theorem nonlinearDilute_admissibility_polynomials_zero (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hDt : ∀ u i j, Dt u i j=Dt u j i) (i j : Fin N) :
    nonlinearReciprocityPolynomial z 0 σ Dt G i j=0 ∧
    nonlinearWronskianUPolynomial z 0 σ Dt G i j=0 ∧
    nonlinearWronskianVPolynomial z 0 σ Dt G i j=0 := by
  have hj := nonlinearDilute_JNumerator_reciprocal z σ Dt G hDt i j
  simp only [nonlinearReciprocityPolynomial, nonlinearWronskianUPolynomial,
    nonlinearWronskianVPolynomial, Pi.zero_apply, Polynomial.C_0, zero_mul,
    Finset.sum_const_zero, add_zero, hj, sub_self]
  constructor
  · simp
  constructor
  · rw [nonlinearDilute_numerator_dictionary,
      nonlinearDilute_LNumerator_neg_transpose z σ Dt G hDt]
    simp only [nonlinearRationalDenominator, Polynomial.mul_comp,
      Polynomial.pow_comp, Polynomial.X_comp, neg_sq]
    ring
  · simp

theorem nonlinearDilute_automatic_finite_certificates (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hDt : ∀ u i j, Dt u i j=Dt u j i) :
    NonlinearFiniteReciprocityCertificate z 0 σ Dt G ∧
      NonlinearFiniteWronskianCertificate z 0 σ Dt G := by
  constructor
  · intro i j n _
    rw [(nonlinearDilute_admissibility_polynomials_zero z σ Dt G hDt i j).1]
    simp
  constructor
  · intro i j n _
    rw [(nonlinearDilute_admissibility_polynomials_zero z σ Dt G hDt i j).2.1]
    simp
  · intro i j n _
    rw [(nonlinearDilute_admissibility_polynomials_zero z σ Dt G hDt i j).2.2]
    simp

theorem nonlinearDilute_root_automatic_finite_certificates (z : ι → ℝ)
    (σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hroot : IsRoot z 0 σ K Dt G) (hK : ∀ u i j, K u i j=K u j i) :
    NonlinearFiniteReciprocityCertificate z 0 σ Dt G ∧
      NonlinearFiniteWronskianCertificate z 0 σ Dt G := by
  apply nonlinearDilute_automatic_finite_certificates
  intro u i j
  rw [nonlinearDt_zero_density_of_root z σ K Dt G hroot,
    nonlinearDt_zero_density_of_root z σ K Dt G hroot, hK u i j]

/-- The actual long-attractive/short-repulsive dilute counterexample passes
the exact finite admissibility check and the structural matrix is positive
definite. Nevertheless the same OZ solution has g<0 outside every core.
This is a zero-density theorem, not a canonical positive-density phase claim. -/
theorem nonlinearDilute_finitely_admissible_negative_RDF_counterexample
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) :
    let z : Fin 2 → ℝ := fun u => if u=0 then 1 else 20
    let K : TailMatrix (Fin 2) N := fun u a b => if u=0 then edgeHi σ a b else -3*edgeHi σ a b
    let Dt := nonlinearZeroDensityDt z K
    let G := nonlinearZeroDensityG z σ K
    IsRoot z 0 σ K Dt G ∧ NonlinearFiniteWronskianCertificate z 0 σ Dt G ∧
      nonlinearWeightedKernelBudget z 0 σ Dt G 0.5=0 ∧
      (∀ k : ℝ, Matrix.PosDef (1-Matrix.of (fun i j =>
        (sqrt ((0 : Fin N → ℝ) i) : ℂ)*(sqrt ((0 : Fin N → ℝ) j) : ℂ)*
          (radial_fourier (orderedRadialCorrelation z 0 σ K Dt G i j) k : ℂ)))) ∧
      (∀ a b, nonlinearH z 0 σ Dt G a b =ᵐ[volume.restrict (Ioi 0)] fun r =>
        orderedRadialCorrelation z 0 σ K Dt G a b r+
          radialMixtureConv (orderedRadialCorrelation z 0 σ K Dt G) (nonlinearH z 0 σ Dt G) 0 a b r) ∧
      (∀ a b, ∃ ε > 0, ∀ r ∈ Ico (edgeHi σ a b) (edgeHi σ a b+ε),
        nonlinearG z 0 σ Dt G a b r<0) := by
  dsimp only
  let z : Fin 2 → ℝ := fun u => if u=0 then 1 else 20
  let K : TailMatrix (Fin 2) N := fun u a b => if u=0 then edgeHi σ a b else -3*edgeHi σ a b
  have hK : ∀ u a b, K u a b=K u b a := by
    intro u a b
    simp only [K]
    split_ifs <;> unfold edgeHi <;> ring
  have h := nonlinear_long_attraction_short_repulsion_OZ_counterexample σ hσ
  change IsRoot z 0 σ K _ _ ∧ _ at h
  refine ⟨h.1, (nonlinearDilute_root_automatic_finite_certificates z σ K _ _ h.1 hK).2,
    nonlinearBudget_zero_density _ _ _ _ _, ?_, h.2.1, h.2.2⟩
  intro k
  simp only [Pi.zero_apply, sqrt_zero, Complex.ofReal_zero, zero_mul]
  have hm : (Matrix.of fun (_ _ : Fin N) => (0 : ℂ)) =
      (0 : Matrix (Fin N) (Fin N) ℂ) := rfl
  rw [hm, sub_zero]
  exact Matrix.PosDef.one

end FMSA.ExactMSA.MultiTailMixture
