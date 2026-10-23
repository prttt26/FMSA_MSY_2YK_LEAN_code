import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDistinctPoles

/-! Residues at a rate value collect all tail labels with that rate.
The actual BH equations cancel the collected residues, without distinctness
of rates or an assumption on the symmetry of unknown moments. -/
noncomputable section
open Real Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearRateFibre (z : ι → ℝ) (r : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun u => z u = r)

def nonlinearRateFibreMatrix (z : ι → ℝ) (A : TailMatrix ι N) (r : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := ∑ u ∈ nonlinearRateFibre z r, Matrix.of (A u)

theorem nonlinearRateFibre_mem (z : ι → ℝ) (r : ℝ) (u : ι) :
    u ∈ nonlinearRateFibre z r ↔ z u = r := by
  classical
  simp [nonlinearRateFibre]

theorem nonlinearRateFibreMatrix_entry (z : ι → ℝ) (A : TailMatrix ι N)
    (r : ℝ) (i j : Fin N) :
    nonlinearRateFibreMatrix z A r i j = ∑ u ∈ nonlinearRateFibre z r, A u i j := by
  simp [nonlinearRateFibreMatrix, Matrix.sum_apply]

theorem nonlinearDistinctJNumerator_eval_neg_rate
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) (i j : Fin N) :
    (nonlinearDistinctJNumerator z ρ σ Dt G i j).eval (-r) =
      r^3 * (nonlinearDistinctRatePolynomialExcept z r).eval (-r) *
        nonlinearRateFibreMatrix z (C z ρ σ Dt G) r i j := by
  classical
  simp only [nonlinearDistinctJNumerator, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finset_sum,
    nonlinearDistinctRatePolynomial_eval_neg_rate z r hr, mul_zero, zero_add]
  rw [nonlinearRateFibreMatrix_entry, Finset.mul_sum]
  rw [← Finset.sum_subset (show nonlinearRateFibre z r ⊆ Finset.univ from Finset.subset_univ _)
    (fun u _ hu => by
      have hne : r ≠ z u := by simpa [eq_comm] using (not_congr (nonlinearRateFibre_mem z r u)).mp hu
      rw [nonlinearDistinctRatePolynomialExcept_eval_other_neg_rate z r (z u) hr hne,
        mul_zero])]
  apply Finset.sum_congr rfl
  intro u hu
  rw [(nonlinearRateFibre_mem z r u).mp hu]
  ring

theorem nonlinearDistinctLNumerator_eval_neg_rate
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) (i j : Fin N) :
    (nonlinearDistinctLNumerator z ρ σ Dt G i j).eval (-r) =
      -(r^3 * (nonlinearDistinctRatePolynomialExcept z r).eval (-r)) *
        nonlinearRateFibreMatrix z (W z ρ Dt G) r i j := by
  classical
  simp only [nonlinearDistinctLNumerator, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_finset_sum, nonlinearDistinctRatePolynomial_eval_neg_rate z r hr,
    mul_zero, zero_sub]
  rw [nonlinearRateFibreMatrix_entry]
  have he : (∑ u, z u * W z ρ Dt G u i j * (-r)^2 *
      (nonlinearDistinctRatePolynomialExcept z (z u)).eval (-r)) =
      ∑ u ∈ nonlinearRateFibre z r, z u * W z ρ Dt G u i j * (-r)^2 *
        (nonlinearDistinctRatePolynomialExcept z (z u)).eval (-r) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    have hne : r ≠ z u := by simpa [eq_comm] using (not_congr (nonlinearRateFibre_mem z r u)).mp hu
    rw [nonlinearDistinctRatePolynomialExcept_eval_other_neg_rate z r (z u) hr hne,
      mul_zero]
  rw [he, neg_mul, neg_inj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [(nonlinearRateFibre_mem z r u).mp hu]
  ring

theorem nonlinearRoot_collected_yukawa_residues_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i) (r : ℝ) :
    let W := nonlinearRateFibreMatrix z (W z ρ Dt G) r
    let C := nonlinearRateFibreMatrix z (C z ρ σ Dt G) r
    let J := nonlinearRationalJ z ρ σ Dt G r
    let L := nonlinearRationalL z ρ σ Dt G r
    let P := Matrix.diagonal ρ
    (r • W.transpose - C*P*J.transpose - L*P*W.transpose = 0) ∧
    (r • W - J*P*C.transpose - W*P*L.transpose = 0) ∧
    (J*P*W.transpose - W*P*J.transpose = 0) ∧
    (r • (C-C.transpose) + L*P*C.transpose - C*P*L.transpose = 0) := by
  classical
  have hh (u : ι) (hu : u ∈ nonlinearRateFibre z r) :=
    nonlinearRoot_yukawa_residue_matrices_zero z ρ σ K Dt G hz hroot hK u
  have ha (u : ι) (hu : u ∈ nonlinearRateFibre z r) :
      z u = r := (nonlinearRateFibre_mem z r u).mp hu
  have h1 : (∑ u ∈ nonlinearRateFibre z r,
      (r • (Matrix.of (W z ρ Dt G u)).transpose -
        Matrix.of (C z ρ σ Dt G u)*Matrix.diagonal ρ*
          (nonlinearRationalJ z ρ σ Dt G r).transpose -
        nonlinearRationalL z ρ σ Dt G r*Matrix.diagonal ρ*
          (Matrix.of (W z ρ Dt G u)).transpose)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simpa only [ha u hu] using (hh u hu).1
  have h2 : (∑ u ∈ nonlinearRateFibre z r,
      (r • Matrix.of (W z ρ Dt G u) -
        nonlinearRationalJ z ρ σ Dt G r*Matrix.diagonal ρ*
          (Matrix.of (C z ρ σ Dt G u)).transpose -
        Matrix.of (W z ρ Dt G u)*Matrix.diagonal ρ*
          (nonlinearRationalL z ρ σ Dt G r).transpose)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simpa only [ha u hu] using (hh u hu).2.1
  have h3 : (∑ u ∈ nonlinearRateFibre z r,
      (nonlinearRationalJ z ρ σ Dt G r*Matrix.diagonal ρ*
        (Matrix.of (W z ρ Dt G u)).transpose -
        Matrix.of (W z ρ Dt G u)*Matrix.diagonal ρ*
          (nonlinearRationalJ z ρ σ Dt G r).transpose)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simpa only [ha u hu] using (hh u hu).2.2.1
  have h4 : (∑ u ∈ nonlinearRateFibre z r,
      (r • (Matrix.of (C z ρ σ Dt G u) - (Matrix.of (C z ρ σ Dt G u)).transpose) +
        nonlinearRationalL z ρ σ Dt G r*Matrix.diagonal ρ*
          (Matrix.of (C z ρ σ Dt G u)).transpose -
        Matrix.of (C z ρ σ Dt G u)*Matrix.diagonal ρ*
          (nonlinearRationalL z ρ σ Dt G r).transpose)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simpa only [ha u hu] using (hh u hu).2.2.2
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.transpose_sum] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end FMSA.ExactMSA.MultiTailMixture
