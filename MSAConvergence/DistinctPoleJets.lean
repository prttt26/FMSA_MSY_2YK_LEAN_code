import MSAConvergence.ResidualJets

/-! Distinct-rate Wronskian polynomial values retain the complete off-root
residue errors. Tangent cancellation sums every label of a repeated rate. -/
noncomputable section
open Real Polynomial
open scoped BigOperators ContDiff

namespace FMSA.Convergence.DistinctPoleJets
open FMSA.Paper.JacobianExterior FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.PoleResidual FMSA.Convergence.ResidualJets

variable {N : ℕ}

/-- The four unnormalized residues at a common rate, with arbitrary matrices. -/
def residueMatrices (C W J L : Matrix (Fin N) (Fin N) ℝ) (rho : Fin N → ℝ) (r : ℝ) :
    Fin 4 → Matrix (Fin N) (Fin N) ℝ :=
  let P := Matrix.diagonal rho
  fun k => match k.val with
    | 0 => r • W.transpose - C * P * J.transpose - L * P * W.transpose
    | 1 => r • W - J * P * C.transpose - W * P * L.transpose
    | 2 => J * P * W.transpose - W * P * J.transpose
    | _ => r • (C - C.transpose) + L * P * C.transpose - C * P * L.transpose

/-- Polynomial numerator values are fixed multiples of the entire residue,
including off-root error terms. -/
theorem cleared_values_factorization
    (C W J L : Matrix (Fin N) (Fin N) ℝ) (rho : Fin N → ℝ) (r c d : ℝ) (i j : Fin N) :
    (-c * W j i * r * d + ∑ m, rho m * (c * C i m * (d * J j m) - d * L i m * (-c * W j m)) =
      -(c * d) * residueMatrices C W J L rho r 0 i j) ∧
    (-d * L i j * (-r) * 0 - (-c * W i j) * (-r) * d +
        ∑ m, rho m * (d * J i m * (c * C j m) - (-c * W i m) * (d * L j m)) =
      -(c * d) * residueMatrices C W J L rho r 1 i j) ∧
    ((∑ m, rho m * (d * J i m * (-c * W j m) - (-c * W i m) * (d * J j m))) =
      -(c * d) * residueMatrices C W J L rho r 2 i j) ∧
    ((c * C i j - c * C j i) * (-r) * d +
        ∑ m, rho m * (c * C i m * (d * L j m) - d * L i m * (c * C j m)) =
      -(c * d) * residueMatrices C W J L rho r 3 i j) := by
  simp [residueMatrices,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, Matrix.mul_apply (M := C * Matrix.diagonal rho),
    Matrix.mul_apply (M := W * Matrix.diagonal rho),
    Matrix.mul_apply (M := J * Matrix.diagonal rho),
    Matrix.mul_apply (M := L * Matrix.diagonal rho), Matrix.mul_diagonal]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply sub_eq_zero.mp
    ring_nf
    try simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    ring

/-- The residue is linear in the C/W tail data when its rate and rational
J/L evaluations are fixed. -/
theorem residueMatrices_sum {I : Type*} (s : Finset I)
    (C W : I → Matrix (Fin N) (Fin N) ℝ) (J L : Matrix (Fin N) (Fin N) ℝ)
    (rho : Fin N → ℝ) (r : ℝ) :
    residueMatrices (∑ u ∈ s, C u) (∑ u ∈ s, W u) J L rho r =
      ∑ u ∈ s, residueMatrices (C u) (W u) J L rho r := by
  funext k
  fin_cases k <;>
    simp [residueMatrices, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, Matrix.transpose_sum, Finset.smul_sum, smul_sub]

variable {T : Type*} [Fintype T]

/-- Collected residue at a rate value, including every repeated tail label. -/
def collectedResidues (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : ℝ) : Fin 4 → Matrix (Fin N) (Fin N) ℝ :=
  residueMatrices (nonlinearRateFibreMatrix z (C z rho sigma p.1 p.2) r)
    (nonlinearRateFibreMatrix z (W z rho p.1 p.2) r)
    (nonlinearRationalJ z rho sigma p.1 p.2 r)
    (nonlinearRationalL z rho sigma p.1 p.2 r) rho r

/-- Four actual distinct-rate polynomial values in the residue component order. -/
def distinctValues (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : ℝ) (i j : Fin N) : Fin 4 → ℝ :=
  fun k => match k.val with
    | 0 => (nonlinearDistinctUPolynomial z rho sigma p.1 p.2 i j).eval r
    | 1 => (nonlinearDistinctUPolynomial z rho sigma p.1 p.2 i j).eval (-r)
    | 2 => (nonlinearDistinctVPolynomial z rho sigma p.1 p.2 i j).eval r
    | _ => (nonlinearDistinctVPolynomial z rho sigma p.1 p.2 i j).eval (-r)

/-- Full off-root polynomial evaluation identity at positive/reflected rates. -/
theorem distinctValues_eq_collected_residues (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (hz : ∀ u, 0 < z u)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) (i j : Fin N) (k : Fin 4) :
    distinctValues z rho sigma p r i j k =
      -(r^3 * (nonlinearDistinctRatePolynomialExcept z r).eval (-r) *
        (nonlinearDistinctDenominator z).eval r) * collectedResidues z rho sigma p r k i j := by
  have hrp := nonlinearDistinctRates_positive z hz r hr
  have hsp (u : T) : r + z u ≠ 0 := (add_pos hrp (hz u)).ne'
  have he := cleared_values_factorization
    (nonlinearRateFibreMatrix z (C z rho sigma p.1 p.2) r)
    (nonlinearRateFibreMatrix z (W z rho p.1 p.2) r)
    (nonlinearRationalJ z rho sigma p.1 p.2 r) (nonlinearRationalL z rho sigma p.1 p.2 r) rho r
    (r^3 * (nonlinearDistinctRatePolynomialExcept z r).eval (-r))
    ((nonlinearDistinctDenominator z).eval r) i j
  have hd : (nonlinearDistinctDenominator z).eval (-r) = 0 := by
    simp [nonlinearDistinctDenominator, nonlinearDistinctRatePolynomial_eval_neg_rate z r hr]
  have hc (q : Polynomial ℝ) (s : ℝ) : (q.comp (-X)).eval s = q.eval (-s) := by
    rw [Polynomial.eval_comp]
    simp
  fin_cases k
  all_goals
    simp [distinctValues, nonlinearDistinctUPolynomial, nonlinearDistinctVPolynomial,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, hc, neg_neg,
      nonlinearDistinctJNumerator_eval z rho sigma p.1 p.2 r hrp.ne' hsp,
      nonlinearDistinctLNumerator_eval z rho sigma p.1 p.2 r hrp.ne' hsp,
      nonlinearDistinctJNumerator_eval_neg_rate z rho sigma p.1 p.2 r hr,
      nonlinearDistinctLNumerator_eval_neg_rate z rho sigma p.1 p.2 r hr, hd] at he ⊢
  · simpa only [collectedResidues, zero_sub, neg_mul, neg_neg] using he.1
  · simpa only [collectedResidues, zero_sub, neg_mul, neg_neg] using he.2.1
  · simpa only [collectedResidues, zero_sub, neg_mul, neg_neg] using he.2.2.1
  · simpa only [collectedResidues, zero_sub, neg_mul, neg_neg] using he.2.2.2

/-- Grouping equal rates is exactly a finite sum of the existing actual
unnormalized residues. It holds off-root and for an empty rate fibre. -/
theorem collectedResidues_eq_sum (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : ℝ) :
    collectedResidues z rho sigma p r =
      ∑ u ∈ nonlinearRateFibre z r, yukawaResidues z rho sigma p u := by
  unfold collectedResidues nonlinearRateFibreMatrix
  rw [residueMatrices_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← (nonlinearRateFibre_mem z r u).mp hu]
  funext k
  fin_cases k <;> rfl

/-- Scalar observation commutes with the exact repeated-rate collection. -/
theorem collectedResidues_entry (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : ℝ) (k : Fin 4) (i j : Fin N) :
    collectedResidues z rho sigma p r k i j =
      ∑ u ∈ nonlinearRateFibre z r, yukawaResidues z rho sigma p u k i j := by
  rw [collectedResidues_eq_sum]
  simp [Finset.sum_apply, Matrix.sum_apply]

/-- Off-root smoothness of the genuine unnormalized actual residue entries. -/
theorem yukawaResidues_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (u : T) (k : Fin 4) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => yukawaResidues z rho sigma a u k i j) := by
  have he : (fun a => yukawaResidues z rho sigma a u k i j) =
      fun a => z u * poleDefects z rho sigma a u k i j := by
    funext a
    rw [yukawaResidues_eq_rate_smul z rho sigma a u (hz u).ne']
    rfl
  rw [he]
  exact contDiff_const.mul (actual_poleDefects_entry_contDiff z rho sigma hz u k i j)

/-- Collecting repeated rates preserves actual entry smoothness. -/
theorem collectedResidues_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (r : ℝ) (k : Fin 4) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => collectedResidues z rho sigma a r k i j) := by
  simp_rw [collectedResidues_entry]
  exact ContDiff.sum fun u _ => yukawaResidues_entry_contDiff z rho sigma hz u k i j

/-- Every distinct-rate polynomial evaluation is genuinely smooth off-root. -/
theorem distinctValues_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (r : ℝ) (hr : r ∈ nonlinearDistinctRates z)
    (k : Fin 4) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => distinctValues z rho sigma a r i j k) := by
  simp_rw [distinctValues_eq_collected_residues z rho sigma _ hz r hr i j k]
  exact contDiff_const.mul (collectedResidues_entry_contDiff z rho sigma hz r k i j)

/-- Actual kernel cancellation commutes with the finite repeated-rate sum. -/
theorem actual_kernel_collectedResidues_fderiv_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (r : ℝ) (k : Fin 4) (i j : Fin N) :
    fderiv ℝ (fun a => collectedResidues z rho sigma a r k i j) p v = 0 := by
  have he : (fun a => collectedResidues z rho sigma a r k i j) =
      fun a => ∑ u ∈ nonlinearRateFibre z r, yukawaResidues z rho sigma a u k i j := by
    funext a
    exact collectedResidues_entry z rho sigma a r k i j
  rw [he, fderiv_fun_sum (fun u _ =>
    (yukawaResidues_entry_contDiff z rho sigma hz u k i j).differentiable (by simp) p)]
  simp only [sum_apply]
  apply Finset.sum_eq_zero
  intro u _
  exact actual_kernel_yukawaResidues_fderiv_zero z rho sigma K hK hz t p v hroot hv u k i j

/-- Positive and reflected distinct-rate polynomial values annihilate every
actual amplitude-Jacobian kernel vector, without a curve of roots. -/
theorem actual_kernel_distinctValues_fderiv_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) (k : Fin 4) (i j : Fin N) :
    fderiv ℝ (fun a => distinctValues z rho sigma a r i j k) p v = 0 := by
  have he : (fun a => distinctValues z rho sigma a r i j k) =
      fun a => -(r^3 * (nonlinearDistinctRatePolynomialExcept z r).eval (-r) *
        (nonlinearDistinctDenominator z).eval r) * collectedResidues z rho sigma a r k i j := by
    funext a
    exact distinctValues_eq_collected_residues z rho sigma a hz r hr i j k
  rw [he]
  have hd := ((collectedResidues_entry_contDiff z rho sigma hz r k i j).differentiable
    (by simp) p).hasFDerivAt.const_mul
      (-(r^3 * (nonlinearDistinctRatePolynomialExcept z r).eval (-r) *
        (nonlinearDistinctDenominator z).eval r))
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul,
    actual_kernel_collectedResidues_fderiv_zero z rho sigma K hK hz t p v hroot hv, mul_zero]

/-- The four genuine polynomial evaluation derivatives in the existing
foundation U/V interface, with repeated rates handled internally. -/
theorem actual_kernel_distinct_wronskian_rates_fderiv_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) (i j : Fin N) :
    (fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval r) p v = 0) ∧
    (fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval (-r)) p v = 0) ∧
    (fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval r) p v = 0) ∧
    (fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval (-r)) p v = 0) := by
  exact ⟨actual_kernel_distinctValues_fderiv_zero z rho sigma K hK hz t p v hroot hv r hr 0 i j,
    actual_kernel_distinctValues_fderiv_zero z rho sigma K hK hz t p v hroot hv r hr 1 i j,
    actual_kernel_distinctValues_fderiv_zero z rho sigma K hK hz t p v hroot hv r hr 2 i j,
    actual_kernel_distinctValues_fderiv_zero z rho sigma K hK hz t p v hroot hv r hr 3 i j⟩

end FMSA.Convergence.DistinctPoleJets

/-- info: 'FMSA.Convergence.DistinctPoleJets.cleared_values_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.cleared_values_factorization

/-- info: 'FMSA.Convergence.DistinctPoleJets.residueMatrices_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.residueMatrices_sum

/-- info: 'FMSA.Convergence.DistinctPoleJets.distinctValues_eq_collected_residues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.distinctValues_eq_collected_residues

/-- info: 'FMSA.Convergence.DistinctPoleJets.collectedResidues_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.collectedResidues_eq_sum

/-- info: 'FMSA.Convergence.DistinctPoleJets.collectedResidues_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.collectedResidues_entry

/-- info: 'FMSA.Convergence.DistinctPoleJets.yukawaResidues_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.yukawaResidues_entry_contDiff

/-- info: 'FMSA.Convergence.DistinctPoleJets.collectedResidues_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.collectedResidues_entry_contDiff

/-- info: 'FMSA.Convergence.DistinctPoleJets.distinctValues_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.distinctValues_contDiff

/-- info: 'FMSA.Convergence.DistinctPoleJets.actual_kernel_collectedResidues_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.actual_kernel_collectedResidues_fderiv_zero

/-- info: 'FMSA.Convergence.DistinctPoleJets.actual_kernel_distinctValues_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.actual_kernel_distinctValues_fderiv_zero

/-- info: 'FMSA.Convergence.DistinctPoleJets.actual_kernel_distinct_wronskian_rates_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.DistinctPoleJets.actual_kernel_distinct_wronskian_rates_fderiv_zero
