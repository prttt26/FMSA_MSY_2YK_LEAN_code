import MSAConvergence.ActualRDFTangent
import MSAConvergence.ComplexWronskianJets

/-! Global exponential order of the actual RDF and its amplitude tangent.
Computed damping is not a physical small-kernel or decay hypothesis. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.RDFExponentialOrder
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.Convergence.ActualRDFTangent
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture

/-- Compact half-axis continuity suffices for continuity on the entire
nonnegative axis; the compact radius is an internal proof device. -/
theorem continuousOn_Ici_of_compact {f : ℝ → ℝ}
    (h : ∀ R : ℝ, 0 ≤ R → ContinuousOn f (Icc 0 R)) : ContinuousOn f (Ici 0) := by
  intro r hr
  change 0 ≤ r at hr
  have hR : 0 ≤ r + 1 := by linarith [hr]
  apply (h (r+1) hR r ⟨hr, by linarith⟩).mono_of_mem_nhdsWithin
  have he : Icc (0 : ℝ) (r+1) = Ici 0 ∩ Iic (r+1) := rfl
  rw [he]
  exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith)))

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The genuine causal derivative is continuous on the whole positive axis. -/
theorem causalVariation_continuousOn (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ContinuousOn (causalVariation z rho sigma p v i j) (Ici 0) :=
  continuousOn_Ici_of_compact (fun _ hR => causalVariation_continuousOn_compact hR z rho sigma p v i j)

/-- The existing extension of the actual derivative below zero is constant. -/
theorem causalVariation_eq_max (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    causalVariation z rho sigma p v i j r = causalVariation z rho sigma p v i j (max 0 r) := by
  rw [← excessVariation_eq_causalVariation, ← excessVariation_eq_causalVariation]
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearRDFExcess z rho sigma a.1 a.2 r i j) =
      fun a => nonlinearRDFExcess z rho sigma a.1 a.2 (max 0 r) i j := by
    funext a
    exact congrFun (congrFun (rdfExcess_eq_max z rho sigma a r) i) j
  unfold excessVariation
  rw [he]

/-- Global continuity of the actual tangent, including its existing fixed
extension below zero, follows from compact Banach derivatives. -/
theorem causalVariation_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Continuous (causalVariation z rho sigma p v i j) := by
  have he : causalVariation z rho sigma p v i j =
      fun r => causalVariation z rho sigma p v i j (max 0 r) := by
    funext r
    exact causalVariation_eq_max z rho sigma p v i j r
  rw [he]
  exact (causalVariation_continuousOn z rho sigma p v i j).comp_continuous
    (continuous_const.max continuous_id) (fun r => show 0 ≤ max (0 : ℝ) r from le_max_left _ _)

/-- The genuine kernel variation uses the full fixed recentered dictionary. -/
theorem kernelVariation_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    kernelVariation z rho sigma p v i j r = rho i *
      ∑ b : BasisIndex T, fderiv ℝ (fun a => bhCoefficient z rho sigma a i j b) p v *
        recenteredBasis z sigma b i r := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearCausalKernel z rho sigma a.1 a.2 r i j) =
      fun a => rho i * ∑ b : BasisIndex T, bhCoefficient z rho sigma a i j b * recenteredBasis z sigma b i r := by
    funext a
    simp only [nonlinearCausalKernel, Matrix.of_apply, recentered_eq_basis]
  have hd (b : BasisIndex T) :=
    ((bhCoefficient_contDiff z rho sigma i j b).differentiable (by simp) p).hasFDerivAt.mul_const
      (recenteredBasis z sigma b i r)
  rw [kernelVariation, he, ((HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => hd b)).const_mul (rho i)).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The genuine source variation retains its affine/exponential dictionary. -/
theorem sourceVariation_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    sourceVariation z rho sigma p v i j r =
      ∑ b : BasisIndex T, fderiv ℝ (fun a => bhCoefficient z rho sigma a i j b) p v * gSourceBasis z b r := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearGSource z rho sigma a.1 a.2 r i j) =
      fun a => ∑ b : BasisIndex T, bhCoefficient z rho sigma a i j b * gSourceBasis z b r := by
    funext a
    exact gSource_eq_basis z rho sigma a i j r
  rw [sourceVariation, he, fderiv_fun_sum (fun b _ =>
    ((bhCoefficient_contDiff z rho sigma i j b).differentiable (by simp) p).mul_const _)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [(((bhCoefficient_contDiff z rho sigma i j b).differentiable (by simp) p).hasFDerivAt.mul_const
    (gSourceBasis z b r)).fderiv]
  simp only [smul_apply, smul_eq_mul, mul_comm]

omit [Fintype T] in
/-- Every recentered basis rate is strictly positive when the tail rates are. -/
theorem basisRate_pos (z : T → ℝ) (hz : ∀ u, 0 < z u) (b : BasisIndex T) : 0 < basisRate z b := by
  rcases b with b | (b | b)
  · exact zero_lt_one
  · exact hz b
  · exact hz b

/-- Each actual kernel basis function is bounded on the whole positive axis,
without imposing any amplitude smallness. -/
theorem recenteredBasis_bounded_positive (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (b : BasisIndex T) (i : Fin N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 ≤ r → |recenteredBasis z sigma b i r| ≤ M := by
  obtain ⟨x, hx, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (sigma i)).Nonempty from ⟨0, le_rfl, hsigma i⟩)
    (recenteredBasis_continuous z sigma b i).abs.continuousOn
  refine ⟨|recenteredBasis z sigma b i x| + (|basisW b| + |basisC b|), by positivity, ?_⟩
  intro r hr
  by_cases h : r ≤ sigma i
  · exact (hm ⟨hr,h⟩).trans (le_add_of_nonneg_right (by positivity))
  · have hi : sigma i ≤ r := (not_le.mp h).le
    have he1 : exp (-basisRate z b*r) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [basisRate_pos z hz b])
    have he2 : exp (-basisRate z b*(r-sigma i)) ≤ 1 := exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (basisRate_pos z hz b).le) (sub_nonneg.mpr hi))
    have he : recenteredBasis z sigma b i r = basisW b * exp (-basisRate z b*r) +
        basisC b * exp (-basisRate z b*(r-sigma i)) := by
      simp [recenteredBasis, min_eq_right hi, max_eq_left hi]
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
    have h1 := mul_le_mul_of_nonneg_left he1 (abs_nonneg (basisW b))
    have h2 := mul_le_mul_of_nonneg_left he2 (abs_nonneg (basisC b))
    nlinarith [abs_nonneg (recenteredBasis z sigma b i x)]

omit [Fintype T] in
/-- Every source basis has at most affine growth on the positive axis. -/
theorem gSourceBasis_affine_bound (z : T → ℝ) (hz : ∀ u, 0 < z u) (b : BasisIndex T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 ≤ r → |gSourceBasis z b r| ≤ M * (1+r) := by
  let M := (|basisA b| + |basisQp b| + |basisRate z b * basisC b|) / (2 * π)
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro r hr
  have he : exp (-basisRate z b*r) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [basisRate_pos z hz b])
  unfold gSourceBasis
  rw [abs_div, abs_of_pos (by positivity : 0 < 2*π)]
  have hs := (abs_add_le (basisA b*r+basisQp b)
    (basisRate z b * basisC b * exp (-basisRate z b*r))).trans
      (add_le_add_left (abs_add_le (basisA b*r) (basisQp b)) _)
  apply (div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2*π)).trans
  rw [abs_mul, abs_of_nonneg hr, abs_mul, abs_of_pos (exp_pos _)]
  have ht := mul_le_mul_of_nonneg_left he (abs_nonneg (basisRate z b * basisC b))
  dsimp only [M]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2*π)
  nlinarith [abs_nonneg (basisA b), abs_nonneg (basisQp b), abs_nonneg (basisRate z b * basisC b)]

/-- A complete finite matrix dictionary inherits one positive-axis growth
bound from its basis functions, with a computed coefficient constant. -/
theorem matrix_dictionary_bound {B : Type*} [Fintype B]
    (a : Fin N → Fin N → B → ℝ) (phi : B → Fin N → ℝ → ℝ) (g : ℝ → ℝ)
    (hphi : ∀ b i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 ≤ r → |phi b i r| ≤ M * g r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 ≤ r →
      FMSA.matrixAbsSum (Matrix.of (fun i j => ∑ b, a i j b * phi b i r)) ≤ M * g r := by
  classical
  choose M hM hb using hphi
  refine ⟨∑ i, ∑ j, ∑ b, |a i j b| * M b i,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun b _ => mul_nonneg (abs_nonneg _) (hM b i)))), ?_⟩
  intro r hr
  simp only [FMSA.matrixAbsSum, Matrix.of_apply, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb b i r hr) (abs_nonneg _)

/-- An upper triangular block jet packages a renewal and its genuine
linearization into one matrix renewal, without a kernel smallness premise. -/
def blockJet (A dA : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (N+N)) (Fin (N+N)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A dA 0 A)

/-- The entry-sum bound of the block jet retains both base copies. -/
theorem blockJet_absSum (A dA : Matrix (Fin N) (Fin N) ℝ) :
    FMSA.matrixAbsSum (blockJet A dA) = 2 * FMSA.matrixAbsSum A + FMSA.matrixAbsSum dA := by
  have he : FMSA.matrixAbsSum (blockJet A dA) =
      ∑ i : Fin N ⊕ Fin N, ∑ j : Fin N ⊕ Fin N, |(Matrix.fromBlocks A dA 0 A) i j| := by
    unfold FMSA.matrixAbsSum
    rw [← finSumFinEquiv.sum_comp (fun i : Fin (N+N) => ∑ j, |blockJet A dA i j|)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← finSumFinEquiv.sum_comp (fun j : Fin (N+N) => |blockJet A dA (finSumFinEquiv i) j|)]
    simp only [blockJet, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [he]
  simp only [FMSA.matrixAbsSum, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, abs_zero, Finset.sum_const_zero, Finset.sum_add_distrib]
  ring

/-- Continuity of both entries makes the entire block jet continuous. -/
theorem blockJet_continuous (A dA : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hA : Continuous A) (hdA : Continuous dA) : Continuous (fun r => blockJet (A r) (dA r)) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun r => Matrix.fromBlocks (A r) (dA r) 0 (A r)
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact hA.matrix_elem i j
  · exact hdA.matrix_elem i j
  · exact continuous_const
  · exact hA.matrix_elem i j

/-- A global positive-axis kernel bound and affine source bound give
exponential order for the actual renewal, at a computed damping rate. -/
theorem matrix_renewal_exponential_order
    (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (hy : Continuous y)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hk : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (q r) ≤ M)
    (hf : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (f r) ≤ B * (1+r))
    (heq : ∀ i j r, 0 ≤ r → y r i j = f r i j +
      ∑ m, ∫ t in (0 : ℝ)..r, q (r-t) i m * y t m j) :
    ∀ r, 0 ≤ r → exp (-(M+1)*r) * FMSA.matrixAbsSum (y r) ≤ B * (M+1) := by
  have hgamma : 0 < M+1 := by linarith
  have hi : IntegrableOn (fun r : ℝ => M * exp (-(M+1)*r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hgamma) 0).const_mul M
  have hki : IntegrableOn (fun r : ℝ => exp (-(M+1)*r) * FMSA.matrixAbsSum (q r)) (Ioi 0) := by
    apply hi.mono' ((by fun_prop : Continuous (fun r : ℝ => exp (-(M+1)*r))).mul
      (FMSA.matrixAbsSum_continuous q hq)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change ‖exp (-(M+1)*r) * FMSA.matrixAbsSum (q r)‖ ≤ M * exp (-(M+1)*r)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (FMSA.matrixAbsSum_nonneg _))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hk r hr.le) (exp_pos (-(M+1)*r)).le
  have hmass : (∫ r in Ioi (0 : ℝ), exp (-(M+1)*r) * FMSA.matrixAbsSum (q r)) ≤ M / (M+1) := by
    calc
      _ ≤ ∫ r in Ioi (0 : ℝ), M * exp (-(M+1)*r) := by
        apply integral_mono_ae hki hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        nlinarith [mul_le_mul_of_nonneg_left (hk r hr.le) (exp_pos (-(M+1)*r)).le]
      _ = M / (M+1) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hgamma)]
        simp only [mul_zero, exp_zero]
        field_simp
  have hsmall : M / (M+1) < 1 := (div_lt_one hgamma).mpr (by linarith)
  have hforce (r : ℝ) (hr : 0 ≤ r) : exp (-(M+1)*r) * FMSA.matrixAbsSum (f r) ≤ B := by
    have hle : 1+r ≤ exp ((M+1)*r) := by
      have hx := add_one_le_exp ((M+1)*r)
      nlinarith
    have hex : exp (-(M+1)*r) * exp ((M+1)*r) = 1 := by
      rw [← exp_add, show -(M+1)*r + (M+1)*r = 0 by ring, exp_zero]
    calc
      _ ≤ exp (-(M+1)*r) * (B * (1+r)) := mul_le_mul_of_nonneg_left (hf r hr) (exp_pos _).le
      _ ≤ exp (-(M+1)*r) * (B * exp ((M+1)*r)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hB) (exp_pos _).le
      _ = B := by nlinarith [hex]
  intro r hr
  have hb := FMSA.matrixRenewal_weighted_absSum_bound q f y hq hy (-(M+1)) (M/(M+1)) B
    hki hmass hsmall hB hforce heq r hr
  have he : B / (1 - M/(M+1)) = B * (M+1) := by field_simp [ne_of_gt hgamma]; ring
  rwa [he] at hb

/-- Transposing the right-oriented renewal and its linearization produces
one left-oriented block renewal, with matrix order retained exactly. -/
theorem blockJet_renewal (q dq f df y dy : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hy : ∀ i j r, 0 ≤ r → y r i j = f r i j +
      ∑ m, ∫ t in (0 : ℝ)..r, q (r-t) m j * y t i m)
    (hdy : ∀ i j r, 0 ≤ r → dy r i j = df r i j +
      (∑ m, ∫ t in (0 : ℝ)..r, q (r-t) m j * dy t i m) +
      ∑ m, ∫ t in (0 : ℝ)..r, dq (r-t) m j * y t i m) :
    ∀ i j r, 0 ≤ r → blockJet (y r).transpose (dy r).transpose i j =
      blockJet (f r).transpose (df r).transpose i j +
        ∑ m, ∫ t in (0 : ℝ)..r,
          blockJet (q (r-t)).transpose (dq (r-t)).transpose i m *
            blockJet (y t).transpose (dy t).transpose m j := by
  intro i j r hr
  rw [← finSumFinEquiv.sum_comp (fun m : Fin (N+N) => ∫ t in (0 : ℝ)..r,
    blockJet (q (r-t)).transpose (dq (r-t)).transpose i m *
      blockJet (y t).transpose (dy t).transpose m j)]
  simp only [blockJet, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · simpa only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.transpose_apply, mul_zero,
      intervalIntegral.integral_zero, Finset.sum_const_zero, add_zero] using hy j i r hr
  · simpa only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, add_assoc] using hdy j i r hr
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, mul_zero,
      intervalIntegral.integral_zero, Finset.sum_const_zero, add_zero]
  · simpa only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.transpose_apply, zero_mul,
      intervalIntegral.integral_zero, Finset.sum_const_zero, zero_add] using hy j i r hr

def kernelJet (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : ℝ) : Matrix (Fin (N+N)) (Fin (N+N)) ℝ :=
  blockJet (nonlinearCausalKernel z rho sigma p.1 p.2 r).transpose
    (Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)).transpose

def sourceJet (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : ℝ) : Matrix (Fin (N+N)) (Fin (N+N)) ℝ :=
  blockJet (nonlinearGSource z rho sigma p.1 p.2 r).transpose
    (Matrix.of (fun i j => sourceVariation z rho sigma p v i j r)).transpose

def causalJet (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : ℝ) : Matrix (Fin (N+N)) (Fin (N+N)) ℝ :=
  blockJet (nonlinearCausalG z rho sigma p.1 p.2 r).transpose
    (Matrix.of (fun i j => causalVariation z rho sigma p v i j r)).transpose

/-- The actual kernel jet is continuous on the whole real line. -/
theorem kernelJet_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : Continuous (kernelJet z rho sigma p v) := by
  apply blockJet_continuous
  · exact continuous_matrix fun i j => (nonlinearCausalKernel_continuous z rho sigma p.1 p.2).matrix_elem j i
  · apply continuous_matrix
    intro i j
    change Continuous (fun r => kernelVariation z rho sigma p v j i r)
    simp_rw [kernelVariation_eq_basis]
    exact continuous_const.mul (continuous_finsetSum _ (fun b _ => continuous_const.mul
      (recenteredBasis_continuous z sigma b j)))

/-- The actual causal jet is continuous globally, including its actual
constant derivative extension below zero. -/
theorem causalJet_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : Continuous (causalJet z rho sigma p v) := by
  apply blockJet_continuous
  · exact continuous_matrix fun i j => (nonlinearCausalG_continuous z rho sigma p.1 p.2).matrix_elem j i
  · exact continuous_matrix fun i j => causalVariation_continuous z rho sigma p v j i

/-- The actual nonlinear renewal and its genuine amplitude derivative are
one global half-axis block renewal, with no root or budget premise. -/
theorem actual_jet_renewal (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) :
    ∀ i j r, 0 ≤ r → causalJet z rho sigma p v r i j = sourceJet z rho sigma p v r i j +
      ∑ m, ∫ t in (0 : ℝ)..r, kernelJet z rho sigma p v (r-t) i m * causalJet z rho sigma p v t m j := by
  unfold causalJet sourceJet kernelJet
  refine blockJet_renewal (nonlinearCausalKernel z rho sigma p.1 p.2)
    (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r))
    (nonlinearGSource z rho sigma p.1 p.2)
    (fun r => Matrix.of (fun i j => sourceVariation z rho sigma p v i j r))
    (nonlinearCausalG z rho sigma p.1 p.2)
    (fun r => Matrix.of (fun i j => causalVariation z rho sigma p v i j r)) ?_ ?_
  · intro i j r hr
    simpa only [mul_comm] using nonlinearCausalG_renewal z rho sigma p.1 p.2 i j r hr
  · exact fun i j r hr => actual_tangent_renewal z rho sigma p v i j r hr

/-- The actual kernel and tangent kernel have one computed global bound;
no physical small-kernel criterion is assumed. -/
theorem kernelJet_bounded_positive (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 ≤ r → FMSA.matrixAbsSum (kernelJet z rho sigma p v r) ≤ M := by
  have hphi (b : BasisIndex T) (i : Fin N) : ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 ≤ r →
      |recenteredBasis z sigma b i r| ≤ M * (1 : ℝ) := by
    simpa only [mul_one] using recenteredBasis_bounded_positive z hz sigma hsigma b i
  obtain ⟨M0, hM0, hb0⟩ := matrix_dictionary_bound
    (fun i j b => rho i * bhCoefficient z rho sigma p i j b) (recenteredBasis z sigma)
    (fun _ => (1 : ℝ)) hphi
  obtain ⟨M1, hM1, hb1⟩ := matrix_dictionary_bound
    (fun i j b => rho i * fderiv ℝ (fun a => bhCoefficient z rho sigma a i j b) p v)
    (recenteredBasis z sigma) (fun _ => (1 : ℝ)) hphi
  refine ⟨2*M0+M1, by positivity, ?_⟩
  intro r hr
  have h0 : FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma p.1 p.2 r) ≤ M0 := by
    simpa only [mul_one, nonlinearCausalKernel, recentered_eq_basis, Finset.mul_sum, mul_assoc] using hb0 r hr
  have h1 : FMSA.matrixAbsSum (Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) ≤ M1 := by
    simp_rw [kernelVariation_eq_basis, Finset.mul_sum, ← mul_assoc]
    simpa only [mul_one] using hb1 r hr
  rw [kernelJet, blockJet_absSum, FMSA.matrixAbsSum_transpose, FMSA.matrixAbsSum_transpose]
  linarith

/-- The actual source and its true tangent have a computed affine bound. -/
theorem sourceJet_affine_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, 0 ≤ r → FMSA.matrixAbsSum (sourceJet z rho sigma p v r) ≤ B * (1+r) := by
  have hphi (b : BasisIndex T) (_ : Fin N) := gSourceBasis_affine_bound z hz b
  obtain ⟨B0, hB0, hb0⟩ := matrix_dictionary_bound (bhCoefficient z rho sigma p)
    (fun b _ => gSourceBasis z b) (fun r => 1+r) hphi
  obtain ⟨B1, hB1, hb1⟩ := matrix_dictionary_bound
    (fun i j b => fderiv ℝ (fun a => bhCoefficient z rho sigma a i j b) p v)
    (fun b _ => gSourceBasis z b) (fun r => 1+r) hphi
  refine ⟨2*B0+B1, by positivity, ?_⟩
  intro r hr
  have h0 : FMSA.matrixAbsSum (nonlinearGSource z rho sigma p.1 p.2 r) ≤ B0 * (1+r) := by
    have he : nonlinearGSource z rho sigma p.1 p.2 r =
        Matrix.of (fun i j => ∑ b : BasisIndex T, bhCoefficient z rho sigma p i j b * gSourceBasis z b r) := by
      ext i j
      exact gSource_eq_basis z rho sigma p i j r
    rw [he]
    exact hb0 r hr
  have h1 : FMSA.matrixAbsSum (Matrix.of (fun i j => sourceVariation z rho sigma p v i j r)) ≤ B1 * (1+r) := by
    simp_rw [sourceVariation_eq_basis]
    exact hb1 r hr
  rw [sourceJet, blockJet_absSum, FMSA.matrixAbsSum_transpose, FMSA.matrixAbsSum_transpose]
  nlinarith

/-- Unconditional global exponential order of the actual causal G and its
genuine amplitude tangent. The rate and bound are constructed internally. -/
theorem actual_causal_jet_exponential_order (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) :
    ∃ gamma B : ℝ, 0 < gamma ∧ 0 ≤ B ∧ ∀ r, 0 ≤ r →
      exp (-gamma*r) * FMSA.matrixAbsSum (causalJet z rho sigma p v r) ≤ B := by
  obtain ⟨M, hM, hk⟩ := kernelJet_bounded_positive z hz rho sigma hsigma p v
  obtain ⟨C, hC, hf⟩ := sourceJet_affine_bound z hz rho sigma p v
  refine ⟨M+1, C*(M+1), by linarith, by positivity, ?_⟩
  exact matrix_renewal_exponential_order _ _ _ (kernelJet_continuous z rho sigma p v)
    (causalJet_continuous z rho sigma p v) M C hM hC hk hf (actual_jet_renewal z rho sigma p v)

/-- One constructed damping rate bounds every actual species entry and its
true derivative; no root, canonicity or physical budget premise is required. -/
theorem actual_causal_entries_exponential_order (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) :
    ∃ gamma B : ℝ, 0 < gamma ∧ 0 ≤ B ∧ ∀ i j r, 0 ≤ r →
      exp (-gamma*r) * |nonlinearCausalG z rho sigma p.1 p.2 r i j| ≤ B ∧
      exp (-gamma*r) * |causalVariation z rho sigma p v i j r| ≤ B := by
  obtain ⟨gamma, B, hg, hB, hb⟩ := actual_causal_jet_exponential_order z hz rho sigma hsigma p v
  refine ⟨gamma, B, hg, hB, ?_⟩
  intro i j r hr
  have hbase : |nonlinearCausalG z rho sigma p.1 p.2 r i j| ≤ FMSA.matrixAbsSum (causalJet z rho sigma p v r) := by
    simpa only [causalJet, blockJet, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.transpose_apply] using
      FMSA.matrixAbsSum_entry_le (causalJet z rho sigma p v r)
        (finSumFinEquiv (Sum.inl j)) (finSumFinEquiv (Sum.inl i))
  have hvar : |causalVariation z rho sigma p v i j r| ≤ FMSA.matrixAbsSum (causalJet z rho sigma p v r) := by
    simpa only [causalJet, blockJet, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.transpose_apply, Matrix.of_apply] using
      FMSA.matrixAbsSum_entry_le (causalJet z rho sigma p v r)
        (finSumFinEquiv (Sum.inl j)) (finSumFinEquiv (Sum.inr i))
  exact ⟨(mul_le_mul_of_nonneg_left hbase (exp_pos _).le).trans (hb r hr),
    (mul_le_mul_of_nonneg_left hvar (exp_pos _).le).trans (hb r hr)⟩

/-- Genuine complex Laplace integrability follows from a proved damping
bound and measurability, without claiming boundary Fourier integrability. -/
theorem exp_order_complex_integrable (f : ℝ → ℝ)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (gamma B : ℝ)
    (hb : ∀ r, 0 < r → exp (-gamma*r) * |f r| ≤ B)
    (s : ℂ) (hs : gamma < s.re) :
    IntegrableOn (fun r : ℝ => (f r : ℂ) * Complex.exp (-s*r)) (Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => B * exp (-(s.re-gamma)*r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(s.re-gamma) < 0) 0).const_mul B
  apply hi.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hm).mul
    (by fun_prop : Continuous (fun r : ℝ => Complex.exp (-s*r))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change ‖(f r : ℂ) * Complex.exp (-s*r)‖ ≤ B * exp (-(s.re-gamma)*r)
  simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs]
  have hex : exp (-s.re*r) = exp (-gamma*r) * exp (-(s.re-gamma)*r) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hex]
  calc
    |f r| * (exp (-gamma*r) * exp (-(s.re-gamma)*r)) =
        (exp (-gamma*r) * |f r|) * exp (-(s.re-gamma)*r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb r hr) (exp_pos _).le

/-- Actual causal G and its actual amplitude derivative have honest Laplace
integrals throughout one sufficiently far right half-plane, for all pairs. -/
theorem actual_causal_laplace_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ s : ℂ, gamma < s.re → ∀ i j,
      IntegrableOn (fun r : ℝ => (nonlinearCausalG z rho sigma p.1 p.2 r i j : ℂ) *
        Complex.exp (-s*r)) (Ioi 0) ∧
      IntegrableOn (fun r : ℝ => (causalVariation z rho sigma p v i j r : ℂ) *
        Complex.exp (-s*r)) (Ioi 0) := by
  obtain ⟨gamma, B, hg, _, hb⟩ := actual_causal_entries_exponential_order z hz rho sigma hsigma p v
  refine ⟨gamma, hg, ?_⟩
  intro s hs i j
  exact ⟨exp_order_complex_integrable _
      ((nonlinearCausalG_continuous z rho sigma p.1 p.2).matrix_elem i j).aestronglyMeasurable
      gamma B (fun r hr => (hb i j r hr.le).1) s hs,
    exp_order_complex_integrable _ (causalVariation_continuous z rho sigma p v i j).aestronglyMeasurable
      gamma B (fun r hr => (hb i j r hr.le).2) s hs⟩

/-- The genuine radius-weighted h variation is exactly a measurable shifted
causal variation on the positive axis, including contact. -/
theorem weighted_hVariation_positive_indicator (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hR : 0 < edgeHi sigma i j)
    (r : ℝ) (hr : 0 < r) :
    r * JacobianExterior.hVariation z rho sigma p v i j r =
      (Ici (edgeHi sigma i j)).indicator
        (fun x => causalVariation z rho sigma p v i j (x-edgeHi sigma i j)) r := by
  rw [actual_weighted_hVariation_positive z rho sigma p v i j hR r hr]
  by_cases h : r < edgeHi sigma i j
  · rw [if_pos h, indicator_of_notMem (show r ∉ Ici (edgeHi sigma i j) from not_le.mpr h)]
  · rw [if_neg h, indicator_of_mem (show r ∈ Ici (edgeHi sigma i j) from not_lt.mp h)]

/-- Positive shifts of an exponentially bounded field remain bounded at the
same computed damping rate, with the core set to zero. -/
theorem shifted_exp_order (f : ℝ → ℝ) (gamma B R : ℝ) (hg : 0 ≤ gamma) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hb : ∀ r, 0 ≤ r → exp (-gamma*r) * |f r| ≤ B) :
    ∀ r, 0 < r → exp (-gamma*r) * |(Ici R).indicator (fun x => f (x-R)) r| ≤ B := by
  intro r _
  by_cases hr : R ≤ r
  · rw [indicator_of_mem (show r ∈ Ici R from hr)]
    have hex : exp (-gamma*r) = exp (-gamma*R) * exp (-gamma*(r-R)) := by
      rw [← exp_add]
      congr 1
      ring
    have he : exp (-gamma*R) ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) hR)
    rw [hex, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hb (r-R) (sub_nonneg.mpr hr)) (exp_pos _).le).trans
      (by nlinarith)
  · rw [indicator_of_notMem (show r ∉ Ici R from hr), abs_zero, mul_zero]
    exact hB

/-- The actual h tangent has an honest radius-weighted positive-axis Laplace
integral in a computed right half-plane, without root or budget assumptions.
This does not assert Fourier boundary integrability or global unweighted L2. -/
theorem actual_weighted_hVariation_laplace_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 < sigma i)
    (p v : TailMatrix T N × TailMatrix T N) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ s : ℂ, gamma < s.re → ∀ i j,
      IntegrableOn (fun r : ℝ => (r * JacobianExterior.hVariation z rho sigma p v i j r : ℂ) *
        Complex.exp (-s*r)) (Ioi 0) := by
  obtain ⟨gamma, B, hg, hB, hb⟩ := actual_causal_entries_exponential_order
    z hz rho sigma (fun i => (hsigma i).le) p v
  refine ⟨gamma, hg, ?_⟩
  intro s hs i j
  have hR : 0 < edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
  let f := (Ici (edgeHi sigma i j)).indicator
    (fun x => causalVariation z rho sigma p v i j (x-edgeHi sigma i j))
  have hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    ((causalVariation_continuous z rho sigma p v i j).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.indicator measurableSet_Ici
  have hi := exp_order_complex_integrable f hm gamma B
    (shifted_exp_order _ gamma B _ hg.le hB hR.le (fun r hr => (hb i j r hr).2)) s hs
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  dsimp only
  rw [← Complex.ofReal_mul, weighted_hVariation_positive_indicator z rho sigma p v i j hR r hr]

/-- Real exponential damping is integrable under the same constructed
exponential-order bound used by the genuine complex transform. -/
theorem exp_order_real_integrable (f : ℝ → ℝ)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (gamma B a : ℝ)
    (hb : ∀ r, 0 < r → exp (-gamma*r) * |f r| ≤ B) (ha : gamma < a) :
    IntegrableOn (fun r => exp (-a*r) * f r) (Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => B * exp (-(a-gamma)*r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(a-gamma) < 0) 0).const_mul B
  apply hi.mono' ((by fun_prop : Continuous (fun r : ℝ => exp (-a*r))).aestronglyMeasurable.mul hm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change ‖exp (-a*r) * f r‖ ≤ B * exp (-(a-gamma)*r)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  have he : exp (-a*r) = exp (-gamma*r) * exp (-(a-gamma)*r) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  calc
    exp (-gamma*r) * exp (-(a-gamma)*r) * |f r| =
        (exp (-gamma*r) * |f r|) * exp (-(a-gamma)*r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb r hr) (exp_pos _).le

/-- A scalar entry and its tangent are controlled by the same block norm. -/
theorem blockJet_entry_bound (A dA : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    |A i j| ≤ FMSA.matrixAbsSum (blockJet A.transpose dA.transpose) ∧
    |dA i j| ≤ FMSA.matrixAbsSum (blockJet A.transpose dA.transpose) := by
  constructor
  · simpa only [blockJet, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.transpose_apply] using
      FMSA.matrixAbsSum_entry_le (blockJet A.transpose dA.transpose)
        (finSumFinEquiv (Sum.inl j)) (finSumFinEquiv (Sum.inl i))
  · simpa only [blockJet, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.transpose_apply] using
      FMSA.matrixAbsSum_entry_le (blockJet A.transpose dA.transpose)
        (finSumFinEquiv (Sum.inl j)) (finSumFinEquiv (Sum.inr i))

/-- Unit exponential damping absorbs a positive-axis affine bound. -/
theorem affine_damping_bound (f : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ r, 0 ≤ r → |f r| ≤ B * (1+r)) :
    ∀ r, 0 ≤ r → exp (-r) * |f r| ≤ B := by
  intro r hr
  have he : exp (-r) * exp r = 1 := by rw [← exp_add]; simp
  have hle : 1+r ≤ exp r := by linarith [add_one_le_exp r]
  calc
    _ ≤ exp (-r) * (B * (1+r)) := mul_le_mul_of_nonneg_left (hb r hr) (exp_pos _).le
    _ ≤ exp (-r) * (B * exp r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hB) (exp_pos _).le
    _ = B := by nlinarith [he]

/-- The existing actual source tangent is globally continuous. -/
theorem sourceVariation_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Continuous (sourceVariation z rho sigma p v i j) := by
  change Continuous (fun r => sourceVariation z rho sigma p v i j r)
  simp_rw [sourceVariation_eq_basis]
  exact continuous_finsetSum _ (fun b _ => continuous_const.mul (gSourceBasis_continuous z b))

/-- Genuine integration of the matrix tangent renewal. Both convolution
terms have proved absolute integrability; no root-only identity is differentiated. -/
theorem complex_matrix_tangent_renewal
    (q dq df y dy : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hdq : Continuous dq) (hdf : Continuous df)
    (hy : Continuous y) (hdy : Continuous dy) (s : ℂ)
    (hiq : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*q t i j) (Ioi 0))
    (hidq : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*dq t i j) (Ioi 0))
    (hidf : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*df t i j) (Ioi 0))
    (hiy : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*y t i j) (Ioi 0))
    (hidy : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*dy t i j) (Ioi 0))
    (heq : ∀ i j r, 0 ≤ r → dy r i j = df r i j +
      (∑ m, ∫ t in (0 : ℝ)..r, q (r-t) m j * dy t i m) +
      ∑ m, ∫ t in (0 : ℝ)..r, dq (r-t) m j * y t i m) :
    rdfMatrixLaplace dy s * (1-rdfMatrixLaplace q s) =
      rdfMatrixLaplace df s + rdfMatrixLaplace y s * rdfMatrixLaplace dq s := by
  have hv0 (i j m : Fin N) := complexCausalLaplace_weighted_convolution
    (fun t => q t m j) (fun t => dy t i m) (hq.matrix_elem m j) (hdy.matrix_elem i m)
    s (hiq m j) (hidy i m)
  have hv1 (i j m : Fin N) := complexCausalLaplace_weighted_convolution
    (fun t => dq t m j) (fun t => y t i m) (hdq.matrix_elem m j) (hy.matrix_elem i m)
    s (hidq m j) (hiy i m)
  have ht (i j : Fin N) : FMSA.causalComplexLaplace (fun t => dy t i j) s =
      FMSA.causalComplexLaplace (fun t => df t i j) s +
        (∑ m, FMSA.causalComplexLaplace (fun t => dy t i m) s * FMSA.causalComplexLaplace (fun t => q t m j) s) +
        ∑ m, FMSA.causalComplexLaplace (fun t => y t i m) s * FMSA.causalComplexLaplace (fun t => dq t m j) s := by
    unfold FMSA.causalComplexLaplace
    have he : (∫ r in Ioi (0 : ℝ), (dy r i j : ℂ)*Complex.exp (-s*r)) =
        ∫ r in Ioi (0 : ℝ), ((df r i j : ℂ)*Complex.exp (-s*r) +
          ∑ m, (causalIntervalConv (fun t => q t m j) (fun t => dy t i m) r : ℂ)*Complex.exp (-s*r)) +
          ∑ m, (causalIntervalConv (fun t => dq t m j) (fun t => y t i m) r : ℂ)*Complex.exp (-s*r) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [heq i j r hr.le]
      push_cast
      simp only [causalIntervalConv, add_mul, Finset.sum_mul]
    let F : ℝ → ℂ := fun r => (df r i j : ℂ)*Complex.exp (-s*r)
    let V0 : Fin N → ℝ → ℂ := fun m r =>
      (causalIntervalConv (fun t => q t m j) (fun t => dy t i m) r : ℂ)*Complex.exp (-s*r)
    let V1 : Fin N → ℝ → ℂ := fun m r =>
      (causalIntervalConv (fun t => dq t m j) (fun t => y t i m) r : ℂ)*Complex.exp (-s*r)
    have hF : IntegrableOn F (Ioi 0) := FMSA.complex_laplace_integrable _
      (hdf.matrix_elem i j).continuousOn s (hidf i j)
    have h0 : IntegrableOn (fun r => ∑ m, V0 m r) (Ioi 0) :=
      integrable_finsetSum Finset.univ (fun m _ => (hv0 i j m).1)
    have h1 : IntegrableOn (fun r => ∑ m, V1 m r) (Ioi 0) :=
      integrable_finsetSum Finset.univ (fun m _ => (hv1 i j m).1)
    rw [he]
    change (∫ r in Ioi (0 : ℝ), F r + (∑ m, V0 m r) + ∑ m, V1 m r) = _
    erw [integral_add (hF.add h0) h1, integral_add hF h0,
      integral_finsetSum _ (fun m _ => (hv0 i j m).1), integral_finsetSum _ (fun m _ => (hv1 i j m).1)]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl (fun m _ => (hv0 i j m).2)
    · exact Finset.sum_congr rfl (fun m _ => (hv1 i j m).2)
  rw [Matrix.mul_sub, Matrix.mul_one]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, rdfMatrixLaplace, Matrix.of_apply]
  linear_combination ht i j

/-- The genuine actual amplitude tangent satisfies the integrated matrix
renewal in a computed right half-plane. This is not the Fourier-boundary OZ
identity and assumes neither a root curve nor any kernel budget. -/
theorem actual_tangent_laplace_renewal (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re →
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => causalVariation z rho sigma p v i j r)) s *
        (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s) =
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => sourceVariation z rho sigma p v i j r)) s +
        rdfMatrixLaplace (nonlinearCausalG z rho sigma p.1 p.2) s *
          rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s := by
  let q := nonlinearCausalKernel z rho sigma p.1 p.2
  let dq : ℝ → Matrix (Fin N) (Fin N) ℝ := fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)
  let df : ℝ → Matrix (Fin N) (Fin N) ℝ := fun r => Matrix.of (fun i j => sourceVariation z rho sigma p v i j r)
  let y := nonlinearCausalG z rho sigma p.1 p.2
  let dy : ℝ → Matrix (Fin N) (Fin N) ℝ := fun r => Matrix.of (fun i j => causalVariation z rho sigma p v i j r)
  have hq : Continuous q := nonlinearCausalKernel_continuous z rho sigma p.1 p.2
  have hdq : Continuous dq := by
    apply continuous_matrix
    intro i j
    change Continuous (fun r => kernelVariation z rho sigma p v i j r)
    simp_rw [kernelVariation_eq_basis]
    exact continuous_const.mul (continuous_finsetSum _ (fun b _ => continuous_const.mul
      (recenteredBasis_continuous z sigma b i)))
  have hdf : Continuous df := continuous_matrix fun i j => sourceVariation_continuous z rho sigma p v i j
  have hy : Continuous y := nonlinearCausalG_continuous z rho sigma p.1 p.2
  have hdy : Continuous dy := continuous_matrix fun i j => causalVariation_continuous z rho sigma p v i j
  obtain ⟨M, _, hk⟩ := kernelJet_bounded_positive z hz rho sigma hsigma p v
  obtain ⟨C, hC, hf⟩ := sourceJet_affine_bound z hz rho sigma p v
  obtain ⟨gamma, B, hg, _, hb⟩ := actual_causal_entries_exponential_order z hz rho sigma hsigma p v
  have hke (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) : |q r i j| ≤ M ∧ |dq r i j| ≤ M :=
    ⟨((blockJet_entry_bound (q r) (dq r) i j).1).trans (hk r hr),
      ((blockJet_entry_bound (q r) (dq r) i j).2).trans (hk r hr)⟩
  have hfe (i j : Fin N) : ∀ r, 0 ≤ r → exp (-r) * |df r i j| ≤ C :=
    affine_damping_bound _ C hC (fun r hr =>
      ((blockJet_entry_bound (nonlinearGSource z rho sigma p.1 p.2 r) (df r) i j).2).trans (hf r hr))
  refine ⟨gamma+1, by linarith, ?_⟩
  intro s hs
  refine complex_matrix_tangent_renewal q dq df y dy hq hdq hdf hy hdy s ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    exact exp_order_real_integrable _ (hq.matrix_elem i j).aestronglyMeasurable 0 M s.re
      (fun r hr => by simpa only [neg_zero, zero_mul, exp_zero, one_mul] using (hke i j r hr.le).1)
      (by linarith)
  · intro i j
    exact exp_order_real_integrable _ (hdq.matrix_elem i j).aestronglyMeasurable 0 M s.re
      (fun r hr => by simpa only [neg_zero, zero_mul, exp_zero, one_mul] using (hke i j r hr.le).2)
      (by linarith)
  · intro i j
    exact exp_order_real_integrable _ (hdf.matrix_elem i j).aestronglyMeasurable 1 C s.re
      (fun r hr => by simpa only [neg_mul, one_mul] using hfe i j r hr.le) (by linarith)
  · intro i j
    exact exp_order_real_integrable _ (hy.matrix_elem i j).aestronglyMeasurable gamma B s.re
      (fun r hr => (hb i j r hr.le).1) (by linarith)
  · intro i j
    exact exp_order_real_integrable _ (hdy.matrix_elem i j).aestronglyMeasurable gamma B s.re
      (fun r hr => (hb i j r hr.le).2) (by linarith)
  · exact fun i j r hr => actual_tangent_renewal z rho sigma p v i j r hr

end FMSA.Convergence.RDFExponentialOrder


/-- info: 'FMSA.Convergence.RDFExponentialOrder.continuousOn_Ici_of_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.continuousOn_Ici_of_compact

/-- info: 'FMSA.Convergence.RDFExponentialOrder.causalVariation_continuousOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.causalVariation_continuousOn

/-- info: 'FMSA.Convergence.RDFExponentialOrder.causalVariation_eq_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.causalVariation_eq_max

/-- info: 'FMSA.Convergence.RDFExponentialOrder.causalVariation_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.causalVariation_continuous

/-- info: 'FMSA.Convergence.RDFExponentialOrder.kernelVariation_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.kernelVariation_eq_basis

/-- info: 'FMSA.Convergence.RDFExponentialOrder.sourceVariation_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.sourceVariation_eq_basis

/-- info: 'FMSA.Convergence.RDFExponentialOrder.basisRate_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.basisRate_pos

/-- info: 'FMSA.Convergence.RDFExponentialOrder.recenteredBasis_bounded_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.recenteredBasis_bounded_positive

/-- info: 'FMSA.Convergence.RDFExponentialOrder.gSourceBasis_affine_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.gSourceBasis_affine_bound

/-- info: 'FMSA.Convergence.RDFExponentialOrder.matrix_dictionary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.matrix_dictionary_bound

/-- info: 'FMSA.Convergence.RDFExponentialOrder.blockJet_absSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.blockJet_absSum

/-- info: 'FMSA.Convergence.RDFExponentialOrder.blockJet_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.blockJet_continuous

/-- info: 'FMSA.Convergence.RDFExponentialOrder.matrix_renewal_exponential_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.matrix_renewal_exponential_order

/-- info: 'FMSA.Convergence.RDFExponentialOrder.blockJet_renewal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.blockJet_renewal

/-- info: 'FMSA.Convergence.RDFExponentialOrder.kernelJet_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.kernelJet_continuous

/-- info: 'FMSA.Convergence.RDFExponentialOrder.causalJet_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.causalJet_continuous

/-- info: 'FMSA.Convergence.RDFExponentialOrder.actual_jet_renewal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.actual_jet_renewal

/-- info: 'FMSA.Convergence.RDFExponentialOrder.kernelJet_bounded_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.kernelJet_bounded_positive

/-- info: 'FMSA.Convergence.RDFExponentialOrder.sourceJet_affine_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.sourceJet_affine_bound

/-- info: 'FMSA.Convergence.RDFExponentialOrder.actual_causal_jet_exponential_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.actual_causal_jet_exponential_order

/-- info: 'FMSA.Convergence.RDFExponentialOrder.actual_causal_entries_exponential_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.actual_causal_entries_exponential_order

/-- info: 'FMSA.Convergence.RDFExponentialOrder.exp_order_complex_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.exp_order_complex_integrable

/-- info: 'FMSA.Convergence.RDFExponentialOrder.actual_causal_laplace_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.actual_causal_laplace_integrable

/-- info: 'FMSA.Convergence.RDFExponentialOrder.weighted_hVariation_positive_indicator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.weighted_hVariation_positive_indicator

/-- info: 'FMSA.Convergence.RDFExponentialOrder.shifted_exp_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.shifted_exp_order

/-- info: 'FMSA.Convergence.RDFExponentialOrder.actual_weighted_hVariation_laplace_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.actual_weighted_hVariation_laplace_integrable

/-- info: 'FMSA.Convergence.RDFExponentialOrder.exp_order_real_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.exp_order_real_integrable

/-- info: 'FMSA.Convergence.RDFExponentialOrder.blockJet_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.blockJet_entry_bound

/-- info: 'FMSA.Convergence.RDFExponentialOrder.affine_damping_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.affine_damping_bound

/-- info: 'FMSA.Convergence.RDFExponentialOrder.sourceVariation_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.sourceVariation_continuous

/-- info: 'FMSA.Convergence.RDFExponentialOrder.complex_matrix_tangent_renewal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.complex_matrix_tangent_renewal

/-- info: 'FMSA.Convergence.RDFExponentialOrder.actual_tangent_laplace_renewal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RDFExponentialOrder.actual_tangent_laplace_renewal
