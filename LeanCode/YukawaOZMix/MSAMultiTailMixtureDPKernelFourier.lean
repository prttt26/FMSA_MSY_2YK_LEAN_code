import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPKernel
import LeanCode.YukawaOZMix.MSAMultiTailMixtureTangentReciprocity

/-! Fourier integrals of the independent fourterm DP construction.
The two reflected HS kernels and every internal density factor are explicit. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def dpSourceComplexRow (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (u : ι) (s : ℂ) (i j : Fin N) (r : ℝ) : ℂ :=
  (dpBareAmplitude z ρ σ K u i j : ℂ)*
    (Ici (edgeHi σ i j)).indicator (shiftedExpComplex (z u) (edgeHi σ i j) s) r

theorem dpB_complex_weighted_eq_sum (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (s : ℂ) (i j : Fin N) (r : ℝ) :
    (dpB z ρ σ K i j r : ℂ)*Complex.exp (-s*r) =
      ∑ u, dpSourceComplexRow z ρ σ K u s i j r := by
  unfold dpB dpSourceComplexRow shiftedExpComplex
  by_cases hr : r ∈ Ici (edgeHi σ i j)
  · simp only [indicator_of_mem hr, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    ring
  · simp only [indicator_of_notMem hr, mul_zero, Finset.sum_const_zero,
      Complex.ofReal_zero, zero_mul]

theorem dpSourceComplexRow_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (u : ι) (s : ℂ) (h : 0 < s.re+z u) (i j : Fin N) :
    Integrable (dpSourceComplexRow z ρ σ K u s i j) := by
  exact (((integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (shiftedExpComplex_integrable (z u) (edgeHi σ i j) s h)).integrable_indicator
      measurableSet_Ici).const_mul _

theorem dpSourceComplexRow_integral (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (u : ι) (s : ℂ) (h : 0 < s.re+z u) (i j : Fin N) :
    (∫ r : ℝ, dpSourceComplexRow z ρ σ K u s i j r) =
      (dpBareAmplitude z ρ σ K u i j : ℂ)*Complex.exp (-s*(edgeHi σ i j : ℂ))/(s+(z u : ℂ)) := by
  unfold dpSourceComplexRow
  rw [integral_const_mul, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    shiftedExpComplex_integral (z u) (edgeHi σ i j) s h]
  ring

theorem dpB_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    Integrable (fun r => (dpB z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
  simp_rw [dpB_complex_weighted_eq_sum]
  exact integrable_finsetSum Finset.univ (fun u _ =>
    dpSourceComplexRow_integrable z ρ σ K u (Complex.I*k) (by simpa using hz u) i j)

def dpBFourier (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) : ℂ :=
  ∫ r : ℝ, (dpB z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)

theorem dpBFourier_eq_source (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    dpBFourier z ρ σ K k i j = ∑ u,
      (dpBareAmplitude z ρ σ K u i j : ℂ)*
        Complex.exp (-(Complex.I*k)*(edgeHi σ i j : ℂ))/(Complex.I*k+(z u : ℂ)) := by
  unfold dpBFourier
  simp_rw [dpB_complex_weighted_eq_sum]
  rw [integral_finsetSum Finset.univ (fun u _ =>
    dpSourceComplexRow_integrable z ρ σ K u (Complex.I*k) (by simpa using hz u) i j)]
  apply Finset.sum_congr rfl
  intro u _
  exact dpSourceComplexRow_integral z ρ σ K u (Complex.I*k) (by simpa using hz u) i j

def realPlusConv (f g : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u : ℝ, f u*g (r+u)

theorem realPlusConv_eq_complex_corr (f g : ℝ → ℝ) (r : ℝ) :
    (realPlusConv f g r : ℂ) = ∫ t : ℝ, (g t : ℂ)*(f (t-r) : ℂ) := by
  unfold realPlusConv
  rw [← integral_complex_ofReal]
  have he := integral_add_right_eq_self (μ := volume) (fun t : ℝ => (g t : ℂ)*(f (t-r) : ℂ)) r
  rw [← he]
  apply integral_congr_ae (Eventually.of_forall _)
  intro u
  simp only [add_sub_cancel_right, Complex.ofReal_mul]
  ring

theorem realPlusConv_axis_weighted_integrable (f g : ℝ → ℝ) (k : ℝ)
    (hf : Integrable (fun t => (f t : ℂ)*Complex.exp ((Complex.I*k)*t)))
    (hg : Integrable (fun t => (g t : ℂ)*Complex.exp (-(Complex.I*k)*t))) :
    Integrable (fun r => (realPlusConv f g r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
  simpa only [realPlusConv_eq_complex_corr] using
    complex_corr_weighted_integrable (fun t => (g t : ℂ)) (fun t => (f t : ℂ)) (Complex.I*k) hg hf

theorem realPlusConv_fourier (f g : ℝ → ℝ) (k : ℝ)
    (hf : Integrable (fun t => (f t : ℂ)*Complex.exp ((Complex.I*k)*t)))
    (hg : Integrable (fun t => (g t : ℂ)*Complex.exp (-(Complex.I*k)*t))) :
    (∫ r : ℝ, (realPlusConv f g r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      (∫ t : ℝ, (g t : ℂ)*Complex.exp (-(Complex.I*k)*t))*
        (∫ t : ℝ, (f t : ℂ)*Complex.exp ((Complex.I*k)*t)) := by
  simpa only [realPlusConv_eq_complex_corr] using
    (complex_corr_transform (fun t => (g t : ℂ)) (fun t => (f t : ℂ)) (Complex.I*k) hg hf).symm

theorem dpSeedQ_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j : Fin N) :
    Integrable (fun r => (dpSeedQ z ρ σ i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)) :=
  q_complex_weighted_integrable z hz σ _ _ _ _ hσ (Complex.I*k) (by simp) i j

theorem dpSeedQ_positive_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j : Fin N) :
    Integrable (fun r => (dpSeedQ z ρ σ i j r : ℂ)*Complex.exp ((Complex.I*k)*r)) := by
  simpa only [Complex.ofReal_neg, mul_neg, neg_neg] using
    dpSeedQ_axis_weighted_integrable z hz ρ σ hσ (-k) i j

def dpSeedFourier (z : ι → ℝ) (ρ σ : Fin N → ℝ) (k : ℝ) (i j : Fin N) : ℂ :=
  ∫ r : ℝ, (dpSeedQ z ρ σ i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)

theorem dpSeedFourier_eq_complexHSQ (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    dpSeedFourier z ρ σ k i j = complexHSQ ρ σ (Complex.I*k) i j := by
  change fourierQ z σ (amplitudeA z ρ σ 0 0) (amplitudeQp z ρ σ 0 0)
    (W z ρ 0 0) (C z ρ σ 0 0) k i j = _
  rw [fourierQ_eq_QhatComplex z hz σ _ _ _ _ hσ k hk, QhatComplex_zero_eq_phase_HS]
  rfl

theorem dpTriple_eq_nested_plusConv (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j m n : Fin N) (r : ℝ) :
    dpTriple z ρ σ K i j m n r = realPlusConv (dpSeedQ z ρ σ i m)
      (realPlusConv (dpSeedQ z ρ σ j n) (dpB z ρ σ K m n)) r := by
  unfold dpTriple realPlusConv
  apply integral_congr_ae (Eventually.of_forall _)
  intro u
  rw [← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall _)
  intro v
  ring

theorem dpSingle_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (k : ℝ) (a b i j : Fin N) :
    Integrable (fun r => (realPlusConv (dpSeedQ z ρ σ a b) (dpB z ρ σ K i j) r : ℂ)*
      Complex.exp (-(Complex.I*k)*r)) :=
  realPlusConv_axis_weighted_integrable _ _ k
    (dpSeedQ_positive_axis_weighted_integrable z hz ρ σ hσ k a b)
    (dpB_axis_weighted_integrable z hz ρ σ K k i j)

theorem dpTriple_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (k : ℝ) (i j m n : Fin N) :
    Integrable (fun r => (dpTriple z ρ σ K i j m n r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
  simp_rw [dpTriple_eq_nested_plusConv]
  exact realPlusConv_axis_weighted_integrable _ _ k
    (dpSeedQ_positive_axis_weighted_integrable z hz ρ σ hσ k i m)
    (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k j n m n)

theorem dpSingle_fourier (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (k : ℝ) (a b i j : Fin N) :
    (∫ r : ℝ, (realPlusConv (dpSeedQ z ρ σ a b) (dpB z ρ σ K i j) r : ℂ)*
      Complex.exp (-(Complex.I*k)*r)) = dpBFourier z ρ σ K k i j*dpSeedFourier z ρ σ (-k) a b := by
  simpa only [dpBFourier, dpSeedFourier, Complex.ofReal_neg, mul_neg, neg_neg] using
    realPlusConv_fourier _ _ k
      (dpSeedQ_positive_axis_weighted_integrable z hz ρ σ hσ k a b)
      (dpB_axis_weighted_integrable z hz ρ σ K k i j)

theorem dpTriple_fourier (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (k : ℝ) (i j m n : Fin N) :
    (∫ r : ℝ, (dpTriple z ρ σ K i j m n r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      dpBFourier z ρ σ K k m n*dpSeedFourier z ρ σ (-k) j n*dpSeedFourier z ρ σ (-k) i m := by
  simp_rw [dpTriple_eq_nested_plusConv]
  rw [realPlusConv_fourier _ _ k
    (dpSeedQ_positive_axis_weighted_integrable z hz ρ σ hσ k i m)
    (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k j n m n),
    dpSingle_fourier z hz ρ σ hσ K]
  simp only [dpSeedFourier, Complex.ofReal_neg, mul_neg, neg_neg]

theorem dpW_axis_weighted_eq_terms (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (k : ℝ) (i j : Fin N) (r : ℝ) :
    (dpW z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*k)*r) =
      (dpB z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*k)*r) -
      (∑ n, (ρ n : ℂ)*((realPlusConv (dpSeedQ z ρ σ j n) (dpB z ρ σ K i n) r : ℂ)*Complex.exp (-(Complex.I*k)*r))) -
      (∑ m, (ρ m : ℂ)*((realPlusConv (dpSeedQ z ρ σ i m) (dpB z ρ σ K m j) r : ℂ)*Complex.exp (-(Complex.I*k)*r))) +
      ∑ m, ∑ n, (ρ m : ℂ)*(ρ n : ℂ)*((dpTriple z ρ σ K i j m n r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
  unfold dpW realPlusConv
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul,
    add_mul, sub_mul, Finset.sum_mul, mul_assoc]

theorem dpW_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    Integrable (fun r => (dpW z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
  have hl := integrable_finsetSum Finset.univ (fun n _ =>
    (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k j n i n).const_mul (ρ n : ℂ))
  have hm := integrable_finsetSum Finset.univ (fun m _ =>
    (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k i m m j).const_mul (ρ m : ℂ))
  have ht := integrable_finsetSum Finset.univ (fun m _ =>
    integrable_finsetSum Finset.univ (fun n _ =>
      (dpTriple_axis_weighted_integrable z hz ρ σ hσ K k i j m n).const_mul ((ρ m : ℂ)*(ρ n : ℂ))))
  have h := (dpB_axis_weighted_integrable z hz ρ σ K k i j).sub hl |>.sub hm |>.add ht
  convert! h using 1
  funext r
  simp only [Pi.add_apply, Pi.sub_apply, dpW_axis_weighted_eq_terms]

def dpWFourier (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) : ℂ :=
  ∫ r : ℝ, (dpW z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)

theorem dpWFourier_fourterms (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    dpWFourier z ρ σ K k i j = dpBFourier z ρ σ K k i j -
      (∑ n, (ρ n : ℂ)*(dpBFourier z ρ σ K k i n*dpSeedFourier z ρ σ (-k) j n)) -
      (∑ m, (ρ m : ℂ)*(dpBFourier z ρ σ K k m j*dpSeedFourier z ρ σ (-k) i m)) +
      ∑ m, ∑ n, (ρ m : ℂ)*(ρ n : ℂ)*
        (dpBFourier z ρ σ K k m n*dpSeedFourier z ρ σ (-k) j n*dpSeedFourier z ρ σ (-k) i m) := by
  have hb := dpB_axis_weighted_integrable z hz ρ σ K k i j
  have hl := integrable_finsetSum Finset.univ (fun n _ =>
    (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k j n i n).const_mul (ρ n : ℂ))
  have hm := integrable_finsetSum Finset.univ (fun m _ =>
    (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k i m m j).const_mul (ρ m : ℂ))
  have ht := integrable_finsetSum Finset.univ (fun m _ =>
    integrable_finsetSum Finset.univ (fun n _ =>
      (dpTriple_axis_weighted_integrable z hz ρ σ hσ K k i j m n).const_mul ((ρ m : ℂ)*(ρ n : ℂ))))
  have ha := integral_add (hb.sub hl |>.sub hm) ht
  have hs := integral_sub (hb.sub hl) hm
  have hs' := integral_sub hb hl
  simp only [Pi.add_apply, Pi.sub_apply] at ha hs hs'
  unfold dpWFourier
  simp_rw [dpW_axis_weighted_eq_terms]
  rw [ha, hs, hs', integral_finsetSum Finset.univ (fun n _ =>
    (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k j n i n).const_mul (ρ n : ℂ)),
    integral_finsetSum Finset.univ (fun m _ =>
      (dpSingle_axis_weighted_integrable z hz ρ σ hσ K k i m m j).const_mul (ρ m : ℂ)),
    integral_finsetSum Finset.univ (fun m _ => integrable_finsetSum Finset.univ (fun n _ =>
      (dpTriple_axis_weighted_integrable z hz ρ σ hσ K k i j m n).const_mul ((ρ m : ℂ)*(ρ n : ℂ))))]
  simp only [integral_const_mul, dpSingle_fourier z hz ρ σ hσ K]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_finsetSum Finset.univ (fun n _ =>
    (dpTriple_axis_weighted_integrable z hz ρ σ hσ K k i j m n).const_mul ((ρ m : ℂ)*(ρ n : ℂ)))]
  simp only [integral_const_mul, dpTriple_fourier z hz ρ σ hσ K]

theorem right_density_factor_entry (Q : Matrix (Fin N) (Fin N) ℂ) (ρ : Fin N → ℝ) (i j : Fin N) :
    (1-Q*Matrix.diagonal (fun m => (ρ m : ℂ))) i j =
      (if i=j then 1 else 0)-Q i j*(ρ j : ℂ) := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_diagonal]

theorem right_density_sandwich_fourterms (Q B : Matrix (Fin N) (Fin N) ℂ)
    (ρ : Fin N → ℝ) (i j : Fin N) :
    ((1-Q*Matrix.diagonal (fun m => (ρ m : ℂ)))*B*
      (1-Q*Matrix.diagonal (fun m => (ρ m : ℂ))).transpose) i j = B i j -
      (∑ n, (ρ n : ℂ)*(B i n*Q j n)) -
      (∑ m, (ρ m : ℂ)*(B m j*Q i m)) +
      ∑ m, ∑ n, (ρ m : ℂ)*(ρ n : ℂ)*(B m n*Q j n*Q i m) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, right_density_factor_entry,
    sub_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, ite_mul, zero_mul, mul_zero,
    one_mul, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.mul_sum]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

/-- Integral identification of the independent DP W with its exact two-sided
HS Fourier factor. This does not define W by a matrix product. -/
theorem dpWFourier_eq_HS_sandwich (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N)
    (k : ℝ) (hk : k ≠ 0) :
    Matrix.of (dpWFourier z ρ σ K k) =
      complexHSRightFactor ρ σ (-(Complex.I*k))*Matrix.of (dpBFourier z ρ σ K k)*
        (complexHSRightFactor ρ σ (-(Complex.I*k))).transpose := by
  ext i j
  rw [complexHSRightFactor, right_density_sandwich_fourterms,
    Matrix.of_apply, dpWFourier_fourterms z hz ρ σ hσ K]
  simp only [dpSeedFourier_eq_complexHSQ z hz ρ σ hσ (-k) (neg_ne_zero.mpr hk),
    Complex.ofReal_neg, mul_neg, Matrix.of_apply]

theorem dpBFourier_eq_contact_sum (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (k : ℝ) :
    Matrix.of (dpBFourier z ρ σ K k) =
      ∑ u, ((z u : ℂ)/(Complex.I*k+(z u : ℂ))) • contactEdgeSlope z ρ σ K u (Complex.I*k) := by
  ext i j
  simp only [Matrix.of_apply, dpBFourier_eq_source z hz ρ σ K, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, contactEdgeSlope, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro u _
  have hb := congrFun (congrFun (dpBareAmplitude_eq_dressedEdgeSlope z ρ σ K hz hv hρ hσ u) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hb
  rw [hb]
  push_cast
  ring

theorem dpWFourier_eq_contact_sandwich_sum (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (k : ℝ) (hk : k ≠ 0) :
    Matrix.of (dpWFourier z ρ σ K k) =
      ∑ u, ((z u : ℂ)/(Complex.I*k+(z u : ℂ))) •
        (complexHSRightFactor ρ σ (-(Complex.I*k))*contactEdgeSlope z ρ σ K u (Complex.I*k)*
          (complexHSRightFactor ρ σ (-(Complex.I*k))).transpose) := by
  rw [dpWFourier_eq_HS_sandwich z hz ρ σ (fun i => (hσ i).le) K k hk,
    dpBFourier_eq_contact_sum z ρ σ K hz hv hρ hσ k]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

/-- The actual P1 Fourier integral is the antiderivative transform of the
independent DP W. This retains the actual Fourier integral on both sides. -/
theorem linearizedPrimitiveReal_fourier_eq_DP_W_difference (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j=K u j i) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    (∫ r : ℝ, (linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K)
      (baseSeed z ρ σ) i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      (dpWFourier z ρ σ K (-k) i j-dpWFourier z ρ σ K k i j)/(Complex.I*k) := by
  rw [linearizedPrimitiveReal_fourier z hz ρ σ (fun i => (hσ i).le),
    linearizedSpectralPrimitive_eq_spectralC z hz ρ σ (fun i => (hσ i).le)]
  have hc := linearizedSpectralC_eq_hsFactorC1 z ρ σ K hz hv hρ hσ k hk
  have he : hsFactorC1 z ρ σ K (Complex.I*k) =
      (1/(Complex.I*k)) • (Matrix.of (dpWFourier z ρ σ K (-k))-Matrix.of (dpWFourier z ρ σ K k)) := by
    rw [hsFactorC1_DP_sum z ρ σ K hK, dpWFourier_eq_contact_sandwich_sum z ρ σ K hz hv hρ hσ (-k) (neg_ne_zero.mpr hk),
      dpWFourier_eq_contact_sandwich_sum z ρ σ K hz hv hρ hσ k hk,
      ← Finset.sum_sub_distrib, Finset.smul_sum]
    simp only [Complex.ofReal_neg, mul_neg, neg_neg]
    apply Finset.sum_congr rfl
    intro u _
    have hden : -(Complex.I*(k : ℂ))+(z u : ℂ) = (z u : ℂ)-Complex.I*k := by ring
    rw [hden]
    simp only [smul_sub, smul_smul, div_eq_mul_inv, mul_inv_rev]
    module
  have hij := congrFun (congrFun (hc.trans he) i) j
  simpa only [Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm, mul_one] using hij

end FMSA.ExactMSA.MultiTailMixture
