import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitiveTangent

/-! Actual Fourier transform of the full-space first variation. All kernel
integrals are fixed before differentiating their finite coefficients. This
does not identify the independent double-propagator expression. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def basisFourierQ (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι)
    (k : ℝ) (i j : Fin N) : ℂ :=
  ∫ t : ℝ, (basisQ z σ b i j t : ℂ) * Complex.exp (-(Complex.I*k)*t)

theorem basisQ_complex_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (b : BasisIndex ι) (k : ℝ) (i j : Fin N) :
    Integrable (fun t => (basisQ z σ b i j t : ℂ) * Complex.exp (-(Complex.I*k)*t)) := by
  simp_rw [basisQ_eq_single_q]
  exact q_complex_weighted_integrable (fun _ : Fin 1 => basisRate z b)
    (fun _ => basisRate_pos z hz b) σ _ _ _ _ hσ (Complex.I*k) (by simp) i j

theorem basisQQ_complex_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (b c : BasisIndex ι) (k : ℝ) (i j l : Fin N) :
    Integrable (fun r => (basisQQ z σ b c i j l r : ℂ) * Complex.exp (-(Complex.I*k)*r)) := by
  have hi := complex_corr_weighted_integrable
    (fun t => (basisQ z σ b i l t : ℂ)) (fun t => (basisQ z σ c j l t : ℂ))
    (Complex.I*k) (basisQ_complex_weighted_integrable z hz σ hσ b k i l)
    (by simpa only [Complex.ofReal_neg, mul_neg, neg_neg] using
      basisQ_complex_weighted_integrable z hz σ hσ c (-k) j l)
  convert hi using 1
  funext r
  congr 1
  rw [basisQQ, ← integral_complex_ofReal]
  apply integral_congr_ae (Eventually.of_forall _)
  intro t
  push_cast
  rfl

theorem basisQQ_fourier (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (b c : BasisIndex ι) (k : ℝ) (i j l : Fin N) :
    (∫ r : ℝ, (basisQQ z σ b c i j l r : ℂ) * Complex.exp (-(Complex.I*k)*r)) =
      basisFourierQ z σ b k i l * basisFourierQ z σ c (-k) j l := by
  have ht := complex_corr_transform
    (fun t => (basisQ z σ b i l t : ℂ)) (fun t => (basisQ z σ c j l t : ℂ))
    (Complex.I*k) (basisQ_complex_weighted_integrable z hz σ hσ b k i l)
    (by simpa only [Complex.ofReal_neg, mul_neg, neg_neg] using
      basisQ_complex_weighted_integrable z hz σ hσ c (-k) j l)
  have hc : (fun r => (basisQQ z σ b c i j l r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      (fun r => (∫ t : ℝ, (basisQ z σ b i l t : ℂ)*(basisQ z σ c j l (t-r) : ℂ))*
        Complex.exp (-(Complex.I*k)*r)) := by
    funext r
    congr 1
    rw [basisQQ, ← integral_complex_ofReal]
    apply integral_congr_ae (Eventually.of_forall _)
    intro t
    push_cast
    rfl
  rw [hc, ← ht]
  simp only [basisFourierQ, Complex.ofReal_neg, mul_neg, neg_neg]

theorem basisFourierQ_neg (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι)
    (k : ℝ) (i j : Fin N) : basisFourierQ z σ b (-k) i j = star (basisFourierQ z σ b k i j) := by
  unfold basisFourierQ
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae (Eventually.of_forall _)
  intro t
  simp [Complex.ofReal_neg, mul_neg, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]

theorem fourierQ_eq_basis (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (i j : Fin N) :
    fourierQ z σ A qp W C k i j =
      ∑ b : BasisIndex ι, (coefficient A qp W C i j b : ℂ)*basisFourierQ z σ b k i j := by
  have he : (fun t => (q z σ A qp W C i j t : ℂ)*Complex.exp (-(Complex.I*k)*t)) =
      (fun t => ∑ b : BasisIndex ι, (coefficient A qp W C i j b : ℂ)*
        ((basisQ z σ b i j t : ℂ)*Complex.exp (-(Complex.I*k)*t))) := by
    funext t
    rw [q_eq_basis]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [fourierQ, he, integral_finsetSum _ (fun b _ =>
    (basisQ_complex_weighted_integrable z hz σ hσ b k i j).const_mul _)]
  simp only [integral_const_mul, basisFourierQ]

def linearizedFourierQ (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) : ℂ :=
  ∑ b : BasisIndex ι, (coefficientSlope z ρ σ D G0 i j b : ℂ)*basisFourierQ z σ b k i j

theorem fourierQ_hasDerivAt_seed (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (k : ℝ) (i j : Fin N) :
    HasDerivAt (fun τ => fourierQ z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) k i j)
      (linearizedFourierQ z ρ σ d.1 G0 k i j) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
    (bhCoefficient_hasDerivAt_seed z ρ σ G0 ψ d h0 hd i j b).ofReal_comp.mul_const
      (basisFourierQ z σ b k i j))
  simp_rw [fourierQ_eq_basis z hz σ _ _ _ _ hσ]
  exact h

theorem reflectedBasisQ_complex_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (b : BasisIndex ι) (k : ℝ) (i j : Fin N) :
    Integrable (fun t => (basisQ z σ b i j (-t) : ℂ)*Complex.exp (-(Complex.I*k)*t)) := by
  have h := (basisQ_complex_weighted_integrable z hz σ hσ b (-k) i j).comp_neg
  simpa only [Complex.ofReal_neg, mul_neg, neg_neg, neg_mul] using h

theorem reflectedBasisQ_fourier (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι)
    (k : ℝ) (i j : Fin N) :
    (∫ t : ℝ, (basisQ z σ b i j (-t) : ℂ)*Complex.exp (-(Complex.I*k)*t)) =
      basisFourierQ z σ b (-k) i j := by
  have he : (fun t : ℝ => (basisQ z σ b i j (-t) : ℂ)*Complex.exp (-(Complex.I*k)*t)) =
      (fun t => (fun u : ℝ => (basisQ z σ b i j u : ℂ)*Complex.exp ((Complex.I*k)*u)) (-t)) := by
    funext t
    simp only [Complex.ofReal_neg, mul_neg, neg_mul]
  rw [he]
  calc
    _ = ∫ t : ℝ, (basisQ z σ b i j t : ℂ)*Complex.exp ((Complex.I*k)*t) :=
      integral_neg_eq_self _ volume
    _ = _ := by simp only [basisFourierQ, Complex.ofReal_neg, mul_neg, neg_neg]

def linearizedSpectralPrimitive (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) : ℂ :=
  linearizedFourierQ z ρ σ D G0 k i j + linearizedFourierQ z ρ σ D G0 (-k) j i -
    ∑ l, (ρ l : ℂ) * ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
      (Complex.ofReal (coefficientSlope z ρ σ D G0 i l b * bhCoefficient z ρ σ (0, G0) j l c +
        bhCoefficient z ρ σ (0, G0) i l b * coefficientSlope z ρ σ D G0 j l c)) *
        (basisFourierQ z σ b k i l * basisFourierQ z σ c (-k) j l)

theorem linearizedPrimitiveReal_weighted_eq_basis (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G0 : TailMatrix ι N) (k : ℝ) (i j : Fin N) (r : ℝ) :
    Complex.ofReal (linearizedPrimitiveReal z ρ σ D G0 i j r)*Complex.exp (-(Complex.I*k)*r) =
    (∑ b : BasisIndex ι, (coefficientSlope z ρ σ D G0 i j b : ℂ)*
      ((basisQ z σ b i j r : ℂ)*Complex.exp (-(Complex.I*k)*r))) +
    (∑ b : BasisIndex ι, (coefficientSlope z ρ σ D G0 j i b : ℂ)*
      ((basisQ z σ b j i (-r) : ℂ)*Complex.exp (-(Complex.I*k)*r))) -
    ∑ l, (ρ l : ℂ)*∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
      Complex.ofReal (coefficientSlope z ρ σ D G0 i l b*bhCoefficient z ρ σ (0, G0) j l c +
        bhCoefficient z ρ σ (0, G0) i l b*coefficientSlope z ρ σ D G0 j l c)*
          ((basisQQ z σ b c i j l r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
  simp only [linearizedPrimitiveReal, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_mul, sub_mul, add_mul, Finset.sum_mul, mul_assoc]

theorem linearizedPrimitiveReal_axis_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) :
    Integrable (fun r => Complex.ofReal (linearizedPrimitiveReal z ρ σ D G0 i j r)*
      Complex.exp (-(Complex.I*k)*r)) := by
  have hlin (a b : Fin N) := integrable_finsetSum Finset.univ (fun c _ =>
    (basisQ_complex_weighted_integrable z hz σ hσ c k a b).const_mul
      (coefficientSlope z ρ σ D G0 a b c : ℂ))
  have href := integrable_finsetSum Finset.univ (fun b _ =>
    (reflectedBasisQ_complex_weighted_integrable z hz σ hσ b k j i).const_mul
      (coefficientSlope z ρ σ D G0 j i b : ℂ))
  have hquad := integrable_finsetSum Finset.univ (fun l _ =>
    (integrable_finsetSum Finset.univ (fun b _ =>
      integrable_finsetSum Finset.univ (fun c _ =>
        (basisQQ_complex_weighted_integrable z hz σ hσ b c k i j l).const_mul
          (Complex.ofReal (coefficientSlope z ρ σ D G0 i l b * bhCoefficient z ρ σ (0, G0) j l c +
            bhCoefficient z ρ σ (0, G0) i l b * coefficientSlope z ρ σ D G0 j l c))))).const_mul (ρ l : ℂ))
  convert (hlin i j).add href |>.sub hquad using 1
  funext r
  simp only [linearizedPrimitiveReal, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_mul, sub_mul, add_mul, Finset.sum_mul, mul_assoc,
    Pi.add_apply, Pi.sub_apply]

theorem linearizedPrimitiveReal_fourier (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) :
    (∫ r : ℝ, Complex.ofReal (linearizedPrimitiveReal z ρ σ D G0 i j r)*
      Complex.exp (-(Complex.I*k)*r)) = linearizedSpectralPrimitive z ρ σ D G0 k i j := by
  have hlin (a b : Fin N) (c : BasisIndex ι) :=
    (basisQ_complex_weighted_integrable z hz σ hσ c k a b).const_mul
      (coefficientSlope z ρ σ D G0 a b c : ℂ)
  have href (b : BasisIndex ι) :=
    (reflectedBasisQ_complex_weighted_integrable z hz σ hσ b k j i).const_mul
      (coefficientSlope z ρ σ D G0 j i b : ℂ)
  have hquad (l : Fin N) (b c : BasisIndex ι) :=
    (basisQQ_complex_weighted_integrable z hz σ hσ b c k i j l).const_mul
      (Complex.ofReal (coefficientSlope z ρ σ D G0 i l b * bhCoefficient z ρ σ (0, G0) j l c +
        bhCoefficient z ρ σ (0, G0) i l b * coefficientSlope z ρ σ D G0 j l c))
  simp_rw [linearizedPrimitiveReal_weighted_eq_basis]
  have hsplit := integral_sub ((integrable_finsetSum Finset.univ (fun b _ => hlin i j b)).add
    (integrable_finsetSum Finset.univ (fun b _ => href b)))
    (integrable_finsetSum Finset.univ (fun l _ =>
      (integrable_finsetSum Finset.univ (fun b _ => integrable_finsetSum Finset.univ (fun c _ => hquad l b c))).const_mul (ρ l : ℂ)))
  have hadd := integral_add (integrable_finsetSum Finset.univ (fun b _ => hlin i j b))
      (integrable_finsetSum Finset.univ (fun b _ => href b))
  simp only [Pi.add_apply] at hsplit hadd
  rw [hsplit, hadd,
    integral_finsetSum _ (fun b _ => hlin i j b), integral_finsetSum _ (fun b _ => href b)]
  simp only [integral_const_mul, reflectedBasisQ_fourier]
  unfold linearizedSpectralPrimitive linearizedFourierQ basisFourierQ
  congr 1
  rw [integral_finsetSum _ (fun l _ =>
    (integrable_finsetSum Finset.univ (fun b _ => integrable_finsetSum Finset.univ (fun c _ => hquad l b c))).const_mul (ρ l : ℂ))]
  apply Finset.sum_congr rfl
  intro l hl
  rw [integral_const_mul, integral_finsetSum _ (fun b _ => integrable_finsetSum Finset.univ (fun c _ => hquad l b c))]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_finsetSum _ (fun c _ => hquad l b c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [integral_const_mul, basisQQ_fourier z hz σ hσ]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, mul_assoc, basisFourierQ]

theorem linearizedFourierQ_neg (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) :
    star (linearizedFourierQ z ρ σ D G0 k i j) = linearizedFourierQ z ρ σ D G0 (-k) i j := by
  simp only [linearizedFourierQ, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← basisFourierQ_neg]
  simp [Complex.star_def, mul_comm]

def linearizedSpectralC (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) : ℂ :=
  linearizedFourierQ z ρ σ D G0 k i j + star (linearizedFourierQ z ρ σ D G0 k j i) -
    ∑ l, (ρ l : ℂ) *
      (linearizedFourierQ z ρ σ D G0 k i l *
        star (fourierQ z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
          (W z ρ 0 G0) (C z ρ σ 0 G0) k j l) +
       fourierQ z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
          (W z ρ 0 G0) (C z ρ σ 0 G0) k i l * star (linearizedFourierQ z ρ σ D G0 k j l))

theorem linearizedSpectralPrimitive_eq_spectralC (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) :
    linearizedSpectralPrimitive z ρ σ D G0 k i j = linearizedSpectralC z ρ σ D G0 k i j := by
  have hbase (w : ℝ) (a b : Fin N) :
      fourierQ z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
        (W z ρ 0 G0) (C z ρ σ 0 G0) w a b =
        ∑ c : BasisIndex ι, (bhCoefficient z ρ σ (0, G0) a b c : ℂ)*basisFourierQ z σ c w a b :=
    fourierQ_eq_basis z hz σ _ _ _ _ hσ w a b
  simp only [linearizedSpectralPrimitive, linearizedSpectralC, linearizedFourierQ_neg,
    fourierQ_conj]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  simp only [linearizedFourierQ, hbase, Complex.ofReal_add, Complex.ofReal_mul,
    add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro b hb <;>
    apply Finset.sum_congr rfl <;> intro c hc <;> ring

/-- Actual derivative of the Q-product coefficient, with the explicit
full-space primitive Fourier transform as its derivative. -/
theorem spectralBaxterC_hasDerivAt_seed (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (k : ℝ) (i j : Fin N) :
    HasDerivAt (fun τ => spectralBaxterC z ρ σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) k i j)
      (linearizedSpectralC z ρ σ d.1 G0 k i j) 0 := by
  have hq := fourierQ_hasDerivAt_seed z hz ρ σ hσ G0 ψ d h0 hd k
  have hp : ∀ l, HasDerivAt (fun τ => (ρ l : ℂ)*
      fourierQ z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
        (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) k i l *
      star (fourierQ z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
        (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
        (C z ρ σ (ψ τ).1 (ψ τ).2) k j l))
      ((ρ l : ℂ) * (linearizedFourierQ z ρ σ d.1 G0 k i l *
        star (fourierQ z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
          (W z ρ 0 G0) (C z ρ σ 0 G0) k j l) +
       fourierQ z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
          (W z ρ 0 G0) (C z ρ σ 0 G0) k i l * star (linearizedFourierQ z ρ σ d.1 G0 k j l))) 0 := by
    intro l
    convert! ((hq i l).mul (hq j l).star).const_mul (ρ l : ℂ) using 1
    · funext τ
      simp only [Pi.mul_apply]
      ring
    · simp only [h0]
  exact ((hq i j).add (hq j i).star).sub (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => hp l))

theorem spectralBaxterC_hasDerivAt_primitive_fourier (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (k : ℝ) (i j : Fin N) :
    HasDerivAt (fun τ => spectralBaxterC z ρ σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) k i j)
      (∫ r : ℝ, Complex.ofReal (linearizedPrimitiveReal z ρ σ d.1 G0 i j r)*
        Complex.exp (-(Complex.I*k)*r)) 0 := by
  rw [linearizedPrimitiveReal_fourier z hz ρ σ hσ,
    linearizedSpectralPrimitive_eq_spectralC z hz ρ σ hσ]
  exact spectralBaxterC_hasDerivAt_seed z hz ρ σ hσ G0 ψ d h0 hd k i j

/-- Joint actual real-space/Fourier first-variation certificate at the
internally constructed PY branch. No family, differentiability or integral
interchange premise is retained. This still supplies no P1 a.e. evenness. -/
theorem exists_contDiffAt_root_with_primitive_fourier_tangent (z : ι → ℝ)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hvac : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      (∀ i j r, HasDerivAt (fun τ => baxterPrimitive z ρ σ
        (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
        (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
        (Complex.ofReal (linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K)
          (baseSeed z ρ σ) i j r)) 0) ∧
      (∀ k i j, HasDerivAt (fun τ => spectralBaxterC z ρ σ
        (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
        (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) k i j)
        (∫ r : ℝ, Complex.ofReal (linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K)
          (baseSeed z ρ σ) i j r)*Complex.exp (-(Complex.I*k)*r)) 0) := by
  obtain ⟨ψ, h0, hr, hc, hp⟩ := exists_contDiffAt_root_with_linearizedPrimitive z ρ σ K hz hvac hρ hσ
  have hd := (hc.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
  have hs := firstOrderDt_eq_of_family z ρ σ K hz hvac hρ hσ ψ _ h0 hr hd
  refine ⟨ψ, h0, hr, hc, hp, fun k i j => ?_⟩
  have h := spectralBaxterC_hasDerivAt_primitive_fourier z hz ρ σ (fun i => (hσ i).le)
    (baseSeed z ρ σ) ψ _ h0 hd k i j
  rw [hs] at h
  exact h

end FMSA.ExactMSA.MultiTailMixture
