import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPQTangent
import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSParity
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitiveTangentFourier

/-! Actual first-order Q transform: the compact polynomial correction is
included in the two-sided HS factor formula. -/
noncomputable section
open Real Filter Topology MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem complex_tangent_kernel (s z x y A a : ℂ)
    (hs : s ≠ 0) (hz : z ≠ 0) (hsz : s+z ≠ 0) :
    complexPolyMoment1 s x*((1/z^2-x/(2*z))*A+a*y*(1/z-x)) -
      complexPolyMoment2 s x*(A/z+2*a*y) +
      (A+z*(x/2*A+a*y))/z^3/(s+z) -
      ((1-z*x)/z^2*(x/2*A+a*y)+(1-z*x+(z*x)^2/2)/z^3*A)*
        (1/s-z*Complex.exp (-s*x)/(s*(s+z))) =
      -(complexPolyMoment1 s x*(x/2*A+a*y)+complexPolyMoment2 s x*A)/(s+z) -
        z*a*y*complexEdgeMomentM s x/(s*(s+z)) := by
  unfold complexPolyMoment1 complexPolyMoment2 complexEdgeMomentM
  field_simp
  <;> ring

theorem hsMoment_source_exponential_cancel (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (i m : Fin N) :
    hsMoment ρ σ (z u) i m + exp (-z u*σ i)*baseSource z ρ σ u i m/(z u) =
      (1-z u*σ i)/(z u)^2*Q0phys ρ σ i m +
        (1-z u*σ i+(z u*σ i)^2/2)/(z u)^3*Qppphys ρ σ m m := by
  unfold hsMoment baseSource
  field_simp
  <;> ring

theorem firstOrderC_moment_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (i j : Fin N) :
    C z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u i j =
      dressedEdgeSlope z ρ σ K u i j - ∑ m, ρ m*
        ((1-z u*σ i)/(z u)^2*Q0phys ρ σ i m +
          (1-z u*σ i+(z u*σ i)^2/2)/(z u)^3*Qppphys ρ σ m m)*
            dressedEdgeSlope z ρ σ K u m j := by
  have hc := cancellation_star (z u) ρ σ
    (Matrix.of (baseSeed z ρ σ u)) (Matrix.of (firstOrderDt z ρ σ K u)) i j
  have hc' : C z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u i j =
      firstOrderDt z ρ σ K u i j-exp (-z u*σ i)*
        W z ρ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u i j := by
    change Ct (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) i j = firstOrderDt z ρ σ K u i j -
        exp (-z u*σ i)*Wt (z u) ρ (Matrix.of (baseSeed z ρ σ u))
          (Matrix.of (firstOrderDt z ρ σ K u)) i j
    simp only [Matrix.of_apply] at hc
    linarith
  rw [hc', firstOrderDt_moment_entry z ρ σ K hz hv hρ hσ,
    firstOrderW_source_entry z ρ σ K hz hv hρ hσ]
  simp only [Finset.mul_sum]
  have he : (∑ m, hsMoment ρ σ (z u) i m*ρ m*dressedEdgeSlope z ρ σ K u m j) +
      (∑ m, exp (-z u*σ i)*(baseSource z ρ σ u i m*ρ m*dressedEdgeSlope z ρ σ K u m j/(z u))) =
      ∑ m, ρ m*((1-z u*σ i)/(z u)^2*Q0phys ρ σ i m +
        (1-z u*σ i+(z u*σ i)^2/2)/(z u)^3*Qppphys ρ σ m m)*dressedEdgeSlope z ρ σ K u m j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    have h := hsMoment_source_exponential_cancel z ρ σ u (hz u).ne' i m
    linear_combination ρ m*dressedEdgeSlope z ρ σ K u m j*h
  linarith

def singleTangentQhat (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (u : ι) (s : ℂ) (i j : Fin N) : ℂ :=
  Complex.exp (-s*(edgeLo σ i j : ℂ)) *
    (complexPolyMoment1 s (σ i)*mixDqp (z u) ρ σ (G0 u) (D u) i j +
      complexPolyMoment2 s (σ i)*mixDA (z u) ρ σ (G0 u) (D u) j +
      (W z ρ D G0 u i j : ℂ)/(s+(z u : ℂ)) +
      (C z ρ σ D G0 u i j : ℂ)*(1-Complex.exp (-s*(σ i : ℂ)))/s) +
    (C z ρ σ D G0 u i j : ℂ)*Complex.exp (-s*(edgeHi σ i j : ℂ))/(s+(z u : ℂ))

theorem QhatComplex_difference_eq_tangent_sum (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G0 : TailMatrix ι N) (s : ℂ) (i j : Fin N) :
    QhatComplex z σ (amplitudeA z ρ σ D G0) (amplitudeQp z ρ σ D G0)
      (W z ρ D G0) (C z ρ σ D G0) s i j -
    QhatComplex z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
      (W z ρ 0 G0) (C z ρ σ 0 G0) s i j = ∑ u, singleTangentQhat z ρ σ D G0 u s i j := by
  rw [QhatComplex_zero_eq_phase_HS]
  unfold QhatComplex amplitudeA amplitudeQp singleTangentQhat
  simp only [Complex.ofReal_add, Complex.ofReal_sum, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  unfold complexHSMoment complexPolyMoment1 complexPolyMoment2
  ring

theorem linearizedFourierQ_eq_Qhat_difference (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    linearizedFourierQ z ρ σ D G0 k i j =
      QhatComplex z σ (amplitudeA z ρ σ D G0) (amplitudeQp z ρ σ D G0)
        (W z ρ D G0) (C z ρ σ D G0) (Complex.I*k) i j -
      QhatComplex z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
        (W z ρ 0 G0) (C z ρ σ 0 G0) (Complex.I*k) i j := by
  rw [← fourierQ_eq_QhatComplex z hz σ _ _ _ _ hσ,
    ← fourierQ_eq_QhatComplex z hz σ _ _ _ _ hσ,
    fourierQ_eq_basis z hz σ _ _ _ _ hσ,
    fourierQ_eq_basis z hz σ _ _ _ _ hσ]
  simp only [linearizedFourierQ, coefficientSlope, bhCoefficient, Complex.ofReal_sub,
    sub_mul, Finset.sum_sub_distrib]
  all_goals exact hk

theorem complex_transform_sum_algebra (s z e L p q E : ℂ) (hs : s ≠ 0)
    (hsz : s+z ≠ 0) (r X Y J C V : Fin N → ℂ) :
    L*(p*(∑ m, r m*X m*V m)+q*(-∑ m, r m*Y m*V m)+
      (∑ m, r m*J m*V m)/(s+z)+(E-∑ m, r m*C m*V m)*(1-e)/s) +
      (E-∑ m, r m*C m*V m)*(L*e)/(s+z) =
    L*(E*(1/s-z*e/(s*(s+z))) +
      ∑ m, r m*V m*(p*X m-q*Y m+J m/(s+z)-C m*(1/s-z*e/(s*(s+z))))) := by
  have hco : (1-e)/s+e/(s+z) = 1/s-z*e/(s*(s+z)) := by field_simp; ring
  calc
    _ = L*(E*((1-e)/s+e/(s+z)) +
      ((∑ m, p*(r m*X m*V m))-(∑ m, q*(r m*Y m*V m)) +
        (∑ m, r m*J m*V m/(s+z)) -
          ∑ m, r m*C m*V m*((1-e)/s+e/(s+z)))) := by
      simp only [div_eq_mul_inv, mul_neg, mul_add, mul_sub, add_mul, sub_mul, Finset.mul_sum,
        Finset.sum_div, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp only [mul_assoc, mul_comm, mul_left_comm]
      ring
    _ = _ := by
      rw [hco]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      ring

theorem complex_physical_tangent_kernel (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0)
    (s : ℂ) (hs : s ≠ 0) (hsz : s+(z u : ℂ) ≠ 0) (i m : Fin N) :
    complexPolyMoment1 s (σ i)*
      (((1/(z u)^2-σ i/(2*z u))*Qppphys ρ σ m m+
        π*σ m/vacMix ρ σ*(1/(z u)-σ i) : ℝ) : ℂ) -
    complexPolyMoment2 s (σ i)*((Qppphys ρ σ m m/(z u)+2*π*σ m/vacMix ρ σ : ℝ) : ℂ) +
      ((baseSource z ρ σ u i m/(z u) : ℝ) : ℂ)/(s+(z u : ℂ)) -
      (((1-z u*σ i)/(z u)^2*Q0phys ρ σ i m+
        (1-z u*σ i+(z u*σ i)^2/2)/(z u)^3*Qppphys ρ σ m m : ℝ) : ℂ)*
        (1/s-(z u : ℂ)*Complex.exp (-s*(σ i : ℂ))/(s*(s+(z u : ℂ)))) =
      -complexHSMoment ρ σ s i m/s +
        (z u : ℂ)*Complex.exp (-s*(σ i : ℂ))*complexHSMoment ρ σ (-s) i m/(s*(s+(z u : ℂ))) := by
  have hzc : (z u : ℂ) ≠ 0 := by exact_mod_cast hz
  have hqp : (Q0phys ρ σ i m : ℂ) =
      (σ i : ℂ)/2*(Qppphys ρ σ m m : ℂ)+((π/vacMix ρ σ : ℝ) : ℂ)*(σ m : ℂ) := by
    have h := physical_HS_rank_one_coefficient ρ σ hv i m
    have hr : Q0phys ρ σ i m = σ i/2*Qppphys ρ σ m m+π/vacMix ρ σ*σ m := by linear_combination h
    exact_mod_cast hr
  have hkernel := complex_tangent_kernel s (z u) (σ i) (σ m) (Qppphys ρ σ m m)
    ((π/vacMix ρ σ : ℝ) : ℂ) hs hzc hsz
  have he : complexPolyMoment1 s (σ i)*
      (((1/(z u)^2-σ i/(2*z u))*Qppphys ρ σ m m+
        π*σ m/vacMix ρ σ*(1/(z u)-σ i) : ℝ) : ℂ) -
    complexPolyMoment2 s (σ i)*((Qppphys ρ σ m m/(z u)+2*π*σ m/vacMix ρ σ : ℝ) : ℂ) +
      ((baseSource z ρ σ u i m/(z u) : ℝ) : ℂ)/(s+(z u : ℂ)) -
      (((1-z u*σ i)/(z u)^2*Q0phys ρ σ i m+
        (1-z u*σ i+(z u*σ i)^2/2)/(z u)^3*Qppphys ρ σ m m : ℝ) : ℂ)*
        (1/s-(z u : ℂ)*Complex.exp (-s*(σ i : ℂ))/(s*(s+(z u : ℂ)))) =
      -complexHSMoment ρ σ s i m/(s+(z u : ℂ)) -
        (z u : ℂ)*((π*σ m/vacMix ρ σ : ℝ) : ℂ)*complexEdgeMomentM s (σ i)/(s*(s+(z u : ℂ))) := by
    convert! hkernel using 1 <;>
      simp only [baseSource, complexHSMoment] <;> push_cast <;> rw [hqp] <;>
        push_cast <;> field_simp [hzc, hs, hsz] <;> ring
  rw [he]
  have hp := complexHSMoment_parity ρ σ hv s hs i m
  simp only [neg_mul] at hp
  field_simp
  linear_combination (z u : ℂ)*hp

theorem singleTangentQhat_hs_factor (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι)
    (s : ℂ) (hs : s ≠ 0) (hsz : s+(z u : ℂ) ≠ 0) (i j : Fin N) :
    singleTangentQhat z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u s i j =
      Complex.exp (-s*(edgeLo σ i j : ℂ))/s *
        ((dressedEdgeSlope z ρ σ K u i j : ℂ) -
          ∑ m, (ρ m : ℂ)*complexHSMoment ρ σ s i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)) -
      (z u : ℂ)*Complex.exp (-s*(edgeHi σ i j : ℂ))/(s*(s+(z u : ℂ))) *
        ((dressedEdgeSlope z ρ σ K u i j : ℂ) -
          ∑ m, (ρ m : ℂ)*complexHSMoment ρ σ (-s) i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)) := by
  let X : Fin N → ℂ := fun m => (((1/(z u)^2-σ i/(2*z u))*Qppphys ρ σ m m+
    π*σ m/vacMix ρ σ*(1/(z u)-σ i) : ℝ) : ℂ)
  let Y : Fin N → ℂ := fun m => ((Qppphys ρ σ m m/(z u)+2*π*σ m/vacMix ρ σ : ℝ) : ℂ)
  let J : Fin N → ℂ := fun m => ((baseSource z ρ σ u i m/(z u) : ℝ) : ℂ)
  let C0 : Fin N → ℂ := fun m => (((1-z u*σ i)/(z u)^2*Q0phys ρ σ i m+
    (1-z u*σ i+(z u*σ i)^2/2)/(z u)^3*Qppphys ρ σ m m : ℝ) : ℂ)
  let V : Fin N → ℂ := fun m => (dressedEdgeSlope z ρ σ K u m j : ℂ)
  have he : Complex.exp (-s*(edgeHi σ i j : ℂ)) =
      Complex.exp (-s*(edgeLo σ i j : ℂ))*Complex.exp (-s*(σ i : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [edgeHi, edgeLo]
    push_cast
    ring
  have hq : (mixDqp (z u) ρ σ (baseSeed z ρ σ u) (firstOrderDt z ρ σ K u) i j : ℂ) =
      ∑ m, (ρ m : ℂ)*X m*V m := by
    rw [show mixDqp (z u) ρ σ (baseSeed z ρ σ u) (firstOrderDt z ρ σ K u) i j =
      mixDqp (z u) ρ σ (Matrix.of (baseSeed z ρ σ u)) (Matrix.of (firstOrderDt z ρ σ K u)) i j from rfl,
      mixDqp_firstOrderDt z ρ σ K hz hv hρ hσ u i j]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, X, V]
  have hA : (mixDA (z u) ρ σ (baseSeed z ρ σ u) (firstOrderDt z ρ σ K u) j : ℂ) =
      -∑ m, (ρ m : ℂ)*Y m*V m := by
    rw [show mixDA (z u) ρ σ (baseSeed z ρ σ u) (firstOrderDt z ρ σ K u) j =
      mixDA (z u) ρ σ (Matrix.of (baseSeed z ρ σ u)) (Matrix.of (firstOrderDt z ρ σ K u)) j from rfl,
      mixDA_firstOrderDt z ρ σ K hz hv hρ hσ u j]
    simp only [Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul, Y, V]
  have hW : (W z ρ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u i j : ℂ) =
      ∑ m, (ρ m : ℂ)*J m*V m := by
    rw [firstOrderW_source_entry z ρ σ K hz hv hρ hσ u i j]
    simp only [J, V, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hC : (C z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u i j : ℂ) =
      (dressedEdgeSlope z ρ σ K u i j : ℂ)-∑ m, (ρ m : ℂ)*C0 m*V m := by
    rw [firstOrderC_moment_entry z ρ σ K hz hv hρ hσ u i j]
    simp only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul, C0, V]
  unfold singleTangentQhat
  rw [hq, hA, hW, hC, he,
    complex_transform_sum_algebra s (z u) _ _ _ _ _ hs hsz]
  have hker : ∀ m, complexPolyMoment1 s (σ i)*X m-complexPolyMoment2 s (σ i)*Y m+
      J m/(s+(z u : ℂ))-C0 m*(1/s-(z u : ℂ)*Complex.exp (-s*(σ i : ℂ))/(s*(s+(z u : ℂ)))) =
      -complexHSMoment ρ σ s i m/s +
        (z u : ℂ)*Complex.exp (-s*(σ i : ℂ))*complexHSMoment ρ σ (-s) i m/(s*(s+(z u : ℂ))) :=
    fun m => complex_physical_tangent_kernel z ρ σ u (hz u).ne' hv.ne' s hs hsz i m
  simp_rw [hker]
  simp only [V, div_eq_mul_inv, mul_add, mul_sub, mul_neg, add_mul, sub_mul,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib]
  ring

/-- Explicit finite-tail Q factor tangent, with the physical HS phases.
The coefficient E is the actual two-sided HS resolvent amplitude. -/
def hsFactorQ1 (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (s : ℂ) (i j : Fin N) : ℂ :=
  ∑ u, (Complex.exp (-s*(edgeLo σ i j : ℂ))/s *
    ((dressedEdgeSlope z ρ σ K u i j : ℂ) -
      ∑ m, (ρ m : ℂ)*complexHSMoment ρ σ s i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)) -
    (z u : ℂ)*Complex.exp (-s*(edgeHi σ i j : ℂ))/(s*(s+(z u : ℂ))) *
      ((dressedEdgeSlope z ρ σ K u i j : ℂ) -
        ∑ m, (ρ m : ℂ)*complexHSMoment ρ σ (-s) i m*(dressedEdgeSlope z ρ σ K u m j : ℂ)))

theorem QhatComplex_firstOrder_difference_hs_factor (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (s : ℂ) (hs : s ≠ 0) (hsz : ∀ u, s+(z u : ℂ) ≠ 0) (i j : Fin N) :
    QhatComplex z σ (amplitudeA z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ))
      (amplitudeQp z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ))
      (W z ρ (firstOrderDt z ρ σ K) (baseSeed z ρ σ))
      (C z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ)) s i j -
    QhatComplex z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ)) (amplitudeQp z ρ σ 0 (baseSeed z ρ σ))
      (W z ρ 0 (baseSeed z ρ σ)) (C z ρ σ 0 (baseSeed z ρ σ)) s i j =
      hsFactorQ1 z ρ σ K s i j := by
  rw [QhatComplex_difference_eq_tangent_sum]
  unfold hsFactorQ1
  apply Finset.sum_congr rfl
  intro u _
  exact singleTangentQhat_hs_factor z ρ σ K hz hv hρ hσ u s hs (hsz u) i j

theorem linearizedFourierQ_eq_hs_factor (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    linearizedFourierQ z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k i j =
      hsFactorQ1 z ρ σ K (Complex.I*k) i j := by
  rw [linearizedFourierQ_eq_Qhat_difference z hz ρ σ (fun i => (hσ i).le) _ _ k hk]
  apply QhatComplex_firstOrder_difference_hs_factor z ρ σ K hz hv hρ hσ
  · exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  · intro u he
    have hr := congrArg Complex.re he
    simp at hr
    exact (hz u).ne' hr

/-- Along every differentiable actual local BH germ, the actual Q Fourier
derivative has this HS factor decomposition. No symmetry hypothesis on K. -/
theorem fourierQ_hasDerivAt_hs_factor_of_family (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, baseSeed z ρ σ))
    (hr : ∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2)
    (hd : HasDerivAt ψ d 0) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    HasDerivAt (fun τ => fourierQ z σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) k i j)
      (hsFactorQ1 z ρ σ K (Complex.I*k) i j) 0 := by
  have h := fourierQ_hasDerivAt_seed z hz ρ σ (fun i => (hσ i).le)
    (baseSeed z ρ σ) ψ d h0 hd k i j
  rw [firstOrderDt_eq_of_family z ρ σ K hz hv hρ hσ ψ d h0 hr hd,
    linearizedFourierQ_eq_hs_factor z ρ σ K hz hv hρ hσ k hk] at h
  exact h

/-- Existence and Fourier decomposition are obtained together from the
internally constructed physical PY seed and its actual BH Jacobian. -/
theorem exists_contDiffAt_root_with_hs_factor_Q1 (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      ∀ k, k ≠ 0 → ∀ i j, HasDerivAt (fun τ => fourierQ z σ
        (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
        (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) k i j)
        (hsFactorQ1 z ρ σ K (Complex.I*k) i j) 0 := by
  obtain ⟨ψ, h0, hr, hc⟩ := exists_contDiffAt_root z ρ σ K hz hv hρ hσ
  have hd := (hc.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
  exact ⟨ψ, h0, hr, hc, fun k hk i j =>
    fourierQ_hasDerivAt_hs_factor_of_family z ρ σ K hz hv hρ hσ ψ _ h0 hr hd k hk i j⟩

end FMSA.ExactMSA.MultiTailMixture
