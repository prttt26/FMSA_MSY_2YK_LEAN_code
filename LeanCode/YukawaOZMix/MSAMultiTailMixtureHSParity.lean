import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPAmplitude

/-! The exact complex HS parity defect is rank one. It is the algebraic
identity needed to retain the compact quadratic correction in the DP tangent.
No inverse, density positivity, or distinct tail rates are assumed here. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def complexPolyMoment1 (s x : ℂ) : ℂ := (1-s*x-Complex.exp (-s*x))/s^2
def complexPolyMoment2 (s x : ℂ) : ℂ :=
  (1-s*x+(s*x)^2/2-Complex.exp (-s*x))/s^3
def complexEdgeMomentM (s x : ℂ) : ℂ :=
  (2-s*x-(2+s*x)*Complex.exp (-s*x))/s^2

def complexHSMoment (ρ σ : Fin N → ℝ) (s : ℂ) (i j : Fin N) : ℂ :=
  complexPolyMoment1 s (σ i)*Q0phys ρ σ i j +
    complexPolyMoment2 s (σ i)*Qppphys ρ σ j j

theorem complex_exp_pair (s x : ℂ) :
    Complex.exp (-s*x)*Complex.exp (-(-s)*x) = 1 := by
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 1 <;> ring

theorem complexPolyMoment1_parity (s x : ℂ) (hs : s ≠ 0) :
    complexPolyMoment1 s x-Complex.exp (-s*x)*complexPolyMoment1 (-s) x =
      complexEdgeMomentM s x := by
  unfold complexPolyMoment1 complexEdgeMomentM
  have he := complex_exp_pair s x
  simp only [neg_mul, neg_neg] at he
  field_simp
  linear_combination he

theorem complexPolyMoment2_parity (s x : ℂ) (hs : s ≠ 0) :
    complexPolyMoment2 s x-Complex.exp (-s*x)*complexPolyMoment2 (-s) x =
      -x/2*complexEdgeMomentM s x := by
  unfold complexPolyMoment2 complexEdgeMomentM
  have he := complex_exp_pair s x
  simp only [neg_mul, neg_neg] at he
  field_simp
  linear_combination -2*he

theorem physical_HS_rank_one_coefficient (ρ σ : Fin N → ℝ)
    (hv : vacMix ρ σ ≠ 0) (i j : Fin N) :
    Q0phys ρ σ i j-σ i/2*Qppphys ρ σ j j = π*σ j/vacMix ρ σ := by
  unfold Q0phys Qppphys
  field_simp
  <;> ring

theorem complexHSMoment_parity (ρ σ : Fin N → ℝ) (hv : vacMix ρ σ ≠ 0)
    (s : ℂ) (hs : s ≠ 0) (i j : Fin N) :
    complexHSMoment ρ σ s i j-Complex.exp (-s*(σ i : ℂ))*complexHSMoment ρ σ (-s) i j =
      ((π*σ j/vacMix ρ σ : ℝ) : ℂ)*complexEdgeMomentM s (σ i) := by
  have hc : (Q0phys ρ σ i j : ℂ)-(σ i : ℂ)/2*(Qppphys ρ σ j j : ℂ) =
      ((π*σ j/vacMix ρ σ : ℝ) : ℂ) := by
    exact_mod_cast physical_HS_rank_one_coefficient ρ σ hv i j
  unfold complexHSMoment
  calc
    _ = (complexPolyMoment1 s (σ i)-Complex.exp (-s*(σ i : ℂ))*complexPolyMoment1 (-s) (σ i))*
        (Q0phys ρ σ i j : ℂ) +
      (complexPolyMoment2 s (σ i)-Complex.exp (-s*(σ i : ℂ))*complexPolyMoment2 (-s) (σ i))*
        (Qppphys ρ σ j j : ℂ) := by ring
    _ = _ := by rw [complexPolyMoment1_parity s _ hs, complexPolyMoment2_parity s _ hs, ← hc]; ring

theorem complexHSMoment_eq_real (ρ σ : Fin N → ℝ) (s : ℝ) (i j : Fin N) :
    complexHSMoment ρ σ (s : ℂ) i j = (hsMoment ρ σ s i j : ℂ) := by
  unfold complexHSMoment hsMoment complexPolyMoment1 complexPolyMoment2
  push_cast
  rfl

/-- The recentered HS moment is the actual zero-Dt Q transform. -/
theorem QhatComplex_zero_eq_phase_HS (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G0 : TailMatrix ι N) (s : ℂ) (i j : Fin N) :
    QhatComplex z σ (amplitudeA z ρ σ 0 G0) (amplitudeQp z ρ σ 0 G0)
      (W z ρ 0 G0) (C z ρ σ 0 G0) s i j =
      Complex.exp (-s*(edgeLo σ i j : ℂ))*complexHSMoment ρ σ s i j := by
  simp only [QhatComplex, amplitudeA_zero, amplitudeQp_zero, W, C, Wt, Ct, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, Complex.ofReal_zero, zero_div,
    zero_mul, add_zero]
  rfl

end FMSA.ExactMSA.MultiTailMixture
