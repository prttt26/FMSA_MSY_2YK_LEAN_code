import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairPhysicalSymbol

/-! Actual HS matrix-symbol dictionaries, retaining additive contact phases
and right-density Baxter products. -/
noncomputable section
open Real FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def hsPairHSBaxterC (ρ σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  complexHSQ ρ σ s+(complexHSQ ρ σ (-s)).transpose-
    complexHSQ ρ σ s*Matrix.diagonal (fun i => (ρ i : ℂ))*(complexHSQ ρ σ (-s)).transpose

theorem hsPair_exp_inverse (s x : ℂ) :
    Complex.exp (-(-s)*x)=1/Complex.exp (-s*x) := by
  apply (eq_div_iff (Complex.exp_ne_zero _)).mpr
  simpa only [mul_comm] using complex_exp_pair s x

theorem hsPair_contactFactor_product (ρ σ : Fin N → ℝ) (s : ℂ)
    (f : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (complexHSRightFactor ρ σ (-s)*
      Matrix.of (fun m n => Complex.exp (-s*(edgeHi σ m n : ℂ))*f m n)) i j =
    Complex.exp (-s*(edgeHi σ i j : ℂ))*
      (f i j-∑ m, (ρ m : ℂ)*complexHSMoment ρ σ (-s) i m*f m j) := by
  rw [complexHSRightFactor, sub_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.mul_apply (M := complexHSQ ρ σ (-s)*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, complexHSQ, Matrix.of_apply]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have he := complexHSQ_contact_product ρ σ s i m j
  linear_combination (ρ m : ℂ)*complexHSMoment ρ σ (-s) i m*f m j*he

theorem hsPairHSBaxterC_unphased (ρ σ : Fin N → ℝ) (s : ℂ) (i j : Fin N) :
    hsPairHSBaxterC ρ σ s i j = Complex.exp (-s*(edgeLo σ i j : ℂ))*
      (complexHSMoment ρ σ s i j+complexHSMoment ρ σ (-s) j i-
        ∑ m, (ρ m : ℂ)*complexHSMoment ρ σ s i m*complexHSMoment ρ σ (-s) j m) := by
  have hsji : Complex.exp (-(-s)*(edgeLo σ j i : ℂ)) =
      Complex.exp (-s*(edgeLo σ i j : ℂ)) := by
    congr 1
    unfold edgeLo
    push_cast
    ring
  have hphase (m : Fin N) :
      Complex.exp (-s*(edgeLo σ i m : ℂ))*Complex.exp (-(-s)*(edgeLo σ j m : ℂ)) =
        Complex.exp (-s*(edgeLo σ i j : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold edgeLo
    push_cast
    ring
  unfold hsPairHSBaxterC
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply]
  rw [Matrix.mul_apply (M := complexHSQ ρ σ s*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, complexHSQ, Matrix.of_apply, hsji]
  rw [mul_sub, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  linear_combination (ρ m : ℂ)*complexHSMoment ρ σ s i m*complexHSMoment ρ σ (-s) j m*hphase m

theorem hsPairHSBaxterC_eq_pair_symbol (ρ σ : Fin N → ℝ) (s : ℂ) (hs : s ≠ 0)
    (i j : Fin N) :
    hsPairHSBaxterC ρ σ s i j = Complex.exp (-s*(edgeLo σ i j : ℂ))*
      hsPairSymbolC (hsPairPhysicalA ρ σ) (hsPairPhysicalC ρ σ)
        (∑ m, (ρ m : ℂ)) (∑ m, (ρ m : ℂ)*(σ m : ℂ))
        (∑ m, (ρ m : ℂ)*(σ m : ℂ)^2) (σ i) (σ j)
        (Complex.exp (-s*σ i)) (Complex.exp (-s*σ j)) s := by
  have he (m : Fin N) := hsPair_exp_inverse s (σ m)
  rw [hsPairHSBaxterC_unphased]
  simp_rw [complexHSMoment_eq_pair_symbol ρ σ s hs,
    complexHSMoment_eq_pair_symbol ρ σ (-s) (neg_ne_zero.mpr hs), he]
  rw [hsPairSymbol_sum_kernel_product]
  unfold hsPairSymbolC
  ring

theorem hsPairSourceMoment_contactFactor (ρ σ : Fin N → ℝ) (s : ℂ) (hs : s ≠ 0)
    (i j : Fin N) :
    (complexHSRightFactor ρ σ (-s)*rdfPhase σ s*hsPairSourceMoment ρ σ s*rdfPhase σ s) i j =
    Complex.exp (-s*(edgeHi σ i j : ℂ))/(2*Real.pi)*
      (hsPairSymbolSource (hsPairPhysicalA ρ σ) (hsPairPhysicalC ρ σ) (σ i) (σ j) s-
        hsPairSymbolSourceProduct
          (hsPairSymbolP (σ i) (1/Complex.exp (-s*σ i)) (-s))
          (hsPairSymbolT (σ i) (1/Complex.exp (-s*σ i)) (-s))
          (hsPairPhysicalA ρ σ) (hsPairPhysicalC ρ σ)
          (∑ m, (ρ m : ℂ)) (∑ m, (ρ m : ℂ)*(σ m : ℂ))
          (∑ m, (ρ m : ℂ)*(σ m : ℂ)^2) (σ j) s) := by
  have hinv (m : Fin N) := hsPair_exp_inverse s (σ m)
  have he : rdfPhase σ s*hsPairSourceMoment ρ σ s*rdfPhase σ s =
      Matrix.of (fun m n => Complex.exp (-s*(edgeHi σ m n : ℂ))*hsPairSourceMoment ρ σ s m n) := by
    ext m n
    simp only [rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    have hp := rdfPhase_contact_product σ s m n
    linear_combination hsPairSourceMoment ρ σ s m n*hp
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (rdfPhase σ s), he,
    hsPair_contactFactor_product]
  simp_rw [hsPairSourceMoment_eq_pair_symbol,
    complexHSMoment_eq_pair_symbol ρ σ (-s) (neg_ne_zero.mpr hs), hinv]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  rw [hsPairSymbol_sum_source_product]
  ring

theorem hsPairSourceMoment_factor_difference (ρ σ : Fin N → ℝ) (s : ℂ) (hs : s ≠ 0) :
    complexHSRightFactor ρ σ (-s)*rdfPhase σ s*hsPairSourceMoment ρ σ s*rdfPhase σ s-
      complexHSRightFactor ρ σ s*rdfPhase σ (-s)*hsPairSourceMoment ρ σ (-s)*rdfPhase σ (-s) =
      (-s/(2*Real.pi)) • hsPairHSBaxterC ρ σ s := by
  have hx2 : (∑ m, (ρ m : ℂ)*(σ m : ℂ)^2)=(xi2 ρ σ : ℂ) := by
    unfold xi2
    push_cast
    rfl
  have hrel : hsPairPhysicalA ρ σ*(∑ m, (ρ m : ℂ)*(σ m : ℂ)^2)=
      4*hsPairPhysicalC ρ σ := by rw [hx2]; exact hsPair_physical_relation ρ σ
  ext i j
  have hplus := hsPairSourceMoment_contactFactor ρ σ s hs i j
  have hminus := hsPairSourceMoment_contactFactor ρ σ (-s) (neg_ne_zero.mpr hs) i j
  have hinv (m : Fin N) := hsPair_exp_inverse s (σ m)
  simp only [neg_neg] at hinv
  simp only [neg_neg] at hminus
  rw [hinv i] at hminus
  simp only [one_div, inv_inv] at hminus
  have hphaseplus : Complex.exp (-s*(edgeHi σ i j : ℂ)) =
      Complex.exp (-s*(edgeLo σ i j : ℂ))*Complex.exp (-s*(σ i : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold edgeLo edgeHi
    push_cast
    ring
  have hphaseminus : Complex.exp (-(-s)*(edgeHi σ i j : ℂ)) =
      Complex.exp (-s*(edgeLo σ i j : ℂ))/Complex.exp (-s*(σ j : ℂ)) := by
    rw [div_eq_mul_inv, ← one_div, ← hsPair_exp_inverse s (σ j), ← Complex.exp_add]
    congr 1
    unfold edgeLo edgeHi
    push_cast
    ring
  have hid := hsPairSymbol_identity_of_HS_relation (hsPairPhysicalA ρ σ) (hsPairPhysicalC ρ σ)
    (∑ m, (ρ m : ℂ)) (∑ m, (ρ m : ℂ)*(σ m : ℂ)) (∑ m, (ρ m : ℂ)*(σ m : ℂ)^2)
    (σ i) (σ j) (Complex.exp (-s*σ i)) (Complex.exp (-s*σ j)) s hs
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) hrel
  simp only [neg_neg] at hphaseminus
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hplus, hminus, hsPairHSBaxterC_eq_pair_symbol ρ σ s hs i j, hphaseplus, hphaseminus]
  linear_combination (Complex.exp (-s*(edgeLo σ i j : ℂ))/(2*Real.pi))*hid

end FMSA.ExactMSA.MultiTailMixture
