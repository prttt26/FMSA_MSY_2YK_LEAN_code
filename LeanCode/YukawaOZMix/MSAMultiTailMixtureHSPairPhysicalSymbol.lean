import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairFourier

/-! Dictionaries connecting the finite symbol algebra to the actual HS
coefficients. The scalar moment relation is a proved physical identity. -/
noncomputable section
open Real FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def hsPairPhysicalA (ρ σ : Fin N → ℝ) : ℂ := (2*Real.pi/vacMix ρ σ : ℝ)
def hsPairPhysicalC (ρ σ : Fin N → ℝ) : ℂ := (Real.pi*xi2 ρ σ/(2*vacMix ρ σ) : ℝ)

theorem hsPair_physical_alpha (ρ σ : Fin N → ℝ) (i : Fin N) :
    hsPairSymbolAlpha (hsPairPhysicalA ρ σ) (hsPairPhysicalC ρ σ) (σ i) =
      (Qppphys ρ σ i i : ℂ) := by
  unfold hsPairSymbolAlpha hsPairPhysicalA hsPairPhysicalC Qppphys
  push_cast
  ring

theorem hsPair_physical_beta (ρ σ : Fin N → ℝ) (i : Fin N) :
    hsPairSymbolBeta (hsPairPhysicalA ρ σ) (σ i) =
      (Real.pi*σ i/vacMix ρ σ : ℝ) := by
  unfold hsPairSymbolBeta hsPairPhysicalA
  push_cast
  ring

theorem hsPair_physical_relation (ρ σ : Fin N → ℝ) :
    hsPairPhysicalA ρ σ*(xi2 ρ σ : ℂ)=4*hsPairPhysicalC ρ σ := by
  unfold hsPairPhysicalA hsPairPhysicalC
  exact_mod_cast hsPair_physical_symbol_relation ρ σ

theorem complexHSMoment_eq_pair_symbol (ρ σ : Fin N → ℝ)
    (s : ℂ) (hs : s ≠ 0) (i j : Fin N) :
    complexHSMoment ρ σ s i j =
      hsPairSymbolP (σ i) (Complex.exp (-s*σ i)) s*
        hsPairSymbolAlpha (hsPairPhysicalA ρ σ) (hsPairPhysicalC ρ σ) (σ j)+
      hsPairSymbolT (σ i) (Complex.exp (-s*σ i)) s*
        hsPairSymbolBeta (hsPairPhysicalA ρ σ) (σ j) := by
  rw [hsPair_physical_alpha, hsPair_physical_beta]
  unfold complexHSMoment complexPolyMoment1 complexPolyMoment2 hsPairSymbolP hsPairSymbolT
  rw [hsPair_Q0_decomposition]
  push_cast
  field_simp [hs]
  ring

theorem hsPairSourceMoment_eq_pair_symbol (ρ σ : Fin N → ℝ) (s : ℂ) (i j : Fin N) :
    hsPairSourceMoment ρ σ s i j =
      hsPairSymbolSource (hsPairPhysicalA ρ σ) (hsPairPhysicalC ρ σ) (σ i) (σ j) s/(2*Real.pi) := by
  unfold hsPairSourceMoment hsPairSymbolSource
  simp only [Matrix.of_apply, hsPair_physical_alpha, hsPair_physical_beta]
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  linear_combination -(s⁻¹*(σ i : ℂ)*(vacMix ρ σ : ℂ)⁻¹/2)*mul_inv_cancel₀ hp

theorem hsPairSymbol_sum_AA (a c : ℂ) (d x : Fin N → ℂ) :
    (∑ m, d m*(hsPairSymbolAlpha a c (x m))^2) =
      hsPairSymbolAA a c (∑ m, d m) (∑ m, d m*x m) (∑ m, d m*(x m)^2) := by
  have he (m : Fin N) : d m*(hsPairSymbolAlpha a c (x m))^2 =
      a^2*d m+(2*a^2*c)*(d m*x m)+(a^2*c^2)*(d m*(x m)^2) := by
    unfold hsPairSymbolAlpha
    ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold hsPairSymbolAA
  ring

theorem hsPairSymbol_sum_AB (a c : ℂ) (d x : Fin N → ℂ) :
    (∑ m, d m*hsPairSymbolAlpha a c (x m)*hsPairSymbolBeta a (x m)) =
      hsPairSymbolAB a c (∑ m, d m*x m) (∑ m, d m*(x m)^2) := by
  have he (m : Fin N) : d m*hsPairSymbolAlpha a c (x m)*hsPairSymbolBeta a (x m) =
      (a^2/2)*(d m*x m)+(a^2*c/2)*(d m*(x m)^2) := by
    unfold hsPairSymbolAlpha hsPairSymbolBeta
    ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold hsPairSymbolAB
  ring

theorem hsPairSymbol_sum_BB (a : ℂ) (d x : Fin N → ℂ) :
    (∑ m, d m*(hsPairSymbolBeta a (x m))^2) =
      hsPairSymbolBB a (∑ m, d m*(x m)^2) := by
  have he (m : Fin N) : d m*(hsPairSymbolBeta a (x m))^2 =
      (a^2/4)*(d m*(x m)^2) := by unfold hsPairSymbolBeta; ring
  simp_rw [he, ← Finset.mul_sum]
  unfold hsPairSymbolBB
  ring

theorem hsPairSymbol_sum_source_product (a c p t y s : ℂ) (d x : Fin N → ℂ) :
    (∑ m, d m*(p*hsPairSymbolAlpha a c (x m)+t*hsPairSymbolBeta a (x m))*
      hsPairSymbolSource a c (x m) y s) =
      hsPairSymbolSourceProduct p t a c (∑ m, d m) (∑ m, d m*x m)
        (∑ m, d m*(x m)^2) y s := by
  have he (m : Fin N) : d m*(p*hsPairSymbolAlpha a c (x m)+t*hsPairSymbolBeta a (x m))*
      hsPairSymbolSource a c (x m) y s =
      (p/s^2+y*p/(2*s))*(d m*(hsPairSymbolAlpha a c (x m))^2)+
      (p/s+t/s^2+y*t/(2*s))*(d m*hsPairSymbolAlpha a c (x m)*hsPairSymbolBeta a (x m))+
      (t/s)*(d m*(hsPairSymbolBeta a (x m))^2) := by unfold hsPairSymbolSource; ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsPairSymbol_sum_AA, hsPairSymbol_sum_AB, hsPairSymbol_sum_BB]
  unfold hsPairSymbolSourceProduct
  ring

theorem hsPairSymbol_sum_kernel_product (a c p t u v : ℂ) (d x : Fin N → ℂ) :
    (∑ m, d m*(p*hsPairSymbolAlpha a c (x m)+t*hsPairSymbolBeta a (x m))*
      (u*hsPairSymbolAlpha a c (x m)+v*hsPairSymbolBeta a (x m))) =
      p*u*hsPairSymbolAA a c (∑ m, d m) (∑ m, d m*x m) (∑ m, d m*(x m)^2)+
      (p*v+t*u)*hsPairSymbolAB a c (∑ m, d m*x m) (∑ m, d m*(x m)^2)+
      t*v*hsPairSymbolBB a (∑ m, d m*(x m)^2) := by
  have he (m : Fin N) : d m*(p*hsPairSymbolAlpha a c (x m)+t*hsPairSymbolBeta a (x m))*
      (u*hsPairSymbolAlpha a c (x m)+v*hsPairSymbolBeta a (x m)) =
      (p*u)*(d m*(hsPairSymbolAlpha a c (x m))^2)+
      (p*v+t*u)*(d m*hsPairSymbolAlpha a c (x m)*hsPairSymbolBeta a (x m))+
      (t*v)*(d m*(hsPairSymbolBeta a (x m))^2) := by ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsPairSymbol_sum_AA, hsPairSymbol_sum_AB, hsPairSymbol_sum_BB]

end FMSA.ExactMSA.MultiTailMixture
