import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairLaplace

/-! The actual pair-contact HS source completes the causal transfer into
the physical finite-rank moment source. This is a transform identity, not
yet the radial HS-reference OZ certificate. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def hsPairBackground (σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (1+s*(edgeHi σ i j : ℂ))/s^2)

def hsPairSourceMoment (ρ σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (Qppphys ρ σ i i : ℂ)/(2*Real.pi*s^2)+
    ((σ i : ℂ)/(2*(vacMix ρ σ : ℂ))+(σ j : ℂ)*(Qppphys ρ σ i i : ℂ)/(4*Real.pi))/s)

theorem rdfMatrixLaplace_kernel_entry (ρ σ : Fin N → ℝ) (s : ℂ) (i j : Fin N) :
    rdfMatrixLaplace (rdfCausalKernel ρ σ) s i j =
      (ρ i : ℂ)*FMSA.causalComplexLaplace (rdfRecenteredHSQ ρ σ i j) s := by
  unfold rdfMatrixLaplace rdfCausalKernel FMSA.causalComplexLaplace
  simp only [Matrix.of_apply]
  push_cast
  simp only [mul_assoc]
  rw [integral_const_mul]

theorem hsPairSourceMoment_eq_column_moments (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (s : ℂ) (i j : Fin N) :
    hsPairSourceMoment ρ σ s i j =
      (1-(∑ m, (ρ m : ℂ)*((∫ t in (0 : ℝ)..σ m,
        rdfRecenteredHSQ ρ σ m i t : ℝ) : ℂ)))/s^2+
      ((edgeHi σ i j : ℂ)+(∑ m, (ρ m : ℂ)*
        (((∫ t in (0 : ℝ)..σ m, t*rdfRecenteredHSQ ρ σ m i t : ℝ) : ℂ)-
          (edgeHi σ m j : ℂ)*((∫ t in (0 : ℝ)..σ m,
            rdfRecenteredHSQ ρ σ m i t : ℝ) : ℂ))))/s := by
  have hm0 := congrArg Complex.ofReal (rdfRecenteredHSQ_column_mass_identity ρ σ hσ hv i)
  have hm1 := congrArg Complex.ofReal (rdfRecenteredHSQ_column_contact_identity ρ σ hσ hv i j)
  push_cast at hm0 hm1
  rw [hm0, hm1]
  unfold hsPairSourceMoment
  simp only [Matrix.of_apply]
  ring

theorem rdfHSCoreSource_laplace_completed (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (s : ℂ) (hs : s ≠ 0) :
    rdfMatrixLaplace (rdfHSCoreSource ρ σ) s+
      (rdfRecenteredFactor ρ σ s).transpose*hsPairBackground σ s = hsPairSourceMoment ρ σ s := by
  rw [rdfRecenteredFactor, Matrix.transpose_sub, Matrix.transpose_one,
    sub_mul, Matrix.one_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [rdfHSCoreSource_laplace_moments ρ σ hσ s hs i j,
    hsPairSourceMoment_eq_column_moments ρ σ hσ hv s i j]
  simp only [rdfMatrixLaplace_kernel_entry, hsPairBackground, Matrix.of_apply]
  let M0 := fun m => ((∫ v in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i v : ℝ) : ℂ)
  let M1 := fun m => ((∫ v in (0 : ℝ)..σ m, v*rdfRecenteredHSQ ρ σ m i v : ℝ) : ℂ)
  let R := fun m => (edgeHi σ m j : ℂ)
  let Q := fun m => FMSA.causalComplexLaplace (rdfRecenteredHSQ ρ σ m i) s
  change (∑ m, (ρ m : ℂ)*((M1 m-R m*M0 m)/s-M0 m/s^2+(R m/s+1/s^2)*Q m))+
    ((1+s*(edgeHi σ i j : ℂ))/s^2-
      ∑ m, (ρ m : ℂ)*Q m*((1+s*R m)/s^2)) =
    (1-(∑ m, (ρ m : ℂ)*M0 m))/s^2+
      ((edgeHi σ i j : ℂ)+(∑ m, (ρ m : ℂ)*(M1 m-R m*M0 m)))/s
  have he (m : Fin N) :
      (ρ m : ℂ)*((M1 m-R m*M0 m)/s-M0 m/s^2+(R m/s+1/s^2)*Q m) =
      (ρ m : ℂ)*Q m*((1+s*R m)/s^2)+
        ((ρ m : ℂ)*(M1 m-R m*M0 m)/s-(ρ m : ℂ)*M0 m/s^2) := by
    field_simp [hs]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  field_simp [hs]
  ring

theorem rdfHSPairExterior_completed_transfer (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (δ : ℝ)
    (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1) (s : ℂ)
    (hs : 0 ≤ s.re) (hs0 : s ≠ 0) :
    (rdfRecenteredFactor ρ σ s).transpose*
      (rdfMatrixLaplace (rdfHSPairExterior ρ σ) s+hsPairBackground σ s) =
      hsPairSourceMoment ρ σ s := by
  rw [mul_add, rdfHSPairExterior_laplace ρ σ δ hδ hb s hs]
  exact rdfHSCoreSource_laplace_completed ρ σ hσ hv s hs0

end FMSA.ExactMSA.MultiTailMixture
