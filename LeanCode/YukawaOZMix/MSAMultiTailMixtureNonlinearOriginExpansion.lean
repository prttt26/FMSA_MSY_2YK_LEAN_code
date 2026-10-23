import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearOriginDictionary
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearReciprocity

/-! Exact finite origin expansions of the actual rational J and L.
The rational remainder is retained; no convergence or infinite-series
assumption is used. The number of terms is arbitrary. -/
noncomputable section
open Real
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem yukawa_resolvent_finite_geometric_expansion (z s : ℝ)
    (hz : z ≠ 0) (hsz : s+z ≠ 0) (n : ℕ) :
    z/(s+z) = (∑ p ∈ Finset.range n, (-s/z)^p) + (-s/z)^n*(z/(s+z)) := by
  have hstep : z/(s+z) = 1+(-s/z)*(z/(s+z)) := by
    field_simp [hz, hsz]
    ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linear_combination ih + (-s/z)^n*hstep

theorem yukawa_tail_finite_origin_expansion (z a : ι → ℝ) (s : ℝ)
    (hz : ∀ u, z u ≠ 0) (hsz : ∀ u, s+z u ≠ 0) (n : ℕ) :
    (∑ u, z u*a u/(s+z u)) =
      (∑ p ∈ Finset.range n, (-s)^p*(∑ u, a u/(z u)^p)) +
      (-s)^n*(∑ u, a u/(z u)^n*(z u/(s+z u))) := by
  have ht (u : ι) : z u*a u/(s+z u) =
      (∑ p ∈ Finset.range n, (-s)^p*(a u/(z u)^p)) +
      (-s)^n*(a u/(z u)^n*(z u/(s+z u))) := by
    calc
      _ = a u*(z u/(s+z u)) := by ring
      _ = a u*((∑ p ∈ Finset.range n, (-s/z u)^p)+
          (-s/z u)^n*(z u/(s+z u))) := by
        exact congrArg (fun t => a u*t)
          (yukawa_resolvent_finite_geometric_expansion (z u) s (hz u) (hsz u) n)
      _ = _ := by
        simp only [mul_add, Finset.mul_sum, div_pow]
        congr 1
        · apply Finset.sum_congr rfl
          intro p _
          ring
        · ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
  · rw [Finset.mul_sum]

def nonlinearOriginCRemainder (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (n : ℕ) (s : ℝ) (i j : Fin N) : ℝ :=
  ∑ u, C z ρ σ Dt G u i j/(z u)^n*(z u/(s+z u))

def nonlinearOriginWRemainder (z : ι → ℝ) (ρ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (n : ℕ) (s : ℝ) (i j : Fin N) : ℝ :=
  ∑ u, W z ρ Dt G u i j/(z u)^n*(z u/(s+z u))

theorem nonlinearRationalJ_finite_origin_expansion
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (s : ℝ) (hsz : ∀ u, s+z u ≠ 0)
    (n : ℕ) (i j : Fin N) :
    nonlinearRationalJ z ρ σ Dt G s i j =
      amplitudeA z ρ σ Dt G j/s^2 + amplitudeQp z ρ σ Dt G i j/s +
      (∑ p ∈ Finset.range n, (-s)^p*nonlinearOriginCmoment z ρ σ Dt G p i j) +
      (-s)^n*nonlinearOriginCRemainder z ρ σ Dt G n s i j := by
  have ht := yukawa_tail_finite_origin_expansion z (fun u => C z ρ σ Dt G u i j) s hz hsz n
  simp only [nonlinearRationalJ, Matrix.of_apply, nonlinearOriginCmoment,
    nonlinearOriginCRemainder, ht]
  ring

theorem nonlinearRationalL_finite_origin_expansion
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (s : ℝ) (hsz : ∀ u, s+z u ≠ 0)
    (n : ℕ) (i j : Fin N) :
    nonlinearRationalL z ρ σ Dt G s i j =
      amplitudeA z ρ σ Dt G j/s^2 +
      (amplitudeQp z ρ σ Dt G i j-σ i*amplitudeA z ρ σ Dt G j)/s +
      nonlinearLowerQValue z ρ σ Dt G i j -
      (∑ p ∈ Finset.range n, (-s)^p*nonlinearOriginWmoment z ρ Dt G p i j) -
      (-s)^n*nonlinearOriginWRemainder z ρ Dt G n s i j := by
  have ht := yukawa_tail_finite_origin_expansion z (fun u => W z ρ Dt G u i j) s hz hsz n
  simp only [nonlinearRationalL, Matrix.of_apply, ht, nonlinearOriginWmoment,
    nonlinearOriginWRemainder]
  ring

theorem nonlinearOriginCRemainder_at_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (n : ℕ) (i j : Fin N) :
    nonlinearOriginCRemainder z ρ σ Dt G n 0 i j =
      nonlinearOriginCmoment z ρ σ Dt G n i j := by
  simp [nonlinearOriginCRemainder, nonlinearOriginCmoment, hz]

theorem nonlinearOriginWRemainder_at_zero
    (z : ι → ℝ) (ρ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (n : ℕ) (i j : Fin N) :
    nonlinearOriginWRemainder z ρ Dt G n 0 i j =
      nonlinearOriginWmoment z ρ Dt G n i j := by
  simp [nonlinearOriginWRemainder, nonlinearOriginWmoment, hz]

end FMSA.ExactMSA.MultiTailMixture
