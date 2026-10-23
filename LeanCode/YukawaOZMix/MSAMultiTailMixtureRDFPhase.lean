import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFMoment

/-! Actual integral identities for the unequal-diameter phase dictionary.
No reference factorization or RDF/OZ identity is assumed here. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfPhase (σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => Complex.exp (-s*(σ i : ℂ)/2))

def complexHSLeftFactor (ρ σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1-Matrix.diagonal (fun i => (ρ i : ℂ))*complexHSQ ρ σ s

theorem causalFull_recenteredHSQ (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (i j : Fin N) (t : ℝ) :
    causalFull (rdfRecenteredHSQ ρ σ i j) t = dpSeedQ z ρ σ i j (t+edgeLo σ i j) := by
  by_cases ht : 0 ≤ t
  · rw [causalFull, indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht)]
    exact rdfRecenteredHSQ_eq_actual z ρ σ i j t ht
  · have hl : t+edgeLo σ i j < edgeLo σ i j := by linarith
    simp [causalFull, ht, dpSeedQ, q, hl]

theorem rdfRecenteredHSQ_axis_laplace (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    FMSA.causalComplexLaplace (rdfRecenteredHSQ ρ σ i j) (Complex.I*k) =
      Complex.exp ((Complex.I*k)*(edgeLo σ i j : ℂ))*complexHSQ ρ σ (Complex.I*k) i j := by
  rw [← causalFull_complex_laplace]
  simp_rw [causalFull_recenteredHSQ z]
  have he := FMSA.MixtureBaxter.laplace_shift
    (fun r => (dpSeedQ z ρ σ i j r : ℂ)) (edgeLo σ i j) (Complex.I*k)
  calc
    _ = Complex.exp ((Complex.I*k)*(edgeLo σ i j : ℂ))*dpSeedFourier z ρ σ k i j := by
      simpa only [dpSeedFourier, neg_mul] using he
    _ = _ := by rw [dpSeedFourier_eq_complexHSQ z hz ρ σ hσ k hk]

theorem rdfPhase_edge_product (σ : Fin N → ℝ) (s : ℂ) (i j : Fin N) :
    Complex.exp (-s*(σ j : ℂ)/2)*Complex.exp (s*(edgeLo σ i j : ℂ)) =
      Complex.exp (-s*(σ i : ℂ)/2) := by
  rw [← Complex.exp_add]
  congr 1
  unfold edgeLo
  push_cast
  ring

theorem rdfPhase_contact_product (σ : Fin N → ℝ) (s : ℂ) (i j : Fin N) :
    Complex.exp (-s*(σ i : ℂ)/2)*Complex.exp (-s*(σ j : ℂ)/2) =
      Complex.exp (-s*(edgeHi σ i j : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  unfold edgeHi
  push_cast
  ring

theorem rdfCausalKernel_axis_laplace (ρ σ : Fin N → ℝ) (s : ℂ) (i j : Fin N) :
    rdfMatrixLaplace (rdfCausalKernel ρ σ) s i j =
      (ρ i : ℂ)*FMSA.causalComplexLaplace (rdfRecenteredHSQ ρ σ i j) s := by
  unfold rdfMatrixLaplace rdfCausalKernel FMSA.causalComplexLaplace
  simp only [Matrix.of_apply, Complex.ofReal_mul]
  rw [← integral_const_mul]
  congr 1
  funext r
  ring

theorem rdfHSLeftFactor_phase (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (k : ℝ) (hk : k ≠ 0) :
    rdfPhase σ (Complex.I*k)*complexHSLeftFactor ρ σ (Complex.I*k) =
      rdfRecenteredFactor ρ σ (Complex.I*k)*rdfPhase σ (Complex.I*k) := by
  ext i j
  simp only [rdfPhase, complexHSLeftFactor, rdfRecenteredFactor,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply]
  rw [rdfCausalKernel_axis_laplace, rdfRecenteredHSQ_axis_laplace z hz ρ σ hσ k hk]
  have he := rdfPhase_edge_product σ (Complex.I*k) i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.one_apply_eq, Matrix.diagonal_mul]
    linear_combination (ρ i : ℂ)*complexHSQ ρ σ (Complex.I*k) i i*he
  · simp only [Matrix.one_apply_ne hij, Matrix.diagonal_mul]
    linear_combination (ρ i : ℂ)*complexHSQ ρ σ (Complex.I*k) i j*he

theorem dpB_eq_causalSource_shift (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    dpB z ρ σ K i j r =
      causalShift (fun t => rdfCausalSource z ρ σ K t i j) (edgeHi σ i j) r := by
  by_cases hr : edgeHi σ i j ≤ r
  · simp [dpB, causalShift, causalFull, rdfCausalSource, hr, sub_nonneg.mpr hr]
  · simp [dpB, causalShift, causalFull, rdfCausalSource, hr,
      show ¬ 0 ≤ r-edgeHi σ i j from fun h => hr (sub_nonneg.mp h)]

theorem dpBFourier_eq_causalSource_phase (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (k : ℝ) :
    Matrix.of (dpBFourier z ρ σ K k) =
      rdfPhase σ (Complex.I*k)*rdfMatrixLaplace (rdfCausalSource z ρ σ K) (Complex.I*k)*
        rdfPhase σ (Complex.I*k) := by
  ext i j
  simp only [rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, rdfMatrixLaplace]
  unfold dpBFourier
  simp_rw [dpB_eq_causalSource_shift]
  rw [causalShift_complex_laplace]
  rw [show Complex.exp (-((Complex.I*(k : ℂ)))*(edgeHi σ i j : ℂ)) =
      Complex.exp (-(Complex.I*k)*(σ i : ℂ)/2)*Complex.exp (-(Complex.I*k)*(σ j : ℂ)/2)
      from (rdfPhase_contact_product σ (Complex.I*k) i j).symm]
  ring

end FMSA.ExactMSA.MultiTailMixture
