import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPFirstOrderRadial
import LeanCode.HSMixture.MixtureOzStar

/-! Actual two-sided causal Volterra construction for the first-order RDF.
Support is constructed, not inferred from a formal inverse. Full-axis decay
and the actual radial OZ identification are separate analytic obligations. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfRecenteredHSQ (ρ σ : Fin N → ℝ) (i j : Fin N) (t : ℝ) : ℝ :=
  Q0phys ρ σ i j*(min t (σ i)-σ i)+Qppphys ρ σ j j/2*(min t (σ i)-σ i)^2

theorem rdfRecenteredHSQ_continuous (ρ σ : Fin N → ℝ) (i j : Fin N) :
    Continuous (rdfRecenteredHSQ ρ σ i j) := by unfold rdfRecenteredHSQ; fun_prop

theorem rdfRecenteredHSQ_eq_actual (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (i j : Fin N) (t : ℝ) (ht : 0 ≤ t) :
    rdfRecenteredHSQ ρ σ i j t = dpSeedQ z ρ σ i j (t+edgeLo σ i j) := by
  have hl : ¬ t+edgeLo σ i j < edgeLo σ i j := by linarith
  have he : t+edgeLo σ i j-edgeHi σ i j = t-σ i := by unfold edgeLo edgeHi; ring
  by_cases hh : t ≤ σ i
  · have hr : t+edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith
    simp [rdfRecenteredHSQ, dpSeedQ, q, hl, hr, he, min_eq_left hh,
      W, C, Wt, Ct]
  · have hr : ¬ t+edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith
    simp [rdfRecenteredHSQ, dpSeedQ, q, hl, hr, min_eq_right (not_le.mp hh).le,
      W, C, Wt, Ct]

def rdfCausalKernel (ρ σ : Fin N → ℝ) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => ρ i*rdfRecenteredHSQ ρ σ i j t)

theorem rdfCausalKernel_continuous (ρ σ : Fin N → ℝ) : Continuous (rdfCausalKernel ρ σ) :=
  continuous_matrix (fun i j => (rdfRecenteredHSQ_continuous ρ σ i j).const_mul (ρ i))

def rdfCausalSource (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => ∑ u, dpBareAmplitude z ρ σ K u i j*exp (-z u*t))

theorem rdfCausalSource_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    Continuous (rdfCausalSource z ρ σ K) := by unfold rdfCausalSource; fun_prop

theorem rdfCausalKernelTranspose_continuous (ρ σ : Fin N → ℝ) :
    Continuous (fun t => (rdfCausalKernel ρ σ t).transpose) :=
  continuous_matrix (fun i j => (rdfCausalKernel_continuous ρ σ).matrix_elem j i)

def rdfCausalLeft (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    ℝ → Matrix (Fin N) (Fin N) ℝ :=
  FMSA.MixtureOzStar.matBaxterPsiOuterFun 0
    (fun t => (rdfCausalKernel ρ σ t).transpose) (rdfCausalSource z ρ σ K)
    (rdfCausalKernelTranspose_continuous ρ σ) (rdfCausalSource_continuous z ρ σ K)

theorem rdfCausalLeft_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    Continuous (rdfCausalLeft z ρ σ K) :=
  FMSA.MixtureOzStar.matBaxterPsiOuterFun_continuous 0 _ _ _ _

theorem rdfCausalLeftTranspose_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    Continuous (fun t => (rdfCausalLeft z ρ σ K t).transpose) :=
  continuous_matrix (fun i j => (rdfCausalLeft_continuous z ρ σ K).matrix_elem j i)

def rdfCausalRightTranspose (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    ℝ → Matrix (Fin N) (Fin N) ℝ :=
  FMSA.MixtureOzStar.matBaxterPsiOuterFun 0
    (fun t => (rdfCausalKernel ρ σ t).transpose)
    (fun t => (rdfCausalLeft z ρ σ K t).transpose)
    (rdfCausalKernelTranspose_continuous ρ σ) (rdfCausalLeftTranspose_continuous z ρ σ K)

def rdfCausalTwoSided (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (t : ℝ) : Matrix (Fin N) (Fin N) ℝ := (rdfCausalRightTranspose z ρ σ K t).transpose

theorem rdfCausalTwoSided_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    Continuous (rdfCausalTwoSided z ρ σ K) :=
  continuous_matrix (fun i j =>
    (FMSA.MixtureOzStar.matBaxterPsiOuterFun_continuous 0 _ _ _ _).matrix_elem j i)

theorem rdfCausalLeft_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    rdfCausalLeft z ρ σ K r i j = rdfCausalSource z ρ σ K r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, rdfCausalKernel ρ σ (r-t) m i*rdfCausalLeft z ρ σ K t m j := by
  exact FMSA.MixtureOzStar.matBaxterPsiOuter_matRenewalEq 0 _ _ _ _ i j r hr

theorem rdfCausalTwoSided_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    rdfCausalTwoSided z ρ σ K r i j = rdfCausalLeft z ρ σ K r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, rdfCausalTwoSided z ρ σ K t i m*rdfCausalKernel ρ σ (r-t) m j := by
  have he := FMSA.MixtureOzStar.matBaxterPsiOuter_matRenewalEq 0
    (fun t => (rdfCausalKernel ρ σ t).transpose)
    (fun t => (rdfCausalLeft z ρ σ K t).transpose)
    (rdfCausalKernelTranspose_continuous ρ σ) (rdfCausalLeftTranspose_continuous z ρ σ K) j i r hr
  change rdfCausalRightTranspose z ρ σ K r j i =
    rdfCausalLeft z ρ σ K r i j+∑ m, ∫ t in (0 : ℝ)..r,
      rdfCausalKernel ρ σ (r-t) m j*rdfCausalRightTranspose z ρ σ K t m i at he
  simpa only [rdfCausalTwoSided, Matrix.transpose_apply, mul_comm] using he

/-- The causal support shift uses the actual additive pair contact. -/
def rdfFirstOrderCausal (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  (Ici (edgeHi σ i j)).indicator
    (fun r => rdfCausalTwoSided z ρ σ K (r-edgeHi σ i j) i j/(2*π*r)) r

theorem rdfFirstOrderCausal_hardcore (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : r < edgeHi σ i j) : rdfFirstOrderCausal z ρ σ K i j r = 0 :=
  indicator_of_notMem (not_le.mpr hr) _

end FMSA.ExactMSA.MultiTailMixture
