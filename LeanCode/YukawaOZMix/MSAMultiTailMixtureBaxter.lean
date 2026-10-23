import LeanCode.YukawaOZMix.MSAMixtureBreakpointConvDirect
import LeanCode.YukawaOZ.MSAMultiTailIntegrals

/-!
# Real-space Baxter convolution for arbitrary finite tails and species

The species and tail index types are separate. Unequal diameters retain the
same support edges and contact junctions for every tail. This module extends
the real-space definitions and their integrability; it does not discharge the
remaining single-tail matrix Fourier-closure axioms by assuming their analogues.
-/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTailMixture

open MSAMixture
open FMSA.ExactMSA.Breakpoint

variable {N : ℕ} {ι : Type*} [Fintype ι]

def q (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : ι → Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  if r < edgeLo σ i j then 0 else if r ≤ edgeHi σ i j then
    qp i j * (r - edgeHi σ i j) + A j / 2 * (r - edgeHi σ i j) ^ 2 +
      ∑ t, (W t i j * exp (-z t * (r - edgeLo σ i j)) + C t i j)
  else ∑ t, (W t i j * exp (-z t * (r - edgeLo σ i j)) +
    C t i j * exp (-z t * (r - edgeHi σ i j)))

def qPrime (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : ι → Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  if r < edgeLo σ i j then 0 else if r ≤ edgeHi σ i j then
    qp i j + A j * (r - edgeHi σ i j) -
      ∑ t, z t * W t i j * exp (-z t * (r - edgeLo σ i j))
  else ∑ t, (-z t * W t i j * exp (-z t * (r - edgeLo σ i j)) -
    z t * C t i j * exp (-z t * (r - edgeHi σ i j)))

/-- Ordered real-space convolution relation. For the whole positive core,
the larger-diameter species must be the row (as in the existing unequal-core theorem).
The reciprocal entry is obtained by exchange of species indices. -/
def correlation (z : ι → ℝ) (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : ι → Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  (-qPrime z σ A qp W C i j r + ∑ l, ρ l * ∫ t : ℝ,
    qPrime z σ A qp W C i l (t + r) * q z σ A qp W C j l t) / (2 * π * r)

private theorem edge_shift (σ : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    r - edgeLo σ i j - σ i = r - edgeHi σ i j := by
  unfold edgeLo edgeHi
  ring

/-- A compact polynomial part plus a finite sum of the existing one-tail Baxter functions. -/
theorem q_decomposition (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : ι → Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    q z σ A qp W C i j r = baxterQ 1 σ A qp (fun _ _ => 0) (fun _ _ => 0) i j r +
      ∑ t, baxterQ (z t) σ (fun _ => 0) (fun _ _ => 0) (W t) (C t) i j r := by
  unfold q baxterQ
  split_ifs <;> simp [edge_shift]

theorem qPrime_decomposition (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : ι → Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    qPrime z σ A qp W C i j r = baxterQ' 1 σ A qp (fun _ _ => 0) (fun _ _ => 0) i j r +
      ∑ t, baxterQ' (z t) σ (fun _ => 0) (fun _ _ => 0) (W t) (C t) i j r := by
  unfold qPrime baxterQ'
  split_ifs <;> (try simp only [edge_shift]) <;>
    simp [Finset.sum_neg_distrib, sub_eq_add_neg]

theorem q_integrable (z : ι → ℝ) (hz : ∀ t, 0 < z t) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : ι → Fin N → Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) : Integrable (q z σ A qp W C i j) := by
  simp_rw [show q z σ A qp W C i j =
    (fun r => baxterQ 1 σ A qp (fun _ _ => 0) (fun _ _ => 0) i j r +
      ∑ t, baxterQ (z t) σ (fun _ => 0) (fun _ _ => 0) (W t) (C t) i j r) from
        funext (q_decomposition z σ A qp W C i j)]
  apply Integrable.add (baxterQ_integrable 1 one_pos σ A qp _ _ i j hσ)
  apply integrable_finsetSum
  intro t _
  exact baxterQ_integrable (z t) (hz t) σ _ _ (W t) (C t) i j hσ

/-- Mixed-rate convolution products are integrable, including repeated rates. -/
theorem crossRate_convolution_integrable (z w : ℝ) (hz : 0 < z) (hw : 0 < w)
    (σ A B : Fin N → ℝ) (qp qp' W C V D : Fin N → Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (r : ℝ) :
    Integrable (fun t => baxterQ' z σ A qp W C i l (t + r) *
      baxterQ w σ B qp' V D j l t) := by
  obtain ⟨M, hM⟩ := baxterQ'_bounded z hz σ A qp W C i l hσ
  exact (baxterQ_integrable w hw σ B qp' V D j l hσ).bdd_mul
    ((baxterQ'_measurable z σ A qp W C i l).comp (measurable_id.add_const r)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hM (t + r)))

/-- The finite-tail real-space convolution is a well-defined Lebesgue integral. -/
theorem convolution_integrable (z : ι → ℝ) (hz : ∀ t, 0 < z t)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : ι → Fin N → Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (r : ℝ) :
    Integrable (fun t => qPrime z σ A qp W C i l (t + r) * q z σ A qp W C j l t) := by
  simp_rw [qPrime_decomposition, q_decomposition, mul_add, add_mul, Finset.sum_mul, Finset.mul_sum]
  apply Integrable.add
  · apply Integrable.add
    · exact crossRate_convolution_integrable 1 1 one_pos one_pos σ A A qp qp
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) hσ i j l r
    · apply integrable_finsetSum
      intro t _
      exact crossRate_convolution_integrable (z t) 1 (hz t) one_pos σ (fun _ => 0) A
        (fun _ _ => 0) qp (W t) (C t) (fun _ _ => 0) (fun _ _ => 0) hσ i j l r
  · apply Integrable.add
    · apply integrable_finsetSum
      intro t _
      exact crossRate_convolution_integrable 1 (z t) one_pos (hz t) σ A (fun _ => 0)
        qp (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (W t) (C t) hσ i j l r
    · apply integrable_finsetSum
      intro u _
      apply integrable_finsetSum
      intro t _
      exact crossRate_convolution_integrable (z u) (z t) (hz u) (hz t) σ (fun _ => 0) (fun _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (W u) (C u) (W t) (C t) hσ i j l r

end FMSA.ExactMSA.MultiTailMixture
