import LeanCode.YukawaOZMix.MSAMultiTailMixtureFirstOrder
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitiveExterior

/-! Actual finite basis for Q and its ordinary derivative. The exact convolution
is a quadratic finite expression in the amplitudes, so coupling differentiation
requires no unproved interchange of an improper integral and a derivative. -/
noncomputable section
open MeasureTheory Set Real
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

abbrev BasisIndex (ι : Type*) := Fin 2 ⊕ (ι ⊕ ι)

def basisRate (z : ι → ℝ) : BasisIndex ι → ℝ
  | .inl _ => 1
  | .inr (.inl u) => z u
  | .inr (.inr u) => z u

def basisA : BasisIndex ι → ℝ
  | .inl b => if b = 1 then 1 else 0
  | .inr _ => 0

def basisQp : BasisIndex ι → ℝ
  | .inl b => if b = 0 then 1 else 0
  | .inr _ => 0

def basisW : BasisIndex ι → ℝ
  | .inr (.inl _) => 1
  | _ => 0

def basisC : BasisIndex ι → ℝ
  | .inr (.inr _) => 1
  | _ => 0

def basisQ (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι) (i j : Fin N) (r : ℝ) : ℝ :=
  baxterQ (basisRate z b) σ (fun _ => basisA b) (fun _ _ => basisQp b)
    (fun _ _ => basisW b) (fun _ _ => basisC b) i j r

def basisPrime (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι) (i j : Fin N) (r : ℝ) : ℝ :=
  baxterQ' (basisRate z b) σ (fun _ => basisA b) (fun _ _ => basisQp b)
    (fun _ _ => basisW b) (fun _ _ => basisC b) i j r

def coefficient (A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (i j : Fin N) : BasisIndex ι → ℝ
  | .inl b => if b = 0 then qp i j else A j
  | .inr (.inl u) => W u i j
  | .inr (.inr u) => C u i j

theorem basisRate_pos (z : ι → ℝ) (hz : ∀ u, 0 < z u) (b : BasisIndex ι) :
    0 < basisRate z b := by
  rcases b with b | (u | u) <;> simp [basisRate, hz]

theorem q_eq_basis (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    q z σ A qp W C i j r = ∑ b : BasisIndex ι, coefficient A qp W C i j b * basisQ z σ b i j r := by
  have he : r - edgeLo σ i j - σ i = r - edgeHi σ i j := by unfold edgeLo edgeHi; ring
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, coefficient, basisQ, basisRate,
    basisA, basisQp, basisW, basisC]
  unfold q baxterQ
  simp only [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    if_true, if_false]
  split_ifs <;> simp [he, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc] <;> ring

theorem qPrime_eq_basis (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    qPrime z σ A qp W C i j r = ∑ b : BasisIndex ι, coefficient A qp W C i j b * basisPrime z σ b i j r := by
  have he : r - edgeLo σ i j - σ i = r - edgeHi σ i j := by unfold edgeLo edgeHi; ring
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, coefficient, basisPrime, basisRate,
    basisA, basisQp, basisW, basisC]
  unfold qPrime baxterQ'
  simp only [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    if_true, if_false]
  split_ifs <;> simp [he, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    mul_comm, mul_left_comm, mul_assoc] <;> ring

def basisConvolution (z : ι → ℝ) (σ : Fin N → ℝ) (b c : BasisIndex ι)
    (i j l : Fin N) (r : ℝ) : ℝ :=
  ∫ t : ℝ, basisPrime z σ b i l (t+r) * basisQ z σ c j l t

theorem basisConvolution_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (b c : BasisIndex ι) (i j l : Fin N) (r : ℝ) :
    Integrable (fun t => basisPrime z σ b i l (t+r) * basisQ z σ c j l t) :=
  crossRate_convolution_integrable _ _ (basisRate_pos z hz b) (basisRate_pos z hz c)
    σ _ _ _ _ _ _ _ _ hσ i j l r

/-- Actual improper convolution equals the finite amplitude quadratic. -/
theorem convolution_eq_basis (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (r : ℝ) :
    (∫ t : ℝ, qPrime z σ A qp W C i l (t+r) * q z σ A qp W C j l t) =
      ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
        (coefficient A qp W C i l b * coefficient A qp W C j l c) *
          basisConvolution z σ b c i j l r := by
  have he : (fun t => qPrime z σ A qp W C i l (t+r) * q z σ A qp W C j l t) =
      (fun t => ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
        (coefficient A qp W C i l b * coefficient A qp W C j l c) *
          (basisPrime z σ b i l (t+r) * basisQ z σ c j l t)) := by
    funext t
    rw [qPrime_eq_basis, q_eq_basis, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hi : ∀ b c : BasisIndex ι, Integrable (fun t =>
      (coefficient A qp W C i l b * coefficient A qp W C j l c) *
        (basisPrime z σ b i l (t+r) * basisQ z σ c j l t)) :=
    fun b c => (basisConvolution_integrable z hz σ hσ b c i j l r).const_mul _
  rw [he, integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hi b c))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun c _ => hi b c)]
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_const_mul]
  rfl

def bhCoefficient (z : ι → ℝ) (ρ σ : Fin N → ℝ) (p : TailMatrix ι N × TailMatrix ι N)
    (i j : Fin N) (b : BasisIndex ι) : ℝ :=
  coefficient (amplitudeA z ρ σ p.1 p.2) (amplitudeQp z ρ σ p.1 p.2)
    (W z ρ p.1 p.2) (C z ρ σ p.1 p.2) i j b

@[fun_prop] theorem bhCoefficient_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (i j : Fin N) (b : BasisIndex ι) :
    ContDiff ℝ ∞ (fun p => bhCoefficient z ρ σ p i j b) := by
  rcases b with b | (u | u)
  · fin_cases b <;> simp only [bhCoefficient, coefficient, Fin.isValue, if_true, if_false]
    · exact amplitudeQp_contDiff z ρ σ i j
    · exact amplitudeA_contDiff z ρ σ j
  · exact W_contDiff z ρ u i j
  · exact C_contDiff z ρ σ u i j

theorem correlation_eq_basis (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (p : TailMatrix ι N × TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    correlation z ρ σ (amplitudeA z ρ σ p.1 p.2) (amplitudeQp z ρ σ p.1 p.2)
      (W z ρ p.1 p.2) (C z ρ σ p.1 p.2) i j r =
    (-(∑ b : BasisIndex ι, bhCoefficient z ρ σ p i j b * basisPrime z σ b i j r) +
      ∑ l, ρ l * ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
        (bhCoefficient z ρ σ p i l b * bhCoefficient z ρ σ p j l c) *
          basisConvolution z σ b c i j l r) / (2*π*r) := by
  unfold correlation
  simp_rw [convolution_eq_basis z hz σ _ _ _ _ hσ i j _ r, qPrime_eq_basis]
  rfl

/-- Coupling smoothness of the actual convolution-defined DCF at each fixed r,
including inner-core breakpoints. No differentiating under the integral is used. -/
theorem correlation_contDiff_amplitudes (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => correlation z ρ σ
      (amplitudeA z ρ σ p.1 p.2) (amplitudeQp z ρ σ p.1 p.2)
      (W z ρ p.1 p.2) (C z ρ σ p.1 p.2) i j r) := by
  simp_rw [correlation_eq_basis z hz ρ σ hσ]
  change ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N =>
    (-(∑ b : BasisIndex ι, bhCoefficient z ρ σ p i j b * basisPrime z σ b i j r) +
      ∑ l, ρ l * ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
        (bhCoefficient z ρ σ p i l b * bhCoefficient z ρ σ p j l c) *
          basisConvolution z σ b c i j l r) / (2*π*r))
  fun_prop

end FMSA.ExactMSA.MultiTailMixture
