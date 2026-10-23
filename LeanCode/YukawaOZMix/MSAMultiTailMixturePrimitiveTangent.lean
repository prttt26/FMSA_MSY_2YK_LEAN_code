import LeanCode.YukawaOZMix.MSAMultiTailMixtureLinearized
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRegularity
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitive
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitiveExterior

/-! The first variation of the actual full-line primitive, including every
finite-core position. Finite fixed kernel integrals supply differentiability;
no differentiation-under-an-improper-integral premise is retained. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem q_bounded (z : ι → ℝ) (hz : ∀ u, 0 < z u) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    ∃ M : ℝ, ∀ r, |q z σ A qp W C i j r| ≤ M := by
  obtain ⟨M, hM⟩ := qRight_bounded z hz σ A qp W C hσ i j
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨M, fun r => ?_⟩
  by_cases hr : r < edgeLo σ i j
  · simpa only [q, if_pos hr, abs_zero] using hM0
  · rw [← qRight_eq_q z σ A qp W C i j r (le_of_not_gt hr)]
    exact hM r

theorem basisQ_eq_single_q (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι)
    (i j : Fin N) (r : ℝ) :
    basisQ z σ b i j r =
      q (fun _ : Fin 1 => basisRate z b) σ (fun _ => basisA b) (fun _ _ => basisQp b)
        (fun _ _ _ => basisW b) (fun _ _ _ => basisC b) i j r := by
  have he : r-edgeLo σ i j-σ i = r-edgeHi σ i j := by unfold edgeLo edgeHi; ring
  simp only [basisQ, baxterQ, q, Fin.sum_univ_one, he, add_assoc]

theorem basisQ_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u) (σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (b : BasisIndex ι) (i j : Fin N) :
    Integrable (basisQ z σ b i j) :=
  baxterQ_integrable _ (basisRate_pos z hz b) σ _ _ _ _ i j hσ

theorem basisQ_bounded (z : ι → ℝ) (hz : ∀ u, 0 < z u) (σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (b : BasisIndex ι) (i j : Fin N) :
    ∃ M : ℝ, ∀ r, |basisQ z σ b i j r| ≤ M := by
  simpa only [basisQ_eq_single_q] using
    q_bounded (fun _ : Fin 1 => basisRate z b) (fun _ => basisRate_pos z hz b) σ
      (fun _ => basisA b) (fun _ _ => basisQp b) (fun _ _ _ => basisW b)
      (fun _ _ _ => basisC b) hσ i j

def basisQQ (z : ι → ℝ) (σ : Fin N → ℝ) (b c : BasisIndex ι)
    (i j l : Fin N) (r : ℝ) : ℝ :=
  ∫ t : ℝ, basisQ z σ b i l t * basisQ z σ c j l (t-r)

theorem basisQQ_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u) (σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (b c : BasisIndex ι) (i j l : Fin N) (r : ℝ) :
    Integrable (fun t => basisQ z σ b i l t * basisQ z σ c j l (t-r)) := by
  obtain ⟨M, hM⟩ := basisQ_bounded z hz σ hσ c j l
  have hm : AEStronglyMeasurable (fun t => basisQ z σ c j l (t-r)) := by
    have h := (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) (-r)).integrable_comp_of_integrable
      (basisQ_integrable z hz σ hσ c j l)
    simpa only [Function.comp_def, sub_eq_add_neg] using h.aestronglyMeasurable
  exact (basisQ_integrable z hz σ hσ b i l).mul_bdd hm
    (Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hM (t-r)))

theorem realQCrossCorr_eq_basis (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (r : ℝ) :
    (∫ t : ℝ, q z σ A qp W C i l t * q z σ A qp W C j l (t-r)) =
      ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
        (coefficient A qp W C i l b * coefficient A qp W C j l c) * basisQQ z σ b c i j l r := by
  have he : (fun t => q z σ A qp W C i l t * q z σ A qp W C j l (t-r)) =
      (fun t => ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
        (coefficient A qp W C i l b * coefficient A qp W C j l c) *
          (basisQ z σ b i l t * basisQ z σ c j l (t-r))) := by
    funext t
    rw [q_eq_basis, q_eq_basis, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have hi : ∀ b c : BasisIndex ι, Integrable (fun t =>
      (coefficient A qp W C i l b * coefficient A qp W C j l c) *
        (basisQ z σ b i l t * basisQ z σ c j l (t-r))) :=
    fun b c => (basisQQ_integrable z hz σ hσ b c i j l r).const_mul _
  rw [he, integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hi b c))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_finsetSum _ (fun c _ => hi b c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [integral_const_mul]
  rfl

theorem qCrossCorr_eq_ofReal (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j l : Fin N) (r : ℝ) :
    qCrossCorr z σ A qp W C i j l r =
      Complex.ofReal (∫ t : ℝ, q z σ A qp W C i l t * q z σ A qp W C j l (t-r)) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae (Eventually.of_forall _)
  intro t
  push_cast
  rfl

def primitiveBasisReal (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (p : TailMatrix ι N × TailMatrix ι N) (i j : Fin N) (r : ℝ) : ℝ :=
  (∑ b : BasisIndex ι, bhCoefficient z ρ σ p i j b * basisQ z σ b i j r) +
    (∑ b : BasisIndex ι, bhCoefficient z ρ σ p j i b * basisQ z σ b j i (-r)) -
    ∑ l, ρ l * ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
      (bhCoefficient z ρ σ p i l b * bhCoefficient z ρ σ p j l c) * basisQQ z σ b c i j l r

theorem baxterPrimitive_eq_basis (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (p : TailMatrix ι N × TailMatrix ι N)
    (i j : Fin N) (r : ℝ) :
    baxterPrimitive z ρ σ (amplitudeA z ρ σ p.1 p.2) (amplitudeQp z ρ σ p.1 p.2)
      (W z ρ p.1 p.2) (C z ρ σ p.1 p.2) i j r =
      Complex.ofReal (primitiveBasisReal z ρ σ p i j r) := by
  simp only [baxterPrimitive, qCrossCorr_eq_ofReal]
  simp only [realQCrossCorr_eq_basis z hz σ _ _ _ _ hσ]
  simp only [q_eq_basis, primitiveBasisReal, bhCoefficient]
  push_cast
  rfl

/-- Explicit full-space first variation with fixed basis correlations. -/
def linearizedPrimitiveReal (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  (∑ b : BasisIndex ι, coefficientSlope z ρ σ D G0 i j b * basisQ z σ b i j r) +
    (∑ b : BasisIndex ι, coefficientSlope z ρ σ D G0 j i b * basisQ z σ b j i (-r)) -
    ∑ l, ρ l * ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
      (coefficientSlope z ρ σ D G0 i l b * bhCoefficient z ρ σ (0, G0) j l c +
        bhCoefficient z ρ σ (0, G0) i l b * coefficientSlope z ρ σ D G0 j l c) *
          basisQQ z σ b c i j l r

theorem primitiveBasisReal_hasDerivAt_seed (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G0 : TailMatrix ι N) (ψ : ℝ → TailMatrix ι N × TailMatrix ι N)
    (d : TailMatrix ι N × TailMatrix ι N) (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0)
    (i j : Fin N) (r : ℝ) :
    HasDerivAt (fun τ => primitiveBasisReal z ρ σ (ψ τ) i j r)
      (linearizedPrimitiveReal z ρ σ d.1 G0 i j r) 0 := by
  have hb := bhCoefficient_hasDerivAt_seed z ρ σ G0 ψ d h0 hd
  have hlin (a b : Fin N) (x : ℝ) := HasDerivAt.fun_sum (u := Finset.univ)
    (fun c _ => (hb a b c).mul_const (basisQ z σ c a b x))
  have hp : ∀ l (b c : BasisIndex ι), HasDerivAt (fun τ =>
      (bhCoefficient z ρ σ (ψ τ) i l b * bhCoefficient z ρ σ (ψ τ) j l c) *
        basisQQ z σ b c i j l r)
      ((coefficientSlope z ρ σ d.1 G0 i l b * bhCoefficient z ρ σ (0, G0) j l c +
        bhCoefficient z ρ σ (0, G0) i l b * coefficientSlope z ρ σ d.1 G0 j l c) *
          basisQQ z σ b c i j l r) 0 := by
    intro l b c
    convert! ((hb i l b).mul (hb j l c)).mul_const (basisQQ z σ b c i j l r) using 1 <;>
      simp only [h0, Pi.mul_apply]
  have hprod := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun c _ => hp l b c))).const_mul (ρ l))
  exact ((hlin i j r).add (hlin j i (-r))).sub hprod

theorem baxterPrimitive_hasDerivAt_seed (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (i j : Fin N) (r : ℝ) :
    HasDerivAt (fun τ => baxterPrimitive z ρ σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
      (Complex.ofReal (linearizedPrimitiveReal z ρ σ d.1 G0 i j r)) 0 := by
  have h := primitiveBasisReal_hasDerivAt_seed z ρ σ G0 ψ d h0 hd i j r
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 h
  convert! hc using 1
  funext τ
  exact baxterPrimitive_eq_basis z hz ρ σ hσ (ψ τ) i j r

/-- The actual smooth BH family and its full-space primitive tangent are
constructed internally, for arbitrary finite species and labelled tails. -/
theorem exists_contDiffAt_root_with_linearizedPrimitive (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      ∀ i j r, HasDerivAt (fun τ => baxterPrimitive z ρ σ
        (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
        (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
        (Complex.ofReal (linearizedPrimitiveReal z ρ σ
          (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r)) 0 := by
  obtain ⟨ψ, h0, hr, hc⟩ := exists_contDiffAt_root z ρ σ K hz hvac hρ hσ
  have hd := (hc.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
  have hs := firstOrderDt_eq_of_family z ρ σ K hz hvac hρ hσ ψ _ h0 hr hd
  refine ⟨ψ, h0, hr, hc, fun i j r => ?_⟩
  have hp := baxterPrimitive_hasDerivAt_seed z hz ρ σ (fun i => (hσ i).le)
    (baseSeed z ρ σ) ψ _ h0 hd i j r
  rw [hs] at hp
  exact hp

theorem linearizedPrimitiveReal_reflection (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) :
    linearizedPrimitiveReal z ρ σ D G0 j i (-r) =
      linearizedPrimitiveReal z ρ σ D G0 i j r := by
  let ψ : ℝ → TailMatrix ι N × TailMatrix ι N := fun τ => (τ • D, G0)
  have hd : HasDerivAt ψ (D, 0) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const D).prodMk
      (hasDerivAt_const (0 : ℝ) G0) using 1 <;> simp only [ψ, one_smul, id_eq]
  have h0 : ψ 0 = (0, G0) := by simp [ψ]
  have hi := baxterPrimitive_hasDerivAt_seed z hz ρ σ hσ G0 ψ (D, 0) h0 hd j i (-r)
  have hj := baxterPrimitive_hasDerivAt_seed z hz ρ σ hσ G0 ψ (D, 0) h0 hd i j r
  have he : (fun τ => baxterPrimitive z ρ σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) j i (-r)) =
      (fun τ => baxterPrimitive z ρ σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) i j r) := by
    funext τ
    exact baxterPrimitive_reflection z ρ σ _ _ _ _ i j r
  rw [he] at hi
  exact_mod_cast hi.unique hj

theorem baxterPrimitive_exterior_hasDerivAt_of_family (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N)
    (hroot : ∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    HasDerivAt (fun τ => baxterPrimitive z ρ σ (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2)
      (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2) (W z ρ (ψ τ).1 (ψ τ).2)
      (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
      (Complex.ofReal (∑ u, 2*π*K u i j/z u*exp (-z u*(r-edgeHi σ i j)))) 0 := by
  let tail : ℝ := ∑ u, 2*π*K u i j/z u*exp (-z u*(r-edgeHi σ i j))
  have hd : HasDerivAt (fun τ : ℝ => Complex.ofReal (τ * tail)) (Complex.ofReal tail) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const tail).ofReal_comp
  apply hd.congr_of_eventuallyEq
  filter_upwards [hroot] with τ hτ
  rw [baxterPrimitive_exterior_of_root z hz ρ σ (τ • K) (ψ τ).1 (ψ τ).2 hσ hτ i j r hr]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem linearizedPrimitiveReal_exterior (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r =
      ∑ u, 2*π*K u i j/z u*exp (-z u*(r-edgeHi σ i j)) := by
  obtain ⟨ψ, h0, hroot, hc, hp⟩ := exists_contDiffAt_root_with_linearizedPrimitive z ρ σ K hz hvac hρ hσ
  exact_mod_cast (hp i j r).unique
    (baxterPrimitive_exterior_hasDerivAt_of_family z hz ρ σ K (fun i => (hσ i).le) ψ hroot i j r hr)

end FMSA.ExactMSA.MultiTailMixture
