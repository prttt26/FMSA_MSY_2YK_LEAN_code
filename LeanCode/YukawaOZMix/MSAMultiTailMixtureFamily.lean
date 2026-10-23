import LeanCode.YukawaOZMix.MSAMultiTailMixtureSystem
import LeanCode.Closures.MSASolutionFamily

/-! Local smooth roots of the actual finite-tail, unequal-diameter mixture BH system. -/
noncomputable section
open Real Filter Topology Set MSAMixture FMSA.MatrixQ0
open scoped BigOperators ContDiff

namespace FMSA.ExactMSA.MultiTailMixture

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- Right multiplication independently in each tail block, with the entrywise product norm. -/
def entry (u : ι) (i j : Fin N) : TailMatrix ι N →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.proj i : (Fin N → Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).comp
      (ContinuousLinearMap.proj u : TailMatrix ι N →L[ℝ] (Fin N → Fin N → ℝ)))

def rightBlock (B : TailMatrix ι N) : TailMatrix ι N →L[ℝ] TailMatrix ι N :=
  ContinuousLinearMap.pi (fun u => ContinuousLinearMap.pi (fun i =>
    ContinuousLinearMap.pi (fun j => ∑ l, B u l j • entry u i l)))

@[simp] theorem rightBlock_apply (B p : TailMatrix ι N) (u : ι) (i j : Fin N) :
    rightBlock B p u i j = ∑ l, p u i l * B u l j := by
  simp [rightBlock, entry, mul_comm]

theorem rightBlock_matrix (B p : TailMatrix ι N) (u : ι) :
    rightBlock B p u = Matrix.of (p u) * Matrix.of (B u) := by
  ext i j
  simp [Matrix.mul_apply]

def inverseBlocks (B : TailMatrix ι N) : TailMatrix ι N := fun u =>
  @Inv.inv (Matrix (Fin N) (Fin N) ℝ) Matrix.inv (Matrix.of (B u))

theorem rightBlock_left_inverse (B : TailMatrix ι N)
    (hB : ∀ u, IsUnit (Matrix.det (B u))) (p : TailMatrix ι N) :
    rightBlock (inverseBlocks B) (rightBlock B p) = p := by
  funext u
  rw [rightBlock_matrix, rightBlock_matrix]
  change (Matrix.of (p u) * Matrix.of (B u)) * (Matrix.of (B u))⁻¹ = Matrix.of (p u)
  exact Matrix.mul_nonsing_inv_cancel_right _ _ (hB u)

theorem rightBlock_right_inverse (B : TailMatrix ι N)
    (hB : ∀ u, IsUnit (Matrix.det (B u))) (p : TailMatrix ι N) :
    rightBlock B (rightBlock (inverseBlocks B) p) = p := by
  funext u
  rw [rightBlock_matrix, rightBlock_matrix]
  change (Matrix.of (p u) * (Matrix.of (B u))⁻¹) * Matrix.of (B u) = Matrix.of (p u)
  exact Matrix.nonsing_inv_mul_cancel_right _ _ (hB u)

def triangular (B H : TailMatrix ι N) (J : TailMatrix ι N →L[ℝ] TailMatrix ι N) :
    (TailMatrix ι N × TailMatrix ι N) →L[ℝ] (TailMatrix ι N × TailMatrix ι N) :=
  ((rightBlock B).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (J.comp (ContinuousLinearMap.fst ℝ _ _) +
      (2 * π) • (rightBlock H).comp (ContinuousLinearMap.snd ℝ _ _))

def triangularInverse (B H : TailMatrix ι N) (J : TailMatrix ι N →L[ℝ] TailMatrix ι N) :
    (TailMatrix ι N × TailMatrix ι N) →L[ℝ] (TailMatrix ι N × TailMatrix ι N) :=
  ((rightBlock (inverseBlocks B)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((2 * π)⁻¹ • (rightBlock (inverseBlocks H)).comp
      (ContinuousLinearMap.snd ℝ _ _ -
        J.comp ((rightBlock (inverseBlocks B)).comp (ContinuousLinearMap.fst ℝ _ _))))

@[simp] theorem triangular_apply (B H : TailMatrix ι N)
    (J : TailMatrix ι N →L[ℝ] TailMatrix ι N) (p : TailMatrix ι N × TailMatrix ι N) :
    triangular B H J p = (rightBlock B p.1, J p.1 + (2 * π) • rightBlock H p.2) := by
  rfl

@[simp] theorem triangularInverse_apply (B H : TailMatrix ι N)
    (J : TailMatrix ι N →L[ℝ] TailMatrix ι N) (p : TailMatrix ι N × TailMatrix ι N) :
    triangularInverse B H J p = (rightBlock (inverseBlocks B) p.1,
      (2 * π)⁻¹ • rightBlock (inverseBlocks H) (p.2 - J (rightBlock (inverseBlocks B) p.1))) := by
  rfl

theorem triangular_isInvertible (B H : TailMatrix ι N)
    (hB : ∀ u, IsUnit (Matrix.det (B u)))
    (hH : ∀ u, IsUnit (Matrix.det (H u)))
    (J : TailMatrix ι N →L[ℝ] TailMatrix ι N) : (triangular B H J).IsInvertible := by
  have hp : (2 : ℝ) * π ≠ 0 := mul_ne_zero two_ne_zero pi_ne_zero
  refine ⟨ContinuousLinearEquiv.equivOfInverse (triangular B H J) (triangularInverse B H J) ?_ ?_, rfl⟩
  · intro p
    simp only [triangular_apply, triangularInverse_apply, rightBlock_left_inverse B hB,
      add_sub_cancel_left, map_smul, rightBlock_left_inverse H hH, smul_smul,
      inv_mul_cancel₀ hp, one_smul]
  · intro p
    simp only [triangular_apply, triangularInverse_apply, rightBlock_right_inverse B hB,
      map_smul, rightBlock_right_inverse H hH, smul_smul, mul_inv_cancel₀ hp, one_smul,
      add_sub_cancel]

def hsTransform (ρ σ : Fin N → ℝ) (s : ℝ) (i j : Fin N) : ℝ :=
  exp (-s * edgeLo σ i j) *
    ((1 - s * σ i - exp (-s * σ i)) / s ^ 2 * Q0phys ρ σ i j +
      (1 - s * σ i + (s * σ i) ^ 2 / 2 - exp (-s * σ i)) / s ^ 3 * Qppphys ρ σ j j)

@[simp] theorem dressedQhat_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G : TailMatrix ι N)
    (s : ℝ) (i j : Fin N) : dressedQhat z ρ σ 0 G s i j = hsTransform ρ σ s i j := by
  simp [dressedQhat, Qhat, W, C, Wt, Ct, hsTransform]

def firstBlock (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) : TailMatrix ι N :=
  fun u l j => (if l = j then 1 else 0) -
    ρ l * exp (z u * edgeLo σ j l) * dressedQhat z ρ σ Dt G (z u) j l

def secondBlock (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) : TailMatrix ι N :=
  fun u l j => (if l = j then 1 else 0) -
    ρ l * exp (z u * edgeLo σ l j) * dressedQhat z ρ σ Dt G (z u) l j

def baseFirst (z : ι → ℝ) (ρ σ : Fin N → ℝ) : TailMatrix ι N := firstBlock z ρ σ 0 0
def baseSecond (z : ι → ℝ) (ρ σ : Fin N → ℝ) : TailMatrix ι N := secondBlock z ρ σ 0 0
def baseSource (z : ι → ℝ) (ρ σ : Fin N → ℝ) : TailMatrix ι N :=
  fun u i j => (Qppphys ρ σ j j + z u * Q0phys ρ σ i j) / (z u) ^ 2

@[simp] theorem firstBlock_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G : TailMatrix ι N) :
    firstBlock z ρ σ 0 G = baseFirst z ρ σ := by
  ext u l j
  simp [firstBlock, baseFirst]

@[simp] theorem secondBlock_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G : TailMatrix ι N) :
    secondBlock z ρ σ 0 G = baseSecond z ρ σ := by
  ext u l j
  simp [secondBlock, baseSecond]

@[simp] theorem secondRHS_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G : TailMatrix ι N)
    (u : ι) (i j : Fin N) : secondRHS z ρ σ 0 G u i j = baseSource z ρ σ u i j := by
  simp [secondRHS, baseSource, C, Ct]

theorem baseFirst_eq (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    baseFirst z ρ σ u = resGuneq (z u) ρ σ (0, 0) := by
  ext l j
  simp only [baseFirst, firstBlock, dressedQhat_zero, resGuneq, Matrix.of_apply,
    qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt]
  simp [hsTransform, qhatMixRuneq, qp0Mat, A0Vec, edgeLo, edgeHi, Qppphys]
  ring

theorem baseSecond_eq (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    baseSecond z ρ σ u = resHuneq (z u) ρ σ (0, 0) := by
  ext l j
  simp only [baseSecond, secondBlock, dressedQhat_zero, resHuneq, Matrix.of_apply,
    qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt]
  simp [hsTransform, qhatMixRuneq, qp0Mat, A0Vec, edgeLo, edgeHi, Qppphys]
  ring

@[fun_prop] theorem firstBlock_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (l j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => firstBlock z ρ σ p.1 p.2 u l j) := by
  unfold firstBlock
  fun_prop

@[fun_prop] theorem secondBlock_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (l j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => secondBlock z ρ σ p.1 p.2 u l j) := by
  unfold secondBlock
  fun_prop

/-- The actual partial derivative has separate right-multiplication blocks
for the transposed first and untransposed second BH equations. -/
theorem residual_partial_triangular (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Gbase : TailMatrix ι N) :
    let E := TailMatrix ι N
    let P := E × E
    let L := (fderiv ℝ (residual z ρ σ K) (0, (0, Gbase))).comp
      (ContinuousLinearMap.inr ℝ ℝ P)
    L = triangular (baseFirst z ρ σ) (baseSecond z ρ σ)
      ((ContinuousLinearMap.snd ℝ E E).comp
        (L.comp (ContinuousLinearMap.inl ℝ E E))) := by
  let E := TailMatrix ι N
  let P := E × E
  let p0 : P := (0, Gbase)
  let L : P →L[ℝ] P := (fderiv ℝ (residual z ρ σ K) (0, p0)).comp
    (ContinuousLinearMap.inr ℝ ℝ P)
  have hne : (∞ : ℕ∞ω) ≠ 0 := by norm_num
  have hd : HasFDerivAt (fun p : P => residual z ρ σ K (0, p)) L p0 :=
    ((residual_contDiff z ρ σ K).contDiffAt.differentiableAt hne).hasFDerivAt.comp p0
      (ContinuousLinearMap.inr ℝ ℝ P).hasFDerivAt
  have htop (u : ι) (i j : Fin N) (p : P) :
      (L p).1 u i j = rightBlock (baseFirst z ρ σ) p.1 u i j := by
    let out : P →L[ℝ] ℝ := (entry u i j).comp (ContinuousLinearMap.fst ℝ E E)
    have hout := out.hasFDerivAt.comp p0 hd
    change HasFDerivAt (fun p : P => firstLHS z ρ σ p.1 p.2 u i j - 2 * π * 0 * K u i j / z u)
      (out.comp L) p0 at hout
    simp only [mul_zero, zero_mul, zero_div, sub_zero] at hout
    have hprod (l : Fin N) :
        HasFDerivAt (fun p : P => p.1 u i l * firstBlock z ρ σ p.1 p.2 u l j)
          (baseFirst z ρ σ u l j • ((entry u i l).comp (ContinuousLinearMap.fst ℝ E E))) p0 := by
      let pr := (entry u i l).comp (ContinuousLinearMap.fst ℝ E E)
      have hp : HasFDerivAt (fun p : P => p.1 u i l) pr p0 := pr.hasFDerivAt
      have hf := ((firstBlock_contDiff z ρ σ u l j).contDiffAt (x := p0)).differentiableAt hne |>.hasFDerivAt
      have hh := hp.mul hf
      convert! hh using 1 <;> simp [p0, E, pr]
    have hsum := HasFDerivAt.sum (u := Finset.univ) (fun l _ => hprod l)
    rw [Finset.sum_fn] at hsum
    simp only [firstBlock] at hsum
    change HasFDerivAt (fun p : P => firstLHS z ρ σ p.1 p.2 u i j) _ p0 at hsum
    have hh := hout.unique hsum
    have he := congrArg (fun f : P →L[ℝ] ℝ => f p) hh
    simpa [out, entry, rightBlock, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst,
      LinearMap.fst, mul_comm] using he
  have hG : L.comp (ContinuousLinearMap.inr ℝ E E) =
      (0 : E →L[ℝ] E).prod ((2 * π) • rightBlock (baseSecond z ρ σ)) := by
    have hdg := hd.comp Gbase (ContinuousLinearMap.inr ℝ E E).hasFDerivAt
    change HasFDerivAt (fun g : E => residual z ρ σ K (0, (0, g))) _ Gbase at hdg
    have he : (fun g : E => residual z ρ σ K (0, (0, g))) =
        (fun g => (0, (2 * π) • rightBlock (baseSecond z ρ σ) g - baseSource z ρ σ)) := by
      funext g
      apply Prod.ext <;> funext u i j
      · simp [residual, firstLHS]
      · simp only [residual, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, secondLHS,
          secondRHS_zero, rightBlock_apply]
        congr 2
        apply Finset.sum_congr rfl
        intro l _
        rw [show ((if l = j then 1 else 0) - ρ l * exp (z u * edgeLo σ l j) *
          dressedQhat z ρ σ 0 g (z u) l j) = baseSecond z ρ σ u l j by
            exact congrFun (congrFun (congrFun (secondBlock_zero z ρ σ g) u) l) j]
    rw [he] at hdg
    have hfresh := (hasFDerivAt_const (0 : E) Gbase).prodMk
      (((2 * π) • rightBlock (baseSecond z ρ σ)).hasFDerivAt.sub_const (baseSource z ρ σ))
    exact hdg.unique hfresh
  change L = triangular (baseFirst z ρ σ) (baseSecond z ρ σ)
    ((ContinuousLinearMap.snd ℝ E E).comp (L.comp (ContinuousLinearMap.inl ℝ E E)))
  apply ContinuousLinearMap.ext
  intro p
  rw [triangular_apply]
  apply Prod.ext
  · funext u i j
    exact htop u i j p
  · have hs : p = (p.1, 0) + (0, p.2) := by
      change p = (p.1 + (0 : E), (0 : E) + p.2)
      rw [add_zero, zero_add]
    have hg := congrArg (fun f : E →L[ℝ] P => f p.2) hG
    change L (0, p.2) = (0, (2 * π) • rightBlock (baseSecond z ρ σ) p.2) at hg
    conv_lhs => rw [hs, map_add, hg]
    rfl

theorem baseFirst_isUnit_det (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    IsUnit (Matrix.det (baseFirst z ρ σ u)) := by
  rw [baseFirst_eq, detGuneq_eq_Q0 (z u) ρ σ 0 hρ]
  exact Q0_mat_phys_isUnit_det (hz u) hvac hρ hσ

theorem baseSecond_isUnit_det (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    IsUnit (Matrix.det (baseSecond z ρ σ u)) := by
  rw [baseSecond_eq, detHuneq_eq_Q0 (z u) ρ σ 0 hρ]
  exact Q0_mat_phys_isUnit_det (hz u) hvac hρ hσ

def baseSeed (z : ι → ℝ) (ρ σ : Fin N → ℝ) : TailMatrix ι N :=
  (2 * π)⁻¹ • rightBlock (inverseBlocks (baseSecond z ρ σ)) (baseSource z ρ σ)

theorem residual_zero_eq (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K G : TailMatrix ι N) :
    residual z ρ σ K (0, (0, G)) =
      (0, (2 * π) • rightBlock (baseSecond z ρ σ) G - baseSource z ρ σ) := by
  apply Prod.ext <;> funext u i j
  · simp [residual, firstLHS]
  · simp only [residual, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, secondLHS,
      secondRHS_zero, rightBlock_apply]
    congr 2
    apply Finset.sum_congr rfl
    intro l _
    rw [show ((if l = j then 1 else 0) - ρ l * exp (z u * edgeLo σ l j) *
      dressedQhat z ρ σ 0 G (z u) l j) = baseSecond z ρ σ u l j by
        exact congrFun (congrFun (congrFun (secondBlock_zero z ρ σ G) u) l) j]

theorem residual_base (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hH : ∀ u, IsUnit (Matrix.det (baseSecond z ρ σ u))) :
    residual z ρ σ K (0, (0, baseSeed z ρ σ)) = 0 := by
  rw [residual_zero_eq]
  unfold baseSeed
  rw [map_smul, rightBlock_right_inverse _ hH, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero), one_smul, sub_self]
  rfl

/-- A genuine local C-infinity BH root family for arbitrary finite tails and
unequal positive additive diameters. Both determinant hypotheses and the seed
equation are discharged internally from physical PY parameters. This theorem
constructs amplitudes; matrix RDF/OZ closure is a separate obligation. -/
theorem exists_contDiffAt_root (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 := by
  have hinv : ((fderiv ℝ (residual z ρ σ K) (0, (0, baseSeed z ρ σ))).comp
      (ContinuousLinearMap.inr ℝ ℝ (TailMatrix ι N × TailMatrix ι N))).IsInvertible := by
    rw [residual_partial_triangular]
    exact triangular_isInvertible _ _
      (baseFirst_isUnit_det z ρ σ hz hvac hρ hσ)
      (baseSecond_isUnit_det z ρ σ hz hvac hρ hσ) _
  obtain ⟨ψ, hψ, heq, hsm⟩ := FMSA.MSASolutionFamily.exists_contDiffAt_root_of_prodDomain_ift
    (by norm_num : (∞ : ℕ∞ω) ≠ 0) (residual_contDiff z ρ σ K).contDiffAt
    (residual_base z ρ σ K (baseSecond_isUnit_det z ρ σ hz hvac hρ hσ)) hinv
  refine ⟨ψ, hψ, ?_, hsm⟩
  filter_upwards [heq] with τ hτ
  exact (residual_eq_zero_iff z ρ σ K (ψ τ).1 (ψ τ).2 τ).mp hτ

end FMSA.ExactMSA.MultiTailMixture
