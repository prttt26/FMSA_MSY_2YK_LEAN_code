import LeanCode.YukawaOZMix.MSAMixtureBHRootUneqDefs
import LeanCode.YukawaOZMix.MSAMultiTailMixtureAEReciprocity

/-! The original single-tail BH equations are the singleton-label specialization
of the kernel-checked finite-tail system. -/
noncomputable section
open MeasureTheory Real Set Filter
open MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

theorem W_single (z : ℝ) (ρ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    W (fun _ : Unit => z) ρ (fun _ => Dt) (fun _ => Gt) = (fun _ : Unit => Wt z ρ Gt Dt) := rfl

theorem C_single (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    C (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) = (fun _ : Unit => Ct z ρ σ Gt Dt) := rfl

theorem amplitudeA_single (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    amplitudeA (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) = AVec z ρ σ Gt Dt := by
  funext j
  simp [amplitudeA, AVec, AMSA]

theorem amplitudeQp_single (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    amplitudeQp (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) = qpMat z ρ σ Gt Dt := by
  funext i j
  simp [amplitudeQp, qpMat, qpMSA]

theorem Qhat_single (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (s : ℝ) (i j : Fin N) :
    Qhat (fun _ : Unit => z) σ A qp (fun _ => Wt) (fun _ => Ct) s i j =
      qhatMixRuneq z σ qp Wt Ct A s i j := by
  simp only [Qhat, qhatMixRuneq, Finset.univ_unique, Finset.sum_singleton, edgeLo, edgeHi]
  ring

theorem QhatComplex_single (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) (i j : Fin N) :
    QhatComplex (fun _ : Unit => z) σ A qp (fun _ => Wt) (fun _ => Ct) s i j =
      qhatMixCuneq z σ qp Wt Ct A s i j := by
  simp only [QhatComplex, qhatMixCuneq, Finset.univ_unique, Finset.sum_singleton, edgeLo, edgeHi,
    neg_mul]
  ring

theorem dressedQhat_single (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℝ) (i j : Fin N) :
    dressedQhat (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) s i j =
      qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
        (AVec z ρ σ Gt Dt) s i j := by
  simp only [dressedQhat, amplitudeA_single, amplitudeQp_single, W_single, C_single]
  exact Qhat_single z σ _ _ _ _ s i j

theorem isRoot_single_iff (z : ℝ) (hz : z ≠ 0) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) :
    IsRoot (fun _ : Unit => z) ρ σ (fun _ => K) (fun _ => Dt) (fun _ => Gt) ↔
      MixBHRootUneq z ρ σ Gt Dt K := by
  have hf (i j : Fin N) :
      secondRHS (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) () i j =
      (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j +
        z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2 := by
    simp only [secondRHS, amplitudeA_single, amplitudeQp_single, C,
      Finset.univ_unique, Finset.sum_singleton]
    field_simp [hz]
    <;> ring
  simp only [IsRoot, firstLHS, secondLHS, dressedQhat_single, hf, MixBHRootUneq,
    ]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor <;> intro i j
    · simpa only [mul_assoc] using h₁ () i j
    · simpa only [mul_assoc] using h₂ () i j
  · rintro ⟨h₁,h₂⟩
    constructor <;> intro u i j
    · simpa only [mul_assoc] using h₁ i j
    · cases u; simpa only [mul_assoc] using h₂ i j


theorem q_single (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) (r : ℝ) :
    q (fun _ : Unit => z) σ A qp (fun _ => Wt) (fun _ => Ct) i j r =
      FMSA.ExactMSA.Breakpoint.baxterQ z σ A qp Wt Ct i j r := by
  have he : r - edgeLo σ i j - σ i = r - edgeHi σ i j := by
    unfold edgeLo edgeHi; ring
  simp only [q, FMSA.ExactMSA.Breakpoint.baxterQ, Finset.univ_unique,
    Finset.sum_singleton, he]
  split_ifs <;> ring

theorem qPrime_single (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) (r : ℝ) :
    qPrime (fun _ : Unit => z) σ A qp (fun _ => Wt) (fun _ => Ct) i j r =
      FMSA.ExactMSA.Breakpoint.baxterQ' z σ A qp Wt Ct i j r := by
  have he : r - edgeLo σ i j - σ i = r - edgeHi σ i j := by
    unfold edgeLo edgeHi; ring
  simp only [qPrime, FMSA.ExactMSA.Breakpoint.baxterQ', Finset.univ_unique,
    Finset.sum_singleton, he]

theorem correlation_single (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (r : ℝ) :
    correlation (fun _ : Unit => z) ρ σ A qp (fun _ => Wt) (fun _ => Ct) i j r =
      FMSA.ExactMSA.Breakpoint.baxterConvCore z ρ σ A qp Wt Ct i j r := by
  simp only [correlation, FMSA.ExactMSA.Breakpoint.baxterConvCore,
    q_single, qPrime_single]

/-- Single-tail ordered DCF, with the original amplitude and support definitions. -/
def legacyRadial (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ → ℝ :=
  orderedRadialCorrelation (fun _ : Unit => z) ρ σ (fun _ => K) (fun _ => Dt) (fun _ => Gt) i j

/-- The closed unequal-diameter core plus prescribed exterior tail equals
its independently defined real-space Baxter convolution almost everywhere.
Only the two removable support knots are excluded. -/
theorem legacyRadial_eq_closed_ae (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, 0 < σ i)
    (hroot : MixBHRootUneq z ρ σ Gt Dt K) (hK : ∀ i j, K i j = K j i) (i j : Fin N) :
    legacyRadial z ρ σ Gt Dt K i j =ᵐ[volume.restrict (Ioi 0)]
      (fun r => matCoreHSuneq z ρ σ i j r + matCoreCorrUneq z ρ σ Gt Dt i j r +
        matMSAtail K z σ i j r) := by
  have hrt := (isRoot_single_iff z hz.ne' ρ σ Gt Dt K).mpr hroot
  have base (a b : Fin N) (ho : σ b ≤ σ a) :
      (fun r => correlation (fun _ : Unit => z) ρ σ
        (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (fun _ => Wt z ρ Gt Dt)
        (fun _ => Ct z ρ σ Gt Dt) a b r) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => if r ≤ edgeHi σ a b then
        MSAMixtureCoreUneq.matCoreUneq z ρ σ (AVec z ρ σ Gt Dt)
          (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) a b r
        else K a b * exp (-z * (r - edgeHi σ a b)) / r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (ae_restrict_of_ae (volume.ae_ne (MSAMixtureCoreUneq.lamA σ a b))),
      (ae_restrict_of_ae (volume.ae_ne (edgeHi σ a b)))] with r hr hkn hR
    by_cases hc : r ≤ edgeHi σ a b
    · rw [if_pos hc, correlation_single]
      apply FMSA.ExactMSA.Breakpoint.baxterConvCore_eq_matCoreUneq_proved
        z hz ρ σ _ _ _ _ a b (fun i => (hσ i).le) (hσ b) ho
      by_cases hl : r < MSAMixtureCoreUneq.lamA σ a b
      · exact Or.inl ⟨hr, hl⟩
      · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt hl) hkn.symm,
          lt_of_le_of_ne hc hR⟩
    · rw [if_neg hc]
      have he := correlation_exterior_of_root (fun _ : Unit => z) (fun _ => hz) ρ σ
        (fun _ => K) (fun _ => Dt) (fun _ => Gt) (fun i => (hσ i).le)
        hrt a b r (lt_of_not_ge hc)
      simp only [W_single, C_single] at he
      simpa only [amplitudeA_single, amplitudeQp_single, W_single, C_single,
        Finset.univ_unique, Finset.sum_singleton] using he
  unfold legacyRadial orderedRadialCorrelation matCoreHSuneq matCoreCorrUneq matMSAtail
  simp only [W_single, C_single]
  simp only [amplitudeA_single, amplitudeQp_single, W_single, C_single]
  by_cases ho : σ j ≤ σ i
  · simp only [if_pos ho]
    filter_upwards [base i j ho] with r hr
    rw [hr]
    change _ = _ + _ + FMSA.ExactMSA.cMSAtail (K i j) z (sigMix σ i j) r
    unfold FMSA.ExactMSA.cMSAtail sigMix edgeHi
    split_ifs <;> first | (exfalso; linarith) | ring
  · simp only [if_neg ho]
    filter_upwards [base j i (le_of_not_ge ho)] with r hr
    rw [hr]
    have he : edgeHi σ j i = edgeHi σ i j := by unfold edgeHi; ring
    rw [he, hK j i]
    change _ = _ + _ + FMSA.ExactMSA.cMSAtail (K i j) z (sigMix σ i j) r
    unfold FMSA.ExactMSA.cMSAtail sigMix edgeHi
    split_ifs <;> first | (exfalso; linarith) | ring


theorem fourierFactor_single (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, 0 ≤ σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (k : ℝ) (hk : k ≠ 0) :
    fourierFactor (fun _ : Unit => z) ρ σ
      (amplitudeA (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt))
      (amplitudeQp (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt))
      (W (fun _ : Unit => z) ρ (fun _ => Dt) (fun _ => Gt))
      (C (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt)) k =
      FtMSAuneq z ρ σ Gt Dt (Complex.I * k) := by
  ext i j
  simp only [fourierFactor, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply,
    FtMSAuneq, ftilde, amplitudeA_single, amplitudeQp_single, W_single, C_single]
  rw [fourierQ_eq_QhatComplex _ (fun _ => hz) σ _ _ _ _ hσ k hk i j,
    QhatComplex_single]
  rw [Real.sqrt_mul (hρ i), Complex.ofReal_mul]

theorem FtMSAuneq_conjTranspose (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) :
    (FtMSAuneq z ρ σ Gt Dt (Complex.I * k)).conjTranspose =
      (FtMSAuneq z ρ σ Gt Dt (-(Complex.I * k))).transpose := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, FtMSAuneq, ftilde]
  have he (s : ℂ) : star (qhatMixCuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
      (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) s j i) =
      qhatMixCuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
        (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) (star s) j i := by
    rw [← QhatComplex_single, QhatComplex_conj, QhatComplex_single]
  rw [star_sub, star_mul, he]
  simp [Complex.star_def, mul_comm]

end FMSA.ExactMSA.MultiTailMixture
