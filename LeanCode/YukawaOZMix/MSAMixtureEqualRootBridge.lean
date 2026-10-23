import LeanCode.YukawaOZMix.MSAMixtureBHRootRecenter

/-! Equal-diameter root and factor interfaces are faithful specializations
of the unequal-diameter definitions. -/
noncomputable section
open MSAMixture Real
namespace FMSA.ExactMSA.MixLeg3
variable {N : ℕ}

/-- **The unequal-σ Baxter transform reduces to the equal-σ one at equal diameters.**  At `σ_i = σ_j = sig`
the recentering exponent `lam = (σ_j−σ_i)/2` is `0` and the per-pair `a = σ_i`, `sij = (σ_i+σ_j)/2` both
become `sig`, so `qhatMixRuneq` collapses to `qhatMixR` term-for-term (the `Ct` split is identical, only
reordered). -/
theorem qhatMixRuneq_eq_qhatMixR_of_equal {N : ℕ} (z sig : ℝ) (σ : Fin N → ℝ)
    (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ) (s : ℝ) (i j : Fin N)
    (hi : σ i = sig) (hj : σ j = sig) :
    qhatMixRuneq z σ qp Wt Ct Av s i j = qhatMixR z sig qp Wt Ct Av s i j := by
  simp only [qhatMixRuneq, qhatMixR, hi, hj]
  rw [show (sig - sig) / 2 = (0:ℝ) from by ring, mul_zero, neg_zero, Real.exp_zero, one_mul,
      show (sig + sig) / 2 = sig from by ring]
  ring

/-- **`MixBHRootUneq` at equal σ ⟹ `MixBHRoot`.**  The equal-σ bridge: at `σ ≡ sig` the recentering
`e^{z·edgeLo σ · ·} = 1` (`edgeLo = 0`) and `qhatMixRuneq = qhatMixR` (`qhatMixRuneq_eq_qhatMixR_of_equal`),
so the recentered unequal-σ root is term-for-term the bare equal-σ root. -/
theorem MixBHRoot_of_MixBHRootUneq {N : ℕ} (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ k, σ k = sig)
    (h : MixBHRootUneq z ρ σ Gt Dt K) : MixBHRoot z sig ρ σ Gt Dt K := by
  obtain ⟨h29, h33⟩ := h
  have hbridge : ∀ a b : Fin N,
      Real.exp (z * edgeLo σ a b)
          * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z a b
        = qhatMixR z sig (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
            (AVec z ρ σ Gt Dt) z a b := by
    intro a b
    rw [show edgeLo σ a b = 0 from by unfold edgeLo; rw [hσ a, hσ b]; ring, mul_zero,
        Real.exp_zero, one_mul,
        qhatMixRuneq_eq_qhatMixR_of_equal z sig σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
          (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z a b (hσ a) (hσ b)]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [← h29 i j]
    exact (Finset.sum_congr rfl (fun l _ => by rw [hbridge j l])).symm
  · rw [← h33 i j]
    congr 1
    exact (Finset.sum_congr rfl (fun l _ => by rw [hbridge l j])).symm


theorem MixBHRootUneq_of_MixBHRoot (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig)
    (h : MixBHRoot z sig ρ σ Gt Dt K) : MixBHRootUneq z ρ σ Gt Dt K := by
  have he (a b : Fin N) : exp (z*edgeLo σ a b)=1 := by
    unfold edgeLo; rw [hσ a,hσ b]; simp
  unfold MixBHRootUneq
  simp only [he, one_mul, qhatMixRuneq_eq_qhatMixR_of_equal z sig σ _ _ _ _ z _ _ (hσ _) (hσ _)]
  exact h

theorem qhatMixCuneq_eq_qhatMixC_of_equal (z sig : ℝ) (σ : Fin N → ℝ)
    (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ) (s : ℂ) (i j : Fin N)
    (hi : σ i = sig) (hj : σ j = sig) :
    qhatMixCuneq z σ qp Wt Ct Av s i j = qhatMixC z sig qp Wt Ct Av s i j := by
  simp only [qhatMixCuneq, qhatMixC, hi, hj]
  rw [show (sig-sig)/2=(0:ℝ) by ring, Complex.ofReal_zero, mul_zero, neg_zero,
    Complex.exp_zero, one_mul, show (sig+sig)/2=sig by ring]
  ring

theorem FtMSAuneq_eq_FtMSA (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig) (s : ℂ) :
    FtMSAuneq z ρ σ Gt Dt s = FtMSA z sig ρ σ Gt Dt s := by
  ext i j
  simp only [FtMSAuneq, FtMSA, ftilde,
    qhatMixCuneq_eq_qhatMixC_of_equal z sig σ _ _ _ _ s i j (hσ i) (hσ j)]

theorem FtHSuneq_eq_FtHS (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, σ i = sig) (s : ℂ) :
    FtHSuneq z ρ σ s = FtHS z sig ρ σ s := by
  ext i j
  simp only [FtHSuneq, FtHS, ftilde,
    qhatMixCuneq_eq_qhatMixC_of_equal z sig σ _ _ _ _ s i j (hσ i) (hσ j)]

theorem Ft1uneq_eq_Ft1 (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, σ i = sig) (s : ℂ) :
    Ft1uneq z ρ σ Gt Dt s = Ft1 z sig ρ σ Gt Dt s := by
  rw [Ft1uneq, Ft1, FtMSAuneq_eq_FtMSA z sig ρ σ Gt Dt hσ s, FtHSuneq_eq_FtHS z sig ρ σ hσ s]

end FMSA.ExactMSA.MixLeg3
