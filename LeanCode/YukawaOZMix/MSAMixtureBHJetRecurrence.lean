import LeanCode.YukawaOZ.MSABHJetRecurrence
import LeanCode.YukawaOZMix.MSAMultiTailMixtureFirstOrder

/-! Actual finite-tail BH coefficient solves at every order. The two physical
seed blocks are proved invertible, including zero-density species and unequal
positive diameters. No infinite coupling-series convergence is used. -/
noncomputable section
open Matrix Real Filter Topology Set FMSA.MatrixQ0
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture.BHJet
variable {N : ℕ} {ι : Type*} [Fintype ι]

def coeff (X : ℝ → Matrix (Fin N) (Fin N) ℝ) (n : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => BSource.jet (fun t => X t i j) n)
def lower (X Y : ℕ → Matrix (Fin N) (Fin N) ℝ) (n : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ j ∈ Finset.range (n - 1), X (j + 1) * Y (n - (j + 1))

theorem coeff_mul (X Y : ℝ → Matrix (Fin N) (Fin N) ℝ) (n : ℕ)
    (hX : ∀ i j, ContDiffAt ℝ n (fun t => X t i j) 0)
    (hY : ∀ i j, ContDiffAt ℝ n (fun t => Y t i j) 0) :
    coeff (fun t => X t * Y t) n=∑ j ∈ Finset.range (n + 1), coeff X j * coeff Y (n - j) := by
  ext a b
  simp only [coeff, Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply]
  have hs : BSource.jet (fun t => ∑ l : Fin N, X t a l * Y t l b) n =
      ∑ l : Fin N, BSource.jet (fun t => X t a l * Y t l b) n := by
    unfold BSource.jet
    rw [iteratedDeriv_fun_sum (fun l _ => (hX a l).mul (hY l b)), Finset.sum_div]
  rw [hs]
  simp_rw [BSource.normalized_mul _ _ n (hX _ _) (hY _ _)]
  rw [Finset.sum_comm]

theorem convolution_split (X Y : ℕ → Matrix (Fin N) (Fin N) ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range (n + 1), X j * Y (n - j))=X n * Y 0 + X 0 * Y n + lower X Y n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [lower, Nat.succ_sub_succ_eq_sub, Nat.sub_self, Nat.sub_zero]
  abel

theorem coeff_local_eq (X Y : ℝ → Matrix (Fin N) (Fin N) ℝ) (n : ℕ)
    (h : X =ᶠ[𝓝 (0: ℝ)] Y) : coeff X n = coeff Y n := by
  ext a b
  have he : (fun t => X t a b)=ᶠ[𝓝 (0: ℝ)] fun t => Y t a b :=
    h.mono (fun t ht => congrFun (congrFun ht a) b)
  exact congrArg (fun v : ℝ => v / (n.factorial: ℝ)) (he.iteratedDeriv_eq n)

theorem coeff_scaled (X : ℝ → Matrix (Fin N) (Fin N) ℝ) (a : ℝ) (n : ℕ) :
    coeff (fun t => a • X t) n = a • coeff X n := by
  ext i j
  simp only [coeff, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, BSource.jet,
    iteratedDeriv_const_mul_field]
  ring

/-- The first BH block fixes D_n from only lower coefficient orders. -/
theorem actual_D_order (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (D G : ℝ → TailMatrix ι N) (u : ι) (n : ℕ) (hn : 0 < n)
    (hz : ∀ v, 0 < z v) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (hD0 : D 0 = 0)
    (hD : ∀ i j, ContDiffAt ℝ n (fun t => D t u i j) 0)
    (hF : ∀ i j, ContDiffAt ℝ n (fun t => firstBlock z ρ σ (D t) (G t) u i j) 0)
    (hroot : ∀ᶠ t in 𝓝 (0: ℝ), IsRoot z ρ σ (t • K) (D t) (G t)) :
    coeff (fun t => Matrix.of (D t u)) n =
      ((if n = 1 then Matrix.of (firstOrderSource z K u) else 0)-
        lower (coeff (fun t => Matrix.of (D t u)))
          (coeff (fun t => Matrix.of (firstBlock z ρ σ (D t) (G t) u))) n)*
        Matrix.of (inverseBlocks (baseFirst z ρ σ) u) := by
  let X := fun t => Matrix.of (D t u)
  let F := fun t => Matrix.of (firstBlock z ρ σ (D t) (G t) u)
  have he : (fun t => X t * F t)=ᶠ[𝓝 (0: ℝ)] fun t => t • Matrix.of (firstOrderSource z K u) := by
    filter_upwards [hroot] with t ht
    ext i j
    simpa only [X, F, firstBlock, Matrix.mul_apply, Matrix.of_apply,
      firstLHS, firstOrderSource, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      mul_div_assoc, mul_assoc, mul_comm, mul_left_comm] using ht.1 u i j
  have hc := coeff_local_eq _ _ n he
  rw [coeff_mul X F n hD hF, convolution_split _ _ n hn] at hc
  have hX0 : coeff X 0 = 0 := by ext i j; simp [coeff, BSource.jet, X, hD0]
  have hF0 : coeff F 0 = Matrix.of (baseFirst z ρ σ u) := by
    ext i j
    simp [coeff, BSource.jet, F, hD0]
  have hforce : coeff (fun t => t • Matrix.of (firstOrderSource z K u)) n =
      if n = 1 then Matrix.of (firstOrderSource z K u) else 0 := by
    ext i j
    simp only [coeff, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [BSource.jet_linear_coupling]
    split_ifs <;> rfl
  rw [hX0, Matrix.zero_mul, add_zero, hF0, hforce] at hc
  have hline : coeff X n * Matrix.of (baseFirst z ρ σ u)=
      (if n = 1 then Matrix.of (firstOrderSource z K u) else 0) - lower (coeff X) (coeff F) n := by
    rw [← hc]
    abel
  have hinv := congrArg (fun M => M * (Matrix.of (baseFirst z ρ σ u))⁻¹) hline
  rw [Matrix.mul_nonsing_inv_cancel_right (Matrix.of (baseFirst z ρ σ u)) (coeff X n)
    (baseFirst_isUnit_det z ρ σ hz hv hρ hσ u)] at hinv
  exact hinv

/-- The second BH block fixes G_n after D_n and its actual dictionary jets.
The RHS is the same triangular seed-Jacobian solve, written by tail block. -/
theorem actual_G_order (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (D G : ℝ → TailMatrix ι N) (u : ι) (n : ℕ) (hn : 0 < n)
    (hz : ∀ v, 0 < z v) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (hD0 : D 0 = 0)
    (hG : ∀ i j, ContDiffAt ℝ n (fun t => G t u i j) 0)
    (hF : ∀ i j, ContDiffAt ℝ n (fun t => secondBlock z ρ σ (D t) (G t) u i j) 0)
    (hroot : ∀ᶠ t in 𝓝 (0: ℝ), IsRoot z ρ σ (t • K) (D t) (G t)) :
    coeff (fun t => Matrix.of (G t u)) n =
      ((2 * π)⁻¹ • coeff (fun t => Matrix.of (secondRHS z ρ σ (D t) (G t) u)) n-
        Matrix.of (G 0 u) * coeff (fun t => Matrix.of (secondBlock z ρ σ (D t) (G t) u)) n-
        lower (coeff (fun t => Matrix.of (G t u)))
          (coeff (fun t => Matrix.of (secondBlock z ρ σ (D t) (G t) u))) n)*
        Matrix.of (inverseBlocks (baseSecond z ρ σ) u) := by
  let X := fun t => Matrix.of (G t u)
  let F := fun t => Matrix.of (secondBlock z ρ σ (D t) (G t) u)
  let P := fun t => Matrix.of (secondRHS z ρ σ (D t) (G t) u)
  have he : (fun t => (2 * π) • (X t * F t))=ᶠ[𝓝 (0: ℝ)] P := by
    filter_upwards [hroot] with t ht
    ext i j
    simpa only [X, F, P, secondBlock, Matrix.mul_apply, Matrix.of_apply,
      secondLHS, Matrix.smul_apply, smul_eq_mul] using ht.2 u i j
  have hc := coeff_local_eq _ _ n he
  rw [coeff_scaled, coeff_mul X F n hG hF, convolution_split _ _ n hn] at hc
  have hX0 : coeff X 0 = Matrix.of (G 0 u) := by ext i j; simp [coeff, BSource.jet, X]
  have hF0 : coeff F 0 = Matrix.of (baseSecond z ρ σ u) := by
    ext i j
    simp [coeff, BSource.jet, F, hD0]
  rw [hX0, hF0] at hc
  have hp : (2 * π: ℝ) ≠ 0 := by positivity
  have hc2 := congrArg (fun M => (2 * π)⁻¹ • M) hc
  rw [smul_smul, inv_mul_cancel₀ hp, one_smul] at hc2
  have hline : coeff X n * Matrix.of (baseSecond z ρ σ u)=
      (2 * π)⁻¹ • coeff P n - Matrix.of (G 0 u) * coeff F n - lower (coeff X) (coeff F) n := by
    rw [← hc2]
    abel
  have hinv := congrArg (fun M => M * (Matrix.of (baseSecond z ρ σ u))⁻¹) hline
  rw [Matrix.mul_nonsing_inv_cancel_right (Matrix.of (baseSecond z ρ σ u)) (coeff X n)
    (baseSecond_isUnit_det z ρ σ hz hv hρ hσ u)] at hinv
  exact hinv

theorem jet_scaled (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    BSource.jet (fun t => a * f t) n = a * BSource.jet f n := by
  simp only [BSource.jet, iteratedDeriv_const_mul_field]
  ring

theorem jet_finite_sum (f : Fin N → ℝ → ℝ) (n : ℕ)
    (hf : ∀ l, ContDiffAt ℝ n (f l) 0) :
    BSource.jet (fun t => ∑ l, f l t) n=∑ l, BSource.jet (f l) n := by
  unfold BSource.jet
  rw [iteratedDeriv_fun_sum (fun l _ => hf l), Finset.sum_div]

theorem product_zero_right_jet (G D : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hD0 : D 0 = 0) (hG : ContDiffAt ℝ n G 0) (hD : ContDiffAt ℝ n D 0) :
    BSource.jet (fun t => G t * D t) n = G 0 * BSource.jet D n+
      BSource.lowerProduct (BSource.jet G) (BSource.jet D) n := by
  rw [BSource.normalized_mul G D n hG hD,
    BSource.convolution_split (BSource.jet G) (BSource.jet D) n hn]
  simp only [BSource.jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    hD0, mul_zero, add_zero]

theorem affine_product_jet (a b : ℝ) (G D : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hD0 : D 0 = 0) (hG : ContDiffAt ℝ n G 0) (hD : ContDiffAt ℝ n D 0) :
    BSource.jet (fun t => (a - b * G t) * D t) n =
      (a - b * G 0) * BSource.jet D n-
        b * BSource.lowerProduct (BSource.jet G) (BSource.jet D) n := by
  have he : (fun t => (a - b * G t) * D t)=fun t => a * D t + (-b) * (G t * D t) := by funext t; ring
  rw [he, ScalarBSource.jet_linear D (fun t => G t * D t) a (-b) n hD (hG.mul hD),
    product_zero_right_jet G D n hn hD0 hG hD]
  ring

/-- W_n depends on D_n and known lower jets; the unknown G_n cancels because D_0=0. -/
theorem actual_W_jet (z : ι → ℝ) (ρ : Fin N → ℝ) (D G : ℝ → TailMatrix ι N)
    (u : ι) (i j : Fin N) (n : ℕ) (hn : 0 < n) (hD0 : D 0 = 0)
    (hG : ∀ l, ContDiffAt ℝ n (fun t => G t u i l) 0)
    (hD : ∀ l, ContDiffAt ℝ n (fun t => D t u l j) 0) :
    BSource.jet (fun t => W z ρ (D t) (G t) u i j) n =
      (2 * π / z u)*∑ l, ρ l * (G 0 u i l * BSource.jet (fun t => D t u l j) n+
        BSource.lowerProduct (BSource.jet (fun t => G t u i l))
          (BSource.jet (fun t => D t u l j)) n) := by
  simp only [W, MSAMixture.Wt, mul_assoc]
  rw [jet_scaled, jet_finite_sum _ n (fun l => contDiffAt_const.mul ((hG l).mul (hD l)))]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [jet_scaled, product_zero_right_jet _ _ n hn (by simp [hD0]) (hG l) (hD l)]

/-- The same endpoint cancellation applies to the actual continuity amplitude. -/
theorem actual_C_jet (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G : ℝ → TailMatrix ι N)
    (u : ι) (i j : Fin N) (n : ℕ) (hn : 0 < n) (hD0 : D 0 = 0)
    (hG : ∀ l, ContDiffAt ℝ n (fun t => G t u i l) 0)
    (hD : ∀ l, ContDiffAt ℝ n (fun t => D t u l j) 0) :
    BSource.jet (fun t => C z ρ σ (D t) (G t) u i j) n =
      ∑ l, exp (z u * (σ l - σ i) / 2)*
        (MSAMixture.gam (z u) ρ σ (Matrix.of (G 0 u)) i l * BSource.jet (fun t => D t u l j) n-
          (2 * π * ρ l * exp (-z u * MSAMixture.sigMix σ i l) / z u)*
            BSource.lowerProduct (BSource.jet (fun t => G t u i l))
              (BSource.jet (fun t => D t u l j)) n) := by
  have he : (fun t => C z ρ σ (D t) (G t) u i j)=fun t => ∑ l,
      exp (z u * (σ l - σ i) / 2) * (((if i = l then 1 else 0)-
        (2 * π * ρ l * exp (-z u * MSAMixture.sigMix σ i l) / z u) * G t u i l) * D t u l j) := by
    funext t
    simp only [C, MSAMixture.Ct, MSAMixture.gam]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, jet_finite_sum _ n (fun l => contDiffAt_const.mul
    ((contDiffAt_const.sub (contDiffAt_const.mul (hG l))).mul (hD l)))]
  apply Finset.sum_congr rfl
  intro l _
  rw [jet_scaled, affine_product_jet _ _ _ _ n hn (by simp [hD0]) (hG l) (hD l)]
  simp only [MSAMixture.gam, Matrix.of_apply]
  ring

def SatisfiesOrder (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (D G : ℝ → TailMatrix ι N) (u : ι) (n : ℕ) : Prop :=
  coeff (fun t => Matrix.of (D t u)) n =
    ((if n = 1 then Matrix.of (firstOrderSource z K u) else 0)-
      lower (coeff (fun t => Matrix.of (D t u)))
        (coeff (fun t => Matrix.of (firstBlock z ρ σ (D t) (G t) u))) n)*
      Matrix.of (inverseBlocks (baseFirst z ρ σ) u) ∧
  coeff (fun t => Matrix.of (G t u)) n =
    ((2 * π)⁻¹ • coeff (fun t => Matrix.of (secondRHS z ρ σ (D t) (G t) u)) n-
      Matrix.of (G 0 u) * coeff (fun t => Matrix.of (secondBlock z ρ σ (D t) (G t) u)) n-
      lower (coeff (fun t => Matrix.of (G t u)))
        (coeff (fun t => Matrix.of (secondBlock z ρ σ (D t) (G t) u))) n)*
      Matrix.of (inverseBlocks (baseSecond z ρ σ) u)

/-- All coefficient regularity is supplied by a single actual smooth root germ. -/
theorem actual_smooth_root_orders (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (hD0 : (ψ 0).1 = 0)
    (hroot : ∀ᶠ t in 𝓝 (0: ℝ), IsRoot z ρ σ (t • K) (ψ t).1 (ψ t).2)
    (hψ : ContDiffAt ℝ ∞ ψ 0) :
    ∀ u n, 0 < n → SatisfiesOrder z ρ σ K (fun t => (ψ t).1) (fun t => (ψ t).2) u n := by
  intro u n hn
  have ho : (n: ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop (le_refl _) n
  have hp : ContDiffAt ℝ n ψ 0 := hψ.of_le ho
  have hd (i j : Fin N) : ContDiffAt ℝ n (fun t => (ψ t).1 u i j) 0 :=
    ((Dt_entry_contDiff u i j).of_le ho).contDiffAt.comp 0 hp
  have hg (i j : Fin N) : ContDiffAt ℝ n (fun t => (ψ t).2 u i j) 0 :=
    ((G_entry_contDiff u i j).of_le ho).contDiffAt.comp 0 hp
  have hf (i j : Fin N) : ContDiffAt ℝ n
      (fun t => firstBlock z ρ σ (ψ t).1 (ψ t).2 u i j) 0 :=
    ((firstBlock_contDiff z ρ σ u i j).of_le ho).contDiffAt.comp 0 hp
  have hh (i j : Fin N) : ContDiffAt ℝ n
      (fun t => secondBlock z ρ σ (ψ t).1 (ψ t).2 u i j) 0 :=
    ((secondBlock_contDiff z ρ σ u i j).of_le ho).contDiffAt.comp 0 hp
  exact ⟨actual_D_order z ρ σ K _ _ u n hn hz hv hρ hσ hD0 hd hf hroot,
    actual_G_order z ρ σ K _ _ u n hn hz hv hρ hσ hD0 hg hh hroot⟩

/-- Physical-domain existence and every finite-order solve are both proved.
No amplitude Jacobian invertibility or finite-B assertion is supplied. -/
theorem exists_actual_root_with_all_orders (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0=(0, baseSeed z ρ σ) ∧
      (∀ᶠ t in 𝓝 (0: ℝ), IsRoot z ρ σ (t • K) (ψ t).1 (ψ t).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      ∀ u n, 0 < n → SatisfiesOrder z ρ σ K (fun t => (ψ t).1) (fun t => (ψ t).2) u n := by
  obtain ⟨ψ, h0, hr, hc⟩ := exists_contDiffAt_root z ρ σ K hz hv hρ hσ
  refine ⟨ψ, h0, hr, hc,?_⟩
  exact actual_smooth_root_orders z ρ σ K hz hv hρ hσ ψ
    (by rw [h0]) hr hc

/-- At gamma=1 the new all-order solve gives the existing HS-dressed DP
amplitude, whose physical radial identification is already proved. -/
theorem first_order_amplitude_recovered (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (D G : ℝ → TailMatrix ι N) (u : ι)
    (h : SatisfiesOrder z ρ σ K D G u 1) :
    coeff (fun t => Matrix.of (D t u)) 1 = Matrix.of (firstOrderDt z ρ σ K u) := by
  have hd := h.1
  simp only [if_pos rfl, lower, Nat.sub_self, Finset.range_zero, Finset.sum_empty, sub_zero] at hd
  rw [hd]
  unfold firstOrderDt
  rw [rightBlock_matrix]
  ext i j
  simp only [ite_true, Matrix.of_apply]

end FMSA.ExactMSA.MultiTailMixture.BHJet
