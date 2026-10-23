import LeanCode.YukawaOZMix.MSAMixtureLegacyFourier

/-! Equal-diameter origin constraints from the actual Wronskian certificate. -/
noncomputable section
open Real MeasureTheory Set Filter Topology MSAMixture FMSA.MatrixQ0 Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def legacyOuterNumerator (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  MSAMixtureCoreUneq.gForm (MSAMixtureCoreUneq.cC0o z ρ σ A qp Wt Ct i j)
    (MSAMixtureCoreUneq.cC1o z ρ σ A qp Wt Ct i j)
    (MSAMixtureCoreUneq.cC2o z ρ σ A qp Wt Ct i j)
    (MSAMixtureCoreUneq.cC3o z ρ σ A qp Wt Ct i j)
    (MSAMixtureCoreUneq.cC4o z ρ σ A qp Wt Ct i j)
    (MSAMixtureCoreUneq.cEmo z ρ σ A qp Wt Ct i j)
    (MSAMixtureCoreUneq.cEpo z ρ σ A qp Wt Ct i j) z r

theorem legacyOuterNumerator_continuous (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N) :
    Continuous (legacyOuterNumerator z ρ σ A qp Wt Ct i j) := by
  unfold legacyOuterNumerator MSAMixtureCoreUneq.gForm
  fun_prop

/-- Primitive reciprocity gives reciprocity of the raw convolution at
all positive noncontact radii when both row orientations are available. -/
theorem correlation_equalDiam_reciprocal (z : ℝ) (hz : 0 < z)
    (ρ σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (sig : ℝ)
    (hs : 0 ≤ sig) (hσ : ∀ i, σ i = sig) (hv : vacMix ρ σ ≠ 0)
    (hr : MixBHRootUneq z ρ σ Gt Dt K) (hK : ∀ i j, K i j = K j i)
    (i j : Fin N) (r : ℝ) (hr0 : 0 < r) (hrR : r ≠ sig) :
    correlation (fun _ : Unit => z) ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (fun _ => Wt z ρ Gt Dt) (fun _ => Ct z ρ σ Gt Dt) i j r =
    correlation (fun _ : Unit => z) ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (fun _ => Wt z ρ Gt Dt) (fun _ => Ct z ρ σ Gt Dt) j i r := by
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => by rw [hσ i]; exact hs
  have ho (a b : Fin N) : σ b ≤ σ a := by rw [hσ a, hσ b]
  have hR (a b : Fin N) : edgeHi σ a b = sig := by unfold edgeHi; rw [hσ a,hσ b]; ring
  let zz := fun _ : Unit => z
  let A := amplitudeA zz ρ σ (fun _ => Dt) (fun _ => Gt)
  let qp := amplitudeQp zz ρ σ (fun _ => Dt) (fun _ => Gt)
  let w := W zz ρ (fun _ => Dt) (fun _ => Gt)
  let c := C zz ρ σ (fun _ => Dt) (fun _ => Gt)
  let P := fun a b r => (baxterPrimitive zz ρ σ A qp w c a b r).re
  have hc := nonlinearRoot_automatic_finite_wronskian zz ρ σ (fun _ => K)
    (fun _ => Dt) (fun _ => Gt) (fun _ => hz) hv
    ((isRoot_single_iff z hz.ne' ρ σ Gt Dt K).mpr hr) (fun _ => hK)
  have hp : P i j =ᵐ[volume] P j i := by
    filter_upwards [nonlinear_finite_wronskian_actual_primitive_reciprocity zz ρ σ
      (fun _ => Dt) (fun _ => Gt) (fun _ => hz) hσ0 hc i j] with x hx
    exact congrArg Complex.re hx
  have hcont (a b : Fin N) : ContinuousOn (P a b) (Ioi 0) := by
    intro x hx
    exact (baxterPrimitive_re_continuousAt_positive zz (fun _ => hz) ρ σ A qp w c
      hσ0 a b (ho a b) x hx).continuousWithinAt
  have he := MeasureTheory.Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hp) isOpen_Ioi (hcont i j) (hcont j i)
  have hj := baxterPrimitive_re_hasDerivAt zz (fun _ => hz) ρ σ A qp w c hσ0 j i (ho j i)
    r hr0 (by rw [hR j i]; exact hrR)
  have hi := baxterPrimitive_re_hasDerivAt zz (fun _ => hz) ρ σ A qp w c hσ0 i j (ho i j)
    r hr0 (by rw [hR i j]; exact hrR)
  have hder := (hi.congr_of_eventuallyEq (by
    filter_upwards [eventually_gt_nhds hr0] with x hx
    exact (he hx).symm)).unique hj
  have hcorr := mul_left_cancel₀ (show (-2*π*r) ≠ 0 by positivity) hder
  simpa only [A, qp, w, c, zz, amplitudeA_single, amplitudeQp_single, W_single, C_single,
    neg_mul, mul_assoc] using hcorr


theorem legacyOuterNumerator_equalDiam_reciprocal_zero (z : ℝ) (hz : 0 < z)
    (ρ σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (sig : ℝ)
    (hs : 0 < sig) (hσ : ∀ i, σ i = sig) (hv : vacMix ρ σ ≠ 0)
    (hr : MixBHRootUneq z ρ σ Gt Dt K) (hK : ∀ i j, K i j = K j i) (i j : Fin N) :
    legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j 0 =
    legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
      (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) j i 0 := by
  have hσp (a : Fin N) : 0 < σ a := by rw [hσ a]; exact hs
  have ho (a b : Fin N) : σ b ≤ σ a := by rw [hσ a,hσ b]
  have hl (a b : Fin N) : MSAMixtureCoreUneq.lamA σ a b = 0 := by
    unfold MSAMixtureCoreUneq.lamA edgeLo; rw [hσ a,hσ b]; simp
  have hR (a b : Fin N) : edgeHi σ a b = sig := by unfold edgeHi; rw [hσ a,hσ b]; ring
  have hform (a b : Fin N) (r : ℝ) (hp : 0 < r) (hsr : r < sig) :
      correlation (fun _ : Unit => z) ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (fun _ => Wt z ρ Gt Dt) (fun _ => Ct z ρ σ Gt Dt) a b r =
      legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) a b r / (2*π*r) := by
    rw [correlation_single]
    have he := FMSA.ExactMSA.Breakpoint.baxterConvCore_eq_matCoreUneq_proved z hz ρ σ
      (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
      a b (fun i => (hσp i).le) (hσp b) (ho a b)
      (show r ∈ Ioo 0 (MSAMixtureCoreUneq.lamA σ a b) ∪
          Ioo (MSAMixtureCoreUneq.lamA σ a b) (edgeHi σ a b) from
        Or.inr (by rw [hl a b,hR a b]; exact ⟨hp,hsr⟩))
    rw [he]
    simp only [MSAMixtureCoreUneq.matCoreUneq, hl, if_neg (not_le.mpr hp), legacyOuterNumerator]
  have he (r : ℝ) (hp : 0 < r) (hsr : r < sig) :
      legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r =
      legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) j i r := by
    have h := correlation_equalDiam_reciprocal z hz ρ σ Gt Dt K sig hs.le hσ hv hr hK i j r hp hsr.ne
    rw [hform i j r hp hsr, hform j i r hp hsr] at h
    exact (div_left_inj' (by positivity : 2*π*r ≠ 0)).mp h
  let F := legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
    (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j
  let G := legacyOuterNumerator z ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
    (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) j i
  have hf : Continuous (fun r : ℝ => F (min r (sig/2))) :=
    (legacyOuterNumerator_continuous z ρ σ _ _ _ _ i j).comp (continuous_id.min continuous_const)
  have hg : Continuous (fun r : ℝ => G (min r (sig/2))) :=
    (legacyOuterNumerator_continuous z ρ σ _ _ _ _ j i).comp (continuous_id.min continuous_const)
  have he0 := nonlinear_boundary_eq_of_positive_eq _ _ hf.continuousAt.continuousWithinAt
    hg.continuousAt.continuousWithinAt (fun r hr => he (min r (sig/2))
      (lt_min hr (by linarith)) (lt_of_le_of_lt (min_le_right _ _) (by linarith)))
  simpa only [min_eq_left (by linarith : (0:ℝ) ≤ sig/2), F, G] using he0

end FMSA.ExactMSA.MultiTailMixture
