import LeanCode.YukawaOZ.MSAMultiTailSystem
import LeanCode.Closures.MSASolutionFamily

/-!
# Local smooth finite-tail BH root through the PY state

The tail Jacobian is block triangular at zero coupling. Cross-tail terms enter
the lower-left block; the two diagonal blocks contain the nonzero PY Baxter
factors. This includes coincident rates and arbitrary signed coupling directions.
-/

noncomputable section
open Real Filter Topology Set
open scoped BigOperators ContDiff

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def diagonal (a : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun u => a u • ContinuousLinearMap.proj u)

@[simp] theorem diagonal_apply (a p : ι → ℝ) (u : ι) : diagonal a p u = a u * p u := by
  simp [diagonal]

def triangular (a : ι → ℝ) (B : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ((ι → ℝ) × (ι → ℝ)) :=
  ((diagonal a).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (B.comp (ContinuousLinearMap.fst ℝ _ _) +
      (diagonal (fun u => 2 * π * a u)).comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem triangular_apply (a : ι → ℝ) (B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (p : (ι → ℝ) × (ι → ℝ)) :
    triangular a B p = (diagonal a p.1, B p.1 + diagonal (fun u => 2 * π * a u) p.2) := by
  rfl

def triangularInverse (a : ι → ℝ) (B : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ((ι → ℝ) × (ι → ℝ)) :=
  ((diagonal (fun u => (a u)⁻¹)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((diagonal (fun u => (2 * π * a u)⁻¹)).comp
      (ContinuousLinearMap.snd ℝ _ _ - B.comp
        ((diagonal (fun u => (a u)⁻¹)).comp (ContinuousLinearMap.fst ℝ _ _))))

@[simp] theorem triangularInverse_apply (a : ι → ℝ) (B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (p : (ι → ℝ) × (ι → ℝ)) :
    triangularInverse a B p = (diagonal (fun u => (a u)⁻¹) p.1,
      diagonal (fun u => (2 * π * a u)⁻¹) (p.2 - B (diagonal (fun u => (a u)⁻¹) p.1))) := by
  rfl

theorem triangular_isInvertible (a : ι → ℝ) (ha : ∀ u, a u ≠ 0)
    (B : (ι → ℝ) →L[ℝ] (ι → ℝ)) : (triangular a B).IsInvertible := by
  have hleft (p : ι → ℝ) : diagonal (fun u => (a u)⁻¹) (diagonal a p) = p := by
    ext u
    simp [ha u]
  have hright (p : ι → ℝ) : diagonal a (diagonal (fun u => (a u)⁻¹) p) = p := by
    ext u
    simp [ha u]
  refine ⟨ContinuousLinearEquiv.equivOfInverse (triangular a B) (triangularInverse a B) ?_ ?_, rfl⟩
  · intro p
    simp only [triangular_apply, triangularInverse_apply, hleft]
    apply Prod.ext
    · rfl
    · ext u
      simp only [diagonal_apply, Pi.sub_apply, Pi.add_apply]
      field_simp [ha u]
      ring
  · intro p
    simp only [triangular_apply, triangularInverse_apply, hright]
    apply Prod.ext
    · rfl
    · ext u
      simp only [diagonal_apply, Pi.sub_apply, Pi.add_apply]
      field_simp [ha u]
      ring

def residual (xi : ℝ) (z K : ι → ℝ) :
    ℝ × ((ι → ℝ) × (ι → ℝ)) → ((ι → ℝ) × (ι → ℝ)) := fun p =>
  ((fun u => p.2.1 u * factor xi z p.2.1 p.2.2 (z u) - 2 * π * p.1 * K u / z u),
   (fun u => 2 * π * p.2.2 u * factor xi z p.2.1 p.2.2 (z u) -
     secondRHS xi z p.2.1 p.2.2 (z u)))

theorem residual_contDiff (xi : ℝ) (z K : ι → ℝ) : ContDiff ℝ ∞ (residual xi z K) := by
  unfold residual factor Qhat secondRHS amplitudeA amplitudeQp momentM momentN W C Mtil Ntil gam
  fun_prop

theorem residual_base {xi : ℝ} (z K : ι → ℝ) (hxi : xi ∈ Ioo (0 : ℝ) 1)
    (hz : ∀ u, 0 < z u) :
    residual xi z K (0, (0, fun u => G0 xi (z u))) = 0 := by
  apply Prod.ext
  · ext u
    simp [residual]
  · ext u
    simp only [residual, factor_pi_zero, secondRHS_pi_zero, Pi.zero_apply]
    have hh := bh_base_eq hxi (hz u)
    simp only [bhF_base, bhP_base, F0] at hh
    simpa [F0, mul_assoc] using sub_eq_zero.mpr hh

/-- Actual amplitude partial of the full coupled residual at zero coupling. -/
theorem residual_partial_triangular (xi : ℝ) (z K Gbase : ι → ℝ) :
    let P := (ι → ℝ) × (ι → ℝ)
    let L := (fderiv ℝ (residual xi z K) (0, (0, Gbase))).comp
      (ContinuousLinearMap.inr ℝ ℝ P)
    L = triangular (fun u => F0 xi (z u))
      ((ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).comp
        (L.comp (ContinuousLinearMap.inl ℝ (ι → ℝ) (ι → ℝ)))) := by
  let E := ι → ℝ
  let P := E × E
  let p0 : P := (0, Gbase)
  let L : P →L[ℝ] P := (fderiv ℝ (residual xi z K) (0, p0)).comp
    (ContinuousLinearMap.inr ℝ ℝ P)
  have hne : (∞ : ℕ∞ω) ≠ 0 := by norm_num
  have hd : HasFDerivAt (fun p : P => residual xi z K (0, p)) L p0 :=
    ((residual_contDiff xi z K).contDiffAt.differentiableAt hne).hasFDerivAt.comp p0
      (ContinuousLinearMap.inr ℝ ℝ P).hasFDerivAt
  have htop (u : ι) (p : P) : (L p).1 u = F0 xi (z u) * p.1 u := by
    let pr : P →L[ℝ] ℝ := (ContinuousLinearMap.proj u).comp (ContinuousLinearMap.fst ℝ E E)
    have hp : HasFDerivAt (fun p : P => p.1 u) pr p0 := pr.hasFDerivAt
    have hf : HasFDerivAt (fun p : P => factor xi z p.1 p.2 (z u))
        (fderiv ℝ (fun p : P => factor xi z p.1 p.2 (z u)) p0) p0 :=
      ((factor_contDiff xi z (z u)).contDiffAt.differentiableAt hne).hasFDerivAt
    have hproduct := hp.mul hf
    have hout := pr.hasFDerivAt.comp p0 hd
    simp only [residual, zero_mul, mul_zero, zero_div, sub_zero] at hout
    have heq := hout.unique hproduct
    have heval := congrArg (fun f : P →L[ℝ] ℝ => f p) heq
    simpa [pr, p0, E, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.fst, LinearMap.fst, smul_eq_mul, factor_pi_zero] using heval
  have hG : L.comp (ContinuousLinearMap.inr ℝ E E) =
      (0 : E →L[ℝ] E).prod (diagonal (fun u => 2 * π * F0 xi (z u))) := by
    have hrestrict := hd.comp Gbase (ContinuousLinearMap.inr ℝ E E).hasFDerivAt
    change HasFDerivAt (fun g : E => residual xi z K (0, (0, g))) _ Gbase at hrestrict
    have he : (fun g : E => residual xi z K (0, (0, g))) =
        (fun g => (0, diagonal (fun u => 2 * π * F0 xi (z u)) g -
          (fun u => bhP0 xi (z u)))) := by
      funext g
      apply Prod.ext
      · ext u
        simp [residual]
      · ext u
        simp [residual]
        ring
    rw [he] at hrestrict
    have hfresh := (hasFDerivAt_const (0 : E) Gbase).prodMk
      ((diagonal (fun u => 2 * π * F0 xi (z u))).hasFDerivAt.sub_const
        (fun u => bhP0 xi (z u)))
    exact hrestrict.unique hfresh
  change L = triangular (fun u => F0 xi (z u))
    ((ContinuousLinearMap.snd ℝ E E).comp (L.comp (ContinuousLinearMap.inl ℝ E E)))
  apply ContinuousLinearMap.ext
  intro p
  rw [triangular_apply]
  apply Prod.ext
  · ext u
    exact htop u p
  · have hs : p = (p.1, 0) + (0, p.2) := by
      change p = (p.1 + (0 : E), (0 : E) + p.2)
      rw [add_zero, zero_add]
    have hg := congrArg (fun f : E →L[ℝ] P => f p.2) hG
    change L (0, p.2) = (0, diagonal (fun u => 2 * π * F0 xi (z u)) p.2) at hg
    conv_lhs => rw [hs, map_add, hg]
    rfl

/-- Smooth real BH root through the PY point for every finite tail set.
The neighbourhood may depend on all rates and on the chosen signed coupling direction.
This is local existence; it gives no root beyond a fold or global convergence radius. -/
theorem exists_contDiffAt_root {xi : ℝ} (z K : ι → ℝ)
    (hxi : xi ∈ Ioo (0 : ℝ) 1) (hz : ∀ u, 0 < z u) :
    ∃ ψ : ℝ → (ι → ℝ) × (ι → ℝ), ψ 0 = (0, fun u => G0 xi (z u)) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot xi z (fun u => τ * K u) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 := by
  let P := (ι → ℝ) × (ι → ℝ)
  let p0 : P := (0, fun u => G0 xi (z u))
  have hF (u : ι) : F0 xi (z u) ≠ 0 := by
    have h := bhF_base_ne_zero hxi (hz u)
    simpa [bhF, F0] using h
  have hinv : ((fderiv ℝ (residual xi z K) (0, p0)).comp
      (ContinuousLinearMap.inr ℝ ℝ P)).IsInvertible := by
    rw [residual_partial_triangular]
    exact triangular_isInvertible _ hF _
  obtain ⟨ψ, h0, hroot, hs⟩ := FMSA.MSASolutionFamily.exists_contDiffAt_root_of_prodDomain_ift
    (by norm_num : (∞ : ℕ∞ω) ≠ 0) (residual_contDiff xi z K).contDiffAt
    (residual_base z K hxi hz) hinv
  refine ⟨ψ, h0, ?_, hs⟩
  filter_upwards [hroot] with τ ht
  constructor
  · intro u
    have hh := congrArg (fun p : P => p.1 u) ht
    simpa [residual, sub_eq_zero, mul_assoc, mul_left_comm, mul_comm] using hh
  · intro u
    have hh := congrArg (fun p : P => p.2 u) ht
    simpa [residual, sub_eq_zero, mul_assoc] using hh

end FMSA.ExactMSA.MultiTail
