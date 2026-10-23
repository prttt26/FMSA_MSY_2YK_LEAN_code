import LeanCode.YukawaOZ.MSAScalarBSource
import LeanCode.Closures.MSAFamilyConcrete

/-! Normalized coefficient recurrence of the ACTUAL scalar BH root. -/
noncomputable section
open Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.BSource
open ScalarBSource

theorem jet_const_add (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n) (a : ℝ) :
    jet (fun t => a + f t) n = jet f n := by
  simp only [jet, iteratedDeriv_const_add hn]

theorem affine_rest_jet (base a b : ℝ) (D G : ℝ → ℝ) (n : ℕ)
    (hn : 0 < n) (hD0 : D 0 = 0) (hD : ContDiffAt ℝ n D 0) (hG : ContDiffAt ℝ n G 0) :
    jet (fun t => base + D t * (a + b * (G t - G 0))) n =
      a * jet D n + b * lowerProduct (jet D) (jet G) n := by
  have he : (fun t => base + D t * (a + b * (G t - G 0))) =
      fun t => base + ((a - b * G 0) * D t + b * (D t * G t)) := by funext t; ring
  rw [he, jet_const_add _ n hn, jet_linear D (fun t => D t * G t) _ _ n hD (hD.mul hG),
    normalized_mul D G n hD hG, convolution_split (jet D) (jet G) n hn]
  simp only [jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    hD0, zero_mul, zero_add]
  ring

theorem actual_F_jet (xi z : ℝ) (D G : ℝ → ℝ) (n : ℕ)
    (hn : 0 < n) (hD0 : D 0 = 0) (hD : ContDiffAt ℝ n D 0) (hG : ContDiffAt ℝ n G 0) :
    jet (fun t => bhF xi z (D t, G t)) n =
      bhFRest xi z (G 0) * jet D n+
      (bhFRest xi z (G 0 + 1) - bhFRest xi z (G 0)) * lowerProduct (jet D) (jet G) n := by
  have he : (fun t => bhF xi z (D t, G t)) = fun t => F0 xi z+
      D t * (bhFRest xi z (G 0) + (bhFRest xi z (G 0 + 1) - bhFRest xi z (G 0)) * (G t - G 0)) := by
    funext t
    rw [bhF, bhFRest_affine xi z (G t) (G 0)]
  rw [he]
  exact affine_rest_jet _ _ _ D G n hn hD0 hD hG

theorem actual_P_jet (xi z : ℝ) (D G : ℝ → ℝ) (n : ℕ)
    (hn : 0 < n) (hD0 : D 0 = 0) (hD : ContDiffAt ℝ n D 0) (hG : ContDiffAt ℝ n G 0) :
    jet (fun t => bhP xi z (D t, G t)) n =
      bhPRest xi z (G 0) * jet D n+
      (bhPRest xi z (G 0 + 1) - bhPRest xi z (G 0)) * lowerProduct (jet D) (jet G) n := by
  have he : (fun t => bhP xi z (D t, G t)) = fun t => bhP0 xi z+
      D t * (bhPRest xi z (G 0) + (bhPRest xi z (G 0 + 1) - bhPRest xi z (G 0)) * (G t - G 0)) := by
    funext t
    rw [bhP, bhPRest_affine xi z (G t) (G 0)]
  rw [he]
  exact affine_rest_jet _ _ _ D G n hn hD0 hD hG

theorem jet_linear_coupling (a : ℝ) (n : ℕ) :
    jet (fun t => t * a) n = if n = 1 then a else 0 := by
  simp only [jet, iteratedDeriv_mul_const_field, iteratedDeriv_fun_id_zero]
  split_ifs with h
  · subst n
    simp
  · simp

/-- All terms on the right involve strictly lower orders. F_n,P_n themselves
are evaluated by actual_F_jet and actual_P_jet after D_n has been solved. -/
theorem actual_BH_recurrence (xi z K : ℝ) (D G : ℝ → ℝ) (n : ℕ)
    (hn : 0 < n) (hD0 : D 0 = 0) (hF0 : F0 xi z ≠ 0)
    (hD : ContDiffAt ℝ n D 0) (hG : ContDiffAt ℝ n G 0)
    (hroot : ∀ᶠ t in 𝓝 (0: ℝ),
      D t * bhF xi z (D t, G t) = t * (2 * π * K / z) ∧
      2 * π * (G t * bhF xi z (D t, G t)) = bhP xi z (D t, G t)) :
    jet D n = ((if n = 1 then 2 * π * K / z else 0)-
      lowerProduct (jet D) (jet (fun t => bhF xi z (D t, G t))) n) / F0 xi z ∧
    jet G n = (jet (fun t => bhP xi z (D t, G t)) n / (2 * π)-
      G 0 * jet (fun t => bhF xi z (D t, G t)) n-
      lowerProduct (jet G) (jet (fun t => bhF xi z (D t, G t))) n) / F0 xi z := by
  have hF : ContDiffAt ℝ n (fun t => bhF xi z (D t, G t)) 0 :=
    ((bhF_contDiff xi z).contDiffAt.of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)).comp 0
      (hD.prodMk hG)
  have hseed : jet (fun t => bhF xi z (D t, G t)) 0 = F0 xi z := by
    simp [jet, bhF, hD0]
  have hseedD : jet D 0 = 0 := by simp [jet, hD0]
  have h1 : jet (fun t => D t * bhF xi z (D t, G t)) n = if n = 1 then 2 * π * K / z else 0 := by
    have he : (fun t => D t * bhF xi z (D t, G t)) =ᶠ[𝓝 (0: ℝ)] fun t => t * (2 * π * K / z) :=
      hroot.mono (fun t h => h.1)
    rw [show jet (fun t => D t * bhF xi z (D t, G t)) n = jet (fun t => t * (2 * π * K / z)) n from
      congrArg (fun x : ℝ => x / (n.factorial : ℝ)) (he.iteratedDeriv_eq n), jet_linear_coupling]
  rw [normalized_mul D _ n hD hF] at h1
  have h2 : (2 * π) * (∑ j ∈ Finset.range (n + 1), jet G j * jet (fun t => bhF xi z (D t, G t)) (n - j)) =
      jet (fun t => bhP xi z (D t, G t)) n := by
    have he : (fun t => 2 * π * (G t * bhF xi z (D t, G t))) =ᶠ[𝓝 (0: ℝ)]
        fun t => bhP xi z (D t, G t) := hroot.mono (fun t h => h.2)
    have hh := congrArg (fun x : ℝ => x / (n.factorial : ℝ)) (he.iteratedDeriv_eq n)
    change jet (fun t => 2 * π * (G t * bhF xi z (D t, G t))) n = _ at hh
    unfold jet at hh
    rw [iteratedDeriv_const_mul_field] at hh
    have hh2 : (2 * π) * jet (fun t => G t * bhF xi z (D t, G t)) n =
        jet (fun t => bhP xi z (D t, G t)) n := by
      simpa only [jet, mul_div_assoc] using hh
    rw [normalized_mul G _ n hG hF] at hh2
    exact hh2
  constructor
  · simpa only [hseed] using solve_D_order (jet D) (jet (fun t => bhF xi z (D t, G t))) n
      (2 * π * K / z) hn hseedD (hseed ▸ hF0) h1
  · have hh := solve_G_order (jet G) (jet (fun t => bhF xi z (D t, G t)))
      (jet (fun t => bhP xi z (D t, G t))) n (2 * π) hn (hseed ▸ hF0) (by positivity) h2
    rw [hseed] at hh
    simpa only [jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] using hh

/-- Existence of actual smooth coefficient sequences satisfying the recurrence
is inherited from the proved concrete BH IFT, not postulated for formal jets. -/
theorem exists_actual_BH_jet_recurrence {xi z : ℝ}
    (hxi : xi ∈ Set.Ioo (0: ℝ) 1) (hz : 0 < z) :
    ∃ D G : ℝ → ℝ, D 0 = 0 ∧ G 0 = G0 xi z ∧
      ContDiffAt ℝ ∞ D 0 ∧ ContDiffAt ℝ ∞ G 0 ∧
      (∀ n : ℕ, 0 < n →
        jet D n = ((if n = 1 then 2 * π / z else 0)-
          lowerProduct (jet D) (jet (fun t => bhF xi z (D t, G t))) n) / F0 xi z ∧
        jet G n = (jet (fun t => bhP xi z (D t, G t)) n / (2 * π)-
          G 0 * jet (fun t => bhF xi z (D t, G t)) n-
          lowerProduct (jet G) (jet (fun t => bhF xi z (D t, G t))) n) / F0 xi z) := by
  obtain ⟨ψ, hψ0, hψeq, hψcd⟩ := FMSA.MSASolutionFamily.exists_contDiffAt_bhRoot hxi hz
  let D := fun t => (ψ t).1
  let G := fun t => (ψ t).2
  have hD0 : D 0 = 0 := by simp [D, hψ0]
  have hG0 : G 0 = G0 xi z := by simp [G, hψ0]
  have hD : ContDiffAt ℝ ∞ D 0 := hψcd.fst
  have hG : ContDiffAt ℝ ∞ G 0 := hψcd.snd
  have hF : F0 xi z ≠ 0 := by
    simpa [bhF, F0] using bhF_base_ne_zero hxi hz
  have heq : ∀ᶠ t in 𝓝 (0: ℝ), D t * bhF xi z (D t, G t)=t * (2 * π * 1 / z) ∧
      2 * π * (G t * bhF xi z (D t, G t))=bhP xi z (D t, G t) := by
    filter_upwards [hψeq] with t ht
    dsimp [D, G]
    rw [Prod.mk.eta]
    constructor
    · have h := sub_eq_zero.mp ht.1
      rw [h]
      ring
    · exact sub_eq_zero.mp ht.2
  refine ⟨D, G, hD0, hG0, hD, hG,?_⟩
  intro n hn
  have ho : (n : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop (le_refl _) n
  simpa only [mul_one] using actual_BH_recurrence xi z 1 D G n hn hD0 hF
    (hD.of_le ho) (hG.of_le ho) heq

end FMSA.ExactMSA.BSource
