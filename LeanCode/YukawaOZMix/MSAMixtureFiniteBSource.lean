import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearComplexKernel
import LeanCode.YukawaOZ.MSAMultiTailIntegrals
import LeanCode.YukawaOZMix.MSABSourceHierarchy

/-!
Actual finite mixture renewal source, with arbitrary additive diameters and
finite positive tail rates, including coincident rates. This source is the
inhomogeneity in the actual excess-RDF Volterra equation, NOT Fourier-OZ B.
The bounded-region integrals are evaluated; no finite-B premise is introduced.
-/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture.FiniteBSource
variable {N : ℕ} {ι : Type*} [Fintype ι]

def innerQp (σ r R : ℝ) : ℝ :=
  (r + R) * r ^ 2 / 2 - r ^ 3 / 3 - σ * ((r + R) * r - r ^ 2 / 2)
def innerA (σ r R : ℝ) : ℝ :=
  ((r + R) * r ^ 3 / 3 - r ^ 4 / 4 - 2 * σ * ((r + R) * r ^ 2 / 2 - r ^ 3 / 3)+
    σ ^ 2 * ((r + R) * r - r ^ 2 / 2)) / 2
def innerC (r R : ℝ) : ℝ := (r + R) * r - r ^ 2 / 2
def innerW (z r R : ℝ) : ℝ :=
  FMSA.FiniteYukawa.expPrimitive z (r + R) (-1) 0 r-
    FMSA.FiniteYukawa.expPrimitive z (r + R) (-1) 0 0

theorem innerQp_explicit (σ r R : ℝ) :
    innerQp σ r R = r ^ 3 / 6 + (R - σ) * r ^ 2 / 2 - σ * R * r := by unfold innerQp; ring

theorem innerA_explicit (σ r R : ℝ) :
    innerA σ r R = r ^ 4 / 24 + (R - σ) * r ^ 3 / 6 + (σ ^ 2 / 4 - σ * R / 2) * r ^ 2 + σ ^ 2 * R * r / 2 := by
  unfold innerA
  ring

theorem innerC_explicit (r R : ℝ) : innerC r R = r ^ 2 / 2 + R * r := by unfold innerC; ring

theorem innerW_explicit (z r R : ℝ) :
    innerW z r R = (r + R) / z - 1 / z ^ 2 - exp (-z * r) * (R / z - 1 / z ^ 2) := by
  simp only [innerW, FMSA.FiniteYukawa.expPrimitive, mul_zero, zero_div, zero_add,
    add_zero, zero_pow (by norm_num : 2 ≠ 0), exp_zero, mul_one]
  ring

theorem polynomial_inner_integral (σ r R A qp C : ℝ) :
    (∫ t in (0: ℝ)..r, (qp * (t - σ) + A / 2 * (t - σ) ^ 2 + C) * (r - t + R)) =
      qp * innerQp σ r R + A * innerA σ r R + C * innerC r R := by
  let p0 := -qp * σ + A * σ ^ 2 / 2 + C
  let p1 := qp - A * σ
  let p2 := A / 2
  have he : (fun t : ℝ => (qp * (t - σ) + A / 2 * (t - σ) ^ 2 + C) * (r - t + R)) =
      fun t => p0 * (r + R) + (p1 * (r + R) - p0) * t + (p2 * (r + R) - p1) * t ^ 2 + (-p2) * t ^ 3 := by
    funext t
    dsimp [p0, p1, p2]
    ring
  rw [he]
  have h := FMSA.FiniteYukawa.integral_cubic 0 r (p0 * (r + R))
    (p1 * (r + R) - p0) (p2 * (r + R) - p1) (-p2)
  simp only [sub_eq_add_neg] at h ⊢
  rw [h]
  dsimp [FMSA.FiniteYukawa.polyPrimitive, p0, p1, p2, innerQp, innerA, innerC]
  ring

theorem exponential_inner_integral (z r R : ℝ) (hz : 0 < z) :
    (∫ t in (0: ℝ)..r, exp (-z * t) * (r - t + R)) = innerW z r R := by
  have he : (fun t : ℝ => exp (-z * t) * (r - t + R)) =
      fun t => ((r + R) + (-1) * t + 0 * t ^ 2) * exp (-z * t) := by funext t; ring
  rw [he, FMSA.FiniteYukawa.integral_quadratic_exp 0 r z (r + R) (-1) 0 hz]
  rfl

theorem actual_background_inner (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (i j : Fin N)
    (r R : ℝ) (hr : 0 ≤ r) (hri : r ≤ σ i) :
    (∫ t in (0: ℝ)..r, nonlinearRecenteredQ z ρ σ D G i j t * (r - t + R)) =
      amplitudeQp z ρ σ D G i j * innerQp (σ i) r R+
      amplitudeA z ρ σ D G j * innerA (σ i) r R+
      ∑ u, (W z ρ D G u i j * innerW (z u) r R+
        C z ρ σ D G u i j * innerC r R) := by
  have he : (∫ t in (0: ℝ)..r, nonlinearRecenteredQ z ρ σ D G i j t * (r - t + R)) =
      ∫ t in (0: ℝ)..r,
        (amplitudeQp z ρ σ D G i j * (t - σ i)+
          amplitudeA z ρ σ D G j / 2 * (t - σ i) ^ 2) * (r - t + R)+
        ∑ u, (W z ρ D G u i j * (exp (-z u * t) * (r - t + R))+
          C z ρ σ D G u i j * (r - t + R)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr] at ht
    have hti : t ≤ σ i := ht.2.trans hri
    simp only [nonlinearRecenteredQ, min_eq_left hti, max_eq_right hti,
      sub_self, mul_zero, exp_zero, mul_one, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 r)
    (Continuous.intervalIntegrable (by fun_prop) 0 r),
    intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) 0 r)]
  have hp := polynomial_inner_integral (σ i) r R (amplitudeA z ρ σ D G j)
    (amplitudeQp z ρ σ D G i j) 0
  simp only [zero_mul, add_zero] at hp
  rw [hp]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 r)
    (Continuous.intervalIntegrable (by fun_prop) 0 r),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    exponential_inner_integral (z u) r R (hz u)]
  have hp := polynomial_inner_integral 0 r R 0 0 1
  simp only [zero_mul, zero_div, sub_zero, zero_add, one_mul] at hp
  rw [hp]

def backgroundQp (σ r R : ℝ) : ℝ :=
  if r ≤ σ then innerQp σ r R else -(r + R) * σ ^ 2 / 2 + σ ^ 3 / 6
def backgroundA (σ r R : ℝ) : ℝ :=
  if r ≤ σ then innerA σ r R else (r + R) * σ ^ 3 / 6 - σ ^ 4 / 24
def backgroundW (z σ r R : ℝ) : ℝ :=
  if r ≤ σ then innerW z r R else (r + R) / z - 1 / z ^ 2 - exp (-z * r) * (R / z - 1 / z ^ 2)
def backgroundC (z σ r R : ℝ) : ℝ :=
  if r ≤ σ then innerC r R else (r + R) * (σ + 1 / z) - σ ^ 2 / 2 - σ / z - 1 / z ^ 2-
    exp (z * σ) * exp (-z * r) * (R / z - 1 / z ^ 2)

theorem backgroundW_no_knot (z σ r R : ℝ) :
    backgroundW z σ r R = (r + R) / z - 1 / z ^ 2 - exp (-z * r) * (R / z - 1 / z ^ 2) := by
  unfold backgroundW
  split_ifs
  · exact innerW_explicit z r R
  · rfl

/-- Evaluated actual background convolution: only the knot sigma_i is needed. -/
theorem actual_background_closed (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) (r R : ℝ) (hr : 0 ≤ r) :
    (∫ t in (0: ℝ)..r, nonlinearRecenteredQ z ρ σ D G i j t * (r - t + R)) =
      amplitudeQp z ρ σ D G i j * backgroundQp (σ i) r R+
      amplitudeA z ρ σ D G j * backgroundA (σ i) r R+
      ∑ u, (W z ρ D G u i j * backgroundW (z u) (σ i) r R+
        C z ρ σ D G u i j * backgroundC (z u) (σ i) r R) := by
  by_cases hi : r ≤ σ i
  · simpa only [backgroundQp, backgroundA, backgroundW, backgroundC, if_pos hi] using
      actual_background_inner z ρ σ D G hz i j r R hr hi
  · rw [nonlinearQ_background_convolution z ρ σ D G hz hσ i j r R hr (not_le.mp hi).le]
    simp only [backgroundQp, backgroundA, backgroundW, backgroundC, if_neg hi,
      nonlinearQMoment0, nonlinearQMoment1, nonlinearTailAmplitude, Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have he : (∑ u, ((r + R) * (W z ρ D G u i j / z u+
        C z ρ σ D G u i j * (σ i + 1 / z u))-
        (W z ρ D G u i j / (z u) ^ 2 + C z ρ σ D G u i j*
          ((σ i) ^ 2 / 2 + σ i / z u + 1 / (z u) ^ 2))-
        (W z ρ D G u i j + C z ρ σ D G u i j * exp (z u * σ i))*
          exp (-z u * r) * (R / z u - 1 / (z u) ^ 2))) =
        ∑ u, (W z ρ D G u i j * ((r + R) / z u - 1 / (z u) ^ 2 - exp (-z u * r) * (R / z u - 1 / (z u) ^ 2))+
          C z ρ σ D G u i j * ((r + R) * (σ i + 1 / z u) - (σ i) ^ 2 / 2 - σ i / z u - 1 / (z u) ^ 2-
            exp (z u * σ i) * exp (-z u * r) * (R / z u - 1 / (z u) ^ 2))) := by
      apply Finset.sum_congr rfl
      intro u _
      ring
    simp only [mul_add, mul_sub, add_mul, sub_mul, div_eq_mul_inv,
      Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at he ⊢
    linear_combination he

abbrev BackgroundIndex (ι : Type*) := Fin 2 ⊕ (ι ⊕ ι)
abbrev SourceIndex (ι : Type*) (N : ℕ) := (Fin 3 ⊕ ι) ⊕ (Fin N × BackgroundIndex ι)

def sourceCoefficient (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix ι N)
    (i j : Fin N) : SourceIndex ι N → ℝ
  | .inl (.inl b) => if b = 0 then 1 else if b = 1 then
      amplitudeA z ρ σ D G j / (2 * π) else amplitudeQp z ρ σ D G i j / (2 * π)
  | .inl (.inr u) => z u * C z ρ σ D G u i j / (2 * π)
  | .inr (m, .inl b) => ρ m * (if b = 0 then amplitudeQp z ρ σ D G m j
      else amplitudeA z ρ σ D G j)
  | .inr (m, .inr (.inl u)) => ρ m * W z ρ D G u m j
  | .inr (m, .inr (.inr u)) => ρ m * C z ρ σ D G u m j

/-- Fully evaluated functions: piecewise polynomials and individual Yukawa
exponentials; the only knots are the finitely many species diameters. -/
def sourceBasis (z : ι → ℝ) (σ : Fin N → ℝ) (i j : Fin N)
    (r : ℝ) : SourceIndex ι N → ℝ
  | .inl (.inl b) => if b = 0 then -(r + edgeHi σ i j) else if b = 1 then r else 1
  | .inl (.inr u) => exp (-z u * r)
  | .inr (m, .inl b) => if b = 0 then backgroundQp (σ m) r (edgeHi σ i m)
      else backgroundA (σ m) r (edgeHi σ i m)
  | .inr (m, .inr (.inl u)) => backgroundW (z u) (σ m) r (edgeHi σ i m)
  | .inr (m, .inr (.inr u)) => backgroundC (z u) (σ m) r (edgeHi σ i m)

/-- No finite-basis premise: the actual nonlinear source equals this dictionary. -/
theorem actual_source_eq_finite (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    nonlinearExcessSource z ρ σ D G r i j =
      ∑ b : SourceIndex ι N, sourceCoefficient z ρ σ D G i j b * sourceBasis z σ i j r b := by
  have hconv (m : Fin N) :
      (∫ t in (0: ℝ)..r, nonlinearRecenteredQ z ρ σ D G m j (r - t) * (t + edgeHi σ i m)) =
      amplitudeQp z ρ σ D G m j * backgroundQp (σ m) r (edgeHi σ i m)+
      amplitudeA z ρ σ D G j * backgroundA (σ m) r (edgeHi σ i m)+
      ∑ u, (W z ρ D G u m j * backgroundW (z u) (σ m) r (edgeHi σ i m)+
        C z ρ σ D G u m j * backgroundC (z u) (σ m) r (edgeHi σ i m)) := by
    have he : (∫ t in (0: ℝ)..r, nonlinearRecenteredQ z ρ σ D G m j (r - t) * (t + edgeHi σ i m)) =
        ∫ t in (0: ℝ)..r, nonlinearRecenteredQ z ρ σ D G m j t * (r - t + edgeHi σ i m) := by
      calc
        _ = ∫ t in (0: ℝ)..r,
            (fun v => nonlinearRecenteredQ z ρ σ D G m j v * (r - v + edgeHi σ i m)) (r - t) := by
          apply intervalIntegral.integral_congr
          intro t _
          dsimp only
          congr 1
          ring
        _ = _ := by
          simpa using intervalIntegral.integral_comp_sub_left
            (f := fun v => nonlinearRecenteredQ z ρ σ D G m j v * (r - v + edgeHi σ i m))
            (a := (0: ℝ)) (b := r) r
    rw [he]
    exact actual_background_closed z ρ σ D G hz hσ m j r _ hr
  simp only [nonlinearExcessSource, nonlinearGSource, Matrix.of_apply, hconv,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    sourceCoefficient, sourceBasis]
  norm_num
  simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
  simp only [Finset.sum_div, Finset.sum_add_distrib, add_div, mul_add, Finset.mul_sum,
    mul_assoc, neg_mul, mul_one, one_mul]
  ring

/-- Every normalized derivative of the ACTUAL source has the evaluated finite
dictionary. Smooth actual amplitude jets are the sole differentiability input. -/
theorem actual_source_jet_finite (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : ℝ → TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) (n : ℕ)
    (hc : ∀ b : SourceIndex ι N, ContDiffAt ℝ n
      (fun t => sourceCoefficient z ρ σ (D t) (G t) i j b) 0) :
    BSource.jet (fun t => nonlinearExcessSource z ρ σ (D t) (G t) r i j) n =
      ∑ b : SourceIndex ι N, sourceBasis z σ i j r b*
        BSource.jet (fun t => sourceCoefficient z ρ σ (D t) (G t) i j b) n := by
  have he : (fun t => nonlinearExcessSource z ρ σ (D t) (G t) r i j) =
      fun t => ∑ b : SourceIndex ι N,
        sourceCoefficient z ρ σ (D t) (G t) i j b * sourceBasis z σ i j r b := by
    funext t
    exact actual_source_eq_finite z ρ σ (D t) (G t) hz hσ i j r hr
  rw [he]
  exact BHierarchy.coefficient_fixed_basis Finset.univ
    (fun b t => sourceCoefficient z ρ σ (D t) (G t) i j b)
    (fun b r => sourceBasis z σ i j r b) n 0 r (fun b _ => hc b)

/-- Beyond the existing finite HS ceiling all polynomial backgrounds cancel.
In particular differentiation introduces no additional decay rates. -/
theorem actual_source_jet_tail (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : ℝ → TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (i j : Fin N) (r : ℝ)
    (hr : rdfHSSupportCeiling σ ≤ r) (n : ℕ)
    (hc : ∀ u, ContDiffAt ℝ n (fun t => nonlinearExcessTail z ρ σ (D t) (G t) u i j) 0) :
    BSource.jet (fun t => nonlinearExcessSource z ρ σ (D t) (G t) r i j) n =
      ∑ u, exp (-z u * r) * BSource.jet (fun t => nonlinearExcessTail z ρ σ (D t) (G t) u i j) n := by
  have he : (fun t => nonlinearExcessSource z ρ σ (D t) (G t) r i j) =
      fun t => ∑ u, nonlinearExcessTail z ρ σ (D t) (G t) u i j * exp (-z u * r) := by
    funext t
    exact nonlinearExcessSource_tail z ρ σ (D t) (G t) hz hσ hv r hr i j
  rw [he]
  exact BHierarchy.coefficient_fixed_basis Finset.univ
    (fun u t => nonlinearExcessTail z ρ σ (D t) (G t) u i j)
    (fun u r => exp (-z u * r)) n 0 r (fun u _ => hc u)

theorem sourceCoefficient_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (i j : Fin N) (b : SourceIndex ι N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N =>
      sourceCoefficient z ρ σ p.1 p.2 i j b) := by
  rcases b with (b | u) | ⟨m, b | (u | u)⟩ <;>
    simp only [sourceCoefficient] <;> (try split_ifs) <;> fun_prop

theorem source_dictionary_size : Fintype.card (SourceIndex ι N) =
    3 + Fintype.card ι + N * (2 + 2 * Fintype.card ι) := by
  simp only [SourceIndex, BackgroundIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- A smooth amplitude-pair germ discharges coefficient regularity internally. -/
theorem actual_source_jet_of_smooth_pair (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) (hψ : ContDiffAt ℝ n ψ 0) :
    BSource.jet (fun t => nonlinearExcessSource z ρ σ (ψ t).1 (ψ t).2 r i j) n =
      ∑ b : SourceIndex ι N, sourceBasis z σ i j r b*
        BSource.jet (fun t => sourceCoefficient z ρ σ (ψ t).1 (ψ t).2 i j b) n := by
  apply actual_source_jet_finite z ρ σ (fun t => (ψ t).1) (fun t => (ψ t).2) hz hσ i j r hr n
  intro b
  have ho : (n: ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop (le_refl _) n
  exact ((sourceCoefficient_contDiff z ρ σ i j b).of_le ho).contDiffAt.comp 0 hψ

/-- Finite source structure at every finite order of a PROVED physical BH root.
Neither an arbitrary-order WH projection nor a finite-source premise is assumed. -/
theorem exists_actual_root_with_finite_sources (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0=(0, baseSeed z ρ σ) ∧
      (∀ᶠ t in 𝓝 (0: ℝ), IsRoot z ρ σ (t • K) (ψ t).1 (ψ t).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      ∀ n i j r, 0 ≤ r →
        BSource.jet (fun t => nonlinearExcessSource z ρ σ (ψ t).1 (ψ t).2 r i j) n =
          ∑ b : SourceIndex ι N, sourceBasis z σ i j r b*
            BSource.jet (fun t => sourceCoefficient z ρ σ (ψ t).1 (ψ t).2 i j b) n := by
  obtain ⟨ψ, h0, hr, hc⟩ := exists_contDiffAt_root z ρ σ K hz hv hρ hσ
  refine ⟨ψ, h0, hr, hc,?_⟩
  intro n i j r hrr
  have ho : (n: ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop (le_refl _) n
  exact actual_source_jet_of_smooth_pair z ρ σ ψ hz (fun i => (hσ i).le) i j r hrr n (hc.of_le ho)

end FMSA.ExactMSA.MultiTailMixture.FiniteBSource
