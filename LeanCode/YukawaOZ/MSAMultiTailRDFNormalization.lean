import LeanCode.YukawaOZ.MSAMultiTailOZ
import LeanCode.YukawaOZ.MSAMultiTailRDFRationalBlocks

/-! Actual BH moment normalization used by RDF rational spectral assembly. -/
noncomputable section
open Real
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def normA (xi : ℝ) (z Dt G : ι → ℝ) : ℝ := rhoOf xi * amplitudeA xi z Dt G
def normQp (xi : ℝ) (z Dt G : ι → ℝ) : ℝ := rhoOf xi * amplitudeQp xi z Dt G
def normW (xi : ℝ) (z Dt G : ι → ℝ) (u : ι) : ℝ := rhoOf xi * W xi z Dt G u
def normC (xi : ℝ) (z Dt G : ι → ℝ) (u : ι) : ℝ := rhoOf xi * C xi z Dt G u
def normOffset (xi : ℝ) (z Dt G : ι → ℝ) : ℝ := normQp xi z Dt G - normA xi z Dt G / 2 -
  ∑ u, (normW xi z Dt G u + normC xi z Dt G u)

theorem momentM_normalized (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, z u ≠ 0) :
    momentM xi z Dt G = -((∑ u, normW xi z Dt G u / z u) +
      (∑ u, normC xi z Dt G u / z u) + ∑ u, normC xi z Dt G u) := by
  have he (u : ι) : Dt u * Mtil xi (z u) (G u) =
      -(normW xi z Dt G u / z u + normC xi z Dt G u / z u + normC xi z Dt G u) := by
    unfold normW normC W C Mtil
    field_simp [hz u]
    ring
  unfold momentM
  simp_rw [he]
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]

theorem momentN_normalized (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, z u ≠ 0) :
    momentN xi z Dt G = (∑ u, (normW xi z Dt G u + normC xi z Dt G u) / (z u) ^ 2) +
      (∑ u, normC xi z Dt G u / z u) + (∑ u, normC xi z Dt G u) / 2 := by
  have he (u : ι) : Dt u * Ntil xi (z u) (G u) =
      (normW xi z Dt G u + normC xi z Dt G u) / (z u) ^ 2 +
        normC xi z Dt G u / z u + normC xi z Dt G u / 2 := by
    unfold normW normC W C Ntil
    field_simp [hz u]
    ring
  unfold momentN
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_div]

theorem hs_scaled_core_identity (a0 b0 m n : ℝ)
    (hbase : (a0 / 2 + b0) ^ 2 + 2 * b0 = 0) :
    let a := a0 * (1 + m) - 4 * b0 * n
    let h := (a0 + b0) * (1 + m) + a0 * n
    (h - a / 2) ^ 2 - 2 * (a - h) * (1 + m) - 2 * a * n = 0 := by
  dsimp only
  linear_combination (1 + m + 2 * n) ^ 2 * hbase

theorem normalized_amplitude_identity (xi : ℝ) (z Dt G : ι → ℝ) (hxi : 1 - xi ≠ 0) :
    (normQp xi z Dt G - normA xi z Dt G / 2) ^ 2 -
      2 * (normA xi z Dt G - normQp xi z Dt G) * (1 + momentM xi z Dt G) -
      2 * normA xi z Dt G * momentN xi z Dt G = 0 := by
  have hb : (rhoOf xi * bA0 xi / 2 + rhoOf xi * bB0 xi) ^ 2 + 2 * (rhoOf xi * bB0 xi) = 0 := by
    unfold rhoOf bA0 bB0
    field_simp [hxi, pi_ne_zero]
    ring
  have hqp : qp0 xi = bA0 xi + bB0 xi := by
    unfold qp0 bA0 bB0
    ring
  have ha := hs_scaled_core_identity (rhoOf xi * bA0 xi) (rhoOf xi * bB0 xi)
    (momentM xi z Dt G) (momentN xi z Dt G) hb
  unfold normA normQp amplitudeA amplitudeQp
  rw [hqp]
  dsimp only at ha
  linear_combination ha

/-- Both the pole at zero and the constant term of the RDF rational residual vanish. -/
theorem rdf_core_normalization (xi : ℝ) (z Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, z u ≠ 0) :
    let a := normA xi z Dt G
    let h := normQp xi z Dt G
    let b := normOffset xi z Dt G
    let w := normW xi z Dt G
    let c := normC xi z Dt G
    ((b + ∑ u, w u) ^ 2 - (∑ u, c u) ^ 2 -
      2 * (a - h) * (1 - ∑ u, w u / z u) -
      2 * a * (∑ u, (w u + c u) / (z u) ^ 2) - 2 * h * (∑ u, c u / z u) = 0) ∧
    (-a ^ 2 + 2 * a * h - 2 * a * b - 2 * a * (∑ u, (w u + c u)) = 0) := by
  dsimp only
  constructor
  · have hm := momentM_normalized xi z Dt G hz
    have hn := momentN_normalized xi z Dt G hz
    have ha := normalized_amplitude_identity xi z Dt G hxi
    unfold normOffset
    simp only [Finset.sum_add_distrib]
    linear_combination ha + 2 * (normA xi z Dt G - normQp xi z Dt G) * hm +
      2 * normA xi z Dt G * hn
  · unfold normOffset
    ring

def rationalT (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) : ℝ :=
  RDFAlgebra.T (normA xi z Dt G) (normQp xi z Dt G) (normOffset xi z Dt G) z
    (normW xi z Dt G) s
def rationalP (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) : ℝ :=
  RDFAlgebra.P (normA xi z Dt G) (normQp xi z Dt G) z (normC xi z Dt G) s

theorem rationalP_eq (xi : ℝ) (z Dt G : ι → ℝ) {s : ℝ} (hs : s ≠ 0) :
    rationalP xi z Dt G s = rhoOf xi * secondRHS xi z Dt G s := by
  unfold rationalP RDFAlgebra.P RDFAlgebra.polyP RDFAlgebra.tailP secondRHS normA normQp normC
  have he : (∑ t, s ^ 2 * z t / (s + z t) * C xi z Dt G t) =
      s ^ 2 * ∑ t, z t * C xi z Dt G t / (s + z t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he]
  have hsum : (∑ u, z u * (rhoOf xi * C xi z Dt G u) / (s + z u)) =
      rhoOf xi * ∑ u, z u * C xi z Dt G u / (s + z u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hsum]
  field_simp [hs]

theorem rationalT_recenter (xi : ℝ) (z Dt G : ι → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hp : ∀ u, s + z u ≠ 0) :
    rationalT xi z Dt G s = s * factor xi z Dt G s - exp (-s) * rationalP xi z Dt G s := by
  have hdict : RDFAlgebra.dictionary (normA xi z Dt G) (normQp xi z Dt G) z
      (normW xi z Dt G) (normC xi z Dt G) (exp (-s)) s = rhoOf xi * Qhat xi z Dt G s := by
    unfold RDFAlgebra.dictionary normA normQp normW normC Qhat phi1 phi2
    rw [mul_add, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro u _
      ring
  unfold rationalT normOffset
  rw [RDFAlgebra.recenter_identity _ _ _ _ _ _ _ hs hp, hdict]
  unfold factor rationalP
  ring

theorem rational_residue (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u) (u : ι) :
    normW xi z Dt G u * rationalT xi z Dt G (z u) -
      normC xi z Dt G u * rationalP xi z Dt G (z u) =
      (rhoOf xi) ^ 2 * Dt u *
        (2 * π * G u * factor xi z Dt G (z u) - secondRHS xi z Dt G (z u)) := by
  rw [rationalT_recenter xi z Dt G (hz u).ne'
    (fun t => (add_pos (hz u) (hz t)).ne'), rationalP_eq xi z Dt G (hz u).ne']
  have hc : W xi z Dt G u * exp (-z u) + C xi z Dt G u = Dt u := by
    unfold W C gam
    ring
  have hw : z u * W xi z Dt G u = 2 * π * rhoOf xi * Dt u * G u := by
    unfold W
    field_simp [(hz u).ne']
  unfold normW normC
  linear_combination rhoOf xi * factor xi z Dt G (z u) * hw -
    (rhoOf xi) ^ 2 * secondRHS xi z Dt G (z u) * hc

/-- The rational OZ identity at the actual finite-tail BH root. This is
algebraic; it does not assert existence of a globally integrable RDF. -/
theorem rdf_rational_identity_of_root (xi : ℝ) (z K Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    {s : ℝ} (hs : s ≠ 0) (hp : ∀ u, s + z u ≠ 0) (hm : ∀ u, s - z u ≠ 0) :
    rationalT xi z Dt G s * rationalT xi z Dt G (-s) -
      rationalP xi z Dt G s * rationalP xi z Dt G (-s) = -s ^ 2 := by
  have he := RDFAlgebra.sum_identity (normA xi z Dt G) (normQp xi z Dt G)
    (normOffset xi z Dt G) s z (normW xi z Dt G) (normC xi z Dt G) hs
    (fun u => (hz u).ne') hp hm (fun u t => (add_pos (hz u) (hz t)).ne')
  have hn := rdf_core_normalization xi z Dt G hxi (fun u => (hz u).ne')
  dsimp only at hn
  rw [hn.1, hn.2, zero_div, add_zero] at he
  have hr (u : ι) : normW xi z Dt G u * rationalT xi z Dt G (z u) -
      normC xi z Dt G u * rationalP xi z Dt G (z u) = 0 := by
    rw [rational_residue xi z Dt G hz u, hroot.2 u, sub_self, mul_zero]
  change rationalT xi z Dt G s * rationalT xi z Dt G (-s) -
    rationalP xi z Dt G s * rationalP xi z Dt G (-s) + s ^ 2 +
    (∑ u, 2 * s ^ 2 / (s ^ 2 - (z u) ^ 2) *
      (normW xi z Dt G u * rationalT xi z Dt G (z u) -
        normC xi z Dt G u * rationalP xi z Dt G (z u))) = 0 at he
  simp_rw [hr, mul_zero] at he
  simp only [Finset.sum_const_zero, add_zero] at he
  linarith

end FMSA.ExactMSA.MultiTail
