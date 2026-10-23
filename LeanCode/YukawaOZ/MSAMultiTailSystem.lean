import LeanCode.YukawaOZ.MSABaxterKSpace

/-!
# Pure-fluid Blum–Høye system with an arbitrary finite set of Yukawa tails

The tail index is independent of the species index used by the mixture files.
These definitions transcribe `msa_exact.py._bhn_pieces/_bhn_residuals` at unit diameter.
No distinctness assumption is imposed on the rates. The cross denominators are
`s + z t`; positive rates suffice, including coincident rates.

This module certifies the residual transcription, its scalar specialization and
the finite-sum Baxter algebra. It does not identify a Fourier transform of a
physical direct correlation function with a square merely by defining it so.
-/

noncomputable section
open scoped ContDiff

namespace FMSA.ExactMSA.MultiTail

open Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def momentM (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  ∑ t, Dt t * Mtil xi (z t) (G t)

def momentN (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  ∑ t, Dt t * Ntil xi (z t) (G t)

def amplitudeA (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  bA0 xi * (1 + momentM xi z Dt G) - 4 * bB0 xi * momentN xi z Dt G

def amplitudeQp (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  qp0 xi * (1 + momentM xi z Dt G) + bA0 xi * momentN xi z Dt G

def W (xi : ℝ) (z Dt G : ι → ℝ) (t : ι) : ℝ :=
  2 * π * rhoOf xi * Dt t * G t / z t

def C (xi : ℝ) (z Dt G : ι → ℝ) (t : ι) : ℝ :=
  gam xi (z t) (G t) * Dt t

/-- Laplace transform of the noncompact Baxter factor, including its constant core term. -/
def Qhat (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) : ℝ :=
  phi1 s * amplitudeQp xi z Dt G + phi2 s * amplitudeA xi z Dt G +
    ∑ t, ((W xi z Dt G t + C xi z Dt G t * exp (-s)) / (s + z t) +
      C xi z Dt G t * (1 - exp (-s)) / s)

def factor (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) : ℝ :=
  1 - rhoOf xi * Qhat xi z Dt G s

def secondRHS (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) : ℝ :=
  (amplitudeA xi z Dt G + s * amplitudeQp xi z Dt G +
    ∑ t, s ^ 2 * z t / (s + z t) * C xi z Dt G t) / s ^ 2

/-- One pair of Blum–Høye equations per tail; no numerical residual normalization. -/
def IsRoot (xi : ℝ) (z K Dt G : ι → ℝ) : Prop :=
  (∀ t, Dt t * factor xi z Dt G (z t) = 2 * π * K t / z t) ∧
  (∀ t, 2 * π * G t * factor xi z Dt G (z t) = secondRHS xi z Dt G (z t))

theorem crossRate_pos {z : ι → ℝ} (hz : ∀ t, 0 < z t) (u t : ι) :
    0 < z u + z t := add_pos (hz u) (hz t)

theorem crossRate_ne_zero {z : ι → ℝ} (hz : ∀ t, 0 < z t) (u t : ι) :
    z u + z t ≠ 0 := (crossRate_pos hz u t).ne'

theorem W_add_C_exp (xi : ℝ) (z Dt G : ι → ℝ) (t : ι) :
    W xi z Dt G t + C xi z Dt G t * exp (z t) = Dt t * exp (z t) := by
  have he : exp (-(z t)) * exp (z t) = 1 := by rw [← exp_add]; simp
  simp only [W, C, gam]
  linear_combination -(Dt t * (2 * π * rhoOf xi * G t / z t)) * he

theorem amplitudeA_affine (xi : ℝ) (z Dt G : ι → ℝ) :
    amplitudeA xi z Dt G = bA0 xi +
      ∑ t, Dt t * (bA0 xi * Mtil xi (z t) (G t) - 4 * bB0 xi * Ntil xi (z t) (G t)) := by
  have he : (∑ t, Dt t * (bA0 xi * Mtil xi (z t) (G t) -
      4 * bB0 xi * Ntil xi (z t) (G t))) =
      bA0 xi * momentM xi z Dt G - 4 * bB0 xi * momentN xi z Dt G := by
    simp only [momentM, momentN, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, amplitudeA]
  ring

theorem amplitudeQp_affine (xi : ℝ) (z Dt G : ι → ℝ) :
    amplitudeQp xi z Dt G = qp0 xi +
      ∑ t, Dt t * (qp0 xi * Mtil xi (z t) (G t) + bA0 xi * Ntil xi (z t) (G t)) := by
  have he : (∑ t, Dt t * (qp0 xi * Mtil xi (z t) (G t) +
      bA0 xi * Ntil xi (z t) (G t))) =
      qp0 xi * momentM xi z Dt G + bA0 xi * momentN xi z Dt G := by
    simp only [momentM, momentN, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, amplitudeQp]
  ring

theorem factor_zero (xi : ℝ) (z G : ι → ℝ) (s : ℝ) :
    factor xi z (fun _ => 0) G s = F0 xi s := by
  simp [factor, Qhat, amplitudeA, amplitudeQp, momentM, momentN, W, C, F0, Qhat0]

theorem secondRHS_zero (xi : ℝ) (z G : ι → ℝ) (s : ℝ) :
    secondRHS xi z (fun _ => 0) G s = bhP0 xi s := by
  simp [secondRHS, amplitudeA, amplitudeQp, momentM, momentN, C, bhP0]

@[simp] theorem factor_pi_zero (xi : ℝ) (z G : ι → ℝ) (s : ℝ) :
    factor xi z (0 : ι → ℝ) G s = F0 xi s := factor_zero xi z G s

@[simp] theorem secondRHS_pi_zero (xi : ℝ) (z G : ι → ℝ) (s : ℝ) :
    secondRHS xi z (0 : ι → ℝ) G s = bhP0 xi s := secondRHS_zero xi z G s

/-- For fixed rates/density the whole coupled residual dictionary is smooth in all amplitudes.
This statement alone does not assert invertibility away from zero coupling. -/
theorem factor_contDiff (xi : ℝ) (z : ι → ℝ) (s : ℝ) :
    ContDiff ℝ ∞ (fun p : (ι → ℝ) × (ι → ℝ) => factor xi z p.1 p.2 s) := by
  unfold factor Qhat amplitudeA amplitudeQp momentM momentN W C Mtil Ntil gam
  fun_prop

theorem secondRHS_contDiff (xi : ℝ) (z : ι → ℝ) (s : ℝ) :
    ContDiff ℝ ∞ (fun p : (ι → ℝ) × (ι → ℝ) => secondRHS xi z p.1 p.2 s) := by
  unfold secondRHS amplitudeA amplitudeQp momentM momentN C Mtil Ntil gam
  fun_prop

theorem amplitudeA_singleton (xi z Dt G : ℝ) :
    amplitudeA xi (fun _ : Fin 1 => z) (fun _ => Dt) (fun _ => G) = msaA xi z Dt G := by
  simp [amplitudeA, momentM, momentN, msaA]

theorem amplitudeQp_singleton (xi z Dt G : ℝ) :
    amplitudeQp xi (fun _ : Fin 1 => z) (fun _ => Dt) (fun _ => G) = msaQp xi z Dt G := by
  simp [amplitudeQp, momentM, momentN, msaQp]

/-- The coupled first equation specializes to the already certified scalar dictionary. -/
theorem factor_singleton (xi z Dt G : ℝ) (hz : z ≠ 0) :
    factor xi (fun _ : Fin 1 => z) (fun _ => Dt) (fun _ => G) z = bhF xi z (Dt, G) := by
  simp only [factor, Qhat, amplitudeA_singleton, amplitudeQp_singleton, W, C,
    Fin.sum_univ_one, bhF, F0, bhFRest, Qhat0, msaA, msaQp, tailtil]
  field_simp
  ring

theorem secondRHS_singleton (xi z Dt G : ℝ) (hz : z ≠ 0) :
    secondRHS xi (fun _ : Fin 1 => z) (fun _ => Dt) (fun _ => G) z = bhP xi z (Dt, G) := by
  simp only [secondRHS, amplitudeA_singleton, amplitudeQp_singleton, C,
    Fin.sum_univ_one, bhP, bhP0, bhPRest, msaA, msaQp]
  field_simp
  ring

end FMSA.ExactMSA.MultiTail
