import LeanCode.YukawaOZMix.MSAMultiTailMixtureBaxter
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneqSmooth

/-!
# Finite-tail Blum–Høye dictionary for additive hard-core mixtures

Tail and species indices are independent. The first BH equation uses the
transposed transform, and the second uses the untransposed transform with the
opposite support-edge recentering. No distinct-rate or amplitude-sign hypothesis
is imposed. This dictionary and its smoothness are not a matrix closure certificate.
-/

noncomputable section
open Real FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators ContDiff

namespace FMSA.ExactMSA.MultiTailMixture

variable {N : ℕ} {ι : Type*} [Fintype ι]

-- The explicit function type keeps the entrywise product norm consistent.
abbrev TailMatrix (ι : Type*) (N : ℕ) := ι → Fin N → Fin N → ℝ

def W (z : ι → ℝ) (ρ : Fin N → ℝ) (Dt G : TailMatrix ι N) (t : ι) :=
  Wt (z t) ρ (G t) (Dt t)

def C (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (t : ι) :=
  Ct (z t) ρ σ (G t) (Dt t)

def amplitudeA (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (j : Fin N) : ℝ :=
  Qppphys ρ σ j j + ∑ t, mixDA (z t) ρ σ (G t) (Dt t) j

def amplitudeQp (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) : ℝ :=
  Q0phys ρ σ i j + ∑ t, mixDqp (z t) ρ σ (G t) (Dt t) i j

/-- Compact polynomial moment and finite noncompact Yukawa moments. -/
def Qhat (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (s : ℝ) (i j : Fin N) : ℝ :=
  exp (-s * edgeLo σ i j) *
    ((1 - s * σ i - exp (-s * σ i)) / s ^ 2 * qp i j +
      (1 - s * σ i + (s * σ i) ^ 2 / 2 - exp (-s * σ i)) / s ^ 3 * A j +
      ∑ t, (W t i j / (s + z t) + C t i j * (1 - exp (-s * σ i)) / s)) +
    ∑ t, C t i j * exp (-s * edgeHi σ i j) / (s + z t)

def dressedQhat (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (s : ℝ) (i j : Fin N) : ℝ :=
  Qhat z σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
    (W z ρ Dt G) (C z ρ σ Dt G) s i j

def firstLHS (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (u : ι) (i j : Fin N) : ℝ :=
  ∑ l, Dt u i l * ((if l = j then 1 else 0) -
    ρ l * exp (z u * edgeLo σ j l) * dressedQhat z ρ σ Dt G (z u) j l)

def secondLHS (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (u : ι) (i j : Fin N) : ℝ :=
  2 * π * ∑ l, G u i l * ((if l = j then 1 else 0) -
    ρ l * exp (z u * edgeLo σ l j) * dressedQhat z ρ σ Dt G (z u) l j)

def secondRHS (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (u : ι) (i j : Fin N) : ℝ :=
  (amplitudeA z ρ σ Dt G j + z u * amplitudeQp z ρ σ Dt G i j +
    ∑ t, (z u) ^ 2 * z t / (z u + z t) * C z ρ σ Dt G t i j) / (z u) ^ 2

def IsRoot (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) : Prop :=
  (∀ u i j, firstLHS z ρ σ Dt G u i j = 2 * π * K u i j / z u) ∧
  (∀ u i j, secondLHS z ρ σ Dt G u i j = secondRHS z ρ σ Dt G u i j)

def residual (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (p : ℝ × (TailMatrix ι N × TailMatrix ι N)) : TailMatrix ι N × TailMatrix ι N :=
  ((fun u i j => firstLHS z ρ σ p.2.1 p.2.2 u i j - 2 * π * p.1 * K u i j / z u),
   (fun u i j => secondLHS z ρ σ p.2.1 p.2.2 u i j - secondRHS z ρ σ p.2.1 p.2.2 u i j))

theorem residual_eq_zero_iff (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (τ : ℝ) :
    residual z ρ σ K (τ, (Dt, G)) = 0 ↔ IsRoot z ρ σ (τ • K) Dt G := by
  constructor
  · intro h
    constructor
    · intro u i j
      have hh := congrFun (congrFun (congrFun (congrArg Prod.fst h) u) i) j
      simpa [residual, sub_eq_zero, mul_assoc] using hh
    · intro u i j
      have hh := congrFun (congrFun (congrFun (congrArg Prod.snd h) u) i) j
      simpa [residual, sub_eq_zero] using hh
  · intro h
    apply Prod.ext <;> funext u i j
    · simp [residual, h.1 u i j, mul_assoc]
    · simp [residual, h.2 u i j]

omit [Fintype ι] in
/-- Per-tail cancellation, uniform in species count and unequal diameters. -/
theorem W_add_C_exp (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (u : ι) (i j : Fin N) :
    W z ρ Dt G u i j * exp (z u * edgeLo σ i j) +
      C z ρ σ Dt G u i j * exp (z u * edgeHi σ i j) =
        Dt u i j * exp (z u * edgeHi σ i j) := by
  have he : exp (-z u * σ i) * exp (z u * edgeHi σ i j) =
      exp (z u * edgeLo σ i j) := by
    rw [← exp_add]
    congr 1
    unfold edgeLo edgeHi
    ring
  have h := congrArg (fun x : ℝ => x * exp (z u * edgeHi σ i j))
    (cancellation_star (z u) ρ σ (G u) (Dt u) i j)
  have hR : (exp (-z u * σ i) * Wt (z u) ρ (G u) (Dt u) i j) *
      exp (z u * edgeHi σ i j) = Wt (z u) ρ (G u) (Dt u) i j *
        exp (z u * edgeLo σ i j) := by
    calc
      _ = Wt (z u) ρ (G u) (Dt u) i j *
          (exp (-z u * σ i) * exp (z u * edgeHi σ i j)) := by ring
      _ = _ := by rw [he]
  rw [sub_mul, hR] at h
  unfold W C
  linarith

@[simp] theorem amplitudeA_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G : TailMatrix ι N) (j : Fin N) :
    amplitudeA z ρ σ 0 G j = Qppphys ρ σ j j := by
  simp [amplitudeA, mixDA, mixM, mixN, Wt, Ct]

@[simp] theorem amplitudeQp_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G : TailMatrix ι N) (i j : Fin N) :
    amplitudeQp z ρ σ 0 G i j = Q0phys ρ σ i j := by
  simp [amplitudeQp, mixDqp, mixM, mixN, Wt, Ct]

@[fun_prop] theorem Dt_entry_contDiff (u : ι) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => p.1 u i j) := by
  exact (contDiff_apply_apply ℝ ℝ i j).comp ((contDiff_apply ℝ _ u).comp contDiff_fst)

@[fun_prop] theorem G_entry_contDiff (u : ι) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => p.2 u i j) := by
  exact (contDiff_apply_apply ℝ ℝ i j).comp ((contDiff_apply ℝ _ u).comp contDiff_snd)

@[fun_prop] theorem W_contDiff (z : ι → ℝ) (ρ : Fin N → ℝ) (u : ι) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => W z ρ p.1 p.2 u i j) := by
  simp only [W, Wt]
  have hD := @Dt_entry_contDiff N ι _
  have hG := @G_entry_contDiff N ι _
  fun_prop

@[fun_prop] theorem C_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => C z ρ σ p.1 p.2 u i j) := by
  simp only [C, Ct, MSAMixture.gam]
  have hD := @Dt_entry_contDiff N ι _
  have hG := @G_entry_contDiff N ι _
  fun_prop

@[fun_prop] theorem amplitudeA_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ) (j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => amplitudeA z ρ σ p.1 p.2 j) := by
  simp only [amplitudeA, mixDA, mixM, mixN, Wt, Ct, MSAMixture.gam]
  have hD := @Dt_entry_contDiff N ι _
  have hG := @G_entry_contDiff N ι _
  fun_prop

@[fun_prop] theorem amplitudeQp_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => amplitudeQp z ρ σ p.1 p.2 i j) := by
  simp only [amplitudeQp, mixDqp, mixM, mixN, Wt, Ct, MSAMixture.gam]
  have hD := @Dt_entry_contDiff N ι _
  have hG := @G_entry_contDiff N ι _
  fun_prop

@[fun_prop] theorem dressedQhat_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ) (s : ℝ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix ι N × TailMatrix ι N => dressedQhat z ρ σ p.1 p.2 s i j) := by
  simp only [dressedQhat, Qhat]
  fun_prop

/-- The actual matrix residual is smooth in coupling and all amplitudes. -/
theorem residual_contDiff (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    ContDiff ℝ ∞ (residual z ρ σ K) := by
  unfold residual
  apply ContDiff.prodMk
  all_goals apply contDiff_pi.mpr; intro u
  all_goals apply contDiff_pi.mpr; intro i
  all_goals apply contDiff_pi.mpr; intro j
  all_goals simp only [firstLHS, secondLHS, secondRHS]
  all_goals fun_prop

theorem amplitudeA_singleton (z : ℝ) (ρ σ : Fin N → ℝ) (Dt G : Matrix (Fin N) (Fin N) ℝ)
    (j : Fin N) :
    amplitudeA (fun _ : Fin 1 => z) ρ σ (fun _ => Dt) (fun _ => G) j = AMSA z ρ σ G Dt j := by
  simp [amplitudeA, AMSA]

theorem amplitudeQp_singleton (z : ℝ) (ρ σ : Fin N → ℝ) (Dt G : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) :
    amplitudeQp (fun _ : Fin 1 => z) ρ σ (fun _ => Dt) (fun _ => G) i j = qpMSA z ρ σ G Dt i j := by
  simp [amplitudeQp, qpMSA]

theorem Qhat_singleton (z : ℝ) (σ A : Fin N → ℝ) (qp W C : Matrix (Fin N) (Fin N) ℝ)
    (s : ℝ) (i j : Fin N) :
    Qhat (fun _ : Fin 1 => z) σ A qp (fun _ => W) (fun _ => C) s i j =
      qhatMixRuneq z σ qp W C A s i j := by
  simp [Qhat, qhatMixRuneq, edgeLo, edgeHi, neg_mul, mul_div_assoc]
  ring

end FMSA.ExactMSA.MultiTailMixture
