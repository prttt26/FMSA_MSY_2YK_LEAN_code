import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureCore
import LeanCode.YukawaOZMix.MSAMixtureFactorization

/-! Root and amplitude definitions, independent of closure certificates. -/

open Real MeasureTheory
open FMSA.Q0Complex FMSA.ExactMSA FMSA.HardSphere FMSA.MatrixQ0 FMSA.MixtureOzStar

namespace MSAMixture

variable {N : ℕ}

/-! ### The full mixture Baxter factor `Q̂(s)` (equal σ, with Yukawa tails) -/

/-- The full mixture Baxter factor `Q̂_ij(s)` at **equal σ** (`σ_i = σ`, `λ = 0`), complex `s`:
`φ₁(sσ)q'_ij + φ₂(sσ)A_j + W̃_ij/(s+z) + C̃_ij[e^{−sσ}/(s+z) + (1−e^{−sσ})/s]`, with
`φ₁(x)=(1−x−e^{−x})/s²`, `φ₂(x)=(1−x+x²/2−e^{−x})/s³` (the `q0_entry_c` Baxter poly plus the tails). -/
noncomputable def qhatMixC (z sigma : ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ)
    (s : ℂ) (i j : Fin N) : ℂ :=
  (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2 * (qp i j : ℂ)
    + (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3 * (Av j : ℂ)
    + (Wt i j : ℂ) / (s + z)
    + (Ct i j : ℂ) * (Complex.exp (-(s * sigma)) / (s + z)
        + (1 - Complex.exp (-(s * sigma))) / s)

/-- The full mixture Baxter factor at **real** `s` (for the (29′)/(33′) residual gate). -/
noncomputable def qhatMixR (z sigma : ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ)
    (s : ℝ) (i j : Fin N) : ℝ :=
  (1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2 * qp i j
    + (1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3 * Av j
    + Wt i j / (s + z)
    + Ct i j * (Real.exp (-(s * sigma)) / (s + z) + (1 - Real.exp (-(s * sigma))) / s)

/-! ### The MSA and hard-sphere amplitude bundles -/

/-- The MSA `q′` amplitude matrix. -/
noncomputable def qpMat (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => qpMSA z rho sigma Gt Dt i j

/-- The MSA `A` amplitude vector (column). -/
noncomputable def AVec (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Fin N → ℝ := fun j => AMSA z rho sigma Gt Dt j

/-- The HS `q^{0′}` amplitude matrix. -/
noncomputable def qp0Mat (rho sigma : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => Q0phys rho sigma i j

/-- The HS `A⁰` amplitude vector. -/
noncomputable def A0Vec (rho sigma : Fin N → ℝ) : Fin N → ℝ := fun j => Qppphys rho sigma j j

/-! ### The symmetric Baxter factor and its HS / MSA / increment instances -/

/-- The symmetric Baxter factor entry `F̃_ij(Q) = δ_ij − √(ρ_iρ_j) Q_ij`. -/
noncomputable def ftilde (rho : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then (1 : ℂ) else 0) - (Real.sqrt (rho i * rho j) : ℂ) * Q i j

/-- The hard-sphere symmetric factor at `s` (coupling-`0`: `W̃ = C̃ = 0`); `sig` is the common σ. -/
noncomputable def FtHS (z sig : ℝ) (rho sigma : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixC z sig (qp0Mat rho sigma) 0 0 (A0Vec rho sigma) s i j)

/-- The full MSA symmetric factor at `s`; `sig` is the common σ. -/
noncomputable def FtMSA (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixC z sig (qpMat z rho sigma Gt Dt)
    (Wt z rho Gt Dt) (Ct z rho sigma Gt Dt) (AVec z rho sigma Gt Dt) s i j)

/-- The coupling increment `Q₁ = F̃_MSA − F̃_HS`. -/
noncomputable def Ft1 (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  FtMSA z sig rho sigma Gt Dt s - FtHS z sig rho sigma s

/-! ### The Blum–Høye BH-root gate (equal σ) -/

/-- **The mixture MSA Blum–Høye root** (equal σ = `sig`): (29′) `Σ_l Dt_il(δ_lj − ρ_l Q̂_jl(z)) =
2πK_ij/z` and (33′) `2π Σ_l Gt_il(δ_lj − ρ_l Q̂_lj(z)) = (A_j + z q'_ij + ½z² C̃_ij)/z²`, with `Q̂` the
full MSA Baxter factor at `s = z` (`qhatMixR`).  The physical-solution gate — the matrix analog of the
scalar `h29`/`h33`; the `hcore` identity holds **only** at such a root. -/
def MixBHRoot (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, ∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * qhatMixR z sig (qpMat z rho sigma Gt Dt) (Wt z rho Gt Dt)
          (Ct z rho sigma Gt Dt) (AVec z rho sigma Gt Dt) z j l)
    = 2 * Real.pi * K i j / z)
  ∧ (∀ i j, 2 * Real.pi * ∑ l, Gt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * qhatMixR z sig (qpMat z rho sigma Gt Dt) (Wt z rho Gt Dt)
          (Ct z rho sigma Gt Dt) (AVec z rho sigma Gt Dt) z l j)
    = (AVec z rho sigma Gt Dt j + z * qpMat z rho sigma Gt Dt i j
        + z ^ 2 * Ct z rho sigma Gt Dt i j / 2) / z ^ 2)

end MSAMixture
