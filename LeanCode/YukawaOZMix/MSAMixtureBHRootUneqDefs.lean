import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRootDefs
import LeanCode.YukawaOZMix.MSAMixtureConcrete
import LeanCode.YukawaOZMix.MSAMixtureFactorization
import LeanCode.YukawaOZMix.MSAMixtureCoreUneq

/-! Unequal-diameter root and Fourier definitions independent of closure certificates. -/

open Real MeasureTheory
open FMSA.Q0Complex FMSA.ExactMSA FMSA.HardSphere FMSA.MatrixQ0 FMSA.MixtureOzStar

namespace MSAMixture

open scoped BigOperators

variable {N : ℕ}

/-! ### The unequal-σ mixture Baxter factor -/

/-- The unequal-σ mixture Baxter factor entry `∫₀^∞ Q_ij(r) e^{−sr} dr`, `λ_ij=(σ_j−σ_i)/2`,
`σ_ij=(σ_i+σ_j)/2`, row width `a=σ_i`.  Reduces to `qhatMixC z σ …` at equal σ. -/
noncomputable def qhatMixCuneq (z : ℝ) (σ : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (Av : Fin N → ℝ) (s : ℂ) (i j : Fin N) : ℂ :=
  let lam : ℂ := (((σ j - σ i) / 2 : ℝ) : ℂ)
  let a : ℂ := ((σ i : ℝ) : ℂ)
  let sij : ℂ := (((σ i + σ j) / 2 : ℝ) : ℂ)
  Complex.exp (-(s * lam)) * ((1 - s * a - Complex.exp (-(s * a))) / s ^ 2 * (qp i j : ℂ)
      + (1 - s * a + (s * a) ^ 2 / 2 - Complex.exp (-(s * a))) / s ^ 3 * (Av j : ℂ)
      + (Wt i j : ℂ) / (s + z)
      + (Ct i j : ℂ) * ((1 - Complex.exp (-(s * a))) / s))
    + (Ct i j : ℂ) * (Complex.exp (-(s * sij)) / (s + z))

/-- Real-`s` version of `qhatMixCuneq` (for the (29′)/(33′) residual gate). -/
noncomputable def qhatMixRuneq (z : ℝ) (σ : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (Av : Fin N → ℝ) (s : ℝ) (i j : Fin N) : ℝ :=
  let lam := (σ j - σ i) / 2
  let a := σ i
  let sij := (σ i + σ j) / 2
  Real.exp (-(s * lam)) * ((1 - s * a - Real.exp (-(s * a))) / s ^ 2 * qp i j
      + (1 - s * a + (s * a) ^ 2 / 2 - Real.exp (-(s * a))) / s ^ 3 * Av j
      + Wt i j / (s + z)
      + Ct i j * ((1 - Real.exp (-(s * a))) / s))
    + Ct i j * (Real.exp (-(s * sij)) / (s + z))

/-! ### Unequal-σ HS / MSA / increment symmetric factors -/

/-- Unequal-σ hard-sphere symmetric factor (coupling 0: `W̃ = C̃ = 0`). -/
noncomputable def FtHSuneq (z : ℝ) (rho σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) s i j)

/-- Unequal-σ full MSA symmetric factor. -/
noncomputable def FtMSAuneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixCuneq z σ (qpMat z rho σ Gt Dt) (Wt z rho Gt Dt)
    (Ct z rho σ Gt Dt) (AVec z rho σ Gt Dt) s i j)

/-- Unequal-σ coupling increment `Q₁ = F̃_MSA − F̃_HS`. -/
noncomputable def Ft1uneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ := FtMSAuneq z rho σ Gt Dt s - FtHSuneq z rho σ s

/-- The unequal-σ **core-DCF correction** = `matCoreUneq` at the MSA amplitudes minus at the HS
amplitudes (`qp0, A0, Wt=Ct=0`).  Kernels are σ_l-free (shared by MSA and HS) so this is exactly the
MSA−HS increment core (the exp part has no HS piece).  Unequal-σ analog of `matMSACoreCorr`. -/
noncomputable def matCoreCorrUneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ → ℝ := fun r =>
  -- orient by σ (larger-diameter row; `c` symmetric) so this is correct for BOTH `(i,j)` orderings,
  -- and cut off at `σ_ij` (exterior = tail `matMSAtail`; `radial_fourier` must stop there).
  let a := if σ j ≤ σ i then i else j
  let b := if σ j ≤ σ i then j else i
  if r ≤ edgeHi σ i j then
    MSAMixtureCoreUneq.matCoreUneq z rho σ (AVec z rho σ Gt Dt) (qpMat z rho σ Gt Dt)
        (Wt z rho Gt Dt) (Ct z rho σ Gt Dt) a b r
      - MSAMixtureCoreUneq.matCoreUneq z rho σ (A0Vec rho σ) (qp0Mat rho σ) 0 0 a b r
  else 0

/-! ### The unequal-σ BH-root gate -/

/-- The unequal-σ mixture MSA Blum–Høye root, with the **recentered** Baxter transform on **both**
conjuncts — the σ-edge FINDING.  Numerically **confirmed to machine precision** (`1.7e-16` on (29′),
`3.6e-15` on (33′)) at a physical unequal-σ root against the validated solver `msa_exact_mix.py`
(whose `_residuals` passes the Tang & Lu gate at `σ₂/σ₁ = 1.5`); the bare form (no recentering) misses
(33′) by `≈5`.

* **c-side (29′)** carries `e^{z·edgeLo σ j l}·Q̂_jl` (= `e^{−z(σ_j−σ_l)/2}·Q̂_jl`); this is also the
  OZ/Baxter-derived (♦) (`FMSA.ExactMSA.MixLeg3.c_side_constraint_of_exterior` /
  `mixBHRootUneq_cSide_of_exterior`).
* **g-side (33′)** carries `e^{z·edgeLo σ l j}·Q̂_lj` (= `e^{+z(σ_j−σ_l)/2}·Q̂_lj`) — **opposite sign,
  transposed `Q̂` index**.  The two descend from Baxter's Eq (8) `D(I − PQ̂ᵀ)` and Eq (32) `2πĝ(I − PQ̂)`
  respectively; the sign/index difference is real (invisible at `N=1`).  (The factor may be written on
  `Q̂` alone or on the whole bracket `δ_lj − ρ_l·Q̂` — identical, since it is `1` at `l = j`.)

At **equal** σ all `edgeLo = 0`, so both factors are `1` and this collapses to the naive form.  The
physical-solution gate (no `∀ i, σ i = sig` constraint). -/
def MixBHRootUneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, ∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * (Real.exp (z * edgeLo σ j l)
          * qhatMixRuneq z σ (qpMat z rho σ Gt Dt) (Wt z rho Gt Dt) (Ct z rho σ Gt Dt)
              (AVec z rho σ Gt Dt) z j l))
    = 2 * Real.pi * K i j / z)
  ∧ (∀ i j, 2 * Real.pi * ∑ l, Gt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * (Real.exp (z * edgeLo σ l j)
          * qhatMixRuneq z σ (qpMat z rho σ Gt Dt) (Wt z rho Gt Dt) (Ct z rho σ Gt Dt)
              (AVec z rho σ Gt Dt) z l j))
    = (AVec z rho σ Gt Dt j + z * qpMat z rho σ Gt Dt i j
        + z ^ 2 * Ct z rho σ Gt Dt i j / 2) / z ^ 2)

noncomputable def cHShatUneq (z : ℝ) (rho σ : Fin N → ℝ) (k : ℝ) (i j : Fin N) : ℂ :=
  (Real.sqrt (rho i * rho j) : ℂ) *
    (qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (Complex.I * k) i j
      + qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (-(Complex.I * k)) j i
      - ∑ l, (rho l : ℂ)
          * (qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (Complex.I * k) i l
              * qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (-(Complex.I * k)) j l))

noncomputable def matCoreHSuneq (z : ℝ) (rho σ : Fin N → ℝ) (i j : Fin N) : ℝ → ℝ := fun r =>
  let a := if σ j ≤ σ i then i else j
  let b := if σ j ≤ σ i then j else i
  if r ≤ edgeHi σ i j then
    MSAMixtureCoreUneq.matCoreUneq z rho σ (A0Vec rho σ) (qp0Mat rho σ) 0 0 a b r
  else 0

end MSAMixture
