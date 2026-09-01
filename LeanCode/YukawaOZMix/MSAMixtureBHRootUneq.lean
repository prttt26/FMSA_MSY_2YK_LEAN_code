/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRoot
import LeanCode.YukawaOZMix.MSAMixtureConcrete
import LeanCode.YukawaOZMix.MSAMixtureFactorization
import LeanCode.YukawaOZMix.MSAMixtureCoreUneq

/-!
# MSAEMIX.4 — the UNEQUAL-σ matrix `hcore` axiom (BH-root gated) and MSAEMIX.1 at unequal diameter

The unequal-σ analog of `MSAMixtureBHRoot.lean`.  The unequal-σ mixture Baxter factor `qhatMixCuneq` is
the Laplace transform of the real-space `Q_ij` (poly on `[λ_ij, σ_ij]` with the `λ_ij=(σ_j−σ_i)/2`
support shift and row width `σ_i`, plus the Yukawa tail); at equal σ (`σ_i=σ_j`) it collapses to the
equal-σ `qhatMixC` (`λ_ij=0`, common `σ`).  With the unequal-σ HS / MSA / increment factors, the
BH-root gate `MixBHRootUneq`, and the closure-recovery axiom `matExactMSAUnequalDiam_hcore` (whose
core is the exactly-derived, validated `MSAMixtureCoreUneq.matCoreUneq`), MSAEMIX.1 closes at unequal
diameter through the abstract `matMixtureFactorization_of_core` — mirroring `matMSAmixture_equalDiam`.
-/

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

/-! ### The unequal-σ closure-recovery axiom and MSAEMIX.1 at unequal diameter -/

/-- ⭐ **MSAEMIX.4 (axiom, unequal σ).**  At the unequal-σ MSA Blum–Høye root (`MixBHRootUneq`) the
Baxter product's coupling increment equals `−√(ρ_iρ_j)(𝓕[matCoreCorrUneq]ᵢⱼ + 𝓕[matMSAtail]ᵢⱼ)`
(the MSA−HS core increment).

**Certified** (`symbolic_{outer,inner}.py`, `verify_{outer,inner}.py`, parent repo): every per-piece
kernel of `matCoreUneq` is the EXACT closed form from the case-split-free symbolic-σ Baxter
convolution (σ_l-independent), reproducing the numerical convolution to `1e-14` on both pieces.  A
*physics-computation* axiom at the physical root (unequal-σ analog of
`matExactMSAEqualDiam_hcore`). -/
axiom matExactMSAUnequalDiam_hcore (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K) (i j : Fin N) :
    (FtHSuneq z rho σ (Complex.I * k) * (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      + (Ft1uneq z rho σ Gt Dt (Complex.I * k)
          * (FtHSuneq z rho σ (-(Complex.I * k))).transpose) i j
      + (Ft1uneq z rho σ Gt Dt (Complex.I * k)
          * (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = -(Real.sqrt (rho i * rho j) : ℂ)
          * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
            + (radial_fourier (matMSAtail K z σ i j) k : ℂ))

/-- ⭐ **MSAEMIX.1 at unequal diameter.**  Given the unequal-σ hard-sphere symmetric factorization
`hHS` and the closure-recovery axiom at a `MixBHRootUneq`, the full MSA factorization holds:
`((F̃₀+F̃₁)(F̃₀ⁿ+F̃₁ⁿ)ᵀ)ᵢⱼ = δᵢⱼ − √(ρ_iρ_j)(ĉ_HS,ij + 𝓕[c_core]ᵢⱼ + 𝓕[c_tail]ᵢⱼ)`, the physical
unequal-σ MSA mixture DCF.  Pure algebra on the abstract `matMixtureFactorization_of_core` (√-weight
folded into the DCFs, `ρ := 1`), mirroring `matMSAmixture_equalDiam`. -/
theorem matMSAmixture_unequalDiam (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K) (cHShat : Fin N → Fin N → ℂ)
    (hHS : ∀ i j, (FtHSuneq z rho σ (Complex.I * k)
        * (FtHSuneq z rho σ (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - cHShat i j) (i j : Fin N) :
    ((FtHSuneq z rho σ (Complex.I * k) + Ft1uneq z rho σ Gt Dt (Complex.I * k))
        * (FtHSuneq z rho σ (-(Complex.I * k))
            + Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (cHShat i j + (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
              + (radial_fourier (matMSAtail K z σ i j) k : ℂ))) := by
  have h := matMixtureFactorization_of_core (FtHSuneq z rho σ (Complex.I * k))
    (Ft1uneq z rho σ Gt Dt (Complex.I * k)) (FtHSuneq z rho σ (-(Complex.I * k)))
    (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))) 1 cHShat
    (fun i j => cHShat i j + (Real.sqrt (rho i * rho j) : ℂ)
      * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
        + (radial_fourier (matMSAtail K z σ i j) k : ℂ)))
    (by intro i j; simpa using hHS i j)
    (by
      intro i j
      have hc := matExactMSAUnequalDiam_hcore z rho σ Gt Dt K k hroot i j
      simpa using hc) i j
  simpa using h

/-! ### Discharging `hHS` at unequal σ by pure `ftilde` algebra (no axiom) -/

/-- **Pure `Matrix` algebra: the symmetric Baxter product in Baxter-factor form.**  For any complex
matrices `A`, `B` and nonnegative densities `ρ`,
`((F̃(A))·(F̃(B))ᵀ)ᵢⱼ = δᵢⱼ − √(ρᵢρⱼ)·(Aᵢⱼ + Bⱼᵢ − Σₗ ρₗ Aᵢₗ Bⱼₗ)`.  The cross term uses the
collapse `√(ρᵢρₗ)·√(ρⱼρₗ) = √(ρᵢρⱼ)·ρₗ` (needs `ρ ≥ 0`).  This is the algebraic heart of the
symmetric factorization — it holds for the HS factor `F̃_HS`, the MSA factor `F̃_MSA`, any `s`. -/
theorem ftilde_mul_transpose_apply (rho : Fin N → ℝ) (hrho : ∀ l, 0 ≤ rho l)
    (A B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ((ftilde rho A) * (ftilde rho B).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (Real.sqrt (rho i * rho j) : ℂ)
            * (A i j + B j i - ∑ l, (rho l : ℂ) * (A i l * B j l)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ftilde]
  have hterm : ∀ l, ((if i = l then (1:ℂ) else 0) - (Real.sqrt (rho i * rho l):ℂ) * A i l)
        * ((if j = l then (1:ℂ) else 0) - (Real.sqrt (rho j * rho l):ℂ) * B j l)
      = (if i = l then (1:ℂ) else 0) * (if j = l then (1:ℂ) else 0)
        - (if i = l then (1:ℂ) else 0) * ((Real.sqrt (rho j * rho l):ℂ) * B j l)
        - (Real.sqrt (rho i * rho l):ℂ) * A i l * (if j = l then (1:ℂ) else 0)
        + (Real.sqrt (rho i * rho l):ℂ) * A i l * ((Real.sqrt (rho j * rho l):ℂ) * B j l) := by
    intro l; ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs1 : (∑ l, (if i = l then (1:ℂ) else 0) * (if j = l then (1:ℂ) else 0))
      = (if i = j then (1:ℂ) else 0) := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i (fun l => if j = l then (1:ℂ) else 0)]
    simp only [Finset.mem_univ, if_true]
    by_cases h : i = j
    · subst h; simp
    · have h' : j ≠ i := fun hh => h hh.symm
      simp [h, h']
  have hs2 : (∑ l, (if i = l then (1:ℂ) else 0) * ((Real.sqrt (rho j * rho l):ℂ) * B j l))
      = (Real.sqrt (rho j * rho i):ℂ) * B j i := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i (fun l => (Real.sqrt (rho j * rho l):ℂ) * B j l)]
    simp
  have hs3 : (∑ l, (Real.sqrt (rho i * rho l):ℂ) * A i l * (if j = l then (1:ℂ) else 0))
      = (Real.sqrt (rho i * rho j):ℂ) * A i j := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j (fun l => (Real.sqrt (rho i * rho l):ℂ) * A i l)]
    simp
  have hs4 : (∑ l, (Real.sqrt (rho i * rho l):ℂ) * A i l
        * ((Real.sqrt (rho j * rho l):ℂ) * B j l))
      = (Real.sqrt (rho i * rho j):ℂ) * ∑ l, (rho l : ℂ) * (A i l * B j l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    have hsqrt : (Real.sqrt (rho i * rho l):ℂ) * (Real.sqrt (rho j * rho l):ℂ)
        = (Real.sqrt (rho i * rho j):ℂ) * (rho l : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      rw [← Real.sqrt_mul (mul_nonneg (hrho i) (hrho l)),
        show rho i * rho l * (rho j * rho l) = rho i * rho j * rho l ^ 2 by ring,
        Real.sqrt_mul (mul_nonneg (hrho i) (hrho j)), Real.sqrt_sq (hrho l)]
    calc (Real.sqrt (rho i * rho l):ℂ) * A i l * ((Real.sqrt (rho j * rho l):ℂ) * B j l)
        = ((Real.sqrt (rho i * rho l):ℂ) * (Real.sqrt (rho j * rho l):ℂ)) * (A i l * B j l) := by
          ring
      _ = ((Real.sqrt (rho i * rho j):ℂ) * (rho l : ℂ)) * (A i l * B j l) := by rw [hsqrt]
      _ = (Real.sqrt (rho i * rho j):ℂ) * ((rho l : ℂ) * (A i l * B j l)) := by ring
  rw [hs1, hs2, hs3, hs4, show (Real.sqrt (rho j * rho i):ℂ) = (Real.sqrt (rho i * rho j):ℂ) by
    rw [mul_comm]]
  ring

/-- The unequal-σ HS-mixture DCF transform in **Baxter-factor form** (no axiom): the `ftilde`
expansion of `F̃_HS(ik)·F̃_HS(−ik)ᵀ` gives it explicitly as
`√(ρᵢρⱼ)·(Q̂_HS,ij(ik) + Q̂_HS,ji(−ik) − Σₗ ρₗ Q̂_HS,il(ik)·Q̂_HS,jl(−ik))`. -/
noncomputable def cHShatUneq (z : ℝ) (rho σ : Fin N → ℝ) (k : ℝ) (i j : Fin N) : ℂ :=
  (Real.sqrt (rho i * rho j) : ℂ) *
    (qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (Complex.I * k) i j
      + qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (-(Complex.I * k)) j i
      - ∑ l, (rho l : ℂ)
          * (qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (Complex.I * k) i l
              * qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) (-(Complex.I * k)) j l))

/-- **`hHS` at unequal σ, DISCHARGED by pure `ftilde` algebra.**  `F̃_HS(ik)·F̃_HS(−ik)ᵀ = δ − Ĉ_HS`
with `Ĉ_HS = cHShatUneq` — no axiom, no Wiener–Hopf hypothesis; the HS symmetric factorization at
unequal σ is free `Matrix` algebra (only `ρ ≥ 0`). -/
theorem FtHSuneq_mul_transpose (z : ℝ) (rho σ : Fin N → ℝ) (hrho : ∀ l, 0 ≤ rho l) (k : ℝ)
    (i j : Fin N) :
    (FtHSuneq z rho σ (Complex.I * k)
        * (FtHSuneq z rho σ (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - cHShatUneq z rho σ k i j := by
  rw [FtHSuneq, FtHSuneq, ftilde_mul_transpose_apply rho hrho]
  simp only [cHShatUneq]

/-- ⭐⭐ **MSAEMIX.1 at unequal diameter, `hHS` DISCHARGED (no HS hypothesis).**  The hard-sphere
symmetric factorization is now supplied by the pure `ftilde`-algebra `FtHSuneq_mul_transpose` (the
HS DCF in Baxter-factor form `cHShatUneq`), so the only remaining input is the closure axiom
`matExactMSAUnequalDiam_hcore` at the `MixBHRootUneq` gate.  This mirrors how the equal-σ
`matMSAmixture_equalDiam_WH` removes the ad-hoc `hHS` — but here with NO Wiener–Hopf atoms
(`hKDEF`/`hbridge`/`hWH`): at unequal σ the HS factorization is free algebra, so `#print axioms`
carries only `matExactMSAUnequalDiam_hcore` (std-3 + the one physics axiom). -/
theorem matMSAmixture_unequalDiam_of_hcore (z : ℝ) (rho σ : Fin N → ℝ) (hrho : ∀ l, 0 ≤ rho l)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K)
    (i j : Fin N) :
    ((FtHSuneq z rho σ (Complex.I * k) + Ft1uneq z rho σ Gt Dt (Complex.I * k))
        * (FtHSuneq z rho σ (-(Complex.I * k))
            + Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (cHShatUneq z rho σ k i j + (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
              + (radial_fourier (matMSAtail K z σ i j) k : ℂ))) :=
  matMSAmixture_unequalDiam z rho σ Gt Dt K k hroot (cHShatUneq z rho σ k)
    (fun i j => FtHSuneq_mul_transpose z rho σ hrho k i j) i j

/-! ### The physical `radial_fourier(Φ_HS)` form — the unequal-σ HS Wiener–Hopf identity -/

/-- The physical unequal-σ **HS-mixture DCF** `Φ_HS,ij(r)` — the coupling-`0` (`W̃ = C̃ = 0`)
`matCoreUneq` at the HS Baxter amplitudes, `σ`-oriented (larger-diameter row) and cut off at `σ_ij`
(the HS DCF vanishes beyond contact; no Yukawa tail).  Real-space partner of `cHShatUneq`. -/
noncomputable def matCoreHSuneq (z : ℝ) (rho σ : Fin N → ℝ) (i j : Fin N) : ℝ → ℝ := fun r =>
  let a := if σ j ≤ σ i then i else j
  let b := if σ j ≤ σ i then j else i
  if r ≤ edgeHi σ i j then
    MSAMixtureCoreUneq.matCoreUneq z rho σ (A0Vec rho σ) (qp0Mat rho σ) 0 0 a b r
  else 0

/-- ⭐ **The unequal-σ HS Baxter–Fourier–Wiener–Hopf identity (sympy-backed axiom).**  The
Baxter-`Q̂`-combo HS DCF `cHShatUneq` equals `√(ρᵢρⱼ)·𝓕[Φ_HS]` — the radial Fourier transform of the
physical real-space HS-mixture DCF `matCoreHSuneq`.  I.e. the HS Baxter factorization's `k`-space
product is the transform of the real-space HS DCF: `Q̂_ij(ik)+Q̂_ji(−ik)−Σₗρₗ Q̂_il(ik)Q̂_jl(−ik) =
radial_fourier(Φ_HS,ij)`.  This is the coupling-`0` sibling of `matExactMSAUnequalDiam_hcore` (same
Baxter-Fourier class, `verify_{inner,outer}.py` / `msaemix_hcore_cert.py` at HS amps, `1e-14`);
the equal-σ analog is `matSF_of_baxterFourierWH` (scalar-σ, does not transfer to per-pair supports).
A direct Lean proof is the exactMSA-class ring, measured infeasible — hence the one named axiom. -/
axiom matHSexactUnequalDiam_kspace (z : ℝ) (rho σ : Fin N → ℝ) (k : ℝ) (i j : Fin N) :
    cHShatUneq z rho σ k i j
      = (Real.sqrt (rho i * rho j) : ℂ) * (radial_fourier (matCoreHSuneq z rho σ i j) k : ℂ)

/-- ⭐⭐⭐ **MSAEMIX.1 at unequal σ in the physical `radial_fourier` form — matches the equal-σ
grade.**  Substituting the HS Baxter–Fourier identity `matHSexactUnequalDiam_kspace` into
`matMSAmixture_unequalDiam_of_hcore`, the full unequal-σ MSA mixture DCF is the radial Fourier
transform of a real-space function: HS core `Φ_HS` + increment core + Yukawa tail — the shape of the
equal-σ `matMSAmixture_equalDiam_WH`.  `#print axioms` carries std-3 + the two Baxter-Fourier axioms
`matExactMSAUnequalDiam_hcore` (increment) and `matHSexactUnequalDiam_kspace` (HS anchor). -/
theorem matMSAmixture_unequalDiam_physical (z : ℝ) (rho σ : Fin N → ℝ) (hrho : ∀ l, 0 ≤ rho l)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K)
    (i j : Fin N) :
    ((FtHSuneq z rho σ (Complex.I * k) + Ft1uneq z rho σ Gt Dt (Complex.I * k))
        * (FtHSuneq z rho σ (-(Complex.I * k))
            + Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matCoreHSuneq z rho σ i j) k : ℂ)
              + (radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
              + (radial_fourier (matMSAtail K z σ i j) k : ℂ)) := by
  rw [matMSAmixture_unequalDiam_of_hcore z rho σ hrho Gt Dt K k hroot i j,
    matHSexactUnequalDiam_kspace z rho σ k i j]
  ring

end MSAMixture
