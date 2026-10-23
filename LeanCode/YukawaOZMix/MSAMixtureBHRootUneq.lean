/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRoot
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneqDefs
import LeanCode.YukawaOZMix.MSAMixtureLegacyFourier
import LeanCode.YukawaOZMix.MSAMixtureConcrete
import LeanCode.YukawaOZMix.MSAMixtureFactorization
import LeanCode.YukawaOZMix.MSAMixtureCoreUneq

/-!
# Kernel-checked unequal-diameter matrix closure recovery

Both former SymPy-supported declarations in this module are proved
standard-three theorems: matExactMSAUnequalDiam_hcore and
matHSexactUnequalDiam_kspace. The singleton bridge to the automatic finite
Wronskian theorem proves the actual matrix Gram relation; checked radial
integrability and the old piecewise convolution formulas split its DCF
into the original HS core, core correction and Yukawa tail.

The explicit physical domain requires z>0, k!=0, positive diameters,
nonnegative densities and positive vacMix; the nonlinear increment also
requires an actual BH root and symmetric K. These Fourier identities need
no weighted RDF decay budget, but do not establish g>=0, thermodynamic
route consistency or accurate Maxwell/binodal coexistence.
-/

open Real MeasureTheory
open FMSA.Q0Complex FMSA.ExactMSA FMSA.HardSphere FMSA.MatrixQ0 FMSA.MixtureOzStar

namespace MSAMixture

open scoped BigOperators

variable {N : ℕ}

/-! ### The unequal-σ closure-recovery theorem and MSAEMIX.1 at unequal diameter -/

/-- Original unequal-diameter coupling increment, proved from the actual
BH root, automatic Wronskian and faithful closed convolution formula. -/
theorem matExactMSAUnequalDiam_hcore (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K)
    (hz : 0 < z) (hk : k ≠ 0) (hsigma : ∀ l, 0 < σ l) (hrho : ∀ l, 0 ≤ rho l)
    (hvac : 0 < FMSA.MatrixQ0.vacMix rho σ) (hK : ∀ a b, K a b = K b a) (i j : Fin N) :
    (FtHSuneq z rho σ (Complex.I * k) * (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      + (Ft1uneq z rho σ Gt Dt (Complex.I * k)
          * (FtHSuneq z rho σ (-(Complex.I * k))).transpose) i j
      + (Ft1uneq z rho σ Gt Dt (Complex.I * k)
          * (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = -(Real.sqrt (rho i * rho j) : ℂ)
          * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
            + (radial_fourier (matMSAtail K z σ i j) k : ℂ))
 :=
  FMSA.ExactMSA.MultiTailMixture.legacyUnequal_hcore z hz rho σ Gt Dt K hsigma hrho
    hvac hroot hK k hk i j

/-- ⭐ **MSAEMIX.1 at unequal diameter.**  Given the unequal-σ hard-sphere symmetric factorization
`hHS` and the closure-recovery theorem at a `MixBHRootUneq`, the full MSA factorization holds:
`((F̃₀+F̃₁)(F̃₀ⁿ+F̃₁ⁿ)ᵀ)ᵢⱼ = δᵢⱼ − √(ρ_iρ_j)(ĉ_HS,ij + 𝓕[c_core]ᵢⱼ + 𝓕[c_tail]ᵢⱼ)`, the physical
unequal-σ MSA mixture DCF.  Pure algebra on the abstract `matMixtureFactorization_of_core` (√-weight
folded into the DCFs, `ρ := 1`), mirroring `matMSAmixture_equalDiam`. -/
theorem matMSAmixture_unequalDiam (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K)
    (hz : 0 < z) (hk : k ≠ 0) (hsigma : ∀ l, 0 < σ l) (hrho : ∀ l, 0 ≤ rho l)
    (hvac : 0 < FMSA.MatrixQ0.vacMix rho σ) (hK : ∀ a b, K a b = K b a) (cHShat : Fin N → Fin N → ℂ)
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
      have hc := matExactMSAUnequalDiam_hcore z rho σ Gt Dt K k hroot hz hk hsigma hrho hvac hK i j
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

/- The unequal-σ HS-mixture DCF transform in **Baxter-factor form** (no axiom): the `ftilde`
expansion of `F̃_HS(ik)·F̃_HS(−ik)ᵀ` gives it explicitly as
`√(ρᵢρⱼ)·(Q̂_HS,ij(ik) + Q̂_HS,ji(−ik) − Σₗ ρₗ Q̂_HS,il(ik)·Q̂_HS,jl(−ik))`. -/


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
HS DCF in Baxter-factor form `cHShatUneq`), so the only remaining input is the closure theorem
`matExactMSAUnequalDiam_hcore` at the `MixBHRootUneq` gate.  This mirrors how the equal-σ
`matMSAmixture_equalDiam_WH` removes the ad-hoc `hHS` — but here with NO Wiener–Hopf atoms
(`hKDEF`/`hbridge`/`hWH`): at unequal σ the HS factorization is free algebra, so `#print axioms`
uses only the standard three axioms. -/
theorem matMSAmixture_unequalDiam_of_hcore (z : ℝ) (rho σ : Fin N → ℝ) (hrho : ∀ l, 0 ≤ rho l)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K)
    (hz : 0 < z) (hk : k ≠ 0) (hsigma : ∀ l, 0 < σ l)
    (hvac : 0 < FMSA.MatrixQ0.vacMix rho σ) (hK : ∀ a b, K a b = K b a)
    (i j : Fin N) :
    ((FtHSuneq z rho σ (Complex.I * k) + Ft1uneq z rho σ Gt Dt (Complex.I * k))
        * (FtHSuneq z rho σ (-(Complex.I * k))
            + Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (cHShatUneq z rho σ k i j + (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
              + (radial_fourier (matMSAtail K z σ i j) k : ℂ))) :=
  matMSAmixture_unequalDiam z rho σ Gt Dt K k hroot hz hk hsigma hrho hvac hK (cHShatUneq z rho σ k)
    (fun i j => FtHSuneq_mul_transpose z rho σ hrho k i j) i j

/-! ### The physical `radial_fourier(Φ_HS)` form — the unequal-σ HS Wiener–Hopf identity -/

/- The physical unequal-σ **HS-mixture DCF** `Φ_HS,ij(r)` — the coupling-`0` (`W̃ = C̃ = 0`)
`matCoreUneq` at the HS Baxter amplitudes, `σ`-oriented (larger-diameter row) and cut off at `σ_ij`
(the HS DCF vanishes beyond contact; no Yukawa tail).  Real-space partner of `cHShatUneq`. -/


/-- The original HS Baxter-factor DCF equals the actual radial Fourier
transform of the closed HS core; the former SymPy-backed axiom is retired. -/
theorem matHSexactUnequalDiam_kspace (z : ℝ) (rho σ : Fin N → ℝ) (k : ℝ) (hz : 0 < z) (hk : k ≠ 0)
    (hsigma : ∀ l, 0 < σ l) (hrho : ∀ l, 0 ≤ rho l)
    (hvac : 0 < FMSA.MatrixQ0.vacMix rho σ) (i j : Fin N) :
    cHShatUneq z rho σ k i j
      = (Real.sqrt (rho i * rho j) : ℂ) * (radial_fourier (matCoreHSuneq z rho σ i j) k : ℂ)
 := by
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j)
    (FMSA.ExactMSA.MultiTailMixture.legacyHS_matrix_gram z hz rho σ hsigma hrho hvac k hk)
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply] at h
  have hb := FtHSuneq_mul_transpose z rho σ hrho k i j
  linear_combination hb - h

/-- ⭐⭐⭐ **MSAEMIX.1 at unequal σ in the physical `radial_fourier` form — matches the equal-σ
grade.**  Substituting the HS Baxter–Fourier identity `matHSexactUnequalDiam_kspace` into
`matMSAmixture_unequalDiam_of_hcore`, the full unequal-σ MSA mixture DCF is the radial Fourier
transform of a real-space function: HS core `Φ_HS` + increment core + Yukawa tail — the shape of the
equal-σ `matMSAmixture_equalDiam_WH`.  `#print axioms` uses only the standard three axioms; both increment and HS anchor are proved. -/
theorem matMSAmixture_unequalDiam_physical (z : ℝ) (rho σ : Fin N → ℝ) (hrho : ∀ l, 0 ≤ rho l)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K)
    (hz : 0 < z) (hk : k ≠ 0) (hsigma : ∀ l, 0 < σ l)
    (hvac : 0 < FMSA.MatrixQ0.vacMix rho σ) (hK : ∀ a b, K a b = K b a)
    (i j : Fin N) :
    ((FtHSuneq z rho σ (Complex.I * k) + Ft1uneq z rho σ Gt Dt (Complex.I * k))
        * (FtHSuneq z rho σ (-(Complex.I * k))
            + Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matCoreHSuneq z rho σ i j) k : ℂ)
              + (radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
              + (radial_fourier (matMSAtail K z σ i j) k : ℂ)) := by
  rw [matMSAmixture_unequalDiam_of_hcore z rho σ hrho Gt Dt K k hroot hz hk hsigma hvac hK i j,
    matHSexactUnequalDiam_kspace z rho σ k hz hk hsigma hrho hvac i j]
  ring

end MSAMixture
