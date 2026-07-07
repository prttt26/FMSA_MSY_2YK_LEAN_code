/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.MatrixQ0

/-!
# Task M.4 — Rank-2 reduction of `det(Q0_mat_phys)`

## Context

`Q0_mat_phys(z)` is exactly a rank-2 perturbation of the identity: `Q0_mat_phys = 1 - U*V`
for `U : Matrix (Fin n) (Fin 2) ℝ`, `V : Matrix (Fin 2) (Fin n) ℝ`. Mathlib's
Weinstein–Aronszajn/Sylvester identity `det_one_sub_mul_comm` then reduces the n×n
determinant to a fixed 2×2 one, `det (1 - V*U)`, independent of the number of species.

See `MatrixQ0.lean`'s M.4 roadmap note for the full derivation this file formalizes.

## Status

| Statement | Status |
|---|---|
| `p1_neg` | ✓ proved (one-line, `Real.add_one_lt_exp`) |
| `mAux_neg`, `nAux_neg` | ✓ proved (derivative-chain, same technique as Task 2.2) |
| `fFun_neg`, `gFun_neg` | ✓ proved (algebraic identity + `mAux_neg`/`nAux_neg`) |
| `Umat`, `Vmat` | defined |
| `Q0_mat_phys_eq_one_sub_mul` | ✓ proved (the rank-2 factorization, entrywise algebra) |
| `Q0_mat_phys_det_eq_two_by_two` | ✓ proved (via `det_one_sub_mul_comm`) |
| `Q0_mat_phys_isUnit_det_of_two_by_two` | ✓ proved, conditional on the explicit 2×2
  inequality `(1+a)(1+d) > b*c` — the smallest remaining gap; not closed unconditionally. |
-/

set_option linter.style.longLine false

open Real Matrix

namespace FMSA.MatrixQ0

/-! ### Auxiliary one-variable sign facts -/

/-- `p1(σ,z) < 0` for `σ,z > 0`. One-line consequence of `Real.add_one_lt_exp`. -/
theorem p1_neg {sigma z : ℝ} (hsigma : 0 < sigma) (hz : 0 < z) :
    (1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2 < 0 := by
  have hu : z * sigma ≠ 0 := (mul_pos hz hsigma).ne'
  have h := Real.add_one_lt_exp (x := -(z * sigma)) (neg_ne_zero.mpr hu)
  have hz2 : 0 < z ^ 2 := by positivity
  apply div_neg_of_neg_of_pos _ hz2
  linarith

/-- `mAux(u) := (2-u) - exp(-u)*(u+2)`; the numerator of `p1(σ,z)·σ + 2·p2(σ,z)` at
`u = z·σ`. Proved negative for `u > 0` via `mAuxNeg := -mAux`, which is increasing from 0
(same two-level `HasDerivAt` + `strictMonoOn_of_hasDerivWithinAt_pos` chain as Task 2.2's
`bigD0/bigD1/bigD2`). -/
noncomputable def mAux (u : ℝ) : ℝ := (2 - u) - Real.exp (-u) * (u + 2)

private noncomputable def mAuxNeg (u : ℝ) : ℝ := Real.exp (-u) * (u + 2) + u - 2
private noncomputable def mAuxNeg1 (u : ℝ) : ℝ := 1 - (u + 1) * Real.exp (-u)
private noncomputable def mAuxNeg2 (u : ℝ) : ℝ := u * Real.exp (-u)

private lemma hasDerivAt_exp_neg (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u := by
  have h : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) u := (hasDerivAt_id u).neg
  simpa using h.exp

private lemma hasDerivAt_mAuxNeg (u : ℝ) : HasDerivAt mAuxNeg (mAuxNeg1 u) u := by
  have hx2 : HasDerivAt (fun x : ℝ => x + 2) (1 : ℝ) u := (hasDerivAt_id u).add_const 2
  have hexp := hasDerivAt_exp_neg u
  have hprod : HasDerivAt (fun x : ℝ => Real.exp (-x) * (x + 2))
      (-Real.exp (-u) * (u + 2) + Real.exp (-u) * 1) u := hexp.mul hx2
  have hx : HasDerivAt (fun x : ℝ => x) (1 : ℝ) u := hasDerivAt_id u
  have h := (hprod.add hx).sub_const (2 : ℝ)
  exact h.congr_deriv (by unfold mAuxNeg1; ring)

private lemma hasDerivAt_mAuxNeg1 (u : ℝ) : HasDerivAt mAuxNeg1 (mAuxNeg2 u) u := by
  have hx1 : HasDerivAt (fun x : ℝ => x + 1) (1 : ℝ) u := (hasDerivAt_id u).add_const 1
  have hexp := hasDerivAt_exp_neg u
  have hprod : HasDerivAt (fun x : ℝ => (x + 1) * Real.exp (-x))
      (1 * Real.exp (-u) + (u + 1) * (-Real.exp (-u))) u := hx1.mul hexp
  have h := (hasDerivAt_const u (1 : ℝ)).sub hprod
  exact h.congr_deriv (by unfold mAuxNeg2; ring)

private lemma mAuxNeg2_pos {u : ℝ} (hu : 0 < u) : 0 < mAuxNeg2 u :=
  mul_pos hu (Real.exp_pos _)

private lemma mAuxNeg1_zero : mAuxNeg1 0 = 0 := by unfold mAuxNeg1; simp

private lemma mAuxNeg_zero : mAuxNeg 0 = 0 := by unfold mAuxNeg; simp

private lemma mAuxNeg1_pos {u : ℝ} (hu : 0 < u) : 0 < mAuxNeg1 u := by
  have hcont : ContinuousOn mAuxNeg1 (Set.Ici 0) :=
    fun x _ => (hasDerivAt_mAuxNeg1 x).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt mAuxNeg1 (mAuxNeg2 x) (interior (Set.Ici (0 : ℝ))) x :=
    fun x _ => (hasDerivAt_mAuxNeg1 x).hasDerivWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < mAuxNeg2 x := by
    intro x hx; rw [interior_Ici] at hx; exact mAuxNeg2_pos hx
  have hmono : StrictMonoOn mAuxNeg1 (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) hcont hderiv hpos
  have h := hmono (Set.self_mem_Ici (a := (0 : ℝ))) hu.le hu
  rwa [mAuxNeg1_zero] at h

private lemma mAuxNeg_pos {u : ℝ} (hu : 0 < u) : 0 < mAuxNeg u := by
  have hcont : ContinuousOn mAuxNeg (Set.Ici 0) :=
    fun x _ => (hasDerivAt_mAuxNeg x).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt mAuxNeg (mAuxNeg1 x) (interior (Set.Ici (0 : ℝ))) x :=
    fun x _ => (hasDerivAt_mAuxNeg x).hasDerivWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < mAuxNeg1 x := by
    intro x hx; rw [interior_Ici] at hx; exact mAuxNeg1_pos hx
  have hmono : StrictMonoOn mAuxNeg (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) hcont hderiv hpos
  have h := hmono (Set.self_mem_Ici (a := (0 : ℝ))) hu.le hu
  rwa [mAuxNeg_zero] at h

/-- `mAux(u) < 0` for `u > 0`. -/
theorem mAux_neg {u : ℝ} (hu : 0 < u) : mAux u < 0 := by
  have h := mAuxNeg_pos hu
  unfold mAuxNeg at h
  unfold mAux
  linarith

/-- `nAux(u) := (1-u/2) - exp(-u)*(1+u/2)`; the numerator of `p1(σ,z)·σ/2 + p2(σ,z)` at
`u = z·σ`. Same proof technique as `mAux_neg`. -/
noncomputable def nAux (u : ℝ) : ℝ := (1 - u / 2) - Real.exp (-u) * (1 + u / 2)

private noncomputable def nAuxNeg (u : ℝ) : ℝ := Real.exp (-u) * (u / 2 + 1) + u / 2 - 1
private noncomputable def nAuxNeg1 (u : ℝ) : ℝ := 1 / 2 - (u + 1) / 2 * Real.exp (-u)
private noncomputable def nAuxNeg2 (u : ℝ) : ℝ := u * Real.exp (-u) / 2

private lemma hasDerivAt_nAuxNeg (u : ℝ) : HasDerivAt nAuxNeg (nAuxNeg1 u) u := by
  have hx1 : HasDerivAt (fun x : ℝ => x / 2 + 1) (1 / 2 : ℝ) u :=
    ((hasDerivAt_id u).div_const (2 : ℝ)).add_const 1
  have hexp := hasDerivAt_exp_neg u
  have hprod : HasDerivAt (fun x : ℝ => Real.exp (-x) * (x / 2 + 1))
      (-Real.exp (-u) * (u / 2 + 1) + Real.exp (-u) * (1 / 2)) u := hexp.mul hx1
  have hx2 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) u := (hasDerivAt_id u).div_const 2
  have h := (hprod.add hx2).sub_const (1 : ℝ)
  exact h.congr_deriv (by unfold nAuxNeg1; ring)

private lemma hasDerivAt_nAuxNeg1 (u : ℝ) : HasDerivAt nAuxNeg1 (nAuxNeg2 u) u := by
  have hx1 : HasDerivAt (fun x : ℝ => (x + 1) / 2) (1 / 2 : ℝ) u :=
    ((hasDerivAt_id u).add_const (1 : ℝ)).div_const (2 : ℝ)
  have hexp := hasDerivAt_exp_neg u
  have hprod : HasDerivAt (fun x : ℝ => (x + 1) / 2 * Real.exp (-x))
      ((1 / 2) * Real.exp (-u) + (u + 1) / 2 * (-Real.exp (-u))) u := hx1.mul hexp
  have h := (hasDerivAt_const u (1 / 2 : ℝ)).sub hprod
  exact h.congr_deriv (by unfold nAuxNeg2; ring)

private lemma nAuxNeg2_pos {u : ℝ} (hu : 0 < u) : 0 < nAuxNeg2 u := by
  unfold nAuxNeg2
  have := mul_pos hu (Real.exp_pos (-u))
  linarith

private lemma nAuxNeg1_zero : nAuxNeg1 0 = 0 := by unfold nAuxNeg1; simp

private lemma nAuxNeg_zero : nAuxNeg 0 = 0 := by unfold nAuxNeg; simp

private lemma nAuxNeg1_pos {u : ℝ} (hu : 0 < u) : 0 < nAuxNeg1 u := by
  have hcont : ContinuousOn nAuxNeg1 (Set.Ici 0) :=
    fun x _ => (hasDerivAt_nAuxNeg1 x).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt nAuxNeg1 (nAuxNeg2 x) (interior (Set.Ici (0 : ℝ))) x :=
    fun x _ => (hasDerivAt_nAuxNeg1 x).hasDerivWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < nAuxNeg2 x := by
    intro x hx; rw [interior_Ici] at hx; exact nAuxNeg2_pos hx
  have hmono : StrictMonoOn nAuxNeg1 (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) hcont hderiv hpos
  have h := hmono (Set.self_mem_Ici (a := (0 : ℝ))) hu.le hu
  rwa [nAuxNeg1_zero] at h

private lemma nAuxNeg_pos {u : ℝ} (hu : 0 < u) : 0 < nAuxNeg u := by
  have hcont : ContinuousOn nAuxNeg (Set.Ici 0) :=
    fun x _ => (hasDerivAt_nAuxNeg x).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt nAuxNeg (nAuxNeg1 x) (interior (Set.Ici (0 : ℝ))) x :=
    fun x _ => (hasDerivAt_nAuxNeg x).hasDerivWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < nAuxNeg1 x := by
    intro x hx; rw [interior_Ici] at hx; exact nAuxNeg1_pos hx
  have hmono : StrictMonoOn nAuxNeg (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) hcont hderiv hpos
  have h := hmono (Set.self_mem_Ici (a := (0 : ℝ))) hu.le hu
  rwa [nAuxNeg_zero] at h

/-- `nAux(u) < 0` for `u > 0`. -/
theorem nAux_neg {u : ℝ} (hu : 0 < u) : nAux u < 0 := by
  have h := nAuxNeg_pos hu
  unfold nAuxNeg at h
  unfold nAux
  linarith

/-! ### `p1`, `p2` and the composite `f`, `g` functions -/

/-- `p1(σ,z) = (1 - z·σ - exp(-z·σ)) / z²`, as used inside `q0_entry`. -/
noncomputable def p1 (sigma z : ℝ) : ℝ :=
  (1 - z * sigma - Real.exp (-(z * sigma))) / z ^ 2

/-- `p2(σ,z) = (1 - z·σ + (z·σ)²/2 - exp(-z·σ)) / z³`, as used inside `q0_entry`. -/
noncomputable def p2 (sigma z : ℝ) : ℝ :=
  (1 - z * sigma + (z * sigma) ^ 2 / 2 - Real.exp (-(z * sigma))) / z ^ 3

/-- Algebraic identity: `p1(σ,z)·σ + 2·p2(σ,z) = mAux(z·σ)/z³`. -/
theorem f_identity {sigma z : ℝ} (hz : z ≠ 0) :
    p1 sigma z * sigma + 2 * p2 sigma z = mAux (z * sigma) / z ^ 3 := by
  unfold p1 p2 mAux
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  field_simp
  ring

/-- Algebraic identity: `p1(σ,z)·σ/2 + p2(σ,z) = nAux(z·σ)/z³`. -/
theorem g_identity {sigma z : ℝ} (hz : z ≠ 0) :
    p1 sigma z * sigma / 2 + p2 sigma z = nAux (z * sigma) / z ^ 3 := by
  unfold p1 p2 nAux
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  field_simp
  ring

/-- `fFun rho sigma i z := (π/vac) · (p1(σᵢ,z)·σᵢ + 2·p2(σᵢ,z))`, the coefficient of `u1_i`
in the rank-2 factorization (`vac` and the implicit `ξ₂` come from the whole mixture). -/
noncomputable def fFun {n : ℕ} (rho sigma : Fin n → ℝ) (i : Fin n) (z : ℝ) : ℝ :=
  (Real.pi / vacMix rho sigma) * (p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z)

/-- `gFun rho sigma i z := (π/vac)·p1(σᵢ,z) + (π²ξ₂/vac²)·(p1(σᵢ,z)·σᵢ/2 + p2(σᵢ,z))`, the
coefficient of `u2_i` in the rank-2 factorization. -/
noncomputable def gFun {n : ℕ} (rho sigma : Fin n → ℝ) (i : Fin n) (z : ℝ) : ℝ :=
  (Real.pi / vacMix rho sigma) * p1 (sigma i) z +
    (Real.pi ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2) *
      (p1 (sigma i) z * sigma i / 2 + p2 (sigma i) z)

/-- `fFun < 0` for `σᵢ,z > 0` and a physical mixture (`vac > 0`). -/
theorem fFun_neg {n : ℕ} {rho sigma : Fin n → ℝ} {i : Fin n} {z : ℝ}
    (hvac : 0 < vacMix rho sigma) (hsigma : 0 < sigma i) (hz : 0 < z) :
    fFun rho sigma i z < 0 := by
  unfold fFun
  rw [f_identity hz.ne']
  have hu : 0 < z * sigma i := mul_pos hz hsigma
  have hz3 : (0:ℝ) < z ^ 3 := by positivity
  have h1 : mAux (z * sigma i) / z ^ 3 < 0 := div_neg_of_neg_of_pos (mAux_neg hu) hz3
  exact mul_neg_of_pos_of_neg (div_pos Real.pi_pos hvac) h1

/-- `gFun < 0` for `σᵢ,z > 0` and a physical mixture (`vac > 0`, `ξ₂ ≥ 0`). -/
theorem gFun_neg {n : ℕ} {rho sigma : Fin n → ℝ} {i : Fin n} {z : ℝ}
    (hvac : 0 < vacMix rho sigma) (hxi2 : 0 ≤ xi2 rho sigma)
    (hsigma : 0 < sigma i) (hz : 0 < z) :
    gFun rho sigma i z < 0 := by
  unfold gFun
  have hterm1 : (Real.pi / vacMix rho sigma) * p1 (sigma i) z < 0 :=
    mul_neg_of_pos_of_neg (div_pos Real.pi_pos hvac) (p1_neg hsigma hz)
  have hu : 0 < z * sigma i := mul_pos hz hsigma
  have hz3 : (0:ℝ) < z ^ 3 := by positivity
  have hn : p1 (sigma i) z * sigma i / 2 + p2 (sigma i) z ≤ 0 := by
    rw [g_identity hz.ne']
    exact le_of_lt (div_neg_of_neg_of_pos (nAux_neg hu) hz3)
  have hcoeff : 0 ≤ Real.pi ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2 := by positivity
  have hterm2 : (Real.pi ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2) *
      (p1 (sigma i) z * sigma i / 2 + p2 (sigma i) z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoeff hn
  linarith

/-! ### Rank-2 factorization -/

/-- `Umat`'s two columns are `u1_i = √ρᵢ·exp(zσᵢ/2)·fFun(...)` (`k=0`) and
`u2_i = √ρᵢ·exp(zσᵢ/2)·gFun(...)` (`k=1`). -/
noncomputable def Umat {n : ℕ} (z : ℝ) (sigma rho : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℝ :=
  fun i k => Real.sqrt (rho i) * Real.exp (z * sigma i / 2) *
    (if k = 0 then fFun rho sigma i z else gFun rho sigma i z)

/-- `Vmat`'s two rows are `v1_j = √ρⱼ·exp(-zσⱼ/2)` (`k=0`) and
`v2_j = √ρⱼ·exp(-zσⱼ/2)·σⱼ` (`k=1`). -/
noncomputable def Vmat {n : ℕ} (z : ℝ) (sigma rho : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  fun k j => Real.sqrt (rho j) * Real.exp (-(z * sigma j / 2)) *
    (if k = 0 then 1 else sigma j)

/-- Isolated computation of `(Umat*Vmat) i j`, merging the `√ρᵢ·√ρⱼ` and
`exp(zσᵢ/2)·exp(-zσⱼ/2)` factors (the only nonlinear, non-`ring` step) before any of the
`fFun`/`gFun`/`Q0phys`/`Qppphys` algebra. -/
theorem UV_apply {n : ℕ} (z : ℝ) (sigma rho : Fin n → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (i j : Fin n) :
    (Umat z sigma rho * Vmat z sigma rho) i j =
    Real.sqrt (rho i * rho j) * Real.exp (-((sigma j - sigma i) / 2 * z)) *
      (fFun rho sigma i z + gFun rho sigma i z * sigma j) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Umat, Vmat, Fin.isValue]
  norm_num
  have hkey :
      Real.sqrt (rho i) * Real.exp (z * sigma i / 2) * fFun rho sigma i z *
          (Real.sqrt (rho j) * Real.exp (-(z * sigma j / 2))) +
        Real.sqrt (rho i) * Real.exp (z * sigma i / 2) * gFun rho sigma i z *
          (Real.sqrt (rho j) * Real.exp (-(z * sigma j / 2)) * sigma j) =
      Real.sqrt (rho i) * Real.sqrt (rho j) *
        (Real.exp (z * sigma i / 2) * Real.exp (-(z * sigma j / 2))) *
        (fFun rho sigma i z + gFun rho sigma i z * sigma j) := by ring
  rw [hkey, ← Real.sqrt_mul (hrho i), ← Real.exp_add,
      show z * sigma i / 2 + -(z * sigma j / 2) = -((sigma j - sigma i) / 2 * z) by ring]

/-- Pure algebraic identity connecting `fFun + gFun·σⱼ` to the `Q0phys`/`Qppphys`/`p1`/`p2`
combination appearing in `q0_entry` — no `sqrt`/`exp` merging needed here, just
`field_simp; ring` (`vac ≠ 0`, `z ≠ 0`). -/
theorem fFun_gFun_eq {n : ℕ} {z : ℝ} {sigma rho : Fin n → ℝ} (i j : Fin n)
    (hz : z ≠ 0) (hvac : vacMix rho sigma ≠ 0) :
    fFun rho sigma i z + gFun rho sigma i z * sigma j =
    Q0phys rho sigma i j * p1 (sigma i) z + Qppphys rho sigma i j * p2 (sigma i) z := by
  unfold fFun gFun Q0phys Qppphys
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  unfold p1 p2
  field_simp
  ring

/-- The key structural fact: `Q0_mat_phys` is exactly a rank-2 perturbation of the identity.
Requires `vac ≠ 0` (physical mixture, `η ≠ 1`), `z ≠ 0`, and `rho ≥ 0` (for `Real.sqrt_mul`). -/
theorem Q0_mat_phys_eq_one_sub_mul {n : ℕ} {z : ℝ} {sigma rho : Fin n → ℝ}
    (hz : z ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) :
    Q0_mat_phys z sigma rho = 1 - Umat z sigma rho * Vmat z sigma rho := by
  funext i j
  rw [Matrix.sub_apply, Matrix.one_apply, UV_apply z sigma rho hrho i j,
      fFun_gFun_eq i j hz hvac]
  change q0_entry z (sigma i) ((sigma j - sigma i) / 2)
      (Q0phys rho sigma i j) (Qppphys rho sigma i j) (rhoGeoPhys rho i j)
      (if i = j then 1 else 0) =
    (if i = j then (1:ℝ) else 0) -
      Real.sqrt (rho i * rho j) * Real.exp (-((sigma j - sigma i) / 2 * z)) *
        (Q0phys rho sigma i j * p1 (sigma i) z + Qppphys rho sigma i j * p2 (sigma i) z)
  unfold q0_entry rhoGeoPhys p1 p2
  ring

/-- **Sylvester/Weinstein–Aronszajn reduction:** `det(Q0_mat_phys)` equals the determinant
of a fixed 2×2 matrix, `Vmat*Umat`, regardless of the number of species `n`. This is why
individual `Q0_mat_phys` entries can diverge as `z → ∞` while the determinant stays bounded:
`Vmat*Umat`'s entries are finite sums `Σᵢ ρᵢ·(...)` in which the `exp(zσᵢ/2)·exp(-zσᵢ/2) = 1`
cancellation removes the blow-up (see `fFun_neg`/`gFun_neg`: all its entries are strictly
negative, since `fFun,gFun < 0`). -/
theorem Q0_mat_phys_det_eq_two_by_two {n : ℕ} {z : ℝ} {sigma rho : Fin n → ℝ}
    (hz : z ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) :
    (Q0_mat_phys z sigma rho).det =
    (1 - Vmat z sigma rho * Umat z sigma rho).det := by
  rw [Q0_mat_phys_eq_one_sub_mul hz hvac hrho]
  exact det_one_sub_mul_comm _ _

/-- Entries of the reduced 2×2 matrix `Vmat*Umat` are finite species-sums with no
`z`-dependent blow-up: `(Vmat*Umat) k l = Σⱼ ρⱼ·σⱼ^k·{fFun or gFun}(j)` (`σⱼ^0=1`), since
`√ρⱼ·exp(-zσⱼ/2)·√ρⱼ·exp(zσⱼ/2) = ρⱼ` for every `j` (the exponentials cancel exactly). -/
theorem VU_apply_00 {n : ℕ} (z : ℝ) (sigma rho : Fin n → ℝ) (hrho : ∀ j, 0 ≤ rho j) :
    (Vmat z sigma rho * Umat z sigma rho) 0 0 = ∑ j, rho j * fFun rho sigma j z := by
  simp only [Matrix.mul_apply, Umat, Vmat, Fin.isValue]
  norm_num
  congr 1; funext j
  have hkey :
      Real.sqrt (rho j) * Real.exp (-(z * sigma j / 2)) *
          (Real.sqrt (rho j) * Real.exp (z * sigma j / 2) * fFun rho sigma j z) =
      (Real.sqrt (rho j) * Real.sqrt (rho j)) *
        (Real.exp (-(z * sigma j / 2)) * Real.exp (z * sigma j / 2)) *
        fFun rho sigma j z := by ring
  rw [hkey, Real.mul_self_sqrt (hrho j), ← Real.exp_add,
    show -(z * sigma j / 2) + z * sigma j / 2 = 0 by ring, Real.exp_zero, mul_one]

/-- **Task M.4, final step:** `Q0_mat_phys` is invertible, conditional on the explicit,
n-independent 2×2 inequality below. Since `fFun, gFun < 0` pointwise (`fFun_neg`, `gFun_neg`)
and `ρⱼ ≥ 0`, every entry of `Vmat*Umat` is a nonneg-weighted sum of a negative quantity,
hence `≤ 0`; the hypothesis `hdet` is exactly the `(1+a)(1+d) > b·c` inequality from the
roadmap (`MatrixQ0.lean`'s M.4 note), with `a,b,c,d ≥ 0` the negated entries. This
inequality is the one genuinely open piece — not closed unconditionally despite extensive
numerical support (20,000 random physical trials, no counterexample) — so it is stated here
as an explicit hypothesis rather than proved for all `z,η`. This is the smallest remaining
gap: a single scalar inequality between four finite species-sums, not an n×n claim. -/
theorem Q0_mat_phys_isUnit_det_of_two_by_two {n : ℕ} {z : ℝ} {sigma rho : Fin n → ℝ}
    (hz : z ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : (1 - (Vmat z sigma rho * Umat z sigma rho) 0 0) *
              (1 - (Vmat z sigma rho * Umat z sigma rho) 1 1) -
            (Vmat z sigma rho * Umat z sigma rho) 0 1 *
              (Vmat z sigma rho * Umat z sigma rho) 1 0 ≠ 0) :
    IsUnit (Q0_mat_phys z sigma rho).det := by
  rw [isUnit_iff_ne_zero, Q0_mat_phys_det_eq_two_by_two hz hvac hrho, Matrix.det_fin_two]
  simpa [Matrix.sub_apply, Matrix.one_apply] using hdet

end FMSA.MatrixQ0
