/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MatrixQ0

/-!
# Task M.4 — Rank-2 reduction of `det(Q0_mat_phys)`

## Context

`Q0_mat_phys(z)` is exactly a rank-2 perturbation of the identity: `Q0_mat_phys = 1 - U*V`
for `U : Matrix (Fin N) (Fin 2) ℝ`, `V : Matrix (Fin 2) (Fin N) ℝ`. Mathlib's
Weinstein–Aronszajn/Sylvester identity `det_one_sub_mul_comm` then reduces the N×N
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
noncomputable def fFun {N : ℕ} (rho sigma : Fin N → ℝ) (i : Fin N) (z : ℝ) : ℝ :=
  (Real.pi / vacMix rho sigma) * (p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z)

/-- `gFun rho sigma i z := (π/vac)·p1(σᵢ,z) + (π²ξ₂/vac²)·(p1(σᵢ,z)·σᵢ/2 + p2(σᵢ,z))`, the
coefficient of `u2_i` in the rank-2 factorization. -/
noncomputable def gFun {N : ℕ} (rho sigma : Fin N → ℝ) (i : Fin N) (z : ℝ) : ℝ :=
  (Real.pi / vacMix rho sigma) * p1 (sigma i) z +
    (Real.pi ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2) *
      (p1 (sigma i) z * sigma i / 2 + p2 (sigma i) z)

/-- `fFun < 0` for `σᵢ,z > 0` and a physical mixture (`vac > 0`). -/
theorem fFun_neg {N : ℕ} {rho sigma : Fin N → ℝ} {i : Fin N} {z : ℝ}
    (hvac : 0 < vacMix rho sigma) (hsigma : 0 < sigma i) (hz : 0 < z) :
    fFun rho sigma i z < 0 := by
  unfold fFun
  rw [f_identity hz.ne']
  have hu : 0 < z * sigma i := mul_pos hz hsigma
  have hz3 : (0:ℝ) < z ^ 3 := by positivity
  have h1 : mAux (z * sigma i) / z ^ 3 < 0 := div_neg_of_neg_of_pos (mAux_neg hu) hz3
  exact mul_neg_of_pos_of_neg (div_pos Real.pi_pos hvac) h1

/-- `gFun < 0` for `σᵢ,z > 0` and a physical mixture (`vac > 0`, `ξ₂ ≥ 0`). -/
theorem gFun_neg {N : ℕ} {rho sigma : Fin N → ℝ} {i : Fin N} {z : ℝ}
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

/-! ### Monotonicity route for the det inequality (Tasks M.5–M.8)

These four lemmas characterise the `(1+a)(1+d) > bc` gap: `bc ≥ ad` holds *always* (Task M.8),
so it is not Cauchy–Schwarz-closable — positivity must use the `1+a+d` slack. See
`numerical_notes/{theory,results}/q0_det_positivity.md`. -/

/-- **Task M.5.** `nAux u = mAux u / 2` (a ring identity), giving
`g/f = πξ₂/(2·vac) + z·pAux(zσ)/mAux(zσ)` (used in `gFun_ratio_eq`). -/
theorem nAux_eq_mAux_div_two (u : ℝ) : nAux u = mAux u / 2 := by
  unfold nAux mAux; ring

/-- **Task M.6.** `1 + u²/2 < cosh u` for `u > 0` (Mathlib has only `1 ≤ cosh` and an upper bound).
Proved by the same two-level `HasDerivAt` chain as `mAuxNeg`: on `h = cosh u − 1 − u²/2`,
`h(0)=0`, `h'=sinh−id` with `h'(0)=0`, and `h''=cosh−1 > 0`. -/
private noncomputable def coshGap (u : ℝ) : ℝ := Real.cosh u - 1 - u ^ 2 / 2
private noncomputable def coshGap1 (u : ℝ) : ℝ := Real.sinh u - u
private noncomputable def coshGap2 (u : ℝ) : ℝ := Real.cosh u - 1

private lemma hasDerivAt_coshGap (u : ℝ) : HasDerivAt coshGap (coshGap1 u) u := by
  have hcosh := Real.hasDerivAt_cosh u
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2 / 2) u u := by
    have h := (hasDerivAt_pow 2 u).div_const 2
    simpa using h
  have h := (hcosh.sub_const 1).sub hsq
  exact h.congr_deriv (by unfold coshGap1; ring)

private lemma hasDerivAt_coshGap1 (u : ℝ) : HasDerivAt coshGap1 (coshGap2 u) u := by
  have hsinh := Real.hasDerivAt_sinh u
  have h := hsinh.sub (hasDerivAt_id u)
  exact h.congr_deriv (by unfold coshGap2; simp)

private lemma coshGap2_pos {u : ℝ} (hu : 0 < u) : 0 < coshGap2 u := by
  have h : 1 < Real.cosh u := Real.one_lt_cosh.mpr hu.ne'
  unfold coshGap2; linarith

private lemma coshGap1_zero : coshGap1 0 = 0 := by unfold coshGap1; simp
private lemma coshGap_zero : coshGap 0 = 0 := by unfold coshGap; simp

private lemma coshGap1_pos {u : ℝ} (hu : 0 < u) : 0 < coshGap1 u := by
  have hcont : ContinuousOn coshGap1 (Set.Ici 0) :=
    fun x _ => (hasDerivAt_coshGap1 x).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt coshGap1 (coshGap2 x) (interior (Set.Ici (0 : ℝ))) x :=
    fun x _ => (hasDerivAt_coshGap1 x).hasDerivWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < coshGap2 x := by
    intro x hx; rw [interior_Ici] at hx; exact coshGap2_pos hx
  have hmono : StrictMonoOn coshGap1 (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) hcont hderiv hpos
  have h := hmono (Set.self_mem_Ici (a := (0 : ℝ))) hu.le hu
  rwa [coshGap1_zero] at h

private lemma coshGap_pos {u : ℝ} (hu : 0 < u) : 0 < coshGap u := by
  have hcont : ContinuousOn coshGap (Set.Ici 0) :=
    fun x _ => (hasDerivAt_coshGap x).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt coshGap (coshGap1 x) (interior (Set.Ici (0 : ℝ))) x :=
    fun x _ => (hasDerivAt_coshGap x).hasDerivWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < coshGap1 x := by
    intro x hx; rw [interior_Ici] at hx; exact coshGap1_pos hx
  have hmono : StrictMonoOn coshGap (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) hcont hderiv hpos
  have h := hmono (Set.self_mem_Ici (a := (0 : ℝ))) hu.le hu
  rwa [coshGap_zero] at h

theorem one_add_half_sq_lt_cosh {u : ℝ} (hu : 0 < u) : 1 + u ^ 2 / 2 < Real.cosh u := by
  have h := coshGap_pos hu
  unfold coshGap at h
  linarith

/-- Bare-`u` numerator `pAux(u) = 1 − u − e^{−u}` (= `z²·p1(σ,z)` at `u = zσ`). -/
noncomputable def pAux (u : ℝ) : ℝ := 1 - u - Real.exp (-u)

/-- The ratio `pAux(u)/mAux(u)` (= `g/f` up to the additive mixture constant, via M.5). -/
noncomputable def ratioPM (u : ℝ) : ℝ := pAux u / mAux u

private lemma hasDerivAt_pAux (u : ℝ) : HasDerivAt pAux (-1 + Real.exp (-u)) u := by
  have h := ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).sub (hasDerivAt_exp_neg u)
  exact h.congr_deriv (by ring)

private lemma hasDerivAt_mAux (u : ℝ) :
    HasDerivAt mAux (-1 + Real.exp (-u) * (u + 1)) u := by
  have h2 : HasDerivAt (fun x : ℝ => x + 2) (1 : ℝ) u := (hasDerivAt_id u).add_const 2
  have hprod : HasDerivAt (fun x : ℝ => Real.exp (-x) * (x + 2))
      (-Real.exp (-u) * (u + 2) + Real.exp (-u) * 1) u := (hasDerivAt_exp_neg u).mul h2
  have h := ((hasDerivAt_const u (2 : ℝ)).sub (hasDerivAt_id u)).sub hprod
  exact h.congr_deriv (by ring)

/-- The Wronskian `W = pAux'·mAux − pAux·mAux'` is negative on `(0,∞)`:
`eᵘ·W = u² − 2·cosh u + 2 < 0` by Task M.6. -/
private lemma wronskian_neg {u : ℝ} (hu : 0 < u) :
    (-1 + Real.exp (-u)) * mAux u - pAux u * (-1 + Real.exp (-u) * (u + 1)) < 0 := by
  set W := (-1 + Real.exp (-u)) * mAux u - pAux u * (-1 + Real.exp (-u) * (u + 1)) with hWdef
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hkey : Real.exp u * W = u ^ 2 - 2 * Real.cosh u + 2 := by
    rw [hWdef]; unfold mAux pAux; rw [Real.cosh_eq]
    linear_combination (2 - Real.exp (-u) + u ^ 2) * he
  have hlt : Real.exp u * W < 0 := by
    rw [hkey]; nlinarith [one_add_half_sq_lt_cosh hu]
  nlinarith [hlt, Real.exp_pos u]

/-- **Task M.7.** `pAux/mAux` is strictly decreasing on `(0,∞)`; its derivative sign is that of the
Wronskian `W`, and `eᵘ·W = u² − 2cosh u + 2 < 0` (Task M.6). -/
theorem ratioPM_strictAntiOn : StrictAntiOn ratioPM (Set.Ioi (0 : ℝ)) := by
  have hderiv : ∀ x ∈ interior (Set.Ioi (0 : ℝ)),
      HasDerivWithinAt ratioPM
        (((-1 + Real.exp (-x)) * mAux x - pAux x * (-1 + Real.exp (-x) * (x + 1)))
          / mAux x ^ 2) (interior (Set.Ioi (0 : ℝ))) x := by
    intro x hx
    rw [interior_Ioi] at hx
    exact ((hasDerivAt_pAux x).div (hasDerivAt_mAux x) (mAux_neg hx).ne).hasDerivWithinAt
  have hneg : ∀ x ∈ interior (Set.Ioi (0 : ℝ)),
      ((-1 + Real.exp (-x)) * mAux x - pAux x * (-1 + Real.exp (-x) * (x + 1)))
        / mAux x ^ 2 < 0 := by
    intro x hx
    rw [interior_Ioi] at hx
    have hne : mAux x ≠ 0 := (mAux_neg hx).ne
    have hden : 0 < mAux x ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (wronskian_neg hx) hden
  have hcont : ContinuousOn ratioPM (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact (((hasDerivAt_pAux x).div (hasDerivAt_mAux x)
      (mAux_neg hx).ne).continuousAt).continuousWithinAt
  exact strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0) hcont hderiv hneg

/-- `gFun = fFun · (πξ₂/(2vac) + z·ratioPM(zσ))` — the `g/f` factorisation (uses M.5). -/
private lemma gFun_ratio_eq {N : ℕ} {z : ℝ} {rho sigma : Fin N → ℝ} (i : Fin N)
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hsig : 0 < sigma i) :
    gFun rho sigma i z =
      fFun rho sigma i z *
        (Real.pi * xi2 rho sigma / (2 * vacMix rho sigma) + z * ratioPM (z * sigma i)) := by
  have hu : 0 < z * sigma i := mul_pos hz hsig
  have hmne : mAux (z * sigma i) ≠ 0 := (mAux_neg hu).ne
  have hmid : mAux (z * sigma i) = z ^ 3 * (p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z) := by
    rw [f_identity hz.ne']; field_simp
  have hpid : pAux (z * sigma i) = z ^ 2 * p1 (sigma i) z := by
    unfold pAux p1; field_simp
  have hden : p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z ≠ 0 := by
    intro h; rw [h, mul_zero] at hmid; exact hmne hmid
  rw [ratioPM, hpid, hmid]
  unfold gFun fFun
  field_simp
  ring

/-- For a `StrictAntiOn` `F` on `(0,∞)` and `a,b>0`, `(a−b)(F a − F b) ≤ 0`. -/
private lemma antiOn_mul_diff_nonpos {F : ℝ → ℝ} (hF : StrictAntiOn F (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : (a - b) * (F a - F b) ≤ 0 := by
  rcases lt_trichotomy a b with h | h | h
  · have hFb : F b < F a := hF (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) h
    nlinarith
  · simp [h]
  · have hFa : F a < F b := hF (Set.mem_Ioi.mpr hb) (Set.mem_Ioi.mpr ha) h
    nlinarith

/-- The cross term `(σₖ−σⱼ)·(fⱼgₖ − fₖgⱼ) ≤ 0` (uses M.5+M.7 via `gFun_ratio_eq`). -/
private lemma cross_nonpos {N : ℕ} {z : ℝ} {rho sigma : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma)
    (hsigma : ∀ i, 0 < sigma i) (j k : Fin N) :
    (sigma k - sigma j) *
      (fFun rho sigma j z * gFun rho sigma k z - fFun rho sigma k z * gFun rho sigma j z) ≤ 0 := by
  have hfj := fFun_neg hvac (hsigma j) hz
  have hfk := fFun_neg hvac (hsigma k) hz
  have hgj := gFun_ratio_eq j hz hvac (hsigma j)
  have hgk := gFun_ratio_eq k hz hvac (hsigma k)
  have hcross : fFun rho sigma j z * gFun rho sigma k z
        - fFun rho sigma k z * gFun rho sigma j z
      = fFun rho sigma j z * fFun rho sigma k z * z
          * (ratioPM (z * sigma k) - ratioPM (z * sigma j)) := by
    rw [hgj, hgk]; ring
  rw [hcross]
  have hff : 0 < fFun rho sigma j z * fFun rho sigma k z := mul_pos_of_neg_of_neg hfj hfk
  have hr : (z * sigma k - z * sigma j) * (ratioPM (z * sigma k) - ratioPM (z * sigma j)) ≤ 0 :=
    antiOn_mul_diff_nonpos ratioPM_strictAntiOn (mul_pos hz (hsigma k)) (mul_pos hz (hsigma j))
  nlinarith [hr, hff, hz, mul_pos hz (hsigma k), mul_pos hz (hsigma j)]

/-- **Task M.8.** `bc ≥ ad` universally: `(∑ⱼρⱼfⱼ)(∑ₖρₖσₖgₖ) ≤ (∑ⱼρⱼgⱼ)(∑ₖρₖσₖfₖ)`.
By Cauchy–Binet `ad − bc = ½ ∑ⱼₖ ρⱼρₖ(σₖ−σⱼ)(fⱼgₖ−fₖgⱼ)`, each summand `≤ 0` (`cross_nonpos`).
Turns M.4's informal "not Cauchy–Schwarz (bc can exceed ad)" into `bc ≥ ad` always. -/
theorem moment_ad_le_bc {N : ℕ} {z : ℝ} {rho sigma : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma)
    (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    (∑ j, rho j * fFun rho sigma j z) * (∑ k, rho k * sigma k * gFun rho sigma k z)
      ≤ (∑ j, rho j * gFun rho sigma j z) * (∑ k, rho k * sigma k * fFun rho sigma k z) := by
  set f := fun i => fFun rho sigma i z with hf
  set g := fun i => gFun rho sigma i z with hg
  have hS : (∑ j, rho j * f j) * (∑ k, rho k * sigma k * g k)
        - (∑ j, rho j * g j) * (∑ k, rho k * sigma k * f k)
      = ∑ j, ∑ k, rho j * rho k * sigma k * (f j * g k - f k * g j) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hP : (2 : ℝ) * (∑ j, ∑ k, rho j * rho k * sigma k * (f j * g k - f k * g j))
      = ∑ j, ∑ k, rho j * rho k * (sigma k - sigma j) * (f j * g k - f k * g j) := by
    rw [two_mul]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hPnonpos :
      (∑ j, ∑ k, rho j * rho k * (sigma k - sigma j) * (f j * g k - f k * g j)) ≤ 0 := by
    refine Finset.sum_nonpos (fun j _ => Finset.sum_nonpos (fun k _ => ?_))
    have hterm : rho j * rho k * (sigma k - sigma j) * (f j * g k - f k * g j)
        = (rho j * rho k) * ((sigma k - sigma j) * (f j * g k - f k * g j)) := by ring
    rw [hterm]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hrho j) (hrho k))
      (cross_nonpos hz hvac hsigma j k)
  nlinarith [hS, hP, hPnonpos]

/-! ### M.4 retirement — Route B kernel inequality (det ≥ 1)

Numerically-guided reduction (`verify_q0_det_positivity.py` `route_scout` + `route_b_*.py`):
`det ≥ 1 ⟺ bc − ad ≤ a + d`, which reduces (Cauchy–Binet, `vac`-free after the `ξ₂` terms cancel)
to a **per-pair** kernel, and after `u = zσⱼ, v = zσₖ` (the `z⁶` cancels) to the clean 2-variable
inequality `kernel_nonneg`.  With `M(u) := −mAux u ≥ 0`, `Q(u) := −pAux u ≥ 0`,
`R(u) := u²/2 − Q u ≥ 0`, the make-or-break identity is
`G(u,v) = M(u)·Φ(u,v) + M(v)·Φ(v,u)` with `Φ(u,v) = u·R(v) + v·Q(v) ≥ 0` — a manifestly-nonneg
sum-of-products (verified symbolically, `route_b_decomp.py`). -/

/-- `pAux(u) = 1 − u − e^{−u} ≤ 0` for all `u` (one line from `Real.add_one_le_exp`). -/
theorem pAux_nonpos (u : ℝ) : pAux u ≤ 0 := by
  have h := Real.add_one_le_exp (-u)
  unfold pAux; linarith

/-- `mAux(u) ≤ 0` for `u ≥ 0` (`mAux_neg` for `u > 0`, `mAux 0 = 0`). -/
theorem mAux_nonpos {u : ℝ} (hu : 0 ≤ u) : mAux u ≤ 0 := by
  rcases hu.lt_or_eq with h | h
  · exact (mAux_neg h).le
  · rw [← h]; simp [mAux]

/-- `R(u) = u²/2 + pAux u ≥ 0` for `u ≥ 0`: `R 0 = 0` and `R'(u) = u − 1 + e^{−u} ≥ 0`
(again `Real.add_one_le_exp`), so `R` is monotone on `[0,∞)`. -/
theorem half_sq_add_pAux_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ u ^ 2 / 2 + pAux u := by
  set R : ℝ → ℝ := fun x => x ^ 2 / 2 + pAux x with hRdef
  have hderiv : ∀ x, HasDerivAt R (x - 1 + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      have h := (hasDerivAt_pow 2 x).div_const 2
      simpa using h
    exact (h1.add (hasDerivAt_pAux x)).congr_deriv (by ring)
  have hcont : ContinuousOn R (Set.Ici 0) :=
    fun x _ => (hderiv x).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt R (x - 1 + Real.exp (-x)) (interior (Set.Ici (0 : ℝ))) x :=
    fun x _ => (hderiv x).hasDerivWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ x - 1 + Real.exp (-x) := by
    intro x _; have := Real.add_one_le_exp (-x); linarith
  have hmono : MonotoneOn R (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont hd hpos
  have h0 : R 0 = 0 := by simp [hRdef, pAux]
  have h := hmono (Set.self_mem_Ici (a := (0 : ℝ))) (Set.mem_Ici.mpr hu) hu
  rwa [h0] at h

/-- `Φ(u,v) = u·(v²/2 + pAux v) − v·pAux v` (`= u·R(v) + v·Q(v)`). -/
noncomputable def phiK (u v : ℝ) : ℝ := u * (v ^ 2 / 2 + pAux v) - v * pAux v

theorem phiK_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ phiK u v := by
  have hR := half_sq_add_pAux_nonneg hv
  have hQ : 0 ≤ -pAux v := neg_nonneg.mpr (pAux_nonpos v)
  have hsplit : phiK u v = u * (v ^ 2 / 2 + pAux v) + v * (-pAux v) := by unfold phiK; ring
  rw [hsplit]
  exact add_nonneg (mul_nonneg hu hR) (mul_nonneg hv hQ)

/-- **M.4 kernel (the crux).**  For `u, v ≥ 0`,
`(v−u)·(mAux v · pAux u − mAux u · pAux v) ≤ ½·u·v·(−v·mAux u − u·mAux v)`.
Proof: the RHS − LHS equals `(−mAux u)·Φ(u,v) + (−mAux v)·Φ(v,u)` (a polynomial identity in the four
`mAux/pAux` atoms), and each summand is a product of nonnegatives. -/
theorem kernel_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (1 / 2) * u * v * (-v * mAux u - u * mAux v)
      - (v - u) * (mAux v * pAux u - mAux u * pAux v) := by
  have hMu : 0 ≤ -mAux u := neg_nonneg.mpr (mAux_nonpos hu)
  have hMv : 0 ≤ -mAux v := neg_nonneg.mpr (mAux_nonpos hv)
  have hid : (1 / 2) * u * v * (-v * mAux u - u * mAux v)
        - (v - u) * (mAux v * pAux u - mAux u * pAux v)
      = (-mAux u) * phiK u v + (-mAux v) * phiK v u := by unfold phiK; ring
  rw [hid]
  exact add_nonneg (mul_nonneg hMu (phiK_nonneg hu hv)) (mul_nonneg hMv (phiK_nonneg hv hu))

/-- **Per-pair moment bound.**  `kernel_nonneg` at `u = z·σⱼ, v = z·σₖ`, divided by `z > 0`:
`(σₖ−σⱼ)·(mAux(zσₖ)pAux(zσⱼ) − mAux(zσⱼ)pAux(zσₖ)) ≤ −½z²σⱼσₖ(σₖ·mAux(zσⱼ) + σⱼ·mAux(zσₖ))`. -/
theorem momentPair_le {z : ℝ} (hz : 0 < z) {σj σk : ℝ} (hj : 0 < σj) (hk : 0 < σk) :
    (σk - σj) * (mAux (z * σk) * pAux (z * σj) - mAux (z * σj) * pAux (z * σk))
      ≤ -(1 / 2) * z ^ 2 * σj * σk * (σk * mAux (z * σj) + σj * mAux (z * σk)) := by
  have hK := kernel_nonneg (u := z * σj) (v := z * σk)
    (mul_nonneg hz.le hj.le) (mul_nonneg hz.le hk.le)
  have hEz :
      (1 / 2) * (z * σj) * (z * σk) * (-(z * σk) * mAux (z * σj) - (z * σj) * mAux (z * σk))
        - ((z * σk) - (z * σj)) *
            (mAux (z * σk) * pAux (z * σj) - mAux (z * σj) * pAux (z * σk))
      = z * (-(1 / 2) * z ^ 2 * σj * σk * (σk * mAux (z * σj) + σj * mAux (z * σk))
        - (σk - σj) * (mAux (z * σk) * pAux (z * σj) - mAux (z * σj) * pAux (z * σk))) := by
    ring
  rw [hEz] at hK
  nlinarith [hK, hz]

/-- `pAux(zσ) = z²·p1(σ,z)`. -/
theorem pAux_z_eq {z σ : ℝ} (hz : z ≠ 0) : pAux (z * σ) = z ^ 2 * p1 σ z := by
  unfold pAux p1; field_simp

/-- `mAux(zσ) = z³·(σ·p1 + 2·p2)` (= `f_identity` cleared). -/
theorem mAux_z_eq {z σ : ℝ} (hz : z ≠ 0) : mAux (z * σ) = z ^ 3 * (p1 σ z * σ + 2 * p2 σ z) := by
  rw [f_identity hz]; field_simp

/-- `fFun i = (π/vac)·mAux(zσᵢ)/z³`. -/
theorem fFun_eq_mAux {N : ℕ} {z : ℝ} (hz : z ≠ 0) {sigma rho : Fin N → ℝ} (i : Fin N) :
    fFun rho sigma i z = Real.pi / vacMix rho sigma * (mAux (z * sigma i) / z ^ 3) := by
  unfold fFun; rw [f_identity hz]

/-- **Per-pair bound in `fFun`/`gFun` form.**  From `momentPair_le` (via `hfg_cross`, the `ξ₂`-free
Cauchy–Binet cancellation `fₖgⱼ − fⱼgₖ = (π/vac)²/z⁵·(mAux(zσₖ)pAux(zσⱼ) − mAux(zσⱼ)pAux(zσₖ))`):
`(σₖ−σⱼ)(fₖgⱼ − fⱼgₖ) ≤ −½(π/vac)·σⱼσₖ(σₖfⱼ + σⱼfₖ)`. -/
theorem per_pair_f {N : ℕ} {z : ℝ} (hz : 0 < z) {sigma rho : Fin N → ℝ}
    (hvac : 0 < vacMix rho sigma) (j k : Fin N) (hj : 0 < sigma j) (hk : 0 < sigma k) :
    (sigma k - sigma j) *
        (fFun rho sigma k z * gFun rho sigma j z - fFun rho sigma j z * gFun rho sigma k z)
      ≤ -(1 / 2) * (Real.pi / vacMix rho sigma) * (sigma j * sigma k) *
          (sigma k * fFun rho sigma j z + sigma j * fFun rho sigma k z) := by
  have hz0 : z ≠ 0 := hz.ne'
  have hvac0 : vacMix rho sigma ≠ 0 := hvac.ne'
  have hcross : fFun rho sigma k z * gFun rho sigma j z
        - fFun rho sigma j z * gFun rho sigma k z
      = (Real.pi / vacMix rho sigma) ^ 2 / z ^ 5 *
          (mAux (z * sigma k) * pAux (z * sigma j) - mAux (z * sigma j) * pAux (z * sigma k)) := by
    rw [mAux_z_eq (σ := sigma k) hz0, mAux_z_eq (σ := sigma j) hz0,
        pAux_z_eq (σ := sigma j) hz0, pAux_z_eq (σ := sigma k) hz0]
    unfold fFun gFun
    field_simp
    ring
  have hscale : (0 : ℝ) ≤ (Real.pi / vacMix rho sigma) ^ 2 / z ^ 5 := by positivity
  calc (sigma k - sigma j) *
          (fFun rho sigma k z * gFun rho sigma j z - fFun rho sigma j z * gFun rho sigma k z)
      = (Real.pi / vacMix rho sigma) ^ 2 / z ^ 5 *
          ((sigma k - sigma j) *
            (mAux (z * sigma k) * pAux (z * sigma j) - mAux (z * sigma j) * pAux (z * sigma k))) := by
        rw [hcross]; ring
    _ ≤ (Real.pi / vacMix rho sigma) ^ 2 / z ^ 5 *
          (-(1 / 2) * z ^ 2 * sigma j * sigma k *
            (sigma k * mAux (z * sigma j) + sigma j * mAux (z * sigma k))) :=
        mul_le_mul_of_nonneg_left (momentPair_le hz hj hk) hscale
    _ = -(1 / 2) * (Real.pi / vacMix rho sigma) * (sigma j * sigma k) *
          (sigma k * fFun rho sigma j z + sigma j * fFun rho sigma k z) := by
        rw [fFun_eq_mAux hz0 j, fFun_eq_mAux hz0 k]; field_simp

/-- **M.4 key inequality (`det ≥ 1`).**  `bc − ad ≤ a + d`, i.e.
`(∑ρg)(∑ρσf) − (∑ρf)(∑ρσg) ≤ −(∑ρf) − (∑ρσg)`.  Sum of `per_pair_f` over `ρⱼρₖ ≥ 0`
(Cauchy–Binet ⇒ `bc − ad = ½∑∑ρⱼρₖ(σₖ−σⱼ)(fₖgⱼ − fⱼgₖ)`), giving `bc − ad ≤ D := −½(π/vac)ξ₂(∑ρσf)`,
then `D ≤ a + d` since `−(∑ρσg) = D + (π/vac)∑ρσ(−p1)` and `−(∑ρf), (π/vac)∑ρσ(−p1) ≥ 0`. -/
theorem moment_key {N : ℕ} {z : ℝ} (hz : 0 < z) {sigma rho : Fin N → ℝ}
    (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    (∑ j, rho j * gFun rho sigma j z) * (∑ k, rho k * sigma k * fFun rho sigma k z)
      - (∑ j, rho j * fFun rho sigma j z) * (∑ k, rho k * sigma k * gFun rho sigma k z)
      ≤ -(∑ j, rho j * fFun rho sigma j z) - (∑ k, rho k * sigma k * gFun rho sigma k z) := by
  set f := fun i => fFun rho sigma i z with hfdef
  set g := fun i => gFun rho sigma i z with hgdef
  set vac := vacMix rho sigma with hvacdef
  -- bc − ad = ½ ∑∑ ρⱼρₖ (σₖ−σⱼ)(fₖgⱼ − fⱼgₖ)
  have e1 : (∑ j, rho j * g j) * (∑ k, rho k * sigma k * f k)
        - (∑ j, rho j * f j) * (∑ k, rho k * sigma k * g k)
      = ∑ j, ∑ k, rho j * rho k * sigma k * (f k * g j - f j * g k) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have e2 : (2 : ℝ) * ∑ j, ∑ k, rho j * rho k * sigma k * (f k * g j - f j * g k)
      = ∑ j, ∑ k, rho j * rho k * (sigma k - sigma j) * (f k * g j - f j * g k) := by
    rw [two_mul]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  -- summed per-pair bound
  have hsum_le : ∑ j, ∑ k, rho j * rho k * (sigma k - sigma j) * (f k * g j - f j * g k)
      ≤ ∑ j, ∑ k, rho j * rho k *
          (-(1 / 2) * (Real.pi / vac) * (sigma j * sigma k) * (sigma k * f j + sigma j * f k)) := by
    refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
    have hpp := per_pair_f hz hvac j k (hsigma j) (hsigma k)
    have hρρ : 0 ≤ rho j * rho k := mul_nonneg (hrho j) (hrho k)
    nlinarith [mul_le_mul_of_nonneg_left hpp hρρ]
  -- ∑∑ of the per-pair RHS = −(π/vac)·ξ₂·(∑ρσf)  (= 2·D)
  have hRHS : ∑ j, ∑ k, rho j * rho k *
          (-(1 / 2) * (Real.pi / vac) * (sigma j * sigma k) * (sigma k * f j + sigma j * f k))
      = -(Real.pi / vac) * xi2 rho sigma * (∑ i, rho i * sigma i * f i) := by
    have hstep : ∀ j, ∑ k, rho j * rho k *
            (-(1 / 2) * (Real.pi / vac) * (sigma j * sigma k) * (sigma k * f j + sigma j * f k))
        = -(1 / 2) * (Real.pi / vac) *
            ((rho j * sigma j * f j) * (∑ k, rho k * sigma k ^ 2)
              + (rho j * sigma j ^ 2) * (∑ k, rho k * sigma k * f k)) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    unfold xi2
    ring
  have hbc_le : (∑ j, rho j * g j) * (∑ k, rho k * sigma k * f k)
        - (∑ j, rho j * f j) * (∑ k, rho k * sigma k * g k)
      ≤ -(1 / 2) * (Real.pi / vac) * xi2 rho sigma * (∑ i, rho i * sigma i * f i) := by
    rw [e1]
    have := hsum_le
    rw [hRHS] at this
    nlinarith [e2, this]
  -- D ≤ a + d
  have hf_np : ∑ j, rho j * f j ≤ 0 :=
    Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hrho j)
      (le_of_lt (fFun_neg (i := j) hvac (hsigma j) hz)))
  have hp1_np : ∑ k, rho k * sigma k * p1 (sigma k) z ≤ 0 :=
    Finset.sum_nonpos (fun k _ => mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hrho k) (hsigma k).le) (le_of_lt (p1_neg (hsigma k) hz)))
  have hsg : ∑ k, rho k * sigma k * g k
      = (1 / 2) * (Real.pi / vac) * xi2 rho sigma * (∑ i, rho i * sigma i * f i)
        + (Real.pi / vac) * (∑ k, rho k * sigma k * p1 (sigma k) z) := by
    have hgk : ∀ k, rho k * sigma k * g k
        = (Real.pi / vac) * (rho k * sigma k * p1 (sigma k) z)
          + (Real.pi ^ 2 * xi2 rho sigma / vac ^ 2) *
              (rho k * sigma k * (p1 (sigma k) z * sigma k / 2 + p2 (sigma k) z)) := by
      intro k; simp only [hgdef, gFun, ← hvacdef]; ring
    have hfk : ∀ i, rho i * sigma i * f i
        = (Real.pi / vac) * (rho i * sigma i * (p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z)) := by
      intro i; simp only [hfdef, fFun, ← hvacdef]; ring
    have hS : (∑ i, rho i * sigma i * f i)
        = (Real.pi / vac) *
            (∑ i, rho i * sigma i * (p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z)) := by
      rw [Finset.sum_congr rfl (fun i _ => hfk i), ← Finset.mul_sum]
    have hLHS : (∑ k, rho k * sigma k * g k)
        = (Real.pi / vac) * (∑ k, rho k * sigma k * p1 (sigma k) z)
          + (Real.pi ^ 2 * xi2 rho sigma / vac ^ 2) *
              (∑ k, rho k * sigma k * (p1 (sigma k) z * sigma k / 2 + p2 (sigma k) z)) := by
      rw [Finset.sum_congr rfl (fun k _ => hgk k), Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
    have hhalf : (∑ k, rho k * sigma k * (p1 (sigma k) z * sigma k / 2 + p2 (sigma k) z))
        = (1 / 2) * (∑ i, rho i * sigma i * (p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hLHS, hhalf, hS]
    have hvne : vac ≠ 0 := hvac.ne'
    field_simp
    ring
  have hDad : -(1 / 2) * (Real.pi / vac) * xi2 rho sigma * (∑ i, rho i * sigma i * f i)
      ≤ -(∑ j, rho j * f j) - (∑ k, rho k * sigma k * g k) := by
    rw [hsg]
    have hπvac : 0 < Real.pi / vac := div_pos Real.pi_pos hvac
    have : (Real.pi / vac) * (∑ k, rho k * sigma k * p1 (sigma k) z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hπvac.le hp1_np
    linarith
  exact le_trans hbc_le hDad

/-! ### Rank-2 factorization -/

/-- `Umat`'s two columns are `u1_i = √ρᵢ·exp(zσᵢ/2)·fFun(...)` (`k=0`) and
`u2_i = √ρᵢ·exp(zσᵢ/2)·gFun(...)` (`k=1`). -/
noncomputable def Umat {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) : Matrix (Fin N) (Fin 2) ℝ :=
  fun i k => Real.sqrt (rho i) * Real.exp (z * sigma i / 2) *
    (if k = 0 then fFun rho sigma i z else gFun rho sigma i z)

/-- `Vmat`'s two rows are `v1_j = √ρⱼ·exp(-zσⱼ/2)` (`k=0`) and
`v2_j = √ρⱼ·exp(-zσⱼ/2)·σⱼ` (`k=1`). -/
noncomputable def Vmat {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) : Matrix (Fin 2) (Fin N) ℝ :=
  fun k j => Real.sqrt (rho j) * Real.exp (-(z * sigma j / 2)) *
    (if k = 0 then 1 else sigma j)

/-- Isolated computation of `(Umat*Vmat) i j`, merging the `√ρᵢ·√ρⱼ` and
`exp(zσᵢ/2)·exp(-zσⱼ/2)` factors (the only nonlinear, non-`ring` step) before any of the
`fFun`/`gFun`/`Q0phys`/`Qppphys` algebra. -/
theorem UV_apply {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (i j : Fin N) :
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
theorem fFun_gFun_eq {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ} (i j : Fin N)
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
theorem Q0_mat_phys_eq_one_sub_mul {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
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
theorem Q0_mat_phys_det_eq_two_by_two {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : z ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) :
    (Q0_mat_phys z sigma rho).det =
    (1 - Vmat z sigma rho * Umat z sigma rho).det := by
  rw [Q0_mat_phys_eq_one_sub_mul hz hvac hrho]
  exact det_one_sub_mul_comm _ _

/-- Entries of the reduced 2×2 matrix `Vmat*Umat` are finite species-sums with no
`z`-dependent blow-up: `(Vmat*Umat) k l = Σⱼ ρⱼ·σⱼ^k·{fFun or gFun}(j)` (`σⱼ^0=1`), since
`√ρⱼ·exp(-zσⱼ/2)·√ρⱼ·exp(zσⱼ/2) = ρⱼ` for every `j` (the exponentials cancel exactly). -/
theorem VU_apply_00 {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) (hrho : ∀ j, 0 ≤ rho j) :
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
theorem Q0_mat_phys_isUnit_det_of_two_by_two {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : z ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : (1 - (Vmat z sigma rho * Umat z sigma rho) 0 0) *
              (1 - (Vmat z sigma rho * Umat z sigma rho) 1 1) -
            (Vmat z sigma rho * Umat z sigma rho) 0 1 *
              (Vmat z sigma rho * Umat z sigma rho) 1 0 ≠ 0) :
    IsUnit (Q0_mat_phys z sigma rho).det := by
  rw [isUnit_iff_ne_zero, Q0_mat_phys_det_eq_two_by_two hz hvac hrho, Matrix.det_fin_two]
  simpa [Matrix.sub_apply, Matrix.one_apply] using hdet

/-- General `Vmat*Umat` entry `(k,l)` as a species-sum (all four entries at once, `σⱼ^k`/`f‖g`). -/
theorem VU_apply' {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) (hrho : ∀ j, 0 ≤ rho j) (k l : Fin 2) :
    (Vmat z sigma rho * Umat z sigma rho) k l =
      ∑ j, rho j * (if k = 0 then 1 else sigma j) *
        (if l = 0 then fFun rho sigma j z else gFun rho sigma j z) := by
  simp only [Matrix.mul_apply, Umat, Vmat, Fin.isValue]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsq : Real.sqrt (rho j) * Real.sqrt (rho j) = rho j := Real.mul_self_sqrt (hrho j)
  have hexp : Real.exp (-(z * sigma j / 2)) * Real.exp (z * sigma j / 2) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hkey :
      Real.sqrt (rho j) * Real.exp (-(z * sigma j / 2)) * (if k = 0 then 1 else sigma j) *
        (Real.sqrt (rho j) * Real.exp (z * sigma j / 2) *
          (if l = 0 then fFun rho sigma j z else gFun rho sigma j z)) =
      Real.sqrt (rho j) * Real.sqrt (rho j) *
        (Real.exp (-(z * sigma j / 2)) * Real.exp (z * sigma j / 2)) *
        ((if k = 0 then 1 else sigma j) *
          (if l = 0 then fFun rho sigma j z else gFun rho sigma j z)) := by ring
  rw [hkey, hsq, hexp]; ring

/-- **Task M.4 — now a THEOREM (axiom retired).**  For a physical mixture (`0<z`, `η<1 ⇔ 0<vacMix`,
`0≤ρᵢ`, `0<σᵢ`) the reduced 2×2 determinant `det = (1+a)(1+d) − bc` is strictly positive — in fact
`det ≥ 1`.  Route B (numerically scouted by `verify_q0_det_positivity.py`): `det = 1 + (a+d) − (bc−ad)`,
and `moment_key` gives `bc − ad ≤ a + d`, so `det ≥ 1 > 0`.  The core is the elementary 2-variable
kernel `kernel_nonneg` (`G(u,v) = M(u)Φ(u,v) + M(v)Φ(v,u) ≥ 0`, `M = −mAux`, `Φ = u·R(v)+v·Q(v)`),
summed via `per_pair_f`.  Full derivation: `numerical_notes/…/q0_det_positivity.md`. -/
theorem Q0_moment_det_pos {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 < sigma i) :
    0 < (1 - (Vmat z sigma rho * Umat z sigma rho) 0 0) *
          (1 - (Vmat z sigma rho * Umat z sigma rho) 1 1) -
        (Vmat z sigma rho * Umat z sigma rho) 0 1 *
          (Vmat z sigma rho * Umat z sigma rho) 1 0 := by
  have h00 : (Vmat z sigma rho * Umat z sigma rho) 0 0 = ∑ j, rho j * fFun rho sigma j z := by
    rw [VU_apply' z sigma rho hrho]; simp
  have h01 : (Vmat z sigma rho * Umat z sigma rho) 0 1 = ∑ j, rho j * gFun rho sigma j z := by
    rw [VU_apply' z sigma rho hrho]; simp
  have h10 : (Vmat z sigma rho * Umat z sigma rho) 1 0
      = ∑ k, rho k * sigma k * fFun rho sigma k z := by
    rw [VU_apply' z sigma rho hrho]; simp
  have h11 : (Vmat z sigma rho * Umat z sigma rho) 1 1
      = ∑ k, rho k * sigma k * gFun rho sigma k z := by
    rw [VU_apply' z sigma rho hrho]; simp
  rw [h00, h01, h10, h11]
  nlinarith [moment_key hz hvac hrho hsigma]

/-- **Task M.4 (unconditional) — and Task M.3 (unconditional).** `Q0_mat_phys` is invertible for
every physical mixture, from `Q0_moment_det_pos`. This is the unconditional `det(Q̂₀) ≠ 0` that M.3
sought (no diagonal-dominance side hypothesis — see `MatrixQ0.lean`'s conditional
`Q0_mat_phys_isUnit_det_of_diag_dom`) *and* the unconditional M.4. Depends on the `Q0_moment_det_pos`
axiom; retiring that axiom makes this theorem axiom-clean. -/
theorem Q0_mat_phys_isUnit_det {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 < sigma i) :
    IsUnit (Q0_mat_phys z sigma rho).det :=
  Q0_mat_phys_isUnit_det_of_two_by_two hz.ne' hvac.ne' hrho
    (Q0_moment_det_pos hz hvac hrho hsigma).ne'

end FMSA.MatrixQ0
