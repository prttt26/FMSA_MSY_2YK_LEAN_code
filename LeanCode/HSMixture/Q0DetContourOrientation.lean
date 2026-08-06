/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureDetGeneralN
import LeanCode.HSMixture.MixtureNoSpinodal
import LeanCode.HSMixture.Q0MomentGeOne

/-!
# Baxter-determinant orientation for the contour integral (item (ii) of the `A(−iy)` wiring)

The eq (20) `A(−iy)` terms feed `[Q̂₀(−y)]⁻¹` to the contour-sum engine, whose `hc`/`hd` need the
determinant of the Baxter factor to be non-zero throughout the contour region — the **closed** upper
half-plane `Im y ≥ 0` (the diameter `[−R,R]` plus the upper arc).  This file matches the project's
two non-vanishing results to that region.

**Convention.**  The physical Baxter factor as a function of the Fourier variable `k` is
`Q̂₀(k) = Q0_mat_c_phys (I·k)` (the `q0_entry_c` kernel `e^{−ikσ}` = `e^{−s σ}` with `s = ik`;
cf. `BaxterRenewalDecay`/`Splitting` — `z = ik`).  The integrand's factor `[Q̂₀(−y)]⁻¹` therefore
has argument `Q0_mat_c_phys (I·(−y))`, whose real part is `Re(I·(−y)) = Im y`.  So:

* `Im y > 0` (open UHP) ↦ `Re > 0`: **`mixtureDet_pole_free_N`** (`det Q̂₀(I·z) ≠ 0` for `Im z < 0`,
  applied at `z = −y`) — `det_Q0_contour_ne_zero_of_im_pos`;
* `Im y = 0, y ≠ 0` (real axis) ↦ purely imaginary argument `I·(−y.re)`:
  **`pyhs_mixture_no_spinodal`** (`det Q̂₀(I·k) ≠ 0` for real `k ≠ 0`, the project's single physics
  axiom = "no spinodal / positive structure factor").

Together they give `det Q̂₀(−y) ≠ 0` on the closed UHP **minus the origin**
(`det_Q0_contour_ne_zero`).  The single remaining point `y = 0` is the `k = 0` **compressibility**
(`det Q̂₀(0)`, where the `q0_entry_c` kernel is `s = 0` junk): `det_Q0_contour_origin_ne_zero`
closes it via the *removable value* — if `det Q̂₀(s) → c` as `s → 0` then `Re c ≥ 1 > 0`.  This
needs **no physics axiom** (compressibility positivity is *proved* from `moment_key`), so the two
together cover the **whole** closed UHP (raw value off the origin, removable value at it).

**Axioms.**  Both results rest on exactly the two axioms `mixtureDet_pole_free_N` already uses — no
new axiom: the math axiom `zeroFree_lowerHalfPlane_of_homotopy` (argument principle / Hurwitz) *and*
the physics axiom `pyhs_mixture_no_spinodal` (which is the real-axis boundary datum of the pole-free
proof, so even the open-UHP `det_Q0_contour_ne_zero_of_im_pos` inherits it).

For `y ≠ 0` the argument `I·(−y) ≠ 0`, so the raw `Q0_mat_c_phys` and the entire representative
(`q0_entry_c_repr`) agree entrywise — the determinant statements here transfer to the representative
matrix used by the engine.
-/

namespace FMSA.MixtureGenN

open FMSA.MixtureNoSpinodal Filter Topology

/-- **Orientation on the open upper half-plane.**  `det Q̂₀(−y) ≠ 0` for `Im y > 0`, directly from
`mixtureDet_pole_free_N` at `z = −y` (`Im (−y) = −Im y < 0`).  Rests on the two pole-free axioms. -/
theorem det_Q0_contour_ne_zero_of_im_pos {N : ℕ} {σ ρ : Fin N → ℝ}
    (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i) (heta : FMSA.MatrixQ0.etaMix ρ σ < 1)
    {y : ℂ} (hy : 0 < y.im) :
    (Q0_mat_c_phys (Complex.I * (-y)) σ ρ).det ≠ 0 :=
  mixtureDet_pole_free_N hσ hρ heta (z := -y) (by rw [Complex.neg_im]; linarith)

/-- **Orientation on the closed upper half-plane minus the origin.**  `det Q̂₀(−y) ≠ 0` for
`Im y ≥ 0`, `y ≠ 0` — the open UHP by `mixtureDet_pole_free_N` and the real axis (`Im y = 0`) by
`pyhs_mixture_no_spinodal` (the no-spinodal physics axiom).  This is exactly the contour region the
engine's `hc`/`hd` require (the origin `y = 0` is the `k = 0` compressibility, a separate removable
point). -/
theorem det_Q0_contour_ne_zero {N : ℕ} {σ ρ : Fin N → ℝ}
    (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i) (heta : FMSA.MatrixQ0.etaMix ρ σ < 1)
    {y : ℂ} (hyim : 0 ≤ y.im) (hy0 : y ≠ 0) :
    (Q0_mat_c_phys (Complex.I * (-y)) σ ρ).det ≠ 0 := by
  rcases hyim.lt_or_eq with h | h
  · exact det_Q0_contour_ne_zero_of_im_pos hσ hρ heta h
  · -- real axis, y ≠ 0 ⇒ y.re ≠ 0 ⇒ purely imaginary argument I·(−y.re)
    have hyim0 : y.im = 0 := h.symm
    have hre : y.re ≠ 0 := fun hc => hy0 (by simp [Complex.ext_iff, hc, hyim0])
    have harg : Complex.I * (-y) = Complex.I * ((-y.re : ℝ) : ℂ) := by
      congr 1; apply Complex.ext <;> simp [hyim0]
    rw [harg]
    exact pyhs_mixture_no_spinodal hσ hρ heta (k := -y.re) (neg_ne_zero.mpr hre)

/-- At a real argument the physical complex Baxter matrix is the cast of the real one (general `N`).
The complex `q0_entry_c` kernel `e^{−sσ}` at `s = z` real is `e^{−zσ}` cast to `ℂ`. -/
theorem Q0_mat_c_phys_ofReal {N : ℕ} (z : ℝ) (σ ρ : Fin N → ℝ) :
    Q0_mat_c_phys (z : ℂ) σ ρ = (FMSA.MatrixQ0.Q0_mat_phys z σ ρ).map Complex.ofReal := by
  funext i j
  simp only [Q0_mat_c_phys, FMSA.MatrixQ0.Q0_mat_phys,
    FMSA.Q0Complex.Q0_mat_c, FMSA.MatrixQ0.Q0_mat, Matrix.map_apply,
    FMSA.Q0Complex.q0_entry_c, FMSA.MatrixQ0.q0_entry]
  split_ifs <;> push_cast [Complex.ofReal_exp] <;> ring

/-- **Orientation at the origin — the `k = 0` compressibility (no physics axiom).**  The remaining
contour point `y = 0` (i.e. `s = 0`), where the `q0_entry_c` kernel is Lean junk, is handled by the
*removable* value: if `det Q̂₀(s) → c` as `s → 0`, then `c ≠ 0` — in fact `Re c ≥ 1`, the `k = 0`
structure factor / isothermal compressibility.  Unlike `det_Q0_contour_ne_zero` (which needs the two
pole-free axioms on the real axis) this rests **only on proved algebra** (`Q0_mat_phys_det_ge_one_N`
⇐ `moment_key`): compressibility positivity is *proved*, not assumed — `pyhs_mixture_no_spinodal`
covers only `k ≠ 0`.  Together with `det_Q0_contour_ne_zero` this closes the **whole** closed upper
half-plane: the raw value is non-zero off the origin, the removable value is non-zero at it. -/
theorem det_Q0_contour_origin_ne_zero {N : ℕ} {σ ρ : Fin N → ℝ}
    (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i) (heta : FMSA.MatrixQ0.etaMix ρ σ < 1)
    {c : ℂ} (hc : Tendsto (fun s => (Q0_mat_c_phys s σ ρ).det) (𝓝[≠] (0:ℂ)) (𝓝 c)) :
    c ≠ 0 := by
  have hofR : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) :=
    FMSA.MatrixQ0.ofReal_tendsto_nhdsNE.mono_left (nhdsWithin_mono 0 (fun x hx =>
      Set.mem_compl_singleton_iff.mpr (ne_of_gt (Set.mem_Ioi.mp hx))))
  have hreal : Tendsto (fun z : ℝ => ((FMSA.MatrixQ0.Q0_mat_phys z σ ρ).det : ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 c) := by
    have hfe : (fun z : ℝ => ((FMSA.MatrixQ0.Q0_mat_phys z σ ρ).det : ℂ))
        = fun z : ℝ => (Q0_mat_c_phys (z : ℂ) σ ρ).det := by
      funext z
      rw [Q0_mat_c_phys_ofReal]
      exact RingHom.map_det Complex.ofRealHom (FMSA.MatrixQ0.Q0_mat_phys z σ ρ)
    rw [hfe]; exact hc.comp hofR
  have hvac : 0 < FMSA.MatrixQ0.vacMix ρ σ := by
    unfold FMSA.MatrixQ0.vacMix; linarith [heta]
  have h := (Complex.continuous_re.tendsto c).comp hreal
  have h1 : (1:ℝ) ≤ c.re := by
    refine ge_of_tendsto h ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Function.comp_apply, Complex.ofReal_re]
    exact FMSA.MatrixQ0.Q0_mat_phys_det_ge_one_N (Set.mem_Ioi.mp hz) hvac
      (fun i => (hρ i).le) hσ
  intro hc0
  rw [hc0, Complex.zero_re] at h1
  linarith

end FMSA.MixtureGenN
