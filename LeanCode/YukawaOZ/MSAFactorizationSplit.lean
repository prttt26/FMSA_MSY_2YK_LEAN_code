/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterWienerHopf

/-!
# MSAEXACT.1 — splitting the factorization off the hard-sphere one

Group **MSAEXACT** (`proof_notes_msa_exact.md`).  Continues the down-payment of
`MSABaxterTransform.lean`.

**The obstacle, restated.**  `HardSphere/BaxterWienerHopf.baxter_wiener_hopf_factorization` is not
general in `q`: it is proved *for* `q0_poly` and `c_HS`, from their explicit cos/sin transforms plus
`field_simp; ring`.  So MSAEXACT.1 cannot be a corollary of it — it has to redo the same computation
with the Yukawa tails.  This file does the half that is structure rather than grind, and leaves the
other half explicitly named.

**The split.**  The MSA Baxter function is `q_MSA = q0_poly + D·e^{−zr}` on the core, so its cos and
sin transforms are the hard-sphere ones plus `D` times the exponential transforms.  The
factorization's left side is then, *identically*,

    (1 − Re)² + Im²  =  [(1 − Re₀)² + Im₀²]                          ← the hard-sphere factorization
                        − 2D·[ (1 − Re₀)·Rez − Im₀·Imz ]             ← linear in the tail amplitude
                        + D²·[ Rez² + Imz² ]                         ← quadratic

with `Re₀, Im₀` the hard-sphere transforms and `Rez, Imz` the exponential ones.  The first
  bracket is
`1 − ρĉ_HS(k)` by BAXTER.3.  ⭐ So **MSAEXACT.1 reduces to matching the `O(D)` and `O(D²)` increments
against `−ρ·(ĉ_MSA − ĉ_HS)(k)`** — which is exactly the content of Waisman's Eq. (3), rather than a
fresh factorization.  That is a sharper target than "re-run BAXTER", and it is what `msa_lhs_split`
below states.

The quadratic coefficient closes in the same breath: `Rez² + Imz²` is the squared modulus of a
  single
exponential integral, `msa_exp_sq_modulus`.

## Results

* `exp_cos_integral`, `exp_sin_integral` — the two transforms the `q`-side was missing.  These are
  the "new integral formulas (exp×cos/sin)" the source note flags; proved by FTC.
* `msa_exp_sq_modulus` — `Rez² + Imz² = (1 − 2e^{−zσ}cos kσ + e^{−2zσ})/(z²+k²)`.
* ⭐ `msa_lhs_split` — the identity above, reducing MSAEXACT.1 to the `O(D)`/`O(D²)` match.
* `msa_lhs_split_at_zero` — at `D = 0` it collapses to BAXTER.3, i.e. `1 − ρĉ_HS(k)`.

⚠ **What is still open.**  The `c`-side: `ĉ_MSA(k)` requires Waisman's inner Eq. (2) (five terms,
including the `v²(cosh zr − 1)/r` piece whose missing `1/x` is the print error of theory note §7e)
plus the exterior Yukawa tail.  Matching it against the two increments is the remaining grind of
MSAEXACT.1, and it is not attempted here.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.MSAExact

/-- `∫₀^σ e^{−zr}cos(kr) dr = [z − e^{−zσ}(z cos kσ − k sin kσ)]/(z² + k²)`.

Antiderivative `e^{−zr}(−z cos kr + k sin kr)/(z²+k²)`; the `(z²+k²)` in the denominator is why the
hypothesis is `z² + k² ≠ 0` rather than `k ≠ 0` alone. -/
theorem exp_cos_integral {z k sigma : ℝ} (h : z ^ 2 + k ^ 2 ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.cos (k * r)
      = (z - Real.exp (-z * sigma) * (z * Real.cos (k * sigma) - k * Real.sin (k * sigma)))
        / (z ^ 2 + k ^ 2) := by
  have key : ∀ r : ℝ, HasDerivAt
      (fun t : ℝ => Real.exp (-z * t) * (-z * Real.cos (k * t) + k * Real.sin (k * t))
        / (z ^ 2 + k ^ 2))
      (Real.exp (-z * r) * Real.cos (k * r)) r := by
    intro r
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-z * t)) (-z * Real.exp (-z * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul (-z)).exp
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-(k * Real.sin (k * r))) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).cos
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (k * t)) (k * Real.cos (k * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).sin
    have hin : HasDerivAt
        (fun t : ℝ => -z * Real.cos (k * t) + k * Real.sin (k * t))
        (-z * -(k * Real.sin (k * r)) + k * (k * Real.cos (k * r))) r :=
      (hcos.const_mul (-z)).add (hsin.const_mul k)
    refine ((hexp.mul hin).div_const (z ^ 2 + k ^ 2)).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => key r)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, one_mul, mul_one]
  field_simp
  ring

/-- `∫₀^σ e^{−zr}sin(kr) dr = [k − e^{−zσ}(k cos kσ + z sin kσ)]/(z² + k²)`. -/
theorem exp_sin_integral {z k sigma : ℝ} (h : z ^ 2 + k ^ 2 ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.sin (k * r)
      = (k - Real.exp (-z * sigma) * (k * Real.cos (k * sigma) + z * Real.sin (k * sigma)))
        / (z ^ 2 + k ^ 2) := by
  have key : ∀ r : ℝ, HasDerivAt
      (fun t : ℝ => Real.exp (-z * t) * (-z * Real.sin (k * t) - k * Real.cos (k * t))
        / (z ^ 2 + k ^ 2))
      (Real.exp (-z * r) * Real.sin (k * r)) r := by
    intro r
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-z * t)) (-z * Real.exp (-z * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul (-z)).exp
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-(k * Real.sin (k * r))) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).cos
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (k * t)) (k * Real.cos (k * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).sin
    have hin : HasDerivAt
        (fun t : ℝ => -z * Real.sin (k * t) - k * Real.cos (k * t))
        (-z * (k * Real.cos (k * r)) - k * -(k * Real.sin (k * r))) r :=
      (hsin.const_mul (-z)).sub (hcos.const_mul k)
    refine ((hexp.mul hin).div_const (z ^ 2 + k ^ 2)).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => key r)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, one_mul, mul_one]
  field_simp
  ring

/-- The algebra behind `msa_exp_sq_modulus`, with the exponential and the two trig values kept
**opaque**.

⚠ Abstracting them is not tidiness.  Left concrete, `field_simp` rewrites `e^{−zσ}` through
`Real.exp_neg` into `(e^{zσ})⁻¹`, treats it as one more denominator, and clears it too — so the
multiple of the Pythagorean identity that closes the goal is no longer the one the algebra predicts.

The two numerators combine to `(z²+k²)[1 − 2EC + E²(C²+S²)]`; `C² + S² = 1` is used exactly once,
which is what the explicit `linear_combination` coefficient records. -/
private theorem sq_modulus_algebra {z k E C S : ℝ} (h : z ^ 2 + k ^ 2 ≠ 0)
    (hpy : S ^ 2 + C ^ 2 = 1) :
    ((z - E * (z * C - k * S)) / (z ^ 2 + k ^ 2)) ^ 2
      + ((k - E * (k * C + z * S)) / (z ^ 2 + k ^ 2)) ^ 2
      = (1 - 2 * E * C + E ^ 2) / (z ^ 2 + k ^ 2) := by
  field_simp
  linear_combination (E ^ 2 * (z ^ 2 + k ^ 2)) * hpy

/-- `Rez² + Imz² = (1 − 2e^{−zσ}cos kσ + e^{−2zσ})/(z² + k²)` — the squared modulus of the single
exponential integral `∫₀^σ e^{(−z+ik)r}dr`, and the `O(D²)` coefficient of `msa_lhs_split`. -/
theorem msa_exp_sq_modulus {z k sigma : ℝ} (h : z ^ 2 + k ^ 2 ≠ 0) :
    (∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.cos (k * r)) ^ 2
      + (∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.sin (k * r)) ^ 2
      = (1 - 2 * Real.exp (-z * sigma) * Real.cos (k * sigma)
          + Real.exp (-z * sigma) ^ 2) / (z ^ 2 + k ^ 2) := by
  rw [exp_cos_integral h, exp_sin_integral h]
  exact sq_modulus_algebra h (Real.sin_sq_add_cos_sq (k * sigma))

/-- ⭐ **The split.**  For any decomposition of the transforms into a hard-sphere part and `D` times
a tail part, the factorization's left side is the hard-sphere left side plus an explicit
polynomial in `D` — linear and quadratic terms only.

This is a `ring` identity, deliberately: the content is *where it sends MSAEXACT.1*.  The `Re₀`,
`Im₀` bracket is `1 − ρĉ_HS(k)` by BAXTER.3 (`msa_lhs_split_at_zero`), so what remains is to match

    −2D·[(1 − Re₀)·Rez − Im₀·Imz] + D²·[Rez² + Imz²]   against   −ρ·(ĉ_MSA − ĉ_HS)(k),

i.e. the `O(D)` and `O(D²)` increments — which is Waisman's Eq. (3), not a fresh factorization. -/
theorem msa_lhs_split (Re₀ Im₀ Rez Imz D : ℝ) :
    (1 - (Re₀ + D * Rez)) ^ 2 + (Im₀ + D * Imz) ^ 2
      = ((1 - Re₀) ^ 2 + Im₀ ^ 2)
        - 2 * D * ((1 - Re₀) * Rez - Im₀ * Imz)
        + D ^ 2 * (Rez ^ 2 + Imz ^ 2) := by
  ring

/-- At `D = 0` the split collapses to BAXTER.3 — the sanity corollary, and the statement that the
`O(1)` term really is the hard-sphere factorization. -/
theorem msa_lhs_split_at_zero (eta sigma rho k : ℝ) (hsigma : 0 < sigma) (hk : k ≠ 0)
    (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (Rez Imz : ℝ) :
    (1 - ((∫ r in (0 : ℝ)..sigma, FMSA.HardSphere.q0_poly eta sigma rho r * Real.cos (k * r))
            + 0 * Rez)) ^ 2
      + ((∫ r in (0 : ℝ)..sigma, FMSA.HardSphere.q0_poly eta sigma rho r * Real.sin (k * r))
            + 0 * Imz) ^ 2
      = 1 - rho * FMSA.HardSphere.radial_fourier (FMSA.HardSphere.c_HS eta sigma) k := by
  simpa using
    FMSA.HardSphere.baxter_wiener_hopf_factorization eta sigma rho k hsigma hk heta heta_def

end FMSA.MSAExact
