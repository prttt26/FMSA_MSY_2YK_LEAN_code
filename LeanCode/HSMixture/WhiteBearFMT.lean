/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task FW.1 / FW.2 — White-Bear FMT hard-sphere free energy and BMCSL contact values

## Summary

`betaf_hs` (Rosenfeld/White-Bear FMT excess free energy density for an N-component additive
hard-sphere mixture, Python: `fmsa_free_energy.py:57`) and `g0_bmcsl` (the BMCSL mixture
contact-value formula, Python: `FMSA_MC_cleaned_2cpp.py:1305-1332`) are ported to Lean here for
the first time — neither existed in this codebase's Lean side before.

**FW.1** — species symmetry: `betaf_hs` depends on the density vector `rho` only through the
four weighted-density moments `wbN0..wbN3`; when all diameters are equal, these moments depend
on `rho` only through its total `∑ᵢ ρᵢ`, so `betaf_hs` collapses to its single-component value.

**FW.2** — thermodynamic consistency: the BMCSL virial pressure (built from `g0_bmcsl`) equals
the pressure obtained by differentiating `betaf_hs` along a fixed-composition density ray
(the standard FMT/Rosenfeld scaled-pressure construction). This is the real open mathematical
content behind `g0_bmcsl` — **not** a claim that `g0_bmcsl` equals some independently-defined
"true" multi-species PY solution (no such solution is formalized, or even computed, anywhere in
this codebase — BMCSL is *used as the definition* of the mixture reference contact value, the
same closure role `c_HS` plays for the single-component DCF). Verified exactly (symbolically,
not just numerically) via `sympy` for N=2 and N=3 species before formalizing: `P_fmt - P_virial`
simplifies to the literal integer `0`. This is distinct from, and does **not** face the same
obstruction as, `g0_HS_contact_value` (`PYOZ_GHS.lean`) — that axiom is about the true PY
(Baxter/Wertheim) contact value `(1+η/2)/(1-η)²`, which genuinely needs Wiener–Hopf
factorization; BMCSL reduces at N=1 to the *different* Carnahan-Starling value
`(1-η/2)/(1-η)³`, not derived from Baxter/PY theory at all.
-/

open Finset

namespace FMSA.HardSphere

/-! ### Weighted densities (Task FW.1) -/

/-- `n₀ = Σᵢ ρᵢ` — the zeroth FMT weighted density (total number density). -/
noncomputable def wbN0 {N : ℕ} (rho : Fin N → ℝ) : ℝ := ∑ i, rho i

/-- `n₁ = Σᵢ ρᵢ·Rᵢ` with `Rᵢ = dᵢ/2` — the first FMT weighted density. -/
noncomputable def wbN1 {N : ℕ} (rho d : Fin N → ℝ) : ℝ := ∑ i, rho i * (d i / 2)

/-- `n₂ = 4π·Σᵢ ρᵢ·Rᵢ²` — the second FMT weighted density (total surface area density). -/
noncomputable def wbN2 {N : ℕ} (rho d : Fin N → ℝ) : ℝ :=
    4 * Real.pi * ∑ i, rho i * (d i / 2) ^ 2

/-- `n₃ = (4π/3)·Σᵢ ρᵢ·Rᵢ³` — the third FMT weighted density (total packing fraction). -/
noncomputable def wbN3 {N : ℕ} (rho d : Fin N → ℝ) : ℝ :=
    (4 / 3) * Real.pi * ∑ i, rho i * (d i / 2) ^ 3

/-! ### White-Bear FMT excess free energy density -/

/-- **Rosenfeld/White-Bear functional, as a pure function of the four weighted-density
moments** (Python: `fmsa_free_energy.py:57`):

    Φ(n₀,n₁,n₂,n₃) = −n₀·log(1−n₃) + n₁n₂/(1−n₃) + (n₂³/36π)·[log(1−n₃)/n₃² + 1/(n₃(1−n₃)²)]

Separated from `betaf_hs` (which supplies `n₀..n₃` from a `Fin N` density/diameter pair) so
the calculus needed for Task FW.2 (differentiating along a density-scaling ray) is a
self-contained single-variable computation, independent of `N` and the `Fin N` sums. -/
noncomputable def wbPhi (n0 n1 n2 n3 : ℝ) : ℝ :=
    -n0 * Real.log (1 - n3) + n1 * n2 / (1 - n3) +
      (n2 ^ 3 / (36 * Real.pi)) * (Real.log (1 - n3) / n3 ^ 2 + 1 / (n3 * (1 - n3) ^ 2))

/-- **Task FW.1 — Rosenfeld/White-Bear FMT excess free energy density**, `Φ` evaluated at the
weighted densities of an N-component mixture. For `N = 1`, this reduces exactly to the
Carnahan-Starling excess free energy density `ρ·η·(4−3η)/(1−η)²` (documented in the Python
source; not re-derived here). -/
noncomputable def betaf_hs {N : ℕ} (rho d : Fin N → ℝ) : ℝ :=
    wbPhi (wbN0 rho) (wbN1 rho d) (wbN2 rho d) (wbN3 rho d)

/-! ### FW.1 — species symmetry -/

/-- **Task FW.1: FMT species symmetry.** When all diameters equal `D`, `betaf_hs` depends on
`rho` only through its total density `∑ᵢ ρᵢ` — splitting a given total density across any
number of species (with the same diameter) does not change the FMT free energy. This is a
more general (and cleaner) statement than the literal "`ρ/N` each" special case: the weighted
densities `wbN0..wbN3` are each `(∑ᵢ ρᵢ) · c` for a `rho`-independent constant `c`, so
`betaf_hs` — being a function of `wbN0..wbN3` alone — is manifestly a function of `∑ᵢ ρᵢ`
alone. -/
theorem betaf_hs_species_symmetry {N : ℕ} (rho : Fin N → ℝ) (D : ℝ) :
    betaf_hs rho (fun _ => D) =
    betaf_hs (fun _ : Fin 1 => ∑ i, rho i) (fun _ : Fin 1 => D) := by
  have h0 : wbN0 rho = wbN0 (fun _ : Fin 1 => ∑ i, rho i) := by
    simp [wbN0]
  have h1 : wbN1 rho (fun _ => D) = wbN1 (fun _ : Fin 1 => ∑ i, rho i) (fun _ => D) := by
    simp [wbN1, Finset.sum_mul]
  have h2 : wbN2 rho (fun _ => D) = wbN2 (fun _ : Fin 1 => ∑ i, rho i) (fun _ => D) := by
    simp [wbN2, Finset.sum_mul]
  have h3 : wbN3 rho (fun _ => D) = wbN3 (fun _ : Fin 1 => ∑ i, rho i) (fun _ => D) := by
    simp [wbN3, Finset.sum_mul]
  unfold betaf_hs
  rw [h0, h1, h2, h3]

/-! ### FW.2 — BMCSL mixture contact value -/

/-- **Task FW.2 — BMCSL (Boublík–Mansoori–Carnahan–Starling–Leland) mixture contact-value
formula**, direct port of `get_g0ij_contact` (Python: `FMSA_MC_cleaned_2cpp.py:1328-1332`):

    g_ij(R_ij⁺) = 1/vac + 3·ζ₂·dᵢdⱼ/((dᵢ+dⱼ)·vac²) + 2·ζ₂²·(dᵢdⱼ/(dᵢ+dⱼ))²/vac³

where `ζ₂ = (π/6)·Σₖ ρₖdₖ²` and `vac = 1 − n₃ = 1 − (π/6)·Σₖ ρₖdₖ³`. This is the closure used
*as the definition* of the mixture reference contact value in this codebase (no independently
computed multi-species PY/Baxter solution exists to compare it against) — reduces at `N=1` to
the Carnahan-Starling value `(1-η/2)/(1-η)³`, **not** the PY value `(1+η/2)/(1-η)²` that
`g0_HS_contact_value` (`PYOZ_GHS.lean`) axiomatizes. -/
noncomputable def g0_bmcsl {N : ℕ} (rho d : Fin N → ℝ) (i j : Fin N) : ℝ :=
    let zeta2 := (Real.pi / 6) * ∑ k, rho k * (d k) ^ 2
    let vac := 1 - wbN3 rho d
    let f := d i * d j / (d i + d j)
    1 / vac + 3 * zeta2 * f / vac ^ 2 + 2 * zeta2 ^ 2 * f ^ 2 / vac ^ 3

/-- The additive mixture contact distance `R_ij = (dᵢ+dⱼ)/2`. -/
noncomputable def wbRij {N : ℕ} (d : Fin N → ℝ) (i j : Fin N) : ℝ := (d i + d j) / 2

/-! ### FW.2, piece 2 — differentiating `wbPhi` along the density-scaling ray -/

/-- **Task FW.2, piece 2:** the Rosenfeld/scaled-pressure construction — differentiating `wbPhi`
along the fixed-composition ray `t ↦ (t·n0,t·n1,t·n2,t·n3)` and forming `n0 + Φ' - Φ` at `t=1`
collapses to the closed, **log-free** BMCSL equation of state. Verified exactly via `sympy`
before formalizing (`P_fmt` simplifies to this rational function with zero residual). -/
theorem wbPhi_ray_pressure_eq {n0 n1 n2 n3 : ℝ} (hn3 : n3 ≠ 0) (hvac : (1 : ℝ) - n3 ≠ 0) :
    n0 + deriv (fun t : ℝ => wbPhi (t * n0) (t * n1) (t * n2) (t * n3)) 1 -
      wbPhi n0 n1 n2 n3 =
    n0 / (1 - n3) + n1 * n2 / (1 - n3) ^ 2 +
      n2 ^ 3 * (3 - n3) / (36 * Real.pi * (1 - n3) ^ 3) := by
  -- Bridges a `HasDerivAt` fact from Pi-algebra form (`f*g`, `f^n`, ...) to pointwise
  -- application form (`fun t => f t * g t`, ...) — the two are equal by `rfl` pointwise, so
  -- `Filter.Eventually.of_forall (fun t => rfl)` always discharges the bridging hypothesis.
  -- Intermediate `have`s below deliberately carry NO type ascription: `HasDerivAt.mul`/`.pow`
  -- naturally evaluate the *original* (unsimplified, e.g. `1 * n2`) function at the point as
  -- part of the derivative formula, so hand-writing a "clean" expected value causes spurious
  -- mismatches. All cleanup happens once, in the final `field_simp`/`ring` step.
  have mulP : ∀ {f g : ℝ → ℝ} {c : ℝ}, HasDerivAt (f * g) c 1 →
      HasDerivAt (fun t => f t * g t) c 1 :=
    fun h => h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have powP : ∀ {f : ℝ → ℝ} {c : ℝ} {n : ℕ}, HasDerivAt (f ^ n) c 1 →
      HasDerivAt (fun t => f t ^ n) c 1 :=
    fun h => h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hvac1 : (1 : ℝ) - 1 * n3 ≠ 0 := by simpa using hvac
  have htn3 : (1 : ℝ) * n3 ≠ 0 := by simpa using hn3
  -- linear scalings `t ↦ t*nk`
  have hlin0 : HasDerivAt (fun t : ℝ => t * n0) n0 1 := hasDerivAt_mul_const n0
  have hlin1 : HasDerivAt (fun t : ℝ => t * n1) n1 1 := hasDerivAt_mul_const n1
  have hlin2 : HasDerivAt (fun t : ℝ => t * n2) n2 1 := hasDerivAt_mul_const n2
  have hlin3 : HasDerivAt (fun t : ℝ => t * n3) n3 1 := hasDerivAt_mul_const n3
  -- vac(t) = 1 - t*n3, and log(vac(t))
  have hV : HasDerivAt (fun t : ℝ => (1 : ℝ) - t * n3) (-n3) 1 := hlin3.const_sub 1
  have hlogV := hV.log hvac1
  -- term A(t) = -(t*n0) * log(1-t*n3)
  have hnegn0 : HasDerivAt (fun t : ℝ => -(t * n0)) (-n0) 1 := hlin0.neg
  have hA := mulP (hnegn0.mul hlogV)
  -- term B(t) = (t*n1)*(t*n2)/(1-t*n3)
  have hnum12 := mulP (hlin1.mul hlin2)
  have hB := hnum12.fun_div hV hvac1
  -- term C(t) = (t*n2)^3/(36π) * (log(1-t*n3)/(t*n3)^2)
  have hcube2 := powP (hlin2.pow 3)
  have hsq3 := powP (hlin3.pow 2)
  have hlogOverSq := hlogV.fun_div hsq3 (pow_ne_zero 2 htn3)
  have hC := mulP ((hcube2.div_const (36 * Real.pi)).mul hlogOverSq)
  -- term D(t) = (t*n2)^3/(36π) * (1/((t*n3)*(1-t*n3)^2))
  have hsqV := powP (hV.pow 2)
  have hdenomD := mulP (hlin3.mul hsqV)
  have hdenomD_ne : (1 : ℝ) * n3 * (1 - 1 * n3) ^ 2 ≠ 0 := by
    simp only [one_mul]
    exact mul_ne_zero hn3 (pow_ne_zero 2 hvac)
  have hinvD := (hasDerivAt_const (1 : ℝ) (1 : ℝ)).fun_div hdenomD hdenomD_ne
  have hD := mulP ((hcube2.div_const (36 * Real.pi)).mul hinvD)
  -- assemble: wbPhiRay(t) = A(t) + B(t) + (C(t) + D(t)); hA,hB,hC,hD are already pointwise
  -- (via `mulP`/`fun_div`), so the outer `.add`s unfold to `wbPhi (t*n0)..` by `rfl`/`unfold`.
  have hABCD := (hA.add hB).add (hC.add hD)
  have heq : (fun t : ℝ => wbPhi (t * n0) (t * n1) (t * n2) (t * n3)) =
      (fun t : ℝ => -(t * n0) * Real.log (1 - t * n3)) +
        (fun t : ℝ => t * n1 * (t * n2) / (1 - t * n3)) +
        ((fun t : ℝ => (t * n2) ^ 3 / (36 * Real.pi) * (Real.log (1 - t * n3) / (t * n3) ^ 2)) +
          (fun t : ℝ => (t * n2) ^ 3 / (36 * Real.pi) * (1 / (t * n3 * (1 - t * n3) ^ 2)))) := by
    funext t
    change wbPhi (t * n0) (t * n1) (t * n2) (t * n3) =
      -(t * n0) * Real.log (1 - t * n3) + t * n1 * (t * n2) / (1 - t * n3) +
        ((t * n2) ^ 3 / (36 * Real.pi) * (Real.log (1 - t * n3) / (t * n3) ^ 2) +
          (t * n2) ^ 3 / (36 * Real.pi) * (1 / (t * n3 * (1 - t * n3) ^ 2)))
    unfold wbPhi
    ring
  have hRay := heq ▸ hABCD
  rw [hRay.deriv]
  unfold wbPhi
  simp only [one_mul]
  field_simp
  ring

/-! ### FW.2, piece 3 — the BMCSL double sum collapses to the same closed form -/

/-- Moment-pair reduction: `∑ᵢ∑ⱼ ρᵢρⱼ·Rᵢᵃ·Rⱼᵇ = (∑ᵢρᵢRᵢᵃ)·(∑ⱼρⱼRⱼᵇ)`, `Rᵢ := dᵢ/2`. The
cross-species double sum always factors into a product of two single-species moment sums —
this is the algebraic fact that makes the BMCSL ansatz's specific `f = dᵢdⱼ/(dᵢ+dⱼ)` structure
collapse correctly (Task FW.2, piece 3). -/
private theorem wb_moment_pair {N : ℕ} (rho d : Fin N → ℝ) (a b : ℕ) :
    (∑ i, ∑ j, rho i * rho j * (d i / 2) ^ a * (d j / 2) ^ b) =
    (∑ i, rho i * (d i / 2) ^ a) * (∑ j, rho j * (d j / 2) ^ b) := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Expand a double sum of a 4-term polynomial-in-`(dᵢ/2,dⱼ/2)` summand into the sum of the
four separately-reduced moment-pair products, via `wb_moment_pair`. -/
private theorem wb_expand4 {N : ℕ} (rho d : Fin N → ℝ) (c0 c1 c2 c3 : ℝ)
    (a0 b0 a1 b1 a2 b2 a3 b3 : ℕ) :
    (∑ i, ∑ j, rho i * rho j *
        (c0 * (d i / 2) ^ a0 * (d j / 2) ^ b0 + c1 * (d i / 2) ^ a1 * (d j / 2) ^ b1 +
          c2 * (d i / 2) ^ a2 * (d j / 2) ^ b2 + c3 * (d i / 2) ^ a3 * (d j / 2) ^ b3)) =
    c0 * ((∑ i, rho i * (d i / 2) ^ a0) * (∑ j, rho j * (d j / 2) ^ b0)) +
      c1 * ((∑ i, rho i * (d i / 2) ^ a1) * (∑ j, rho j * (d j / 2) ^ b1)) +
      c2 * ((∑ i, rho i * (d i / 2) ^ a2) * (∑ j, rho j * (d j / 2) ^ b2)) +
      c3 * ((∑ i, rho i * (d i / 2) ^ a3) * (∑ j, rho j * (d j / 2) ^ b3)) := by
  rw [← wb_moment_pair rho d a0 b0, ← wb_moment_pair rho d a1 b1,
      ← wb_moment_pair rho d a2 b2, ← wb_moment_pair rho d a3 b3]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Same as `wb_expand4`, for a 3-term summand. -/
private theorem wb_expand3 {N : ℕ} (rho d : Fin N → ℝ) (c0 c1 c2 : ℝ)
    (a0 b0 a1 b1 a2 b2 : ℕ) :
    (∑ i, ∑ j, rho i * rho j *
        (c0 * (d i / 2) ^ a0 * (d j / 2) ^ b0 + c1 * (d i / 2) ^ a1 * (d j / 2) ^ b1 +
          c2 * (d i / 2) ^ a2 * (d j / 2) ^ b2)) =
    c0 * ((∑ i, rho i * (d i / 2) ^ a0) * (∑ j, rho j * (d j / 2) ^ b0)) +
      c1 * ((∑ i, rho i * (d i / 2) ^ a1) * (∑ j, rho j * (d j / 2) ^ b1)) +
      c2 * ((∑ i, rho i * (d i / 2) ^ a2) * (∑ j, rho j * (d j / 2) ^ b2)) := by
  rw [← wb_moment_pair rho d a0 b0, ← wb_moment_pair rho d a1 b1, ← wb_moment_pair rho d a2 b2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Same as `wb_expand4`, for a 2-term summand. -/
private theorem wb_expand2 {N : ℕ} (rho d : Fin N → ℝ) (c0 c1 : ℝ) (a0 b0 a1 b1 : ℕ) :
    (∑ i, ∑ j, rho i * rho j *
        (c0 * (d i / 2) ^ a0 * (d j / 2) ^ b0 + c1 * (d i / 2) ^ a1 * (d j / 2) ^ b1)) =
    c0 * ((∑ i, rho i * (d i / 2) ^ a0) * (∑ j, rho j * (d j / 2) ^ b0)) +
      c1 * ((∑ i, rho i * (d i / 2) ^ a1) * (∑ j, rho j * (d j / 2) ^ b1)) := by
  rw [← wb_moment_pair rho d a0 b0, ← wb_moment_pair rho d a1 b1]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Task FW.2, piece 3:** the BMCSL double sum, expanded via `R_ij = Rᵢ+Rⱼ` (`Rᵢ := dᵢ/2`)
and moment-pair reduction, collapses to *exactly* the closed form reached in piece 2
(`wbPhi_ray_pressure_eq`, minus the leading `n0` term) — purely in terms of `wbN0..wbN3`, with
all cross-species detail cancelling. Verified via a fast polynomial-level `sympy` check (expand
`(dᵢ+dⱼ)^k`, map monomials `dᵢᵃdⱼᵇ ↦ Ma·Mb`) before formalizing. The positivity hypothesis
`hd` (physical: diameters are positive) avoids a zero-denominator case split when cancelling
`(dᵢ+dⱼ)` out of `g0_bmcsl`'s `f = dᵢdⱼ/(dᵢ+dⱼ)` factor. -/
theorem g0_bmcsl_virial_sum_eq {N : ℕ} (rho d : Fin N → ℝ) (hd : ∀ i, 0 < d i)
    (hvac : (1 : ℝ) - wbN3 rho d ≠ 0) :
    (2 * Real.pi / 3) * ∑ i, ∑ j, rho i * rho j * (wbRij d i j) ^ 3 * g0_bmcsl rho d i j =
    wbN0 rho * wbN3 rho d / (1 - wbN3 rho d) +
      wbN1 rho d * wbN2 rho d / (1 - wbN3 rho d) ^ 2 +
      (wbN2 rho d) ^ 3 * (3 - wbN3 rho d) / (36 * Real.pi * (1 - wbN3 rho d) ^ 3) := by
  have hP0 : (∑ i, rho i * (d i / 2) ^ 0) = wbN0 rho := by simp [wbN0]
  have hP1 : (∑ i, rho i * (d i / 2) ^ 1) = wbN1 rho d := by simp [wbN1]
  have hpi : (4 : ℝ) * Real.pi ≠ 0 := by positivity
  have hP2 : (∑ i, rho i * (d i / 2) ^ 2) = wbN2 rho d / (4 * Real.pi) := by
    rw [eq_div_iff hpi]; unfold wbN2; ring
  have hP3 : (∑ i, rho i * (d i / 2) ^ 3) = 3 * wbN3 rho d / (4 * Real.pi) := by
    rw [eq_div_iff hpi]; unfold wbN3; ring
  have hzeta2 : (Real.pi / 6) * ∑ k, rho k * (d k) ^ 2 = wbN2 rho d / 6 := by
    have hconv : (∑ k, rho k * (d k) ^ 2) = 4 * ∑ i, rho i * (d i / 2) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hconv, hP2]
    field_simp
  -- Cancel the `(dᵢ+dⱼ)` denominator in `g0_bmcsl`'s `f` term-by-term (valid: `dᵢ,dⱼ>0`).
  have hsplit : ∀ i j : Fin N,
      rho i * rho j * (wbRij d i j) ^ 3 * g0_bmcsl rho d i j =
      rho i * rho j * ((d i / 2) ^ 3 + 3 * (d i / 2) ^ 2 * (d j / 2) +
          3 * (d i / 2) * (d j / 2) ^ 2 + (d j / 2) ^ 3) / (1 - wbN3 rho d) +
        3 * ((Real.pi / 6) * ∑ k, rho k * (d k) ^ 2) *
          (rho i * rho j * (2 * (d i / 2) ^ 3 * (d j / 2) + 4 * (d i / 2) ^ 2 * (d j / 2) ^ 2 +
            2 * (d i / 2) * (d j / 2) ^ 3)) / (1 - wbN3 rho d) ^ 2 +
        2 * ((Real.pi / 6) * ∑ k, rho k * (d k) ^ 2) ^ 2 *
          (rho i * rho j * (4 * (d i / 2) ^ 3 * (d j / 2) ^ 2 +
            4 * (d i / 2) ^ 2 * (d j / 2) ^ 3)) / (1 - wbN3 rho d) ^ 3 := by
    intro i j
    have hij : d i + d j ≠ 0 := (add_pos (hd i) (hd j)).ne'
    unfold wbRij g0_bmcsl
    have hR : d i / 2 + d j / 2 = (d i + d j) / 2 := by ring
    field_simp
    ring
  -- Bridge each *unpadded* polynomial (as it appears below, matching `hsplit`) to the
  -- `wb_expand4`-reduced moment-product form via a per-`(i,j)` `ring` congruence (`wb_expand4`
  -- itself is stated with explicit `1 * _ ^0`-padded coefficients so it applies uniformly to
  -- any 4-term polynomial; hand-simplifying its output to a single closed form proved
  -- error-prone in an earlier attempt, so `hP0..hP3` substitution is deferred to the end).
  have hT1 : (∑ i : Fin N, ∑ j : Fin N, rho i * rho j *
      ((d i / 2) ^ 3 + 3 * (d i / 2) ^ 2 * (d j / 2) + 3 * (d i / 2) * (d j / 2) ^ 2 +
        (d j / 2) ^ 3)) =
      (∑ i, rho i * (d i / 2) ^ 3) * (∑ j, rho j * (d j / 2) ^ 0) +
        3 * ((∑ i, rho i * (d i / 2) ^ 2) * (∑ j, rho j * (d j / 2) ^ 1)) +
        3 * ((∑ i, rho i * (d i / 2) ^ 1) * (∑ j, rho j * (d j / 2) ^ 2)) +
        (∑ i, rho i * (d i / 2) ^ 0) * (∑ j, rho j * (d j / 2) ^ 3) := by
    simpa using wb_expand4 rho d 1 3 3 1 3 0 2 1 1 2 0 3
  have hT2 : (∑ i : Fin N, ∑ j : Fin N, rho i * rho j *
      (2 * (d i / 2) ^ 3 * (d j / 2) + 4 * (d i / 2) ^ 2 * (d j / 2) ^ 2 +
        2 * (d i / 2) * (d j / 2) ^ 3)) =
      2 * ((∑ i, rho i * (d i / 2) ^ 3) * (∑ j, rho j * (d j / 2) ^ 1)) +
        4 * ((∑ i, rho i * (d i / 2) ^ 2) * (∑ j, rho j * (d j / 2) ^ 2)) +
        2 * ((∑ i, rho i * (d i / 2) ^ 1) * (∑ j, rho j * (d j / 2) ^ 3)) := by
    simpa using wb_expand3 rho d 2 4 2 3 1 2 2 1 3
  have hT3 : (∑ i : Fin N, ∑ j : Fin N, rho i * rho j *
      (4 * (d i / 2) ^ 3 * (d j / 2) ^ 2 + 4 * (d i / 2) ^ 2 * (d j / 2) ^ 3)) =
      4 * ((∑ i, rho i * (d i / 2) ^ 3) * (∑ j, rho j * (d j / 2) ^ 2)) +
        4 * ((∑ i, rho i * (d i / 2) ^ 2) * (∑ j, rho j * (d j / 2) ^ 3)) :=
    wb_expand2 rho d 4 4 3 2 2 3
  have hsum : (∑ i, ∑ j, rho i * rho j * (wbRij d i j) ^ 3 * g0_bmcsl rho d i j) =
      (∑ i : Fin N, ∑ j : Fin N, rho i * rho j *
        ((d i / 2) ^ 3 + 3 * (d i / 2) ^ 2 * (d j / 2) + 3 * (d i / 2) * (d j / 2) ^ 2 +
          (d j / 2) ^ 3)) / (1 - wbN3 rho d) +
      3 * (wbN2 rho d / 6) *
        (∑ i : Fin N, ∑ j : Fin N, rho i * rho j *
          (2 * (d i / 2) ^ 3 * (d j / 2) + 4 * (d i / 2) ^ 2 * (d j / 2) ^ 2 +
            2 * (d i / 2) * (d j / 2) ^ 3)) / (1 - wbN3 rho d) ^ 2 +
      2 * (wbN2 rho d / 6) ^ 2 *
        (∑ i : Fin N, ∑ j : Fin N, rho i * rho j *
          (4 * (d i / 2) ^ 3 * (d j / 2) ^ 2 + 4 * (d i / 2) ^ 2 * (d j / 2) ^ 3)) /
        (1 - wbN3 rho d) ^ 3 := by
    simp_rw [hsplit, hzeta2]
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hsum, hT1, hT2, hT3]
  simp only [hP0, hP1, hP2, hP3]
  field_simp [Real.pi_ne_zero]
  ring

/-! ### FW.2, piece 4 — assembled: BMCSL/White-Bear thermodynamic consistency -/

/-- **Task FW.2 (assembled): BMCSL/White-Bear thermodynamic consistency.** The BMCSL virial
pressure (LHS: total density + (2π/3)·Σᵢⱼρᵢρⱼ·R_ij³·g₀^BMCSL(i,j), the standard virial-route
hard-sphere pressure formula built from pairwise contact values) exactly equals the
Rosenfeld/White-Bear scaled pressure (RHS: n₀ + Φ'(1) − Φ(1) along the fixed-composition
density-scaling ray, the standard FMT pressure construction from `betaf_hs`) — for any
N-component additive hard-sphere mixture, unconditionally (no smallness/dilute hypothesis).

This is the honest Lean formalization of the "FW.2" open task. **Not** a claim that
`g0_bmcsl` equals some independently-defined *true* multi-species PY solution — no such
solution is formalized, or even computed, anywhere in this codebase (only the single-component
Baxter/PY solution exists, `g0_HS_contact_value`, a *different* formula — see `g0_bmcsl`'s doc
comment). Rather, this is the real open mathematical content behind *using* BMCSL as the
mixture reference contact-value closure: the two independently-motivated pressure routes
(virial, from pairwise contact values; scaled-particle, from the free energy functional) agree
*exactly*. This matches what `verify_wc.py`'s `wc2()` (W-C.2) checks numerically (to ~1e-5,
limited by finite-difference truncation) as an *exact* algebraic identity here — assembled
directly from piece 2 (`wbPhi_ray_pressure_eq`) and piece 3 (`g0_bmcsl_virial_sum_eq`), both of
which independently reach the same closed, log-free rational-function form. -/
theorem bmcsl_virial_eq_fmt_pressure {N : ℕ} (rho d : Fin N → ℝ) (hd : ∀ i, 0 < d i)
    (hn3 : wbN3 rho d ≠ 0) (hvac : (1 : ℝ) - wbN3 rho d ≠ 0) :
    wbN0 rho +
      (2 * Real.pi / 3) * ∑ i, ∑ j, rho i * rho j * (wbRij d i j) ^ 3 * g0_bmcsl rho d i j =
    wbN0 rho +
      deriv (fun t : ℝ => wbPhi (t * wbN0 rho) (t * wbN1 rho d) (t * wbN2 rho d)
        (t * wbN3 rho d)) 1 -
      betaf_hs rho d := by
  unfold betaf_hs
  rw [g0_bmcsl_virial_sum_eq rho d hd hvac,
      wbPhi_ray_pressure_eq (n0 := wbN0 rho) (n1 := wbN1 rho d) (n2 := wbN2 rho d)
        (n3 := wbN3 rho d) hn3 hvac]
  field_simp
  ring

end FMSA.HardSphere
