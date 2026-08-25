/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterFactor

/-!
# The concrete Blum–Høye residual system at `N = 1` — Group `MSAFAM.1–2`

Records: `Lean_code/proof_notes_closures.md`, "Group MSAFAM".
Numerical partner: `numerical_notes/theory/waisman_msa_closed_form.md` §7f–§7g and
`msa_exact.py._bh_pieces`.

FOEQ.5's `C¹` capstone `msa_amplitude_differentiable_of_bh_shape`
(`Closures/FirstOrderEquivalence.lean`) discharges the *analytic* half of the implicit-function
obligation from four abstract facts about a residual pair `F, P : ℝ × ℝ → ℝ`:

* `ContDiff ℝ 1 F`, `ContDiff ℝ 1 P`;
* vanishing `G`-directional derivative at the Percus–Yevick base point,
  `fderiv F (0, G₀) (0, 1) = 0` and the same for `P`;
* the hard-sphere Baxter factor is nonzero, `F (0, G₀) ≠ 0`;
* the PY base equation `2π · G₀ · F (0, G₀) = P (0, G₀)`.

This file supplies the **concrete** `F, P` — the Blum–Høye `2 × 2` system at one tail, in the
`(Dt, G)` variables where every `e^{z}` cancels (theory note §7f) — and proves all four facts
(MSAFAM.2), so that at `N = 1` FOEQ.5 becomes hypothesis-free at `γ = 1`.  The construction is the
`⭐` insight of the group: writing `bhF`, `bhP` in the factored form `base + Dt · rest(G)` makes the
vanishing-`G`-derivative *syntactic* (every `G`-bearing monomial carries a literal `Dt` factor, and
`Dt = 0` at the base point), and the base equation a rational identity in `w := e^{−z}`.

Faithfulness to `_bh_pieces` is the derivation of §7f–§7g (validated numerically for arbitrary
`(Dt, G, w)`); the factoring `Qh = Q̂₀ + Dt·QhRest(G)`, `A = A⁰ + Dt(…)`, `q′ = q⁰′ + Dt(…)` is
exact.
The one place the transcription touches the rest of the library is
`bhF (0, G₀) = 1 − ρ Q̂₀(z)` — which is what lets `HardSphere.Q0_ne_zero_at_yukawa` enter — and the
base equation, whose hard-sphere content `2π·ĝ_PY(z)e^z·(1−ρQ̂₀) = (A⁰ + z q⁰′)/z²` is proved here
directly from the closed forms.
-/

namespace FMSA.ExactMSA

open Real
open scoped ContDiff

variable (xi z : ℝ)

/-! ## The hard-sphere Baxter data (Blum & Høye Eq. 25, `σ = 1`) and the `φ` transforms -/

/-- Number density `ρ = 6ξ/π` at `σ = 1`. -/
noncomputable def rhoOf : ℝ := 6 * xi / π

/-- PY hard-sphere Baxter coefficient `A⁰` (Blum & Høye Eq. 25). -/
noncomputable def bA0 : ℝ := 2 * π / (1 - xi) ^ 2 * (1 + 2 * xi)

/-- PY hard-sphere Baxter coefficient `B⁰` (Blum & Høye Eq. 25). -/
noncomputable def bB0 : ℝ := 2 * π / (1 - xi) ^ 2 * (-(3 / 2) * xi)

/-- PY hard-sphere Baxter slope `q⁰′ = A⁰ + B⁰` (Blum & Høye Eq. 25). -/
noncomputable def qp0 : ℝ := 2 * π / (1 - xi) ^ 2 * (3 / 2 * xi + (1 - xi))

/-- Blum & Høye Eq. (22): `φ₁(z) = (1 − z − e^{−z})/z²`. -/
noncomputable def phi1 : ℝ := (1 - z - Real.exp (-z)) / z ^ 2

/-- Blum & Høye Eq. (22): `φ₂(z) = (1 − z + z²/2 − e^{−z})/z³`. -/
noncomputable def phi2 : ℝ := (1 - z + z ^ 2 / 2 - Real.exp (-z)) / z ^ 3

/-- The PY Baxter factor's transform `Q̂₀(z) = φ₁(z) q⁰′ + φ₂(z) A⁰`. -/
noncomputable def Qhat0 : ℝ := phi1 z * qp0 xi + phi2 z * bA0 xi

/-- `F₀ = 1 − ρ Q̂₀(z)` — the hard-sphere Baxter factor at frequency `z` (the `K=0` value of `F`).
-/
noncomputable def F0 : ℝ := 1 - rhoOf xi * Qhat0 xi z

/-- `bhP₀ = (A⁰ + z q⁰′)/z²` — the right side of Blum & Høye (33) at the PY point (`Dt = 0`). -/
noncomputable def bhP0 : ℝ := (bA0 xi + z * qp0 xi) / z ^ 2

/-! ## The `G`-dependent pieces (`γ` affine in `G`; each carries a `Dt` factor upstream) -/

/-- Blum & Høye Eq. (27): `γ = 1 − 2πρ G e^{−z}/z` (affine in `G`). -/
noncomputable def gam (G : ℝ) : ℝ := 1 - 2 * π * rhoOf xi * G * Real.exp (-z) / z

/-- `M = Dt · Mtil`; `Mtil(G) = −(ρ/z)(γ(1+z) + 2πρG/z)` (Blum & Høye Eq. 20, cancellation done). -/
noncomputable def Mtil (G : ℝ) : ℝ :=
  -(rhoOf xi / z) * (gam xi z G * (1 + z) + 2 * π * rhoOf xi * G / z)

/-- `N = Dt · Ntil`; `Ntil(G) = (ρ/z²)(2πρG/z + γ(1+z+z²/2))` (Blum & Høye Eq. 21, corrected). -/
noncomputable def Ntil (G : ℝ) : ℝ :=
  rhoOf xi / z ^ 2 * (2 * π * rhoOf xi * G / z + gam xi z G * (1 + z + z ^ 2 / 2))

/-- `tail = Dt · tailtil`; `tailtil(G) = (1/2z)(2πρG/z + γ(2 − e^{−z}))` (Blum & Høye Eq. 37). -/
noncomputable def tailtil (G : ℝ) : ℝ :=
  1 / (2 * z) * (2 * π * rhoOf xi * G / z + gam xi z G * (2 - Real.exp (-z)))

/-- The `Dt`-linear coefficient of `bhF`: `bhF = F₀ + Dt · bhFRest(G)`, so
`bhFRest(G) = −ρ (Mtil·Q̂₀ + Ntil(φ₁A⁰ − 4B⁰φ₂) + tailtil)` (from `F = 1 − ρ Qh`,
`Qh = Q̂₀ + Dt·QhRest`). -/
noncomputable def bhFRest (G : ℝ) : ℝ :=
  -(rhoOf xi) * (Mtil xi z G * Qhat0 xi z
    + Ntil xi z G * (phi1 z * bA0 xi - 4 * bB0 xi * phi2 z) + tailtil xi z G)

/-- The `Dt`-linear coefficient of `bhP`: `bhP = bhP₀ + Dt · bhPRest(G)`, so
`bhPRest(G) = [(A⁰Mtil − 4B⁰Ntil) + z(q⁰′Mtil + A⁰Ntil) + (z²/2)γ]/z²` (from `A = A⁰ + Dt(…)`,
`q′ = q⁰′ + Dt(…)`, and the `(z²/2)γDt` term). -/
noncomputable def bhPRest (G : ℝ) : ℝ :=
  ((bA0 xi * Mtil xi z G - 4 * bB0 xi * Ntil xi z G)
    + z * (qp0 xi * Mtil xi z G + bA0 xi * Ntil xi z G) + z ^ 2 / 2 * gam xi z G) / z ^ 2

/-! ## The Blum–Høye residual data `bhF`, `bhP`, and the PY base point `G₀` -/

/-- **MSAFAM.1** — the Blum–Høye Baxter factor `F(Dt, G) = 1 − ρ Q̂(z)` at `N = 1`, one tail, in the
factored form `F₀ + Dt · bhFRest(G)` (theory note §7f, `_bh_pieces['F']`). -/
noncomputable def bhF (p : ℝ × ℝ) : ℝ := F0 xi z + p.1 * bhFRest xi z p.2

/-- **MSAFAM.1** — the Blum–Høye second-equation right side
`P(Dt, G) = [A + z q′ + (z²/2)γ Dt]/z²` at `N = 1`, one tail, in the factored form
`bhP₀ + Dt · bhPRest(G)` (theory note §7f, Eq. (33)). -/
noncomputable def bhP (p : ℝ × ℝ) : ℝ := bhP0 xi z + p.1 * bhPRest xi z p.2

/-- The denominator of `G₀`, in the exact form of `HardSphere.Q0_ne_zero_at_yukawa`:
`S(z) + L(z) e^{−z}`, with `S`, `L` the [chsY]/Blum–Høye moments. -/
noncomputable def G0denom : ℝ :=
  (1 - xi) ^ 2 * z ^ 3 + 6 * xi * (1 - xi) * z ^ 2 + 18 * xi ^ 2 * z -
    12 * xi * (1 + 2 * xi) +
    12 * xi * ((1 + xi / 2) * z + (1 + 2 * xi)) * Real.exp (-z)

/-- **MSAFAM.1** — the Percus–Yevick base point `G₀ = ĝ_PY(z) e^{z}` in closed form
(`hs_laplace_moment_scaled`): `G₀ = z L / (12ξ (S + L e^{−z}))`. -/
noncomputable def G0 : ℝ :=
  z * (12 * xi * ((1 + xi / 2) * z + (1 + 2 * xi))) / (12 * xi * G0denom xi z)

/-! ## `MSAFAM.1` — smoothness -/

/-- `bhFRest` is a polynomial in `G` with constant coefficients, hence `C^∞`. -/
theorem bhFRest_contDiff : ContDiff ℝ ∞ (bhFRest xi z) := by
  unfold bhFRest Mtil Ntil tailtil gam
  fun_prop

/-- `bhPRest` is a polynomial in `G` with constant coefficients, hence `C^∞`. -/
theorem bhPRest_contDiff : ContDiff ℝ ∞ (bhPRest xi z) := by
  unfold bhPRest Mtil Ntil gam
  fun_prop

/-- **MSAFAM.1** — `bhF` is `C^∞` (a degree-2 polynomial in `(Dt, G)`). -/
theorem bhF_contDiff : ContDiff ℝ ∞ (bhF xi z) := by
  unfold bhF
  exact contDiff_const.add (contDiff_fst.mul ((bhFRest_contDiff xi z).comp contDiff_snd))

/-- **MSAFAM.1** — `bhP` is `C^∞` (a degree-2 polynomial in `(Dt, G)`). -/
theorem bhP_contDiff : ContDiff ℝ ∞ (bhP xi z) := by
  unfold bhP
  exact contDiff_const.add (contDiff_fst.mul ((bhPRest_contDiff xi z).comp contDiff_snd))

/-! ## `MSAFAM.2` — the four properties FOEQ.5's capstone assumes -/

/-- The structural core of the vanishing-`G`-derivative: for any map of the form
`p ↦ base + p.1 · rest p.2` with `rest` differentiable, the directional derivative in the pure-`G`
direction `(0, 1)` at a base point `(0, G₀)` **vanishes** — because `p.1 = 0` there kills the only
term the `G`-derivative could reach.  This is the `⭐ "Dt = 0 kills every G-dependence"` insight,
made syntactic by the `base + Dt · rest(G)` factoring of `bhF`/`bhP`. -/
theorem fderiv_fst_factor_snd_apply {base G₀ : ℝ} {rest : ℝ → ℝ}
    (hrest : DifferentiableAt ℝ rest G₀) :
    fderiv ℝ (fun p : ℝ × ℝ => base + p.1 * rest p.2) (0, G₀) (0, 1) = 0 := by
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, G₀) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ => rest p.2)
      ((fderiv ℝ rest G₀).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) (0, G₀) :=
    hrest.hasFDerivAt.comp (0, G₀) (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  -- Ascribe the lambda form so `hadd.fderiv` matches the goal syntactically.
  have hadd : HasFDerivAt (fun p : ℝ × ℝ => base + p.1 * rest p.2) _ (0, G₀) :=
    (hasFDerivAt_const base (0, G₀)).add (hfst.mul hsnd)
  rw [hadd.fderiv]
  simp

/-- **MSAFAM.2 (i)** — `bhF` has vanishing `G`-directional derivative at the PY base point. -/
theorem bhF_fderiv_snd (G₀ : ℝ) :
    fderiv ℝ (bhF xi z) (0, G₀) (0, 1) = 0 :=
  fderiv_fst_factor_snd_apply
    ((bhFRest_contDiff xi z).differentiable (by norm_num)).differentiableAt

/-- **MSAFAM.2 (i)** — `bhP` has vanishing `G`-directional derivative at the PY base point. -/
theorem bhP_fderiv_snd (G₀ : ℝ) :
    fderiv ℝ (bhP xi z) (0, G₀) (0, 1) = 0 :=
  fderiv_fst_factor_snd_apply
    ((bhPRest_contDiff xi z).differentiable (by norm_num)).differentiableAt

/-- **MSAFAM.2 (ii)** — `bhF` at the base point is exactly the hard-sphere Baxter factor
`1 − ρ Q̂₀(z)`.  This is the one identity that connects the transcription to the rest of the
library. -/
theorem bhF_base : bhF xi z (0, G0 xi z) = 1 - rhoOf xi * Qhat0 xi z := by
  simp [bhF, F0]

/-- `bhP` at the base point is `(A⁰ + z q⁰′)/z²` (the `Dt`-linear term drops). -/
theorem bhP_base : bhP xi z (0, G0 xi z) = bhP0 xi z := by
  simp [bhP]

/-- **MSAFAM.2 (iv)** — the **PY base equation** `2π·G₀·F₀ = (A⁰ + z q⁰′)/z²`.  A rational identity
in `w := e^{−z}` (it holds for arbitrary `w`, so no transcendental fact about `exp` is used — only
that the denominators are nonzero), closed by `field_simp; ring`.  The nonvanishing of `G₀`'s
denominator is `HardSphere.Q0_ne_zero_at_yukawa`. -/
theorem bh_base_eq {xi z : ℝ} (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) (hz : 0 < z) :
    2 * π * (G0 xi z * bhF xi z (0, G0 xi z)) = bhP xi z (0, G0 xi z) := by
  have hz0 : z ≠ 0 := hz.ne'
  have hxi0 : xi ≠ 0 := hxi.1.ne'
  have hxi1 : (1 : ℝ) - xi ≠ 0 := (sub_pos.mpr hxi.2).ne'
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  -- G₀'s denominator is nonzero — this is exactly `Q0_ne_zero_at_yukawa`.
  have hden : G0denom xi z ≠ 0 := FMSA.HardSphere.Q0_ne_zero_at_yukawa hxi hz
  rw [bhF_base, bhP_base]
  -- Unfold everything *except* `G0denom`, so `field_simp` can clear it as an atom via `hden`.
  simp only [G0, bhP0, Qhat0, phi1, phi2, bA0, qp0, rhoOf]
  field_simp
  -- Now expose the atom; the identity is polynomial in `(xi, z, e^{−z})` and holds for arbitrary
  -- `e^{−z}`, so `ring` closes it.
  simp only [G0denom]
  ring

/-- **MSAFAM.2 (iii)** — the hard-sphere Baxter factor is nonzero at the base point,
`bhF (0, G₀) ≠ 0`.  Follows from the base equation `2π·(G₀·bhF(0,G₀)) = bhP(0,G₀)` and the strict
positivity of `bhP (0, G₀) = (A⁰ + z q⁰′)/z² > 0`; equivalently `F₀ = C·G0denom` with `C ≠ 0` and
`G0denom ≠ 0` by `Q0_ne_zero_at_yukawa`. -/
theorem bhF_base_ne_zero {xi z : ℝ} (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) (hz : 0 < z) :
    bhF xi z (0, G0 xi z) ≠ 0 := by
  have h1 : (0 : ℝ) < 1 - xi := sub_pos.mpr hxi.2
  have hx : (0 : ℝ) < xi := hxi.1
  have hA : 0 < bA0 xi := by
    simp only [bA0]
    exact mul_pos (div_pos (by positivity) (pow_pos h1 2)) (by linarith)
  have hq : 0 < qp0 xi := by
    simp only [qp0]
    exact mul_pos (div_pos (by positivity) (pow_pos h1 2)) (by linarith)
  have hpos : 0 < bhP xi z (0, G0 xi z) := by
    rw [bhP_base]
    simp only [bhP0]
    exact div_pos (by positivity) (by positivity)
  intro hF0
  have hbase := bh_base_eq hxi hz
  rw [hF0, mul_zero, mul_zero] at hbase
  exact (ne_of_lt hpos) hbase

end FMSA.ExactMSA
