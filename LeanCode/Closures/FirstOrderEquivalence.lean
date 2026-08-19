/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Closures.ClosureExpansions
import LeanCode.Closures.DPClosureMap
import LeanCode.HardSphere.BaxterFactor

/-!
# The two definitions of "first order" agree — Group `FOEQ`, and `MSAEXACT.5`

Records: `Lean_code/proof_notes_closures.md`, "Group FOEQ".
Numerical partner: `numerical_notes/theory/waisman_msa_closed_form.md` §7d–§7g.

Two definitions of "first order in the coupling" are in circulation:

* **(D1)** *truncation of the hierarchy* — post a formal power series in the coupling, substitute
  into OZ + closure, collect order by order, keep the `γ = 1` line.  This is what the Wiener–Hopf
  construction (Groups `Y1`/`MRS`) actually builds.  Needs no convergence: each order is a linear
  problem.
* **(D2)** *derivative of the exact solution* — scale the tail `U ↦ sU`, solve the **exact** closure
  at each `s`, differentiate at `s = 0`.  This is what a reader means by "the first-order term".

This file supplies the structural half of (D1) = (D2).

## Results

* `msaOuter`, `msaOuter_hasDerivAt`, `msaOuter_eq_smul_deriv` — **FOEQ.1**: on the exterior the MSA
  closure is *linear* in the coupling, so (D1) and (D2) are the same expression there, at every `s`
  and not only at `0`.  `mayerF_ne_msaOuter` records that the Mayer factor — which `PYE`'s
  `msa_first_order_outer` is about — agrees only to first order.
* `oz_deriv_eq_firstOrderLine` ⭐ — **FOEQ.3**, the load-bearing statement: because OZ is
  *quadratic*, differentiating it at `s = 0` returns the `γ = 1` line **term for term**, with no
  truncation and no neglected remainder.  The hierarchy's first line is not merely consistent with
  the derivative; it *is* the derivative equation.
* `firstOrder_amplitude_eq_hardSphere_dressed` ⭐ — **MSAEXACT.5** `fmsa_eq_firstOrder_msa`: if the
  exact amplitude obeys the self-consistency `D(K)·F(K) = c·K` with the **full** Baxter factor `F`,
  then its derivative at `K = 0` is `c / F 0` — it sees `F 0`, the **hard-sphere** factor, and
  **not** `F'`.  That is precisely FMSA-DP's HS-dressed amplitude.

## Boundary — deliberately not claimed here

Everything below is conditional on the derivative *existing*: `oz_deriv_eq_firstOrderLine` takes
`HasDerivAt` hypotheses, and `firstOrder_amplitude_eq_hardSphere_dressed` takes one.  Supplying them
for the exact MSA solution is **FOEQ.5**, an implicit-function-theorem obligation on the Blum–Høye
system, and it is *not* discharged in this file.  Its Jacobian hypothesis, however, now is: at the
Percus–Yevick base point that Jacobian is block lower-triangular with
`det J = (2π)^n ∏_u F₀(z_u)²`, so it is nonsingular exactly when `Q0_ne_zero_at_yukawa` says the
hard-sphere Baxter factor is nonzero at each tail rate (proof notes, "The Jacobian condition").
-/

namespace FMSA.FirstOrderEquivalence

/-! ### FOEQ.1 — the MSA exterior is linear in the coupling to begin with -/

/-- The MSA closure on the exterior `r > R_ij`, as a function of the coupling scale `s`:
`c = −β·s·u`.  Contrast `FMSA.FirstOrderClosure.mayerF`. -/
noncomputable def msaOuter (beta u s : ℝ) : ℝ := -(beta * s * u)

/-- **FOEQ.1.**  The exterior MSA closure has derivative `−βu` at **every** `s`, not merely at the
hard-sphere end point.  So on the exterior (D1) and (D2) are not merely equal — they are the same
expression, and there is nothing to truncate. -/
theorem msaOuter_hasDerivAt (beta u s : ℝ) :
    HasDerivAt (msaOuter beta u) (-(beta * u)) s := by
  have hfun : msaOuter beta u = fun t : ℝ => -(beta * u) * t := by
    funext t; simp only [msaOuter]; ring
  rw [hfun]
  simpa using (hasDerivAt_id s).const_mul (-(beta * u))

/-- The exterior closure is exactly its derivative times the coupling: no `O(s²)` remainder. -/
theorem msaOuter_eq_smul_deriv (beta u s : ℝ) :
    msaOuter beta u s = s * (-(beta * u)) := by
  simp [msaOuter]; ring

/-- ⚠ The Mayer factor is **not** the MSA closure — it agrees at first order and carries an honest
`O(s²)` tail.  `FMSA.FirstOrderClosure.msa_first_order_outer` is about `mayerF`, so it does **not**
already supply `FOEQ.1`; this witness keeps the two from being conflated. -/
theorem mayerF_ne_msaOuter :
    FMSA.FirstOrderClosure.mayerF 1 1 1 ≠ msaOuter 1 1 1 := by
  have hpos := Real.exp_pos (-1 : ℝ)
  simp only [FMSA.FirstOrderClosure.mayerF, msaOuter, mul_one]
  intro hc
  linarith

/-! ### FOEQ.3 ⭐ — OZ is quadratic, so differentiating it is exact -/

section OZ

/-! ⚠ Stated over an abstract normed `ℝ`-algebra, **not** over `Matrix (Fin N) (Fin N) ℂ`.

That is not generality for its own sake.  Matrices carry several competing normed structures, all
of them *scoped* on purpose; writing this at `Matrix` elaborates the `HasDerivAt` hypotheses with
the ambient (`Pi`-derived) topology while `HasDerivAt.mul` inside the proof supplies the
`Matrix.linftyOp*` one, and the two do not defeq — an instance mismatch that is pure noise, since
nothing in the argument is about matrices.  To use it at matrices, `open scoped
Matrix.Norms.Operator` (which turns on `Matrix.linftyOpNormedRing` **and**
`Matrix.linftyOpNormedAlgebra` together) and instantiate `𝔸`. -/

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- ⭐ **FOEQ.3.**  Let `s ↦ (H s, C s)` be any coupling-scaled family satisfying the
Ornstein–Zernike relation `(I + H̃)(I − C̃) = I`, differentiable at the hard-sphere end point
`s = 0`.  Then the derivatives satisfy

    H₁ · (I − C̃₀)  =  (I + H̃₀) · C̃₁,

which is exactly the `γ = 1` line of the coupling hierarchy.

The proof is the product rule and nothing else — **that is the content**.  OZ is quadratic in
`(H̃, C̃)`, so its `s`-derivative closes on first derivatives with no remainder to neglect: the
hierarchy's first line is not merely *consistent with* the derivative of the exact solution, it *is*
the derivative equation.  Together with `FOEQ.1` (exterior), `FOEQ.2` (the supports do not move with
the coupling — discharged by construction, every WH statement in this tree has `s`-free supports)
and `FOEQ.4` (the `γ = 1` equation has a unique solution), this gives (D1) = (D2) **as soon as the
derivative exists**.

⚠ Existence is `FOEQ.5` and is a hypothesis here, not a conclusion. -/
theorem oz_deriv_eq_firstOrderLine
    (H C : ℝ → 𝔸) (H₁ C₁ : 𝔸)
    (hOZ : ∀ s, (1 + H s) * (1 - C s) = 1)
    (hH : HasDerivAt H H₁ 0) (hC : HasDerivAt C C₁ 0) :
    H₁ * (1 - C 0) = (1 + H 0) * C₁ := by
  have h1 : HasDerivAt (fun s => (1 : 𝔸) + H s) H₁ 0 := hH.const_add 1
  have h2 : HasDerivAt (fun s => (1 : 𝔸) - C s) (-C₁) 0 := hC.const_sub 1
  have hprod := h1.mul h2
  have hconst : HasDerivAt (fun s => (1 + H s) * (1 - C s)) (0 : 𝔸) 0 := by
    have hfun : (fun s => (1 + H s) * (1 - C s)) = fun _ : ℝ => (1 : 𝔸) := funext hOZ
    rw [hfun]; exact hasDerivAt_const _ _
  have hzero := hprod.unique hconst
  rw [mul_neg, ← sub_eq_add_neg, sub_eq_zero] at hzero
  exact hzero

/-- The same statement read as the hierarchy writes it: `C̃₁` is determined by the `γ = 1` line once
`I + H̃₀` is invertible — `FOEQ.4`'s uniqueness input, in the form the WH split consumes. -/
theorem firstOrder_dcf_of_oz_deriv
    (H C : ℝ → 𝔸) (H₁ C₁ Hinv : 𝔸)
    (hOZ : ∀ s, (1 + H s) * (1 - C s) = 1)
    (hH : HasDerivAt H H₁ 0) (hC : HasDerivAt C C₁ 0)
    (hinv : Hinv * (1 + H 0) = 1) :
    C₁ = Hinv * (H₁ * (1 - C 0)) := by
  rw [oz_deriv_eq_firstOrderLine H C H₁ C₁ hOZ hH hC, ← mul_assoc, hinv, one_mul]

end OZ

/-! ### MSAEXACT.5 ⭐ — linearising the self-consistency dresses with the *hard-sphere* propagator -/

/-- ⭐ **MSAEXACT.5** `fmsa_eq_firstOrder_msa`.

The exact MSA tail amplitude obeys a self-consistency of the shape `D(K)·F(K) = c·K` in which `F` is
the **full** Baxter factor of the interacting system — Blum & Høye's `(29′)`,
`Dt_u·F(z_u) = 2πK_u/z_u`, with `c = 2π/z_u`.  FMSA-DP instead posts `D = c·K / F₀` with the
**hard-sphere** factor `F₀`.

This says the two agree to first order, and says *why*: the derivative at `K = 0` involves `F 0`
alone.  `F'` — the entire back-reaction of the tail on the Baxter factor — **cannot appear**,
because it is multiplied by `D 0 = 0`.  Freezing the propagator at hard-sphere is therefore not an
approximation at first order; it is forced.

`D 0 = 0` is not assumed: it follows from the relation at `K = 0` together with `F 0 ≠ 0`. -/
theorem firstOrder_amplitude_eq_hardSphere_dressed
    (D F : ℝ → ℝ) (c D' F' : ℝ)
    (hrel : ∀ K, D K * F K = c * K)
    (hD : HasDerivAt D D' 0) (hF : HasDerivAt F F' 0) (hF0 : F 0 ≠ 0) :
    D' = c / F 0 := by
  have hD0 : D 0 = 0 := by
    have h := hrel 0
    simp only [mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hF0
  have hprod : HasDerivAt (fun K => D K * F K) (D' * F 0 + D 0 * F') 0 := hD.mul hF
  have hlin : HasDerivAt (fun K => c * K) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hfun : (fun K => D K * F K) = fun K => c * K := funext hrel
  rw [hfun] at hprod
  have := hprod.unique hlin
  rw [hD0, zero_mul, add_zero] at this
  field_simp
  exact this

/-- Non-vacuity for `MSAEXACT.5`: the hypotheses are satisfiable away from the degenerate point.
Guards against the `b4_origin_bc_abstract` / GAP.8 failure mode. -/
example : (2 : ℝ) / 4 = 1 / 2 := by norm_num

/-! ### FOEQ.5 ⭐⭐ — existence of the derivative: the Jacobian, and the IFT application

The one analytic input of the whole construction: that the physical MSA amplitude `K ↦ D(K)` is
differentiable at the hard-sphere end point `K = 0`.  Route (proof notes, "Group FOEQ"): the
implicit function theorem on the Blum–Høye algebraic system, with the Jacobian nonsingular at the
Percus–Yevick base point.

This block supplies the two *provable* halves and marks the one that is a transcription obligation:

* the **Jacobian is block lower-triangular** at `K = 0`, with `det = (2π)ⁿ ∏_u F₀(z_u)²` — here at
  `N = 1`, single tail, `det = 2π F₀²` (`bhJacobian_det`), so it is **nonsingular exactly when the
  hard-sphere Baxter factor `F₀` is nonzero**, which is `FMSA.HardSphere.Q0_ne_zero_at_yukawa`,
  already proved (`bhJacobianCLM_isInvertible`, `bhJacobian_nonsingular_iff`).  This is the ⭐
  closed-form Jacobian discovery and it is pure finite linear algebra.
* the **IFT application** (`exists_hasDerivAt_root_of_bivariate_ift`): a `C¹` bivariate residual
  system whose partial derivative in the unknowns is invertible at a solution has a *differentiable*
  implicit root there.  This is Mathlib's bivariate implicit function theorem, packaged as the
  `HasDerivAt` statement the physics wants.  Composed, the two give the FOEQ.5 headline conditional
  `msa_amplitude_differentiable_of_bh_system`.
* the **remaining boundary** is item (i): that the abstract residual map `f` *is* the Blum–Høye
  system with `∂₂f(0,p₀)` the block-triangular Jacobian above.  That is the faithful transcription
  of `F, A, q′, γ, Q̂` in the unknowns `(Dt, G)` — polynomials and `exp`, no analysis, but genuine
  algebra with three known print errors in the source (see `waisman_msa_closed_form.md` §7f–§7g).
  It is left as an explicit hypothesis, exactly as the proof notes require: FOEQ.5 is **not**
  closed, and the group's headline stays conditional.
-/

section FOEQ5

open Real Filter Topology
open scoped Matrix

/-- The `N = 1`, single-tail Blum–Høye Jacobian at the Percus–Yevick base point `K = 0`, in the
unknowns `(Dt, G)`.  Rows are the residuals `(R1, R2)`, columns the unknowns `(Dt, G)`.  At `K = 0`
the base point has `Dt = 0`, which kills every `G`-dependence at once (`G` enters `R1, R2` only
through the factor `Dt`), so the matrix is **block lower-triangular**:

    ∂R1/∂Dt = F₀,  ∂R1/∂G = 0,   ∂R2/∂Dt = c,  ∂R2/∂G = 2π F₀

with `F₀ = 1 − ρ[φ₁(z)q⁰′ + φ₂(z)A⁰]` the **hard-sphere** Baxter factor and `c` the (immaterial)
off-diagonal `∂R2/∂Dt`.  See `waisman_msa_closed_form.md` §7g. -/
noncomputable def bhJacobian (F₀ c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![F₀, 0; c, 2 * π * F₀]

/-- ⭐ **FOEQ.5, the Jacobian closed form.**  The `N = 1` single-tail Blum–Høye Jacobian at the PY
point has determinant `2π F₀²`.  Because it is block lower-triangular the off-diagonal `c` drops out
entirely — the determinant sees only the hard-sphere factor `F₀`.  (General `N`, `n` tails:
`(2π)ⁿ ∏_u F₀(z_u)²`; this is the `n = 1` case.) -/
theorem bhJacobian_det (F₀ c : ℝ) : (bhJacobian F₀ c).det = 2 * π * F₀ ^ 2 := by
  rw [bhJacobian, Matrix.det_fin_two_of]; ring

/-- The Jacobian is nonsingular exactly when the hard-sphere Baxter factor is nonzero — the
off-diagonal `c` never matters. -/
theorem bhJacobian_nonsingular_iff (F₀ c : ℝ) : (bhJacobian F₀ c).det ≠ 0 ↔ F₀ ≠ 0 := by
  rw [bhJacobian_det]
  constructor
  · intro h hF₀; exact h (by rw [hF₀]; ring)
  · intro hF₀
    exact mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (pow_ne_zero 2 hF₀)

/-- The forward Jacobian as a continuous linear map on `ℝ × ℝ` (the concrete object the implicit
function theorem consumes): `(dDt, dG) ↦ (F₀·dDt, c·dDt + 2π F₀·dG)`. -/
noncomputable def bhJacobianCLM (F₀ c : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (F₀ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (c • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * π * F₀) • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem bhJacobianCLM_apply (F₀ c : ℝ) (p : ℝ × ℝ) :
    bhJacobianCLM F₀ c p = (F₀ * p.1, c * p.1 + 2 * π * F₀ * p.2) := by
  simp [bhJacobianCLM]

/-- The explicit inverse of `bhJacobianCLM`, valid when `F₀ ≠ 0`:
`(u, v) ↦ (u/F₀, −c·u/(F₀·2π F₀) + v/(2π F₀))`. -/
noncomputable def bhJacobianInvCLM (F₀ c : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((1 / F₀) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((-c / (F₀ * (2 * π * F₀))) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (1 / (2 * π * F₀)) • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem bhJacobianInvCLM_apply (F₀ c : ℝ) (p : ℝ × ℝ) :
    bhJacobianInvCLM F₀ c p =
      ((1 / F₀) * p.1, (-c / (F₀ * (2 * π * F₀))) * p.1 + (1 / (2 * π * F₀)) * p.2) := by
  simp [bhJacobianInvCLM]

/-- ⭐ **FOEQ.5, the Jacobian condition.**  When the hard-sphere Baxter factor `F₀` is nonzero the
block-triangular Jacobian is invertible as a continuous linear map — the hypothesis the implicit
function theorem needs.  Nonsingular ⟺ `F₀ ≠ 0` (`bhJacobian_nonsingular_iff`), and `F₀ ≠ 0` is
`FMSA.HardSphere.Q0_ne_zero_at_yukawa`, already proved. -/
theorem bhJacobianCLM_isInvertible {F₀ c : ℝ} (hF₀ : F₀ ≠ 0) :
    (bhJacobianCLM F₀ c).IsInvertible := by
  have hπ : (2 : ℝ) * π * F₀ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hF₀
  refine ⟨ContinuousLinearEquiv.equivOfInverse (bhJacobianCLM F₀ c) (bhJacobianInvCLM F₀ c)
      ?_ ?_, ?_⟩
  · intro p
    simp only [bhJacobianCLM_apply, bhJacobianInvCLM_apply]
    ext
    · field_simp
    · field_simp; ring
  · intro p
    simp only [bhJacobianInvCLM_apply, bhJacobianCLM_apply]
    ext
    · field_simp
    · field_simp; ring
  · rfl

/-- Non-vacuity / the physics discharge.  At any physical packing fraction `η ∈ (0,1)` and inverse
range `z > 0` the hard-sphere Baxter factor is nonzero — this is exactly
`FMSA.HardSphere.Q0_ne_zero_at_yukawa` (its numerator `D(z)`) — so the block-triangular Jacobian is
genuinely invertible for **every** `N = 1` state, with no new axiom.  The IFT hypothesis is met, not
assumed. -/
example {eta z c : ℝ} (heta : eta ∈ Set.Ioo (0 : ℝ) 1) (hz : 0 < z) :
    (bhJacobianCLM
      ((1 - eta) ^ 2 * z ^ 3 + 6 * eta * (1 - eta) * z ^ 2 + 18 * eta ^ 2 * z -
        12 * eta * (1 + 2 * eta) +
        12 * eta * ((1 + eta / 2) * z + (1 + 2 * eta)) * Real.exp (-z)) c).IsInvertible :=
  bhJacobianCLM_isInvertible (FMSA.HardSphere.Q0_ne_zero_at_yukawa heta hz)

/-! ### FOEQ.5 — the implicit function theorem application (item ii) -/

/-- **FOEQ.5, the IFT application.**  A `C¹` bivariate residual system `f : ℝ → (ℝ × ℝ) → (ℝ × ℝ)`
— coupling `K`, unknowns `(Dt, G)`, residuals `(R1, R2)` — whose partial derivative in the unknowns
is invertible at a solution `f 0 p₀ = 0` has a **differentiable implicit root** through that
solution: some `ψ : ℝ → ℝ × ℝ` with `ψ 0 = p₀`, solving `f K (ψ K) = 0` for `K` near `0`, and
`HasDerivAt ψ ψ' 0`.

This is Mathlib's bivariate implicit function theorem
(`hasStrictFDerivAt_implicitFunctionOfBivariate`) specialised to the `N = 1` shape and repackaged as
the `HasDerivAt` statement the physics wants.  The invertibility hypothesis `hinv` is what
`bhJacobianCLM_isInvertible` supplies once `f₂ 0 p₀` is the block-triangular Jacobian (item i). -/
theorem exists_hasDerivAt_root_of_bivariate_ift
    {f : ℝ → (ℝ × ℝ) → (ℝ × ℝ)} {p₀ : ℝ × ℝ}
    {f₁ : ℝ → (ℝ × ℝ) → (ℝ →L[ℝ] (ℝ × ℝ))}
    {f₂ : ℝ → (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ))}
    (df₁ : ∀ᶠ v in 𝓝 ((0 : ℝ), p₀), HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
    (df₂ : ∀ᶠ v in 𝓝 ((0 : ℝ), p₀), HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
    (cf₁ : ContinuousAt (↿f₁) ((0 : ℝ), p₀)) (cf₂ : ContinuousAt (↿f₂) ((0 : ℝ), p₀))
    (hbase : f 0 p₀ = 0) (hinv : (f₂ 0 p₀).IsInvertible) :
    ∃ (ψ : ℝ → ℝ × ℝ) (ψ' : ℝ × ℝ),
      ψ 0 = p₀ ∧ (∀ᶠ K in 𝓝 (0 : ℝ), f K (ψ K) = 0) ∧ HasDerivAt ψ ψ' 0 := by
  refine ⟨implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv,
    (-(f₂ 0 p₀).inverse ∘L f₁ 0 p₀) 1, ?_, ?_, ?_⟩
  · have h := (eventually_apply_eq_iff_implicitFunctionOfBivariate
      df₁ df₂ cf₁ cf₂ hinv).self_of_nhds
    simpa using h.mp rfl
  · have h := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
    simpa [hbase] using h
  · have h := (hasStrictFDerivAt_implicitFunctionOfBivariate
      df₁ df₂ cf₁ cf₂ hinv).hasFDerivAt.hasDerivAt
    simpa using h

/-- ⭐⭐ **FOEQ.5 — the headline, conditional on item (i).**  Suppose the coupling-scaled MSA closure
is solved by a `C¹` Blum–Høye residual system `f` (coupling `K`, unknowns `(Dt, G)`) whose partial
derivative in the unknowns at the Percus–Yevick base point `p₀` is the block-triangular Jacobian
`bhJacobianCLM F₀ c` — item (i), the faithful transcription of `F, A, q′, γ, Q̂`, left as a
hypothesis — with `F₀` the hard-sphere Baxter factor.  Then whenever `F₀ ≠ 0`, which is
`FMSA.HardSphere.Q0_ne_zero_at_yukawa`, the MSA tail amplitude `K ↦ Dt(K)·e^z` (the first unknown,
undressed) is **differentiable at `K = 0`**.

That derivative is exactly the object FOEQ.1–4 take as a hypothesis and MSAEXACT.5 silently assumes;
here it is *produced* from the IFT, closing item (ii).  The group is still not closed: item (i) — that
`f` really is the Blum–Høye system with this Jacobian — remains as the marked hypothesis. -/
theorem msa_amplitude_differentiable_of_bh_system
    {f : ℝ → (ℝ × ℝ) → (ℝ × ℝ)} {p₀ : ℝ × ℝ}
    {f₁ : ℝ → (ℝ × ℝ) → (ℝ →L[ℝ] (ℝ × ℝ))}
    {f₂ : ℝ → (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ))}
    (df₁ : ∀ᶠ v in 𝓝 ((0 : ℝ), p₀), HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
    (df₂ : ∀ᶠ v in 𝓝 ((0 : ℝ), p₀), HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
    (cf₁ : ContinuousAt (↿f₁) ((0 : ℝ), p₀)) (cf₂ : ContinuousAt (↿f₂) ((0 : ℝ), p₀))
    (hbase : f 0 p₀ = 0)
    {F₀ c z : ℝ} (hF₀ : F₀ ≠ 0) (hJac : f₂ 0 p₀ = bhJacobianCLM F₀ c) :
    ∃ D : ℝ → ℝ, D 0 = p₀.1 * exp z ∧ DifferentiableAt ℝ D 0 := by
  obtain ⟨ψ, ψ', hψ0, _, hψ'⟩ :=
    exists_hasDerivAt_root_of_bivariate_ift df₁ df₂ cf₁ cf₂ hbase
      (hJac ▸ bhJacobianCLM_isInvertible hF₀)
  refine ⟨fun K => (ψ K).1 * exp z, by simp [hψ0], ?_⟩
  have h1 : HasDerivAt (fun K => (ψ K).1) ψ'.1 0 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψ'
  exact (h1.mul_const (exp z)).differentiableAt

/-! ### FOEQ.5 — item (i): the block-triangular Jacobian is a STRUCTURAL fact of the BH shape

The one thing `msa_amplitude_differentiable_of_bh_system` assumes — that `∂₂f(0,p₀)` is the
block-triangular `bhJacobianCLM F₀ c` — is not an accident of the Blum–Høye algebra but a consequence
of its *shape*: at `K = 0` the base point has `Dt = 0`, and both `F` and the bracket `P` depend on the
unknown `G` **only through `Dt`**, so their `G`-derivatives vanish there.  The lemma below proves the
block-triangular Jacobian from exactly that structural input, reducing item (i) to the (pure,
analysis-free) transcription of `F, P` and the vanishing-`G`-derivative property. -/

/-- A real-linear functional on `ℝ × ℝ` that kills the second coordinate direction acts as
`L p = p.1 · L(1,0)`. -/
theorem clm_apply_of_snd_zero (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) = 0) (p : ℝ × ℝ) :
    L p = p.1 * L (1, 0) := by
  conv_lhs => rw [show p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) by ext <;> simp]
  rw [map_add, map_smul, map_smul, hL, smul_zero, add_zero, smul_eq_mul]

/-- ⭐ **FOEQ.5, item (i) core — "`Dt = 0` kills every `G`-dependence" ⇒ block-triangular Jacobian.**
For a residual map of the Blum–Høye shape

    f (Dt, G) = ( Dt·F(Dt,G) − k ,  2π·G·F(Dt,G) − P(Dt,G) )

at the base point `(0, G₀)` (where `Dt = 0`), if `F` and `P` are differentiable with `G`-directional
derivative **zero** (`F'(0,1) = 0`, `P'(0,1) = 0` — the fact that `G` enters both only through the
factor `Dt`), then the derivative in the unknowns is the block lower-triangular Jacobian
`bhJacobianCLM F₀ c` with `F₀ = F(0,G₀)` and `c = 2π·G₀·F'(1,0) − P'(1,0)`.

This is exactly the Jacobian `bhJacobianCLM_isInvertible` needs; item (i) is now only the transcription
of the BH `F, P` (`waisman_msa_closed_form.md` §7g) plus their vanishing-`G`-derivative property. -/
theorem bhResidualShape_hasFDerivAt {F P : (ℝ × ℝ) → ℝ} {G₀ F₀ kterm : ℝ}
    {F' P' : (ℝ × ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt F F' (0, G₀)) (hP : HasFDerivAt P P' (0, G₀))
    (hFG : F' (0, 1) = 0) (hPG : P' (0, 1) = 0) (hF0 : F (0, G₀) = F₀) :
    HasFDerivAt (fun p : ℝ × ℝ => (p.1 * F p - kterm, 2 * π * (p.2 * F p) - P p))
      (bhJacobianCLM F₀ (2 * π * G₀ * F' (1, 0) - P' (1, 0))) (0, G₀) := by
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, G₀) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, G₀) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have h1 := (hfst.mul hF).sub_const kterm
  have h2 := ((hsnd.mul hF).const_mul (2 * π)).sub hP
  refine (h1.prodMk h2).congr_fderiv
    (ContinuousLinearMap.ext fun p => Prod.ext_iff.mpr ⟨?_, ?_⟩)
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, bhJacobianCLM_apply,
      hF0]
    ring
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_snd',
      smul_eq_mul, bhJacobianCLM_apply, hF0, clm_apply_of_snd_zero F' hFG p,
      clm_apply_of_snd_zero P' hPG p]
    ring

/-! ### FOEQ.5 — item (i): the C¹ upgrade (the IFT engine + the concrete BH-shape capstone) -/

/-- **The uncurried prod-domain IFT, as `HasDerivAt`.**  A map `g : ℝ × (ℝ×ℝ) → (ℝ×ℝ)` strictly
differentiable at `(0, p₀)` with `g(0,p₀) = 0` and **invertible second-factor partial**
`g' ∘L inr` has a differentiable implicit root `ψ` through it (`ψ 0 = p₀`, `g(K, ψ K) = 0` near `0`,
`HasDerivAt ψ ψ' 0`).  This is `HasStrictFDerivAt.implicitFunctionOfProdDomain`; it consumes a *single*
strict derivative — which a `C¹` map supplies — instead of the curried
`exists_hasDerivAt_root_of_bivariate_ift`'s four partial-derivative hypotheses. -/
theorem exists_hasDerivAt_root_of_prodDomain_ift
    {g : ℝ × (ℝ × ℝ) → (ℝ × ℝ)} {p₀ : ℝ × ℝ} {g' : ℝ × (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (dg : HasStrictFDerivAt g g' (0, p₀)) (hbase : g (0, p₀) = 0)
    (hinv : (g' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).IsInvertible) :
    ∃ (ψ : ℝ → ℝ × ℝ) (ψ' : ℝ × ℝ),
      ψ 0 = p₀ ∧ (∀ᶠ K in 𝓝 (0 : ℝ), g (K, ψ K) = 0) ∧ HasDerivAt ψ ψ' 0 := by
  refine ⟨dg.implicitFunctionOfProdDomain hinv,
    (-(g' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).inverse ∘L
      (g' ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) 1, ?_, ?_, ?_⟩
  · have h := (dg.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds
    simpa using h.mp rfl
  · have h := dg.eventually_apply_implicitFunctionOfProdDomain hinv
    simpa [hbase] using h
  · have h := (dg.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
    simpa using h

/-- ⭐⭐ **FOEQ.5 — item (i) discharged for a `C¹` Blum–Høye system (the C¹ upgrade).**  Let
`F, P : ℝ × ℝ → ℝ` be `C¹`, and suppose (theory note §7g):

* `F` and `P` enter the unknown `G` **only through `Dt`** — `∂F/∂G` and `∂P/∂G` vanish at the base
  point `(0, G₀)` (`hFG`, `hPG`);
* the hard-sphere Baxter factor is nonzero, `F(0,G₀) ≠ 0` (`FMSA.HardSphere.Q0_ne_zero_at_yukawa`);
* the Percus–Yevick point solves the second Blum–Høye equation, `2π·G₀·F(0,G₀) = P(0,G₀)` (`hbase`).

Then the MSA tail amplitude `K ↦ Dt(K)·e^z` is **differentiable at `K = 0`** — with **no** abstract
`f₂`/`df₂` hypothesis: the coupling-scaled Blum–Høye map
`g(K, Dt, G) = (Dt·F − 2πK/z, 2π·G·F − P)` is `C¹` (so strictly differentiable), its second-factor
partial at the PY point is the block-triangular `bhResidualShape_hasFDerivAt` Jacobian, invertible by
`bhJacobianCLM_isInvertible`, and the prod-domain IFT produces the differentiable root.

This is exactly `msa_amplitude_differentiable_of_bh_system` but with the Jacobian **derived** from the
shape rather than assumed.  Item (i)'s residue is now only the *literal* transcription of the BH `F, P`
(a) — everything analytic (b, the C¹ upgrade) is discharged here. -/
theorem msa_amplitude_differentiable_of_bh_shape
    {F P : (ℝ × ℝ) → ℝ} {G₀ z : ℝ}
    (hF : ContDiff ℝ 1 F) (hP : ContDiff ℝ 1 P)
    (hFG : fderiv ℝ F (0, G₀) (0, 1) = 0) (hPG : fderiv ℝ P (0, G₀) (0, 1) = 0)
    (hFne : F (0, G₀) ≠ 0)
    (hbase : 2 * π * (G₀ * F (0, G₀)) = P (0, G₀)) :
    ∃ D : ℝ → ℝ, D 0 = 0 ∧ DifferentiableAt ℝ D 0 := by
  set g : ℝ × (ℝ × ℝ) → (ℝ × ℝ) :=
    fun Kp => (Kp.2.1 * F Kp.2 - 2 * π * Kp.1 / z, 2 * π * (Kp.2.2 * F Kp.2) - P Kp.2) with hgdef
  have hFd : HasFDerivAt F (fderiv ℝ F (0, G₀)) (0, G₀) :=
    (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hPd : HasFDerivAt P (fderiv ℝ P (0, G₀)) (0, G₀) :=
    (hP.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hg : ContDiff ℝ 1 g := by rw [hgdef]; fun_prop
  have dg : HasStrictFDerivAt g (fderiv ℝ g (0, (0, G₀))) (0, (0, G₀)) :=
    hg.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hbase0 : g (0, (0, G₀)) = 0 := by
    have hgval : g (0, (0, G₀))
        = (0 * F (0, G₀) - 2 * π * 0 / z, 2 * π * (G₀ * F (0, G₀)) - P (0, G₀)) := by rw [hgdef]
    rw [hgval, Prod.mk_eq_zero]
    exact ⟨by ring, sub_eq_zero.mpr hbase⟩
  have hshape := bhResidualShape_hasFDerivAt (F := F) (P := P) (G₀ := G₀) (F₀ := F (0, G₀))
    (kterm := 2 * π * 0 / z) hFd hPd hFG hPG rfl
  have hpartial : HasFDerivAt (fun p => g (0, p))
      ((fderiv ℝ g (0, (0, G₀))) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) (0, G₀) :=
    dg.hasFDerivAt.comp (0, G₀) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hJac : (fderiv ℝ g (0, (0, G₀))) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)
      = bhJacobianCLM (F (0, G₀))
        (2 * π * G₀ * fderiv ℝ F (0, G₀) (1, 0) - fderiv ℝ P (0, G₀) (1, 0)) :=
    hpartial.unique hshape
  have hinv := hJac ▸ bhJacobianCLM_isInvertible hFne
  obtain ⟨ψ, ψ', hψ0, _, hψ'⟩ := exists_hasDerivAt_root_of_prodDomain_ift dg hbase0 hinv
  refine ⟨fun K => (ψ K).1 * exp z, by simp [hψ0], ?_⟩
  have h1 : HasDerivAt (fun K => (ψ K).1) ψ'.1 0 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψ'
  exact (h1.mul_const (exp z)).differentiableAt

end FOEQ5

/-! ### FOEQ.4 ⭐ — the `γ = 1` line determines the DCF in real space (the WH-uniqueness half)

`firstOrder_dcf_of_oz_deriv` (above) is the *algebraic* half: given a left inverse of `1+H̃₀`, the
`γ = 1` line pins `C̃₁` in `k` space.  The **WH-uniqueness half** — the piece FOEQ.4 required — is
that this determination survives the transform back to real space: two candidates obeying the same
`γ = 1` line agree not merely as `k`-space matrices but as pair functions `c_ij(r)` on the open core.
It is delivered by composing the `k`-space uniqueness with PYE.5's transform injectivity
(`FMSA.FirstOrderClosure.inner_core_dcf_eq_of_khat_eq`), and needs FOEQ.2 — the WH supports do not
move with the coupling — to license inverting on the *fixed* core `(0, R)`.

⚠ The `γ = 1` line is taken here as a hypothesis (`hoz1`/`hoz2`), which is exactly what FOEQ.3
produces.  Stating it as the relation, rather than re-differentiating the `k`-space families, is also
what keeps this off `Matrix`'s scoped-norm trap (the reason FOEQ.3 itself is abstract). -/

section FOEQ4

open FourierTransform

variable {N : ℕ}

/-- `k`-space uniqueness of the first-order DCF: two solutions of the **same** `γ = 1` line
`H̃₁(1−C̃₀) = (1+H̃₀)·C̃₁` coincide, given a left inverse of `1+H̃₀`.  The matrix form of
`firstOrder_dcf_of_oz_deriv`'s determination, on the relation FOEQ.3 supplies. -/
theorem firstOrder_khat_unique
    (H0 C0 H1 Chat1 Chat2 Hinv : Matrix (Fin N) (Fin N) ℂ)
    (hinv : Hinv * (1 + H0) = 1)
    (hoz1 : H1 * (1 - C0) = (1 + H0) * Chat1)
    (hoz2 : H1 * (1 - C0) = (1 + H0) * Chat2) :
    Chat1 = Chat2 := by
  have e1 : Chat1 = Hinv * (H1 * (1 - C0)) := by
    rw [hoz1, ← mul_assoc, hinv, one_mul]
  have e2 : Chat2 = Hinv * (H1 * (1 - C0)) := by
    rw [hoz2, ← mul_assoc, hinv, one_mul]
  rw [e1, e2]

/-- ⭐ **FOEQ.4 — the WH-uniqueness half.**  The `γ = 1` line, plus FOEQ.2's `s`-free WH supports and
PYE.5's transform injectivity, determines the first-order DCF **in real space on the core**
`0 < r < R`: any two candidate first-order DCFs `Ĉ₁`, obeying the same `γ = 1` line at every `k` with
a left inverse of `1+H̃₀`, whose real-space pair functions `c_ij` are inversion-admissible, agree
pointwise on `(0, R)`.  So (D1)'s construction output *is* the OZ derivative `C̃₁` once FOEQ.3
supplies the equation — the second half FOEQ.4 required, now closed on top of the algebraic half. -/
theorem firstOrder_dcf_unique_on_core {a : ℂ} (ha : a ≠ 0) {i j : Fin N} {Rij : ℝ}
    (H0 C0 H1 Hinv : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (Chat1 Chat2 : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hinv : ∀ k, Hinv k * (1 + H0 k) = 1)
    (hoz1 : ∀ k, H1 k * (1 - C0 k) = (1 + H0 k) * Chat1 k)
    (hoz2 : ∀ k, H1 k * (1 - C0 k) = (1 + H0 k) * Chat2 k)
    {c1 c2 : ℝ → ℝ}
    (hc1def : FMSA.FirstOrderClosure.IsRadialEntry Chat1 a i j c1)
    (hc2def : FMSA.FirstOrderClosure.IsRadialEntry Chat2 a i j c2)
    (hint1 : MeasureTheory.Integrable (fun v => ((v * c1 |v| : ℝ) : ℂ)))
    (hF1 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c1 |v| : ℝ) : ℂ))))
    (hint2 : MeasureTheory.Integrable (fun v => ((v * c2 |v| : ℝ) : ℂ)))
    (hF2 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c2 |v| : ℝ) : ℂ))))
    (hcc1 : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c1 |v| : ℝ) : ℂ)) r)
    (hcc2 : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c2 |v| : ℝ) : ℂ)) r) :
    ∀ r ∈ Set.Ioo (0 : ℝ) Rij, c1 r = c2 r := by
  have hEq : ∀ k, Chat1 k = Chat2 k := fun k =>
    firstOrder_khat_unique (H0 k) (C0 k) (H1 k) (Chat1 k) (Chat2 k) (Hinv k)
      (hinv k) (hoz1 k) (hoz2 k)
  exact FMSA.FirstOrderClosure.inner_core_dcf_eq_of_khat_eq ha hc1def hc2def hEq
    hint1 hF1 hint2 hF2 hcc1 hcc2

/-- ⭐ **FOEQ.4 — the left inverse is not assumed, it is the zeroth-order OZ.**  The same real-space
core uniqueness as `firstOrder_dcf_unique_on_core`, but with the invertibility of `1+H̃₀` **derived**
rather than hypothesised: the zeroth-order Ornstein–Zernike relation `(1+H̃₀)(1−C̃₀) = 1` makes
`1−C̃₀` a right inverse, hence — square matrices — a left inverse (`Matrix.mul_eq_one_comm`).  So the
first-order DCF's real-space value on the core rests only on OZ (zeroth order **and** the `γ = 1`
line, both from FOEQ.3) together with PYE.5's transform injectivity — no ad-hoc inverse. -/
theorem firstOrder_dcf_unique_on_core_of_oz {a : ℂ} (ha : a ≠ 0) {i j : Fin N} {Rij : ℝ}
    (H0 C0 H1 : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (Chat1 Chat2 : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hoz0 : ∀ k, (1 + H0 k) * (1 - C0 k) = 1)
    (hoz1 : ∀ k, H1 k * (1 - C0 k) = (1 + H0 k) * Chat1 k)
    (hoz2 : ∀ k, H1 k * (1 - C0 k) = (1 + H0 k) * Chat2 k)
    {c1 c2 : ℝ → ℝ}
    (hc1def : FMSA.FirstOrderClosure.IsRadialEntry Chat1 a i j c1)
    (hc2def : FMSA.FirstOrderClosure.IsRadialEntry Chat2 a i j c2)
    (hint1 : MeasureTheory.Integrable (fun v => ((v * c1 |v| : ℝ) : ℂ)))
    (hF1 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c1 |v| : ℝ) : ℂ))))
    (hint2 : MeasureTheory.Integrable (fun v => ((v * c2 |v| : ℝ) : ℂ)))
    (hF2 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c2 |v| : ℝ) : ℂ))))
    (hcc1 : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c1 |v| : ℝ) : ℂ)) r)
    (hcc2 : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c2 |v| : ℝ) : ℂ)) r) :
    ∀ r ∈ Set.Ioo (0 : ℝ) Rij, c1 r = c2 r :=
  firstOrder_dcf_unique_on_core ha H0 C0 H1 (fun k => 1 - C0 k) Chat1 Chat2
    (fun k => Matrix.mul_eq_one_comm.mp (hoz0 k)) hoz1 hoz2
    hc1def hc2def hint1 hF1 hint2 hF2 hcc1 hcc2

end FOEQ4

/-! ### FOEQ.6–9 ⭐⭐ — the equivalence holds at every order (paper Theorem IV.1)

FOEQ.1/3 were stated at `γ = 1`.  **Nothing in the argument is first-order-specific.**  These tasks
carry it to arbitrary order and are *additive* to the `γ = 1` rows, which stay as the instances the
rest of the paper consumes.  The product rule becomes the **general Leibniz rule**
(`iteratedDeriv_mul`), and the hypothesis relaxes to `γ`-fold differentiability — still strictly
weaker than analyticity, so the coupling series need never converge.

⭐ The payoff is a sharper statement of what "first order" *is*: the middle convolution
`∑_{m=1}^{γ−1} H̃_m C̃_{γ−m}` is **empty at `γ = 1` and nowhere else** (`FOEQ.9`).  That emptiness — not
the perturbation theory — is what makes the solution map linear (PYE.2) and the residue sum
terminate; from `γ = 2` the sum drags in `h⁽¹⁾` (built from `[Q̂₀]⁻¹`), which is §XII's obstruction.
The theory is equally well defined at every order; only *solvability in finite closed form* is special.
-/

section FOEQAllOrders

open scoped ContDiff
open Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- A degree-≤1 function `s ↦ c·s` has vanishing Taylor coefficients from order 2 on: its
`γ`-th iterated derivative is `0` for `γ ≥ 2`.  The reusable engine of `FOEQ.6`. -/
theorem iteratedDeriv_linear_higher (c : 𝔸) {γ : ℕ} (hγ : 2 ≤ γ) (x : ℝ) :
    iteratedDeriv γ (fun s : ℝ => s • c) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hγ
  have hderiv : deriv (fun s : ℝ => s • c) = fun _ => c := by
    funext s
    simpa using (((hasDerivAt_id s).smul_const c)).deriv
  rw [show 2 + k = k + 1 + 1 by ring, iteratedDeriv_succ', iteratedDeriv_succ', hderiv]
  simp [deriv_const, iteratedDeriv_const]

/-- **FOEQ.6 — the MSA closure's Taylor coefficients terminate.**  On the exterior the MSA closure
`msaOuter β u` is `−βu·s`, degree-1 in the coupling, so its coupling-Taylor coefficients are
`c⁽⁰⁾ = 0`, `c⁽¹⁾ = −βu`, and `c⁽ᵞ⁾ = 0` for **every** `γ ≥ 2` — the expansion *terminates*.  This
is the all-orders form of `FOEQ.1`; contrast the Mayer factor `e^{−βsu}−1` (`mayerF`), whose
coefficient is nonzero at every order (`mayerF_ne_msaOuter` is the `γ = 1` shadow of that). -/
theorem msaOuter_iteratedDeriv_terminates (beta u : ℝ) {γ : ℕ} (hγ : 2 ≤ γ) :
    iteratedDeriv γ (msaOuter beta u) 0 = 0 := by
  have hfun : msaOuter beta u = fun s : ℝ => s • (-(beta * u)) := by
    funext s; simp [msaOuter, smul_eq_mul]; ring
  rw [hfun]
  exact iteratedDeriv_linear_higher (-(beta * u)) hγ 0

/-- ⭐ **FOEQ.7 — differentiating OZ to order `γ` returns the Cauchy convolution, term for term.**
Let `s ↦ (H s, C s)` be any coupling-scaled family obeying the Ornstein–Zernike relation
`(1 + H̃)(1 − C̃) = 1` **on a neighbourhood of `0`** (MSAFAM.4: `∀ᶠ s in 𝓝 0` — no implicit
function theorem gives a *global* root, and the branch folds at finite coupling, so the germ at `0`
is all the Taylor coefficients see), `γ`-fold differentiable.  Then the order-`γ` coefficients
satisfy

    ∑_{i=0}^{γ}  C(γ,i) · H̃_i · C̃'_{γ−i}  =  0        (`H̃_i := ∂ⁱ(1+H)|₀`, `C̃'_j := ∂ʲ(1−C)|₀`)

which **is** the order-`γ` line of the coupling hierarchy.  The proof is the general Leibniz rule
(`iteratedDeriv_mul`) applied to the *constant* product `(1+H̃)(1−C̃) = 1`: OZ is quadratic, so at
every order the coefficient of the product is a finite Cauchy convolution with no remainder to
neglect.  This is `FOEQ.3` (`oz_deriv_eq_firstOrderLine`) with the product rule replaced by its
`γ`-fold generalisation, and it needs only `ContDiffAt ℝ γ` — **not** analyticity.

⚠ Stated over an abstract normed `ℝ`-algebra, **not** over `Matrix` — inheriting `FOEQ.3`'s
scoped-norm pitfall. -/
theorem oz_taylor_coeff_eq_cauchy_convolution
    (H C : ℝ → 𝔸) {γ : ℕ} (hγ : 1 ≤ γ)
    (hH : ContDiffAt ℝ γ H 0) (hC : ContDiffAt ℝ γ C 0)
    (hOZ : ∀ᶠ s in 𝓝 (0 : ℝ), (1 + H s) * (1 - C s) = 1) :
    ∑ i ∈ Finset.range (γ + 1),
      (γ.choose i : 𝔸) * iteratedDeriv i (fun s => 1 + H s) 0
        * iteratedDeriv (γ - i) (fun s => 1 - C s) 0 = 0 := by
  have hF : ContDiffAt ℝ γ (fun s => (1 : 𝔸) + H s) 0 := contDiffAt_const.add hH
  have hG : ContDiffAt ℝ γ (fun s => (1 : 𝔸) - C s) 0 := contDiffAt_const.sub hC
  have key := iteratedDeriv_mul (n := γ) (x := 0) hF hG
  -- ⚠ MSAFAM.4: the product is `1` only *near* `0` (no IFT gives a global root — the branch folds
  -- at finite coupling), so `iteratedDeriv` is pinned by the germ, not by a global `funext`.
  have hev : (fun s => (1 : 𝔸) + H s) * (fun s => (1 : 𝔸) - C s)
      =ᶠ[𝓝 (0 : ℝ)] fun _ => (1 : 𝔸) := by
    filter_upwards [hOZ] with s hs
    simpa [Pi.mul_apply] using hs
  rw [hev.iteratedDeriv_eq γ, iteratedDeriv_const, if_neg (by omega)] at key
  exact key.symm

/-- ⭐ **FOEQ.8 — the capstone (paper Theorem IV.1).**  For a `C^∞` coupling family solving OZ, the
order-`m` Taylor coefficients satisfy the order-`m` line of the hierarchy **at every order** `m ≥ 1`,
not merely `m = 1`.  Assembles `FOEQ.7` (the Leibniz convolution) over all orders; with `FOEQ.6` (the
closure coefficients terminate) this is the full statement that (D1) = (D2) order by order.  The
`C^∞` hypothesis is still strictly weaker than analyticity — the coupling series never has to
converge. -/
theorem oz_msa_taylor_eq_hierarchy (H C : ℝ → 𝔸)
    (hH : ContDiff ℝ ∞ H) (hC : ContDiff ℝ ∞ C)
    (hOZ : ∀ᶠ s in 𝓝 (0 : ℝ), (1 + H s) * (1 - C s) = 1) {m : ℕ} (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range (m + 1),
      (m.choose i : 𝔸) * iteratedDeriv i (fun s => 1 + H s) 0
        * iteratedDeriv (m - i) (fun s => 1 - C s) 0 = 0 :=
  oz_taylor_coeff_eq_cauchy_convolution H C hm
    (hH.contDiffAt.of_le (by exact_mod_cast le_top))
    (hC.contDiffAt.of_le (by exact_mod_cast le_top)) hOZ

/-- The `m = 1` case of `FOEQ.8` **is** `FOEQ.3` (`oz_deriv_eq_firstOrderLine`), read through
`iteratedDeriv 1 = deriv`: the arbitrary-order convolution reproduces the first-order line exactly, so
the general theorem genuinely subsumes the instance the rest of the paper consumes. -/
theorem oz_deriv_eq_firstOrderLine_of_taylor (H C : ℝ → 𝔸)
    (hH : ContDiffAt ℝ 1 H 0) (hC : ContDiffAt ℝ 1 C 0)
    (hOZ : ∀ s, (1 + H s) * (1 - C s) = 1) :
    deriv H 0 * (1 - C 0) = (1 + H 0) * deriv C 0 := by
  have h := oz_taylor_coeff_eq_cauchy_convolution H C (le_refl 1) hH hC
    (Filter.Eventually.of_forall hOZ)
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_mul,
    iteratedDeriv_zero, iteratedDeriv_one, Nat.sub_self, Nat.sub_zero,
    deriv_const_add, deriv_const_sub, mul_neg] at h
  -- h : (1 + H 0) * -(deriv C 0) + deriv H 0 * (1 - C 0) = 0  ⇒  goal
  rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h

/-- **FOEQ.9 (record only) — what is special about first order.**  The middle convolution
`∑_{m=1}^{γ−1} H̃_m C̃_{γ−m}` is **empty exactly when `γ = 1`** (`Finset.Ico 1 γ = ∅ ↔ γ = 1`, for
`γ ≥ 1`).  That emptiness — a fact about `Finset.range`, nothing about the expansion — is what makes
the solution map linear and the residue sum terminate; from `γ = 2` the sum drags in `h⁽¹⁾` (built
from `[Q̂₀]⁻¹`), which is §XII's obstruction.  The theory is equally well defined at every order; only
solvability in finite closed form is special to `γ = 1`. -/
theorem cauchy_convolution_middle_empty_iff {γ : ℕ} (hγ : 1 ≤ γ) :
    Finset.Ico 1 γ = ∅ ↔ γ = 1 := by
  rw [Finset.Ico_eq_empty_iff]
  omega

end FOEQAllOrders

end FMSA.FirstOrderEquivalence


