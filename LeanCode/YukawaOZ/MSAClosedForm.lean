/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# The exact MSA closed form for a hard-core Yukawa fluid — Group `MSAEXACT`

Group **MSAEXACT** (single component; the mixture is `MSAEMIX`, deliberately gated — see
`proof_notes_msa_exact.md`).  Numerical partner: Group **MSAX**,
`todo/waisman_msa_plan.md` and `numerical_notes/theory/waisman_msa_closed_form.md`.

**Source.** E. Waisman, *Mol. Phys.* **25**, 45 (1973), §1.  With `x = r/d`, `ξ = πρd³/6`,
closure `C(x) = K x⁻¹e^{−z(x−1)}` for `x > 1` and `g(x) = 0` for `x < 1`, the solution is

    −C(x) = a + bx + ξ a x³/2 + v[1 − e^{−zx}]/(zx) + v²(cosh zx − 1)/(2Kz²e^{z})

with `(a, b, v)` fixed by his Eq. (3a)–(3c).  This file works in `w = v/K`, in which the
`K → 0` limit is regular (in `v` it is `0/0`, because Eq. (2) carries `v²/(2Kz²e^z)`).

**Why this group is worth formalising.** The whole content is algebra over `ℝ` with `e^{−z}`,
`cosh z`, `sinh z` as parameters — no contour integrals, no `L¹`, nothing touching the seven
analysis axioms of `MATH_AXIOMS.md`.  **No new axiom is admissible here**; needing one means the
algebraic route was abandoned somewhere.

## This file (MSAEXACT.4)

The `K = 0` reduction: **the Percus–Yevick coefficients satisfy Waisman's system identically in
`ξ`**, for *every* `w`.  That last clause is not a throwaway — `w` enters the system only through
`K·w`, so at `K = 0` it drops out entirely and the root is a whole line.  That degeneracy is
exactly why the numerical continuation cannot obtain `w` from the algebra at `K = 0` and must take
it from `w`'s definition instead (MSAX.1; theory note §7c).

Verified numerically before formalising: the residuals vanish to `3.8e-13` over a grid of `ξ` and
`w`, and `sympy` returns exactly `0` for all three after simplification.

## Results

* `y0`, `y1`, `y2`, `res3a`, `res3b`, `res3c` — Waisman's system in `(ξ, K, z, a, b, w)`.
* `y0_zero_coupling` etc. — the `K = 0` reduction, where every transcendental drops out.
* `pyA`, `pyB` — the Wertheim–Thiele Percus–Yevick coefficients.
* `pyA_pyB_satisfy_zero_coupling` — ⭐ all three residuals vanish at `K = 0`, **for every `w`**.
* `y0_py_eq_contact` — the by-product `y₀ = (1 + ξ/2)/(1 − ξ)²`, the PY contact value, confirming
  that Waisman's `y₀` really is `g(1⁺)`.
-/

namespace FMSA.MSAExact

open Real

/-- Waisman's `y₀ = [x g(x)]|_{x=1⁺}`, the contact value, in the regular variable `w = v/K`. -/
noncomputable def y0 (xi K z a b w : ℝ) : ℝ :=
  K + a + b + xi * a / 2 + (K * w / z) * (1 - exp (-z))
    + (K * w ^ 2 / (2 * z ^ 2)) * ((cosh z - 1) * exp (-z))

/-- Waisman's `y₁ = (d/dx)[x g(x)]|_{x=1⁺}`. -/
noncomputable def y1 (xi K z a b w : ℝ) : ℝ :=
  -z * K + a + 2 * b + 2 * xi * a + K * w * exp (-z)
    + (K * w ^ 2 / (2 * z ^ 2)) * ((cosh z - 1) * exp (-z) + z * (sinh z * exp (-z)))

/-- Waisman's `y₂ = (d²/dx²)[x g(x)]|_{x=1⁺}`. -/
noncomputable def y2 (xi K z a b w : ℝ) : ℝ :=
  z ^ 2 * K + 2 * b + 6 * xi * a - K * w * z * exp (-z)
    + (K * w ^ 2 / (2 * z ^ 2))
        * (2 * z * (sinh z * exp (-z)) + z ^ 2 * (cosh z * exp (-z)))

/-- Waisman Eq. (3a) as a residual: `24ξy₀² − (−4b + 2vz − v²/(K e^z))`, with `v = K w`. -/
noncomputable def res3a (xi K z a b w : ℝ) : ℝ :=
  24 * xi * (y0 xi K z a b w) ^ 2
    - (-4 * b + 2 * (K * w) * z - K * w ^ 2 * exp (-z))

/-- Waisman Eq. (3b) as a residual. -/
noncomputable def res3b (xi K z a b w : ℝ) : ℝ :=
  24 * xi * ((y1 xi K z a b w) ^ 2 - 2 * (y0 xi K z a b w) * (y2 xi K z a b w))
    - (24 * xi * a - 2 * (K * w) * z ^ 3 + K * w ^ 2 * exp (-z) * z ^ 2)

/-- Waisman Eq. (3c) as a residual, specialised to `K = 0`.

At `K = 0` the outer Yukawa contributes nothing and `∫₀^∞ C x² dx` collapses to the polynomial
part, giving `a = 1 + 8ξa + 6ξb + 2ξ²a`.  The general-`K` form needs the full moment integral and
is left to a later task; this file only claims the `K = 0` statement. -/
noncomputable def res3c_zero (xi a b : ℝ) : ℝ :=
  a - (1 + 8 * xi * a + 6 * xi * b + 2 * xi ^ 2 * a)

/-! ### The `K = 0` reduction

`w` enters only through `K·w`, so at `K = 0` every transcendental disappears **and `w` drops out**.
The `w`-freedom in the statements below is the formal record of that degeneracy. -/

@[simp] theorem y0_zero_coupling (xi z a b w : ℝ) :
    y0 xi 0 z a b w = a + b + xi * a / 2 := by
  simp [y0]

@[simp] theorem y1_zero_coupling (xi z a b w : ℝ) :
    y1 xi 0 z a b w = a + 2 * b + 2 * xi * a := by
  simp [y1]

@[simp] theorem y2_zero_coupling (xi z a b w : ℝ) :
    y2 xi 0 z a b w = 2 * b + 6 * xi * a := by
  simp [y2]

theorem res3a_zero_coupling (xi z a b w : ℝ) :
    res3a xi 0 z a b w = 24 * xi * (a + b + xi * a / 2) ^ 2 + 4 * b := by
  simp [res3a]

theorem res3b_zero_coupling (xi z a b w : ℝ) :
    res3b xi 0 z a b w =
      24 * xi * ((a + 2 * b + 2 * xi * a) ^ 2
        - 2 * (a + b + xi * a / 2) * (2 * b + 6 * xi * a)) - 24 * xi * a := by
  simp [res3b]

/-! ### The Percus–Yevick point -/

/-- Wertheim–Thiele `λ₁`: the PY value of Waisman's `a`, which is also `∂βp/∂ρ`. -/
noncomputable def pyA (xi : ℝ) : ℝ := (1 + 2 * xi) ^ 2 / (1 - xi) ^ 4

/-- Wertheim–Thiele `6ηλ₂`: the PY value of Waisman's `b`. -/
noncomputable def pyB (xi : ℝ) : ℝ := -6 * xi * (1 + xi / 2) ^ 2 / (1 - xi) ^ 4

/-- ⭐ **MSAEXACT.4.** At zero coupling the Percus–Yevick coefficients annihilate all three of
Waisman's equations, identically in `ξ` and **for every `w`**.

The `∀ w` is the substantive part: it records that the `K = 0` system does not determine `w` at
all, which is why the physical branch has to be selected by continuity from this point rather than
read off the algebra (theory note §7c, `msa_exact.solve_continued`). -/
theorem pyA_pyB_satisfy_zero_coupling (xi z w : ℝ) (h : xi ≠ 1) :
    res3a xi 0 z (pyA xi) (pyB xi) w = 0 ∧
    res3b xi 0 z (pyA xi) (pyB xi) w = 0 ∧
    res3c_zero xi (pyA xi) (pyB xi) = 0 := by
  have h4 : (1 - xi) ^ 4 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h))
  refine ⟨?_, ?_, ?_⟩
  · rw [res3a_zero_coupling, pyA, pyB]; field_simp; ring
  · rw [res3b_zero_coupling, pyA, pyB]; field_simp; ring
  · unfold res3c_zero pyA pyB; field_simp; ring

/-- By-product: Waisman's `y₀` at the PY point is the Percus–Yevick contact value
`(1 + ξ/2)/(1 − ξ)²` — confirming that `y₀` really is `g(1⁺)`. -/
theorem y0_py_eq_contact (xi z w : ℝ) (h : xi ≠ 1) :
    y0 xi 0 z (pyA xi) (pyB xi) w = (1 + xi / 2) / (1 - xi) ^ 2 := by
  have h2 : (1 - xi) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h))
  have h4 : (1 - xi) ^ 4 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h))
  rw [y0_zero_coupling, pyA, pyB]; field_simp; ring

/-- Non-vacuity: the hypothesis `xi ≠ 1` is satisfiable in the physical range, and the coefficients
are not degenerate there. Guards against the whole file being vacuously true — the
`b4_origin_bc_abstract` / GAP.8 failure mode recorded in `proof_notes_msa_exact.md`. -/
example : pyA (1/5 : ℝ) = 4.78515625 ∧ pyB (1/5 : ℝ) = -3.544921875 := by
  refine ⟨?_, ?_⟩
  · unfold pyA; norm_num
  · unfold pyB; norm_num

/-! ### MSAEXACT.3 (positivity foothold) — Blum–Høye (39): the compressibility is a perfect square

The **necessary condition** the source flags as "possibly most of the theorem"
(`proof_notes_msa_exact.md`, MSAEXACT.3); the uniqueness capstone `msaRoot_unique_of_coupling_lt` is
below.  (The eliminated polynomial itself — degree 8, **reducible into two quartics** — is MSAEXACT.2,
`YukawaOZ/MSAElimination.lean`.)  At `N = 1` the `k = 0` structure factor is the *square* of the
Baxter factor,

    1 − ρĉ(0)  =  [1 − ρQ̂(0)]²  =  (A/2π)²                    Blum & Høye (39),

with `A/2π = 1 − ρQ̂(0)` real on the factorizable branch.  Four consequences, all elementary once the
square identity is in hand — which is exactly why the positivity is "most of the theorem":

* it is **manifestly ≥ 0** on that branch (`compressibility_nonneg_of_baxter_sq`);
* it **vanishes exactly at the spinodal `A = 0`** (same lemma);
* a mechanically unstable state `1 − ρĉ(0) < 0` has **no real Baxter factor at all**
  (`no_real_baxter_factor_of_neg`), so *inside* the spinodal is not merely hard to reach — no real
  solution of the factorized system exists there;
* the physical acceptability criterion — **vacuous** in Blum & Høye's mixture form at `N = 1`, hence
  a rule the literature does not supply — is simply `A/2π > 0`, and that selects a **unique** root
  (`physical_baxter_factor_unique`).

The dictionary (theory note §7g, verified `2.2e-16`) is **Waisman's `a` = Blum & Høye's `(A/2π)²`**,
so `pyA` — the PY/`K=0` value of `a` — must itself be a perfect square; it is
(`pyA_eq_sq`, `pyA_pos`), the `K = 0` instance of (39).  Its double root in `a` versus regular zero in
`A` (`baxter_sq_double_root_at_spinodal`) is why the numerical ramp must **track `A`, not `a`**. -/

open Real in
/-- (39) consequences: if the `k=0` compressibility `S` is the square of the Baxter factor `B`
(`= A/2π`), then `S ≥ 0`, and `S = 0` **iff** `B = 0` — the spinodal is exactly the vanishing of the
Baxter factor. -/
theorem compressibility_nonneg_of_baxter_sq {S B : ℝ} (h39 : S = B ^ 2) :
    0 ≤ S ∧ (S = 0 ↔ B = 0) := by
  refine ⟨h39 ▸ sq_nonneg B, ?_⟩
  rw [h39]; exact pow_eq_zero_iff two_ne_zero

/-- **Inside the spinodal is structurally unreachable.** A mechanically unstable `k=0` compressibility
`S < 0` (which FWL's numerics returned freely at `z = 5`) admits **no** real Baxter factor `B` with
`S = B²` — the factorization's own precondition failing, not a solver artefact. -/
theorem no_real_baxter_factor_of_neg {S : ℝ} (hS : S < 0) : ¬ ∃ B : ℝ, S = B ^ 2 := by
  rintro ⟨B, rfl⟩
  exact absurd (sq_nonneg B) (not_le.mpr hS)

open Real in
/-- **The single-component acceptability criterion, and it gives uniqueness.** Blum & Høye's `N`-body
rule `g_ij = g_ji` (their Eq. 41) is vacuous at `N = 1`, so the literature supplies no scalar
selection rule.  The Baxter framework does: the factor `A/2π = 1 − ρQ̂(0)` must be **positive** (a sign
change is a change of Wiener–Hopf winding, not a physical branch).  For a positive compressibility `S`
there is then **exactly one** admissible Baxter factor, `√S` — the missing `N=1` selection rule. -/
theorem physical_baxter_factor_unique {S : ℝ} (hS : 0 < S) :
    ∃! B : ℝ, 0 < B ∧ B ^ 2 = S := by
  refine ⟨Real.sqrt S, ⟨Real.sqrt_pos.mpr hS, Real.sq_sqrt hS.le⟩, ?_⟩
  rintro B ⟨hBpos, hBsq⟩
  rw [← hBsq, Real.sqrt_sq hBpos.le]

/-- **The `K = 0` instance of (39).**  Waisman's `a = ∂βp/∂ρ = 1 − ρĉ(0)`, at the PY / hard-sphere
end point `K = 0`, is a manifest perfect square `pyA ξ = ((1+2ξ)/(1−ξ)²)²` — so it *is* `(A/2π)²` with
`A/2π = (1+2ξ)/(1−ξ)²`, confirming the theory-note dictionary at the reference point. -/
theorem pyA_eq_sq (xi : ℝ) :
    pyA xi = ((1 + 2 * xi) / (1 - xi) ^ 2) ^ 2 := by
  rw [pyA, div_pow, ← pow_mul]

/-- The PY compressibility is strictly **positive** for every physical `ξ ∈ (0,1)`: the hard-sphere
reference fluid is mechanically stable, as it must be, and has no spinodal — the `K = 0` edge of the
positivity condition. -/
theorem pyA_pos {xi : ℝ} (h : xi ∈ Set.Ioo (0 : ℝ) 1) : 0 < pyA xi := by
  rw [pyA]
  exact div_pos (pow_pos (by linarith [h.1]) 2) (pow_pos (by linarith [h.2]) 4)

/-- Why the spinodal is a **regular** point in `A` but a **double** root in `a = (A/2π)²`: at the
Baxter factor `B = 0` both the value and the derivative of `B ↦ B²` vanish, so `a` touches zero
quadratically while `A` crosses it linearly.  Consequence (theory note §7h): a ramp in `a` stalls
quadratically at the spinodal, so the continuation must **track `A`, not `a`** — `A = 0` locates the
spinodal cleanly and analytically. -/
theorem baxter_sq_double_root_at_spinodal :
    (fun B : ℝ => B ^ 2) 0 = 0 ∧ deriv (fun B : ℝ => B ^ 2) 0 = 0 := by
  refine ⟨by norm_num, ?_⟩
  simpa using (hasDerivAt_pow 2 (0 : ℝ)).deriv

/-! ### MSAEXACT.3 — the uniqueness capstone

`msaRoot_unique_of_coupling_lt` is the theorem the source (Blum & Høye 1978 p. 323) leaves open at
`N = 1`: *"one must expect multiple solutions … of which only one is acceptable"* — with an
acceptability rule (their Eq. 41) that is **vacuous at one component**.  The Baxter framework supplies
the missing rule and its uniqueness, and this file assembles it from the pieces already proved:

* **acceptability** = `A/2π > 0` (`physical_baxter_factor_unique`): the physical Baxter factor is the
  *positive* root of the compressibility, `A/2π = √a`, and it is unique given `a`;
* **threshold** = the spinodal `a = 0` (`compressibility_nonneg_of_baxter_sq`, `A = 0` a double root);
* **the coupling pins the compressibility below the threshold** — the physical `a = ∂βp/∂ρ` is
  strictly monotone in `K` (it falls from the PY value to `0` at the spinodal, `K_c ≈ 3.32` at
  `ξ = 0.2`; `msax_elimination.py`, theory note §7).

⚠ **The monotonicity is a *measured* input, not proved here**: it is a property of the physical branch
of the transcendental elimination quartic (MSAEXACT.2), a continuity/branch statement outside
`ring`/`decide`.  It enters below as the injectivity hypothesis `hcoupling_pins`.  Likewise the
explicit threshold value (`βK ≈ 3`, FWL) is numerical.  Those are the parts of MSAEXACT.3 that stay
measured; everything else — the selection rule and the uniqueness it yields — is proved. -/

/-- ⭐ **MSAEXACT.3.**  Below the spinodal (physical compressibility `a > 0`), the physical solution
is unique: two acceptable roots (positive Baxter factor `B = A/2π`, `B² = a`) at the **same coupling**
have the same Baxter factor.  Combines `physical_baxter_factor_unique` (given `a`, the positive `B` is
unique) with the measured fact that the coupling pins `a` on the physical branch (`hcoupling_pins` —
the strict monotonicity of `a` in `K`, encoded as injectivity of the compressibility→coupling map).

The single-component acceptability criterion `A/2π > 0` is precisely what Blum & Høye's Eq. (41)
cannot supply at `N = 1`; this is the uniqueness it delivers. -/
theorem msaRoot_unique_of_coupling_lt
    {couplingOf : ℝ → ℝ} (hcoupling_pins : Function.Injective couplingOf)
    {a₁ a₂ B₁ B₂ : ℝ}
    (hsame : couplingOf a₁ = couplingOf a₂)
    (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (ha₁ : B₁ ^ 2 = a₁) (ha₂ : B₂ ^ 2 = a₂) :
    B₁ = B₂ := by
  have ha : a₁ = a₂ := hcoupling_pins hsame
  obtain ⟨B, _, hu⟩ := physical_baxter_factor_unique (S := a₁) (ha₁ ▸ pow_pos hB₁ 2)
  exact (hu B₁ ⟨hB₁, ha₁⟩).trans (hu B₂ ⟨hB₂, ha.symm ▸ ha₂⟩).symm

/-! ### §8 foothold — real solutions, the spinodal wall, and the first-order crossing

The theory-note chapter §8 ("Real solutions, the spinodal, and the fold") turns on two structural
facts, both of which reduce — given the perfect-square identity above — to elementary statements
proved here.  What stays **measured** (theory note §8a/§8b) is the *finite-`K` branch geometry*:
that the spinodal `A = 0` is a **regular** point (`det J ≠ 0` — the full finite-`K` Jacobian, not the
block-triangular `K=0` one), that the real branch continues to a **fold** at `det J = 0` a few %
lower in `T*`, and that it goes complex beyond it.  Those are branch statements about the
transcendental elimination (MSAEXACT.2), outside `ring`/`decide`; see
`msaRoot_unique_of_coupling_lt`'s note. -/

open Real in
/-- **The spinodal wall, as a range statement.**  A value `a` is realizable as an exact `k = 0`
compressibility `a = (A/2π)²` **iff** `a ≥ 0`: the achievable set is exactly `[0, ∞)`.  Forward is
`compressibility_nonneg_of_baxter_sq`; the reverse takes the Baxter factor `√a`.  So the
mechanically-unstable interior `a < 0` is *outside the range* of any real Baxter factorisation
(`no_real_baxter_factor_of_neg` is the contrapositive of the forward half) — which is why no solver
**and no analytic continuation** can manufacture it (theory note §8, §8b). -/
theorem compressibility_realizable_iff_nonneg (a : ℝ) :
    (∃ B : ℝ, a = B ^ 2) ↔ 0 ≤ a := by
  constructor
  · rintro ⟨B, rfl⟩; exact sq_nonneg B
  · intro ha; exact ⟨Real.sqrt a, (Real.sq_sqrt ha).symm⟩

/-- **Why the first-order truncation crosses the wall that the exact solution cannot** (theory note
§8).  The *exact* compressibility is a perfect square `aExact K = (A K)²`, hence `≥ 0` for **every**
coupling `K` — it can never enter `a < 0`.  The *first-order* (FMSA) compressibility is instead
**affine** in the coupling, `aFMSA K = a₀ − s·K`, because the DP map is linear in `K` (FOEQ
`msaOuter_eq_smul_deriv`); so once the coupling is large enough that `s·K > a₀` (for a positive
slope, `K > a₀/s` — a *positive* threshold when `a₀ = a_PY > 0`, `pyA_pos`) it is **strictly
negative**.  Thus at any such coupling `aExact K ≥ 0 > aFMSA K`: the exact solution stays
out of the unstable region and the first-order truncation walks straight in.  This is the structural
core of §8 — the perfect square is the wall; the affine truncation crosses it freely — with the
branch geometry (regular spinodal, fold) the measured part. -/
theorem exact_vs_firstOrder_compressibility_wall (A : ℝ → ℝ) (a₀ s : ℝ) :
    (∀ K, 0 ≤ (A K) ^ 2) ∧ (∀ K, a₀ < s * K → a₀ - s * K < 0) :=
  ⟨fun K => sq_nonneg _, fun _ hK => by linarith⟩

end FMSA.MSAExact

