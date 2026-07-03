# Proof Notes: Free Energy Integrals

Detailed proof records for Group F — closed-form free energy integrals
and contact-value approximation error.
See `todo_lean.md` for task status summary.

## Group F — Free Energy Integrals  *(energy and thermodynamic consistency)*

These tasks check whether the first-order Helmholtz free energy from FMSA is
analytically computable and consistent across FMSA_poly and FMSA_GA_matrix_mix.

### Task F.1 — Outer-core free energy integral (closed form)

**Statement:** For the Yukawa outer-core `c^(1)(r) = K · exp(−z·(r−d)) / r` for r > d:
```
4π ∫_d^∞ c^(1)(r) · r² dr  =  4π · K · (d/z + 1/z²)
```
Derivation: `∫_d^∞ K · exp(−z(r−d)) · r dr = K·exp(z·d) · ∫_d^∞ r·exp(−z·r) dr`
`= K · (d/z + 1/z²)` by standard Laplace integral.

**Lean:** Show `∫ r in d..+∞, K * Real.exp (-z * (r - d)) * r = K * (d / z + 1 / z^2)`
using `MeasureTheory.integral_mul_right` and the standard Laplace integral lemmas.

**Status:** ✓ complete — `LeanCode/FreeEnergy/OuterIntegral.lean`
  (`outer_core_integral`, `outer_core_free_energy`; complete)

  Key lemmas proved:
  - `hasDerivAt_exp_neg_mul_sub` — `HasDerivAt` for `x ↦ exp(−z·(x−d))` via chain rule
  - `outer_antideriv_hasDerivAt` — antiderivative `G(r) = −exp(−z(r−d))·(r/z+1/z²)` via product rule + `congr_deriv`
  - `outer_antideriv_tendsto_zero` — `G(r) → 0` via `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`
  - `outer_integrable` — integrability on `Ioi d` by splitting at `c = max d 0 + 1`, using `integrableOn_Ioi_deriv_of_nonpos'` on the tail
  - `outer_core_integral` — FTC via `integral_Ioi_of_hasDerivAt_of_tendsto`

---

### Task F.2a — Inner-core energy integral for E_ij part (closed form)

**Context:** This is the inner-core free energy via the FMSA DCF, used in **FMSA_GA_matrix_mix** (exact
formula [chsY] Eq. 41). It is NOT what `betaf1_inner` in FMSA_poly computes — that uses the
LJ potential directly with a contact-value approximation (see Task F.2b). Keep both for comparison:
F.2a = exact DCF route (FMSA_GA_matrix_mix); F.2b = LJ contact-value route (FMSA_poly).

**Statement:** For the E_ij contribution to `c^(1)(r)` for r ∈ [0, R]:
```
∫_0^R E_ij(r) · r dr  =  Σ A_ij(z) · [R/z  −  1/z²  +  exp(−z·R)/z²]
```
This follows directly from `∫_0^R r·exp(z·(r−R)) dr = exp(−z·R) · I₁(R, R, z)` [Task 1.1].

**Why it matters:** Gives the exact inner-core free energy from the MSA DCF for FMSA_GA_matrix_mix,
as an alternative to the contact-value LJ approximation used in FMSA_poly.

**Status:** ✓ DONE — `eij_inner_integral` in `LeanCode/FreeEnergy/InnerIntegral.lean` (complete):
  1. `hrw`: rewrites `eij A z R r * r` via `Finset.sum_congr rfl` + `congr 1; congr 1; ring`
     (`-(z k)*(R-r) = z k*(r-R)`) to match `inner_core_eij_integral` integrand exactly
  2. `simp_rw [hrw]; exact inner_core_eij_integral A z R hz`
  Import added: `import LeanCode.FMSAPoly.EijStructure` in `InnerIntegral.lean`.

---

### Task F.2b — LJ inner-core integral identity (FMSA_poly contact-value free energy)

**Context:** `betaf1_inner` and `betaf2_lj` in FMSA_poly (FMSA_MC_cleaned_2cpp.py:1401, 1514)
approximate `∫_0^R g₀_YK(r) u_inner(r) r² dr` using the **contact-LJ approximation**:
(1) `g₀_YK(r) → g₀_YK(R_ij)` (contact-value), (2) LJ shape for inner-core potential over [σ, R].
The combined integral is evaluated analytically:

**Statement:** For σ, R > 0 with s = σ/R:
```
∫_σ^R [(σ/r)¹² − (σ/r)⁶] r² dr  =  R³ · (−s¹²/9 + s⁶/3 − 2s³/9)
```
The code's `LJ_term = R³·(s¹²/9 − s⁶/3 + 2s³/9) = −∫_σ^R [...]`.

**Derivation:** Antiderivative `F(r) = −σ¹²/(9r⁹) + σ⁶/(3r³)`:
- `F(R) = R³(−s¹²/9 + s⁶/3)`, `F(σ) = 2σ³/9 = R³(2s³/9)` (lower-limit term)
- `∫_σ^R = F(R) − F(σ) = R³(−s¹²/9 + s⁶/3 − 2s³/9)` ✓

**What Lean CANNOT verify:** contact-value `g₀_YK(r) ≈ g₀_YK(R_ij)` and LJ shape accuracy.

**Status:** ✓ complete — `LeanCode/FreeEnergy/LJIntegral.lean`
  (`lj_integral`, `lj_term_eq`, `lj_integrand_eq`; complete)

  Key lemmas proved:
  - `lj_antideriv_hasDerivAt` — `F(r) = (−σ¹²/9)·(r⁹)⁻¹ + (σ⁶/3)·(r³)⁻¹` via `hasDerivAt_pow` + `.inv` + `.const_mul` + `congr_deriv`
  - `lj_integrable` — integrability via `ContinuousOn.intervalIntegrable_of_Icc`
  - `lj_integral` — main identity via `integral_eq_sub_of_hasDerivAt` + `field_simp` + `ring`
  - `lj_integrand_eq` — `((σ/r)¹²−(σ/r)⁶)·r² = σ¹²/r¹⁰−σ⁶/r⁴` via `field_simp`
  - `lj_term_eq` — `LJ_term = −∫(...)` via `linarith`

---

### Task F.3a — Free energy convergence (FMSA_GA_matrix_mix DCF route)

**Statement:** The FMSA_GA_matrix_mix DCF integrand `c^(1)(r)·r²` is in `L¹(0, ∞)`:
- Inner [0, R]: E_ij + P_ij form is continuous on compact → integrable.
- Outer (R, ∞): `K·r·exp(−z(r−R))` decays exponentially → integrable.

**Status:** ✓ DONE — three theorems in `LeanCode/FreeEnergy/Convergence.lean` (complete):
  - `eij_single_R_continuous`: `Continuous (fun r => eij A z R r)` for fixed `R : ℝ`.
    Key: inner `R - r` uses `continuous_const.sub continuous_id` (not `id.sub const`).
  - `ga_matrix_mix_inner_integrable`: `IntegrableOn (eij·r) (Set.Icc 0 R)` via `inner_core_integrable`.
  - `ga_matrix_mix_route_convergence`: inner + outer (`outer_core_energy_integrable`) together.
  Import added: `import LeanCode.FMSAPoly.EijStructure` in `Convergence.lean`.

---

### Task F.3b — Free energy convergence (LJ/FMSA_poly route)

**Statement:** The FMSA_poly contact-LJ free energy integrand is in L¹:
- Inner `[σ, R]`: `(σ¹²/r¹⁰ − σ⁶/r⁴)` — continuous, compact, r ≥ σ > 0 → `IntervalIntegrable`.
- Outer `(R, ∞)`: `K·r·exp(−z(r−R))` — exponential decay for z > 0 → integrable.

The exact values follow from `lj_integral` (F.2b) and `outer_core_integral` (F.1) directly.

**Status:** ✓ complete — `LeanCode/FreeEnergy/Convergence.lean`
  (`lj_route_convergence`; complete)

  Key:
  - Inner piece: `lj_integrable hσ hσR` (from Task F.2b, exposed as non-private)
  - Outer piece: `outer_core_energy_integrable (d := R) hz` (from Task F.1, via `outer_integrable`)
  - Also proved: `outer_core_integrable` (proved), `outer_integrand_tendsto_zero` (proved)

---

### Task F.4 — Compressibility sum rule *(deleted)*

**Status: ✗ DELETED.**

**Why deleted:** The task as formulated mixed two different thermodynamic routes:
- **Energy route** (what FMSA computes): `β·f₁ ∝ ∫ u₁(r) g₀(r) r² dr` via G0red Laplace
- **Compressibility route** (what `Ĉ^(1)(0)` integrates): `4π ∫ r² c^(1)(r) dr`

For any first-order approximate theory (MSA, FMSA, PY) these two routes give different
numbers — the gap measures thermodynamic inconsistency of the approximation, not a model
defect. Verifying their agreement is therefore not a meaningful model check.

**Root cause of the sorry (documented for reference):** The Lean theorem attempted to equate
`b_{00}(0)/z = K(1+A)²/z` (Baxter/Laplace of h^(1), the pair correlation) with
`4π ∫ r² c^(1)(r) dr` (3D Fourier of the DCF). These are fundamentally different:

```
4π ∫ r² c^(1) dr  =  Ĉ^(1)(0)          [compressibility route]
b_{00}(0) / (2πρ)  =  ∫ r h^(1) dr      [Laplace at s=0 of h, r-weight]
```

Connected via OZ.4: `Ĉ^(1) = Ĥ^(1)/S₀²`, but `b_{00}` encodes `Ĥ^(1)`, not `Ĉ^(1)`.
The hypothesis `hParseval` was unsatisfiable for FMSA parameters (confirmed numerically:
η=0.3, z=1 gives FMSA (1+A)² ≈ 0.153 vs `hParseval` requiring ≈ 7.10).

**Lean artefact:** The `compressibility_sum_rule` sorry in `FreeEnergy/SumRule.lean` has
been left in place (it is unreachable dead code now that the task is deleted). It can be
removed in a future cleanup pass.

---

### Task F.5 — Contact-value approximation error via FMSA_GA_matrix_mix closed-form g(r)

**Motivation:** FMSA_GA_matrix_mix ([chsY] Eq. 41) provides `c^(1)(r)` in closed form for all r.
Via the linearised OZ equation (Task OZ.4), this yields `g^(1)(r)` analytically.
Combined with the PY reference `g₀_HS(r)` (Task OZ.3), the full first-order RDF
`g(r) = g₀_HS(r) + g^(1)(r)` is analytically known — enabling a formal Lean assessment
of whether the contact-value approximation `g(r) ≈ g(R)` is accurate.

**Statement (two forms):**

**(a) Error formula** (always provable):
```
∫_{σ}^{R} g(r) · u_LJ(r) · r² dr  −  g(R) · ∫_{σ}^{R} u_LJ(r) · r² dr
  =  ∫_{σ}^{R} (g(r) − g(R)) · u_LJ(r) · r² dr
```
where both integrals have closed forms given the analytical `g(r)` and Task F.2b.

**(b) Error bound** (goal: prove at specific physical parameters, e.g. η=0.3, z=2.96, σ=1):
```
|∫_{σ}^{R} (g(r) − g(R)) · u_LJ(r) · r² dr| ≤ ε
```
or conversely prove ε is large (approximation fails for large z or dense packing).

**Proof strategy:**
- `g₀_HS(r)` from Task OZ.3: sum of damped oscillations, bounded variation on [σ, R]
- `g^(1)(r)` from Task OZ.4: explicit exponential form from the chsY solution
- `∫ u_LJ · r² dr` from Task F.2b: closed form
- Bound `∫(g(r)−g(R))u_LJ r² dr` via `‖g′‖_{L∞} · (R−σ) · |∫ u_LJ r² dr|`
  (Lipschitz estimate; the Lipschitz constant of g comes from its explicit exponential form)

**Prerequisites (in dependency order):**
1. **Task OZ.1** — PY DCF closed form `c_HS(r)`
2. **Task OZ.2** — real-space `g₀_HS` via OZ fixed point  *(needs OZ.1)*
3. **Task OZ.3** — `Ĉ_HS(s)`, `S₀(s)`, `oz_laplace_identity`, `g0_HS_laplace_spec`  *(needs OZ.1)*
4. **Task OZ.4** — general linearised OZ identity `Ĥ^(1) = Ĉ^(1)·S₀`  *(needs OZ.3 only)*
4. **Task 4.4** — FMSA_GA_matrix_mix closed-form `c^(1)(r)` — needed only to get explicit `h^(1)(r)`
5. **Task F.2b** — LJ integral closed form  *(complete)*

**What Lean can prove:**
- The exact error formula (a) — always true, no approximation needed
- A Lipschitz bound on the error given the explicit g(r) form — provable with `nlinarith`
- For specific parameters: `norm_num` after substituting η, z, σ values

**What Lean still cannot prove:**
- That the combined contact-LJ approximation (contact-value g AND LJ potential shape)
  is accurate — the LJ shape substitution for `u_inner(r)` remains uncontrolled

**Difficulty:** High — longest dependency chain in Group F; requires completing OZ.1–OZ.4

**Status:** ✓ DONE (abstract + FMSA_GA_matrix_mix improvement) — `LeanCode/FreeEnergy/ContactError.lean` (complete):

- **`lj_u_integrable`**: `((σ/r)¹²−(σ/r)⁶)·r²` is `IntervalIntegrable` on `[σ,R]` for `0 < σ ≤ R`.
  Proof: rewrite integrand to power-law form via `lj_integrand_eq`, then use `lj_integrable`.

- **`f5_contact_error_formula`** (part a): pure linearity identity, any `g` and `u`:
  ```
  (∫_σ^R g(r)·u(r)·r² dr) − gR·(∫_σ^R u(r)·r² dr) = ∫_σ^R (g(r)−gR)·u(r)·r² dr
  ```
  Proof: `integral_congr` (ring rewrite inside integral) + `integral_sub` + `integral_const_mul`;
  `linear_combination -hcongr - hsub + hconst`.

- **`f5_lj_contact_error`**: specialises to LJ potential using `lj_integral` (Task F.2b):
  ```
  (∫_σ^R g(r)·((σ/r)¹²−(σ/r)⁶)·r² dr) − gR·R³·(−s¹²/9+s⁶/3−2s³/9) = ∫_σ^R (g−gR)·...
  ```

- **`f5_error_bound`** (part b): abstract Lipschitz bound for any `M`:
  ```
  (∀ r ∈ [σ,R], |g(r)−gR| ≤ M) → |∫_σ^R (g−gR)·u·r²| ≤ M · ∫_σ^R |u·r²| dr
  ```
  Proof: `norm_integral_le_integral_norm` + `integral_mono_on` + `integral_const_mul`.

**FMSA_GA_matrix_mix improvement (added):** Three new proved theorems in `section PathBImprovement`:

- **`eij_contact_variation_formula`**: exact formula `eij(R)−eij(r) = Σ Aₖ·(1−exp(−zₖ·(R−r)))`.
  Proof: `unfold eij; simp [sub_self, exp_zero, mul_one]; ← Finset.sum_sub_distrib; congr+ring`.

- **`eij_contact_variation_bound`**: for r ∈ [σ,R], Aₖ ≥ 0, zₖ ≥ 0:
  `0 ≤ eij(R)−eij(r)` and `eij(R)−eij(r) ≤ Σ Aₖ·(1−exp(−zₖ·(R−σ)))`.
  Proof: `Finset.sum_nonneg` + `Finset.sum_le_sum`; per-term: `exp_le_exp.mpr` + `nlinarith`.

- **`f5_ga_matrix_mix_error_bound`**: concrete M = Σ Aₖ·(1−exp(−zₖ·(R−σ))) for `f5_error_bound`
  when g = eij. No OZ.2/g₀_HS needed.
  Proof: applies `f5_error_bound` with `hbound` derived from `eij_contact_variation_bound`.

**Remaining open:** Full numeric bound for g = g₀_HS + g^(1) still requires the
closed-form `g₀_HS(r)` at general r > σ. `g₀_HS` is now defined concretely as `1 + oz_h`
in `PYOZ_GHS.lean` , but bounding `oz_h(r)` explicitly requires OZ.2a (`oz_fixed_pt_unique`)
and OZ.2b (radial Laplace convolution). The contact value `g₀_HS(σ) = (1+η/2)/(1−η)²` is an axiom.
The FMSA_GA_matrix_mix contribution `g^(1)` now has an explicit bound.

**Key implementation lesson:** Lean 4's `∫ r in a..b, A r − ∫ r in a..b, B r` is parsed
as a *single* integral `∫r, (A r − ∫r, B r)` (greedy notation), not a subtraction of two
integrals. Explicit parens `(∫r, A r) − (∫r, B r)` are required. Also, `interval_sub` /
`integral_const_mul` produce types with Lean's internal bound variable `x` while goal uses
`r`; use `by apply ...` (tactic mode) rather than `:= term` to avoid elaboration mismatch.

---

### Task F.6 — Self-consistent inner-core free energy comparison: FMSA_GA_matrix_mix exact vs LJ approximation

**Context:** `FMSA_GA_matrix_mix` (FMSA_GA_matrix_mix) computes the inner-core first-order free energy by
integrating the exact FMSA DCF `c^(1)(r)` from [chsY] Eq. 41.  `FMSA_poly` instead uses the
LJ contact-value approximation `g₀(R_ij) · ∫_σ^R u_LJ(r)·r² dr` (Task F.2b).  Both give
closed-form answers; this task formalises the algebraic difference between them.

**Statements (two closed forms already proved):**

**(A) FMSA_GA_matrix_mix exact inner-core free energy** (from F.2a + Task 4.1):
```
βA^(1)_inner,PathB / (4π ρ/2)  =  K · (1+A(z))² · [R/z − 1/z² + exp(−zR)/z²]
                                 =  K · (1+A)² · inner_I1
```
where `inner_I1 := R/z − 1/z² + exp(−zR)/z²` is the I₁ result (Task 1.1).

**(B) LJ contact-value approximation** (from F.2b):
```
βA^(1)_inner,LJ / (4π ρ/2)  ≈  g₀(R) · R³ · (−(σ/R)¹²/9 + (σ/R)⁶/3 − 2(σ/R)³/9)
                              =  g₀(R) · (−LJ_term)
```
where `LJ_term = R³·((σ/R)¹²/9 − (σ/R)⁶/3 + 2(σ/R)³/9)` (negative of ∫ u_LJ r² dr).

**(C) Algebraic difference (main theorem):**
```lean
-- Task F.6 main theorem: exact algebraic identity relating the two routes
theorem ga_matrix_mix_vs_lj_inner_energy
    (K A_val z R g0 σ : ℝ) (hR : 0 < R) (hσ : 0 < σ) (hσR : σ ≤ R) (hz : 0 < z) :
    let inner_I1 := R / z - 1 / z ^ 2 + Real.exp (-(z * R)) / z ^ 2
    let lj_int   := R ^ 3 * ((σ/R)^12/9 - (σ/R)^6/3 + 2*(σ/R)^3/9)
    K * (1 + A_val) ^ 2 * inner_I1 - g0 * (-lj_int) =
    K * (1 + A_val) ^ 2 * inner_I1 + g0 * lj_int := by
  ring
```
**Note:** The `ring` proof confirms the two representations are related by a sign convention
only — the real content is in the physical values of K, (1+A)², g₀ which differ in the two
routes. The diagnostic theorem of interest is the **numeric bound on the difference**, which
requires substituting the FMSA expressions for K, A, g₀:

**(D) Concrete bound theorem (physical parameters):**
For single-component, N=1, using Task 4.2 (`g = S/D`, `a = 12ηL/D`) and Task 4.1
(`(1+A)² = (1−η)⁴z⁶/D²`):
```lean
-- The FMSA_GA_matrix_mix coefficient (1+A)² and the FMSA_pure coefficient (1-g²) differ:
-- (proved in Task 4.3 counterexample)
-- So the free energy difference is:
theorem ga_matrix_mix_inner_ne_lj_inner (η z : ℝ) (hη : 0 < η) (hη1 : η < 1) (hz : 0 < z) :
    -- (1+A)²·inner_I1 ≠ (1-g²)·lj_int   in general
    ...
```

**Why it matters:**
- Provides the formal algebraic statement that FMSA_GA_matrix_mix and FMSA_poly compute *different*
  inner-core free energies (not just different DCFs), quantified by the closed-form gap.
- The N=1 case connects directly to Task 4.3 (`(1+A)² ≠ 1−g²`): the free energy
  difference is proportional to `[(1+A)² − (1−g²)] · inner_I1`.
- Together with the outer-core (Task F.1, identical for both routes), gives the total
  first-order free energy discrepancy between FMSA_GA_matrix_mix and FMSA_poly.

**Proof strategy for (C):** `ring` — trivially true as written, since it is a sign identity.

**Proof strategy for (D):** Substitute the Baxter A(z) and g(z) expressions, use
`eq41_n1_reduces_to_eq42` (Task 4.4) + `identity_one_plus_A_sq_ne_one_minus_g_sq` (Task 4.3)
to show `(1+A)² ≠ 1−g²`, then conclude the free energies differ by `≠ 0`.

**Depends on:** Task 1.1 (I₁ formula, for `inner_I1`), Task F.2b (LJ integral, ✓ done),
Task 4.1 (`b_n1_baxter_formula`), Task 4.3 (counterexample `(1+A)² ≠ 1−g²`).

**Status:** ✓ DONE — two theorems in `LeanCode/FreeEnergy/SumRule.lean` (complete):
  - `ga_matrix_mix_vs_lj_inner_energy_diff` (part C): sign identity `pathB − lj_approx = pathB + g₀·lj_int`
    proved by `ring` alone.
  - `ga_matrix_mix_vs_lj_energy_integral_form` (part D): substitutes `inner_core_single_term_integral` (F.2a)
    and `lj_integral` (F.2b) then `ring`. Import added: `LeanCode.FreeEnergy.LJIntegral`.
  Note: "Imports out of date" build-cache warning expected on first load after new import.

---

