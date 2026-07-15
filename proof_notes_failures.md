# Proof Notes: Formula Failure Analysis

Detailed proof records for method failures:
- **Group chsY** — why the naive [chsY] Eq. 41 formula fails (wrong (1+A)² coefficient)
- **Group P** — why polynomial approximation structurally fails for repulsive Yukawa tails
- **Group GA** — why FMSA_GA_matrix_mix's *own* inner formula is ill-conditioned for unlike pairs
  at large σ-ratio (Tasks GA.1, GA.2; positive counterparts C.2, C.5 stay in `proof_notes_yukawa_dcf.md` Group C)

See `todo_lean.md` for task status summary.

---

## Group chsY — FMSA_chsY Inner-Core Formula Failure  *(FMSA_chsY specific)*

These tasks document why the naive application of [chsY] Eq. 41 produces the wrong inner-core
DCF for pairs involving the smallest-diameter species. The root cause: the coefficient `(1+A)²`
in Term I of Eq. 41 is NOT equal to `(1−g²)` from FMSA_pure, despite the paper's implicit claim.
This is the algebraic origin of the positive spike seen in `check_gcmc_chsY.py` results.

The fix (FMSA_GA_matrix_mix) uses the full G/A matrix decomposition to replace `(1+A)²` with the
correct matrix entries `(1−Ĝ²_{ij})` and `Â²_{ij}`. See `proof_notes_yukawa_dcf.md` Groups B, C.

### Task 4.3 — Does `(1+A(z))² = 1−g²`?  (Root cause of the HSY positive spike)

**Result: DISPROVED (analytically). No Lean proof needed — algebraic falsification is complete.**

**Algebraic proof of falsification:**

With D = S(z) + 12ηL(z)e^{−z} = (1−η)²z³Q₀(z), the identity reduces to:
```
(1−η)⁴z⁶ = 12ηL(z)·e^{−z} · (2S(z) + 12ηL(z)·e^{−z})
```
LHS is a polynomial in (η,z) with no exponential factors; RHS contains e^{−z} and e^{−2z}.
These cannot be equal for generic parameters — the identity is structurally impossible.

**Counterexample (η = 3/4, z = 1, σ = 1):**
- S(1) = −179/8,  L(1) = 31/8
- LHS = (1/4)⁴ = 1/256 > 0
- Using e^{−1} ≤ 1/2 (from Real.add_one_le_exp):  inner factor ≤ −179/4 + 279/16 = −437/16 < 0
- RHS = (positive) × (negative) < 0  →  LHS > 0 > RHS  ✗

**Physical consequence:** For any pair involving the smallest-diameter species (like pairs in
single-component; also c₁₁ and c₁₂ in binary), Terms II/III/IV of [chsY] Eq. 41 are
identically zero inside the core. Only Term I = K(1+A)²e^{−z(r−R)} survives, giving the
wrong inner-core coefficient. FMSA_pure uses K(1−g²)e^{−z(r−R)} (correct). Since (1+A)² ≠ 1−g²,
the chsY formula is wrong for these pairs for all r < R_ij.

**Generalisation:** The spike affects ALL pairs (i,j) where min(σ_i,σ_j) = σ_min (global
minimum diameter) — not just like pairs. Cross-pair c₁₂ in a binary mixture is also affected.

**Fix direction:** For problematic pairs, add the missing growing-exponential and polynomial
correction from [chsY] Eq. 43. For N=1 the exact fix is FMSA_pure (Eq. 42). Multi-component
fix requires deriving matrix analogs of g_{ij} and a_{ij} from Q̂₀ decomposition.

**See:** `problem_answers/math_conclusions.md` §5a and §5b for full derivation.

**Status:** ✓ RESOLVED — identity is FALSE. Lean counterexample in
  `LeanCode/FMSAPoly/OriginCheck.lean` (proof strategy ready, using nlinarith + exp bound).

---

## Group P — FMSA_poly Inner-Core Structure  *(FMSA_poly specific)*

These tasks formalise the E+P decomposition used in `FMSA_poly_term_species` and explain
why it fails for repulsive tails.  They are independent of the exact formula (Group 4).

**Central conclusion (established by P.1–P.C1):** The polynomial approximation failure in
FMSA_poly is **not** a matter of insufficient degree — it is a structural impossibility.
The FMSA_poly origin normalisation (Task P.2) forces `P_ij(0) = −E_ij(0) ≤ 0`, but the
target function satisfies `exp(z·(R−0)) = exp(z·R) ≈ 10⁶`.  The error at r = 0 is
therefore ≥ exp(z·R) for **any** polynomial of **any** degree N, because only the constant
term determines p(0) and the normalisation fixes it.  The fix (Tasks P.B1/P.B2, FMSA_GA_matrix_mix) is
to replace the polynomial basis with a 2-term exponential sum that can satisfy both boundary
conditions exactly — something no polynomial can do under the normalisation constraint.

### Task P.1 — E_ij is a sum of decaying exponentials

**Statement:** The `get_e_ij` contribution has the form:
```
E_ij(r) = Σ_{t, m, n} A_ij(z_{mn}^t) · exp(−z_{mn}^t · (R_ij − r))
```
where all `z_{mn}^t > 0`, so each term GROWS from `exp(−z·R_ij) ≈ 0` at r=0 to 1 at r=R_ij.
In particular:
```
E_ij(R_ij) = Σ A_ij(z_{mn}^t)      (sum of propagator values)
E_ij(0)    = Σ A_ij(z_{mn}^t) · exp(−z_{mn}^t · R_ij)  (exponentially small for large z)
```

**Lean:** Define `E_ij` as a finite sum of such exponentials; show both boundary values
by `simp [Real.exp_zero]` and monotonicity of exp.

**Status:** ✓ DONE — proved in `LeanCode/FMSAPoly/EijStructure.lean` (complete):
  - `eij`: definition as a finite sum `Σ_k A_k · exp(−z_k · (R−r))`
  - `eij_at_contact`: E_ij(R) = Σ_k A_k  (all exp factors = 1)
  - `eij_at_origin`: E_ij(0) = Σ_k A_k · exp(−z_k · R)
  - `eij_exp_factor_strictMono`: for z > 0, r ↦ exp(−z·(R−r)) is strictly increasing

---

### Task P.2 — Origin constraint: p₀ = −E_ij(0) is necessary and sufficient

**Statement:** For like pairs (λ_ij = 0), the DCF formula has a 1/r singularity:
```
c^(1)_ij(r) = [E_ij(r) + P_ij(r)] / (2π√(ρiρj) · r)
```
This is finite at r = 0 **if and only if** `E_ij(0) + P_ij(0) = 0`, i.e., `p₀ = −E_ij(0)`.

Under this condition, by L'Hôpital:
```
lim_{r→0} [E_ij(r) + P_ij(r)] / r = E_ij'(0) + p₁
```
where `E_ij'(0) = Σ A_ij(z) · z · exp(−z · R_ij)` (finite).

**Lean:** Formalise using `Filter.Tendsto` and `HasDerivAt`:
```lean
theorem origin_finiteness (E P : ℝ → ℝ) (h : E 0 + P 0 = 0)
    (hE : HasDerivAt E e₀ 0) (hP : HasDerivAt P p₁ 0) :
    Filter.Tendsto (fun r => (E r + P r) / r) (nhdsWithin 0 {0}ᶜ) (nhds (e₀ + p₁)) := ...
```

**Note:** Setting `p₀ = −E_ij(0)` makes `c^(1)(0) = 0` — this is a renormalisation choice
in FMSA_poly, NOT required by the exact Yukawa theory (see Section 4 of math_conclusions.md).

**Status:** ✓ DONE — proved in `LeanCode/FMSAPoly/OriginConstraint.lean` (complete):
  - `origin_finiteness`: `E 0 + P 0 = 0` + HasDerivAt ⟹ `(E r + P r)/r → e₀ + p₁`
    Proof: `hasDerivAt_iff_tendsto_slope` + `vsub_eq_sub` to convert slope to `/r` form
  - `origin_necessity`: limit finite + ContinuousAt ⟹ `E 0 + P 0 = 0`
    Proof: product `r·((E r+P r)/r) → 0·L = 0` via `Filter.Tendsto.mul`; uniqueness via `tendsto_nhds_unique`

---

### Task P.3 — No polynomial of ANY degree can approximate exp(+z·(R−r)) under origin normalisation

**Statement (informal):** Under the FMSA_poly normalisation constraint `P_ij(0) ≤ 0`, NO
polynomial of ANY degree N can approximate `f(r) = exp(+z·(R−r))` on [0, R] with L∞ error
less than `exp(z·R)`:
```
∀ N,  ∀ P ∈ ℝ[x] with P(0) ≤ 0:   max_{r ∈ [0,R]} |exp(z·(R−r)) − P(r)|  ≥  exp(z·R)
```
For z = 14, R = 1: lower bound = exp(14) ≈ 1.2 × 10⁶, **independent of degree N**.

**Note — degree-independent result vs. Chebyshev bound:**
The classical Chebyshev/Bernstein lower bound for UNCONSTRAINED polynomials is
`C · exp(z·R) / (2^N · N!)`, which DECREASES with N and → 0 as N → ∞.
Without the normalisation constraint, high-degree polynomials (or the Taylor series for exp)
CAN approximate `exp(+z·(R−r))` arbitrarily well on [0, R]. The FMSA_poly normalisation
`P(0) = −E_ij(0) ≤ 0` is what makes approximation IMPOSSIBLE at any degree: only the constant
term of P determines `p(0)`, and that term is pinned to ≤ 0 by the normalisation. Since the
target satisfies `f(0) = exp(z·R) ≫ 1`, the error at r = 0 is ≥ exp(z·R) regardless of how
many higher-degree terms P has. The degree N is structurally irrelevant.

**Why it matters:** This formally explains the negative spike near r = R_ij in FMSA_poly for
repulsive 2YK tails: the normalisation that makes `c(r)/r` finite at r = 0 forces P_ij(0) ≤ 0,
but the target `exp(+z·(R−r))` is exponentially large at r = 0. No polynomial degree can
overcome this single-point pinning. The fix (FMSA_GA_matrix_mix, Tasks P.B1/P.B2) replaces the polynomial
with a 2-term exponential sum that satisfies BOTH boundary conditions exactly — without any
normalisation conflict.

**Lean:** Proved in `LeanCode/FMSAPoly/PolyApproxFails.lean` (complete, **no degree bound**):
```lean
-- General version: p(0) ≤ exp(zR)/2 suffices for error ≥ exp(zR)/2
theorem poly_approx_fails (z R : ℝ) (hR : 0 < R) (p : Polynomial ℝ)
    (hp : p.eval 0 ≤ Real.exp (z * R) / 2) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| ≥ Real.exp (z * R) / 2

-- FMSA_poly case: normalisation gives p(0) ≤ 0 → error ≥ exp(zR)
theorem poly_approx_fails_origin (z R : ℝ) (hR : 0 < R) (hz : 0 < z) (p : Polynomial ℝ)
    (hp : p.eval 0 ≤ 0) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| ≥ Real.exp (z * R)
```
`p : Polynomial ℝ` carries **no** `natDegree p ≤ N` hypothesis — Lean's polynomial type is
the free ring over ℝ. Both theorems hold for degree 0, 1, 5, 100, or any N.

**Status:** ✓ DONE  *(corrected hypothesis in `poly_approx_fails`: `p(0) ≤ exp(zR)/2`; both
theorems build cleanly with no admitted goals and no degree hypothesis — degree-agnostic result proved)*

---
### Task P.4 — E_ij contact value matches outer-core MSA at r = R_ij

**Statement:** The outer-core DCF from the MSA closure at r = R_ij is:
```
c^(1)_ij(R_ij+) = Σ_t K_t / R_ij
```
(sum over all Yukawa tails, each contributing `K_t · exp(0) / R_ij = K_t / R_ij`).

From Task P.1, `E_ij(R_ij) = Σ A_ij(z_t)`. The matching condition at contact requires:
```
[E_ij(R_ij) + P_ij(R_ij)] / R_ij  =  Σ_t K_t / R_ij
→  E_ij(R_ij) + P_ij(R_ij)  =  Σ_t K_t
```

**Why it matters:** For FMSA_poly, this is approximately satisfied (P_ij absorbs the
mismatch), but the polynomial cannot achieve exact continuity AND smooth behaviour
near r = R_ij simultaneously when Σ K_t < 0 (repulsive net tail).

**Lean:** Show the outer-core limit by `simp [Real.exp_zero]`.  The mismatch is:
`E_ij(R_ij) + P_ij(R_ij) − Σ K_t = residual` where `|residual|` grows with z.

**Status:** ✓ DONE — proved in `LeanCode/FMSAPoly/ContactValue.lean` (complete):
  - `outer_dcf_at_contact` : `Σ K_t · exp(−z_t·0) / R = Σ K_t / R` by `simp [sub_self, Real.exp_zero]`
  - `contact_matching` : `(E+P)/R = Σ K_t / R ↔ E+P = Σ K_t` by `div_left_inj'`
  - `contact_poly_value` : under matching, `P(R) = Σ K_t − Σ A_k` by `eij_at_contact` + `linarith`

---

### Task P.C1 — Corollary: FMSA_poly normalization forces large approximation error (P.1 + P.2 + P.3)

**Statement:** Under the FMSA_poly origin normalisation with non-negative amplitudes `A_k ≥ 0`,
the polynomial `P_ij` is constrained to satisfy:
```
P_ij(0) = −E_ij(0) = −Σ_k A_k · exp(−z_k · R)  ≤  0
```
By Task P.3 (`poly_approx_fails_origin`), this immediately gives:
```
∃ r ∈ [0, R],  |exp(z·(R−r)) − P_ij(r)|  ≥  exp(z·R)
```
i.e. the approximation error is at least `exp(z·R)` — exponentially large, **for any degree N**.

**Why it matters:** This is the formal chain P.1 → P.2 → P.3 in one theorem: the normalisation
condition that makes `c(r)/r` finite at `r = 0` (Task P.2) is **exactly** the condition that
makes the polynomial approximation maximally bad (Task P.3). FMSA_poly pays for its `r = 0`
regularity with catastrophic approximation error throughout `[0, R]`.

The Lean theorem `fmsa_poly_origin_failure` takes `P : Polynomial ℝ` with **no degree bound**:
the result holds for N = 1, 5, 100, or any N. This is strictly stronger than the Chebyshev
bound `C·exp(zR)/(2^N·N!)`, which decreases with N — the P.C1 bound exp(z·R) is independent
of N because the normalisation pins `P(0)` regardless of how many higher-degree terms P has.

**Lean:** Direct composition in a new file `PolyApproxCorollary.lean`:
```lean
theorem fmsa_poly_origin_failure {n : ℕ} (A z : Fin n → ℝ) (hA : ∀ k, 0 ≤ A k)
    (R : ℝ) (hR : 0 < R) (P : Polynomial ℝ)
    -- Origin normalisation from Task P.2: E_ij(0) + P_ij(0) = 0
    (hnorm : FMSA.EijStructure.eij A z R 0 + P.eval 0 = 0)
    (z₀ : ℝ) (hz₀ : 0 < z₀) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z₀ * (R - r)) - P.eval r| ≥ Real.exp (z₀ * R) := by
  apply FMSA.PolyApproxFails.poly_approx_fails_origin _ _ hR hz₀
  -- Need: P.eval 0 ≤ 0.  From hnorm: P.eval 0 = −E_ij(0).
  -- From eij_at_origin + hA: E_ij(0) = Σ A_k · exp(−z_k·R) ≥ 0.
  have hE : 0 ≤ FMSA.EijStructure.eij A z R 0 := by
    simp only [FMSA.EijStructure.eij_at_origin]
    apply Finset.sum_nonneg; intro k _
    exact mul_nonneg (hA k) (Real.exp_nonneg _)
  linarith
```

**Status:** ✓ DONE — `fmsa_poly_origin_failure` in `LeanCode/FMSAPoly/PolyApproxCorollary.lean` (complete):
  `rw [eij_at_origin]` + `Finset.sum_nonneg` + `linarith`; imports EijStructure + PolyApproxFails.

---

### Task P.C2 — Tighter two-endpoint bound: error at r = 0 OR r = R (no hypothesis on p(0))

**Statement:** For any polynomial `p` of **any degree N** satisfying `p(0) ≤ p(R)` (polynomial
non-decreasing over `[0, R]`, i.e. going in the OPPOSITE direction to the strictly decreasing
target `f(r) = exp(+z·(R−r))`), at least one endpoint has large error:
```
max(|f(0) − p(0)|,  |f(R) − p(R)|)  ≥  (exp(z·R) − 1) / 2
```

**Why this is "tighter" than P.3:** Task P.3 requires `p(0) ≤ exp(z·R)/2` and witnesses only
`r = 0`. Task P.C2 requires only the monotonicity hypothesis `p(0) ≤ p(R)` — a different and
complementary regime — and witnesses whichever of `r = 0` or `r = R` gives the larger error.
Together P.3 + P.C2 cover:
- `p(0) ≤ exp(zR)/2` → P.3 applies, large error at r = 0.
- `p(0) ≤ p(R)` (wrong-direction polynomial) → P.C2 applies, large error at one endpoint.

The gap (polynomials with `p(0) ∈ (exp(zR)/2, exp(zR)]` AND `p(0) > p(R)`) requires the
full Chebyshev equioscillation theorem and is not yet Lean-formalised.

**Proof sketch:**
- Case 1: `p(0) ≤ (exp(zR) + 1)/2`. Then error at r = 0 is
  `exp(zR) − p(0) ≥ (exp(zR) − 1)/2`. ∎
- Case 2: `p(0) > (exp(zR) + 1)/2`. By `p(0) ≤ p(R)`, also `p(R) > (exp(zR)+1)/2 > 1`.
  So error at r = R is `p(R) − 1 > (exp(zR)−1)/2`. ∎

**Lean:**
```lean
theorem poly_approx_fails_two_endpoints (z R : ℝ) (hR : 0 < R) (p : Polynomial ℝ)
    (hmono : p.eval 0 ≤ p.eval R) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| ≥ (Real.exp (z * R) - 1) / 2 := by
  by_cases h : p.eval 0 ≤ (Real.exp (z * R) + 1) / 2
  · -- Case 1: large error at r = 0
    refine ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hR.le⟩, ?_⟩
    simp only [sub_zero]
    rw [abs_of_nonneg (by linarith [Real.exp_pos (z * R)])]
    linarith
  · -- Case 2: p(0) > (exp(zR)+1)/2 and p(R) ≥ p(0), so large error at r = R
    push Not at h
    refine ⟨R, Set.mem_Icc.mpr ⟨hR.le, le_refl R⟩, ?_⟩
    simp only [sub_self, mul_zero, Real.exp_zero]
    rw [abs_of_nonpos (by linarith [Real.exp_pos (z * R)])]
    linarith [Real.exp_pos (z * R)]
```

**Status:** ✓ DONE — `poly_approx_fails_two_endpoints` added to `LeanCode/FMSAPoly/PolyApproxFails.lean` (complete):
  two-case split; `Real.add_one_le_exp` for `hexp`; `abs_of_nonneg`/`abs_of_nonpos` + `linarith`.
  Note: `push_neg` deprecated → used `push Not` instead.

---

### Task P.B1 — Exponential basis: the 2×2 boundary system is always solvable

**Motivation:** Tasks P.3 and P.C1 prove that NO polynomial of ANY degree N can satisfy both
boundary conditions while keeping the approximation error small — the normalisation structurally
forces a catastrophic error at r = 0. The exponential basis circumvents this by adding a second
free parameter: instead of pinning the constant term (as polynomials do), it spreads freedom
across two exponentials that each affect the full range [0, R].

**Statement:** Replace the polynomial `P_ij` with a 2-term exponential sum
`Q_ij(r) = a · exp(−z·(R−r)) + b · exp(+z·(R−r))`.
The two FMSA_poly boundary conditions become a 2×2 linear system:
```
a  +  b                        =  Σ_t K_t − Σ_k A_k    [contact, from P.4: contact_poly_value]
a · exp(−zR)  +  b · exp(+zR) =  −E_ij(0)              [origin,  from P.2 + P.1]
```
The coefficient matrix determinant is `exp(zR) − exp(−zR) = 2 sinh(zR) ≠ 0` for `z, R > 0`,
so the system always has a unique solution `(a, b)` — regardless of z and R.

**Lean:** Prove `exp(z*R) - exp(-(z*R)) ≠ 0` for `z, R > 0`:
```lean
theorem exp_basis_det_ne_zero (z R : ℝ) (hz : 0 < z) (hR : 0 < R) :
    Real.exp (z * R) - Real.exp (-(z * R)) ≠ 0 := by
  have h1 : Real.exp (-(z * R)) < Real.exp (z * R) :=
    Real.exp_lt_exp.mpr (by linarith [mul_pos hz hR])
  linarith
```

**Depends on:** P.4 (`contact_poly_value` gives the RHS of the contact equation).

**Status:** ✓ DONE — `exp_basis_det_ne_zero` in `LeanCode/FMSAPoly/ExpBasis.lean` (complete):
  `Real.exp_lt_exp.mpr (by linarith [mul_pos hz hR])` + `linarith`; 3 lines as expected.

---

### Task P.B2 — Exponential basis: zero endpoint errors (contrast with P.3)

**Statement:** By construction, `Q_ij` satisfies both boundary conditions exactly:
- `Q_ij(R) + E_ij(R) = Σ K_t`  → error at r = R is **zero** (vs ≥ exp(zR)/2 for polynomials)
- `Q_ij(0) + E_ij(0) = 0`       → origin constraint holds exactly (P.2)

This proves `Q_ij` does what `P_ij` cannot at ANY degree: represent the [chsY] Eq. 41 Term I
exactly. The degree-agnostic failure proved in P.3/P.C1 is the formal justification for why
FMSA_pure's FMSA_GA_matrix_mix (exponential basis) is not just a numerical improvement over FMSA_poly, but
a structurally necessary replacement.

**Lean:** Given `(a, b)` solving the P.B1 system, show zero endpoint errors.
The proof is by definition: plug `r = 0` and `r = R` into `Q_ij` and use `Real.exp_zero`.

**Depends on:** P.B1 (for `(a, b)` values), P.4 (`contact_poly_value`), P.2, P.1.

**Status:** ✓ DONE — four theorems in `LeanCode/FMSAPoly/ExpBasis.lean` (complete):
  - `exp_basis_contact_bc` / `exp_basis_origin_bc`: abstract BC satisfaction (`rw` + `exact hbc`)
  - `exp_basis_satisfies_contact`: `rw [qij_at_contact, eij_at_contact]` + `linarith`
  - `exp_basis_satisfies_origin`: `rw [qij_at_origin]` + `linarith`
  Also defines `qij` (`noncomputable def`) and helper lemmas `qij_at_contact`, `qij_at_origin`.

---

## Group GA — FMSA_GA_matrix_mix Inner-Core Conditioning Failure  *(FMSA_GA_matrix_mix specific)*

FMSA_GA_matrix_mix is itself the **fix** for the two failures above — it replaces Group chsY's
wrong `(1+A)²` coefficient with the matrix entries `(1−Ĝ²_{ij})` / `Â²_{ij}`, and Group P's
polynomial basis with a two-exponential basis (Tasks P.B1/P.B2). This group documents the regime
where FMSA_GA_matrix_mix's *own* inner formula breaks down: **unlike pairs at large σ-ratio**,
where the two-exponential base `K·exp(z·R_{ij})` diverges and no bounded additive correction can
rescue it.

The full story has four parts; the two **failure** results are formalized here (GA.1, GA.2), and the
two **positive** counterparts stay in `proof_notes_yukawa_dcf.md` Group C (C.2, C.5):

- **C.2** *(Group C — positive)* — for N=1 like pairs an **exp-cancellation** keeps the two-exp
  formula bounded. This is *why* the single-component limit is well-conditioned; it is the
  reference point the failures below deviate from.
- **GA.1** *(here — failure)* — for N=2 unlike pairs the exp-cancellation is absent: the base
  `K·exp(z·R_{ij})` grows without bound with σ-ratio, and the additive HS-pole residue sum
  (Route C, `fmsa_hs_pole_residue.py`) contributes only O(K/z²), so it **cannot cancel** the
  divergence for any finite pole set. Extends Group P's degree-agnostic failure (P.3/P.C1) from
  polynomials to bounded-coefficient exponential sums.
- **GA.2** *(here — failure, structural root cause)* — the off-diagonal `G_{01}(z) → 0`
  exponentially for large σ-ratio, so `(1−G²) ≈ 1` and the large factor `exp(z·R_{01})` has no
  algebraic cancellation. This is *why* GA.1's base diverges for unlike pairs but not for the N=1
  like pair of C.2.
- **C.5** *(Group C — positive)* — `K·G·exp` is the leading-order Yukawa-pole residue (the exact
  residue is the doubly-propagated `Q̂₀⁻¹·K·Q̂₀⁻ᵀ`; `K·G·exp` = `K·G²` at N=1 — see the C.5 CORRECTION),
  so the Route C inner formula is correct at leading order; the residual 2YK error is entirely in the
  outer-region `K₀₁` values, not the inner formula. (Interprets the numerically observed
  ĉ₁₂ ≈ 0 as *expected*, not a bug.) The concrete derivation now lives in **Group Y1** (Y1.1/Y1.5/Y1.6
  done; Y1.3 = remaining WH split).

**Task IDs.** GA.1 and GA.2 are the group-local task IDs, renumbered 2026-07-15 from their
original `C.3`/`C.4` when they were split out of Group C into this failure group. Any in-progress
proof effort keyed to the old `C.3`/`C.4` names should update to `GA.1`/`GA.2`. C.1/C.2/C.5 remain
in Group C.

*Source: `fmsa_hs_pole_residue.py` Route C analysis + `_build_pure_refs` bug fix (2026-07-15).*

---

### Task GA.1 (formerly C.3) — Unlike-pair two-exp base grows without bound; additive HS-pole sum cannot cancel it

**Statement (part A — existential):**
```lean
theorem unlike_pair_twoexp_unbounded (K : ℝ) (hK : 0 < K) (M : ℝ) :
    ∃ z R : ℝ, 0 < z ∧ 0 < R ∧ K * Real.exp (z * R) ≥ M := by
  use 1, max 0 (Real.log (M / K)) + 1
  constructor; · norm_num
  constructor; · linarith [Real.log_pos (div_pos (lt_of_lt_of_le ... hK) hK)]
  · calc K * Real.exp (1 * _) ≥ K * Real.exp (Real.log (M / K) + 1) := ...
          _ ≥ M := ...
```
(Choose z = 1, R = log(M/K) + 1; then K·exp(z·R) = K·exp(log(M/K)+1) ≥ M.)

**Statement (part B — additive correction insufficient):**
```lean
theorem hs_pole_additive_insufficient
    (K z R : ℝ) (hK : K > 0) (hz : z > 0) (hR : R > 0) (hzR : z * R > 1)
    (n : ℕ) (B : Fin n → ℝ) (hB : ∀ k, |B k| ≤ K / z ^ 2)
    (additive : ℝ) (hadditive : additive = ∑ k, B k) :
    K * Real.exp (z * R) + additive ≥ K * (Real.exp (z * R) - n / z ^ 2) := by
  ...
-- Corollary: for z*R >> 1, K·exp(z·R) dominates n·K/z² (finitely many poles)
```

**Why it matters:** Closes the Route C failure story. Groups P.3/P.C1 proved no POLYNOMIAL
can approximate `exp(+z(R-r))` under normalisation; Task GA.1 extends this to HS-pole residue
sums: since `|B_k| ≤ |K| · |adj Q̂₀(s_k)|_{ij} / (|z²-s_k²| · |det' Q̂₀(s_k)|) = O(K/z²)` and
there are finitely many poles, the total correction `|Σ_k B_k| ≤ n·|K|/z²` ≪ K·exp(z·R)
when z·R ≫ log(n). This proves the HS-pole additive approach fails for any finite number of poles.

**Depends on:** P.3 (done), P.C1 (done). New content: the O(K/z²) bound on residues.

**Status:** ✓ DONE (2026-07-15), axiom-clean — `LeanCode/FMSAPoly/PolyApproxFails.lean`.
Part A `unlike_pair_twoexp_unbounded` (witness `z=1`, `R = max 0 (log(M/K)) + 1`; `Real.exp_log` +
`Real.exp_le_exp` + case split on `M ≤ 0`). Part B `hs_pole_additive_insufficient` (`|∑ B k| ≤
∑|B k| ≤ n·(K/z²)` via `Finset.abs_sum_le_sum_abs`, then `linarith`); the `|B k| ≤ K/z²` residue
bound stays the explicit hypothesis `hB` (numerically verified), as planned.

---

### Task GA.2 (optional, formerly C.4) — Off-diagonal G-matrix element decays exponentially for large σ-ratio

**Physical content:** For N=2, G_{01}(z) = [adj Q̂₀(z)]_{01} / det Q̂₀(z). The numerator
`[adj Q̂₀]_{01} = -Q̂₀_{10}(z)` (2×2 cofactor) involves an off-diagonal entry of Q̂₀, which
from B.2's decomposition `Q̂₀ = P̂ + Ê·exp(-z·σ_min)` contributes terms proportional to
`exp(-z·λ_{01}) = exp(-z·(σ₁-σ₀)/2)`. So `G_{01} = O(exp(-z·(σ₁-σ₀)/2)) → 0` as σ₁-σ₀ → ∞.

**Lean statement (scaling limit):**
```lean
theorem g_mat_offdiag_decay (σ₀ σ₁ : ℝ) (hσ : σ₀ < σ₁) :
    Filter.Tendsto (fun z => G_mat_01 z σ₀ σ₁)
                   Filter.atTop (nhds 0) := ...
```

**Effort:** High — requires analysing the explicit N=2 Q̂₀ matrix formula from B.2,
expanding the cofactor, and applying exponential-decay dominated-convergence. Depends on
B.2 (done), M.3/M.4. Priority: lower than C.2/C.5.

**Status:** ◑ decay mechanism DONE (2026-07-15), axiom-clean —
`LeanCode/YukawaDCF/OffDiagDecay.lean`.  `g_mat_offdiag_decay`: given the numerator's exp-decay
bound `|num z| ≤ C·exp(−z·λ)` (`λ = (σ₁−σ₀)/2 > 0`) and `den z → L ≠ 0`, the ratio `num/den → 0`
(squeeze via helper `exp_neg_mul_atTop`, then `Tendsto.div`).  **Deferred (high effort):** discharge
the two hypotheses from the explicit N=2 `Q0_mat` — prove `|Q̂₀_{01}(z)| ≤ C·exp(−z·(σ₁−σ₀)/2)`
(B.2) and `det Q̂₀(z) → L ≠ 0` (M.4).

---


