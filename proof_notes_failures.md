# Proof Notes: Formula Failure Analysis

Detailed proof records for method failures:
- **Group chsY** — why the naive [chsY] Eq. 41 formula fails (wrong (1+A)² coefficient)
- **Group P** — why polynomial approximation structurally fails for repulsive Yukawa tails
- **Group GA** — why FMSA_GA_matrix_mix's *own* inner formula is ill-conditioned for unlike pairs
  at large σ-ratio (Tasks GA.1–GA.3; **GA.4 retired 2026-07-17** — doubly falsified, tombstone kept;
  positive counterparts C.2, C.5 stay in `proof_notes_yukawa_dcf.md` Group C)

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

The core story has four parts; the two **failure** results are formalized here (GA.1, GA.2; further
extended by GA.3 below — **GA.4 retired 2026-07-17**, see its tombstone), and the two **positive**
counterparts stay in `proof_notes_yukawa_dcf.md` Group C (C.2, C.5):

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

**Task IDs.** GA.1–GA.3 are the live group-local task IDs (**GA.4 retired 2026-07-17**, tombstone
kept below). GA.1/GA.2 were renumbered 2026-07-15 from their original `C.3`/`C.4` when they were split
out of Group C into this failure group (any in-progress proof effort keyed to the old `C.3`/`C.4` names
should update to `GA.1`/`GA.2`). **GA.3** (perturbation *ratio* unbounded) extends the failure argument
from the termwise base bound to the ratio. **GA.4** (perturbation *series* radius of convergence → 0,
formerly `Y2.16`, moved here 2026-07-15 in the Group-Y2 split) was **retired as doubly falsified** — it
over-reached from "the GA split is ill-conditioned" (true) to "perturbation theory itself diverges"
(false). C.1/C.2/C.5 remain in Group C.

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
    {C K z R : ℝ} (_hK : 0 < K) (_hz : 0 < z) {n : ℕ} (B : Fin n → ℝ)
    (hB : ∀ k, |B k| ≤ C * K / z ^ 2) :
    K * Real.exp (z * R) - (n : ℝ) * (C * K / z ^ 2) ≤ K * Real.exp (z * R) + ∑ k, B k
```
(Corollary: for `z·R ≫ log n`, `K·exp(z·R)` dominates the fixed `n·C·K/z²`.)

**Statement (part B, helper — `hB` discharged structurally, 2026-07-17):**
```lean
theorem residue_propagator_bound {n : ℕ} (A s : Fin n → ℂ) {C K z : ℝ}
    (hK : 0 ≤ K) (hz : 0 < z) (hA : ∀ k, ‖A k‖ ≤ C)
    (hsep : ∀ k, 2 * ‖s k‖ ≤ z) (k : Fin n) :
    ‖A k * K / ((z : ℂ) ^ 2 - (s k) ^ 2)‖ ≤ 4 / 3 * C * K / z ^ 2
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
∑|B k| ≤ n·(C·K/z²)` via `Finset.abs_sum_le_sum_abs`, then `linarith`).

**Update 2026-07-17 — `hB` discharged; it was never a physics input.**  `hB` sat in the
conditional-hypothesis table as `num` ("numerically verified").  That classification was **wrong**.
Reading the Route-C implementation (`fmsa_hs_pole_residue.py:17,116`):
```
B_k = Σ_t  K_t · A_k / (z_t² − s_k²),      A_k := [adj Q̂₀(s_k)]_ij / det′Q̂₀(s_k)
```
`A_k` and `s_k` come from `ga._hs_adj` / `ga._hs_det_prime` / `ga._hs_poles` — the **hard-sphere**
Baxter matrix alone.  They carry **no `z`-dependence**: every `z` in `B_k` sits in `K_t` or in the
propagator `1/(z_t² − s_k²)`.  Two consequences:

1. **The `O(K/z²)` shape is elementary**, now proved by `residue_propagator_bound`: away from
   resonance (`2‖s_k‖ ≤ z`) the reverse triangle inequality gives `‖z² − s_k²‖ ≥ z² − ‖s_k‖² ≥
   (3/4)z²`, hence `‖B_k‖ ≤ (4/3)·C·K/z²` with `C := max_k ‖A_k‖`.  The max exists because GA.1's
   pole set is **finite** (`Fin n`) — which is why **no** `POLE.5`/`MML.5`-style per-pole magnitude
   machinery is needed here.  That machinery is for *infinite* pole sums (`mixHS_summable`); GA.1
   never needed it.
2. **The sharp constant was fake precision.**  `‖B_k‖ ≤ K/z²` (i.e. `C = 1`) is **not** a theorem:
   it forces `‖A_k‖ ≤ ‖1 − s_k²/z²‖`, whose limit as `z → ∞` is `1` — so it demands `‖A_k‖ ≲ 1`, a
   numerical accident of the HS Baxter matrix, not a fact.  The theorem now quantifies over an
   arbitrary `C`; the GA.1 argument is **insensitive** to it (it only needs `n·C·K/z²` *fixed* while
   `K·exp(z·R) → ∞`).  Nothing was lost by dropping the sharp form.

**Scope caveat — GA.1 bounds a formula that is itself a candidate.**  `fmsa_hs_pole_residue.py:27`
states: *"This is an EXPERIMENTAL implementation. The residue coupling factor `1/(z_t²−s_k²)` is a
**candidate** derived from the Laplace-space 1D Yukawa propagator."*  So GA.1's counting argument
refutes one guessed ansatz, not HS-pole corrections in general.

**The stronger reason Route C fails (2026-07-17).**  The shipped, validated `fmsa_double_prop`
assembles `Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` — **no `Q̂₀⁻¹`, hence no HS poles in the DCF at all**; the
zeros of `det Q̂₀` enter only the RDF `ĥ₁` (via `Q̂₀⁻¹`).  Route C's premise — adding HS-pole residues
to the DCF inner core — adds objects that **do not belong there**.  GA.1's conclusion (Route C fails)
stands, but this structural fact is a far stronger reason than the `O(K/z²)` counting.  Cf. the GA.3
scope correction: the *true* `c^(1)` is O(1)-bounded (0.332 vs the GA formula's 1.78×10⁸), so the
perturbation expansion is fine — it is the **split** that diverges.

---

### Task GA.2 (optional, formerly C.4) — Off-diagonal G-matrix element decays exponentially for large σ-ratio

**Physical content:** For N=2, G_{01}(z) = [adj Q̂₀(z)]_{01} / det Q̂₀(z). The numerator
`[adj Q̂₀]_{01} = -Q̂₀_{10}(z)` (2×2 cofactor) involves an off-diagonal entry of Q̂₀, which
from M.10's decomposition `Q̂₀ = P̂ + Ê·exp(-z·σ_min)` contributes terms proportional to
`exp(-z·λ_{01}) = exp(-z·(σ₁-σ₀)/2)`. So `G_{01} = O(exp(-z·(σ₁-σ₀)/2)) → 0` as σ₁-σ₀ → ∞.

**Lean statement (scaling limit):**
```lean
theorem g_mat_offdiag_decay (σ₀ σ₁ : ℝ) (hσ : σ₀ < σ₁) :
    Filter.Tendsto (fun z => G_mat_01 z σ₀ σ₁)
                   Filter.atTop (nhds 0) := ...
```

**Effort:** was High — the explicit N=2 `Q̂₀` cofactor + a large-`z` limit argument. Depends on
M.10 (done), M.3/M.4. Done via a `Tendsto` layer over the M.4 rank-2 apparatus.

**Status:** ✓ DONE (2026-07-15), fully axiom-clean. Two files:

*Mechanism* (`LeanCode/YukawaDCF/OffDiagDecay.lean`): `g_mat_offdiag_decay'` (Tendsto form:
`num→0` + `den→L≠0` ⟹ `num/den→0`, via `Tendsto.div`+`zero_div`) and `g_mat_offdiag_decay`
(the exp-bound form, now a corollary via `squeeze_zero_norm`).

*Concrete N=2 discharge* (`LeanCode/HSMixture/Q0DetLimit.lean`, all axiom-clean):
- **atomic** `p1_tendsto_zero` / `p2_tendsto_zero`: `p1(σ,z),p2(σ,z)→0` as `z→∞` (term-split
  `p1 = 1/z² − σ/z − e^{−zσ}/z²` etc., each `→0`); propagated to `fFun_tendsto_zero`,
  `gFun_tendsto_zero`.
- `Q0_mat_phys_offdiag01_tendsto_zero`: `Q0_mat_phys(z) 0 1 → 0` for `σ₀<σ₁`, via
  `Q0_mat_phys = 1−U·V` + generalized `UV_apply`; entry(0,1) `= −√(ρ₀ρ₁)·exp(−λz)·(fFun 0+gFun 0·σ₁)`
  with `exp(−λz)→0` and bracket `→0`.
- `Q0_mat_phys_det_tendsto_one`: `det Q0_mat_phys(z) → 1` via the rank-2 2×2 form
  (`Q0_mat_phys_det_eq_two_by_two`+`det_fin_two`); the four `Vmat·Umat` entries are `∑ⱼρⱼ(…)→0`
  (`VU_apply`/`VU_entry_tendsto_zero`), so `det → (1−0)(1−0)−0·0 = 1`. **This gives the nonzero
  limit `L=1` WITHOUT the `Q0_moment_det_pos` axiom.**

Final: `g_mat_offdiag_decay_concrete` (`OffDiagDecay.lean`): `Q0_mat_phys 0 1 / det → 0`.
**Design note:** the sketch's literal global bound `|Q̂₀_{01}(z)| ≤ C·exp(−z·(σ₁−σ₀)/2)` was
*replaced* by the cleaner, sufficient `Tendsto num → 0` — no clean constant `C` exists on all of
`(0,∞)` since the bracket is `O(1/z)` (blows up as `z→0⁺`). `#print axioms` on all three key
theorems: `[propext, Classical.choice, Quot.sound]`.

---

### Task GA.3 — Unlike-pair ratio of the **GA-matrix split** is unbounded

> **⚠ Scope corrected 2026-07-17 — this is about the GA-matrix *split*, not about perturbation theory.**
>
> The theorem is true and axiom-clean, but the original wording below ("FMSA outside its own
> convergence domain", "the perturbation expansion is formally invalid at 2YK physical parameters")
> **over-reached** — the same conflation that got **GA.4 retired**.
>
> What is unbounded is `K·exp(z·R_{01})`, the growing branch of the GA-matrix `(1−G²)/A²` **split**,
> against a `z`-independent HS bound. As a statement about *this approximation formula* it is real:
> `true_first_order_probe.md` measures GA-formula errors up to **10⁹** (pair (1,2): GA's
> max |c^(1)| = **1.78×10⁸**).
>
> It is **not** a statement about first-order perturbation theory, which is **fine** at 2YK: the
> **true** `c^(1)` is O(1)-bounded (max |c^(1)| = **0.332** for pair (1,2)), `c(s·K)` is smooth on
> `s ∈ [0,1]`, and first order at **full** coupling `s=1` is **1.3% / 1.4%** accurate in `ĉ(0)`.
> The exponentially large ratio is the split's **catastrophic cancellation**: the exact first-order
> term contains cancellations (N=1 analogue `(1−g²)·e^{zR} = 2a − a²e^{−zR}`, bounded via
> `Ĝ + Â·e^{−zσ} = I`) that the GA split destroys for unlike pairs because `R_ij > σ_min`.
>
> **Correct reading.** GA.3 ⇒ *the GA-matrix inner formula is unusable at large `z·R`* (which is why
> Route C / `FMSA_double_prop` replaced it) — **not** *FMSA perturbation theory diverges*.

**What to prove.** The ratio of the FMSA first-order inner amplitude to the zeroth-order (hard-sphere)
reference grows without bound as `z·R_{01} → ∞`:

```
‖c^(1)_{01}(r)‖_∞  /  ‖c_HS_{01}‖_∞  ≥  C · K · exp(z · R_{01})  →  ∞
```

In plain terms: the amplitude **the GA split assigns** to the inner core is exponentially large relative
to the HS reference. For 2YK parameters (`z₂ ≈ 9.3`, `R_{01} ≈ 1.43`, `|K₂| ≈ 2.32`), the ratio is
`≳ 2.32 · exp(13.3) ≈ 3.5 × 10⁶` — matching the probe's measured GA artifact (1.78×10⁸ for pair (1,2)),
and *not* the true `c^(1)` (0.332). See the scope box above.

**Mathematical content.** This is a direct corollary of GA.1 (`unlike_pair_twoexp_unbounded`:
`K · exp(z · R_{01}) → ∞`) combined with the observation that `c_HS` is bounded above by a constant
independent of `z`. Specifically: `c_HS,01` is a piecewise polynomial in `r` whose coefficients
depend only on the packing fractions and diameters (not on `z`), so `‖c_HS_{01}‖_∞ ≤ M_HS(η, σ)`
for a fixed bound. Therefore `c^(1)_{01}(r) ≥ K · exp(z · R_{01}) / C_r` at points `r ≈ 0` (from
the growing exponential branch), while `c_HS` is bounded — ratio → ∞.

**Why this is not just GA.1.** GA.1 proves the absolute amplitude `K·exp(z·R)→∞`; GA.3 phrases this
as a *relative* statement (first-order / zeroth-order ratio), which is the standard definition of
"not a small perturbation." GA.3 is the Lean-level bridge connecting the numerical observation
(OZ+MSA ≠ **GA-matrix** FMSA for 2YK) to a formal statement about **the split**.

**Lean plan.** Add `perturbation_ratio_unbounded` to `FMSAPoly/PolyApproxFails.lean`:
1. Quote `unlike_pair_twoexp_unbounded` (GA.1) for the numerator lower bound.
2. Quote a `c_HS_bounded_above` lemma (the HS FMT DCF is bounded by a `z`-independent constant;
   if not already in Lean, follows from the polynomial structure of `c_HS` + compact domain).
3. Combine: `liminf (ratio) ≥ liminf (K·exp(z·R) / M_HS) = +∞`.

**Effort.** Low — almost immediate from GA.1 + a bounded-c_HS lemma.

**Status.** ✓ DONE (2026-07-15), axiom-clean — `perturbation_ratio_unbounded` in
`FMSAPoly/PolyApproxFails.lean`. Direct corollary of `unlike_pair_twoexp_unbounded` (GA.1) applied at
target `M·M_HS`: for any `K>0`, fixed `z`-independent HS bound `M_HS>0`, and target `M`, there is a
state point `(z,R)` with `M ≤ K·exp(z·R)/M_HS`. `M_HS` (the `z`-independent sup bound on `‖c_HS,01‖`)
is threaded as an explicit hypothesis rather than derived — matching `hs_pole_additive_insufficient`'s
`hB`. `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---


### Task GA.4 — ~~*(post-MML.3 Corollary)* Convergence radius of the unlike-pair MSA perturbation series → 0 as z·R → ∞~~ **RETIRED (2026-07-17)**

> **⚠ RETIRED 2026-07-17 — doubly falsified. Do not revive as stated.**
>
> **(i) The mechanism no longer exists.** The argument below rests on "the exact inner-DCF poles
> `s_k(ε)`, roots of `det(Q̂₀(s,ε)) = 0`". (★) (Group MRS; `todo/to_Lean.md` §1) proves
> `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` carries **no `Q̂₀⁻¹`**, so the inner **DCF has no HS poles at all** — the
> `det Q̂₀` zeros never enter it. There are no inner-DCF poles to migrate with `ε`.
>
> **(ii) The conclusion is refuted numerically.** `numerical_notes/results/true_first_order_probe.md`
> (`probe_true_first_order.py`; non-circular certified ground truth) states verbatim: *"the claimed
> convergence radius `R_c ~ e^{−zR} ≈ 10⁻⁶` **is refuted**"*. Concretely: `c(s·K)` is **smooth on
> `s ∈ [0,1]`** (OZ converges in 28 iterations at every `s` — no singularity); first order at **full**
> coupling `s = 1` is **1.3% / 1.4%** accurate in `ĉ(0)` for pairs (1,2)/(2,2); the second-order
> fraction grows only linearly in `s` (0.05 → 0.2) — *"consistent with a well-behaved series at
> `s=1`"*. That is the exact opposite of `R_conv ≲ 2×10⁻⁶ ≪ |K₂| ≈ 2.3`.
>
> **(iii) Root cause — the conflation to avoid.** GA.4 read *the GA-matrix approximation's*
> ill-conditioning (**real**: GA.1–GA.3; the probe measures GA-formula errors up to 10⁹) as
> *first-order perturbation theory itself* diverging (**false**: the true `c^{(1)}` is O(1)-bounded —
> max |c^{(1)}| inner = **0.332** for pair (1,2), vs GA's **1.78×10⁸**). This is precisely the
> conflation called out in `true_first_order_probe.md` §5.4, which also forced a correction banner on
> `numerical_notes/theory/perturbative_breakdown_large_sigma_ratio.md` §3–5.
>
> **Status.** Never started; no Lean code to retract. **GA.1–GA.3 are unaffected** — they are
> statements about the GA-matrix *split*, not about perturbation theory, and the probe corroborates
> them (the 10⁶–10⁸ magnitudes *are* that split's ill-conditioning).
>
> The original text is kept below as a record of the refuted argument.

**Physical motivation.** GA.3 shows FMSA's first-order term is large (not a small perturbation). GA.4
is the companion series-level statement: even summing all orders, the perturbation series in the Yukawa
coupling `ε` has zero radius of convergence in the limit `z·R → ∞`. Together GA.3 + GA.4 give the
complete picture: FMSA is invalid both termwise and as a resummed series at 2YK parameters.

**Mathematical content.** Parameterise `Q̂₀(s, ε)` where `ε` scales the Yukawa interaction (`K_t → ε·K_t`).
The exact inner-DCF poles `s_k(ε)` are roots of `det(Q̂₀(s,ε)) = 0`. At `ε = 0`, `det = (φ₁φ₂)` with
roots at `s = z_t` (the Yukawa pole); for `ε > 0`, the roots shift. By holomorphy of `det` in `ε`, the
radius of convergence of `s_k(ε)` as a power series in `ε` is the distance to the nearest singularity
of `s_k(ε)`. The key claim:

```
R_conv(s_k) ≤ C · exp(−z · R_{01})
```

Mechanism: the Mittag-Leffler poles at `Im(s_k) ≈ k·π/R` (MZERO.1, quasi-periodic family at spacing `π/R`)
enter as functions of `ε` with an exponentially small coupling `∼ exp(−z·R)` — the same factor that
makes the unlike-pair inner formula ill-conditioned (the off-diagonal entry `Q̂₀_{01}(s,ε)` contains
`exp(−z·R)·ε`). As `z·R → ∞`, `exp(−z·R) → 0`, so the poles decouple from the coupling and
`R_conv → 0`. At 2YK physical parameters: `exp(−z₂·R_{01}) ≈ exp(−13.3) ≈ 2×10⁻⁶`, while
`|ε_phys| = |K₂| ≈ 2.32` — FMSA is inside the disk but the exact MSA poles lie outside, confirming
the series diverges.

**Why post-MML.3.** The full statement needs the Mittag-Leffler assembly (MML.3) to identify the physical
inner DCF as a convergent pole sum; the convergence radius claim then follows from the analytic
structure of the poles in `ε`. MZERO.1 (pole existence) is sufficient to establish `R_conv > 0`; bounding
it by `exp(−z·R)` needs the explicit quasi-periodic spacing from MZERO.2–MZERO.7.

**Lean plan.**
1. Define `Q0_coupling (ε : ℝ) (s : ℂ) := det(Q̂₀(s, ε·K))` — holomorphic in both arguments.
2. From MZERO.1/MZERO.2–MZERO.7: for each `n`, ∃`s_n(ε)` with `Q0_coupling ε s_n = 0` near `Im ≈ n·π/R`.
3. Show `|s_n(0) - z| < δ` (at ε=0, roots near the Yukawa poles), then by implicit function theorem
   (holomorphic IFT, available in Mathlib via `analytic_implicit_function` or similar) `s_n(ε)` is
   analytic in `ε` in a disk of radius ≥ `C·exp(−z·R)`.
4. Conclude `R_conv ≤ C·exp(−z·R)` (the poles become non-analytic at `|ε| ∼ exp(−z·R)`).
5. Specialize to 2YK: `R_conv ≲ 2×10⁻⁶ ≪ |K₂| = 2.32`.

**Depends on.** MZERO.1 (poles exist), MZERO.2–MZERO.7 (quasi-periodic family + spacing `π/R`), MML.3
(Mittag-Leffler assembly, for the "exact MSA inner DCF" conclusion). The implicit function theorem
step needs `AnalyticAt` for `Q0_coupling` in both arguments simultaneously (Mathlib has this via
`AnalyticOn.implicitFunction` or the complex IFT). The `exp(−z·R)` bound needs the off-diagonal
structure `Q̂₀_{01} = … · exp(−z·R_{01})` (from M.10, `QhatDecomposition.lean`).

**Status.** ☐ not started. Effort: HARD (the analytic IFT + `ε`-coupling parameterization is new
infrastructure; the quasi-periodic spacing from MZERO.2–MZERO.7 is the key geometric input).

---
