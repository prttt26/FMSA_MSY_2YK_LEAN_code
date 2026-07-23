# Proof Notes: Inner-Core Mediated Breakpoints (Group IB)

Proof records for **Group IB** — the mediated inner-core breakpoint structure of the FMSA
mixture DCF. Split out of [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) (2026-07-15)
once it outgrew that file; see [todo_lean.md](todo_lean.md) for the status index.

**Source:** the Python `_compute_mediated` / `get_HS_FMT` in `fmsa_ga_matrix_mix.py`, and the
numerical passes `verify_mediated_breakpoints.py` / `verify_stepwise_breakpoints.py`.

> **⚠ DCF vs stepwise-poly / RDF scope (2026-07-17).** IB.6–IB.8's mediated breakpoints `r*`, `r**`
> are features of the `_compute_mediated` **stepwise-polynomial decomposition** and of the **RDF** —
> **not** of the exact first-order **DCF**, which has only the `λ_ij` knot (and `R_ij`) for every N.
> A formalization asserting a mediated *DCF* breakpoint would be **false**. See **IB.9** for the
> DCF-side bound. Same DCF/RDF dividing line as (★)/Group MRS (`todo/to_Lean.md`).


## Task ID ↔ Lean identifier map

**IB.1–IB.8 were formerly IB.1–IB.8.** The Lean identifiers in `YukawaDCF/InnerDecomp.lean` were
made **task-ID-free** (2026-07-15, e.g. `b11_…`→`terms_II_III_zero`), so IB.* can be renumbered
without touching Lean source.

| Task | (formerly) | Lean identifier(s) in `YukawaDCF/InnerDecomp.lean` | Status |
|------|-----------|-----------------------------------------------------|--------|
| IB.1 | IB.1 | `terms_II_III_zero` | ✓ DONE |
| IB.2 | IB.2 | `termIV_geometry_and_vanishing` | ✓ DONE |
| IB.3 | IB.3 | `active_pair_size_chain`, `mediated_zero_of_no_active_pair`, `binary_mediated_zero` | ✓ DONE |
| IB.4 | IB.4 | `residue_is_polynomial` | ✓ DONE |
| IB.5 | IB.5 | `ternary_148_active` | ✓ DONE |
| IB.6 | B.16 | `qP_at_uLo_zero`, `ivIntegrand_at_uLo_zero` | ✓ DONE |
| IB.7 | B.17 | `rstarstar_interior_iff_C`, `condC_activeB_imp_activeA` | ✓ DONE |
| IB.8 | B.18 | `uHiEff_eq_r`, `uHiEff_eq_r_of_active` | ✓ DONE |
| IB.9 | *(new)* | `MixtureConvolution.lean` (support geom) + `MixtureDCFSmooth.lean` (`dcfOdd_contDiffOn_upper`/`_lower`/`_like`, general N) | ✓ **general-N: only interior knot is λ_ij** |

The optional hard-sphere `λ_ij` kink (formerly B.19) moved to **Group OZ as OZ.18** — see
[proof_notes_hard_sphere.md](proof_notes_hard_sphere.md).

---

### Tasks IB.1–IB.5 — Inner DCF decomposition: mediated vanishing, Term IV breakpoints, domain of `P_ij`

**Motivation — new tasks, discovered from the numerical (Python) session, not from [chsY]/[LN]
directly.** GAP.5–GAP.10 establish `P_ij`'s degree and coefficients via the GAP.8 Laplace-moment
inversion, but leave open what `P_ij`'s actual *domain* is once cross-species "mediated"
contributions are accounted for. This surfaced as a real formalization gap during the Group Z
numerical work: specifically the `_update_polycorr` fix that subtracts `c_HS` (`get_HS_FMT`)
and `mediated` (`_compute_mediated`) from the OZ-converged inner DCF *before* running the GAP.8
moment fit. The fix only makes sense if `mediated` is analytically separable and provably
zero (or has characterized breakpoints) in the inner region.

**Breakpoint analysis** (completed 2026-07-12; script `verify_mediated_breakpoints.py`;
notes `numerical_notes/theory/mediated_breakpoints.md`).

*Sign convention:* `lambda_ij[k,l] = (sigma[l] − sigma[k]) / 2` (second minus first, over 2);
see `fmsa_ga_matrix_mix.py:162`.

> **CORRECTION:** an earlier version of these notes stated a "factor-of-3 threshold"
> (`sigma_j > 3·sigma_b` for Terms II/III to activate), based on an incorrect sign convention
> for `lambda_ij` (had first−second rather than second−first). That analysis was wrong.
> Terms II and III are always zero; the correct condition involves Term IV only.

**Statement (decomposition):** for pair (i,j) in an N-component mixture:
```
c^(1)_ij(r) = [Term_I(r) + P_ij(r)] / (2π·√(ρᵢ·ρⱼ)·r) + c^HS_ij(r) + mediated_ij(r)
```
`Term_I` is pure-exponential, `P_ij(r) = p₀+p₁r+p₂r²+p₃r³+p₄r⁴` (degree ≤ 4, GAP.5/GAP.8),
`mediated = (II + III + IV) / (2π√(ρᵢρⱼ)·r)` from `_compute_mediated`.

---

#### Why the old monolithic B.11 (now IB.1–IB.5) was rewritten (2026-07-13)

The previous single task (old **B.11**, before the IB.1–IB.5 split) carried four `sorry`s. Re-derived against the numerics, all four
statements turned out to be **vacuous** — they quantified over an *unconstrained* abstract
`mediated : ℝ → Fin N → Fin N → ℝ` and took the physical content as hypotheses:

| Old theorem | Defect |
|---|---|
| `b11_terms_II_III_zero` | `hII` already assumed `alpha < 0 → mediated_II = 0`. The derivation `alpha = r − σ_a − R_ij` — the sign-convention fix, i.e. the whole point — was assumed away. |
| `b11_termIV_activation` | **Unprovable.** `mediated_IV` was an unconstrained function with no hypothesis tying it to anything, and `hr_star_eq` was the tautology `X = X`. No proof term can exist. |
| `b11_residue_is_polynomial` | `hdecomp` baked in `(fun _ => 0) r`, i.e. `P ≡ 0`; closable by `P := 0`, erasing the degree-≤4 content. |
| `b11_mediated_zero_no_active_pair` | `hmedIV` **was** the conclusion, universally quantified; closable by `hmedIV r i i (hno_pair i i)`. |

The rewritten `InnerDecomp.lean` fixes this at the root: a `Mix N M` structure carries
`σ, ρ, b_grow` poles/coeffs, `Q0`, `Qpp` and `hσ : ∀ k, 0 < σ k`, and every definition
(`lam`, `alphaII`, `lstar`, `I1cl`, `I2cl`, `DeltaAi`, `cexp`, `dexp`, `uLo`, `uLoEff`,
`uHiEff`, `ivIntegrand`, `termIVsub`, `termIV`, `mediated`) mirrors `_compute_mediated`
(`fmsa_ga_matrix_mix.py:705-857`) line by line. `I1cl`/`I2cl` are stated *verbatim* as the RHS
of `I1_formula`/`I2_formula`, so Tasks 1.1–1.3 are genuine reuse rather than re-derivation.

The task was split: old **B.11** → IB.1–IB.5 (originally numbered B.11–B.15; renumbered to IB.* on
2026-07-15 when this group split off from Group GAP).

**The identity that drives everything (new, not in the earlier notes):**
```
Δ_ai := lam[i,a] − σ[a] = (σ_a−σ_i)/2 − σ_a = −(σ_i+σ_a)/2 = −R[i,a]   < 0  always
  ⇒  Alm   = max(Δ_ai, 0)          = 0
  ⇒  c_exp = R[a,b] + max(0,−Δ_ai) = R[a,b] + R[i,a]  =: r*
  ⇒  d_exp = R[a,b] − Δ_ai         = R[a,b] + R[i,a]  = r*      (so c_exp = d_exp)
```
This **derives** the breakpoint `r*` instead of positing it, and it makes conditions A/B
*consequences* rather than assumptions. Everything below follows from `σ > 0` alone — no axiom,
no numerical input.

---

### Task IB.1 — Terms II and III vanish in the inner region (unconditional)

**Statement:** for every `N`, every pair `(i,j)`, every σ, and all `r ∈ (0, R_ij)`:
`termII r i j = 0` and `termIII r i j = 0`.

**Proof:** Term II's activation variable collapses (`Mix.alphaII_eq`, ✓ proved by `ring`):
```
alpha = l + lambda_ij[i,a] − sigma[a] = r − sigma[a] − R[i,j]
```
Since `r < R[i,j]` (from `Ioo`) and `sigma[a] > 0` (`Mix.hσ`), `alpha < 0` — always. Then
`lstar = max(0, min(l, alpha)) = 0` (`lstar_eq_zero_of_alpha_neg`, ✓ proved), and
`I1cl _ _ 0 = I2cl _ _ 0 = 0` (`I1cl_at_zero` / `I2cl_at_zero`, ✓ proved — the closed-form face
of **Task 1.3**). Both `Finset` sums then vanish termwise. Term III is identical with `σ[b]`
(`Mix.alphaIII_eq`, ✓ proved).

Independent of `N`, of σ-ratio, and of which pair — unconditional.

**Corollary (worth recording):** the guard `if r < R[a,j]: continue` in `_compute_mediated` is
**redundant**. When `r < R[a,j]` we get `l < 0`; but `alpha < 0` holds regardless, so `lstar = 0`
on both branches. The Lean `termII`/`termIII` omit the guard and are still faithful.

**Lean:** `terms_II_III_zero`, `InnerDecomp.lean`.
**Depends on:** 1.3 (I₁/I₂ vanish at ℓ=0).
**Status:** ✓ DONE (proved 2026-07-14, axiom-clean).

---

### Task IB.2 — Term IV geometry and vanishing below the breakpoint

**Statement:** for all `i, j, a, b`:
```
Δ_ai = −R[i,a]  ∧  max(Δ_ai, 0) = 0  ∧  c_exp = R[a,b] + R[i,a]  ∧  d_exp = R[a,b] + R[i,a]
  ∧  ∀ r ≤ R[a,b] + R[i,a],  termIVsub r i j a b = 0
```

**Proof:** the four identities are `ring` after unfolding (`Δ_ai = −R[i,a]`, above). For the
vanishing: `u_hi_eff = min(r, u_hi_bj) ≤ r` by definition, and
`u_lo_eff = max(c_exp, u_lo_bj) ≥ c_exp = r*`. So `r ≤ r*` gives `u_hi_eff ≤ r ≤ r* ≤ u_lo_eff`,
which is exactly the `if u_lo_eff >= u_hi_eff: continue` branch — the sub-term is `0` by
definition. **No appeal to conditions A/B**: the vanishing half is unconditional.

*Note on faithfulness:* the `continue` is a **definitional clamp**, not a property of the
integral — a reversed interval integral is `−∫`, not `0`. The Lean `termIVsub` therefore keeps
the `if`, mirroring the Python rather than the (wrong) integral intuition.

**Lean:** `termIV_geometry_and_vanishing`, `InnerDecomp.lean`.
**Depends on:** nothing beyond `hσ`.
**Status:** ✓ DONE.

---

### Task IB.3 — Mediated ≡ 0 when no `(a,b)` is active; the binary corollary

**Activation conditions.** Conditions A and B are exactly the two ways Term IV's window can be
nonempty somewhere in the inner region:

- **(A)** `2·sigma[a] + sigma[b] < sigma[j]`  ⟺  `r* < R[i,j]` (breakpoint inside inner region)
- **(B)** `sigma[j] < 3·sigma[b]`             ⟺  `u_lo_bj < r` (window nonempty above `r*`)

If either fails, sub-term `(a,b)` is identically zero on `(0, R_ij)`: ¬A puts `r* ≥ R_ij > r`, so
IB.2 applies; ¬B gives `u_lo_bj = r + (σ_j − 3σ_b)/2 ≥ r ≥ u_hi_eff`, so the window is empty at
every `r`.

**Structural lemma (✓ PROVED, `active_pair_size_chain`):** A ∧ B force the strict size chain
```
sigma[a] < sigma[b] < sigma[j]
```
From A and `σ_a > 0`: `σ_b < σ_j`. From A and B: `2σ_a < σ_j − σ_b < 3σ_b − σ_b = 2σ_b`, so
`σ_a < σ_b`. Both are `linarith`.

**Binary corollary:** three *strictly increasing* diameters are required, but `a, b, j : Fin 2`
range over only two species — impossible. Hence **N=2 ⇒ mediated ≡ 0 for every pair at any
σ-ratio**. (Lean: `fin_cases` on `a`, `b`, `j` leaves 8 goals, each closed by `linarith` against
the chain.) This is the σ=[1,2] and σ=[1,4] rows of `verify_mediated_breakpoints.py`.

**Numerical verification (all 6 tested pairs confirmed):**

| Mixture | Active pairs | Outcome |
|---------|-------------|---------|
| Binary N=2, any σ | none — no (a,b) can satisfy both A+B | mediated ≡ 0 ✓ |
| Ternary σ=[1,2,4] | none — 2×1+2=4 not strictly less than σ_j=4 | mediated ≡ 0 ✓ |
| Ternary σ=[1,4,8] | (0,2),(1,2),(2,2) — 2×1+4=6<8 ✓; 8<12 ✓ | mediated ≠ 0, confirmed at r*=3.386/4.837/6.772 ✓ |

**Lean:** `active_pair_size_chain` (✓ proved), `mediated_zero_of_no_active_pair` (✓ proved),
`binary_mediated_zero` (✓ proved), `InnerDecomp.lean`.
**Depends on:** IB.1 (Terms II+III), IB.2 (Term IV window).
**Status:** ✓ DONE (all three theorems; proved 2026-07-14, axiom-clean).

---

### Task IB.4 — The residue is a *single* polynomial on `(0, R_ij)`

**Statement:** after exact subtraction of `c_HS` and `mediated`, the residue
`(c1_inner − c_hs − mediated) / prefac − term_I` equals one polynomial of `natDegree ≤ 4` on all
of `(0, R_ij)` — with **no piecewise split** at the Term IV breakpoint `r*` or at the `c_HS` kink
`|λ_ij| = (σ_j − σ_i)/2`.

**Why it matters:** this is what licenses `oz_numerical._update_polycorr` to run a *single* GAP.8
moment inversion over the whole inner region after subtracting `get_HS_FMT` and
`_compute_mediated`. `P_ij` is piecewise only if mediated is left *in*; once it is subtracted
exactly (rather than approximated), the sole source of a breakpoint at `r*` is gone.

**Proof:** algebra from the decomposition hypothesis plus `prefac ≠ 0` (`field_simp`); the degree
bound is imported from GAP.5 (`q0_entry_degree_bound`, `MixturePolyCoeffs.lean`), not re-derived.

**Lean:** `residue_is_polynomial`, `InnerDecomp.lean`.
**Depends on:** GAP.5 (degree bound), IB.3.
**Status:** ✅ **REDONE 2026-07-17 — the real content is now supplied; the original theorem is flagged
as the conditional it is.**

**New (`InnerDecomp.lean`, axiom-clean, zero `sorry`) — piecewise rigidity, which is what IB.4 should
have said:**
- `single_poly_forces_pieces_eq`: if `f = P₁.eval` on `(0,λ)`, `f = P₂.eval` on `(λ,R)`, **and**
  `f = Q.eval` on all of `(0,R)` for a single polynomial `Q`, then **`P₁ = Q ∧ P₂ = Q`**. Proof:
  `(0,λ)` and `(λ,R)` are each infinite, and a polynomial is pinned by its values on any infinite set
  (`Polynomial.eq_of_infinite_eval_eq` + `Set.Ioo_infinite`).
- `not_single_poly_of_pieces_ne` (contrapositive — the mathematical core of the falsification):
  **`P₁ ≠ P₂` ⇒ no single polynomial `Q` exists on `(0,R)`.** Instantiated at the measured witness
  (`P₁ = 1.111·r` vs `P₂ = −1.281 + 1.189r + 0.203r² + 0.0447r⁴`) this gives: for an unlike pair there
  is **no** single `P_ij` as [LN] Eq (101) asserts. At λ=0 (like pair) there is no interior breakpoint,
  the obstruction is vacuous, and Eq (101) is correct — which is why N=1 Tang/FMSA_pure works.

**The original `residue_is_polynomial` is kept** (it *is* true, and has no consumers); its docstring has
been made honest: the sentence "the content here is that the same `P` works on both sides of every
breakpoint" was removed (that *is* the hypothesis `hdecomp`, an **input**), and replaced by an explicit
CONDITIONAL flag + the fact that `hdecomp` is false for unlike pairs + the note that its claim to license
`_update_polycorr` does not follow.

**Original diagnosis (kept for the record):**

⚠ **Original status: vacuous + hypothesis likely false.**

**(a) Vacuous (same pattern as GAP.8).** `residue_is_polynomial` puts all of its content into the
hypothesis `hdecomp`:
`c1_inner r = (term_I r + P.eval r) * prefac r + c_hs r + X.mediated r i j`,
i.e. it *already assumes* that a **single** `P` (deg ≤ 4) works on **all** of `(0, R_ij)`; the conclusion
`∃ Q, …` then takes `Q := P` and closes by `ring`. The earlier claim "**the content here is that the same
`P` works on both sides of every breakpoint**" does not hold — that *is* `hdecomp`, an **input**, not
something proved. `c1_inner/c_hs/term_I/prefac` are arbitrary functions, so the theorem says **nothing**
about any physical object.

**(b) The hypothesis is false for unlike pairs.** The shipped, validated `fmsa_double_prop` closed form
(2YK) shows the unlike pair (0,1) inner core has **different polynomials on the two sides of `λ_ij`**
(`(0,λ)`: `1.111·r`; `(λ,R)`: degree 4 with nonzero constant); only like pairs (λ=0) are single-piece.
This is the opposite of what this task's title claimed ("no piecewise split … at the `c_HS` kink
`|λ_ij|`"). See `proof_notes_mixture_dcf.md` Group MPOLY (MPOLY.4/MPOLY.5) for the full falsification
record, and `not_single_poly_of_pieces_ne` above for the rigidity that makes it conclusive.

**(c) Impact.** This task was cited as licensing `oz_numerical._update_polycorr` to run a **single** GAP.8
moment inversion over the whole inner region — that licence is **not established** (and GAP.8 is itself
vacuous). The chain `GAP.5 → IB.4 (assumed) → _update_polycorr → GAP.8 (vacuous)` is assumption, not proof.
What would be needed: prove (or refute) that the physical `c1_inner` actually satisfies `hdecomp`.

---

### Task IB.5 — The activation conditions are satisfiable (sharpness)

**Statement:** ternary σ = [1, 4, 8] with intermediate pair `(a,b) = (0,1)` and target `j = 2`:
```
(A)  2·σ₀ + σ₁ = 2·1 + 4 = 6 < 8 = σ₂          ✓
(B)  σ₂ = 8 < 12 = 3·σ₁                        ✓
     r* = R[0,1] + R[0,0] = 2.5 + 1 = 3.5 < 4.5 = R[0,2]
```

**Why it matters:** without a witness, IB.3's characterisation could be read as vacuously
"always zero" — a theory that never activates would be uninteresting *and* would mean the whole
mediated machinery in `_compute_mediated` is dead code. IB.5 shows the conditions are
genuinely reachable, so IB.3's hypothesis has real content.

This is the Tern148 block of `verify_mediated_breakpoints.py`, where mediated is confirmed
nonzero for pairs (0,2), (1,2), (2,2) at `r* = 3.3859 / 4.8370 / 6.7717` (BH-corrected σ).

**Out of scope (numerical only):** that mediated is *strictly positive* just above `r*`. That
depends on the signs of the `b_grow` poles/coefficients from the converged Q-matrix, so it does
not follow from `σ > 0` and is deliberately **not** formalized — see the "Numerically verified"
table in `todo_lean.md`. The Lean side proves only the vanishing half (IB.2).

**Lean:** `ternary_148_active`, `InnerDecomp.lean` (`norm_num` on `σ = ![1,4,8]`).
**Depends on:** IB.3 (definitions of A/B).
**Status:** ✓ DONE, no `sorry`.

---

### Tasks IB.6–IB.8 — Inner-core breakpoint follow-ons (the second mediated knot `r**`)

**Motivation — from the 2026-07-14 stepwise-breakpoint pass** (`todo/to_Lean.md`,
`verify_stepwise_breakpoints.py`, `numerical_notes/{theory,results}/stepwise_breakpoints.md`).
IB.1–IB.5 characterized the *first* mediated knot `r* = R[a,b] + R[i,a]` (where Term IV's
integration window **opens**). But the window's lower limit `u_lo_eff = max(c_exp, u_lo_bj)` also
**switches form** once the moving bound `u_lo_bj(r) = r + (d_j − 3d_b)/2` overtakes the constant
`c_exp = r*`. That crossing is a *second* breakpoint

  `r** = r* + (3·d_b − d_j) / 2`

and the complete inner-core stepwise-poly breakpoint set is `{λ_ij, r*, r**}`.

Notation (as in IB.1–IB.5 / `_compute_mediated`): `d_k = fmsa.sigma[k]` (BH diameters),
`R[k,l] = (d_k+d_l)/2`, `λ_ij[k,l] = (d_l−d_k)/2`. Each task mirrors `_compute_mediated`
line-by-line and is provable from `d_k > 0` plus the stated Conditions alone — no axiom, no
numerical input — exactly as IB.1–IB.5.

**Scope decision (settled 2026-07-14).** The production solver is OZ-DIIS (non-perturbative,
all-order in ρ), which *perturbatively* would add higher-order knots at ≥3-contact-distance sums
`R[i,a]+R[a,b]+R[b,c]`. A dedicated pass (`verify_oz_breakpoints.py`,
`numerical_notes/{theory,results}/oz_breakpoints.md`) showed these are **numerically negligible**:
the OZ-converged inner-core residue `r·(c − yuk − c_hs − med)` is a single polynomial to
rel_err ≤ 2e-3 with no grid-stable, density-independent extra knot (large-σ mixtures — the only
ones with higher-order mediation — are packing-limited to low ρ*, suppressing the amplitudes).
So `{λ_ij, r*, r**}` is the operative set; the higher-order OZ knots are **explicitly not a Lean
target** (no clean, non-vacuous `d_k>0` statement). Cite the numerical note if it resurfaces.

---

### Task IB.6 — `r**` switch identity: `qP(u_lo_bj) = 0` ⇒ no slope jump at `r**`

**Statement (land first — pure ring identity):** the b–j quadratic coefficients built by
`_compute_mediated` (lines 1090–1092)
```
qP2 = −C·½·Qpp[j],  qP1 = −C·(−Q0[b,j] − Qpp[j]·u_lo_bj),  qP0 = −C·(Q0[b,j]·u_lo_bj + ½·Qpp[j]·u_lo_bj²)
```
satisfy, when the quadratic is evaluated at `u = u_lo_bj`,
```
qP0 + qP1·u_lo_bj + qP2·u_lo_bj² = −C·Qpp[j]·u_lo_bj²·(½ − 1 + ½) = 0.
```
A pure `ring` identity in `u_lo_bj, Q0[b,j], Qpp[j], C`. This is the Term-IV analog of IB.2's
`Δ_ai = −R[i,a]` (there for the a–i edge; here for the b–j moving edge).

**Corollary (C¹ at `r**`, second lemma):** at the crossover `u_lo_bj = c_exp` the integrand
vanishes on the moving boundary, so the boundary term `−F(u_lo_bj, r)·(d u_lo_bj/dr)` in
`d/dr mediated` is `0` — value **and** slope are continuous across `r**`.

**Out of scope:** the stronger empirical fact that curvature is *also* continuous (cubic branch
difference `D(r) ∝ (r−r**)³`) depends on the a–i integrand double-zero and is left numerical
(`verify_stepwise_breakpoints.py`: switch residual ≤ 9e-16) unless a clean statement emerges.

**Key factorization (makes the C¹ corollary a ring identity):** `ivIntegrand u = qP(u)·(Ak·exp(z·u)
+ p(u))` — the polynomial part of `ivIntegrand` is exactly the convolution `p(u)·qP(u)`. So
`qP(u_lo_bj) = 0` forces the *whole* integrand to vanish at the moving boundary, hence the Leibniz
boundary term `−ivIntegrand(u_lo_bj)·(d u_lo_bj/dr)` in `d/dr mediated` is `0`. No slope jump ⇒ **C¹**.

**Lean:** `qP_at_uLo_zero` (the `½−1+½=0` ring identity) and `ivIntegrand_at_uLo_zero`
(`ivIntegrand r i j a b k (u_lo_bj) = 0` via the factorization above), `InnerDecomp.lean`.
**Depends on:** IB.2 (Term IV geometry, `u_lo_bj`/`c_exp` definitions).
**Status:** ✓ DONE (2026-07-15), axiom-clean. The two ring identities are the provable C¹ core; the
*full* Leibniz-rule differentiability of `mediated` across `r**` and the curvature continuity stay
out of scope / numerical (as noted above).

---

### Task IB.7 — `r**` interior ⟺ Condition C (`d_a + 2·d_b < d_j`); and `C ⟹ A`

**Statement:** substituting `r* = R[a,b]+R[i,a]` and `r** = r* + (3d_b − d_j)/2` into
`r** < R_ij = (d_i+d_j)/2`:
```
d_a + (4d_b + d_i − d_j)/2 < (d_i + d_j)/2  ⟺  2d_a + 4d_b < 2d_j  ⟺  d_a + 2d_b < d_j    (Condition C)
```
So both mediated knots lie interior to `(0, R_ij)` exactly when `d_a + 2d_b < d_j < 3d_b`
(C ∧ B). Moreover **C ∧ B ⟹ A** *unconditionally*: `d_a + 2d_b < d_j < 3d_b` gives `d_a < d_b`, so
`2d_a + d_b < d_a + 2d_b < d_j` (= A) — whenever `r**` is interior *and* the window is nonempty,
`r*` is interior too. (`linarith` finds it as the nonneg combination `2·h_C + h_B`.)

Pure diameter arithmetic — `linarith` after unfolding, once `r*`/`r**` are in terms of `d_k`.
For σ=[1,4,8], `r**` lands *outside* the core (needs a stronger size split); first interior at
e.g. σ=[1,2,5.5] (see results note).

**Lean:** `rstarstar_interior_iff_C` and `condC_activeB_imp_activeA`, `InnerDecomp.lean`.
**Depends on:** the `rstarstar`/`CondC` defs; nothing beyond `d_k` arithmetic — no IB.3 needed, since
`C ∧ B` gives `d_a < d_b` directly.
**Status:** ✓ DONE (2026-07-15), axiom-clean. Both `linarith`.

---

### Task IB.8 — Mediated knot completeness: only `r*` and (if C) `r**`

**Statement:** under A∧B, the `(a,b)` sub-term of Term IV changes analytic form on `(0, R_ij)`
**only** at `r*` (window opens, `u_lo_eff = c_exp` first ≤ `u_hi_eff`) and, if C holds, at `r**`
(lower-limit switch). No third knot.

**Proof sketch:** the *upper* limit never switches. Under A∧B, `d_b < d_j` (IB.3), so
`λ_ij[b,j] = (d_j − d_b)/2 > 0`, giving `u_hi_bj = r + λ_ij[b,j] > r`, hence
`u_hi_eff = min(r, u_hi_bj) = r` for all `r` — unconditionally. The only moving boundary is the
lower one (IB.6/IB.7). Combined with the single-piece q-factors (each `q_ai`, `q_bj` is one
polynomial×exp on the relevant range), the sub-term's closed form can only change where the lower
limit changes: `r*` and `r**`.

**Lean:** `uHiEff_eq_r` (`σ_b < σ_j ⇒ u_hi_eff = r`, by `min_eq_left`) and `uHiEff_eq_r_of_active`
(under A∧B, via `active_pair_size_chain`), `InnerDecomp.lean`.
**Depends on:** IB.3's `active_pair_size_chain` (for the activated form).
**Status:** ✓ DONE (2026-07-15), axiom-clean. `u_hi_eff = r` (upper limit pinned) is the provable
core; the "no third knot" completeness is its interpretation.

---

### Task IB.9 — *(optional)* The first-order **DCF** has only the `λ_ij` knot — mediated `r*` add none, for all N

*New 2026-07-17, from `numerical_notes/results/FMSA_dp_stepwise_breakpoints.md` (`fmsa_double_prop.py`
`closed_form_pieces`/`get_c1_inner`/`get_c1_exact`). The DCF-side complement to IB.6–IB.8: the
mediated breakpoints that are real for the stepwise-poly decomposition / RDF do **not** appear in the
exact first-order DCF.*

**Statement.** For the exact first-order MSA DCF `r·c^(1)_ij(r) = 𝒲_ij(r) − 𝒲_ij(−r)`
(`𝒲 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ`, Group MRS), on the open core `(0, R_ij)`, for **every** N and set of diameters:

> The only interior breakpoint of `c^(1)_ij` is the pair's own `λ_ij = |d_i − d_j|/2` — unlike pairs
> have **exactly one** (C¹: value + slope continuous, curvature jumps); **like pairs have none** (a
> single analytic piece on all of `(0, R_ii)`, even the largest species where a mediated `r*` is
> geometrically interior). Neither the mediated points `r* = R[a,b]+R[i,a]` (up to 3 distinct interior
> per pair) nor the intermediate-species distances `λ_im, R_im` (m≠i,j) ever appear: the raw `𝒲_ij`
> support-edge set is always exactly `{±λ_ij, ±R_ij}`. Two propagations do **not** smear breakpoints
> across pairs. ⇒ **piece count ≤ 4 for every pair, every N**.

**Why (support geometry, not cancellation).** `c^(1)` is built from the **same** `q_ij` Baxter
kernels (support `[λ_ij, R_ij]`, the Lebowitz/Baxter HS structure) convolved with the Yukawa `ℬ`
(support `[R_mn, ∞)`). The cross-species mediated triple convolution `Σ_{m,n} P_im ⋆ ℬ_mn ⋆ P_jn` (the
only N≥3-specific term) has interior-facing edges that either land at `|r| ≥ R_ij` (outside the core)
or are removable (adjacent pieces share coefficients and merge): it shifts polynomial-piece *values*
but adds no *knot*.

**Relation to IB.6–IB.8.** Complementary, not contradictory. IB.6–IB.8's `r*`/`r**` are real for the
`_compute_mediated` stepwise-poly decomposition (cubic/C² onset, verified in `mediated_breakpoints.md`)
and for the RDF `h₁`; IB.9 says the exact first-order DCF does not inherit them. This is the DCF/RDF
dividing line of (★)/Group MRS (`todo/to_Lean.md` §1).

**Numerical status.** Two independent computations (real-space triple convolution vs k-space QAWF
`get_c1_exact`) agree to ~10⁻¹¹. Ternaries [1,2,4]/[1,4,8]/[1,2,5.5] (mediated `r*` chosen distinct
from `λ_ij`): every unlike pair has exactly one interior knot = `λ_ij`; every like pair none. Direct
smoothness test: 1st/2nd-deriv jumps at every mediated `r*` sit at the 10⁻¹²/10⁻⁶ noise floor (C^∞);
at `λ_ij` the 2nd-deriv jump is ~10⁻²–10⁻¹ (C¹ knot). Includes the decisive large-like-pair case
([1,4,8] (2,2), interior `r*` at 5.50/7.00): still a single smooth piece.

**Proof route (Lean).** Support-geometry + reflection, **not** the hard cancellation it first looks
like: convolving a kernel supported on `[λ_ij, R_ij]` with an exponential on `[R_mn, ∞)` and reflecting
into `(0, R_ij)` preserves the `{λ_ij, R_ij}` edge set and adds no interior knot; the N≥3 content is
specifically that the cross-species mediated convolutions add nothing. Reuses Group MRS's real-space
Baxter infra (`q0_poly`/`phi_real`); `px_convolve`'s breakpoint bookkeeping in `fmsa_double_prop.py`
is the concrete model. **Effort:** medium (support-edge bookkeeping).

**Depends on.** Group MRS (the `𝒲_ij` closed form), IB.1–IB.3 (mediated structure), the HS
Lebowitz/Baxter piecewise-cubic breakpoint set.

**Status.** ✓ **FULLY CLOSED for GENERAL N (2026-07-19, axiom-clean, sorry-free):** support geometry
(all N) + N=1 `innerDCF_N1_contDiffOn` + **general-N `dcfOdd_contDiffOn_upper`/`_lower`/`_like`** (only
interior knot is `λ_ij`, every N, every pair — mechanical term-by-term, NO cancellation). —
`LeanCode/YukawaDCF/MixtureConvolution.lean`
(axiom-clean, sorry-free, ns `FMSA.MixtureConvolution`, imports only the stable `WHSupports`/`Mix`
interfaces — **not** the actively-developed `MixtureRealSpace.lean`). Kernels `bMixEntry` (`ℬ_mn` on
`[R_mn,∞)`) and `pMixEntry` (reflected `𝒬⁻` on `[−R_im,−λ_im]`) with `Function.support ⊆ …` lemmas;
mediated two-fold `bConvP` (`ℬ_in⋆P_jn`) and triple `pbpConv` (`P_im⋆ℬ_mn⋆P_jn`) with their
`*_support_subset` lemmas via Mathlib `support_convolution_subset` + Minkowski helpers
`Ici_add_Icc_subset`/`Icc_add_Ici_subset`.

**The full support-geometry claim is CLOSED — `pbp_breakpoints_subset` + the four edge identities
`pbp_edge_eq`/`pbp_edge_lu`/`pbp_edge_ul`/`pbp_edge_uu`.**  The triple `P_im ⋆ ℬ_mn ⋆ P_jn` is
piecewise with breakpoints at the four sums `{−R_im,−λ_im} + {R_mn} + {−R_jn,−λ_jn}`, and **all four
evaluate to the `m,n`-free set `{−R_ij, −λ_ij, λ_ij, R_ij}`** — the intermediate species cancel out
of *every* one (contact algebra `R_ab=(σ_a+σ_b)/2`).  So `r* = R[a,b]+R[i,a]` — an `m,n`-dependent
quantity — is **not a DCF breakpoint at all**; it is a breakpoint of the *stepwise-poly*
decomposition (IB.6–IB.8), which the DCF does not inherit.  On the open core `(0,R_ij)` only `λ_ij`
survives (`−R_ij,−λ_ij ≤ 0`; `R_ij` is the boundary).  Plus `eq_zero_on_core_of_edge_ge`
(start `≥ R_ij` ⇒ vanishes on the core) for the outer-region terms.

**⚠ Correction (2026-07-18).**  An earlier note here claimed `r*` is an interior piece-edge that
needs a "coefficient-merging" cancellation.  That was **wrong**: computing *all four* triple
breakpoints (not just the support start) shows `r*` is never among them — it cancels structurally.
Pure support geometry closes IB.9, exactly as the original proof note asserted ("support geometry,
*not* the hard cancellation it first looks like").

**Analytic half — N=1 DCF smoothness FULLY CLOSED (2026-07-18), `LeanCode/YukawaDCF/MixtureDCFSmooth.lean`
(axiom-clean, sorry-free).**  Headline `innerDCF_N1_contDiffOn`:

> For the one-component fluid, `fun r ↦ −bConvP(r) − (P⋆ℬ)(r) + pbpConv(r) − pbpConv(−r)`
> (`= 2π√(ρ²)·r·c₁(r)` on the core, by `MixtureClosedForm.innerDCF_N1_oddPart`) is
> `ContDiffOn ℝ ⊤ (Set.Ioo 0 (X.R 0 0))`.  Since N=1 forces `λ_00 = 0`, the breakpoint set `{±λ,±R}`
> reduces to `{0, ±R}` and NONE lie in the open core ⇒ the inner DCF has **no interior knot** — the
> numerically observed `C^∞` core, proved.

Atoms/terms (all axiom-clean):
- `expQuadClosed_outer_eq` — the **outer**-region per-pole term collapses to a **pure exponential**
  `K·e^{−zy}` (the `y`, `y²` coefficients cancel identically): the companion to
  `MixtureClosedForm.expQuadClosed_decomp` (aligned region) that the terminated MRS session had not
  supplied; `outer_perpole_integral` closes `∫ P·(outer term)` via `integral_quadratic_exppos_conv`.
- `expQuadClosed_contDiff` / `expQuadClosedPos_contDiff` — every closed-form atom is `ContDiff ℝ ⊤`
  (`fun_prop` after unfolding); this is the "poly+exp ⇒ analytic" engine.
- **`bConvP_contDiffOn` / `pConvB_contDiffOn`** — the `ℬ⋆P` and `P⋆ℬ` DCF terms are
  `ContDiffOn ℝ ⊤ (Ioo 0 R_00)` (via their closed forms + `expQuadClosed_contDiff`).
- **`pbpConv_pos_contDiffOn` / `pbpConv_neg_contDiffOn`** — the two triple `P⋆ℬ⋆P` terms.

**How the `pbpConv(±r)` gate was discharged — piecewise INTEGRABILITY, not continuity.**  `pbpConv`'s
value is `pbpConv_eq_intervalIntegral`, whose hypothesis `hint` is `bConvP`-interval-integrability.
The earlier note feared this needed `bConvP` *continuity* (which Mathlib's convolution-continuity
lemmas cannot give — both `bMixEntry`/`pMixEntry` are discontinuous).  **That fear was misplaced: only
integrability is needed, and integrability is piecewise.**  Split at the jump `t₀ = x−R`; on each half
`bConvP(x−t)` *equals a continuous closed form* (outer on `[−R, x−R]`, aligned on `[x−R, 0]`), so each
half's integrand is continuous ⇒ integrable, and `IntervalIntegrable.trans` glues them
(`pbpIntegrand_intervalIntegrable`).  The jump at `t₀` is irrelevant to a Lebesgue integral — this is
the "piecewise gluing", but applied to integrability, which is far cleaner than continuity and needs
neither closed-form matching at `R` nor `bConvP(0)=0`.  With `hint` in hand, `pbpConv(r)` splits into
outer (`Σ_q outerPerPoleVal`, via `outer_perpole_integral`) + aligned (`Σ_q alignedPerPoleVal`, via
`aligned_perpole_integral`) halves — a finite `poly+exp` in `r`, `ContDiff` by `fun_prop`
(`pbpConv_pos_contDiffOn`).  For `pbpConv(−r)` the `[−r,0]` piece vanishes by support (`−r−t<0` below
`[0,∞)`), leaving only the aligned window ⇒ same conclusion (`pbpConv_neg_contDiffOn`).  The
`C¹`-vs-jump at `λ_ij` vs `C^∞` at `R_ij` is then the same closed form read at the edge (`q0MixEntry`
jumps at `λ_ij`, vanishes at `R_ij` — `q0Mix_quad_at_R`).

**General-N — FULLY CLOSED (2026-07-19), `LeanCode/YukawaDCF/MixtureDCFSmooth.lean` (axiom-clean).**
The N=1 restriction was lifted: for **every** `N` and **every** species pair `(i,j)` (`0 ≤ λ_ij`, WLOG
by `c_ij = c_ji`), the inner DCF `dcfOdd X i j = Wmix(x) − Wmix(−x)` (with the real-space matrix entry
`Wmix X i j = ℬ_ij − Σ_n ℬ_in⋆P_jn − Σ_m P_im⋆ℬ_mj + Σ_{m,n} P_im⋆ℬ_mn⋆P_jn`) is:
- `dcfOdd_contDiffOn_upper` — `ContDiffOn ℝ ⊤` on `(λ_ij, R_ij)`;
- `dcfOdd_contDiffOn_lower` — `ContDiffOn ℝ ⊤` on `(0, λ_ij)`;
- `dcfOdd_contDiffOn_like` — like pairs (`λ_ii = 0`) smooth on the WHOLE core `(0, R_ii)`.

Together: **the only possible interior knot of `c^(1)_ij` on `(0, R_ij)` is `λ_ij`, for all `N`** — the
numerically-observed "only λ_ij" knot, proved.

**⚠ Correction (2026-07-19) — NO aggregate cancellation is needed; general-N is a mechanical term-by-
term extension.**  An intermediate worry that the mediated two-fold breakpoint `R_in − λ_jn` was an
`n`-dependent interior knot requiring a Baxter-factorization cancellation was a **SIGN ERROR** (used
`|λ|` instead of the signed `Mix.lam k l = (σ_l − σ_k)/2`).  With the correct sign, `R_in − λ_jn = R_ij`
**identically** (`R_sub_lam_eq`, `simp [Mix.R, Mix.lam]; ring`) — so every term's breakpoints are
exactly `{±λ_ij, ±R_ij}`, `m,n`-free, term-by-term.  Confirmed numerically: the individual term
`ℬ_01⋆P_21` for the ternary `[1,2,4]` pair `(0,2)` is a single smooth piece on `(−λ_ij, R_ij)` (no knot
at the phantom `0.5`).  Consequences: on `(λ_ij, R_ij)` the reflected two-fold terms vanish by support,
leaving `−Σℬ⋆P − ΣP⋆ℬ + ΣpbpConv(r) − ΣpbpConv(−r)`; on `(0, λ_ij)` the forward `P⋆ℬ` and both `ℬ_ij`
vanish and the whole `P_im`-window is aligned, so `pbpConv(±x)` and the reflected `ℬ⋆P(−x)` are single
`Σ_q alignedPerPoleVal` pieces (`pbpConv_contDiffOn_midAligned`, reused via `.mono` forward and
`.comp Neg.neg` reflected).  Engine: general-index `bConvP_contDiffOn_aligned` / `pConvB_contDiffOn_aligned`
(two-fold) + `pbpConv_forward_contDiffOn` / `pbpConv_reflected_contDiffOn` (triple, outer+aligned split
at `t* = x − R_mj`) + `bConvP_eq_zero_of_lt`/`pConvB_eq_zero_of_lt`/`bMixEntry_eq_zero_of_lt` (support).

**Scope note (superseded).** The earlier "only N=1 formalized" claim is now obsolete — both subintervals
are formalized for general `N` via the same index-general atoms; only the frozen `innerDCF_N1_oddPart`
(N=1 odd-part reduction) remains N=1, but `Wmix`/`dcfOdd` give the general-N object directly.

**Corollary — `c_total` smoothness at `λ_ij` depends on the HS reference (cf. OZ.18/OZ.19).** `c^(1)`
is C¹ at `λ_ij`; `c^HS-PY` is C¹ (slope continuous); `c^HS-FMT` has a C⁰ kink (slope jump ≈ +0.1). So
`c_total(hs_ref='py')` is **C¹** at `λ_ij`, `c_total(hs_ref='fmt')` is **C⁰** — the `c_total` kink is
entirely the FMT weight-convolution corner (OZ.18/OZ.19), not the Yukawa first-order part.
