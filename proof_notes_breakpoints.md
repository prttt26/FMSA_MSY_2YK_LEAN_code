# Proof Notes: Inner-Core Mediated Breakpoints (Group IB)

Proof records for **Group IB** — the mediated inner-core breakpoint structure of the FMSA
mixture DCF. Split out of [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) (2026-07-15)
once it outgrew that file; see [todo_lean.md](todo_lean.md) for the status index.

**Source:** the Python `_compute_mediated` / `get_HS_FMT` in `fmsa_ga_matrix_mix.py`, and the
numerical passes `verify_mediated_breakpoints.py` / `verify_stepwise_breakpoints.py`.

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

The optional hard-sphere `λ_ij` kink (formerly B.19) moved to **Group OZ as OZ.18** — see
[proof_notes_hard_sphere.md](proof_notes_hard_sphere.md).

---

### Tasks IB.1–IB.5 — Inner DCF decomposition: mediated vanishing, Term IV breakpoints, domain of `P_ij`

**Motivation — new tasks, discovered from the numerical (Python) session, not from [chsY]/[LN]
directly.** B.5–B.10 establish `P_ij`'s degree and coefficients via the B.8 Laplace-moment
inversion, but leave open what `P_ij`'s actual *domain* is once cross-species "mediated"
contributions are accounted for. This surfaced as a real formalization gap during the Group Z
numerical work: specifically the `_update_polycorr` fix that subtracts `c_HS` (`get_HS_FMT`)
and `mediated` (`_compute_mediated`) from the OZ-converged inner DCF *before* running the B.8
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
`Term_I` is pure-exponential, `P_ij(r) = p₀+p₁r+p₂r²+p₃r³+p₄r⁴` (degree ≤ 4, B.5/B.8),
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
2026-07-15 when this group split off from Group B).

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

**Why it matters:** this is what licenses `oz_numerical._update_polycorr` to run a *single* B.8
moment inversion over the whole inner region after subtracting `get_HS_FMT` and
`_compute_mediated`. `P_ij` is piecewise only if mediated is left *in*; once it is subtracted
exactly (rather than approximated), the sole source of a breakpoint at `r*` is gone.

**Proof:** algebra from the decomposition hypothesis plus `prefac ≠ 0` (`field_simp`); the degree
bound is imported from B.5 (`b5_degree_bound`, `B5MixturePoly.lean`), not re-derived.

**Lean:** `residue_is_polynomial`, `InnerDecomp.lean`.
**Depends on:** B.5 (degree bound), IB.3 (so the `mediated` being subtracted is characterized).
**Status:** ✓ DONE.

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

