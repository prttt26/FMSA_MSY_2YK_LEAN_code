# Lean Proof Tasks: FMSA Yukawa Mixture Theory

This file is the **status index** for all Lean 4 + Mathlib proofs in `LeanCode/`.
Detailed proof records (statements, proof sketches, pitfalls, Lean API notes) are in:

- [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) — Groups 2, 3, OZ (pure HS foundations)
- [proof_notes_baxter.md](proof_notes_baxter.md) — Group BAXTER (Baxter Q-factor, Wiener–Hopf
  route to the PY closed form; depends on Group OZ, split off once it outgrew
  `proof_notes_hard_sphere.md`)
- [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) — Groups 1, 4, B, C, 5 (Yukawa DCF derivation)
- [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) — Group M (multi-component Baxter Q̂₀ matrix
  identity + rank-2 det reduction + det-positivity monotonicity M.5–M.8; split from
  `proof_notes_yukawa_dcf.md` 2026-07-15)
- [proof_notes_breakpoints.md](proof_notes_breakpoints.md) — Group IB (inner-core mediated
  breakpoints; split from `proof_notes_yukawa_dcf.md` 2026-07-15 once it outgrew it)
- [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) — Group Y1 (first-order Yukawa RDF/DCF via
  Wiener–Hopf; the ε¹ analog of Group BAXTER, split off 2026-07-15 for the concrete-C.5 derivation)
- [proof_notes_failures.md](proof_notes_failures.md) — Groups chsY, P, GA (method-failure analysis)
- [proof_notes_free_energy.md](proof_notes_free_energy.md) — Groups F, FW (free energy integrals; White-Bear FMT/BMCSL)

**Source markers:**
- **[chsY]** — `pdf/FMSA_chsY.pdf` (analytical multi-species MSA solution)
- **[LN]** — `pdf/lecture_notes_OZ_Yukawa_poly.pdf`

---

## Open / Unfinished Items

### Sorries — actual `sorry` proof terms in source files

| Sorry | File | Task | What remains |
|-------|------|------|--------------|

### Axioms — `axiom` declarations assumed without proof

| Axiom | File | Task | Physical meaning / proof path |
|-------|------|------|-------------------------------|
| `oz_fixed_pt_unique` | `HardSphere/PYOZ_GHS.lean` | OZ.10 | OZ fixed point uniqueness. Dilute case (`eta<1`, `24·eta·bracket<1`) now a real theorem, `oz_fixed_pt_unique_dilute` (`HardSphere/OzFixedPtDilute.lean`, no axiom). Mid/high density is **TRUE** (hard spheres have no spinodal, so `1−ρĉ(k)>0 ∀k` and `1∉spectrum(K)=symbol range⊂(−∞,1)`) — but **not** provable via compact Fredholm: `oz_linear_op` (K) is a *non-compact* half-line Wiener–Hopf operator (asymptotic multiplier `−24η·bracket` = spectral radius = dilute threshold). Mathlib *has* compact Fredholm (`FredholmAlternative.lean`), it just doesn't apply. No general Wiener–Hopf theory needed either: the factorization is already the **Baxter factorization** (BAXTER.3); the missing piece is BAXTER.12–13's explicit `h_explicit` inverse ⇒ **same-core as, gated by, the BAXTER line**. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.10. |
| `oz_core_closure` | `HardSphere/PYOZ_GHS.lean` | OZ.9a | PY core closure (Baxter/Wertheim). Numerically verified; a genuine Lean proof needs Group BAXTER's full residue-series construction (`BAXTER.9`–`13`, staged, not yet attempted) — see [proof_notes_baxter.md](proof_notes_baxter.md) Task `BAXTER.2`. |
| `oz_h_exterior_regularity` | `HardSphere/JumpAsymptotic.lean` | OZ.3 | Analytic regularity/decay/integrability of the OZ exterior solution `oz_h` on `[σ,∞)` (differentiable, `r·oz_h(r)→0` and integrable, convolution/sine-transform integrands integrable). **Replaced the old bare `g0_HS_contact_value` physical-number axiom** (2026-07-15): the specific PY contact value `(1+η/2)/(1-η)²` is now a *proved theorem* `g0_HS_contact_value` (`JumpAsymptotic.lean`, still namespace `FMSA.HardSphere`), derived from BAXTER.6/7 + OZ.9b + this regularity axiom. Strictly weaker epistemic content than the retired axiom — the number is derived, not assumed; only the analytic niceness of the (opaque `Classical.choose`-built) `oz_h` stays open. See [proof_notes_baxter.md](proof_notes_baxter.md) Task `BAXTER.8`. |

*(`radial_laplace_conv` and `oz_laplace_oz_eq` were **deleted** 2026-07-15, together with the theorems that only consumed them
See OZ.2/OZ.6/OZ.7 and [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md).)*

### Numerically verified — not proved in Lean

| Claim | File | Task | What's verified / what's missing |
|-------|------|------|-----------------------------------|
| PY core closure | `HardSphere/PYOZ_GHS.lean` (axiom `oz_core_closure`) | OZ.9a | Baxter/Wertheim result; numerically verified across state points, needs Group BAXTER's Wiener–Hopf/residue-series construction for a Lean proof. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.9 and [proof_notes_baxter.md](proof_notes_baxter.md) Task `BAXTER.2`. |
| `(1-M₀₀)(1-M₁₁) ≠ M₀₁·M₁₀` (`M := Vmat·Umat`) | `YukawaDCF/Q0DetRankTwo.lean`, explicit hypothesis on `Q0_mat_phys_isUnit_det_of_two_by_two` | M.4 | Rank-2 reduction leaves this one scalar inequality `(1+a)(1+d)>bc`; robust numerically (20 000 trials, `det ≥ 1` always). **`bc ≥ ad` now PROVED (M.8)** so it is *not* Cauchy–Schwarz-closable; residual gap is `O(ρ²) ≤ O(ρ)` under `η<1`. Recommended closure routes: (a) `det(z)` monotone-decreasing in z with `det(∞)=1` (numerically bulletproof); (b) sharp `a+d ≥ bc−ad`. Blocks M.3's unconditional `det(Q̂₀)≠0`. See [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) Tasks M.4–M.8. |
| `D_ij ≠ 0` for unlike pairs | `YukawaDCF/B5MixturePoly.lean` (theorem `b9_d_ij_nonzero_example`) | B.9 | Confirmed numerically: `verify_oz_solver.py` Check 4 gives `D_01 = -3295.03` for the canonical binary HSY state point (σ=[1.0,1.2], ρ*=0.5, T*=1.5) — clearly nonzero. The Lean theorem only proves existence of valid unlike-pair parameters, not `D≠0` for them; the actual inequality is unproved. See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) Task B.9. |

### Open tasks — not yet started

| Task | Title | Depends on | Notes |
|------|-------|-----------|-------|
| `BAXTER.14` | Rigorous `n^{1-2r/σ}` magnitude bound + concrete `h_explicit` instantiation (split out of `BAXTER.12`) | `BAXTER.12` (done except this) | `BAXTER.12`'s only remaining gap: `h_explicit_summable`'s magnitude-bound hypothesis is only heuristically (`Θ`-level) derived, not a rigorous two-sided Lean bound. Needs `Chat_complex(k_n)` magnitude bounds (from `Chat_F_formula`) combined with `G_baxter_deriv_ne_zero_of_large`/`G_baxter_neg_ne_zero_of_large`'s cubic bounds, evaluated at a concrete pole from `G_baxter_pole_family_exists`; likely related to discharging `BAXTER.11`'s own `hstep`. Blocks `BAXTER.13`. See [proof_notes_baxter.md](proof_notes_baxter.md) Task `BAXTER.14`. |
| `BAXTER.13` | `OzFixedPt` + uniqueness assembly (retires `oz_core_closure`) | `BAXTER.12`, `BAXTER.14` | Flagged as likely the largest remaining estimate in Group BAXTER: `oz_core_closure` is about the OZ convolution identity *inside* the hard core, and the only existing bridge (`oz_fourier_oz_eq_of_core_closure`) runs the wrong direction — needs a genuine new Fourier-inversion/contour-integration argument, no existing shortcut in the codebase. See [proof_notes_baxter.md](proof_notes_baxter.md) Task `BAXTER.13`. |
| **Group Y1** (Y1.1–Y1.7) | First-order Yukawa RDF/DCF via Wiener–Hopf ([LN] §5–§6) — the full concrete-C.5 derivation, promoted to its own group (ε¹ analog of Group BAXTER). Y1.1/Y1.2/Y1.5/Y1.6 + Y1.3a (WH support lemmas) done; remaining core Y1.3b (FT injectivity), re-routed off the Hilbert transform. | C.5 core + single-tail (done), B.2, M.3/M.4 | See the **Group Y1** table in Task Status below and [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md). |
| **Group Y2** (Y2.1–Y2.4) | N=2 mixture inner-core Mittag-Leffler closed form: exact B_k residue formula + infinitely many HS poles for det(Q̂₀). Y2.1–Y2.2 provable now from existing tools; Y2.3 hard; Y2.4 blocked on Y1.3. | Y1.1 (`inv_apply_eq_adj_div_det`), `residue_of_simple_pole` (done), M.3/M.4 | See the **Group Y2** table in Task Status below and [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md). |
| GA.2 (concrete) | Discharge GA.2's decay/limit hypotheses from the explicit N=2 `Q̂₀`: prove `\|Q̂₀_{01}(z)\| ≤ C·exp(−z·(σ₁−σ₀)/2)` and `det Q̂₀(z) → L ≠ 0` | GA.2 mechanism (done), B.2, M.3/M.4 | The decay mechanism (`g_mat_offdiag_decay`) is done; this ties it to the real N=2 cofactor. High effort (explicit B.2 entry + dominated exp-decay). See [proof_notes_failures.md](proof_notes_failures.md) Task GA.2. |


---

## Task Status

### Group 1 — Closed-Form Integral Identities *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 1.1 | I₁ antiderivative | ✓ DONE | `YukawaDCF/I1I2Integrals.lean` |
| 1.2 | I₂ antiderivative | ✓ DONE | `YukawaDCF/I1I2Integrals.lean` |
| 1.3 | I₁/I₂ vanish at ℓ=0 | ✓ DONE | `YukawaDCF/I1I2Integrals.lean` |

### Group 2 — Hard-Sphere Baxter Factor *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 2.1 | φ₁, φ₂ auxiliary formulas | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| 2.2 | det(s) non-vanishing | ✓ DONE | `HardSphere/BaxterFactor.lean` |

### Group 3 — Wiener–Hopf Structure *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 3.1 | B₁+D₁ = T_U identity | ✓ DONE | `HardSphere/Splitting.lean` |
| 3.2 | Support of T_S on (−∞, R_ij] | ✓ DONE | `HardSphere/Splitting.lean` |

### Group chsY — FMSA_chsY Formula Failure *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.3 | (1+A)² ≠ 1−g² — root cause of HSY spike | ✓ RESOLVED | `FMSAPoly/OriginCheck.lean` |

### Group 4 — Single-Component Reduction *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.1 | b_ij N=1 collapse formula | ✓ DONE | `YukawaDCF/BijReduction.lean` |
| 4.2 | g + a·exp(−z) = 1 | ✓ DONE | `YukawaDCF/SingleCompIdentity.lean` |
| 4.4 | Full N=1 reduction Eq.41→42 | ✓ DONE | `YukawaDCF/SingleCompReduction.lean` |

### Group M — Multi-Component Baxter Identity *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| M.1 | Abstract matrix identity Ĝ+Â·c=I | ✓ DONE | `YukawaDCF/MatrixIdentity.lean` |
| M.2 | N=1 limit: Ĝ₀₀=g, Â₀₀=a | ✓ DONE | `YukawaDCF/MatrixN1.lean` |
| M.3 | det(Q̂₀) ≠ 0 multi-component | ◑ conditional (old axiom disproved; see M.4) | `YukawaDCF/MatrixQ0.lean`, `YukawaDCF/Q0DetRankTwo.lean` |
| M.4 | Unconditional `det(Q0_mat_phys) ≠ 0` for all `z > 0` | ◑ conditional — rank-2 reduction done; one scalar inequality left as explicit hypothesis, robust numerically but not proved unconditionally; see Numerically verified section | `YukawaDCF/MatrixQ0.lean` |
| M.5 | `nAux_eq_mAux_div_two` (`nAux u = mAux u/2`) | ✓ DONE | `YukawaDCF/Q0DetRankTwo.lean` |
| M.6 | `one_add_half_sq_lt_cosh` (`1+u²/2 < cosh u` for `u>0`) | ✓ DONE | `YukawaDCF/Q0DetRankTwo.lean` |
| M.7 | `ratioPM_strictAntiOn` (`pAux/mAux` decreasing on `(0,∞)`) | ✓ DONE | `YukawaDCF/Q0DetRankTwo.lean` |
| M.8 | `moment_ad_le_bc` (**`bc ≥ ad`** for all N) | ✓ DONE | `YukawaDCF/Q0DetRankTwo.lean` |

**Group M note (2026-07-15).** **M.5–M.8 PROVED, axiom-clean** (`Q0DetRankTwo.lean`; migrated from
the M.4 det-positivity handoff, were M.4a–d): **M.5** `nAux_eq_mAux_div_two` (ring) ⇒
`g/f = πξ₂/(2vac)+z·pAux/mAux`; **M.6** `one_add_half_sq_lt_cosh` (via the `mAux_neg` derivative
chain); **M.7** `ratioPM_strictAntiOn` (Wronskian `eᵘW=u²−2cosh u+2 < 0` by M.6); **M.8**
`moment_ad_le_bc` — **`bc ≥ ad` for all N** (`gFun = fFun·(πξ₂/(2vac)+z·ratioPM)` + Cauchy–Binet
`ad−bc = ½∑ρρ(σₖ−σⱼ)(fⱼgₖ−fₖgⱼ) ≤ 0`), so it is *not* Cauchy–Schwarz-closable. Main `det>0` stays
**M.4** (`hdet` hypothesis). **New (2026-07-15):** `det(z)` is numerically **monotone decreasing in
z** with `det(∞)=1`, giving the clean route `det(z) > 1` (`verify_q0_det_positivity.py`
`monotone_in_z_scan`); the two Lean-tractable routes to close M.4 are (a) that monotonicity
(`det(∞)=1` + `d(det)/dz<0`) and (b) the sharp `a+d ≥ bc−ad`. Full records:
`proof_notes_matrix_q0.md` (Group M); analysis in `numerical_notes/{theory,results}/q0_det_positivity.md`.

### Group B — FMSA_GA_matrix_mix Algebraic Foundation and Polynomial Determination *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| B.1 | Shifted-exponent integral | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| B.2 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) | ✓ DONE | `YukawaDCF/QhatDecomposition.lean` |
| B.3 | Coefficient algebra (1−g²)−a²c²=2acg | ✓ DONE | `YukawaDCF/SingleCompIdentity.lean` |
| B.4 | Origin BC automatic for FMSA_GA_matrix_mix | ✓ DONE | `YukawaDCF/B4OriginBC.lean` |
| B.5 | Degree bound exisr: deg P_{ij} ≤ 4 (no r^n for n≥N with N=4) | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.6 | Origin uniqueness: only A_{ij}=−E_{ij}(0) forced at r=0 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.7 | No contact BC: B,C,D,E^{(4)} not fixed by r=R_{ij} | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.8 | Laurent extraction: all five coefficients from R_{ij}(s) at s=0 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.9 | D_{ij} generically nonzero for unlike pairs | ◑ weakened — numerically confirmed, not proved; see Numerically verified section | `YukawaDCF/B5MixturePoly.lean` |
| B.10 | Exact degree: natDegree P_{ij} = 4 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |

### Group IB — Inner-Core Mediated Breakpoints *(breakpoints)*

*Split out of Group B (2026-07-15) once the mediated inner-core breakpoint work outgrew it.
**IB.1–IB.8 were formerly B.11–B.18**; the old B.19 (hard-sphere `λ_ij` kink) moved to Group OZ as
**OZ.18** (it is FMT hard-sphere, outside the Yukawa mediated chain). The Lean identifiers in
`YukawaDCF/InnerDecomp.lean` were made **task-ID-free** (2026-07-15, e.g. `b11_…`→`terms_II_III_zero`),
so IB.* can be renumbered without touching Lean source. Proof records:
[proof_notes_breakpoints.md](proof_notes_breakpoints.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| IB.1 | Terms II+III ≡ 0 in the inner region (unconditional: `alpha = r−σ_a−R_ij < 0`) | ✓ DONE | `YukawaDCF/InnerDecomp.lean` |
| IB.2 | Term IV geometry: `Δ_ai = −R[i,a]` ⇒ `Alm=0`, `c_exp=d_exp=r*=R[a,b]+R[i,a]`; sub-term ≡ 0 below `r*` (unconditional) | ✓ DONE | `YukawaDCF/InnerDecomp.lean` |
| IB.3 | mediated ≡ 0 on `(0,R_ij)` when no `(a,b)` satisfies A∧B; **binary N=2 ⇒ mediated ≡ 0 for any σ** | ✓ DONE (both; size chain `σ_a<σ_b<σ_j` via `active_pair_size_chain`) | `YukawaDCF/InnerDecomp.lean` |
| IB.4 | Residue is a *single* degree-≤4 polynomial on `(0,R_ij)` after c_HS+mediated subtraction (no piecewise split at `r*`) | ✓ DONE | `YukawaDCF/InnerDecomp.lean` |
| IB.5 | Sharpness witness: σ=[1,4,8], `(a,b,j)=(0,1,2)` satisfies A∧B and `r* < R[0,2]` | ✓ DONE, no sorry (`ternary_148_active`) | `YukawaDCF/InnerDecomp.lean` |
| IB.6 | r** switch identity: `qP(u_lo_bj)=0` ⇒ integrand vanishes at moving boundary ⇒ C¹ at `r**=r*+(3d_b−d_j)/2` (no slope jump) | ✓ DONE (`qP_at_uLo_zero`, `ivIntegrand_at_uLo_zero`; full Leibniz-C¹ + curvature stay numerical) | `YukawaDCF/InnerDecomp.lean` |
| IB.7 | r** interior ⟺ Condition C (`d_a+2d_b<d_j`); `C ∧ B ⟹ A`; both mediated knots interior iff `d_a+2d_b<d_j<3d_b` | ✓ DONE (`rstarstar_interior_iff_C`, `condC_activeB_imp_activeA`) | `YukawaDCF/InnerDecomp.lean` |
| IB.8 | Mediated knot completeness: `u_hi_eff=r` under A∧B (upper limit never switches ⇒ only `r*`,`r**` knots) | ✓ DONE (`uHiEff_eq_r`, `uHiEff_eq_r_of_active`) | `YukawaDCF/InnerDecomp.lean` |

**IB.1 split note (2026-07-13, formerly B.11).** The old single B.11 (`sorry ×4`) was re-derived
against `verify_mediated_breakpoints.py` and split into IB.1–IB.5. The four old statements were
**vacuous**: each took its physical content as a hypothesis (`b11_mediated_zero_no_active_pair`'s
`hmedIV` *was* its own conclusion; `b11_termIV_activation` was unprovable — `mediated_IV` was an
unconstrained function and `hr_star_eq` was the tautology `X = X`). The rewritten file defines
`lam`/`alphaII`/`lstar`/`c_exp`/`u_lo_eff`/… as faithful mirrors of `_compute_mediated`
(`fmsa_ga_matrix_mix.py:705-857`), so the new statements have real content. Conditions A/B and the
breakpoint `r*` are now **derived** from `Δ_ai = −R[i,a]`, not assumed. All of IB.1–IB.5 are
provable from `σ > 0` alone (no axiom, no numerical input).

**IB.1–IB.5 proofs landed (2026-07-14).** All five theorems are proved, no `sorry`, axiom-clean
(only `propext`/`Classical.choice`/`Quot.sound`). IB.1 (`terms_II_III_zero`):
`alphaII_eq`/`alphaIII_eq` → `alpha<0` → `lstar_eq_zero_of_alpha_neg` → `I1cl_at_zero`/`I2cl_at_zero`
→ `Finset.sum_eq_zero` (+`simp`). IB.2 (`termIV_geometry_and_vanishing`): `Δ_ai=−R[i,a]` by `ring`;
`Alm=0`, `c_exp=d_exp=r*` via `max_eq_right`; vanishing by `if_pos` on the empty window
`u_hi_eff ≤ r ≤ c_exp ≤ u_lo_eff`. IB.3 (`mediated_zero_of_no_active_pair`/`binary_mediated_zero`):
case-split `not_and_or` on which of A/B fails — ¬A reduces to IB.2's window (`R[i,j] ≤ r*`), ¬B gives
`u_lo_bj ≥ r` directly; binary corollary by `fin_cases a b j` on `Fin 2` against the size chain.
IB.4 (`residue_is_polynomial`): `Q=P`, cancel via `mul_div_assoc`+`div_self hpf'`. Only the *strict
positivity* of mediated just above `r*` stays numerical (depends on `b_grow` pole/coeff signs, not
on `σ>0`).

**IB.6–IB.8 candidates (2026-07-14, formerly B.16–B.18).** From the stepwise-breakpoint handoff
`todo/to_Lean.md`. These extend the IB.1–IB.5 mediated family to the **second** mediated knot
`r** = r* + (3d_b − d_j)/2` (the lower-limit switch `c_exp → u_lo_bj`) and to per-sub-term knot
completeness. **DECISION recorded there:** the first-order set `{λ_ij, r*, r**}` is *exactly* the
breakpoint set the OZ stepwise-poly solver uses; higher-order OZ knots (≥3 contact-distance sums
`R[i,a]+R[a,b]+R[b,c]`) are numerically negligible (OZ inner-core residue is a single polynomial to
<0.2% at all accessible packing) and are **explicitly not a Lean target**. Each mirrors
`_compute_mediated` line-by-line as IB.1–IB.5 do and is provable from `d_k > 0` plus the stated
Conditions. IB.6's core is the ring identity `qP(u_lo_bj)=0` (analog of IB.2's `Δ_ai=−R[i,a]`);
IB.7 is diameter arithmetic; IB.8 rules out a third knot via `u_hi_eff=r` under A∧B. The old B.19
(FMT `λ_ij` slope kink from `get_HS_FMT`) is now **OZ.18** (hard-sphere, outside the Yukawa mediated
chain). Strict positivity / exact cubic onset order at `r*`/`r**` stays numerical
(`verify_stepwise_breakpoints.py`). Proof sketches in
[proof_notes_breakpoints.md](proof_notes_breakpoints.md).

### Group C — FMSA_GA_matrix_mix Consistency *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| C.1 | N=1: corrected formula = FMSA_pure | ✓ DONE | `YukawaDCF/SingleCompReduction.lean` |
| C.2 | N=1 like-pair inner formula bounded: `(1−G²₀₀)·exp(z(R−r))` ≤ C on (0,d) via exp-cancellation | ✓ DONE (`c1_n1_twoexp_bounded`) | `YukawaDCF/SingleCompReduction.lean` |
| C.5 | Leading Yukawa-pole residue of the first-order MSA amplitude. **CORRECTED:** exact single-tail residue is `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` (doubly-propagated), **not** `K·G` (the numerical shorthand is a leading-order approx; `K·G²` at N=1) | ◑ core (`c5_residue_eq_K_mul_Ginv`) + single-tail exact residue (`spectralAmp_residue`, `spectralAmp_residue_n1`) DONE; multi-tail + Wiener–Hopf derivation of `b_{ij}(s)` → **Group Y1** | `YukawaDCF/YukawaPoleResidue.lean`, `YukawaDCF/SpectralAmplitude.lean` |

**Group C note (2026-07-15).** C.2 and C.5 are the **positive** HS-pole residue results (from the
Route C session, `fmsa_hs_pole_residue.py` + `_build_pure_refs` fix): C.2 proves the like-pair
inner formula is bounded via the exp-cancellation (1−G²)·exp(z·(R−r)) = A₀₀·(D+S)/D²·exp(−z·r) ≤
const (using `R=d` and Task 4.2); C.5's exact single-tail Yukawa-pole residue is `Q̂₀⁻¹·K·Q̂₀⁻ᵀ`
(the numerical `K·G·exp` is a **leading-order approximation** — see the C.5 CORRECTION), so Route C's
inner formula is correct at leading order and the residual 2YK error is entirely in the outer `K₀₁`
values. The **failure** counterparts GA.1 (divergence + additive HS-pole correction insufficient) and
GA.2 (structural root cause `G_{01}→0`) moved to Group GA below. The **full first-order Yukawa
Wiener–Hopf derivation** behind C.5 is promoted to **Group Y1** (below). Full statements:
[proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) (Group C), [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) (Group Y1).

### Group Y1 — First-Order Yukawa RDF/DCF (Wiener–Hopf derivation) *(yukawa_wh)*

*The ε¹-order analog of Group BAXTER (same **algebraic** Wiener–Hopf machinery — causal/anti-causal
split + support + residues, **not** the Hilbert transform of [LN] §6.3 which Mathlib lacks; see Y1.3
— applied to the first-order OZ equation `H̃₁(I−C̃₀)=(I+H̃₀)C̃₁`). Split off 2026-07-15 as the full
concrete-C.5 derivation. Source: **[LN]** §5–§6. Records: [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md).*

| Task | Title ([LN] ref) | Status | Lean file |
|------|-------|--------|-----------|
| Y1.1 | Complex Baxter matrix `Q̂₀(s):ℂ→Matrix` (Eq. 10–13) + inverse-as-`adj/det` (Eq. 14) | ✓ DONE (`q0_entry_c`, `Q0_mat_c`, `q0_entry_c_real`, `inv_apply_eq_adj_div_det`); closed-form Eq. 14 deferred | `YukawaDCF/Q0Complex.lean` |
| Y1.2 | Outer MSA DCF Laplace transform `U₁(k)_{ij}=K_{ij}e^{−ikR_{ij}}/(ik+z_{ij})` (Eq. 34/46) + Yukawa pole at `k=iz_{ij}` | ✓ DONE (`integral_Ioi_cexp`, `outerDCF_transform`) | `YukawaDCF/OuterDCF.lean` |
| Y1.3 | Wiener–Hopf one-sided projection isolating `B₁={T_U}^{[R,∞)}` (Eq. 55–66) — **algebraic split + support + residues, NOT Hilbert transform** (Mathlib lacks it; mirror `Splitting.lean`/Group BAXTER). Split a/b/c | ◑ **Y1.3a DONE** (support lemmas: `q0_poly_support_subset`, `q0MixEntry`+`_support_subset`, `integral_{Iic,Ici}_eq_of_support`, `fourier_{Iic,Ici}_eq_full`); Y1.3b (FT injectivity, crux) + Y1.3c (residue id., ⊆`matrix_conj_residue`) ☐ | `YukawaDCF/WHSupports.lean` (Y1.3a); Y1.3c → `YukawaWienerHopf.lean` |
| Y1.4 | Residue evaluation of the WH projection → `B₁(k)` (§6.4.1, Eq. 63–67) | ◑ residue-theorem step DONE (`matrix_conj_residue`, `triple_apply`); Y1.3-dependent derivation of the Eq. 63 integrand deferred | `YukawaDCF/YukawaWienerHopf.lean` |
| Y1.5 | Spectral amplitude `b_{ij}(s)` four-term/multi-tail (Eq. 73) + tie `A` to `Q̂₀(s)⁻¹` | ✓ single-tail + multi-tail collapse DONE (`spectralAmp_residue`/`_n1`, `bMulti`, `bMulti_single_eq`, `bMulti_single_residue`, `simplePole_residue`); general distinct-`z` ☐ | `YukawaDCF/SpectralAmplitude.lean` |
| Y1.6 | First-order RDF `Ĥ₁=[Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (Eq. 68) + the exact C.5 residue corollary | ✓ DONE (`Hhat1`, `Hhat1_spec`, `Hhat1_residue`) | `YukawaDCF/YukawaWienerHopf.lean` |
| Y1.7 | *(opt.)* inner-core `S₁(k)` (§9) + contact matching (§7) — links to `P_ij` (Groups B/IB) | ☐ not started | new `YukawaDCF/…` |

**Group Y1 note (updated 2026-07-15).** Promoted from the single "C.5 (multi-tail / derivation)"
open-task row once the [LN] §6 derivation was read in full. Done: Y1.1, Y1.2, Y1.5 (single/multi-tail
collapse), Y1.6, and **Y1.3a** (WH support lemmas). Remaining analytic core: **Y1.3b** (FT injectivity
/ support-orthogonality) — re-routed off the Hilbert transform to the algebraic-split + support
method (mirrors `Splitting.lean` / Group BAXTER), building on the existing real-space infra
(`BaxterRealSpace.q0_poly`/`phi_real`, `InnerDecomp.Mix` `R`/`lam`/`mediated`). Already-proved
cross-links: `WHSupports.lean` (Y1.3a), `SpectralAmplitude.lean` (Y1.5 single-tail),
`YukawaPoleResidue.lean` (`g_entry_eq_adj_div_det`, `c5_residue_eq_K_mul_Ginv`),
`HardSphere/BaxterResidue.lean` (`residue_of_simple_pole`).

### Group Y2 — N=2 Mixture Inner-Core Closed Form (Mittag-Leffler) *(yukawa_wh)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| Y2.1 | Explicit 2×2 adjugate/det formulas for Q̂₀: `adj(Q̂₀)₀₁=−Q̂₀₀₁`, `[Q̂₀⁻¹]₀₁=−Q̂₀₀₁/det(Q̂₀)` | ☐ not started (trivial, Mathlib `Matrix.det_fin_two`/`adjugate_fin_two`) | extend `YukawaDCF/Q0Complex.lean` |
| Y2.2 | B_k residue formula: `Res_{s=s_k}[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` from `residue_of_simple_pole` + Y2.1 | ☐ not started (medium; compose existing tools) | new `YukawaDCF/MixtureHSPoles.lean` |
| Y2.3 | Infinitely many HS poles for N=2: `det(Q̂₀(s))=0` has infinitely many complex roots (analog of `BAXTER.11`) | ☐ not started (hard; quasi-polynomial analysis of 2×2 det) | `YukawaDCF/MixtureHSPoles.lean` |
| Y2.4 | Full inner-DCF Mittag-Leffler assembly: `c^{inner}_{01}(r) = [Yukawa poles] + Σ_k B_k·e^{−s_k·r}` | ☐ not started (very hard; blocked on Y1.3) | new `YukawaDCF/…` |

**Group Y2 note (2026-07-15).** Motivated by the observation that Q̂₀(z) and its 2×2 inverse
adj/det are fully algebraic (Y1.1 DONE), so the HS-pole residue B_k = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)
is provable without Y1.3, using only `residue_of_simple_pole` (DONE, `BaxterResidue.lean`).
This resolves the "no closed form for N=2" claim: the exact inner DCF IS a convergent
Mittag-Leffler series; the "transcendental" obstacle is only the pole *locations* s_k (roots of
det(Q̂₀)=0), not the residues. The N=2 det(Q̂₀) is an exponential polynomial in s (quasi-polynomial)
— the analog of `Qhat_complex` for N=1 (BAXTER.11 `Qhat_complex_zeros_infinite`). Full assembly
(Y2.4) needs Y1.3. See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) Group Y2.

### Group GA — FMSA_GA_matrix_mix Inner-Core Conditioning Failure *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| GA.1 | Unlike-pair two-exp base unbounded `K·exp(z·R)→∞`; additive HS-pole sum (≤ C/z²) cannot cancel it | ✓ DONE (`unlike_pair_twoexp_unbounded`, `hs_pole_additive_insufficient`) | `FMSAPoly/PolyApproxFails.lean` |
| GA.2 | *(opt.)* Off-diagonal `G_{01}(z)→0` exponentially as `z·(σ₁−σ₀)→∞`; structural cause of unlike-pair divergence | ◑ decay mechanism DONE (`g_mat_offdiag_decay`, `exp_neg_mul_atTop`); concrete N=2 Q̂₀ cofactor deferred | `YukawaDCF/OffDiagDecay.lean` |

**Group GA note (2026-07-15).** FMSA_GA_matrix_mix is the fix for Groups chsY/P, but its own
two-exponential inner formula is ill-conditioned for unlike pairs at large σ-ratio. GA.1 and GA.2
(formerly C.3/C.4) were split out of Group C into this failure group and renumbered to the
group-local `GA.*` prefix on 2026-07-15. Positive counterparts C.2/C.5 stay in Group C. Full
records: [proof_notes_failures.md](proof_notes_failures.md) Group GA.

### Group P — FMSA_poly Failure Analysis *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| P.1 | E_ij is sum of decaying exponentials | ✓ DONE | `FMSAPoly/EijStructure.lean` |
| P.2 | Origin constraint p₀=−E_ij(0) | ✓ DONE | `FMSAPoly/OriginConstraint.lean` |
| P.3 | No polynomial approximates exp(+z·(R−r)) under normalisation | ✓ DONE | `FMSAPoly/PolyApproxFails.lean` |
| P.4 | E_ij contact value matches outer-core MSA | ✓ DONE | `FMSAPoly/ContactValue.lean` |
| P.C1 | Corollary: normalisation forces large error | ✓ DONE | `FMSAPoly/PolyApproxCorollary.lean` |
| P.C2 | Two-endpoint bound | ✓ DONE | `FMSAPoly/PolyApproxFails.lean` |
| P.B1 | Exponential basis: 2×2 system always solvable | ✓ DONE | `FMSAPoly/ExpBasis.lean` |
| P.B2 | Exponential basis: zero endpoint errors | ✓ DONE | `FMSAPoly/ExpBasis.lean` |

### Group OZ — Ornstein-Zernike Structure *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| OZ.1 | PY closed-form DCF for hard spheres | ✓ DONE | `HardSphere/PYDCF.lean` |
| OZ.2 | g₀_HS via OZ fixed point | ◑ fixed-point framework (`oz_h`, `oz_fixed_pt_unique`) live and reused by the Fourier line; its Laplace specialization (`oz_laplace_oz_eq` axiom + `g0_HS_laplace_spec`) **deleted** 2026-07-15. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/PYOZ_GHS.lean` |
| OZ.2b | Gap A: exterior 3D-OZ equation for `oz_h` (`oz_h_satisfies_conv_ext`) | ✓ DONE, transform-independent — reused verbatim by OZ.7; the Laplace assembly `oz_laplace_oz_eq_of_core_closure` that consumed it was **deleted** 2026-07-15 (it used the false `radial_laplace_conv`). See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/OZExteriorBridge.lean` |
| OZ.3 | g₀_HS via OZ Laplace inversion | ◑ conditional on OZ.2 + `oz_h_exterior_regularity` axiom (was `g0_HS_contact_value` axiom; that bare physical axiom is **retired** — `g0_HS_contact_value` is now a theorem in `JumpAsymptotic.lean`, see BAXTER.8) | `HardSphere/PYOZ.lean`, `HardSphere/JumpAsymptotic.lean` |
| OZ.4 | Linearised OZ: Ĥ¹=Ĉ¹·S₀ | ✓ DONE | `HardSphere/PYOZ.lean` |
| OZ.6 | Radial sine/Fourier transform convolution theorem — correct replacement for the disproven `radial_laplace_conv` | ✓ DONE, no axiom | `HardSphere/RadialFourier.lean` |
| OZ.7 | Fourier-domain exterior OZ equation (Gap A ∪ Gap B, correct-transform counterpart of `oz_laplace_oz_eq_of_core_closure`) | ✓ DONE, conditional only on OZ.9 (`hcore`) | `HardSphere/OZFourierBridge.lean` |
| OZ.8 | Closed-form sine-transform formula for `c_HS` + bridge to `C_HS_laplace`/`S0` via `s↔-ik` | ✓ DONE (Parts A+B), no axiom/sorry. Bridge to `g0_HS_contact_value` — see Group BAXTER `BAXTER.4`/`8` | `HardSphere/RadialFourierCHS.lean` |
| OZ.9a | PY core closure (Gap B) for `r < σ` — promoted to a named, numerically-verified axiom | ✓ DONE (axiom `oz_core_closure`, Route A; not proved from Mathlib real-analysis — needs Group BAXTER's full construction, staged not started) | `HardSphere/PYOZ_GHS.lean` |
| OZ.9b | `oz_fourier_oz_eq_of_PY_core`: OZ.7 specialized to consume `oz_core_closure` instead of an externally-supplied `hcore` — most complete/trustworthy result in the whole OZ chain (Gap A + convolution theorem + Gap B all proved/axiomatized by name, only routine integrability hypotheses remain) | ✓ DONE | `HardSphere/OZFourierBridge.lean` |
| OZ.10 | Uniqueness of the OZ fixed point (`oz_fixed_pt_unique`) | ◑ axiom — dilute proved (OZ.10-dilute); mid/high density is **TRUE** (hard spheres have no spinodal) but same-core as the BAXTER Wiener–Hopf line, **not** compact Fredholm (`oz_linear_op` K is a non-compact half-line Wiener–Hopf operator; Mathlib *has* compact Fredholm but it doesn't apply). No general WH theory needed: factorization = Baxter factorization (BAXTER.3); missing piece = BAXTER.12–13's explicit `h_explicit` inverse. Gated by the BAXTER line. | `HardSphere/PYOZ_GHS.lean` |
| OZ.10-dilute | Dilute-regime (`eta<1`, `24·eta·bracket<1`, i.e. `eta≲0.088`) Banach existence/uniqueness for `oz_fixed_pt_unique`, exterior-only | ✓ DONE — `oz_fixed_pt_unique_dilute`, genuine theorem, no axiom/sorry. Mid/high density (`eta≈0.3–0.5`) is TRUE but gated by the BAXTER line (K non-compact ⇒ not compact Fredholm; `24η·bracket` = K's spectral radius = the dilute threshold; Baxter factorization + BAXTER.12–13 explicit inverse), not attempted here — see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.10-dilute. | `HardSphere/OzFixedPtDilute.lean` (+ `c_HS_abs_t2_integrableOn` in `HardSphere/PYDCF.lean`) |
| OZ.18 | Hard-sphere `λ_ij` kink: `c_HS,ij` is C⁰ (slope kink) at `λ_ij=\|d_i−d_j\|/2`, unlike pairs *(formerly B.19)* | ✓ DONE — C⁰ + both one-sided slopes proved; genuine kink conditional on core-slope≠0 (numerical) | `HardSphere/CHSKink.lean` |

**Tasks OZ.5, OZ.11–OZ.17 (and `OZ.13`) have moved to Group BAXTER** (`proof_notes_baxter.md`),
renumbered `BAXTER.1`–`BAXTER.8` — see the table below.

### Group BAXTER — Baxter Q-Factor & Wiener–Hopf Route to the PY Closed Form *(hard_sphere)*

*Depends on Group OZ above (uses `oz_h`, `c_HS`, `radial_fourier`, `oz_core_closure`, etc.);
Group OZ does not depend on this group. See [proof_notes_baxter.md](proof_notes_baxter.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `BAXTER.1` | Baxter real-space convolution identity *(formerly OZ.5)* | ✓ DONE | `HardSphere/BaxterRealSpace.lean` |
| `BAXTER.2` | Re-derive Baxter's second relation (Route B) from a primary source *(formerly OZ.11)* | ☐ not started — residue-series construction validated 3 independent ways (ground truth, pole-growth law, real-space OZ check); staged into `BAXTER.9`–`13` | — |
| `BAXTER.3` | Baxter's Wiener–Hopf factorization `(1-ρQ̂(k))(1-ρQ̂(-k)) = 1-ρĈ_sine(k)` *(formerly OZ.12)* | ✓ DONE — `baxter_wiener_hopf_factorization`, genuine theorem, no sorry/axiom; uses existing `q0_poly` | `HardSphere/BaxterWienerHopf.lean` |
| `BAXTER.4` | Derive `g0_HS_contact_value` from OZ.8's Fourier-domain closed form (full residue inversion) *(formerly OZ.13)* | ☐ deliberately parked — fully absorbed into `BAXTER.2`'s scope, not independent | — |
| `BAXTER.5` | Extract `g0_HS_contact_value` via a jump-asymptotic argument on `Ĥ(k)`'s large-`k` behavior *(formerly OZ.14)* | ✓ DONE as a whole — split into `BAXTER.6`/`7`/`8`, all three done | — |
| `BAXTER.6` | General jump-asymptotic lemma for `radial_fourier`: `f k = 4πσJ·cos(kσ)/k² + o(1/k²)` for `f` with jump `J` at `σ` *(formerly OZ.15)* | ✓ DONE — `radial_fourier_jump_asymptotic`, genuine theorem, no sorry/axiom; via one IBP + Mathlib's Riemann-Lebesgue lemma | `HardSphere/JumpAsymptotic.lean` |
| `BAXTER.7` | Concrete closed-form asymptotic of `Ĥ(k)=Ĉ(k)/(1-ρĈ(k))`: leading coefficient `4πσ(1+η/2)/(1-η)²` *(formerly OZ.16)* | ✓ DONE — `Hhat_closed_asymptotic`, genuine theorem, no sorry/axiom | `HardSphere/RadialFourierCHS.lean` |
| `BAXTER.8` | Assembly: apply `BAXTER.6` to `oz_h`, match against `BAXTER.7`, conclude `g0_HS_contact_value` *(formerly OZ.17)* | ✓ DONE — `g0_HS_contact_value_of_oz_h_regularity` (conditional theorem, no sorry/axiom) **plus** its unconditional consequence: the bare `g0_HS_contact_value` axiom is now **retired**, replaced by the named regularity axiom `oz_h_exterior_regularity` bundling BAXTER.8's `oz_h` hypotheses, from which `theorem g0_HS_contact_value` is proved (`#print axioms` → `oz_core_closure`, `oz_fixed_pt_unique`, `oz_h_exterior_regularity`; no `g0_HS_contact_value` axiom). Retires OZ.3's physical-number axiom. | `HardSphere/JumpAsymptotic.lean` |
| `BAXTER.9` | `Qhat_complex : ℂ → ℂ` in closed form, proved entire | ✓ DONE — `Qhat_complex_entire` + `Qhat_complex_formula`, genuine theorems, no sorry/axiom; entireness via `entire_poly_exp_integral` (dominated-convergence differentiation under the integral), closed form via new `zeta0`/`zeta1`/`zeta2` moment lemmas; numerically cross-checked against the raw integral and against `BAXTER.3`'s real-`k` formulas | `HardSphere/BaxterZeros.lean` |
| `BAXTER.10` | Numerical/symbolic feasibility check for the Banach-pole-existence strategy | ✓ DONE — **GO**: uniform contraction bound (`max_L→0.369`, margin `≈63%`) found for `n≥10`, robust across `η∈[0.05,0.45]` | — (Python, not Lean) |
| `BAXTER.11` | Pole existence in Lean via Banach contraction | ✓ DONE (conditional) — `Qhat_complex_zeros_infinite`, no sorry/axiom; all magnitude bounds, branch-safety, Lipschitz/MVT, Banach wiring, distinctness/infinitude proved unconditionally for general `η∈(0,1),σ>0,ρ≠0`; one explicit "good guess" hypothesis (`hstep`, numerically validated by `BAXTER.10`) not yet discharged for the specific asymptotic guess formula | `HardSphere/BaxterPoles.lean` |
| `BAXTER.12` | Residue formula + convergence for `h_explicit` | ◐ in progress — `residue_of_simple_pole`, `Chat_complex` (complex `Ĉ`, `RadialFourierCHSComplex.lean`), `G_baxter_deriv`, `Hhat_residue_at_pole` (full residue formula), `G_baxter_zero_mirror` (mirror pole family, B.2), `h_explicit`/`h_explicit_term`/`h_explicit_summable` (B.3 — `Summable` conditional on `r>σ` + a magnitude-bound hypothesis matching the `n^{1-2r/σ}` decay law, exponent corrected + numerically re-verified at 3 σ values this pass, replacing an earlier σ=1-only check that masked the σ-dependence), `G_baxter_deriv_ne_zero_of_large`/`G_baxter_neg_ne_zero_of_large` (both of `Hhat_residue_at_pole`'s non-degeneracy hypotheses now discharged in general as standalone magnitude-bound theorems), and `G_baxter_pole_family_exists` (`BAXTER.11`'s witness function now exposed as a standalone name) all done, no sorry/axiom; remaining item split out to `BAXTER.14` | `HardSphere/BaxterResidue.lean`, `HardSphere/RadialFourierCHSComplex.lean`, `HardSphere/BaxterPoles.lean` |
| `BAXTER.14` | Rigorous `n^{1-2r/σ}` magnitude bound + concrete `h_explicit` instantiation | ☐ not started, blocked on `BAXTER.12` (done except this) — split out of `BAXTER.12`'s "what's left" as its own task since it's an asymptotic-estimate task (like `BAXTER.11`'s `hstep`), not an assembly/definition task | `HardSphere/BaxterResidue.lean`, `HardSphere/BaxterPoles.lean` |
| `BAXTER.13` | `h_explicit` satisfies `OzFixedPt`; invoke `oz_fixed_pt_unique` (retires `oz_core_closure`) | ☐ not started, blocked on `BAXTER.12`/`BAXTER.14` | — |

### Group F — Free Energy Integrals *(free_energy)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| F.1 | Outer-core free energy integral | ✓ DONE | `FreeEnergy/OuterIntegral.lean` |
| F.2a | Inner-core energy integral (E_ij part) | ✓ DONE | `FreeEnergy/InnerIntegral.lean` |
| F.2b | LJ inner-core integral identity | ✓ DONE | `FreeEnergy/LJIntegral.lean` |
| F.3a | Free energy convergence (FMSA_GA_matrix_mix route) | ✓ DONE | `FreeEnergy/Convergence.lean` |
| F.3b | Free energy convergence (LJ/FMSA_poly route) | ✓ DONE | `FreeEnergy/Convergence.lean` |
| F.4 | Compressibility sum rule | ✗ deleted | — |
| F.5 | Contact-value approximation error | ✓ DONE | `FreeEnergy/ContactError.lean` |
| F.6 | FMSA_GA_matrix_mix exact vs LJ free energy comparison | ✓ DONE | `FreeEnergy/SumRule.lean` |

**F.4 deletion note:** The compressibility sum rule `∂(βP)/∂ρ = 1−ρĉ(0)` mixes the energy-route
free energy (what FMSA computes: `∫ u g₀ r² dr`) with the compressibility-route DCF (`ĉ(0)` from
integrating c(r)). For any first-order approximate theory these two routes give different numbers —
the gap measures route inconsistency, not model quality. Verifying route inconsistency numerically
is not a useful model check. Deleted.

### Group FW — White-Bear FMT / BMCSL Mixture Thermodynamics *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| FW.1 | FMT species symmetry: `betaf_hs` depends on `rho` only through `∑ᵢρᵢ` when all diameters equal | ✓ DONE, no axiom (`betaf_hs_species_symmetry`) | `HardSphere/WhiteBearFMT.lean` |
| FW.2 | BMCSL/White-Bear thermodynamic consistency: virial pressure (from `g0_bmcsl`) = FMT scaled pressure (from `betaf_hs`) | ✓ DONE, no axiom (`bmcsl_virial_eq_fmt_pressure`) | `HardSphere/WhiteBearFMT.lean` |

**2026 note — corrected framing, then proved.** An earlier round of this file claimed FW.2
faced "the same obstruction as `g0_HS_contact_value`" (Baxter Wiener–Hopf). That was wrong —
`g0_bmcsl` reduces at N=1 to the Carnahan-Starling value `(1-η/2)/(1-η)³`, not the PY value
`(1+η/2)/(1-η)²` that `g0_HS_contact_value` axiomatizes, and is *used as a definition* in this
codebase (no independently-computed multi-species PY/Baxter solution exists to compare it
against). The real open content was the thermodynamic consistency identity numerically checked
by `verify_wc.py`'s `wc2()` — proved exactly (not axiomatized) via `bmcsl_virial_eq_fmt_pressure`,
assembled from a `HasDerivAt` chain along the density-scaling ray (`wbPhi_ray_pressure_eq`) and
a `Finset` double-sum moment reduction (`g0_bmcsl_virial_sum_eq`). See
[proof_notes_free_energy.md](proof_notes_free_energy.md) for the full derivation.

### Group 5 — Matching at Contact *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 5.1 | Inner/outer matching at r=R_ij (2YK only) | ✓ structural (I1/I2=0) / **⊥ physical claim disproved** | `YukawaDCF/ContactMatching.lean` |

**5.1 disproof note:** The Lean proof establishes only that `I1(0) = I2(0) = 0` (integral over an
empty interval — trivially true) and `eij(R,R) = ΣA_k`. It explicitly states in a comment that
full DCF continuity additionally requires the MSA closure condition `K = A_k` at each Yukawa
pole, which is NOT proved and does NOT hold.

Numerical evidence from `FMSA_pure` (verify_pure.py V.1): the first-order c₁ gap at r = d_bh is
~1.1–1.7 across liquid-range state points, far from the ~1e-6 numerical-precision level.  The
total-c gap is smaller (~0.02–0.7) only because the FMT c₀ accidentally partially compensates.
Since the pure-fluid limit is the simplest case, the same discontinuity must appear in mixtures.
The intended physical matching property (DCF continuity at contact for the 2YK FMSA) is false.

### Group D — Pure-Limit Equivalence

~~Tasks D.1–D.4 deleted.~~ Written for the old scalar Path B approach; no longer valid after
FMSA_GA_matrix_mix redesign (full G/A matrix, mediated terms). Pure-limit N=1 reduction is covered
by **C.1** (✓ DONE). See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) if a new Group D is needed.

---

*Numerical verification tasks (Groups V and W) are in `../todo/todo_numerical.md`.*
