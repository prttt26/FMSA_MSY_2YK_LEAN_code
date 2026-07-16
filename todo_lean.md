# Lean Proof Tasks: FMSA Yukawa Mixture Theory

This file is the **status index** for all Lean 4 + Mathlib proofs in `LeanCode/`.
Detailed proof records (statements, proof sketches, pitfalls, Lean API notes) are in:

- [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) — Groups 2, 3, OZ (pure HS foundations)
- [proof_notes_baxter.md](proof_notes_baxter.md) — Group BAXTER (Baxter Q-factor + Wiener–Hopf route to the PY closed form)
- [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) — Group M (multi-component HS Baxter Q̂₀ matrix identity, rank-2 det reduction, det-positivity monotonicity M.5–M.8)
- [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) — Groups 1, 4, B, C, 5 (Yukawa DCF derivation)
- [proof_notes_breakpoints.md](proof_notes_breakpoints.md) — Group IB (inner-core mediated breakpoints)
- [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) — Groups Y1, MML, MZERO, MPOLY (first-order Yukawa RDF/DCF via Wiener–Hopf; N=2 mixture inner-core Mittag-Leffler)
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

| Task | Axiom | File | Physical meaning / proof path |
|------|-------|------|-------------------------------|
| OZ.10 | `oz_fixed_pt_unique` | `HardSphere/PYOZ_GHS.lean` | OZ fixed-point uniqueness. Dilute case proved (`oz_fixed_pt_unique_dilute`); mid/high density TRUE but gated by the BAXTER line (`K` is a non-compact Wiener–Hopf op ⇒ compact Fredholm doesn't apply). See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) OZ.10. |
| OZ.9a | `oz_core_closure` | `HardSphere/PYOZ_GHS.lean` | PY core closure (Baxter/Wertheim). Lean proof needs Group POLE's pole/residue series (`POLE.1`–`5`) plus Group OZFIX's assembly (`OZFIX.1`–`8`). Numerically verified — evidence in the Numerically-verified table below. See [proof_notes_baxter.md](proof_notes_baxter.md) `BAXTER.2`. |
| OZ.3 | `oz_h_exterior_regularity` | `HardSphere/JumpAsymptotic.lean` | Regularity/decay/integrability of the OZ exterior solution `oz_h` on `[σ,∞)`. See [proof_notes_contact.md](proof_notes_contact.md) `CONTACT.5`. |
| M.4 | `Q0_moment_det_pos` | `HardSphere/Q0DetRankTwo.lean` | Multi-component HS Baxter `det=(1+a)(1+d)−bc > 0` (physical hyps). Discharges `hdet` ⇒ unconditional `Q0_mat_phys_isUnit_det` (M.3 & M.4); retire when proved. Numerically verified — evidence in the Numerically-verified table below. See [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) M.4. |
| MA.1 (OZFIX.10) | `circleIntegral_eq_sum_of_small_circles` | `Analysis/ContourDeformation.lean` | **General-purpose classical math, not project physics**: contour deformation, big circle → finitely many disjoint off-center small circles (keyhole/slit argument; Mathlib has no winding numbers/residue theorem — its own `docs/1000.yaml` tracks these as unformalized). Powers the genuine theorem `circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles` (finite residue-sum formula). Reusable by MZERO Route B. See [MATH_AXIOMS.md](MATH_AXIOMS.md). Retire if/when Mathlib gains a residue theorem. |
| MA.1 (OZFIX.10) | `halfDiskBoundary_eq_sum_of_small_circles` | `Analysis/ContourDeformation.lean` | **General-purpose classical math**: same keyhole/slit deformation content for the *upper half-disk boundary* (`[-R,R]` diameter + semicircular arc) — the contour shape Fourier-inversion arguments close; the circular axiom above deliberately doesn't cover it. Powers `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`. Companion to the axiom-free `jordan_lemma_arc_bound` (`Analysis/JordanLemma.lean` — proved outright, NOT an axiom). See [MATH_AXIOMS.md](MATH_AXIOMS.md). Retire alongside the above. |
| MA.2 | `mittagLeffler_expansion_of_bounded_on_circles` | `Analysis/MittagLeffler.lean` | **General-purpose classical math**: Mittag-Leffler expansion theorem (Whittaker–Watson §7.4) — simple poles + uniformly bounded on expanding circles ⇒ ordered pole expansion `f(z)-f(0)=Σ resₙ(1/(z-pₙ)+1/pₙ)`. Tracked unformalized in Mathlib's `docs/1000.yaml`. Numerically pre-checked against `Ĥ` at η∈{0.3,0.45}. Consumers: `OZFIX.9`/`OZFIX.10`, potentially `MML.3`/`GA.4`. Companion genuine theorem (NOT an axiom): `fourier_kernel_one_pole` (same file). See [MATH_AXIOMS.md](MATH_AXIOMS.md). Retire when Mathlib gains Mittag-Leffler/residue theorem. |
| MA.7 | `sokhotski_plemelj_upper` | `Analysis/SokhotskiPlemelj.lean` | **General-purpose classical math**: Sokhotski–Plemelj boundary values (integrated upper form; P.V. existence as hypothesis — no distribution theory). Mathlib has no Hilbert transform/P.V. API (Y1.3 was re-routed around this gap). Pre-placed (user-requested); no current consumer ([LN] §6.3-style WH derivations, potentially `MML.3`). Numerically pre-checked (3 test functions). See [MATH_AXIOMS.md](MATH_AXIOMS.md). Retire when Mathlib gains a Hilbert-transform/P.V. API. |
| MA.4 | `vanDerCorput_first_derivative_test` | `Analysis/VanDerCorput.lean` | **General-purpose classical math**: van der Corput first-derivative test with amplitude (Stein VIII.1.2 + cor.): monotonic `φ'`, `\|φ'\|≥λ` ⇒ `‖∫e^{iφ}ψ‖ ≤ (3/λ)(‖ψ(b)‖+∫‖ψ'‖)`. No oscillatory-integral estimates in Mathlib. No current consumer (toolbox; the OZFIX.10 monolithic arc defeats plain VdC and was resolved by MA.2+MA.3 instead). Numerically pre-checked both monotone branches. See [MATH_AXIOMS.md](MATH_AXIOMS.md). **Retire by proving** — plausibly provable via `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (IBP). |

### Numerically verified — not proved in Lean

*(Items backed by a named `axiom` are cross-listed with the Axioms table above — the declaration +
meaning + proof-path live there; the numerical evidence lives here. The `Axiomatized as` column names
the axiom, or `—` for numerically-verified claims that are not axiomatized.)*

| Task | Claim | Axiomatized as | File | What's verified (numerical evidence) |
|------|-------|----------------|------|--------------------------------------|
| OZ.9a | PY core closure | `oz_core_closure` | `HardSphere/PYOZ_GHS.lean` | Verified across all tested state points/densities. See [proof_notes_baxter.md](proof_notes_baxter.md) `BAXTER.2`. |
| M.4 | `det(Q0_mat_phys) > 0` (`(1+a)(1+d) > bc`) | `Q0_moment_det_pos` | `HardSphere/Q0DetRankTwo.lean` | 20 000 random physical trials: `det ≥ 1` always (min ≈ 1.0000013); `det(z)` monotone↓ with `det(∞)=1`; `bc≥ad` proved (M.8). See [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) M.4. |
| B.9 | `D_ij ≠ 0` for unlike pairs | — (not axiomatized; Option B proved, faithful → MPOLY) | `YukawaDCF/B5MixturePoly.lean` (`b9_dij_cubic_nonzero`) | Verified (`D_01=−3295` at σ=[1,1.2], ρ*=0.5, T*=1.5); Option B cubic Taylor coeff `−133/2880 ≠ 0` proved axiom-clean. See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) B.9. |

### Conditional-theorem hypotheses — proved, but conditional on an explicit open assumption

*Named theorems that **are** proved in Lean but carry one explicit, genuinely-open hypothesis
(a `theorem T (h : …) : P`, structurally distinct from a bare `axiom X : P`). Excludes routine
`IntervalIntegrable`/`Integrable` side-conditions (too numerous, not physically meaningful) and real
geometry predicates (`ActiveA`/`ActiveB` etc.). 
`Status`: 
**num** = numerically validated · 
**lit** = physically expected from the literature · 
**open** = genuinely open. Hypotheses that were promoted to
named axioms (`hcore`→`oz_core_closure`, `oz_h` regularity→`oz_h_exterior_regularity`,
`hdet`→`Q0_moment_det_pos`) live in the Axioms table above, not here.*

| Task | Hypothesis | On theorem (file) | Status | What it assumes / discharge path |
|------|-----------|-------------------|--------|----------------------------------|
| POLE.3 | `hstep` | `Qhat_complex_zeros_infinite` (`HardSphere/BaxterPoles.lean`) | num (POLE.2) | good-guess contraction bound for the asymptotic pole family (checked `η∈{.05,.1,.3,.45}`, `n≤10⁴`, margin ≈18–20%). **Discharge = provide `ChordPoleFamily (G_baxter …)`** (`Analysis/BanachPoleFamily.lean`) — the *same shared obligation* as MZERO.5 below; a chord-Newton route `G_baxter_zeros_infinite_of_chordPoleFamily` consumes that predicate. **NB: POLE.5 is DONE** (the `n^{1−2r/σ}` summability bound) and does **not** discharge this `hstep`; but its magnitude machinery (`abs_exp_neg_ikn_sigma_*`, `G_baxter_deriv_lower_bound_of_zero`, `Npoly/Dpoly` bounds) is the reusable technique. **2026-07-15 dependency survey: `hstep` is the single abstract→concrete gate** — every `h_explicit` theorem (POLE.5/OZFIX.3/5/7/8) is stated over an abstract `kfam` (hstep-free), but the only concrete-family constructor `G_baxter_pole_family_exists_growth` carries `hstep`; discharging it unlocks POLE.3 + MZERO.5/MZERO.7 unconditional, concrete instantiation of the OZFIX chain (⇒ with `hcollapse` + σ-endpoint, the `oz_core_closure`/`oz_h_exterior_regularity` retirement chain), and OZ.10 mid/high-density. `POLE.6` pre-wired the summability consumer (`h_explicit_summable_concrete`, `HardSphere/HExplicitConcrete.lean`, incl. the previously-missing `hkfam_im`). **Discharge in progress as `POLE.7`** (scoping GO: derived log-lift guess, explicit per-η thresholds). See [proof_notes_pole.md](proof_notes_pole.md) `POLE.3`/`POLE.7`. |
| MZERO.5 | `hbound`+`hstep` (= `ChordPoleFamily det_c`) | `Q0_det_c_zeros_infinite` (`YukawaDCF/MixtureHSZeros.lean`) | num (MZERO.2) | chord-Newton contraction (`‖1−det′/Fp1‖≤K`) + good-guess (`‖det(s₁)/Fp1‖≤r(1−K)`) for the Im-spaced (Δ≈π) `det(Q̂₀)` zero family (K≈0.30 uniform). **Same `ChordPoleFamily F` obligation as POLE.3** (shared predicate, `Analysis/BanachPoleFamily.lean`): `det_c`'s rank-2 form lives in the same `mAux/nAux(sσⱼ)` Baxter auxiliaries as `G_baxter`, so one asymptotic-family lemma (2-freq extension of POLE.5's 1-freq method) closes **both**. See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) MZERO.5. |
| POLE.5 | pole-family **magnitude growth** `hkfam_re` (`c·n+d ≤ ‖kₙ‖`) | `h_explicit_summable_of_pole_family` (`HardSphere/BaxterResidue.lean`) | num — short mechanical follow-on | **Separate from POLE.3/MZERO.5's `ChordPoleFamily` existence/contraction (`hstep`) gap** — this is the family's linear *magnitude* input to the **proved** summability theorem (`n^{1−2r/σ}` decay ⇒ `h_explicit` `Summable`), not the family-existence good-guess. Holds for any linearly-spaced pole family: Baxter's (`Re kₙ = 2πn/σ`) and the mixture's (`Im sₙ = π·n`) both give it; wiring `G_baxter_pole_family_exists`'s concrete centres (or a `ChordPoleFamily`'s linear-spaced ones — note `ChordPoleFamily.hsep` alone forces `{kₙ}` unbounded, not the linear *rate*) into `hkfam_re` discharges it. See [proof_notes_pole.md](proof_notes_pole.md) `POLE.5`. |
| OZ.18 | `hslope` | `cHS_FMT_not_differentiableAt` (`HardSphere/CHSKink.lean`) | num | core-slope `deriv(cHS_core)\|Rᵢ−Rⱼ\| ≠ 0` ⇒ genuine (non-removable) `c_HS` kink; C⁰ + both one-sided slopes are unconditional. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) OZ.18. |
| C.5 | `hblum` | `c5_residue_eq_K_mul_Ginv` (`YukawaDCF/YukawaPoleResidue.lean`) | lit (Blum 1975) | the Blum simple-pole residue shape `N(z_t)/D′ = K_t·[Q̂₀⁻¹]_{ij}`; the residue-assembly core of C.5. See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) C.5. |
| B.10 | `ha` (`A_{ij}=R(0)/24 ≠ 0`) | `b10_natDegree_eq_four` (`YukawaDCF/B5MixturePoly.lean`) | open (same flavor as B.9) | leading coeff nonzero ⇒ `natDegree P_{ij}=4`; whether the actual FMSA `A_{ij} ≠ 0` holds is open. See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) B.10. |
| GA.2 | `hB` (`\|B_k\| ≤ K/z²`) | `hs_pole_additive_insufficient` (`FMSAPoly/PolyApproxFails.lean`) | num | the additive HS-pole correction is `O(1/z²)`-bounded ⇒ cannot cancel the unbounded two-exp base. See [proof_notes_failures.md](proof_notes_failures.md) GA.2. |

### Open tasks — not yet started

*Mixture (MML/MZERO) DONE pieces (not repeated below): MML.1/MML.2, MZERO.1-foundation, **Route A** (MZERO.2–MZERO.7, conditional on MZERO.5), **Route B** capstones MZERO.8/MZERO.10/MZERO.11 + unconditional `divisor det ≥ 0` (`det_divisor_nonneg`, part of MZERO.9). The **MZERO.5** Route-A magnitude bound (≡ **POLE.3** `hstep`) is a **conditional hypothesis** — see the Conditional-hypotheses table above, not repeated here.*

| Task | Title | Depends on | Notes |
|------|-------|-----------|-------|
| `OZFIX.6` | `OzFixedPt` (exterior) algebraic collapse | `OZFIX.1`–`5` (all done) | Termwise strategy via `oz_forcing`+`oz_linear_op` directly (no `radial3d_conv`/Fourier inversion needed). **Numerically scoped: the originally-planned per-pole/termwise collapse is FALSE** (checked directly: a single pole's `oz_linear_op` contribution vs. its naive `h_explicit_term` target has ratio `-2.72`, not `1` — `oz_forcing`'s pole-index-free contribution must do essential structural work, so the identity only closes at the full-series level). The *aggregate* target `oz_forcing+oz_linear_op[h_explicit]=h_explicit` is not in doubt (strong prior numerical confirmation via `radial3d_conv`, `BAXTER.2`), but the proof route needs rethinking — see `proof_notes_ozfix.md` `OZFIX.6` for the two candidate routes considered. **`OZFIX.7` and `OZFIX.8` are now DONE** (conditional on this gap plus `OZFIX.7`'s own σ-endpoint gap) — see Group OZFIX table above. Retiring `oz_core_closure` itself is a separate Phase C follow-on. See [proof_notes_ozfix.md](proof_notes_ozfix.md). |
| `MML.3` | Full inner-DCF Mittag-Leffler assembly: `c^{inner}_{01}(r)=[Yukawa poles]+Σ_k B_k·e^{−s_k·r}` | MML.2 (done), MZERO.1-foundation (done), Y1.3 (done) | ☐ not started; **VERY HARD** (full assembly). Y1.3 unblocked it. See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) MML.3. |
| `MPOLY` *(optional)* | Faithful inner-core poly coeffs `D_ij=R'_ij(0)/6` via inside-core Laplace remainder `R_ij(s)=s⁵[e^{sR}S_ij−Y_ij]` | MML.1, B.5–B.10, B.9 Option B (done) | ☐ not started; optional — upgrades B.9 Option B *mechanism* to the exact `R'_ij(0)/6` identity; needs inside-core `S_ij`/`Y_ij` packaging. See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) MPOLY. |
| `MZERO.9` (`hJensen`) | Route-B Nevanlinna/Jensen finsum counting bound (finite zeros ⇒ `O(log R)`) | MZERO.8/MZERO.10/MZERO.11 (done), `det_divisor_nonneg` (done) | ◑ `divisor det ≥ 0` now **unconditional**; only the finsum bound (`MeromorphicOn.circleAverage_log_norm` + finite support) remains. **Not blocking — Route A closes MZERO.1.** See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) MZERO.9. |
| `GA.4` *(corollary)* | MSA `ε`-series convergence radius `R_conv≤C·e^{−z·R_{01}}→0` as `z·R→∞` | MZERO.1, MML.3, `ε`-param of `det(Q̂₀)` zeros | ☐ not started; post-MML.3 corollary — completes GA.3 (termwise-large) with series-level divergence at 2YK (`R_conv≲2×10⁻⁶≪|K₂|`). See [proof_notes_failures.md](proof_notes_failures.md) GA.4 (Group GA). |


---

## Task Status

### Group MA — MathAxioms: General-Purpose Math Axioms & Missing-Mathlib Machinery *(analysis)*

*Cross-cutting infrastructure group (2026-07-15): surveys the project for missing-Mathlib-machinery
gaps, pre-places admissible axioms (named classical theorems only, numerically pre-checked,
narrowest form — see the admissibility discipline in [MATH_AXIOMS.md](MATH_AXIOMS.md)), and proves
what's provable. Lean home: `LeanCode/Analysis/` (project-independent, no `FMSA.*` def usage).
Registry + task records: [MATH_AXIOMS.md](MATH_AXIOMS.md). Axiom declarations are cross-listed in
the Axioms table above.*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| MA.1 | Founding pieces (re-filed from the `OZFIX.10` Route B effort): circular + half-disk contour-deformation axioms, their derived residue-sum theorems, and the **axiom-free** `jordan_lemma_arc_bound` | ✓ DONE | `Analysis/ContourDeformation.lean`, `Analysis/JordanLemma.lean` |
| MA.2 | **Mittag-Leffler expansion axiom** (Whittaker–Watson §7.4: simple poles, bounded on expanding circles ⇒ ordered pole expansion) — numerically pre-checked against `Ĥ` at η∈{0.3,0.45} (`sup‖Ĥ‖` constant on circles; expansion → `Ĥ` pointwise, ~1e-7 @ N=60) | ✓ DONE | `Analysis/MittagLeffler.lean` |
| MA.3 | **One-pole Fourier kernel** `∫_{-R}^{R} e^{ixr}/(x-k₀)dx → 2πi·e^{ik₀r}` (`Im k₀>0`, `r>0`) — genuine theorem, `#print axioms` = halfDisk axiom + standard three; with MA.2 this decomposes `OZFIX.10`'s blocked monolithic arc estimate | ✓ DONE (no new axiom) | `Analysis/MittagLeffler.lean` |
| MA.4 | **Van der Corput first-derivative test** (with amplitude; monotone-or-antitone `φ'`, `\|φ'\|≥λ` ⇒ `‖∫e^{iφ}ψ‖ ≤ (3/λ)(‖ψ(b)‖+∫‖ψ'‖)`) — numerically pre-checked both branches, `λ∈{1..500}` | ✓ DONE (axiom; **retire-by-proving preferred** — plausibly provable via Mathlib IBP) | `Analysis/VanDerCorput.lean` |
| MA.5 | **Jensen counting bound** (`f` meromorphic on `ℂ`, no poles, **finite divisor support** ⇒ `circleAverage(log‖f‖) ≤ M·logR+C`) — discharges MZERO Route B's `hJensen` (wiring to `detC` needs the mechanical literal-zeros→divisor-support bridge via analyticity, left to MZERO). **NB: first landed as an axiom with a FALSE literal-zero-set statement** (junk-value `sin`-modification counterexample, caught while attempting the proof) — corrected and **PROVED** from Mathlib's Jensen formula, `#print axioms` = standard three | ✓ DONE (**proved, no axiom**) | `Analysis/JensenCounting.lean` |
| MA.6 | Relocate misfiled pure math `HardSphere/→Analysis/`: `ResidueAtSimplePole.lean`, `BanachPoleFamily.lean` (+5 consumer imports; namespaces kept) | ✓ DONE (`lake build` green) | `Analysis/ResidueAtSimplePole.lean`, `Analysis/BanachPoleFamily.lean` |
| MA.7 | **Sokhotski–Plemelj boundary values** (upper, integrated form; P.V. existence as hypothesis) — user-requested pre-placement, numerically pre-checked (3 test functions, linear-in-ε convergence) | ✓ DONE | `Analysis/SokhotskiPlemelj.lean` |

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
| 4.2→M.9 | g + a·exp(−z) = 1 — *re-IDed to* **M.9** *(Group M, hard-sphere)* | ✓ DONE | see M.9 — `HardSphere/SingleCompIdentity.lean` |
| 4.4 | Full N=1 reduction Eq.41→42 | ✓ DONE | `YukawaDCF/SingleCompReduction.lean` |

### Group M — Multi-Component Baxter Identity *(hard-sphere Baxter matrix)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| M.1 | Abstract matrix identity Ĝ+Â·c=I | ✓ DONE | `HardSphere/MatrixIdentity.lean` |
| M.2 | N=1 limit: Ĝ₀₀=g, Â₀₀=a | ✓ DONE | `HardSphere/MatrixN1.lean` |
| M.3 | det(Q̂₀) ≠ 0 multi-component | ✓ (mod axiom) — unconditional `Q0_mat_phys_isUnit_det` from `Q0_moment_det_pos`; conditional Gershgorin `..._of_diag_dom` kept as historical partial | `HardSphere/MatrixQ0.lean`, `HardSphere/Q0DetRankTwo.lean` |
| M.4 | Unconditional `det(Q0_mat_phys) ≠ 0` for all `z > 0` | ✓ (mod axiom) — rank-2 reduction + M.5–M.8 all proved; the one open scalar inequality is the **named axiom `Q0_moment_det_pos`** (see Axioms table), which discharges `hdet` ⇒ unconditional `Q0_mat_phys_isUnit_det`. Retire axiom when proved | `HardSphere/Q0DetRankTwo.lean` |
| M.5 | `nAux_eq_mAux_div_two` (`nAux u = mAux u/2`) | ✓ DONE | `HardSphere/Q0DetRankTwo.lean` |
| M.6 | `one_add_half_sq_lt_cosh` (`1+u²/2 < cosh u` for `u>0`) | ✓ DONE | `HardSphere/Q0DetRankTwo.lean` |
| M.7 | `ratioPM_strictAntiOn` (`pAux/mAux` decreasing on `(0,∞)`) | ✓ DONE | `HardSphere/Q0DetRankTwo.lean` |
| M.8 | `moment_ad_le_bc` (**`bc ≥ ad`** for all N) | ✓ DONE | `HardSphere/Q0DetRankTwo.lean` |
| M.9 | g + a·exp(−z) = 1 — single-comp Baxter contact identity *(ex-4.2)* | ✓ DONE | `HardSphere/SingleCompIdentity.lean` |
| M.10 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) *(ex-B.2)* | ✓ DONE | `HardSphere/QhatDecomposition.lean` |
| M.11 | Coefficient algebra (1−g²)−a²c²=2acg *(ex-B.3)* | ✓ DONE | `HardSphere/SingleCompIdentity.lean` |


### Group B — FMSA_GA_matrix_mix Algebraic Foundation and Polynomial Determination *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| B.1 | Shifted-exponent integral | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| B.2→M.10 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) — *re-IDed to* **M.10** *(Group M, hard-sphere)* | ✓ DONE | see M.10 — `HardSphere/QhatDecomposition.lean` |
| B.3→M.11 | Coefficient algebra (1−g²)−a²c²=2acg — *re-IDed to* **M.11** *(Group M, hard-sphere)* | ✓ DONE | see M.11 — `HardSphere/SingleCompIdentity.lean` |
| B.4 | Origin BC automatic for FMSA_GA_matrix_mix | ✓ DONE | `YukawaDCF/B4OriginBC.lean` |
| B.5 | Degree bound exisr: deg P_{ij} ≤ 4 (no r^n for n≥N with N=4) | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.6 | Origin uniqueness: only A_{ij}=−E_{ij}(0) forced at r=0 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.7 | No contact BC: B,C,D,E^{(4)} not fixed by r=R_{ij} | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.8 | Laurent extraction: all five coefficients from R_{ij}(s) at s=0 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.9 | D_{ij} generically nonzero for unlike pairs | ✓ DONE (Option B, cubic-coefficient mechanism, axiom-clean): `p1_cubic_coeff`/`p2_cubic_coeff`/`exp_neg_cubic_rem`/`q0_entry_taylor3`/`b9_dij_cubic_nonzero` (concrete unlike cubic coeff = −133/2880 ≠ 0). Faithful `D_ij=R'_ij(0)/6` packaging moved to optional **MPOLY**. See Numerically verified section | `YukawaDCF/B5MixturePoly.lean` |
| B.10 | Exact degree: natDegree P_{ij} = 4 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |

### Group IB — Inner-Core Mediated Breakpoints *(breakpoints)*

*Split out of Group B once the mediated inner-core breakpoint work outgrew it.
**IB.1–IB.8 were formerly B.11–B.18**; the old B.19 (hard-sphere `λ_ij` kink) moved to Group OZ as
**OZ.18** (it is FMT hard-sphere, outside the Yukawa mediated chain). The Lean identifiers in
`YukawaDCF/InnerDecomp.lean` were made **task-ID-free** (e.g. `b11_…`→`terms_II_III_zero`),
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


### Group C — FMSA_GA_matrix_mix Consistency *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| C.1 | N=1: corrected formula = FMSA_pure | ✓ DONE | `YukawaDCF/SingleCompReduction.lean` |
| C.2 | N=1 like-pair inner formula bounded: `(1−G²₀₀)·exp(z(R−r))` ≤ C on (0,d) via exp-cancellation | ✓ DONE (`c1_n1_twoexp_bounded`) | `YukawaDCF/SingleCompReduction.lean` |
| C.5 | Leading Yukawa-pole residue of the first-order MSA amplitude. **CORRECTED:** exact single-tail residue is `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` (doubly-propagated), **not** `K·G` (the numerical shorthand is a leading-order approx; `K·G²` at N=1) | ◑ core (`c5_residue_eq_K_mul_Ginv`) + single-tail exact residue (`spectralAmp_residue`, `spectralAmp_residue_n1`) DONE; multi-tail + Wiener–Hopf derivation of `b_{ij}(s)` → **Group Y1** | `YukawaDCF/YukawaPoleResidue.lean`, `YukawaDCF/SpectralAmplitude.lean` |

### Group Y1 — First-Order Yukawa RDF/DCF (Wiener–Hopf derivation) *(yukawa_wh)*

*The ε¹-order analog of Group BAXTER (same **algebraic** Wiener–Hopf machinery — causal/anti-causal
split + support + residues, **not** the Hilbert transform of [LN] §6.3 which Mathlib lacks; see Y1.3
— applied to the first-order OZ equation `H̃₁(I−C̃₀)=(I+H̃₀)C̃₁`). Split off as the full
concrete-C.5 derivation. Source: **[LN]** §5–§6. Records: [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md).*

| Task | Title ([LN] ref) | Status | Lean file |
|------|-------|--------|-----------|
| Y1.1 | Complex Baxter matrix `Q̂₀(s):ℂ→Matrix` (Eq. 10–13) + inverse-as-`adj/det` (Eq. 14) | ✓ DONE (`q0_entry_c`, `Q0_mat_c`, `q0_entry_c_real`, `inv_apply_eq_adj_div_det`); closed-form Eq. 14 deferred | `YukawaDCF/Q0Complex.lean` |
| Y1.2 | Outer MSA DCF Laplace transform `U₁(k)_{ij}=K_{ij}e^{−ikR_{ij}}/(ik+z_{ij})` (Eq. 34/46) + Yukawa pole at `k=iz_{ij}` | ✓ DONE (`integral_Ioi_cexp`, `outerDCF_transform`) | `YukawaDCF/OuterDCF.lean` |
| Y1.3 | Wiener–Hopf one-sided projection isolating `B₁={T_U}^{[R,∞)}` (Eq. 55–66) — **algebraic split + support + residues, NOT Hilbert transform** (Mathlib lacks it; mirror `Splitting.lean`/Group BAXTER). Split a/b/c | ✓ **DONE (a/b/c, axiom-clean, real-space route)**. a: `q0_poly_support_subset`, `q0MixEntry`+`_support_subset`, `integral_/fourier_{Iic,Ici}_eq_of_support/_eq_full`. b: `causal_projection_real`/`_fourier` (support-orthogonality = `1_{[R,∞)}·`, no FT injectivity). c: `matrix_conj_residue_analytic`, `outer_residue`, `outer_residue_eq_spectralAmp_residue` (`Res T_U = Res b_{ij}`). Remaining = physics inputs (OZ eqn, concrete supports), not logic gaps | `WHSupports.lean` (a); `YukawaCausalProjection.lean` (b); `YukawaCausalResidue.lean`+`YukawaWienerHopf.lean` (c) |
| Y1.4 | Residue evaluation of the WH projection → `B₁(k)` (§6.4.1, Eq. 63–67) | ✓ DONE — residue-theorem step (`matrix_conj_residue`, `triple_apply`) + the Eq. 63 integrand now supplied by Y1.3c (`matrix_conj_residue_analytic`, `outer_residue`) | `YukawaDCF/YukawaWienerHopf.lean`, `YukawaCausalResidue.lean` |
| Y1.5 | Spectral amplitude `b_{ij}(s)` four-term/multi-tail (Eq. 73) + tie `A` to `Q̂₀(s)⁻¹` | ✓ **DONE** — single-tail (`spectralAmp_residue`/`_n1`), collapse (`bMulti_single_eq`/`_residue`), **general distinct-`z`** (`simplePole_offResidue`, `bMulti_residue` = per-pole term matching, `bMulti_residue_Qinv` = tie to `Q̂₀⁻¹` via `one_add_sub_one`) | `YukawaDCF/SpectralAmplitude.lean` |
| Y1.6 | First-order RDF `Ĥ₁=[Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (Eq. 68) + the exact C.5 residue corollary | ✓ DONE (`Hhat1`, `Hhat1_spec`, `Hhat1_residue`) | `YukawaDCF/YukawaWienerHopf.lean` |
| Y1.7 | inner-core `S₁(k)` (§9, Eq. 45) + origin constraint (Eq. 76) + contact matching (§7) — Group Y1 capstone | ✓ DONE (axiom-clean): `innerS1`/`innerS1_support_subset_Iio` (Eq. 45, Proof 2 anti-causal), `b1_causal_eq_U1_fourier` (§9.3, instantiates Y1.3b for concrete `S₁`), `origin_constraint_eq76` (Eq. 76, reuses P.2 + `eij_at_origin`), `innerS1_contact_value` (§7, reuses Group 5.1) | `YukawaDCF/YukawaInnerCore.lean` |


### Group MML — N=2 Mixture Mittag-Leffler Inner-Core *(yukawa_wh)*

For N=2, Q̂₀(z) and its 2×2 inverse (adj/det) are fully algebraic (Y1.1 DONE), so the HS-pole
residue `B_k = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` is provable without Y1.3 via `residue_of_simple_pole`.
This resolves the "no closed form for N=2" claim: the exact inner DCF **is** a convergent
Mittag-Leffler series; the only transcendental obstacle is the pole *locations* `s_k` (roots of
`det(Q̂₀)=0` — see **Group MZERO**), not the residues. Full assembly (MML.3) needs Y1.3 (done).
See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) Group MML.

| Task | Title | Status | Route / Lean file |
|------|-------|--------|-----------|
| MML.1 | Explicit 2×2 adjugate/det formulas for Q̂₀: `adj(Q̂₀)₀₁=−Q̂₀₀₁`, `[Q̂₀⁻¹]₀₁=−Q̂₀₀₁/det(Q̂₀)` | ✓ DONE (axiom-clean): `adjugate_fin_two_zero_one`, `inv_zero_one_eq`, `Q0_det_fin_two`, `Q0inv_zero_one` | `YukawaDCF/MixtureHSPoles.lean` |
| MML.2 | B_k residue formula: `Res_{s=s_k}[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` from `residue_of_simple_pole` + MML.1 | ✓ DONE (axiom-clean): `b_k_residue` (simple-zero data as hyps, matching `residue_of_simple_pole`) | `YukawaDCF/MixtureHSPoles.lean` |
| MML.3 | Full inner-DCF Mittag-Leffler assembly: `c^{inner}_{01}(r) = [Yukawa poles] + Σ_k B_k·e^{−s_k·r}` | ☐ not started (very hard; **Y1.3 ✓ DONE** — unblocked; remaining deps: MML.2, MZERO.1) | new `YukawaDCF/…` |

### Group MZERO — Mixture `det(Q̂₀)` Zero Family (HS-pole existence) *(yukawa_wh)*

**MZERO.2–MZERO.11 decompose MZERO.1** (`det(Q̂₀)` has ∞ many complex zeros; foundation done,
`MixtureHSZeros.lean`) into two independent routes — **Route A** Banach (MZERO.2–MZERO.7) and
**Route B** Rouché/Jensen (MZERO.8–MZERO.11); either route alone closes MZERO.1. The N=2
`det(Q̂₀)` is an exponential polynomial in `s` (quasi-polynomial) — the analog of `Qhat_complex`
for N=1 (POLE.3 `Qhat_complex_zeros_infinite`). See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) Group MZERO.

| Task | Title | Status | Route / Lean file |
|------|-------|--------|-----------|
| MZERO.1 | Infinitely many HS poles for N=2: `det(Q̂₀(s))=0` has infinitely many complex roots (analog of `POLE.3`) | ◑ **foundation DONE** (axiom-clean): `Q0_det_c_tendsto_one` (det→1 ⇒ non-constant), `q0_diag_c_tendsto_one`, `q0_offdiag_prod_tendsto_zero` (λ-cancellation), `Q0_det_c_not_identically_zero`, **+ holomorphy `Q0_det_c_differentiableAt` (s≠0)**. Full zero-family = POLE.3-scale, staged | `YukawaDCF/MixtureHSZeros.lean` |
| MZERO.2 | *(Python, POLE.2 analog — GO/NO-GO gate)* feasibility | ✓ **GO** (`verify_mixture_hs_poles.py`): quasi-periodic zero family (Δ Im≈π, 22 zeros to Im≈239), chord-Newton `g=s−F/F'(s1)` on `r=0.15` — both Banach conds hold uniformly, **K≈0.30–0.35 (does NOT drift to 1)**, self-map gap≪r(1−K). Banach path viable w/ chord-Newton | Banach; `verify_mixture_hs_poles.py` |
| MZERO.3 | generic chord-Newton Banach wrapper (Lipschitz self-map ⇒ ∃ zero); map-independent | ✓ DONE (axiom-clean): `chord_zero_exists_of_bounds` (via `ContractingWith.exists_fixedPoint'`) | Banach; `MixtureHSZeros.lean` |
| MZERO.4 | chord map `s↦s−F s/Fp1` + `fp ⟺ F=0` (unconditional; simpler than log-map, no branch-safety) | ✓ DONE (axiom-clean): `chordPhi`, `chordPhi_fixedPt_iff` | Banach; `MixtureHSZeros.lean` |
| MZERO.5 | magnitude bounds: `‖1−det′(s)/det′(s₁)‖ ≤ K` (chord-Lipschitz) + self-map `hstep` (`‖det(s₁)/Fp1‖ ≤ r(1−K)`) | ◑ **the remaining piece** — enters MZERO.6/MZERO.7 as explicit **hypotheses** (numerically validated by MZERO.2: `K≈0.30`, gap≪`r(1−K)`); a closed-form derivation is the open work. `det` differentiability on the disk IS proved (`Q0_det_c_differentiableAt`) | Banach (bulk) |
| MZERO.6 | `LipschitzOnWith K (chordPhi F Fp1) ball` (from `HasDerivAt`+MZERO.5 bound) + `MapsTo` disk-into-itself | ✓ DONE (axiom-clean): `chordPhi_lipschitzOnWith` (`Convex.lipschitzOnWith_of_nnnorm_deriv_le`), `mapsTo_closedBall_of_lipschitzOnWith_of_dist_le` | Banach; `MixtureHSZeros.lean` |
| MZERO.7 | single-`n` (`det_zero_exists_for_n`) → Im-spaced family (`Q0_det_c_pole_family_exists`) → distinctness ⇒ `{s:det=0}` infinite | ✓ DONE (axiom-clean, **conditional on MZERO.5 hyps**): `Q0_det_c_zeros_infinite` (`Set.Infinite`, via `Set.infinite_of_injective_forall_mem`) | Banach; `MixtureHSZeros.lean` |
| MZERO.8 | `det(Q̂₀)` meromorphic (for Jensen) | ✓ **DONE** (`det_meromorphicAt`/`det_meromorphicOn`): meromorphic algebra (`φ=entire/sⁿ` ratio) + `fun_prop` — **no continuation needed**, s=0 hard part dissolves | Rouché; `MixtureHSZeros.lean` |
| MZERO.9 | `divisor det ≥ 0` + Jensen-counting bound (`hJensen`) | ◑ **`divisor det U ≥ 0` now UNCONDITIONAL** — `det_divisor_nonneg` (axiom-clean). The "det has a limit at `0`" hyp of `det_divisor_nonneg_of_tendsto` is discharged by the Baxter removable values `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6` (`phi1_tendsto`/`phi2_tendsto`, from exp-Taylor `(e^w−1−w)/w²→½` `expTaylor2`, `(e^w−1−w−w²/2)/w³→⅙` `expTaylor3`) → `q0_entry_c_tendsto` → `detC_tendsto`. **These `s=0` Taylor coeffs are reusable for the inner-core poly / numerics (cf. MPOLY, B.9).** Only remaining Route-B piece: the Nevanlinna/Jensen finsum bound (`hJensen`, research-scale). Not blocking — Route A closes MZERO.1 | Rouché; `MixtureHSCounting.lean` |
| MZERO.10 | boundary growth → hypothesis | ✓ `DetBoundaryGrowth` + `detBoundaryGrowth_of_linear` (physical `≥c·R` ⟹ it, via `isLittleO_log_id`). Axiom-clean | Rouché; `MixtureHSCounting.lean` |
| MZERO.11 | Jensen capstone ⇒ ∞ many zeros | ✓ **structural capstone** `infinite_zeros_of_growth` + `detC_zeros_infinite_of_growth` (indep. Route-B proof of `Set.Infinite {detC=0}`, matches Route A, modulo `hJensen`+`DetBoundaryGrowth`). Axiom-clean; reuses `det_meromorphicOn` (MZERO.8) | Rouché; `MixtureHSCounting.lean` |


### Group MPOLY — Mixture Inner-Core Polynomial Coefficients *(yukawa_wh)*

*(optional)* Faithful inner-core polynomial coefficients `D_ij = R'_ij(0)/6` (and A,B,C,E⁴) via the
inside-core Laplace remainder `R_ij(s) = s⁵[e^{sR}·S_ij(s) − Y_ij(s)]` ([LN] §9.4, Eqs 106–120) —
promotes **B.9 Option B** (cubic-coefficient *mechanism*, DONE) to the exact `R'_ij(0)/6` identity.
Decomposed into MPOLY.1–MPOLY.5 (`YukawaDCF/MixtureLaurent.lean`); MPOLY.1 DONE, MPOLY.2–MPOLY.5
staged. **Scope correction:** the crux (MPOLY.5) is the closed-form `S_ij` from the transform eq
(§9.4.5) — HARD, overlaps Y1.3/MML.3, *not* the "independent/medium-hard" the older notes implied.
Fallback = land MPOLY.1–MPOLY.4 (abstract machinery). See [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) Group MPOLY.

| Task | Title | Status | Route / Lean file |
|------|-------|--------|-----------|
| MPOLY.1 | *(MPOLY pipeline)* order-4 Taylor of `q0_entry` = `δ − ρ·Ep₄·Pp₄` (the 5-coeff `q_ij(s)=q^[0]+…+q^[4]s⁴` structure, [LN] Eq 134) | ✓ DONE (axiom-clean): `q0_entry_taylor4` + new `p1_quartic_coeff`(`−σ⁶/720`), `p2_quartic_coeff`(`σ⁷/5040`), `exp_neg_quartic_rem`; extends B.9's `q0_entry_taylor3` by one order (`Real.exp_bound`) | `YukawaDCF/MixtureLaurent.lean` |
| MPOLY.2 | *(MPOLY pipeline)* reciprocal series `1/Δ_Q`: `δ₀=1/d₀`, `δₙ=−(1/d₀)Σₘ dₘδₙ₋ₘ` ([LN] Eq 136–137) | ☐ tractable, self-contained series algebra; no new deps | `MixtureLaurent.lean` |
| MPOLY.3 | *(MPOLY pipeline)* `Δ_Q=q₁₁q₂₂−q₁₂q₂₁` order-4 coeffs (from MPOLY.1) + `[Q̂₀⁻¹]₀₁=−q₁₂·(1/Δ_Q)` order-4 series ([LN] Eq 130; **analytic at 0** — `1/s⁵` pole is in `S_ij`, not here) | ☐ deps MPOLY.1, MPOLY.2, MML.1 | `MixtureLaurent.lean` |
| MPOLY.4 | *(MPOLY pipeline, **fallback endpoint**)* Laurent→coeff machinery: `R_ij=s⁵[e^{sR}S−Y]` analytic ⇒ `D=a^{(−4)}/3!` and unified `coeff[rᵐ]P=R^{(4−m)}(0)/(m!(4−m)!)` ([LN] Eq 105/120); `S`/`Y` **abstract** | ☐ tractable; extends B.8 `b8_poly_coeff_from_laurent` | `MixtureLaurent.lean` |
| MPOLY.5 | *(MPOLY pipeline, **CRUX**)* exact closed-form `S_01(s)` from the transform eq ([LN] Eq 128/129, §9.4.5) ⇒ `R_01` analytic ⇒ `D_01=R'_01(0)/6` matching B.9's `−133/2880`-style value | ☐ **HARD** — closed-form `S_ij` is the PDF's "real difficulty", overlaps Y1.3/MML.3; deps MPOLY.1–MPOLY.4, MML.1, Y1.5, [LN] §9.4.5 | new `YukawaDCF/…` |

### Group GA — FMSA_GA_matrix_mix Inner-Core Conditioning Failure *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| GA.1 | Unlike-pair two-exp base unbounded `K·exp(z·R)→∞`; additive HS-pole sum (≤ C/z²) cannot cancel it | ✓ DONE (`unlike_pair_twoexp_unbounded`, `hs_pole_additive_insufficient`) | `FMSAPoly/PolyApproxFails.lean` |
| GA.2 | *(opt.)* Off-diagonal `G_{01}(z)→0` exponentially as `z·(σ₁−σ₀)→∞`; structural cause of unlike-pair divergence | ✓ DONE, axiom-clean — mechanism (`g_mat_offdiag_decay'` Tendsto form / `g_mat_offdiag_decay` exp-bound form) + concrete N=2 discharge `g_mat_offdiag_decay_concrete` (`Q0_mat_phys 0 1/det→0`); rests on `p1/p2_tendsto_zero`⇒`Q0_mat_phys_offdiag01_tendsto_zero` + `Q0_mat_phys_det_tendsto_one` (`det→1`, **not** via the `Q0_moment_det_pos` axiom) | `YukawaDCF/OffDiagDecay.lean`, `HardSphere/Q0DetLimit.lean` |
| GA.3 | FMSA unlike-pair perturbation ratio unbounded: `‖c^(1)_{01}‖ / ‖c_HS_{01}‖ ≥ C·K·exp(z·R_{01}) → ∞` as `z·R → ∞` — FMSA lies outside its own small-parameter domain for large `z·R`. Corollary of GA.1 (`unlike_pair_twoexp_unbounded`): the ratio of the first-order Yukawa inner amplitude to the zeroth-order HS reference grows without bound, so the perturbation expansion is formally invalid at 2YK physical parameters. | ✓ DONE, axiom-clean — `perturbation_ratio_unbounded` (∀ `K>0`, fixed `z`-independent HS bound `M_HS>0`, target `M`: ∃ `(z,R)`, `M ≤ K·exp(z·R)/M_HS`); direct corollary of GA.1 at target `M·M_HS`; `M_HS` threaded as hypothesis (cf. `hs_pole_additive_insufficient`'s `hB`) | `FMSAPoly/PolyApproxFails.lean` |
| GA.4 | *(post-MML.3 Corollary)* Convergence radius of the unlike-pair MSA perturbation series in the Yukawa coupling `ε` satisfies `R_conv ≤ C·exp(−z·R_{01}) → 0` as `z·R_{01} → ∞`. Mechanism: the Mittag-Leffler poles of the exact inner DCF (MZERO.1/MML.3, roots of `det(Q̂₀(s))=0`) are at `Im(s_k) ≈ kπ/R` with `Re(s_k) ~ z` (from MZERO.2–MZERO.7's quasi-periodic family); as functions of the coupling `ε`, these poles migrate to `ε=0` with rate `exp(−z·R)`, so `R_conv ∼ exp(−z·R_{01})`. At 2YK parameters (`z₂≈9.3`, `R_{01}≈1.43`): `R_conv ≲ exp(−13.3) ≈ 2×10⁻⁶ ≪ |K₂| ≈ 2.3` — FMSA lies far outside the convergence disk. Completes the GA.3 argument: GA.3 shows the first-order term is large; GA.4 shows the full series diverges at physical parameters. | ☐ not started; depends on MZERO.1 (pole existence) + MML.3 (Mittag-Leffler assembly) + the `ε`-dependence of `det(Q̂₀)` zeros (needs parameterisation of `Q̂₀(s,ε)` in the coupling). Note: the coupling `ε` enters `Q̂₀` through `K_t = βε_t·…`; the `ε`-analytic structure of the det zeros follows from holomorphy in `ε`. | new `YukawaDCF/…` |


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
| OZ.2 | g₀_HS via OZ fixed point | ◑ fixed-point framework (`oz_h`, `oz_fixed_pt_unique`) live and reused by the Fourier line. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/PYOZ_GHS.lean` |
| OZ.2b | Gap A: exterior 3D-OZ equation for `oz_h` (`oz_h_satisfies_conv_ext`) | ✓ DONE, transform-independent — reused verbatim by OZ.7. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/OZExteriorBridge.lean` |
| OZ.3 | g₀_HS via OZ Laplace inversion | ◑ conditional on OZ.2 + `oz_h_exterior_regularity` axiom (see CONTACT.5) | `HardSphere/PYOZ.lean`, `HardSphere/JumpAsymptotic.lean` |
| OZ.4 | Linearised OZ: Ĥ¹=Ĉ¹·S₀ | ✓ DONE | `HardSphere/PYOZ.lean` |
| OZ.6 | Radial sine/Fourier transform convolution theorem | ✓ DONE, no axiom | `HardSphere/RadialFourier.lean` |
| OZ.7 | Fourier-domain exterior OZ equation (Gap A ∪ Gap B) | ✓ DONE, conditional only on OZ.9 (`hcore`) | `HardSphere/OZFourierBridge.lean` |
| OZ.8 | Closed-form sine-transform formula for `c_HS` + bridge to `C_HS_laplace`/`S0` via `s↔-ik` | ✓ DONE (Parts A+B), no axiom/sorry. Bridge to `g0_HS_contact_value` — see Group CONTACT `CONTACT.1`/`5` | `HardSphere/RadialFourierCHS.lean` |
| OZ.9a | PY core closure (Gap B) for `r < σ` — promoted to a named, numerically-verified axiom | ✓ DONE (axiom `oz_core_closure`, Route A; not proved from Mathlib real-analysis — needs Group BAXTER's full construction, staged not started) | `HardSphere/PYOZ_GHS.lean` |
| OZ.9b | `oz_fourier_oz_eq_of_PY_core`: OZ.7 specialized to consume `oz_core_closure` instead of an externally-supplied `hcore` — most complete/trustworthy result in the whole OZ chain (Gap A + convolution theorem + Gap B all proved/axiomatized by name, only routine integrability hypotheses remain) | ✓ DONE | `HardSphere/OZFourierBridge.lean` |
| OZ.10 | Uniqueness of the OZ fixed point (`oz_fixed_pt_unique`) | ◑ axiom — dilute proved (OZ.10-dilute); mid/high density is **TRUE** (hard spheres have no spinodal) but same-core as the BAXTER Wiener–Hopf line, **not** compact Fredholm (`oz_linear_op` K is a non-compact half-line Wiener–Hopf operator; Mathlib *has* compact Fredholm but it doesn't apply). No general WH theory needed: factorization = Baxter factorization (BAXTER.3); missing piece = POLE.4's explicit `h_explicit` inverse plus Group OZFIX's assembly. Gated by the BAXTER line. | `HardSphere/PYOZ_GHS.lean` |
| OZ.10-dilute | Dilute-regime (`eta<1`, `24·eta·bracket<1`, i.e. `eta≲0.088`) Banach existence/uniqueness for `oz_fixed_pt_unique`, exterior-only | ✓ DONE — `oz_fixed_pt_unique_dilute`, genuine theorem, no axiom/sorry. Mid/high density (`eta≈0.3–0.5`) is TRUE but gated by the BAXTER line (K non-compact ⇒ not compact Fredholm; `24η·bracket` = K's spectral radius = the dilute threshold; Baxter factorization + POLE.4/Group OZFIX explicit inverse), not attempted here — see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.10-dilute. | `HardSphere/OzFixedPtDilute.lean` (+ `c_HS_abs_t2_integrableOn` in `HardSphere/PYDCF.lean`) |
| OZ.18 | Hard-sphere `λ_ij` kink: `c_HS,ij` is C⁰ (slope kink) at `λ_ij=\|d_i−d_j\|/2`, unlike pairs *(formerly B.19)* | ✓ DONE — C⁰ + both one-sided slopes proved; genuine kink conditional on core-slope≠0 (numerical) | `HardSphere/CHSKink.lean` |

**Tasks OZ.5, OZ.11–OZ.17 (and `OZ.13`) have moved to Group BAXTER**

### Group BAXTER — Baxter Q-Factor & Wiener–Hopf Factorization Foundations *(hard_sphere)*

*Depends on Group OZ above (uses `oz_h`, `c_HS`, `radial_fourier`, `oz_core_closure`, etc.);
Group OZ does not depend on this group. Feeds Groups CONTACT/POLE/OZFIX below. See
[proof_notes_baxter.md](proof_notes_baxter.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `BAXTER.1` | Baxter real-space convolution identity *(formerly OZ.5)* | ✓ DONE | `HardSphere/BaxterRealSpace.lean` |
| `BAXTER.2` | Re-derive Baxter's second relation (Route B) from a primary source *(formerly OZ.11)* | ☐ not started — residue-series construction validated 3 independent ways (ground truth, pole-growth law, real-space OZ check); staged into Group POLE (`POLE.1`–`5`) + Group OZFIX (`OZFIX.1`–`8`) | — |
| `BAXTER.3` | Baxter's Wiener–Hopf factorization `(1-ρQ̂(k))(1-ρQ̂(-k)) = 1-ρĈ_sine(k)` *(formerly OZ.12)* | ✓ DONE — `baxter_wiener_hopf_factorization`, genuine theorem, no sorry/axiom; uses existing `q0_poly` | `HardSphere/BaxterWienerHopf.lean` |

### Group CONTACT — `g0_HS_contact_value` via the Jump-Asymptotic Route *(hard_sphere)*

*Split from Group BAXTER (`BAXTER.4`–`8`). Depends on Group BAXTER (`BAXTER.1`–`3`)
and Group OZ (`oz_h`, OZ.8/OZ.9b). See [proof_notes_contact.md](proof_notes_contact.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `CONTACT.1` | Derive `g0_HS_contact_value` from OZ.8's Fourier-domain closed form (full residue inversion) *(formerly `BAXTER.4`/OZ.13)* | ☐ deliberately parked — fully absorbed into `BAXTER.2`'s scope, not independent | — |
| `CONTACT.2` | Extract `g0_HS_contact_value` via a jump-asymptotic argument on `Ĥ(k)`'s large-`k` behavior *(formerly `BAXTER.5`/OZ.14)* | ✓ DONE as a whole — split into `CONTACT.3`/`4`/`5`, all three done | — |
| `CONTACT.3` | General jump-asymptotic lemma for `radial_fourier`: `f k = 4πσJ·cos(kσ)/k² + o(1/k²)` for `f` with jump `J` at `σ` *(formerly `BAXTER.6`/OZ.15)* | ✓ DONE — `radial_fourier_jump_asymptotic`, genuine theorem, no sorry/axiom; via one IBP + Mathlib's Riemann-Lebesgue lemma | `HardSphere/JumpAsymptotic.lean` |
| `CONTACT.4` | Concrete closed-form asymptotic of `Ĥ(k)=Ĉ(k)/(1-ρĈ(k))`: leading coefficient `4πσ(1+η/2)/(1-η)²` *(formerly `BAXTER.7`/OZ.16)* | ✓ DONE — `Hhat_closed_asymptotic`, genuine theorem, no sorry/axiom | `HardSphere/RadialFourierCHS.lean` |
| `CONTACT.5` | Assembly: apply `CONTACT.3` to `oz_h`, match against `CONTACT.4`, conclude `g0_HS_contact_value` *(formerly `BAXTER.8`/OZ.17)* | ✓ DONE — `g0_HS_contact_value_of_oz_h_regularity` (conditional theorem, no sorry/axiom) **plus** its unconditional consequence: the bare `g0_HS_contact_value` axiom is now **retired**, replaced by the named regularity axiom `oz_h_exterior_regularity` bundling `CONTACT.5`'s `oz_h` hypotheses, from which `theorem g0_HS_contact_value` is proved (`#print axioms` → `oz_core_closure`, `oz_fixed_pt_unique`, `oz_h_exterior_regularity`; no `g0_HS_contact_value` axiom). Retires OZ.3's physical-number axiom. | `HardSphere/JumpAsymptotic.lean` |

### Group POLE — Complex-Analytic Pole/Residue Construction for the Baxter Q-Factor *(hard_sphere)*

*Split from Group BAXTER (`BAXTER.9`,`10`,`11`,`12`,`14`). Depends on Group BAXTER
(`BAXTER.1`–`3`); feeds Group OZFIX. See [proof_notes_pole.md](proof_notes_pole.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `POLE.1` | `Qhat_complex : ℂ → ℂ` in closed form, proved entire *(formerly `BAXTER.9`)* | ✓ DONE — `Qhat_complex_entire` + `Qhat_complex_formula`, genuine theorems, no sorry/axiom; entireness via `entire_poly_exp_integral` (dominated-convergence differentiation under the integral), closed form via new `zeta0`/`zeta1`/`zeta2` moment lemmas; numerically cross-checked against the raw integral and against `BAXTER.3`'s real-`k` formulas | `HardSphere/BaxterZeros.lean` |
| `POLE.2` | Numerical/symbolic feasibility check for the Banach-pole-existence strategy *(formerly `BAXTER.10`)* | ✓ DONE — **GO**: uniform contraction bound (`max_L→0.369`, margin `≈63%`) found for `n≥10`, robust across `η∈[0.05,0.45]` | — (Python, not Lean) |
| `POLE.3` | Pole existence in Lean via Banach contraction *(formerly `BAXTER.11`)* | ✓ DONE (conditional) — `Qhat_complex_zeros_infinite`, no sorry/axiom; all magnitude bounds, branch-safety, Lipschitz/MVT, Banach wiring, distinctness/infinitude proved unconditionally for general `η∈(0,1),σ>0,ρ>0`; one explicit "good guess" hypothesis (`hstep`, numerically validated by `POLE.2`) not yet discharged for the specific asymptotic guess formula. **✅ `G_baxter`'s zero condition double-counted-`ρ` bug FIXED** (was `1-ρ·Qhat_complex(k)=0`, corrected to `1-Qhat_complex(k)=0`; `baxterP0/1/2` unchanged, `Dpoly`'s affine coeffs lose one `ρ` power, `hrho` strengthened `rho≠0→0<rho` throughout `BaxterPoles.lean`/`BaxterResidue.lean`/OZFIX files). Full project `lake build` green; `G_baxter`'s own first pole now matches `BAXTER.2`'s ground truth `6.058015+1.436794i` to machine precision; `h_explicit(2.0)` converges to the known value `0.005663`. See `proof_notes_pole.md` `POLE.3` for the full writeup. **Group OZFIX's aggregate identity (`OZFIX.9`) was subsequently re-scoped on the corrected family and CONFIRMED — the earlier `~50%` residual was truncation (N=11 poles at slow-converging `r=1.5`); per-pole exact for `r≥2σ`, slowly convergent (`~1/N`) for `σ≤r<2σ`. See `proof_notes_ozfix.md` `OZFIX.9`.** | `HardSphere/BaxterPoles.lean` |
| `POLE.4` | Residue formula + convergence for `h_explicit` *(formerly `BAXTER.12`)* | ✓ DONE — `residue_of_simple_pole`, `Chat_complex`, `G_baxter_deriv`, `Hhat_residue_at_pole`, `G_baxter_zero_mirror`, `h_explicit`/`h_explicit_term`/`h_explicit_summable`, and `G_baxter_pole_family_exists` all done; `POLE.5` (below) closes the one remaining gap (the magnitude-bound hypothesis, now proved rigorously not just numerically). No sorry/axiom. | `Analysis/ResidueAtSimplePole.lean`, `HardSphere/BaxterResidue.lean`, `HardSphere/RadialFourierCHSComplex.lean`, `HardSphere/BaxterPoles.lean` |
| `POLE.5` | Rigorous `n^{1-2r/σ}` magnitude bound + concrete `h_explicit` instantiation *(formerly `BAXTER.14`)* | ✓ DONE — `residue_term_norm_bound` (rigorous `‖residue_term(k)‖≤C·‖k‖^{1-2r/σ}`, assembled from new `Npoly_upper_bound`/`Dpoly_upper_bound`, `G_baxter_deriv_lower_bound_of_zero`/`G_baxter_neg_lower_bound` (direct lower-bound versions of the old non-vanishing theorems), `abs_exp_neg_ikn_sigma_lower/upper`, `abs_exp_ikr_eq_rpow`/`abs_exp_ikr_upper_of_zero`, `Chat_F_norm_bound`/`Chat_complex_norm_bound`, and two existential wrappers `exists_hkN_hkT_threshold`/`exists_D_for_exp_neg_bound` working around `baxterP0/1/2`'s cross-file privacy); `h_explicit_term_norm_bound` (pole+mirror pairing); `h_explicit_summable_of_pole_family` (general `Summable` theorem for any zero family with linear `‖k_n‖` growth — wiring to `G_baxter_pole_family_exists_growth`'s concrete witness DONE as `POLE.6`). No sorry/axiom (one `set_option maxHeartbeats` bump, a performance not correctness issue). | `HardSphere/BaxterResidue.lean`, `HardSphere/BaxterPoles.lean`, `HardSphere/RadialFourierCHSComplex.lean` |
| `POLE.6` | Concrete pole family wired into `h_explicit`'s summability | ✓ DONE (axiom-clean) — `h_explicit_summable_concrete` consumes `G_baxter_pole_family_exists_growth`'s conclusion tuple (existentially, since that theorem's hypotheses mention the `private` `baxterP0/1/2` — same cross-file-privacy pattern as POLE.5's wrappers) + a new centre hypothesis `hk1im : r ≤ Im(k1 n)`, and yields an injective, `G_baxter`-zero, upper-half-plane family with `Summable (h_explicit_term …)` for every `y>σ`. **Fixes the `hkfam_im` hidden gap**: `_growth`'s output lacked `0 ≤ Im(g n)` (which every `h_explicit` lemma consumes) — recovered via `pole_family_im_nonneg` (`Complex.abs_im_le_norm`). Conditional only through `hfam` — fires unconditionally the moment POLE.3's `hstep` lands. See [proof_notes_pole.md](proof_notes_pole.md) `POLE.6`. | `HardSphere/HExplicitConcrete.lean` |
| `POLE.7` | Discharge `hstep` via the derived log-lift guess | ◐ in progress — **scoping GO (2026-07-15)**: fit-free guess `k1(n)=2πn/σ+(i/σ)·ln‖Npoly(xₙ)/Dpoly(xₙ)‖` (supersedes the fitted `2ln x−2.12`); residual `≈3.5·ln(xₙ)/xₙ→0`, elementary mean-value chain `res ≤ sup\|φ′\|·\|k1−xₙ\|+\|arg(N/D)\|/σ` is tight; vs Lean's `hC` K-formula + admissibility, `hstep` holds for `n≥N` with explicit `N=4/4/6/17` at `η=.05/.1/.3/.45` (`r=1`, checked to `n=10⁴`); branch safety `Re(N/D)≥1.1`; chord-route (`ChordPoleFamily`, shared w/ MZERO.5) works at `r=0.3` (`K≈0.35`, `N=17/15/9/2`). Lean plan = 5 sub-lemma clusters (real-axis N/D bounds; `\|φ′\|≤c/‖k‖`; arg bound; branch safety; MVT assembly). See [proof_notes_pole.md](proof_notes_pole.md) `POLE.7`. | `HardSphere/BaxterPoleGuess.lean` (new) |

### Group OZFIX — `h_explicit`'s Closed-Form Assembly into `OzFixedPt` *(hard_sphere)*

*Split from Group BAXTER (`BAXTER.13`/`15`) — both retired, replaced by the eight
topic-scoped tasks below. Depends on Group BAXTER (`BAXTER.1`–`3`) and Group POLE. See
[proof_notes_ozfix.md](proof_notes_ozfix.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `OZFIX.1` | Strategy scoping (`B.0`) + zeroth-moment inner integral (`B.1`/`B.2`) | ✓ DONE — `moment0_formula`; `B.0` (pole-family completeness) resolved as not needed for the termwise strategy. No sorry/axiom. | `HardSphere/BaxterResidue.lean` |
| `OZFIX.2` | Complex-`k` Wiener–Hopf bridge (`OZFIX.6`'s key prerequisite) | ✓ DONE — `baxter_wiener_hopf_complex`, via analytic continuation/identity theorem, unconditional, no new axiom | `HardSphere/BaxterWienerHopfComplex.lean` |
| `OZFIX.3` | Sum/integral interchange machinery (`B.3`–`B.4` core) | ✓ DONE — `h_explicit_series_hasDerivAt` (`hasDerivAt_tsum_of_isPreconnected` payoff), `h_explicit_series_integral` (two-sided FTC, `lo>σ`), `s_mul_h_explicit_integral` (closed-form value `oz_linear_op` needs). No sorry/axiom. | `HardSphere/BaxterResidue.lean` |
| `OZFIX.4` | The `σ`-boundary case | ✓ DONE (conditional on `hint`) — `residue_term_norm_bound` weakening, `Hterm_uniform_summable_bound_of_pole_family`, `h_explicit_series_integral_from_sigma` (one-sided FTC); `hint` is a confirmed-genuine integrability gap, not Lean bookkeeping (see `proof_notes_ozfix.md` for the `g0_HS_contact_value`/Group CONTACT investigation that ruled out a quick reuse). No sorry/new axiom. | `HardSphere/BaxterResidue.lean` |
| `OZFIX.5` | Outer `t`-integral assembly (`B.3` proper) | ✓ DONE — `oz_forcing_add_linear_op_h_explicit_eq_outer_integral` eliminates the raw inner `∫s` integral entirely (closed `Hterm` form), case split `r-t≷σ` via `inner_h_explicit_integral_bridge`; no sorry/axiom | `HardSphere/OzFixedPtHExplicit.lean`, `HardSphere/BaxterResidue.lean` |
| `OZFIX.6` | Algebraic collapse (`B.5`, the mathematical payoff) | ☐ not started — numerically scoped: the per-pole/termwise route is FALSE (pole-5 ratio `-2.72`, not `1`); needs either an `oz_forcing` residue expansion or a full-series Fourier-inversion route, neither attempted; aggregate target itself well-confirmed numerically | `HardSphere/BaxterResidue.lean` |
| `OZFIX.7` | Regularity (`B.6`): `ContinuousOn`+boundedness | ✓ DONE on `(σ,∞)`/`[r0,∞)`, `r0>σ` — `h_explicit_continuousOn_Ioi`, `h_explicit_bounded_on_Ici`, no sorry/axiom. Closed endpoint `r=σ` remains open (same `σ`-boundary gap as `OZFIX.4`/`6`) | `HardSphere/HExplicitRegularity.lean` |
| `OZFIX.8` | Final assembly (`B.7`): invoke `oz_fixed_pt_unique` | ✓ DONE, conditional on `hcollapse` (`OZFIX.6`) + `hcont_sigma` (`OZFIX.7`'s σ-endpoint gap) — `oz_h_eq_spliced_h_explicit`, `#print axioms` only `oz_fixed_pt_unique` beyond the standard three; retiring `oz_core_closure` itself is a separate Phase C follow-on | `HardSphere/OzFixedPtHExplicitFinal.lean` |
| `OZFIX.9` | `hcollapse` via **Route A** (`oz_forcing` termwise Mittag-Leffler expansion), alternative to Route B (whole-series `radial3d_conv` + Mathlib-axiom, done elsewhere) | ☐ **Direction (user-confirmed 2026-07-15): Route B closes `hcollapse`** (favorable axiom trade — physics `oz_core_closure` → standard/reusable residue axiom); Route A kept as the future *unconditional* (axiom-free) path, `r≥2σ` part now tractable. **UNBLOCKED — the POLE fix resolved the aggregate; Route A viable but research-scale (≈ Route-B difficulty).** Re-scoped against the now-fixed `G_baxter=(-ik)³(1-Q̂)`: (a) anchor `h_explicit(2.0)=0.005688` = ground truth; (b) **aggregate `oz_forcing+oz_lin=h_explicit` HOLDS** — exactly per-pole for `r≥2σ` (`oz_forcing=0`; the earlier "−2.72 per-pole false" was the wrong pole family), slowly convergent (`~1/N`) for `σ≤r<2σ`. The earlier "~50% fail" was **truncation** (N=11), now retracted (both here and in `proof_notes_pole.md`). (c) Route A `oz_forcing=Σ Re[H_n−L_n]` holds numerically but `R_n=H_n−L_n` is **not** a clean `ô_forcing(k_n)` coefficient (ratio oscillates), so it's the aggregate rearranged, not obviously cheaper than Route B. Realistic path: `r≥2σ` per-pole tractable; `σ≤r<2σ` needs the genuine termwise argument. | new `HardSphere/OzForcingResidue.lean` |
| `OZFIX.10` | `hcollapse` via **Route B** (growing-contour Fourier inversion: `∫_{-R}^{R} k·Ĥ·e^{ikr} → 2πi·Σres`, then back to `radial3d_conv`) — the user-confirmed closing route (see `OZFIX.9`) | ◑ **infrastructure DONE, arc-vanishing OPEN.** Done (2026-07-15, `lake build` clean): (a) **`jordan_lemma_arc_bound`** (`Analysis/JordanLemma.lean`) — quantitative Jordan's lemma `‖∫_arc g·e^{iaz}‖≤πM/a`, **proved outright, NO axiom** (`Real.mul_le_sin` + ML-inequality + `Complex.norm_exp` + FTC); (b) **half-disk residue theorem** — axiom `halfDiskBoundary_eq_sum_of_small_circles` + genuine theorem `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles` (`Analysis/ContourDeformation.lean`, see Axioms table + `MATH_AXIOMS.md`); (c) Step-0 numerics: `residue_term` = true residue of `k·Ĥ·e^{ikr}` to machine precision, `2πi` normalization exact. **OPEN**: `\|k·Ĥ(k)\|` *grows* `≈1.745·R` on the arc (numerically confirmed, plateau over `θ∈(10°,170°)`), so Jordan's crude sup-bound gives a growing estimate; the arc's real `O(1/R)` decay (confirmed to `N=55`, `R≈349`) is **oscillatory cancellation** — needs a non-stationary-phase/Van-der-Corput estimate, deliberately NOT axiomatized (would assume the theorem's hardest part). See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.10`. | `Analysis/JordanLemma.lean`, `Analysis/ContourDeformation.lean`; application file TBD |

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

---

*Numerical verification tasks are in `../todo/todo_numerical.md`.*
