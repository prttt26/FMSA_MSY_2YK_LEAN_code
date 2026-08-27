# Foundations (非闭包依赖基础) — task status

Hard-sphere / Ornstein–Zernike / Baxter / Wiener–Hopf / thermodynamics infrastructure that **every**
closure builds on and that is independent of *which* closure. No scope-gate `.lean` file — this track
is depended-upon, not a claim track; its results are gated indirectly through the three claim tracks.

↩ **Index:** [`todo_lean.md`](todo_lean.md) — layer map, project-wide axiom/sorry ledger, category index.

**Detailed records:**
- [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) — Groups 2, 3, OZ
- [proof_notes_baxter.md](proof_notes_baxter.md) — Group BAXTER
- [proof_notes_contact.md](proof_notes_contact.md) — Group CONTACT
- [proof_notes_pole.md](proof_notes_pole.md) — Group POLE
- [proof_notes_ozfix.md](proof_notes_ozfix.md) — Group OZFIX
- [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) — Group M
- [proof_notes_hs_mixture.md](proof_notes_hs_mixture.md) — MIXCHS (HS-mixture c_HS)
- [proof_notes_free_energy.md](proof_notes_free_energy.md) — Groups F, FW
- [MATH_AXIOMS.md](MATH_AXIOMS.md) — Group MA registry

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
| MA.1 | Founding pieces (re-filed from the `OZFIX.10` Route B effort): circular + half-disk contour-deformation axioms, their derived residue-sum theorems, and the… | ✓ DONE | `Analysis/ContourDeformation.lean`, `Analysis/JordanLemma.lean` |
| MA.2 | **Mittag-Leffler expansion** (simple poles + bounded on expanding circles ⇒ circle-grouped pole expansion) | ✓ DONE (**proved from the circle-deformation axiom; its own axiom RETIRED**) — ~430 lines. First stated with an *ordered*-partial-sum conclusion, which is **false** (pole-pair-splitting counterexample); fixed to the classical grouped form. See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 2. | `Analysis/MittagLeffler.lean` |
| MA.3 | **One-pole Fourier kernel** `∫_{-R}^{R} e^{ixr}/(x-k₀)dx → 2πi·e^{ik₀r}` (`Im k₀>0`, `r>0`) — genuine theorem, `#print axioms` = halfDisk axiom + standard three; with… | ✓ DONE (no new axiom) | `Analysis/MittagLeffler.lean` |
| MA.4 | **Van der Corput first-derivative test** (`\|φ'\|≥λ`, `φ'` monotone ⇒ `‖∫e^{iφ}ψ‖ ≤ (3/λ)(‖ψ(b)‖+∫‖ψ'‖)`) | ✓ DONE (**proved; axiom RETIRED**) — ~370 lines. The textbook `C¹` form is **true but unprovable** here (needs Stieltjes IBP / 2nd MVT, neither in Mathlib); restated at `C²` (no consumers ⇒ free). See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 3. | `Analysis/VanDerCorput.lean` |
| MA.5 | **Jensen counting bound** (no poles + finite divisor support ⇒ `circleAverage(log‖f‖) ≤ M·logR+C`) | ✓ DONE (**proved, no axiom**) — ~90 lines from Mathlib's Jensen. First stated over the *literal* zero set, which is **false** under junk values; fixed to divisor support. Discharges `MZERO.11`'s `hJensen`. See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 1. | `Analysis/JensenCounting.lean` |
| MA.6 | Relocate misfiled pure math `HardSphere/→Analysis/`: `ResidueAtSimplePole.lean`, `BanachPoleFamily.lean` (+5 consumer imports; namespaces kept) | ✓ DONE (`lake build` green) | `Analysis/ResidueAtSimplePole.lean`, `Analysis/BanachPoleFamily.lean` |
| MA.7 | **Sokhotski–Plemelj boundary values** (upper, integrated form; P.V. existence as hypothesis) — user-requested pre-placement, numerically pre-checked (3 test functions,… | ✓ DONE | `Analysis/SokhotskiPlemelj.lean` |
| MA.8 | **Homotopy-invariance Cauchy** (free-homotopy-through-loops of loops in open `U`, `f` holomorphic ⇒ equal contour integrals) — was pre-placed as the intended future… | ✓ **RETIRED to a THEOREM 2026-07-24 — axiom removed** (gap closed upstream). Mathlib `v4.31.0` gained the Poincaré lemma for `1`-forms (`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`, `CurveIntegral/Poincare.lean`), so the "Mathlib lacks homotopy/winding machinery" justification is stale. Proved axiom-free in `Analysis/ContourHomotopy.lean`: … [detail in linked notes] | `Analysis/ContourHomotopy.lean`, `Analysis/HomotopyInvariance.lean` |
| MA.9 | **Radial Fourier inversion** — left inverse of `radial_fourier`: `f(r) = (1/(2π²r))∫₀^∞ k·F(k)·sin(kr)dk`, plus the antiderivative form a jump discontinuity forces (`k·F… | ✓ DONE (**never axiomatized — proved** from Mathlib's `fourierInv_fourier_eq`; fully closed, no `hC` hypothesis). Also gives reusable `fourier_of_odd`/`fourier_of_even` bridges. The `4π/k` cancels ⇒ radial inversion = sine inversion + ~20 lines. First antiderivative form had an **unsatisfiable `∀ k` hypothesis** (vacuous at the junk `k=0`); fixed to `∀ k ∈ Ioi 0`. See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 4. | `Analysis/RadialFourierInversion.lean` |
| MA.10 | **Volterra integral equation of the second kind — existence & uniqueness** (continuous kernel, on compacts): `u(r) = g(r) + ∫ᵃ^r K(r,t)·u(t)dt` has a unique solution… | ✓ **DONE 2026-07-17 (never axiomatized — proved, axiom-clean, ~130 lines).** Route: **iterate bound, not Bielecki** (reuses `C(Icc a b, ℝ)`'s existing metric — no new normed structure). Engine `volterra_iterate_bound`: `|Tⁿu(r)−Tⁿw(r)| ≤ Mⁿ(r−a)ⁿ/n!·dist u w` — the local `(r−a)ⁿ` (not `(b−a)ⁿ`) is what lets the induction close; sup form is a one-line weakening. Then … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.10. | `Analysis/Volterra.lean` |
| MA.11 | **Argument principle / zero-count** — for `f` meromorphic on a disc, `(1/2πi)∮_{C(c,R)} f'/f = Z − P` (interior zeros minus poles, each weighted by order).… | ✓ **DONE 2026-07-17 — DERIVED THEOREM, no new axiom** (`Analysis/ArgumentPrinciple.lean`, ~90 code lines). As predicted, it is **MA.1 applied to `F := logDeriv f`**. The genuinely new content is the per-circle bridge `circleIntegral_logDeriv_zpow_smul_eq`: `∮_{C(k,r)} logDeriv((·−k)^n·g) = 2πi·n` for `g` analytic-nonzero on the disk — **axiom-clean** (`#print axioms` = … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.11. | `Analysis/ArgumentPrinciple.lean` |
| MA.12 | **Krein / Wiener–Hopf half-line unique solvability** — would let `OZ.10` (`oz_fixed_pt_unique`) be derived. Scoping brief in [MATH_AXIOMS.md](MATH_AXIOMS.md). | ✓ **DONE 2026-07-17 — PROVED, no new axiom** (`Analysis/WienerHopf.lean`, ~110 code lines, axiom-clean). **The spec's premise was wrong:** it assumed axiomatization because Mathlib lacks WH/Toeplitz/index/winding theory (confirmed absent — all unformalized in `docs/1000.yaml`). That holds for the *full index theorem* but **not** for the recommended (Q2) **positive-symbol** … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.12. | `Analysis/WienerHopf.lean` |
| MA.13 | **Paley–Wiener / Wiener-algebra renewal decay** — a right-compactly-supported kernel whose Laplace symbol `1−q̂(z)` is nonvanishing on `{Re z ≥ 0}` gives a decaying… | ✓ **AXIOM (legitimate) + WIRED, 2026-07-18.** Unlike MA.12, this is a **genuine axiom**: recon confirmed Mathlib has no Wiener `1/f`/Wiener-algebra inversion, no L¹ convolution Banach algebra, no Laplace transform, no Paley–Wiener/renewal theory — and **no elementary shortcut** (the classical proof needs the Gelfand-spectrum identification of the Wiener algebra with the … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.13. | `Analysis/WienerRenewal.lean`, `HardSphere/BaxterRenewalDecay.lean` |
| MA.14 | **Hermite–Biehler root location** — `Q̂≠1` on the closed lower half-plane (all physical η<1) ⇒ every Baxter pole in the open UHP; supplies MA.13's symbol-nonvanishing… | ✓ **AXIOM (bounded core) + END-TO-END LOOP CLOSED, 2026-07-18** (processed by another session). The axiom was **shrunk** from the whole closed LHP to the bounded core `G_baxter_ne_zero_on_lower_core` on `{Im k≤0, k≠0, ‖Npoly‖≤‖Dpoly‖}`: the outer region became the axiom-clean THEOREM `G_baxter_ne_zero_of_norm_dominant` (a zero forces `‖Npoly‖=‖Dpoly‖·e^{σ·Im k}≤‖Dpoly‖`; the … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.14. | `HardSphere/BaxterHermiteBiehler.lean`, `HardSphere/BaxterExteriorRegularityGeneral.lean` |
| MA.15 | **Bounded (`L∞`) Wiener–Hopf injectivity, radial shell operator** — arbitrary kernel `C` supported in `[0,σ]`, coercive symbol `1−ρĈ ≥ ε>0` ⇒ `I−K` injective on bounded… | ✓ **AXIOM, abstracted + migrated to `Analysis/` 2026-07-19.** Created by abstracting the former OZ.10 axiom `oz_linear_op_bounded_injective` (a domain-referencing math axiom) into a project-independent statement; that concrete result is **now a THEOREM** instantiating it at `C := c_HS` (support from `c_HS_outer`; `radial_fourier` and `oz_linear_op` unfold definitionally). … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.15. | `Analysis/RadialWienerHopf.lean` |
| MA.16 | **Leibniz rule with a variable upper limit AND an `r`-dependent integrand** — `d/dr ∫_a^r K(r−t)·φ(t)dt = K 0 · φ r + ∫_a^r K'(r−t)·φ(t)dt`. Consumer: `OZFIX.25` (★DIFF). | ✓ **DONE 2026-07-19 — PROVED, no new axiom** (~200 lines, axiom-clean). `K` need only be differentiable **a.e.**; regularity across the kink is carried by one `LipschitzOnWith` hypothesis on the window of arguments that occur. **Split at the base point** (`∫_a^r = ∫_a^{r₀} + ∫_{r₀}^r`) rather than the spec's `r ↦ (r,r)` chain rule, which would have needed *joint* differentiability; the … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.16. | `Analysis/ConvolutionLeibniz.lean` |

### Group 2 — Hard-Sphere Baxter Factor *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 2.1 | φ₁, φ₂ auxiliary formulas | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| 2.2 | det(s) non-vanishing | ✓ DONE | `HardSphere/BaxterFactor.lean` |

### Group 3 — Wiener–Hopf Structure *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 3.1 | B₁+D₁ = T_U identity | ✓ DONE | `YukawaOZ/Splitting.lean` |
| 3.2 | Support of T_S on (−∞, R_ij] | ✓ DONE | `YukawaOZ/Splitting.lean` |

### Group M — Multi-Component Baxter Identity *(hard-sphere Baxter matrix)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| M.1 | Abstract matrix identity Ĝ+Â·c=I | ✓ DONE | `Analysis/MatrixIdentity.lean` |
| M.2 | N=1 limit: Ĝ₀₀=g, Â₀₀=a | ✓ DONE | `HardSphere/MatrixN1.lean` |
| M.3 | det(Q̂₀) ≠ 0 multi-component | ✓ **DONE, axiom-clean** — unconditional `Q0_mat_phys_isUnit_det` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`); conditional Gershgorin `..._of_diag_dom` kept as historical partial | `HSMixture/MatrixQ0.lean`, `HSMixture/Q0DetRankTwo.lean` |
| M.4 | Unconditional `det(Q0_mat_phys) > 0` (in fact `≥ 1`) for all `z > 0` | ✓ **DONE, axiom-clean (`Q0_moment_det_pos` axiom RETIRED → theorem, 2026-07-16)** — Route B: `det = 1+(a+d)−(bc−ad)`, `moment_key` (`bc−ad ≤ a+d`) ⇒ `det ≥ 1`; core is the elementary 2-var kernel `kernel_nonneg` (`G=M·Φ+M·Φ`), summed via `per_pair_f`. See [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) M.4 | `HSMixture/Q0DetRankTwo.lean` |
| M.5 | `nAux_eq_mAux_div_two` (`nAux u = mAux u/2`) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.6 | `one_add_half_sq_lt_cosh` (`1+u²/2 < cosh u` for `u>0`) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.7 | `ratioPM_strictAntiOn` (`pAux/mAux` decreasing on `(0,∞)`) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.8 | `moment_ad_le_bc` (**`bc ≥ ad`** for all N) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.9 | g + a·exp(−z) = 1 — single-comp Baxter contact identity *(ex-4.2)* | ✓ DONE | `HardSphere/SingleCompIdentity.lean` |
| M.10 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) *(ex-B.2)* | ✓ DONE | `HardSphere/QhatDecomposition.lean` |
| M.11 | Coefficient algebra (1−g²)−a²c²=2acg *(ex-B.3)* | ✓ DONE | `HardSphere/SingleCompIdentity.lean` |

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
| OZ.9b | `oz_fourier_oz_eq_of_PY_core`: OZ.7 specialized to consume `oz_core_closure` instead of an externally-supplied `hcore` — most complete/trustworthy result in the whole OZ… | ✓ DONE | `HardSphere/OZFourierBridge.lean` |
| OZ.10 | Uniqueness of the OZ fixed point (`oz_fixed_pt_unique`) | ✓ **NO LONGER AN AXIOM** — `oz_fixed_pt_unique_thm` (`OzWienerHopfBounded.lean:153`) is a theorem. ⚠ It is *not* axiom-clean: `#print axioms` (2026-08-04) gives the standard three **plus** `radialShell_bounded_injective` (MA.15), `wiener_causal_resolvent` (MA.13) and `zeroFree_lowerHalfPlane_of_homotopy` (MA.14) — all **math** axioms, so the physics assumption is gone but three Mathlib gaps … | `HardSphere/PYOZ_GHS.lean` |
| OZ.10-dilute | Dilute-regime (`eta<1`, `24·eta·bracket<1`, i.e. `eta≲0.088`) Banach existence/uniqueness for `oz_fixed_pt_unique`, exterior-only | ✓ DONE — `oz_fixed_pt_unique_dilute`, genuine theorem, no axiom/sorry. Mid/high density (`eta≈0.3–0.5`) is TRUE but gated by the BAXTER line (K non-compact ⇒ not compact Fredholm; `24η·bracket` = K's spectral radius = the dilute threshold; Baxter factorization + POLE.4/Group OZFIX explicit inverse), not attempted here — see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.10-dilute. | `HardSphere/OzFixedPtDilute.lean` (+ `c_HS_abs_t2_integrableOn` in `HardSphere/PYDCF.lean`) |
| OZ.18 | Hard-sphere `λ_ij` kink: `c_HS,ij` is C⁰ (slope kink) at `λ_ij=\|d_i−d_j\|/2`, unlike pairs *(formerly B.19)* | ✓ **DONE, slope now CLOSED-FORM (2026-07-16, axiom-clean)** — C⁰ + both one-sided slopes; **`cHS_core_deriv_at_cutoff`: `F′(λ)=2(χ₂₂−χ₁/(4π))`** (all `χ₃/χ₂/χ₁` cancel; indep. of `Rᵢ,Rⱼ,χ₀,χ₂,χ₃`) ⇒ the ex-numerical `hslope` is now the elementary `χ₂₂≠χ₁/(4π)` (`cHS_core_deriv_at_cutoff_ne_zero_iff`, `cHS_FMT_not_differentiableAt_of_chi`). … | **✅ 2026-07-17: kink now UNCONDITIONAL on `0<η<1`** — `cHS_FMT_kink_WB`/`_fmt` (`CHSKinkWB.lean`, axiom-clean) discharges `χ₂₂≠χ₁/(4π)` via the closed form `χ₂₂−χ₁/(4π)=E_WB=n₂·g(η)/(12η²v²)` + `g_wb_pos` (`g>0` on `(0,1)` by nested monotonicity `g′=4p`, `p′=−log(1−η)>0`); vanishes only at the ρ→0 boundary. Left-slope cleaned by OZ.19. |
| OZ.19 | `c_HS,ij` **exactly constant on `(0, λ_ij)`** — interval flatness, **functional-agnostic** (weight-support geometry, no Φ). **Strengthens OZ.18**: left slope 0 ⇒ its… | ✓ **DONE 2026-07-17, axiom-clean** — `cHS_flat_of_convs_const` (reduction, ∀ Φ) + `cHS_fmt_inner_const` + the OZ.18-cleanup kink lemmas `hasDerivWithinAt_Iic_zero_of_flat` / `not_differentiableAt_of_flat_below_of_right_deriv` (kink off `clampedBelow`) | `HSMixture/CHSFlatInner.lean` |

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
| `CONTACT.5` | Assembly: apply `CONTACT.3` to `oz_h`, match against `CONTACT.4`, conclude `g0_HS_contact_value` *(formerly `BAXTER.8`/OZ.17)* | ✓ DONE — `g0_HS_contact_value_of_oz_h_regularity` (conditional theorem, no sorry/axiom) **plus** its unconditional consequence: the bare `g0_HS_contact_value` axiom is now **retired**, replaced by `oz_h_exterior_regularity` bundling `CONTACT.5`'s `oz_h` hypotheses, from which `theorem g0_HS_contact_value` is proved. … | `HardSphere/JumpAsymptotic.lean` |

### Group POLE — Complex-Analytic Pole/Residue Construction for the Baxter Q-Factor *(hard_sphere)*

*Split from Group BAXTER (`BAXTER.9`,`10`,`11`,`12`,`14`). Depends on Group BAXTER
(`BAXTER.1`–`3`); feeds Group OZFIX. See [proof_notes_pole.md](proof_notes_pole.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `POLE.1` | `Qhat_complex : ℂ → ℂ` in closed form, proved entire *(formerly `BAXTER.9`)* | ✓ DONE — `Qhat_complex_entire` + `Qhat_complex_formula`, genuine theorems, no sorry/axiom; entireness via `entire_poly_exp_integral` (dominated-convergence differentiation under the integral), closed form via new `zeta0`/`zeta1`/`zeta2` moment lemmas; numerically cross-checked against the raw integral and against `BAXTER.3`'s real-`k` formulas | `HardSphere/BaxterZeros.lean` |
| `POLE.2` | Numerical/symbolic feasibility check for the Banach-pole-existence strategy *(formerly `BAXTER.10`)* | ✓ DONE — **GO**: uniform contraction bound (`max_L→0.369`, margin `≈63%`) found for `n≥10`, robust across `η∈[0.05,0.45]` | — (Python, not Lean) |
| `POLE.3` | Pole existence in Lean via Banach contraction *(formerly `BAXTER.11`)* | ✓ DONE (conditional) — `Qhat_complex_zeros_infinite`, no sorry/axiom; all magnitude bounds, branch-safety, Lipschitz/MVT, Banach wiring, distinctness/infinitude proved unconditionally for general `η∈(0,1),σ>0,ρ>0`; one explicit "good guess" hypothesis (`hstep`, numerically validated by `POLE.2`) not yet discharged for the specific asymptotic guess formula. … | `HardSphere/BaxterPoles.lean` |
| `POLE.4` | Residue formula + convergence for `h_explicit` *(formerly `BAXTER.12`)* | ✓ DONE — `residue_of_simple_pole`, `Chat_complex`, `G_baxter_deriv`, `Hhat_residue_at_pole`, `G_baxter_zero_mirror`, `h_explicit`/`h_explicit_term`/`h_explicit_summable`, and `G_baxter_pole_family_exists` all done; `POLE.5` (below) closes the one remaining gap (the magnitude-bound hypothesis, now proved rigorously not just numerically). No sorry/axiom. | `Analysis/ResidueAtSimplePole.lean`, `HardSphere/BaxterResidue.lean`, `HardSphere/RadialFourierCHSComplex.lean`, `HardSphere/BaxterPoles.lean` |
| `POLE.5` | Rigorous `n^{1-2r/σ}` magnitude bound + concrete `h_explicit` instantiation *(formerly `BAXTER.14`)* | ✓ DONE — `residue_term_norm_bound` (rigorous `‖residue_term(k)‖≤C·‖k‖^{1-2r/σ}`, assembled from new `Npoly_upper_bound`/`Dpoly_upper_bound`, `G_baxter_deriv_lower_bound_of_zero`/`G_baxter_neg_lower_bound` (direct lower-bound versions of the old non-vanishing theorems), `abs_exp_neg_ikn_sigma_lower/upper`, `abs_exp_ikr_eq_rpow`/`abs_exp_ikr_upper_of_zero`, … | `HardSphere/BaxterResidue.lean`, `HardSphere/BaxterPoles.lean`, `HardSphere/RadialFourierCHSComplex.lean` |
| `POLE.6` | Concrete pole family wired into `h_explicit`'s summability | ✓ DONE (axiom-clean) — `h_explicit_summable_concrete` consumes `G_baxter_pole_family_exists_growth`'s conclusion tuple (existentially, since that theorem's hypotheses mention the `private` `baxterP0/1/2` — same cross-file-privacy pattern as POLE.5's wrappers) + a new centre hypothesis `hk1im : r ≤ Im(k1 n)`, and yields an injective, `G_baxter`-zero, upper-half-plane family with `Summable … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.6`. | `HardSphere/HExplicitConcrete.lean` |
| `POLE.7` | Discharge `hstep` via the derived log-lift guess | ✓ **DONE — `hstep` PROVED (eventually form), axiom-clean, no sorry, full build green (2026-07-16)**: `k1_guess_hstep_eventually` — for the fit-free guess `k1_guess(n)=2πn/σ+(i/σ)·ln(‖Npoly(xₙ)‖/‖Dpoly(xₙ)‖)` (supersedes POLE.2's fitted `2ln x−2.12`; `hk1re` exact by construction), `∃N, ∀n≥N, dist(k1_guess n, baxterPhi n (k1_guess n)) ≤ rr(1−KK)` for **every** positive target and all physical … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.7`. | `HardSphere/BaxterPoleGuess.lean` (new) |
| `POLE.8` | Fire the log-route family: POLE.3 unconditional | ✓ **DONE (2026-07-16) — `POLE.3` CLOSED UNCONDITIONALLY**, axiom-clean, sorry-free, first build green: **`Qhat_complex_zeros_infinite_unconditional`** + `G_baxter_zeros_infinite_unconditional` (hypotheses = physical parameters only!) + POLE.6 payoff **`h_explicit_summable_unconditional`** (`∃ g` injective `G_baxter`-zero family, `Im≥0`, `Summable (h_explicit_term … y g)` for every `y>σ` — the … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.8`. | `HardSphere/BaxterPoleFamilyConcrete.lean` (new) |
| `POLE.9` | Chord `ChordPoleFamily (G_baxter)` (shared MZERO.5 obligation) | ✓ **DONE (2026-07-16)** — `chordPoleFamily_G_baxter_exists` + `G_baxter_zeros_infinite_chord` (axiom-clean, sorry-free, zero warnings): the 1-freq chord obligation is CLOSED for all physical params; pivotal lemmas `exp_at_k1_guess` (exact phase kill via `exp_int_mul_two_pi_mul_I`) and `norm_sub_ratio_mul_le` (algebraic unit-phase-difference bound, no arg/trig); `r=1/(10σ)`, `K=1/2`; 2-freq … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.9`. | `HardSphere/BaxterChordFamily.lean` (new) |
| `POLE.10` | **Pole-family EXHAUSTION**: the constructed family enumerates *all* UHP zeros of `G_baxter`, injectively, with non-degenerate mirror pairing | ☐ **opened 2026-07-16 — on the critical path for BOTH remaining `hcollapse` routes** (`OZFIX.14` options (b) and (c)). Needed: `Function.Injective kfam`; `∀ z, 0 < z.im → G_baxter … z = 0 → ∃ n, z = kfam n ∨ z = -conj (kfam n)`; and pairing non-degeneracy (`(kfam n).re ≠ 0`, else `k = -conj k` and `Hterm`/`Kterm` double-count; `kfam m ≠ -conj (kfam n)`). **`POLE.8`'s … [detail in linked notes] | `HardSphere/BaxterPoleFamilyConcrete.lean` or new |

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
| `OZFIX.6` | Algebraic collapse (`B.5`, the mathematical payoff) | ◑ **split → `OZFIX.11` (`r≥2σ`, ✓ DONE 2026-07-16) + `OZFIX.12`/`OZFIX.13` (`σ≤r<2σ` + endpoint, scoped)**. The old scoping's "per-pole route FALSE (`-2.72`)" is now fully understood: it is specific to `σ≤r<2σ` (where `oz_forcing≠0`); for `r≥2σ` the per-pole collapse is TRUE and **proved** (collapse factor `ρ·Ĉ(k_n)=1`, see `OZFIX.11`). Aggregate target well-confirmed numerically. | see `OZFIX.11`–`13` |
| `OZFIX.7` | Regularity (`B.6`): `ContinuousOn`+boundedness | ✓ DONE on `(σ,∞)`/`[r0,∞)`, `r0>σ` — `h_explicit_continuousOn_Ioi`, `h_explicit_bounded_on_Ici`, no sorry/axiom. Closed endpoint `r=σ` remains open (same `σ`-boundary gap as `OZFIX.4`/`6`) | `HardSphere/HExplicitRegularity.lean` |
| `OZFIX.8` | Final assembly (`B.7`): invoke `oz_fixed_pt_unique` | ✓ DONE, conditional on `hcollapse` (`OZFIX.6`) + `hcont_sigma` (`OZFIX.7`'s σ-endpoint gap) — `oz_h_eq_spliced_h_explicit`, `#print axioms` only `oz_fixed_pt_unique` beyond the standard three; retiring `oz_core_closure` itself is a separate Phase C follow-on. … | `HardSphere/OzFixedPtHExplicitFinal.lean`, `HardSphere/OzCollapseTwoSigma.lean` |
| `OZFIX.9` | `hcollapse` via **Route A** (`oz_forcing` termwise Mittag-Leffler expansion), alternative to Route B (whole-series `radial3d_conv` + Mathlib-axiom, done elsewhere) | ☐ **Direction (user-confirmed 2026-07-15): Route B closes `hcollapse`** (favorable axiom trade — physics `oz_core_closure` → standard/reusable residue axiom); Route A kept as the future *unconditional* (axiom-free) path, `r≥2σ` part now tractable. **UNBLOCKED — the POLE fix resolved the aggregate; Route A viable but research-scale (≈ Route-B difficulty).** Re-scoped against … | new `HardSphere/OzForcingResidue.lean` |
| `OZFIX.10` | `hcollapse` via **Route B** (growing-contour Fourier inversion: `∫_{-R}^{R} k·Ĥ·e^{ikr} → 2πi·Σres`, then back to `radial3d_conv`) — the user-confirmed closing route… | ◑ **infrastructure DONE, arc-vanishing OPEN.** Done (2026-07-15, `lake build` clean): (a) **`jordan_lemma_arc_bound`** (`Analysis/JordanLemma.lean`) — quantitative Jordan's lemma `‖∫_arc g·e^{iaz}‖≤πM/a`, **proved outright, NO axiom** (`Real.mul_le_sin` + ML-inequality + `Complex.norm_exp` + FTC); (b) **half-disk residue theorem** — axiom … → **`−1/ρ`** (smoking gun: the recorded circle bounds … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.10`–`12`. | `Analysis/JordanLemma.lean`, `Analysis/ContourDeformation.lean`; application file TBD |
| `OZFIX.11` | `hcollapse` for `r ≥ 2σ` — per-pole collapse via `ρ·Ĉ(k_n)=1` | ✓ **DONE (2026-07-16), axiom-clean** (`#print axioms` = standard three; NO `hint`-family hypothesis — vacuous on this region): `oz_collapse_of_two_sigma_le` — `OZFIX.5`'s outer integral collapses **per pole**: each pole's `t`-integral closes to `residue_term(r,k)·Ĉ(k)/(2π)` (`integral_Chat_poly_exp_pair` + `Chat_F_neg_sub_eq`, pure `Chat_F`/`Chat_J` moment algebra), and **`ρ·Ĉ(k)=1` at every … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.11`. | `HardSphere/OzCollapseTwoSigma.lean` (new) |
| `OZFIX.12` | `hcollapse` for `σ < r < 2σ` — exact defect algebra + reduction to the core-closure series identity (★) | ◑ **Reduction target IDENTIFIED + numerically CONFIRMED; `Kterm` infra ✓ DONE (axiom-clean, build green); assembly remains.** Derived the exact defect: `oz_forcing + oz_linear_op[h_explicit] = h_explicit + (ρ/r)·Re ∑'ₙDₙ(r)` with `Dₙ(r) = ∫_{r−σ}^σ Chat_poly(r−u)[Hterm n u − Hterm n σ]du` (uses `integral_Chat_poly_mul_Hterm_pair`, which needs **no** `r≥2σ`) ⇒ `hcollapse` ⟺ … See … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.12`. | `HardSphere/OzCollapseInner.lean` (new) |
| `OZFIX.13` | `σ`-endpoint + full `hcollapse` discharge wiring | ☐ **scoped**: `r=σ` from `hcont_sigma` + continuity of the LHS at `σ⁺` (forcing explicit; linop via `OZFIX.5`'s closed form + `Σ'Hterm` continuity down to `σ`, `OZFIX.4` machinery); then the fully-discharged `oz_h_eq_spliced_h_explicit` variant (hypotheses = `OZFIX.11`'s + `OZFIX.12`'s bundle + `hcont_sigma`). … | TBD |
| `OZFIX.14` | **Circularity: (★) ⟺ core closure ⇒ Group OZFIX CANNOT retire `oz_core_closure`** | ✗ **NEGATIVE RESULT (2026-07-16), closed.** Closing the UHP contour on (★)'s pole sum **provably cannot** prove it. With `ρĈ(kₙ)=1` the summands are `Res_k[S]·Ξ(k)/(iρ)`, `S:=1/(1−ρĈ)=z⁶/(G(z)G(−z))`, `Ξ` **entire**; writing `S=1+ρĤ`, the `ρĤ` arc →0 (Jordan + two-regime) and the `1` part cancels **exactly at every R** between line and arc (`∮Ξ=0`) ⇒ `2πi·∑'Res_k[S]Ξ(k) = ρ∫_ℝ … See … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.14`. | — |
| `OZFIX.15` | **Real-space Baxter/Wertheim–Thiele — the ψ construction (claims A/B/C ⇒ `ψ ⋆ Q₊ ⋆ Q₋ = φ`)** | ✓ **DONE 2026-07-17 — axiom-clean, `lake build` green** (`HardSphere/BaxterRenewal.lean`). Target **`baxter_psi_conv_eq_phi`**: `(ψ⋆Q₊⋆Q₋)(r) = r·c_HS(r) = φ(r)` for **every** `r>0`, every object concrete. **(1) Global ψ by uniqueness-as-glue:** `MA.10` gives a different `C(Icc σ b, ℝ)` per `b` (dependent type, useless to a convolution identity on `ℝ`); `volterraSol_compat` … → [ozfix](proof_notes_ozfix.md) `OZFIX.15` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.16` | **The `1D-odd ↔ 3D-radial` bridge: `d/dr[r·(f ⊛₃ g)(r)] = −2π·(f̃ ⋆ g̃)(r)`** — turns the real-space Baxter identity `ψ⋆Q₊⋆Q₋=φ` into OZ for all `r>0` | ✓ **DONE 2026-07-17 — BOTH HALVES PROVED, axiom-clean** (`HardSphere/BaxterRenewal.lean`). Target theorem **`hasDerivAt_radial3d_conv_bridge`**. Chain: `radial3d_conv_eq_oddExt` (kills the `\|r−t\|` via `integral_shell_eq_oddExt`) + **brick 1 `hasDerivAt_shell`** (FTC on the shell: `d/dx ∫_{x−t}^{x+t} φ = φ(r+t)−φ(r−t)`, needing continuity of `φ` **only at the two endpoints**; … → [ozfix](proof_notes_ozfix.md) `OZFIX.16` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.17` | **Assembly ⇒ `oz_core_closure` becomes a THEOREM (Phase C)** | ☐ **RE-SCOPED 2026-07-17 — was NOT one task.** Investigating the chain found a structural obstacle the old sketch hid: **`Q̂` is a 1D transform but `Ĉ` is a 3D radial one** (`Qhat_complex` of `q0_poly` vs `radial_fourier` of `c_HS`), so `OZFIX.2`'s `(1−Q̂(k))(1−Q̂(−k)) = 1−ρĈ(k)` does **not** make `1−ρĈ` the transform of `δ−ρc̃`; the two differ by `2πi/k` = an … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/PYOZ_GHS.lean`, `HardSphere/BaxterRenewal.lean` |
| `OZFIX.18` | **Real-space Baxter factorization `Q₊ ⋆ Q₋ = δ − ρ·K`** | ◑ **CORE FORM `rho_baxterK_eq_q0_self_conv` PROVED 2026-07-17, axiom-clean**: `ρ·K(v) = q0(v) − ∫_v^σ q0(t)·q0(t−v)dt` for `v∈(0,σ)` (the double integral IS `(q0·1_{[0,σ]} ⋆ q0(−·)·1_{[−σ,0]})(v)`). Proof = **two FTC evaluations + `field_simp`/`ring` under `heta_def`** (degree-4 antiderivative `Gpoly` for `∫ s·c_HS`, degree-5 `Fpoly` for `∫ q0·q0`; `HasDerivAt` via … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.19` | **The antiderivative bridge `r·(f ⊛₃ g)(r) = (g̃ ⋆ K_f)(r)`** | ✓ **DONE 2026-07-17, axiom-clean** (`radial3d_conv_eq_baxterK_shell`): `r·(c_HS ⊛₃ g)(r) = ∫₀^σ K(u)·(g̃(r−u)+g̃(r+u))du` for `r>0` (= `(K⋆g̃)(r)` folded onto `[0,σ]` by `K` even). **KEY REALIZATION: it is NOT a differentiation argument — just Fubini** (differentiate-in-`u` would break at `u=σ−r` where `g̃=ψ` jumps; Fubini only needs integrability, jump-proof). … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.20` | **Convolution associativity `(ψ ⋆ Q₊) ⋆ Q₋ = ψ ⋆ (Q₊ ⋆ Q₋)` (Fubini)** | ✓ **DONE 2026-07-17, axiom-clean** (`dbl_conv_reindex`): `∫₀^σ∫₀^σ q0(t)q0(s)ψ(r+t−s) = ∫₀^σ(∫_u^σ q0(t)q0(t−u)dt)(ψ(r−u)+ψ(r+u))` for **any** ψ (numerically verified 3 ψ to 1e-16). **Both sides reduce to `∫ t in 0..σ,∫ s in 0..t, q0(t)q0(s)(ψ(r+t−s)+ψ(r+s−t))`**: RHS by `intervalIntegral_triangle_swap_gen` (the new 2-var triangle Fubini) + inner change-of-var `s=t−u`; LHS by splitting the inner … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.21` | **OZ★ linchpin + axiom consolidation** | ✓ **OZ★ DONE 2026-07-17, axiom-clean** (`baxterPsi_eq_phi_add_rho_conv`): `baxterPsi(r) = r·c_HS(r) + ρ·r·radial3d_conv(c_HS, baxterPsi/·)(r)` ∀`r>0` — the concrete real-space **OZ equation** solved by the constructed `baxterPsi`, assembled from `baxter_psi_conv_eq_phi` (`OZFIX.15`) + `radial3d_conv_eq_baxterK_shell` (`OZFIX.19`) + `rho_baxterK_eq_q0_self_conv` (`OZFIX.18` KDEF) + … → [ozfix](proof_notes_ozfix.md) `OZFIX.21` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.22` | **Axiom consolidation — RETIRE `oz_core_closure` + `oz_h_exterior_regularity` (net 3→2)** | ✓ **DONE 2026-07-17, full build green (8653 jobs), no cycles.** New file `HardSphere/OzCoreClosure.lean`: `radial3d_conv_cHS_congr` (decay-free brick: `radial3d_conv c_HS g r` depends on `g` only on `(0,r+σ)`), `oz_core_closure_of_bridge` (decay-free reduction: closure = OZ★ ⊘ r + bridge), `ozBaxterFixedPt := if r<σ then -1 else baxterPsi r/r`, `oz_h_eq_ozBaxterFixedPt` (**the … → [ozfix](proof_notes_ozfix.md) `OZFIX.22` | `HardSphere/OzCoreClosure.lean` |
| `OZFIX.24` | **RETIRE `ozExterior_triple_shell_sin_integrable` (6h): axiom → theorem** | ✓ **DONE 2026-07-19, full build green (8675 jobs), no new axiom, no `sorry`** — `axiom` keyword deleted, name/signature unchanged so no consumer edit needed. It had been axiomatized on an **effort** argument ("formalizing the triple `lintegral` chain is substantial"), not a gap argument — in tension with Group MA admissibility rule (c); same category as MA.10/11/12, all retired by proving. … → [ozfix](proof_notes_ozfix.md) `OZFIX.24` | `HardSphere/BaxterExteriorConvIntegrable.lean` |

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
| FW.1 | FMT species symmetry: `betaf_hs` depends on `rho` only through `∑ᵢρᵢ` when all diameters equal | ✓ DONE, no axiom (`betaf_hs_species_symmetry`) | `HSMixture/WhiteBearFMT.lean` |
| FW.2 | BMCSL/White-Bear thermodynamic consistency: virial pressure (from `g0_bmcsl`) = FMT scaled pressure (from `betaf_hs`) | ✓ DONE, no axiom (`bmcsl_virial_eq_fmt_pressure`) | `HSMixture/WhiteBearFMT.lean` |
