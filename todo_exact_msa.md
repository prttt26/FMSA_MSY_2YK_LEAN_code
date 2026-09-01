# Exact MSA (+ FMSA↔Exact-MSA bridge) — task status

The exact MSA closed form (Waisman / Blum–Høye / Ginoza), single component and mixture, **plus**
everything about the FMSA↔exact-MSA relationship: MSAEXACT.5 (`fmsa_eq_firstOrder_msa`), FOEQ (the two
definitions of "first order" agree), MSAFAM (the MSA solution family, smooth at zero coupling), the
exact-MSA mixture core BRK (incl. the axiom-free BRK.16 `baxterConvCore = matCoreUneq`), and the
leg-3 Blum–Høye N=1 derivation. **Scope + axiom gate:**
[`LeanCode/ExactMSAProject.lean`](LeanCode/ExactMSAProject.lean).

↩ **Index:** [`todo_lean.md`](todo_lean.md) — layer map, project-wide axiom/sorry ledger, category index.

**Detailed records:**
- [proof_notes_msa_exact.md](proof_notes_msa_exact.md) — Groups MSAEXACT, MSAEMIX
- [proof_notes_breakpoints_MSA.md](proof_notes_breakpoints_MSA.md) — Group BRK (exact-MSA mixture core)
- [proof_notes_closures.md](proof_notes_closures.md) — the **FOEQ** and **MSAFAM** parts (the bridge)
- [proof_notes_leg3_bh_realspace.md](proof_notes_leg3_bh_realspace.md) — leg-3 Blum–Høye derivation

---

## Task Status

### Groups MSAEXACT / MSAEMIX — The Exact MSA Closed Form *(msa_exact)*

Waisman/Blum–Høye/Ginoza analytic MSA for a hard-core Yukawa fluid, split scalar (**MSAEXACT**) /
matrix (**MSAEMIX**). **No new axiom** (algebra over ℝ, `e^{−zσ}` a parameter). Detail, substrate,
boundaries, non-vacuity: [proof_notes_msa_exact.md](proof_notes_msa_exact.md). Numerical: Group MSAX.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| MSAEXACT.1 | non-compact Baxter factorization `\|1−ρQ̂(ik)\|²=1−ρĉ_MSA` | ◑ **reduced to MSAEXACT.6** (staged via `factorization_of_core`); ⛔ compact `exactMSA_iff_core` route dead | `YukawaOZ/{MSABaxterKSpace,MSAFullFactorization}` |
| MSAEXACT.6 ⭐ | **the gap** — discharge the `hcore` closure-recovery ring | ⊘ **`ring`-INFEASIBLE, measured 2026-08-22** (clean 323-mono deg-22 slice = `ring` 3h12m/23GB; irreducible per-order reassembly ~weeks/~200GB; atom form worse deg≈35; `native_decide` blocked by noncomputable `MvPolynomial`). ✅ **Fourier layer DISCHARGED** (`YukawaOZ/ExactMSA6Certificate.lean`, out-of-`defaultTargets` lib): `exactMSA_hcore_of_residual` ⇒ exact `exactMSA_hcore` statement from ONE pure-cos/sin/exp axiom `exactMSA_kspace_residual`. **"Upgradeable/30-min" RETRACTED.** Sole gap of .1, MSAFAM.5/.6@N=1; MSAEMIX.1 = matrix analog | `YukawaOZ/{MSAFullFactorization,ExactMSA6Certificate}` |
| MSAEXACT.2 | degree-8 elimination = two quartics; physical branch quartic | ✓ DONE | `YukawaOZ/MSAElimination` |
| MSAEXACT.3 ⭐ | `msaRoot_unique_of_coupling_lt` — unique physical root below coupling threshold | ◑ core DONE (`βK≈3` measured) | `YukawaOZ/MSAClosedForm` |
| MSAEXACT.4 | PY coeffs annihilate Waisman's eqns at `K=0`, ∀`w` | ✓ DONE | `YukawaOZ/MSAClosedForm` |
| MSAEXACT.5 ⭐ | `fmsa_eq_firstOrder_msa` — 1st-order MSA = FMSA-DP HS-dressed amplitudes | ✓ DONE (needs FOEQ.5 for "linearise"="differentiate") | `Closures/FirstOrderEquivalence` |
| MSAEMIX.0 ⭐ | mixture positivity + stability det (spinodal = `det F=0`) | ✓ DONE | `YukawaOZMix/MSAMixturePositivity` |
| MSAEMIX.1 | matrix factorization (matrix form of MSAEXACT.1) | ◑ (★) cancellation DONE + **staged to matrix `hcore`** (`matMixtureFactorization_of_core`, analog of MSAEXACT.6) | `YukawaOZMix/{MSAMixtureCancellation,MSAMixtureFactorization}` |
| MSAEMIX.2 | `N=1` reduces to MSAEXACT.1 | ◑ positivity half; factorization half ← MSAEMIX.1 | `YukawaOZMix/MSAMixturePositivity` |
| MSAEMIX.3 ⭐ | Eq.(41) mixture root selection = `g_ij=g_ji` | ✓ DONE | `YukawaOZMix/MSAMixtureSelection` |

### Group FOEQ — The Two Definitions of "First Order" Agree *(closures)*

**Opened 2026-08-10** (paper §IV). Two definitions of "first order": **(D1)** truncate the hierarchy order-by-order at `γ=1` (what the WH construction builds; unconditional); **(D2)** `c⁽¹⁾ = d/ds[c_MSA(sK)]|₀` (differentiate the exact family; needs only differentiability at `s=0`). FOEQ proves they agree. ⚠ Distinct from MSAEXACT.5 (which *assumes* the derivative exists — the gap) and from PYE (which identifies *which* closure). → [closures](proof_notes_closures.md) Group FOEQ.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| FOEQ.1 | `msa_exterior_linear_in_coupling` — the MSA exterior is `c = −βsU`, **linear in `s`**, so on `r>R_ij` (D1) and (D2) are the *same expression*, with no remainder and no `O(s²)` | **✓ DONE 2026-08-10** as `msaOuter_hasDerivAt` + `msaOuter_eq_smul_deriv` + `mayerF_ne_msaOuter` (`Closures/FirstOrderEquivalence.lean`). ⚠ `msa_first_order_outer` does **not** already say this: it is the `y₀ ↦ 1` case of the *Mayer* factor `e^{−βsu}−1`, which agrees with MSA at first order but is not the MSA closure. The honest statement is `HasDerivAt` at **every** `s` with vanishing second derivative | `Closures/ClosureExpansions.lean` |
| FOEQ.2 | the WH split's support obligations are **coupling-independent** (`h_ij = −1` on `r<R_ij` is exact at every `s`; `R_ij` is core data, not tail data) | ☐ **record only — discharged by construction.** The supports are already `s`-free constants in every WH statement in the tree, so there is nothing to prove. Named anyway because it is precisely what a *moving-boundary* perturbation problem violates, and there order-by-order solution and differentiation do **not** commute. A reader who does not see it named will assume it needs an argument, or worse, will not notice it was needed | — |
| FOEQ.3 ⭐ | `oz_gamma_one_is_the_derivative_equation` — differentiating `(I+H̃)(I−C̃) = I` at `s=0` returns the `γ=1` line **term for term**. OZ is quadratic, so this is the product rule  | **✓ DONE 2026-08-10** as `oz_deriv_eq_firstOrderLine`, axiom-clean. ⚠ **Do not state it at `Matrix`** — the `HasDerivAt` hypotheses elaborate with the ambient `Pi` topology while `HasDerivAt.mul` supplies `Matrix.linftyOp*`, and they are not defeq. Over an abstract `[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]` it goes through at once, and matrices follow by `open scoped Matrix.Norms.Operator` + instantiation. No new axiom | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.4 | `first_order_solution_determined` — the `γ=1` equation **plus** the `s`-free support conditions determines `C̃₁`, so (D1)'s answer *is* the derivative once FOEQ.3 supplies the equation | ◑ **algebraic half done 2026-08-10** — `firstOrder_dcf_of_oz_deriv` gives `C̃₁ = Hinv·(H₁(I−C̃₀))` from a left inverse of `I+H̃₀`. The WH-uniqueness half still wants PYE.2 linearity (`dpDCFLinear`) + `radial_fourier_injective` (PYE.5) / `MixtureDCFAEInjective` | `Closures/FirstOrderEquivalence.lean`, `Closures/DPClosureMap.lean` |
| FOEQ.5 ⭐⭐ | `msa_solution_differentiable_at_zero_coupling` — **the one input algebra does not settle.** The physical MSA root is differentiable in `K` at `K=0`, by the implicit function t | ◑ ⭐ **the Jacobian condition is CLOSED (2026-08-10), in closed form.** At the PY base point `Dt = 0`, which kills every `G`-dependence (it enters only through `M,N ∝ Dt`), so the Jacobian is block lower-triangular and `det J = (2π)^n ∏_u F₀(z_u)²` — verified numerically to 6e-11…9e-10 over ξ∈{0.05,0.20,0.40,0.49} × n∈{1,2,3}. Nonsingular ⟺ `F₀(z_u) ≠ 0`, which is **`Q0_ne_zero_at_yukawa`, already proved**. … | `Closures/…` |

### ⭐⭐ Scope raised to arbitrary order (2026-08-10, paper Theorem IV.1)

FOEQ.1–5 were `γ=1`; **the equivalence holds at every order** (product rule → general Leibniz, in Mathlib). FOEQ.6–9 add the general-order versions (FOEQ.1/3 stay as the `γ=1` instances the paper consumes). Consequences: (a) the hypothesis becomes `C^∞` differentiability at `s=0` — still weaker than analyticity; (b) what's special about first order is only **finite-closed-form solvability** — the middle convolution `∑_{m=1}^{γ−1}` is empty iff `γ=1` (FOEQ.9).
| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| FOEQ.6 | `msa_closure_taylor_coeffs_terminate` — generalises FOEQ.1 to all orders. The closure is a **degree-≤1 polynomial in `s`**, so its Taylor coefficients are identities that *ter | **✓ DONE 2026-08-10** as `msaOuter_iteratedDeriv_terminates` (+ reusable `iteratedDeriv_linear_higher`: a degree-≤1 `s↦s•c` has `iteratedDeriv γ = 0` for `γ≥2`). Contrast PY/HNC, whose Mayer exterior has a nonvanishing coefficient at **every** order — FOEQ.1's `mayerF_ne_msaOuter` is the `γ=1` shadow of that | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.7 ⭐ | `oz_taylor_coeff_eq_cauchy_convolution` — generalises FOEQ.3 to order `γ`. Dividing `∑ᵢ C(γ,i)·f⁽ⁱ⁾·g⁽ᵞ⁻ⁱ⁾` by `γ!` turns the binomial into `1/(i!(γ−i)!)`, so the order-`γ` co | **✓ DONE 2026-08-10, load-bearing** (`oz_taylor_coeff_eq_cauchy_convolution`). Via **`iteratedDeriv_mul`** applied to the *constant* product `(1+H̃)(1−C̃)=1`, so its order-γ coefficient (`iteratedDeriv_const`, γ≥1) is `0` = the finite Cauchy convolution. Hypothesis `ContDiffAt ℝ γ` (γ-fold, **not** `C^∞`), over abstract `[NormedRing 𝔸][NormedAlgebra ℝ 𝔸]` *not* `Matrix` (FOEQ.3 pitfall inherited). Axiom-clean | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.8 ⭐ | `oz_msa_taylor_eq_hierarchy` — the capstone: assemble FOEQ.6+FOEQ.7 (+FOEQ.2) into *for every `m ≤ γ`, the order-`m` Taylor coefficient of the exact solution satisfies the ord | **✓ DONE 2026-08-10** as `oz_msa_taylor_eq_hierarchy` (`∀ m≥1` from FOEQ.7 under `ContDiff ℝ ∞`) + the `γ=1` corollary `oz_deriv_eq_firstOrderLine_of_taylor` (`iteratedDeriv 1 = deriv`, recovers FOEQ.3's `deriv H 0·(1−C 0)=(1+H 0)·deriv C 0`). Axiom-clean | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.9 | *(record only)* the empty-convolution characterisation: `∑_{m=1}^{γ−1}` is empty **iff** `γ=1` | **✓ DONE 2026-08-10** as `cauchy_convolution_middle_empty_iff` (`Finset.Ico 1 γ = ∅ ↔ γ=1`, via `Finset.Ico_eq_empty_iff`+`omega`) — the precise statement of what §XII's obstruction *is*, naming it prevents the misreading that higher orders are ill-defined rather than merely not closed-form | `Closures/FirstOrderEquivalence.lean` |

**Numerical witness for FOEQ.5** (it is measured, not proved — say so wherever it is quoted;
⚠ it is also **`γ=1` only**, so it does not test FOEQ.6–8):
BH-linearised ≡ FMSA-DP to **6.4e-7 … 2.8e-5** over 25 states, `η ∈ [0.05,0.40]`, `z ∈ [1.8,28.75]`,
on `∂_K(∂βp/∂ρ)` at `N=1`; central difference in `±s` of converged OZ+MSA agrees to **5e-6**, with the
estimator itself linear in `s` to 2e-5 between `s=1e-4` and `1e-5`. Neither is evidence that the
derivative *exists* — both presuppose it.

**Constraint: no new axiom.** FOEQ.1–4 are calculus and linear algebra; FOEQ.5 is the IFT on an
algebraic system over `ℝ` with `e^{−zσ}` a parameter. Needing an axiom means a route was abandoned.

⚠ **Do not mark FOEQ closed on FOEQ.1–4 alone.** Those give "(D1)=(D2) *as soon as the derivative
exists*", which is the algebraic half and is not the claim. Without FOEQ.5 the group's headline
remains conditional, and the paper's §"What is *not* formalized" must keep saying so.

### Group leg-3 — Blum–Høye `N=1` scalar derivation (h29/h33 from the OZ primitives)

The scalar (`N=1`) Blum–Høye Eqs (29)/(33) `Dt·bhF = 2πK/z`, `2πG·bhF = bhP` are **derived** from the
recognised OZ/Baxter primitives, not posited. Detail: [proof_notes_leg3_bh_realspace.md](proof_notes_leg3_bh_realspace.md).
**Gated in [`ExactMSAProject.lean`](LeanCode/ExactMSAProject.lean)** (5 `#guard_msgs`). Every derivation
is axiom-clean; the end-to-end factorization inherits **only** the pre-existing `exactMSA_hcore`.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| leg-3 Ph.0–3 | map machinery + γ (RDF Laplace moment) + dressed coeffs `msaQp`/`msaA` (Baxter moments Eq 13/14) + tail moment | ✓ DONE | `YukawaOZ/MSABlumHoyeDerivation` |
| leg-3 Ph.4 (h29) | `h29_of_baxter_exterior` — Eq 29 from Baxter's exterior Eq 8 + MSA closure `cMSAtail` | ✓ DONE, axiom-clean | `YukawaOZ/MSABlumHoyeDerivation` |
| leg-3 Ph.5 (h33) | `h33_of_gside` — Eq 33 from the g-side OZ Eq 32 Laplace-transformed at `s=z`; print-error (σ-anchored C-exp) resolved | ✓ DONE, axiom-clean | `YukawaOZ/MSAGSideOZ` |
| leg-3 conv-thm ⭐ | `laplace_conv_eq_rdf_mul_qhat_of_integrable` — `L_z[(rg)⋆Q]=ĝ(z)Q̂(z)`. **Fubini swap DISCHARGED** (`Integrable.convolution_integrand`+`Measure.prod_restrict`+`integral_integral_swap`); only physical `L¹` moment integrability assumed | ✓ DONE, axiom-clean | `YukawaOZ/MSAGSideOZ` |
| leg-3 Q-side | `bhBaxterSupp` (+`_transform`/`_weighted_integrable`) discharge the concrete Baxter `Q̂=1−bhF` and `e^{−z·}Q∈L¹` | ✓ DONE, axiom-clean | `YukawaOZ/MSAGSideOZ` |
| leg-3 Ph.6 | `exactMSA_factorization_of_oz` — wire the derived h29/h33 into `exactMSA_factorization`, retiring the posited constraints (footprint = std-3 + `exactMSA_hcore`, **no new axiom**) | ✓ DONE | `YukawaOZ/MSAFactorizationFromOZ` |
| leg-3 hbax/hgside | `hbax_iff_h29` / `hgside_iff_h33` — the OZ primitives are **exactly** h29/h33 (both directions). ⚠ **NOT** unconditionally dischargeable: they are physical-root conditions, false off-root; full discharge = "closed-form Baxter fn solves OZ from first principles" = the `exactMSA_hcore` content | ✓ RESOLVED, axiom-clean | `YukawaOZ/MSAGSideOZ` |

### Group leg-3-mix — mixture (general `N`, matrix) Blum–Høye derivation

**Mirror image of scalar:** the analytic ring is already discharged (`matExactMSA{Equal,Unequal}Diam_hcore`),
but the physical root `MSAMixture.MixBHRootUneq` (matrix (29′)/(33′)) is **posited**. Mixture leg-3 derives
the root from the real-space OZ/Baxter primitives. Plan/progress: [proof_notes_leg3_mixture.md](proof_notes_leg3_mixture.md).
New files under `YukawaOZMix/`, namespace `FMSA.ExactMSA.MixLeg3`.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| MPhase 1 ⭐ | `baxterQ_transform` / `baxterQ_transform_eq_qhatMixRuneq` — the matrix Baxter transform `∫_ℝ baxterQ_ij·e^{−sr} = qhatMixRuneq` (the posited real-`s` factor **is** the transform of real-space `baxterQ`). 4 support-clean pieces; `Wt` spans core+tail, its `e^{−(s+z)σ_ij}` term cancels; `edgeLo+σ_i=edgeHi`. Helpers `baxterQ_poly_moment`/`yukawa_shift_interval`/`expLin_interval`/`yukawa_shift_integrableOn_Ioi` | ✓ DONE, axiom-clean (std-3) | `YukawaOZMix/MixtureBlumHoyeDerivation` |
| MPhase 1 rem. | `s=z` value (`∑_l ρ_l Q̂(z)` → `δ − …`) + `T_n` moments + complex-`s` `qhatMixCuneq` lift | ○ deferred (do when consumed in MP2/4) | — |
| MPhase 2 ⭐ | c-side exterior Baxter relation: `baxterQ_exterior_conv` (per-`l` exterior conv `∫ Q'_il(t+r)Q_jl(t) = −z e^{−zr}(…)Q̂_jl(z)`, **factors through the MPhase-1 transform** since `edgeLo_jl+edgeHi_ij=edgeHi_il`) + `mat_exterior_baxter_relation` (assembled Eq 8). `perL_conv_*` NOT needed | ◑ exterior DONE, axiom-clean (std-3) | `YukawaOZMix/MixtureBlumHoyeDerivation` |
| MPhase 2 amp ⭐ | amplitude algebra: `baxterS_eq_edgeHi_Dt` (`Wt_il e^{z·edgeLo_il}+Ct_il e^{z·edgeHi_il} = e^{z·edgeHi_il}·Dt_il` via `cancellation_star`) + `mat_exterior_baxter_relation_Dt` (exterior relation in `Dt` form). Numeric `S`-check 4.4e-16 | ✓ DONE, axiom-clean (std-3) | `YukawaOZMix/MixtureBlumHoyeDerivation` |
| MPhase 2 (♦) ⚠ | `c_side_constraint_of_exterior` — from the exterior closure `hbax` derives the c-side constraint **(♦)** `Dt_ij − ∑_l ρ_l·e^{z·edgeLo_jl}·Dt_il·Q̂_jl(z) = 2πK_ij/z` (matrix analog of scalar `h29_of_baxter_exterior`). **FINDING:** the **recentering `e^{z·edgeLo_jl}`** is ABSENT in the posited `MixBHRootUneq` (29′) → coincide at equal σ, differ at unequal σ (σ-power masked by σ=1). (♦) Lean-proven; (29′) untouched. **User decision:** fix (29′) to recentered + wire at MP5, or reconcile | ✓ (♦) DONE, axiom-clean; ⚠ (29′) FLAGGED | `YukawaOZMix/MixtureBlumHoyeDerivation` |
| MPhase 3 (CRUX) | g-side matrix Laplace-conv stack: matrix `rdfLaplaceMoment` + matrix conv thm `∑_l ĝ_il·Q̂_jl` (matrix product) + matrix Fubini (scalar technique lifts per species, `∑_l` contraction is new) | ○ TODO | `YukawaOZMix/…` |
| MPhase 4/5 | assemble (33′) + wire-in `MixBHRootUneq_of_oz` (retire posited root) + hbax/hgside-style equivalences | ○ TODO | `YukawaOZMix/…` |
