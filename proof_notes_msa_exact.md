# Proof Notes: The Exact MSA Closed Form (Groups MSAEXACT / MSAEMIX)

Proof records for the **exact** mean-spherical approximation of a hard-core Yukawa fluid — the
Waisman / Blum–Høye / Ginoza closed form — split on the single-component / mixture seam:

* **Group MSAEXACT** — single component, scalar algebra. `LeanCode/YukawaOZ/MSAClosedForm.lean`.
* **Group MSAEMIX** — mixture, matrix eigenstructure. `LeanCode/YukawaOZMix/MSAMixtureClosedForm.lean`.

The shared `MSAE` stem marks the pairing; the split is where the *mathematics* changes, not merely
the index count, mirroring how the tree already separates **Y1** (single-component foundation) from
**MRS**/**MML**/**MZERO** (mixture). One file for two groups, per `feedback_proof_notes_structure`
(a group split does not force a file split — cf. PYE+HNCB here, MRS+MPOLY in
`proof_notes_mixture_dcf.md`).

**Source.** `numerical_notes/theory/waisman_msa_closed_form.md` (the derivation and its convention
hazards), `todo/waisman_msa_plan.md` (Group MSAX, the numerical partner), and the failure that
prompted both: `numerical_notes/results/fisher_widom/fw_vs_chi_id.md` §1.1.

---

## Why this group exists

Group FWL's Stopper Fig. 8 gate fails at `z = 5` and is unattemptable at `z = 10`, and the cause was
*measured*: the numerical OZ solver converges to **different MSA solutions** depending on the radial
grid, and λ-ramping pins the branch only up to `βK ≈ 3`. That is not a discretisation error — **the
ambiguity is in the equation**. The exact MSA replaces "which fixed point did DIIS find" with "which
root of an explicit algebraic system is physical", and *that* is a statement Lean can carry.

Two targets justify the group on their own:

* **MSAEXACT.3** is the formal counterpart of the measured `βK ≈ 3` boundary — a uniqueness theorem
  for the physical root below an explicit coupling threshold.
* **MSAEXACT.5** turns the project's founding premise, *FMSA is the first order of MSA*, from a
  working assumption into a theorem.

## Why it is an unusually good target

The whole content is **algebra over `ℝ` with `e^{−zσ}` as a parameter**. No contour integrals, no
`L¹`, no Wiener algebra — nothing that touches the 7 math axioms. Contrast every other analytic
group in this tree, whose costs are exactly those. **Constraint for both groups: no new axiom.** If
a step appears to need one, the algebraic route was abandoned somewhere; go back and find where.

## Substrate already in the library — reuse, do not re-derive

| piece | where |
|---|---|
| `φ₁`, `φ₂` truncated-Laplace moments and their closed forms | `HardSphere/BaxterFactor.lean` — `phi1_formula`, `phi2_formula`, `phi1_shifted_formula` |
| `Q̂₀ ≠ 0` at a Yukawa rate / on the imaginary axis | same — `Q0_ne_zero_at_yukawa`, `Q0_imaginary_axis_ne_zero` |
| the HS mixture Baxter matrix and its invertibility | `HSMixture/MatrixQ0.lean` — `q0_entry`, `Q0_mat_phys`, `Q0_mat_phys_isUnit_det_of_diag_dom` |
| **the `K = 0` target**: `(1−q̂₀(k))(1−q̂₀(−k)) = 1−ρĈ_PY(k)` | BAXTER.3 `baxter_wiener_hopf_complex` = MRS.8 at `N=1`; already reused by PYE.6 |
| first-order linearity in `K` (for MSAEXACT.5) | Group Y1 `bMulti`; MRS.3 (★) `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` |

---

## Group MSAEXACT — single component

Opens with MSAX.1. **MSAEXACT.1 cannot start before MSAX.1's gate 0** (reproduce the elimination
degree in this project's conventions) — the Lean statement has to quantify over the *right*
algebraic system, and the theory note flags the degree as unsettled.

| Task | Title | Status |
|------|-------|--------|
| MSAEXACT.1 | `exactMSA_factorization` — `\|1 − ρQ̂(ik)\|² = 1 − ρĉ_MSA(k)`, `Q̂` the **non-compact** Baxter factor (pole at `s=−z`) | ✅ **CLOSED via `exactMSA_hcore` axiom, 2026-08-21** (`MSAFullFactorization.lean`): `factorization_of_core` (pure algebra) + the sympy-verified axiom ⇒ `exactMSA_factorization`. `#print axioms` = `[propext, Classical.choice, Quot.sound, exactMSA_hcore]`. Staging (`factorization_of_core`) splits `\|1−ρQ̂\|²` into `Dt⁰`(=`1−ρ𝓕[c_HS]`) + `O(Dt)` + `O(Dt²)`. ⚠ compact `exactMSA_iff_core` route is a DEAD END (entire-in-`k` ≠ physical) |
| MSAEXACT.6 ⭐ | discharge `hcore` — the closure-recovery ring `ρ(𝓕[c_core]+𝓕[c_tail]) = 2Dt·X − Dt²·Y` under Blum–Høye (29′)/(33) | ⊘ **LANDED as documented sympy-verified axiom `exactMSA_hcore`, 2026-08-21.** Math CERTIFIED in `exactMSA_cert.py` (parent repo): `Δ = m29·r29 + m33·r33` exactly (poly-div remainder 0), via SEPARATE physics multipliers + Gröbner over inverse-atom relations (2 coupled extras hand-verified). Lean mechanism PROVEN at `Dt⁰` (`Cert_dt0_full.lean` compiles axiom-clean, `linear_combination` over `(C,S)`-chunks). ⛔ **`ring` is the wall, MEASURED (2026-08-22) — NOT a heartbeat budget:** a clean single `(cos,sin,exp)`-graded `Dt²` coefficient (323 mono, deg≈22, `maxRecDepth` set, no error cascade) costs `ring` **3h12m / 23GB**; the irreducible per-order pieces are ~1000–2843 high-deg mono ⇒ the per-order reassembly (mathematically unavoidable — one full normalization) extrapolates to **~weeks / ~200GB (OOM-risk @250GB)**. Atom (inverse-atom) form is WORSE: deg≈35, 16 vars, 4.5MB/chunk. `native_decide` blocked (`MvPolynomial` semiring noncomputable). ⇒ **full closure is NEARLY INFEASIBLE with current tooling; the earlier "30-min timeout / upgradeable" note was measured on the wrong (denom-cleared, high-deg) form + a `maxRecDepth` bug and is RETRACTED.** ✅ **Fourier layer DISCHARGED 2026-08-22** (`YukawaOZ/ExactMSA6Certificate.lean`, out-of-`defaultTargets` lib `ExactMSA6Certificate`): `exactMSA_hcore_of_residual` proves the *exact* `exactMSA_hcore` statement from ONE pure-algebra axiom `exactMSA_kspace_residual` (both radial transforms rewritten to closed cos/sin/exp form via `radial_fourier_coreCorrection`+`psi1/2/4`+`one_sub_exp`+`coshRatio`+`radial_fourier_cMSAtail`); `#print axioms` = std-3 + `exactMSA_kspace_residual` (NOT the original axiom) ⇒ only the polynomial identity remains axiomatic. ⭐ MSAEMIX.4 (matrix analog) has a DIFFERENT wall — not this ring timeout but a c-side derivation: `msaemix_hcore_cert.py` shows the mixture core = scalar 5-basis only at EQUAL σ (with Σ_l-coupled coefficients, not the scalar formula) and PIECEWISE at unequal σ |
| MSAEXACT.2 | elimination at one tail — degree 8, **REDUCIBLE = two quartics**; the physical branch is a quartic | ✅ **DONE 2026-08-10** (`YukawaOZ/MSAElimination.lean`, axiom-clean; Python `msax_elimination.py`). ⚠ **Corrects the earlier "irreducible"** — that was a float + uncorrected-Eq(2) artefact |
| MSAEXACT.3 ⭐ | `msaRoot_unique_of_coupling_lt` — **exactly one physical root below an explicit coupling threshold** | ✅ **provable core DONE 2026-08-10** (`MSAClosedForm.lean`, axiom-clean): positivity/(39) selection + `physical_baxter_factor_unique` + the **capstone** `msaRoot_unique_of_coupling_lt` (physical uniqueness given the measured monotone coupling). ⚠ The monotonicity of `a` in `K` on the physical branch, and the explicit `βK≈3` threshold, stay **measured** (branch of a transcendental quartic — outside `ring`) |
| MSAEXACT.4 | `pyA_pyB_satisfy_zero_coupling` — at `K = 0` the PY coefficients annihilate all three of Waisman's equations, **for every `w`** | **✓ DONE 2026-08-10** (axiom-clean) |
| MSAEXACT.5 ⭐ | `firstOrder_amplitude_eq_hardSphere_dressed` — linearising the self-consistency in `K` returns FMSA-DP's HS-dressed amplitudes | **✓ DONE 2026-08-10** (`Closures/FirstOrderEquivalence.lean`, axiom-clean). From `D(K)·F(K) = c·K` — Blum–Høye (29′) — with `F` the **full** Baxter factor, the derivative at `K=0` is `c / F 0`: it sees `F 0`, the **hard-sphere** factor, and `F'` **cannot appear** because it is multiplied by `D 0 = 0` (itself derived, not assumed). So freezing the propagator at hard-sphere is not an approximation at first order — it is forced. ⚠ Conditional on the derivative existing: that is FOEQ.5 |

### Landed

**MSAEXACT.4 — `LeanCode/YukawaOZ/MSAClosedForm.lean`** (2026-08-10, build 8558 jobs,
`#print axioms` = the standard three on all four theorems). Waisman's system is defined in
`(ξ, K, z, a, b, w)` with `w = v/K` — the variable in which `K → 0` is regular, since Eq. (2)
carries `v²/(2Kz²e^z)` and the limit is `0/0` in `v`. `y0/y1/y2`, `res3a/res3b/res3c_zero`, the
`K = 0` reduction lemmas (every transcendental drops out), `pyA`/`pyB`, and the headline
`pyA_pyB_satisfy_zero_coupling` — all three residuals vanish **identically in `ξ` and for every
`w`**. The `∀ w` is the substantive clause: it is the formal record that the `K = 0` system does
**not** determine `w`, which is precisely why the physical branch must be selected by continuity
rather than read off the algebra. By-product `y0_py_eq_contact` confirms Waisman's `y₀` is the PY
contact value `(1+ξ/2)/(1−ξ)²`. Non-vacuity by an explicit numeric `example`.

⚠ **Bookkeeping note.** The raw `grep -rn "^axiom "` count moved 10 → 11 during this period, but
**not from this group**: the new hit is a third *prose* false positive (an `-- axiom form —` comment
in `YukawaOZMix/MixturePoleExhaustion.lean`). The real ledger is unchanged at **8 = 7 math + 1
physics**. Read the count as `11 = 3 prose + 8 real`.

### Notes per task

**MSAEXACT.1.** The ansatz is the hard-sphere quadratic plus one exponential per tail
(theory note §4); setting all amplitudes to zero must reduce to the existing `Q̂₀`, which is the
statement's own sanity check and should be a corollary, not a separate proof. Reuses the `φ` formulas
directly.

**◑ Bounded down-payment landed 2026-08-10** (`YukawaOZ/MSABaxterTransform.lean`, axiom-clean):
`msaBaxterFn` (the Baxter function `q0_poly + D·e^{−zr}`), `msaBaxterFn_yukawa_zero` (the `D = 0 ⇒
q0_poly` sanity corollary — exactly as this note prescribes), and the two Yukawa transform lemmas
that the factorization is assembled from: `yukawa_laplace_unit`
(`∫₀^1 e^{−zr}e^{−sr} = (1−e^{−(s+z)})/(s+z)`, so `Q̂(s) = Q̂₀(s) − 2πρD·(1−e^{−(s+z)})/(s+z)` — one
simple pole per tail) and `yukawa_tail_laplace` (`∫_{r>1} e^{−z(r−1)}e^{−sr} = e^{−s}/(s+z)`, the
exterior DCF piece where `r·c(r)` is a clean Yukawa).

⚠ **The full factorization is the remaining analytic core** and was scoped out deliberately: it is
the *real-space* statement that the ansatz **recovers the MSA closure** `c = −βu` on the exterior,
i.e. the k-space identity `|Q̂_MSA(k)|² = 1 − ρ𝓕[c_MSA](k)` with `q_MSA`, `c_MSA` independently
defined. That re-runs `baxter_wiener_hopf_factorization` (Group BAXTER) with the modified polynomial
coefficients and the Yukawa tails in *both* `q` and `c` — several new integral formulas (exp×cos/sin,
the exterior tail) plus a large algebraic verification with the Pythagorean identity — a multi-file
effort comparable to the original BAXTER group, not a one-shot emit. The transform identity alone is
*definitional* (ĉ is defined by the factorization); the content is the closure recovery.

### Landed — MSAEXACT.1 the CORRECT non-compact reduction + MSAEXACT.6 defined (2026-08-20)

`YukawaOZ/{MSAExteriorTransform, MSABaxterKSpace, MSAFullFactorization}.lean`, axiom-clean, build
8631 jobs. **This supersedes the compact-ansatz route below** (the third down-payment's
`exactMSA_iff_core`).

⛔ **Why the compact route died.** The physical MSA `c = −βu = K e^{−z(r−1)}/r` is infinite-range,
so `1 − ρĉ_MSA(k)` has poles at `k = ±iz` and the Baxter factor `Q̂(s)` a genuine simple pole at
`s = −z` (residue `D = Dt·e^z`). A transform over `[0,σ]` — entire in `k` — can never equal it, so
the compact `msaBaxterFn = q0_poly + D·e^{−zr}` ansatz is unsatisfiable by a genuine real-space `c`
(verified 3 ways, k-dependent `D`-roots). `exactMSA_iff_core` is a TRUE algebraic iff but its
`hcore` is **vacuous** for physical MSA.

✅ **The correct route — stage the modulus of the non-compact factor.** `Q̂(ik)` is **affine in `Dt`**
(`A, q′, tail` all `Dt`-linear; `γ` has none), so `MSABaxterKSpace` writes `msaQre/msaQim` (Re/Im of
`ρQ̂(ik)`, validated ==`baxter_F` to 1e-14) with the `Dt`-affine split `msaQre_eq/msaQim_eq`, and the
`Dt⁰` bridges `msaQre_zero/msaQim_zero` (= the `q0_poly` cos/−sin integrals). `MSAExteriorTransform`
supplies the exterior transforms `∫_{Ioi 0} e^{−zr}cos/sin = z/(z²+k²), k/(z²+k²)`. Then
`MSAFullFactorization.msa_factor_split` reorganises

    |1 − ρQ̂(ik)|² = (1 − ρ𝓕[c_HS]) − 2Dt·X + Dt²·Y      (X,Y the O(Dt),O(Dt²) brackets)

with the `Dt⁰` bracket collapsed to the hard-sphere factor by `baxter_wiener_hopf_factorization`
(BAXTER.3). The capstone **`factorization_of_core`** then concludes MSAEXACT.1 from a *single*
hypothesis `hcore : ρ(𝓕[c_core] + 𝓕[c_tail]) = 2Dt·X − Dt²·Y`. Unlike the compact one this `hcore`
is **satisfiable** (`Q̂` carries the physical pole).

### MSAEXACT.6 — the `hcore` closure-recovery ring (the gap, 2026-08-20)

**MSAEXACT.6 = discharge `hcore` for the specific `coreCorrection` dictionary under (29′)/(33).** The
c-side is fully closed and pinned (`MSACoreTransform.lean`: `radial_fourier_coreCorrection` glue,
`coshRatio`/`one_sub_exp` sine integrals; dictionary `c1=−da, c2=−db, c3=−½ξda, c4=−v/z,
c5=−v²/(2Kz²)` == `−minus_C` to 5e-15). The match closes by
`linear_combination m29·h29 + m33·h33` with `h29 : Dt·F = 2πK/z`, `h33 : 2πG·F = (A+z q′+(z²/2)γDt)/z²`
— but **`m33 ≈ 1935 symbolic ops** and there is **no small-multiplier route**: (a) eliminate `Dt`
via h33 → `Dtsol` op-count 317, blow-up; (b) rewrite `K` via h29 + `bhF→bhP/(2πG)` → FALSE (breaks
r29); (c) keep `A/q′/γ` atomic → FALSE (needs their `(Dt,G)` forms); (d) `Dt`-order split → collapse
identity FALSE, degrades to a `D2·Dt`≈same-size multiplier. Only path = **sympy→Lean codegen of
`m29`(93 ops, explicit `−(z/2π)∂Δ/∂K`) + `m33` then `field_simp; linear_combination; Pythagorean;
ring`** — robust but slow, OOM risk. This is the honest BAXTER-scale boundary. **Sole gap of
MSAEXACT.1, MSAFAM.5/.6@N=1; MSAEMIX.1 is the matrix analog.**

### MSAEXACT.6 — the codegen route MEASURED infeasible; Fourier layer discharged (2026-08-22)

The "sympy→Lean codegen + `ring`" path above was **built and measured**, and it does not close in any
practical budget — the blocker is `ring`'s performance, not a heartbeat cap:

* **Clean `ring` timings** (`maxRecDepth 1000000`, no error cascade, `lake env lean`, 250 GB box):
  * dense control `((a+b+c+d)^6)^2 = (a+b+c+d)^12` — 455 mono, deg 12: **17 s**.
  * dense control deg 16 — 969 mono: **1 m 45 s**.
  * **one `(cos,sin,exp)`-graded coefficient of the `Dt²` identity — 323 mono, deg ≈22: `ring`
    3 h 12 m, 23 GB.**  Degree, not count, is the enemy (the cleared wave-denominators `k⁵·(z²+k²)²`
    push total degree to ~22).
* **The earlier "30-min timeout, doesn't decompose, upgradeable" note was wrong twice over:** it was
  measured (i) on the high-degree *denominator-cleared* form, and (ii) with a `maxRecDepth` bug (the
  `exactMSA_codegen.py`/`scaletest.py` headers omit `set_option maxRecDepth`, so the flat 100s-term
  sums blew the default depth 512 and threw 101 "failed to synthesize" errors — those runs were timing
  a *failing* elaboration, not `ring`).  **RETRACTED.**
* **The irreducible pieces are large.** Every representation forces one full normalization of a
  per-order identity: cleared form ≈2843 high-deg mono (deg 22); inverse-atom form is *worse* — the
  `Dt¹` chunks are 897–1034 mono at total degree ≈35 in 16 atoms (both `k` and `ki=1/k` present),
  4.5 MB per chunk (the 897-mono chunk did not finish in 20 min, still only 813 MB = stuck in
  elaboration).  Extrapolating the 323→2843 curve: the per-order reassembly ≈ **weeks / ~200 GB**.
* **`native_decide` is unavailable:** `MvPolynomial`'s `AddMonoidAlgebra.semiring` is noncomputable,
  so the compiled-kernel route fails outright.  A custom computable reflection would add
  `Lean.ofReduceBool` and is a major framework — not attempted.

**What DID land (`YukawaOZ/ExactMSA6Certificate.lean`, out-of-build lib, 2026-08-22):**
`exactMSA_hcore_of_residual` proves the *exact* statement of `exactMSA_hcore`, deriving it from a
single pure-cos/sin/exp axiom `exactMSA_kspace_residual` by rewriting both `radial_fourier` integrals
into closed form (`radial_fourier_coreCorrection` + `psi1/2/4_formula` + `one_sub_exp_sin_integral` +
`coshRatio_sin_integral` + `radial_fourier_cMSAtail`, then `simp [mul_one, one_pow]`).  Its
`#print axioms` is `[propext, Classical.choice, Quot.sound, exactMSA_kspace_residual]` — the Fourier
/ definitional layer is fully formalized and the *only* remaining axiom is the polynomial identity
itself.  The file is deliberately **out of `defaultTargets`** (lib `ExactMSA6Certificate`); a normal
`lake build` skips it, `lake build ExactMSA6Certificate` verifies it on demand.  Net: MSAEXACT.6 is
as closed as `ring` allows — the physics is proven, the residual is one explicit, externally-certified
polynomial identity that is *nearly infeasible* to discharge in-kernel.

### Landed — MSAEXACT.1 third down-payment (`YukawaOZ/MSADCFTransform.lean`, 2026-08-19) — ⚠ SUPERSEDED

⚠ **SUPERSEDED by the correct non-compact route above (2026-08-20).** `exactMSA_iff_core` is the
compact-ansatz reduction; its `hcore` is unsatisfiable for physical MSA (see ⛔ above). The transform
infrastructure here (`yukawa_tail_sine_integral`, `radial_fourier_cMSAtail`, `msaBaxter_cos/sin_transform`)
is still valid and reused; only the `q0_poly+D·e^{−zr}` *vehicle* is dead.

Build 8787 jobs, all six theorems on the standard three axioms, own `^axiom ` count 0.

The `c`-side has two halves of very different character, and this file closes one of them and
**isolates** the other rather than pretending they are the same job.

* **Closed — the exterior.** The MSA closure *gives* `c(r) = −βu(r) = K e^{−z(r−σ)}/r` for `r > σ`.
  The radial transform's `r` cancels the Yukawa's `1/r` exactly, so `yukawa_tail_sine_integral`
  (`∫_σ^∞ e^{−z(r−σ)}sin kr dr = (k cos kσ + z sin kσ)/(z²+k²)`, by `integral_Ioi_…_of_tendsto'`)
  and then `radial_fourier_cMSAtail` finish it. This is the Fourier partner of the existing
  Laplace-side `yukawa_tail_laplace`.
* **Connected.** `msaBaxter_cos_transform`/`msaBaxter_sin_transform`: the ansatz's transform really
  is hard-sphere `+ D·`exponential, so `msa_lhs_split` is a statement about `msaBaxterFn` itself
  rather than about an unmotivated pair of reals.
* ⭐ **`exactMSA_iff_core` — the reduction.** Given only that `ĉ_MSA` splits as
  `ĉ_HS + cCore + ĉ_tail`, the MSA factorization holds **iff** `ρ·cCore` equals an explicit
  closed form: the `O(D)` bracket, minus the `O(D²)` bracket of `msa_exp_sq_modulus`, minus the tail
  above. Nothing about the core is assumed — it is one scalar unknown.
  `exactMSA_core_at_zero_coupling` checks the `K = D = 0` case returns `cCore = 0`.

⇒ **All that is left of MSAEXACT.1 is: show Waisman's Eq. (2) has that transform.**

⚠ **Why this is an `iff` and not a theorem about Eq. (2).** Eq. (2) as printed does not satisfy it.
The `1/x` repair of theory note §7e was found at contact, through `y₀`; before formalising anything
the target was checked over all `k` by `exactMSA_cside_check.py`, which evaluates
`F(ik)F(−ik) = 1 − ρĉ(k)` with the two sides sharing no code path (Laplace transform of the Baxter
factor vs Fourier transform of the DCF). Corrected: worst **9.9e-10** over 8 states × 8 `k`, and
that is the quadrature floor at the smallest `k` — every `k ≥ 1` entry is `1e-15`–`1e-16`. As
printed: worst **5.1**, and ⭐ **`1 − ρĉ(k)` goes negative at 3 sampled points**, impossible for a
squared modulus. So the printed form is refuted by the factorization alone. Formalising it would
have been formalising a false statement.

⚠ **Lean note.** `Set.indicator_of_mem`/`_notMem` need the membership in `∈` form
(`Set.mem_Ioi.mpr h`), not the unfolded `<`; and `fun_prop` does not discharge
`IntervalIntegrable` here — spell the continuity out and use `Continuous.intervalIntegrable`.

### Landed — MSAEXACT.1 second down-payment (`YukawaOZ/MSAFactorizationSplit.lean`, 2026-08-19)

Build 8786 jobs, `#print axioms` = the standard three on all five theorems, own `^axiom ` count 0.

⚠ **First, a check that saved the effort from being wasted:** `baxter_wiener_hopf_factorization` is
**not general in `q`**. It is proved *for* `q0_poly` and `c_HS`, from their explicit cos/sin transform
formulas plus `field_simp; ring`. So MSAEXACT.1 cannot be a corollary of BAXTER.3 — confirmed by
reading the statement, before writing anything.

But it can be **split**, and that is what this file does.

* `exp_cos_integral`, `exp_sin_integral` — the two transforms the `q`-side was missing, i.e. exactly
  the "new integral formulas (exp×cos/sin)" this note flags. FTC with the explicit antiderivatives;
  the hypothesis is `z² + k² ≠ 0`, not `k ≠ 0`.
* `msa_exp_sq_modulus` — `Rez² + Imz² = (1 − 2e^{−zσ}cos kσ + e^{−2zσ})/(z²+k²)`, the squared
  modulus of one exponential integral. ⚠ **The algebra had to be abstracted into
  `sq_modulus_algebra` with the exponential opaque**: left concrete, `field_simp` rewrites
  `e^{−zσ}` through `Real.exp_neg` into `(e^{zσ})⁻¹`, clears it as one more denominator, and the
  `linear_combination` multiple the algebra predicts no longer closes the goal.
* ⭐ `msa_lhs_split` — with `q_MSA = q0_poly + D·e^{−zr}`, the factorization's left side is
  *identically*

      (1 − Re)² + Im² = [(1 − Re₀)² + Im₀²] − 2D[(1 − Re₀)Rez − Im₀Imz] + D²[Rez² + Imz²]

  and `msa_lhs_split_at_zero` identifies the first bracket as `1 − ρĉ_HS(k)` via BAXTER.3.

⇒ **MSAEXACT.1 is now "match the `O(D)` and `O(D²)` increments against `−ρ(ĉ_MSA − ĉ_HS)(k)`"** —
which is the content of Waisman's Eq. (3) — rather than "re-run BAXTER with tails". The `O(D²)`
coefficient is already closed.

⚠ **Still open, and named:** the `c`-side. `ĉ_MSA(k)` needs Waisman's inner Eq. (2) — five terms,
including the `v²(cosh zr − 1)/r` piece carrying the missing `1/x` of theory note §7e — plus the
exterior Yukawa tail (`yukawa_tail_laplace`, already landed). That match is the remaining grind.

**MSAEXACT.2. ✅ FORMALIZED 2026-08-10** (`YukawaOZ/MSAElimination.lean`, axiom-clean; the exact
symbolic elimination is `msax_elimination.py`, emitting the Lean coefficients). Eliminating `a` (from
`r3`, linear) then `b` from the three residuals gives a polynomial of **degree 8 in `w`** — but:

⚠ **CORRECTION to the earlier gate-0 record ("degree 8, irreducible").** With the *corrected*
Waisman Eq. (2) (the missing `1/x`, `msa_exact.HCY.minus_C`) and *exact* coefficients (`E = e^{−z}` a
free symbol, `ξ, z, K` rational), the degree-8 elimination **FACTORS over ℚ[E] as two quartics**,
`P₈ = C₀·F₄·G₄` — it is **reducible** at every state point tested. The earlier "irreducible" was a
double artefact: (i) **float** coefficients, which `sympy.factor` cannot split, and (ii) the
*uncorrected* Eq. (2). Verified in Lean as the ring identity `elimination_factors`, and
`elimination_sound` shows every solution of the three residuals satisfies `F₄·G₄ = 0`.

⭐ **The physical branch is a quartic.** The Percus–Yevick-connected (physical) root lies in the
**single** factor `G₄` at every state point — `(0.2,5,0.5)`, `(0.3,1.8,1)`, `(0.1,10,2)`, and
**Waisman's own published point** `(0.49, 28.751, 1.336)`, where the elimination reproduces his
`a = 51.84` (his `51.85`) and `v = 2.432` to printed precision. So the folklore *quartic* for the
physical branch is essentially **vindicated**: the octic is (physical quartic) × (unphysical
quartic), not an irreducible degree 8. Real-root counts observed: 2–4.

⚠ **Ceiling.** One representative state point with `E` symbolic is the honest `ring`-checkable limit.
**Irreducibility of each quartic over ℚ(E)** (true numerically) is *not* formalised — factoring a
quartic is outside `ring`/`decide` — nor is the full `K`-space root count of MSAEXACT.3.

**MSAEXACT.3 ⭐.** The payoff, and **the source leaves it open on purpose**. Blum & Høye 1978 p. 323:
*"with `K_ij` … as known one must expect multiple solutions to occur, of which only one is
acceptable"* — they state an acceptability criterion (their Eq. 41, from `g_ij = g_ji`) which is
**vacuous at `N = 1`**. So there is no single-component selection rule in the literature we hold,
and this task is not formalising a known theorem but supplying a missing one.

Two footholds the source does give:

* **Positivity. ✅ FORMALIZED 2026-08-10** (`MSAClosedForm.lean`, axiom-clean). Their Eq. (39) makes
  `1 − ρĉ(0)` a *perfect square* `(A/2π)²` at `N = 1`, so `1 − ρĉ(0) ≥ 0` is a **necessary condition**
  on the physical root — "possibly most of the theorem", and now landed:
  - `compressibility_nonneg_of_baxter_sq` — `S = B² ⇒ S ≥ 0 ∧ (S = 0 ↔ B = 0)` (the spinodal is
    exactly `A = 0`);
  - `no_real_baxter_factor_of_neg` — `S < 0 ⇒ ¬∃ B, S = B²`: **inside the spinodal is structurally
    unreachable** (no real Baxter factor), the formal counterpart of FWL's negative `1 − ρĉ(0)` at
    `z = 5` being off the physical branch;
  - `physical_baxter_factor_unique` — the `N = 1` acceptability criterion that Blum & Høye's `g_ij =
    g_ji` (Eq. 41) leaves **vacuous** at one component is `A/2π > 0`, and `∃! B > 0, B² = S`: the
    positive Baxter factor is a **unique** root. This is the missing single-component selection rule,
    supplied;
  - concrete: `pyA_eq_sq` (`pyA ξ = ((1+2ξ)/(1−ξ)²)²`, the `K=0` instance of (39)), `pyA_pos`
    (PY compressibility `> 0` on `ξ ∈ (0,1)` — the reference fluid is stable), and
    `baxter_sq_double_root_at_spinodal` (`B²` has value **and** derivative `0` at `B=0` ⇒ **track
    `A`, not `a`**, the §7h ramp fix).
* **Direction. ✅ FORMALIZED as the capstone 2026-08-10** (`msaRoot_unique_of_coupling_lt`). The map
  `γ ↦ D` is linear, hence unique (their Eq. 34); only `K ↦ D` is multivalued. Phrased, per the note's
  own suggestion, as *invertibility of the selection (`physical_baxter_factor_unique`: `a ↦ B=√a` is a
  bijection on the physical `A/2π>0` branch) plus monotonicity of the coupling*: two acceptable roots
  (`B>0`, `B²=a`) at the **same coupling** coincide, given that the coupling **pins** the
  compressibility (`hcoupling_pins`, injectivity). So below the threshold the physical solution is
  unique.

⭐ **The measured monotonicity that `hcoupling_pins` encodes** (`msax_elimination.py`; investigated
2026-08-10): along the PY-continued physical branch the compressibility `a = ∂βp/∂ρ` is **strictly
decreasing in `K`**, from the PY value to `0` at the spinodal — e.g. at `ξ = 0.2, z = 5`,
`a: 4.79 → 0` monotonically as `K: 0 → K_c ≈ 3.32` (`spinodal_coupling`). The spinodal `a = 0` **is**
the explicit threshold, and there `a = (A/2π)²` has its double root, so the branch is unique on
`[0, K_c)` and degenerates at `K_c`.

⚠ **What stays measured (not formalised).** The monotonicity of `a(K)` and the numeric threshold
`K_c ≈ 3.32` (`βK ≈ 3`) are properties of the physical branch of the **transcendental** elimination
quartic (MSAEXACT.2, `E = e^{−z}`) — continuity/branch statements outside `ring`/`decide`. They are
the `hcoupling_pins` hypothesis of the capstone and the FWL numeric input, respectively. The
*acceptability rule and the uniqueness it yields* are proved; the *branch monotonicity* is measured.

### §8 foothold — real solutions, the spinodal, and the fold (theory note §8)

The theory note now has a dedicated chapter §8 ("Real solutions, the spinodal, and the fold"). Its two
structural claims are formalised; its branch geometry is the measured ceiling. Three tiers:

**Tier 1 — PROVED (`MSAClosedForm.lean`, axiom-clean).** Everything that reduces to the perfect-square
identity, i.e. an algebraic fact at fixed `K`:
* the positivity/selection footholds above (`compressibility_nonneg_of_baxter_sq`,
  `no_real_baxter_factor_of_neg`, `physical_baxter_factor_unique`, `baxter_sq_double_root_at_spinodal`);
* **✅ NEW 2026-08-12** — the §8 chapter's two theses, as checked statements:
  - `compressibility_realizable_iff_nonneg` — **the wall as a range**: `(∃ B, a = B²) ↔ 0 ≤ a`. The
    exact compressibility's achievable set is exactly `[0,∞)`; `a < 0` is *outside the range*, so no
    solver **and no analytic continuation** can produce it (§8b). `no_real_baxter_factor_of_neg` is the
    contrapositive of the forward half.
  - `exact_vs_firstOrder_compressibility_wall` — **why FMSA crosses it**: the exact `aExact K = (A K)²`
    is `≥ 0` for *every* `K`, whereas the affine `aFMSA K = a₀ − s·K` (DP map linear in `K`, FOEQ
    `msaOuter_eq_smul_deriv`) is `< 0` once `s·K > a₀`. Perfect square = the wall; affine truncation =
    crosses it freely. Trivial by design — the content is that it *reduces* to square-vs-affine given
    the two proved ingredients.

**Tier 2 — abstract-provable but not yet done (candidates, gated on demand).** The *local* branch
existence is within reach of the FOEQ.5 IFT engine (`exists_hasDerivAt_root_of_prodDomain_ift`): "the
real branch persists as a differentiable function of `K` wherever the Jacobian is invertible, and the
IFT hypothesis fails exactly where `det J = 0`." That packages the spinodal-passes / fold-terminates
*dichotomy* abstractly (regular ⇒ continue, singular ⇒ IFT gives nothing) without the finite-`K`
transcendental input. Not built — it would restate the IFT with a running base point; low marginal
value over the `K=0` capstone until a mixture (`N>1`) forces it.

**Tier 3 — MEASURED ceiling (theory note §8a/§8b; outside `ring`/`decide`).** The finite-`K` branch
geometry, all statements about the *transcendental* elimination quartic (MSAEXACT.2):
* the full finite-`K` Jacobian is **not** the block-triangular `K=0` one, so `det J = (2π)^n∏F₀²`
  (FOEQ.5) does **not** apply away from `K=0`;
* the spinodal `A = 0` is a **regular** point of that Jacobian (`|det J| = 2e−2…8e−1`, measured);
* the real branch continues to a **fold** `det J = 0` a few % lower in `T*`, and goes complex beyond
  it — the radius of convergence of the `K=0` HS-reference series is fold-bounded (§8b);
* the FMSA slope's sign (`a_FMSA` more compressible ⇒ spinodal too high in `T*`) — MSAX.3 measurement.

So the §8 chapter is formalised **exactly to the fixed-`K` algebraic boundary**: the wall and the
crossing are theorems; where the wall sits in `(η, z, K)`-space and how the branch dies at the fold
stay measured, for the same reason MSAEXACT.3's `hcoupling_pins` does.

**MSAEXACT.4.** Should be nearly free: BAXTER.3 = MRS.8 at `N=1` is already in the library and PYE.6
already wires it to the physical PY objects (`pyBaxterMat`, `pyT0Mat`, `dp_zeroth_order_is_py_n1`).
Extend that wiring rather than re-deriving it.

**MSAEXACT.5 ⭐.** The structural statement of theory note §6: the amplitude is
`D ∝ K/Q̂(z)` with the **full** Baxter factor, whereas FMSA-DP has `K/Q̂₀(z)` with the
**hard-sphere** one. Linearising about `Q̂ = Q̂₀` must return `_b_of_s`. Reuses Y1's linearity and
MRS.3's (★). ⚠ Like PYE.2, this will need the **rates frozen** — free rates sit in `s + z` and the
map is not linear.

---

## Group MSAEMIX — mixture

**⭐ UNGATED 2026-08-19.** The gate was "MSAX.5 returns GO". MSAX.5's go/no-go was **bypassed
deliberately** when MSAX.6 closed (2026-08-13, `todo/waisman_msa_plan.md`): two of its three criteria
were already answered, and the third — root selection — is exactly what the mixture *supplies*, since
Blum & Høye's Eq. (41) is a criterion at `N ≥ 2` and vacuous at `N = 1`. MSAX.6 itself is closed and
externally gated (72/72 Tang & Lu column-II contact values to their printed precision), so the
algebra the mixture group formalises is the algebra that was measured.

| Task | Title | Status |
|------|-------|--------|
| MSAEMIX.0 ⭐ | mixture positivity, the stability determinant, and what (39) does **not** see | **✓ DONE 2026-08-19** (`YukawaOZMix/MSAMixturePositivity.lean`, axiom-clean, 9 theorems) |
| MSAEMIX.1 | `msaMixture_factorization` — the matrix form of MSAEXACT.1 at general `N` | ✅ **(★) cancellation DONE 2026-08-19** (`MSAMixtureCancellation.lean`) + **staged to a matrix `hcore` 2026-08-20** (`MSAMixtureFactorization.lean`, axiom-clean): `matBaxterProd_split` + `matMixtureFactorization_of_core` reduce the matrix factorization to a single matrix `hcore` ring — **the matrix analog of MSAEXACT.6** — with the coupling-`0` part discharged via the HS-mixture `matSF_of_baxterFourierWH` (`matMixtureFactorization_of_baxterFourierWH`). ⚠ the matrix `hcore` for the specific MSA factor is the analytic core. **Concrete increment `Q₁` DONE 2026-08-21** (`MSAMixtureConcrete.lean`): `Q0_mat_c_sub` (the mixture Baxter factor `Q0_mat_c` is **linear in the amplitudes** ⇒ `q`-side increment = same form at the `M,N`-dressed amplitude differences − δ) + `matMSAtail`/`radial_fourier_matMSAtail` (the `c`-side exterior tail is per-entry the scalar `cMSAtail`). ⭐ **the amplitude-difference VALUES landed + validated 2026-08-21** (`mixM/mixN/mixDA/mixDqp`, `MSAMixtureConcrete.lean`): `M_j,N_j` (BH (20)/(21)) from the (★) `Wt,Ct`; `Δq′_ij=Q0phys·M_j+Qppphys_i·N_j` (row index), `ΔA_j=Qppphys_j·M_j+(2π²ξ₂/vac²)·N_j`; reuse existing `Q0phys/Qppphys/xi2/vacMix`. **Validated vs `msa_exact_mix._pieces`** (`msaemix_MN_check.py`): `M,N` err 0, `ΔA,Δq′` ≤1.8e-15, increment linear to 1e-16, over binary eq/uneq-σ + ternary. Remaining = the matrix `hcore` ring = **MSAEMIX.4** |
| MSAEMIX.2 | `msaMixture_reduces_to_scalar_at_fin_one` — the `N = 1` specialisation **is** MSAEXACT.1 | ✅ **DONE 2026-08-25.** *positivity* half (`mixCompressibility_fin_one`, `mixStability_fin_one`); **factorization half's `N=1` bridge DONE 2026-08-20** (`matMixtureFactorization_fin_one_iff`/`matMixtureFactorization_of_core_fin_one`, `MSAMixtureFactorization.lean`): at `N=1` the matrix factorization for a conjugate-pair factor `A∓iB` **is** the scalar Baxter modulus `A²+B²=1−ρĉ` — the `factorization_of_core` shape (`A=1−ρReQ̂`, `B=ρImQ̂`). ⭐⭐ **capstone LANDED** `msaMixture_reduces_to_scalar_at_fin_one` (`MSAMixtureFinOne.lean`): the concrete-`hcore` blocker is gone (MSAEMIX.1's `matMSAmixture_fin_one` supplies it) — with the mixture factor as the conjugate pair `A∓iB`, `matMSAmixture_fin_one` collapses via `matMixtureFactorization_fin_one_iff` + `√(ρ₀ρ₀)=ρ₀` to `A²+B²=1−ρ₀(𝓕[c_HS]+𝓕[c_core]+𝓕[c_tail])`, the scalar exact-MSA modulus. `#print axioms = [propext, Classical.choice, matExactMSAEqualDiam_hcore, Quot.sound]`. ⇒ the one-component mixture IS the scalar MSAEXACT.1 (both halves reduced) |
| MSAEMIX.3 ⭐ | mixture root selection — Eq. (41) as the `N ≥ 2` acceptability criterion | **✓ DONE 2026-08-19** (`YukawaOZMix/MSAMixtureSelection.lean`, axiom-clean, 8 theorems) |
| MSAEMIX.4 ⭐ (**the matrix ring**) | discharge the matrix `hcore` — `matMixtureFactorization_of_core`'s closure-recovery ring | ✅ **DONE (equal σ f0ae03a; unequal σ Stage 3 CLOSED 2026-08-22) — numerical cert BUILT + RUN 2026-08-22 (`msaemix_hcore_cert.py`, parent repo); it REFUTES the earlier "per-entry scalar `msaCoreCorr`" plan.** The cert extracts the mixture core transform from the solved Baxter factor and fits the 5 scalar core-basis transforms {1,r,r³,(1−e^{−zr})/r,coshRatio/r} at σ_ij, checking HELD-OUT k. Findings (all machine-precision): **(A) the identity is SOUND** — `(Baxter product increment)_ij = −√(ρ_iρ_j)(ĉ_MSA−ĉ_HS)_ij`, and `ĉ_MSA−ĉ_HS = core+tail` (tail = `matMSAtail`, exact). **(B) EQUAL σ: the core IS the scalar `coreCorrection` 5-basis per entry** (held-out 3.5e-9, binary+ternary) — the FORM is right — **BUT the coefficients `c₁..c₅_ij` are NOT the scalar formula**: they carry Σ_l species coupling (regression: `c₁ ≠ −(AᵢAⱼ−A⁰ᵢA⁰ⱼ)/(2π)²`, resid 0.15; `c₃ ≠ ξc₁/2` at unequal ρ). ⇒ eq-σ landing needs the mixture Baxter **real-space DCF constant** derivation (Blum–Høye Σ_l convolution), which the "same formula as scalar" assumption got WRONG. **(C) UNEQUAL σ: the core is PIECEWISE** (single-piece 5-basis held-out 1.9e-4 ≫ fit) — breakpoints at λ_ij/mediated points (cf. `_compute_mediated`); `matMSACoreCorr` is piecewise there, NOT per-entry scalar. ⇒ two tiers: eq-σ = coeff derivation (bounded); uneq-σ = piecewise core (mediated-breakpoints scale). ⚠⚠ **EQUAL-ρ IS A DEGENERACY TRAP** (2026-08-22): at equal ρ the candidates `c₁=−(AᵢAⱼ−A⁰ᵢA⁰ⱼ)/(2π)²`, `c₃=ξc₁/2`, `c₄=−v/z` with `v=4π(K diag(ρ)Gt)_ij` pass the constrained held-out test to **1.5e-10** — but at UNEQUAL ρ they fail (2.4e-2), because `√(ρᵢρⱼ)=ρ`, `diag(ρ)=ρI` collapse there. **Never validate a mixture coeff formula at equal ρ** — no ρ-weighting variant is distinguishable. `v_ij` at unequal ρ matches NONE of {`4π(K diag ρ Gt)`, `√ρ`-similarity, `4π√(ρᵢρⱼ)(KGt)`, `4π(√ρ K Gt √ρ)`} (err 0.2–1.1) ⇒ the general coeffs genuinely need the Blum–Høye real-space derivation, not a pattern match. ⭐⭐ **4/5 coeffs CRACKED 2026-08-22** (`msaemix_core_coeffs.py`, parent repo) via the clean k-space relation `ĉ_ij=Q̂_ij(ik)+Q̂_ji(−ik)−Σ_l ρ_l Q̂_il(ik)Q̂_jl(−ik)` (derived from `F̃F̃ᵀ`, ρ_l coupling explicit) + **mpmath-exact coeff extraction** (held-out 1e-16) + regression over unequal-ρ binary/ternary. With `D=diag(ρ)`, single tail, equal σ: **`c₂=(1/4π)[Σ_l ρ_l(q'_il q'_jl−q'⁰_il q'⁰_jl) − Σ_l ρ_l(A_l Ct_jl+Ct_il A_l)]`**, **`c₃=−(1/48π)Σ_l ρ_l(A_l²−A⁰_l²)`**, **`c₄=−(2π/z)Σ_l ρ_l(K_il Gt_jl+Gt_il K_jl)`**, **`c₅=−(8π²/z²)Σ_{l,m}ρ_lρ_m Gt_il K_lm Gt_jm`** — all reduce to scalar `msaCoreCorr` at N=1 (e.g. c₄→−4πρKG/z=−v/z, c₃→−ξda/2). ⭐⭐⭐ **ALL 5 coeffs DERIVED 2026-08-22** (`msaemix_core_derivation.py` symbolic + `msaemix_core_coeffs.py` verify, parent repo) — **c₁ CRACKED via the corrected Baxter real-space relation** `2πr c_ij=−Q'_ij(r)+Σ_l ρ_l ∫₀^∞ Q'_il(t+r)Q_jl(t)dt` (from the Wiener-Hopf split; the earlier baxrel form `∫_r^∞ Q'(t)Q(t−r)` was WRONG). Symbolic convolution (3-region, 0<r<1) of the real-space `Q_ab(r)` [core: q'(r−1)+(A_b/2)(r−1)²+W e^{−zr}+Ct; tail: W e^{−zr}+Ct e^{−z(r−1)}] gives per-pairwise coeffs; total = [linear −Q'_ij] + Σ_l ρ_l[pairwise], core = MSA−HS: **`c₁=−(A_j−A⁰_j)/(2π)+Σ_l ρ_l[c₁ᵖ(MSA)−c₁ᵖ(HS)]`, `c₁ᵖ=(6A_l Ct_il+6A_l W_jl+z(A_l²+6A_l Ct_jl−3A_l q'_jl+6Ct_il q'_jl−6Ct_jl q'_il))/(12πz)`** (+ c₄ carries linear `−zW_ij/(2π)`). ⭐ **ALL-5 closed-form verification (NO fitting) vs mpmath-exact extraction: held-out ~1e-12** (binary/ternary, unequal ρ, z∈[1.5,2.6]). ⭐⭐ **GENERAL N** — every coeff is [per-(i,j) linear] + Σ_l ρ_l (or Σ_{l,m}) from one generic pairwise (i,l),(j,l); verified N=2 AND N=3. ⭐⭐⭐ **`matMSACoreCorr` LANDED IN LEAN 2026-08-22** (`YukawaOZMix/MSAMixtureCore.lean`, commit 2bd09a4, builds green `lake build LeanCode.YukawaOZMix.MSAMixtureCore`, PROVED — no axiom): `coreC1..coreC5` (the 5 derived coeffs, Σ_l species sums, general N, in Lean amplitudes `Q0phys`+`mixDqp`/`Qppphys`+`mixDA`/`Wt`/`Ct`/K/`Gt`) + `matMSACoreCorr` = per-entry `coreCorrection(c₁..c₅,z,σ_ij)` + **`radial_fourier_matMSACoreCorr`** (per-entry the scalar `radial_fourier_coreCorrection`). This RESOLVES the "assemble matMSACoreCorr" blocker. ⭐⭐⭐ **AXIOM LANDED + MSAEMIX.1 CLOSED AT EQUAL σ 2026-08-22** (`YukawaOZMix/MSAMixtureBHRoot.lean`, commit f0ae03a, builds green): built the matrix BH-root infra — **`qhatMixC`/`qhatMixR`** (full mixture `Q̂(s)` at equal σ WITH the Yukawa tails `W̃/(s+z)`, `C̃[e^{−sσ}/(s+z)+σ(1−e^{−sσ})/s]`), **`ftilde`/`FtHS`/`FtMSA`/`Ft1`** (symmetric factor `δ−√(ρᵢρⱼ)Q̂` + HS/MSA/increment), **`MixBHRoot`** (Blum–Høye (29′)/(33′) at equal σ = the physical-solution gate, matrix `h29/h33`). **`matExactMSA6_hcore` (AXIOM)**: at a `MixBHRoot`, `(F̃₀F̃₁ⁿᵀ+F̃₁F̃₀ⁿᵀ+F̃₁F̃₁ⁿᵀ)ᵢⱼ = −√(ρᵢρⱼ)(𝓕[matMSACoreCorr]+𝓕[matMSAtail])ᵢⱼ` — GATED by the root ⇒ SOUND (false off-root, but the gate forbids that). **`matMSAmixture_equalDiam` (THEOREM)**: closes MSAEMIX.1 at equal diameter via the abstract `matMixtureFactorization_of_core` (symmetric √-weight folded into `cHShat/cMSAhat`, `ρ:=1`) + `hHS` + the axiom. **`#print axioms matMSAmixture_equalDiam = [propext, Classical.choice, matExactMSA6_hcore, Quot.sound]`** — clean footprint, mirrors scalar `exactMSA_factorization`. ✅ **MSAEMIX.4/.1 DONE at equal σ.** ⭐ **`hHS` DISCHARGED 2026-08-22** (commit 37b7f02): `matMSAmixture_equalDiam_WH` routes the HS symmetric factorization through the shared HS-mixture WH atoms (`MatBaxterFactorization` + shell-cosine bridge + `MatBaxterFourierWH` for `FtHS`) via `matMixtureFactorization_of_baxterFourierWH` (→ `matSF_of_baxterFourierWH`), so `hHS` is no longer an ad-hoc hypothesis but the same WH machinery the mixture-RDF/OZ★ work rests on; footprint still `[propext, Classical.choice, matExactMSA6_hcore, Quot.sound]`. ⭐⭐⭐ **`hWH` (and `hKDEF`/`hbridge`/`hHS`) FULLY DISCHARGED at N=1 2026-08-22** (`YukawaOZMix/MSAMixtureFinOne.lean`, commit 23b3fc1, green): **`matMSAmixture_fin_one`** — at one component, given ONLY `MixBHRoot` (+ η<1, σ>0, ρ≥0), the MSA factorization holds with the physical HS DCF `ρ₀·𝓕[c_HS]` and **no HS hypothesis**. Bridge `sqrt_rho_qhatMixC_HS_fin_one`: `FtHS`'s √-weighted complex-Laplace `qhatMixC` = the scalar HS Baxter factor `Qhat_complex` (both = `q0_poly` Laplace) via `Qhat_complex_formula` + `Q0phys_n1`/`Qppphys_n1` (⭐ trick: keep `s=I·k` opaque ⇒ rational identity in `(s,e^{−sσ})`, `field_simp;ring`, no `I²=−1`); `FtHS_mul_fin_one` from `baxter_wiener_hopf_complex` + `Chat_complex_eq_radial_fourier`. `#print axioms matMSAmixture_fin_one = [propext, Classical.choice, matExactMSA6_hcore, Quot.sound]` — HS WH atoms PROVED, not assumed. ⚠ general-N `hWH` discharge is a separate large task (mixture-RDF took the determinant route, never wired the WH-cosine `hWH` at general N; needs the √-Laplace↔`matFourierFactor` bridge + `hWK_matrix` integrability + `Mix`-structure bridge). ⚠⚠ **SOUNDNESS FIX 2026-08-22 (commit 5ded95d)**: `qhatMixC`/`qhatMixR` C̃ **box term** had a spurious `σ` factor (`σ(1−e^{−sσ})/s` → correct `(1−e^{−sσ})/s`, box height 1). Latent at σ=1 (`σ·Ct=Ct`) and never exercised by the equal-σ proofs (`FtHS` has C̃=0), it broke `Ft1` (the increment) and hence `matExactMSA6_hcore` at general amplitudes. Exposed by the unequal-σ forward-transform check (`∫Q e^{−sr}=qhat_ij` failed for rows σ_i≠1, err 0.3 → fixed 1e-15); both modules rebuild green, footprints unchanged. Lesson: validate transcribed transforms at σ≠1 (see feedback `sigma_one_masks_bugs`). ⭐ **UNEQUAL σ Stage 1 (commit 08a6791, `msaemix_uneq_core.py`)**: the real-space Baxter `Q_ij(r)` (unequal σ: supported `[λ_ji,∞)`, poly on `[λ_ji,σ_ij]` **width σ_i** shifted by `λ_ji`, C̃ box height C̃) validated to ~1e-8 vs `qhat` (forward transform, all entries, complex s); the Baxter convolution `2πr c_ij=−Q'_ij+Σ_l ρ_l ∫Q'_il(t+r)Q_jl(t)dt` reproduces the k-space core; **the interior core breakpoint of `c_ij(r)` on `(0,σ_ij)` is `r=λ_ji=(σ_j−σ_i)/2`** (C⁰ kink from the poly-support shift; equal σ ⇒ λ=0 ⇒ single-piece 5-basis). ⭐⭐ **UNEQUAL σ Stage 2 (commit 18ef2da, `msaemix_uneq_pieces.py`): piecewise structure FULLY characterized** (all entries machine-precision 1e-14). ⚠ the earlier "piecewise hard" was **quad error** — the convolution integrand has kinks at `t=λ_lj,σ_jl,λ_li−r,σ_il−r`; passing them to `quad` (`points=`) makes every piece fit to 1e-14. `g(r):=2πr c_ij(r)`: **diagonal (λ=0)** = single piece, g-basis `{1,r,r²,r⁴,e^{−zr},e^{+zr}}` (= equal-σ form); **off-diagonal** = TWO pieces, breakpoint `r=|λ_ij|=|σ_i−σ_j|/2`; **OUTER** (|λ|<r<σ_ij) = the full equal-σ basis; **INNER** (0<r<|λ|) reduced (`i<j`: `{1,r,r²,e^±}`; `i>j`: `{r,e^±}`). No r³; g(0)=0 ⇒ c finite. Clean 2-piece structure ⇒ the unequal-σ core is a piecewise `coreCorrection` (breakpoint `|λ_ij|`, outer=equal-σ form, inner reduced). ⭐⭐⭐ **N≥3 has NO mediated breakpoints (commit e973781, `msaemix_uneq_n3.py`)** — the "N≥3 adds 3-body breakpoints" fear is REFUTED for the exact MSA. The 4 t-kink crossings setting the r-breakpoints (`λ_li−λ_lj`, `σ_il−σ_jl`, `σ_il−λ_lj`, `λ_li−σ_jl`) are ALL `σ_l`-**independent** (σ_l enters `λ_li=(σ_l−σ_i)/2` and `λ_lj=(σ_l−σ_j)/2` symmetrically, cancels in the difference), so the interior breakpoint is `|λ_ij|` at EVERY N; verified N=3 unequal σ [1.0,1.4,1.9], all 6 off-diagonal cores 2-piece to 1e-13..1e-15. (UNLIKE FMSA 1st order's 3-body mediated breakpoints — the exact-MSA single Baxter convolution has none.) Both pieces share the 6-term basis `{1,r,r²,r⁴,e^{±zr}}` (inner coeffs partly 0). ⇒ the unequal-σ `matMSACoreCorr` is a clean 2-piece `coreCorrection` (breakpoint `|λ_ij|`), general N. **The breakpoint structure is MSAEMIX.5**. ⭐⭐⭐ **STAGE 3 COMPLETE 2026-08-22 — MSAEMIX.4/.1 CLOSED AT UNEQUAL σ.** KEY: the symbolic-σ Baxter convolution is **CASE-SPLIT-FREE** — on both pieces the four t-breakpoints keep a UNIVERSAL order in σ_l (OUTER `λ_il−r<λ_jl<σ_il−r<σ_jl`; INNER swaps `σ_jl↔σ_il−r`), so σ_i,σ_j,σ_l can all be symbolic and every per-piece kernel comes out as an EXACT `σ_l`-free closed form in `(σ_i,σ_j,z)` (`symbolic_{outer,inner}.py`, parent). End-to-end validated by re-assembling kernels+self vs the numerical convolution: **OUTER 1.8e-14, INNER 8.9e-15** (`verify_{outer,inner}.py`). ⭐ per-`l` **r³ (c3)** AND the **inner c0** are nonzero per-`l` but `Σ_l ρ_l→0` on the BH root (on-root `g={1,r,r²,r⁴,e^±}` outer / `{r,sinh(zr)}` inner); kept for all-amplitude exactness. **Lean core: `YukawaOZMix/MSAMixtureCoreUneq.lean`** (commit 242f4d1, no axioms/sorry, IN default target via `MSAMixtureBreakpointScheme`): `gForm` (shared 7-basis) + `cC0o..cEpo` (OUTER) + `cC0i/cC1i/cEmi/cEpi` (INNER, c2=c3=c4=0) + `matCoreUneq` piecewise@`\|λ_ij\|`. **Lean closing: `YukawaOZMix/MSAMixtureBHRootUneq.lean`** (commit ece6ebe, orphan like the equal-σ `MSAMixtureBHRoot`): `qhatMixCuneq/Runeq` (unequal-σ Baxter factor → `qhatMixC` at equal σ) + `FtHSuneq/FtMSAuneq/Ft1uneq` + `MixBHRootUneq` gate + `matCoreCorrUneq` (the MSA−HS **increment** = `matCoreUneq`(MSA)−`matCoreUneq`(HS); ⚠ SOUNDNESS: the hcore RHS must be the increment, not the full core — the first commit was FALSE, fixed ece6ebe) + axiom `matExactMSAUneq_hcore` + `matMSAmixture_unequalDiam` (closes MSAEMIX.1 at unequal σ via `matMixtureFactorization_of_core`). `#print axioms matMSAmixture_unequalDiam = [propext, Classical.choice, matExactMSAUneq_hcore, Quot.sound]` (std-3 + ONE physics axiom, mirrors equal-σ). Full `lake build LeanCode` GREEN 8799 jobs. ⭐⭐⭐ **BRK.13 CLOSURE SEAM DISCHARGED 2026-08-24** (`YukawaOZMix/MSAMixtureBaxterConv.lean`, orphan lib `MSAMixtureBaxterConvCertificate`, out-of-`defaultTargets` so `lake build LeanCode` stays std-3): the real-space Baxter `baxterQ`/`baxterQ'` (faithful `Qn`/`Qpn` transcription, `msaemix_uneq_symconv.py`) + the **physical exact-MSA core** `baxterConvCore = (−Q'_ij(r)+Σ_l ρ_l ∫_ℝ Q'_il(t+r)Q_jl(t)dt)/(2πr)` + its `K`-family `baxterConvCoreK`, and MSAEMIX.4 Stage 3's identity `baxterConvCore = matCoreUneq` on the two open `(0,σ_ij)` pieces as ONE sympy-backed axiom **`baxterConvCore_eq_matCoreUneq`** (grade 2 per BRK POLICY — the real-space analog of `matExactMSAUnequalDiam_hcore`; grade-1 proof is the exactMSA-class piecewise-convolution ring, measured infeasible). Feeds the BRK-side hypothesis-parametrised lemmas (`exactCore_smooth_off_unique_breakpoint_of_eqOn`, `matCoreUneq_paramDeriv_contDiffOn_{inner,outer}`) ⇒ **`baxterConvCore_smooth_off_unique_breakpoint`** (the physical core is `ContDiffOn ℝ ⊤` on `(0,σ_ij)` off the unique interior breakpoint `\|λ_ij\|`) + **`baxterConvCoreK_paramDeriv_contDiffOn_{inner,outer}`** (every `K`-derivative, all orders). All three `#print axioms` = `[propext, Classical.choice, Quot.sound, baxterConvCore_eq_matCoreUneq]`. Closes the BRK group's last open seam (BRK side was already std-3, waiting only on this MSAEMIX-owned input). ⭐⭐⭐ **`hHS` DISCHARGED at unequal σ 2026-08-24 (no axiom) — `matMSAmixture_unequalDiam` no longer needs the HS-factorization hypothesis.** KEY: `ftilde ρ Q = δ − √(ρᵢρⱼ)Q`, so `(F̃_HS(ik)·F̃_HS(−ik)ᵀ)_ij = δ_ij − √(ρᵢρⱼ)(Q̂_HS,ij(ik)+Q̂_HS,ji(−ik)−Σ_l ρ_l Q̂_HS,il(ik)Q̂_HS,jl(−ik))` is **pure `Matrix` algebra** (only `ρ≥0`; the cross term via `√(ρᵢρ_l)√(ρⱼρ_l)=√(ρᵢρⱼ)ρ_l`). `MSAMixtureBHRootUneq.lean` gains: `ftilde_mul_transpose_apply` (the general expansion, std-3) + `cHShatUneq` (the HS DCF in **Baxter-factor form**) + `FtHSuneq_mul_transpose` (hHS proved, std-3) + **`matMSAmixture_unequalDiam_of_hcore`** (MSAEMIX.1 at unequal σ with hHS supplied internally). `#print axioms matMSAmixture_unequalDiam_of_hcore = [propext, Classical.choice, matExactMSAUnequalDiam_hcore, Quot.sound]` — **the unequal-σ MSA factorization needs ONLY the hcore axiom**, no HS hypothesis, no WH atoms. This EXCEEDS the equal-σ grade: `matMSAmixture_equalDiam_WH` still carries `hKDEF`/`hbridge`/`hWH` (to put the HS part in `radial_fourier(Φ_HS)` form), whereas at unequal σ the HS factorization is free algebra (the HS DCF stays in the natural Baxter-`Q̂`-combo form `cHShatUneq`). ⭐⭐⭐ **PHYSICAL `radial_fourier(Φ_HS)` FORM CLOSED 2026-08-25** — the unequal-σ HS Wiener–Hopf identity `matHSexactUnequalDiam_kspace` (one sympy-backed axiom, the coupling-`0` sibling of `matExactMSAUnequalDiam_hcore`): `cHShatUneq = √(ρᵢρⱼ)·radial_fourier(matCoreHSuneq)`, i.e. the HS Baxter-`Q̂`-combo IS the transform of the physical real-space HS DCF `matCoreHSuneq` (= `matCoreUneq` at HS amps, σ-oriented, cut at σ_ij). `matMSAmixture_unequalDiam_physical` then puts the whole unequal-σ MSA mixture DCF in the equal-σ shape `δ − √(ρᵢρⱼ)(radial_fourier(Φ_HS) + radial_fourier(matCoreCorrUneq) + radial_fourier(matMSAtail))`; `#print axioms = [propext, Classical.choice, matHSexactUnequalDiam_kspace, matExactMSAUnequalDiam_hcore, Quot.sound]` (std-3 + the two Baxter-Fourier axioms). Grade-2 (the direct proof is the exactMSA-class ring, measured infeasible; the equal-σ `matSF_of_baxterFourierWH` is scalar-σ, `∫₀^σ`+`matSelfConv`, does NOT transfer to per-pair unequal supports). ⇒ unequal-σ MSAEMIX.1 now matches the equal-σ closure form. |
| MSAEMIX.5 ⭐ | the unequal-σ core **breakpoint structure** — `σ_l`-independent, NO mediated (3-body) breakpoints, all `N` | **✓ DONE 2026-08-22** (`msaemix_uneq_core.py`/`msaemix_uneq_pieces.py`/`msaemix_uneq_n3.py`, parent repo, commits 18ef2da+e973781). The exact-MSA core `c_ij(r)` on `(0,σ_ij)` is **piecewise with interior breakpoint(s) drawn ONLY from `{\|λ_ij\|}`** (`λ_ij=(σ_i−σ_j)/2`), `σ_ij` the endpoint — **at every `N`**: diagonal (σ_i=σ_j) single-piece, off-diagonal 2-piece split at `\|λ_ij\|`, both pieces the 6-term g-basis `{1,r,r²,r⁴,e^{−zr},e^{+zr}}` (inner coeffs partly 0; `g:=2πr c`, g(0)=0 ⇒ c finite, no r³). ⭐⭐ **No mediated 3-body breakpoints**: the 4 t-kink crossings that set the r-breakpoints (`λ_li−λ_lj`, `σ_il−σ_jl`, `σ_il−λ_lj`, `λ_li−σ_jl`) are ALL `σ_l`-**independent** (σ_l enters `λ_li=(σ_l−σ_i)/2`, `λ_lj=(σ_l−σ_j)/2` symmetrically ⇒ cancels), so the intermediate species adds nothing — UNLIKE FMSA 1st order (`_compute_mediated`'s `r*=R[a,b]+R[i,a]`, which ARE σ-dependent). Verified N=2 and N=3 (σ=[1.0,1.4,1.9], all 6 off-diag cores 2-piece to 1e-13..1e-15) with breakpoint-aware quad (pass integrand kinks `t=λ_lj,σ_jl,λ_li−r,σ_il−r`; the earlier "piecewise hard" was quad error). ⇒ feeds MSAEMIX.4's unequal-σ Stage 3 (the piece structure is now fixed; only per-piece coefficients remain). ⭐⭐ **LEAN-FORMALIZED 2026-08-22** (`YukawaOZMix/MSAMixtureBreakpoints.lean`, in default target, NO custom axioms — footprint `[propext, Classical.choice, Quot.sound]`): `edgeLo/edgeHi` (the `Q_ab` support/poly edges) + `bp_loLo/hiHi/hiLo/loHi` (the four t-kink crossings, each = an `i,j`-only value with `σ_l` cancelled by `ring`) + `bp_*_indep` (the crossing is identical for any two intermediate species) + `breakpoints_sigma_l_free` (crossing set = `{±(σ_i−σ_j)/2, ±(σ_i+σ_j)/2}`, `σ_l`-free) + `interior_breakpoint_eq_absLam` (the UNIQUE crossing in the open core interval `(0,σ_ij)` is `\|λ_ij\|`, `σ_ij` the endpoint). So the "no mediated breakpoints" claim is a genuine Lean theorem; the analytic link (`edgeLo/Hi` = real `Q` supports; convolution kinks = these crossings) stays numeric/Stage-3. |

### Landed — MSAEMIX.0 (`LeanCode/YukawaOZMix/MSAMixturePositivity.lean`, 2026-08-19)

Build 8558 jobs, `#print axioms` = the standard three on all nine theorems, raw `grep -rn "^axiom "`
unchanged. Pure `Matrix` algebra — `Matrix.det_mul`, `Matrix.det_transpose`, `Finset.sum_nonneg` —
so the group's "no new axiom" constraint holds trivially, as intended.

**What it adds over the scalar wall.** `MSAClosedForm.lean` proves `a = B²` at `N = 1`. At `N ≥ 2`
there are **two different squares**, and conflating them is a real trap:

* `mixCompressibility_nonneg` — Eq. (39) is a **sum of squares**, so `∂βp/∂ρ ≥ 0` with *no
  cancellation between species possible*; `no_real_mix_baxter_of_neg_compressibility` is the range
  statement.
* `mixStability_eq_det_sq` / `mixStability_nonneg` — the **stability determinant** is
  `det(F Fᵀ) = (det F)²`, a *different* square. ⇒ **no real Baxter factorization represents a
  thermodynamically unstable mixture**, at every `N`. `mixStability_eq_zero_iff`: the spinodal is
  exactly `det F = 0` — **one** condition.
* ⭐⭐ `mixCompressibility_pos_of_det_zero_example` / `..._pos_at_spinodal_example` — **Eq. (39) does
  not detect that spinodal.** An explicit binary `F` sitting *on* the spinodal (`det F = 0`) with
  every column sum (`= A_j/2π`, their Eq. 13) strictly positive, hence `∂βp/∂ρ > 0` there. This is
  the formal counterpart of the MSAX.6 measurement (`∂βp/∂ρ` runs **0.4 … 24.5** at the mixture
  spinodal) and the formal reason the scalar rule "spinodal ⟺ `A = 0`" must **not** be lifted to
  "`A_j = 0` ∀ `j`" — that is `N` conditions for one parameter, and the true condition is compatible
  with every `A_j` bounded away from zero.
* MSAEMIX.2 discipline applied in place: `mixCompressibility_fin_one`, `mixStability_fin_one` reduce
  to the scalar objects, and a non-degenerate binary `example` (not the dilute `F = I` point) guards
  non-vacuity.

### Landed — MSAEMIX.1 down-payment (`LeanCode/YukawaOZMix/MSAMixtureCancellation.lean`, 2026-08-19)

Build 8785 jobs, `#print axioms` = the standard three on all four theorems, own `^axiom ` count 0.

⚠ **A different kind of down-payment from MSAEXACT.1's.** The scalar one is *transform
infrastructure* (ansatz, `D = 0` reduction, two Laplace integrals). This one is a **theorem the
scalar case cannot state**: the mixture `e^{zσ}` cancellation.

Blum & Høye's `M_j`, `N_j` (their (20)/(21)) are built from `D_lj + C_lj`, whose terms are each
`O(e^{+zσ_l})` while the sum is `O(K)`. At `N = 1` that cancellation is on the face of it —
`D + C = (1−γ)D` with `1−γ = 2πρĝ(z)/z`. At `N ≥ 2` it is **not term-by-term**: it runs through the
*off-diagonal* of `γ`, and forming `M`, `N` from the unscaled `D`, `C` loses `zσ_max/ln 10` digits.

* `entry_cancel` — the load-bearing step, and the reason it is one theorem rather than two:
  `δ_lk − γ_lk e^{z(σ_k−σ_l)/2} = (2π/z)ρ_k Gt_lk e^{−zσ_l}` holds for `k = l` (the two Kronecker
  deltas cancel, the exponential is `1`, `σ_ll = σ_l`) **and** for `k ≠ l` (`sigMix_exponent`:
  `−σ_lk + (σ_k−σ_l)/2 = −σ_l` exactly). Same right-hand side both ways.
* ⭐ `cancellation_star` — **(★)** `Dt_lj − Ct_lj = e^{−zσ_l}·W̃_lj` with
  `W̃_ij = (2π/z)Σ_k ρ_k Gt_ik Dt_kj`, manifestly `O(K)` and exponential-free.
* `cancellation_star_fin_one` — MSAEMIX.2's discipline applied here: at one component (★) *is* the
  scalar `(1−γ)D`.

⚠ **Scope.** The analytic core of MSAEMIX.1 — that the matrix ansatz **recovers** the MSA closure
`c_ij = −βu_ij` on the exterior, i.e. the `k`-space identity at general `N` — re-runs the `BAXTER`
machinery with Yukawa tails in both `Q` and `c`. **Staged 2026-08-20** (`MSAMixtureFactorization.lean`,
axiom-clean): `matBaxterProd_split` + `matMixtureFactorization_of_core` reduce it to a single matrix
`hcore` ring (the coupling-`0` part discharged via `matSF_of_baxterFourierWH`), **the matrix analog
of MSAEXACT.6**. The matrix `hcore` for the specific MSA factor (increment from `M_j,N_j`+tails) is
the analytic core, not attempted — at least as hard as scalar MSAEXACT.6.

### Landed — MSAEMIX.3 (`LeanCode/YukawaOZMix/MSAMixtureSelection.lean`, 2026-08-19)

Build 8784 jobs, `#print axioms` = the standard three on all eight theorems, own `^axiom ` count 0.
`ring`, `field_simp`, `Finset` cardinality — nothing else.

**Eq. (41) is not an extra physical input.** `bh41_iff_contact_symm` shows the criterion is exactly
`g_ij = g_ji` (the `2πσ_ij` of (38) is common to both sides, given `σ` symmetric and nonzero), and
`bh41_expand` shows that substituting (24) turns that difference into Blum & Høye's *printed* (41),
needing only that `q^{0′}` is symmetric. So (41) is `g_ij = g_ji` rewritten, and the numerical
finding that it is a **free root test** — not imposed, the system is square without it, and it
returns `0 … 1e-15` on the branch through `K = 0` (MSAX.6 gate §4) — is consistent with it being a
consequence rather than a constraint.

**The vacuity, stated both ways.** `bh41_vacuous_at_fin_one`: at `N = 1` *every* candidate passes —
the formal record of why single-component selection had to be supplied separately by MSAEXACT.3
(`physical_baxter_factor_unique`, `A/2π > 0`). `bh41_conditions_card_{one,two,three}` counts the
same fact: `0`, `1`, `3` conditions. And `bh41_not_vacuous` closes the group's own non-vacuity
discipline from the other side — an explicit `N = 2` candidate the criterion **rejects**, so
"acceptable root" theorems are not vacuously true.

⭐ **`A0_row_index_forced` — the trap MSAX.6 had to clear.** (24) is printed as
`q′_ij = q^{0′}_ij(1 + M_j) + A_i⁰ N_j`, and `A_i⁰` is the one object carrying the **row** index,
alone among `M_j, N_j, A_j, B_j`. It is forced, not a typo: (13)/(14) give `q′_ij = B_j + σ_ij A_j`,
and expanding with (23) makes the `N_j` coefficient `A_j⁰ + 4B_j⁰λ_ji/σ_j²`, which collapses
identically to `A_i⁰`. Proved here as a `field_simp; ring` identity on (25)'s closed forms.
⚠ At equal diameters `λ_ji = 0` and the two readings coincide — which is exactly why the misreading
survives every equal-`σ` check, and why it only surfaced against Tang & Lu's `σ₂/σ₁ = 1.5` table.

⚠ **Ceiling.** Eq. (41) is formalised as a *criterion* — what it says, that it is `g_ij = g_ji`, that
it is vacuous at `N = 1` and proper beyond. That the physical branch **satisfies** it is measured
(MSAX.6, `SolutionMix.symmetry_defect`), not proved; proving it needs MSAEMIX.1, the factorization.

⚠ **Ceiling.** This is the fixed-`(η, T)` algebra only, exactly as the scalar Tier 1 is. That the
*physical* branch has `det F > 0`, and where in `(η, T, x)` it vanishes, are measured
(`msa_exact_mix.spinodal_densities` / `trace_coupling_mix`), for the same reason MSAEXACT.3's
`hcoupling_pins` is.

**MSAEMIX.2 is not decoration.** It is the check that the matrix statement is the right
generalisation and not a differently-normalised object — the role `AppendixBridgeN1` plays for the
residue programme, and the non-vacuity gate for the whole group. Write it before MSAEMIX.1 is
believed.

**MSAEMIX.3** is left open on purpose. Root uniqueness at general `N` is a matrix problem; the
scalar theorem (MSAEXACT.3) is what the FWL boundary needs and must exist before the matrix version
is worth attempting.

---

## Boundaries — recorded, not overlooked

* **Real-space `g(r)`** re-enters the MZERO/POLE analysis machinery (Mittag-Leffler series, contour
  arguments, the MML.5 wall) and gains nothing here. The whole point of these groups is to stay in
  the algebra. Contact values *are* algebraic in the Baxter framework
  (`project_fmsa_dp_rdf_routes`), so the Tang & Lu gate does not force this boundary.
* **The physical-root condition is a hypothesis until MSAEXACT.3.** Until then, statements should
  carry it explicitly rather than assume a canonical root — the same discipline as
  `MixRDFInnerCollapse` and `TailFitWHConvergent`.
* ⚠ **Non-vacuity.** Every theorem here quantifies over "coefficients satisfying the algebraic
  system". If that system were unsatisfiable the whole group would be vacuously true and the build,
  `#print axioms`, and review would all stay silent — the `b4_origin_bc_abstract` / GAP.8 /
  PYE.3 failure mode. **Each group needs a non-degenerate `example` witness** (not the trivial
  dilute `Q̂₀ = I` point) before any of its results are quoted.
