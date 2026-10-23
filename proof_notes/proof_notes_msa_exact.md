# Proof Notes: The Exact MSA Closed Form (Groups MSAEXACT / MSAEMIX)

**Current status — 2026-10-09 legacy migration complete.** The four former
matrix SymPy-supported axioms are now proved Lean theorems with their
original DCF definitions and closed right-hand sides. All migrated public
interfaces and callers build. The default target guards 77 migration
footprints in addition to the existing 1074 multitail footprints. The
four-target build passes with 9008 jobs; the independent joint audit has
526 footprints (524 standard-three, two generic HS standard-two). The
selected-source scan covers 182 current hashes and has no axioms, sorry,
native_decide or ofReduceBool. See the final retirement record below and
`results/multitail_extension/mixture_legacy_retirement_validation.json`.
Earlier dated descriptions of accepted matrix axioms and open structural
bridges are historical; they are superseded by the automatic completion
and retirement records. The explicit physical and analytic domains remain
part of every conclusion; no g positivity, thermodynamic consistency,
global root existence or physical coexistence guarantee is claimed.


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

> **2026-10-08 completion update — scalar closure recovery proved.**
> The single-component, single-Yukawa chain now includes the actual rational
> dictionary, denominator clearing, K-elimination, Pythagorean
> reduction, sparse division and Fourier bridges. `exactMSA_hcore` and
> `exactMSA_kspace_residual` are theorems with only the standard three axioms.
> `exactMSA_factorization` and its OZ-derived version have that same footprint.
> The default build imports this proof; `lake build LeanCode
> ExactMSACertificate ExactMSASparseFeasibility` passes (8834 jobs).
> The explicit Fourier domain is `z > 0`, `xi != 1`, `k != 0`, including
> `K = 0`; the factorization uses `xi < 1`. The source inventory now has
> 12 project axioms (7 mathematical + 4 mixture symbolic + 1 physical).
> Historical direct-`ring` timings below do not establish decomposition
> impossibility or a controlled speedup comparison. See
> `results/exact_msa_feasibility/findings.txt` for the proof chain, measurements,
> reproducible data generation and final build logs.

> **Current certification boundary.** Content name in code = `ExactMSA`.
> **.1 and .6** are now standard-three scalar theorems on their stated regular
> domain. **.2–.5** retain the qualifications below. The matrix closure axioms
> are not discharged by this scalar proof. Neither branch existence at every
> thermodynamic state nor universal finite-order physical validity, coexistence
> or strict finite-k stability follows from closure recovery.

Opens with MSAX.1. **MSAEXACT.1 cannot start before MSAX.1's gate 0** (reproduce the elimination
degree in this project's conventions) — the Lean statement has to quantify over the *right*
algebraic system, and the theory note flags the degree as unsettled.

| Task | Title | Status |
|------|-------|--------|
| MSAEXACT.1 | `exactMSA_factorization` — the non-compact Baxter factorization | ✅ **PROVED std-3, 2026-10-08.** `MSAFullFactorization` combines the staged hard-sphere factor with the now-proved scalar closure identity. `MSAFactorizationFromOZ` supplies both root conditions from the OZ/Baxter primitives. Explicit regular physical domain; compact ansatz remains superseded. |
| MSAEXACT.6 ⭐ | discharge `hcore` under Blum–Høye (29′)/(33) | ✅ **FULL SCALAR BRIDGE PROVED, 2026-10-08.** Actual rational dictionaries, elimination, trigonometric reduction, sparse division/reassembly and Fourier transforms all kernel-checked; `exactMSA_hcore` and compatibility `exactMSA_kspace_residual` retired as axioms. Standard three only, including `K = 0`. Mixture matrix closure remains separate. See `results/exact_msa_feasibility/findings.txt`. |
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

### Landed — MSAEXACT.6 complete scalar proof (2026-10-08)

`ExactMSAResidualRecovery.deltaActual_zero` connects the original residual to
all the checked polynomial identities. `MSAFullFactorization.exactMSA_hcore`
then reuses the interval and exterior Fourier formulas, and
`exactMSA_factorization_of_oz` closes the full scalar factorization from the
already-derived root constraints. Their axiom guards contain only
`propext`, `Classical.choice`, `Quot.sound`. The sparse circuit tactic uses
native proposals for normal forms and kernel-checked integer equalities for
every step; no `native_decide` or polynomial assumption is introduced.

The new large bridge modules passed the integration build in 646 s
(elimination), 737 s (trigonometric reduction), and 807 s (original Delta
dictionary). The residual recovery and Fourier/factorization modules took
3.6 s and 3.8 s. The final combined build passes 8834 jobs; the first
integration run's final gate needed only a whitespace correction in its
expected axiom output. An independent uncached data reconstruction reproduced
the emitted rational-data file byte-for-byte, with recorded source/data SHA256.

The physical Fourier domain is explicit: `z > 0`, `xi != 1`, `k != 0`;
`K = 0` is covered separately. The old unrestricted axiom signature is not
asserted as a theorem at divergent/singular parameters. The factorization
uses `xi < 1`, and the existing OZ consumer already assumes `z > 0`.
`exactMSA_structureDen_nonneg` also proves nonnegativity at every real nonzero
wavevector at such a root. Zeros and the `k = 0` limit remain separate issues.

### Historical direct tactic attempts (2026-08-20/22; superseded)

The earlier experiments tried large explicit multipliers in
`Delta = m29*r29 + m33*r33`. Several smaller-multiplier substitutions failed,
and direct expanded `field_simp; linear_combination; ring` was selected at
that time. The recorded benchmarks included a 323-monomial coefficient taking
3 h 12 m / 23 GB, and failed or unfinished normalizations of larger pieces.
These observations describe that representation; they do not establish
irreducibility, a lower bound, or that every decomposition must repeat a full
normalization. The extrapolation to weeks / approximately 200 GB is superseded
as a conclusion about the whole proof.

The old `msaexact6_scaletest.py` emitter expanded both sides identically, so
it is not a controlled benchmark of the new factored division identities.
Its algebraic prefix remains useful for reconstructing proposed source data.
The noncomputable `MvPolynomial` route could not use `native_decide`; the new
computable semantic checker avoids trusting native reduction as a proof and
adds no `Lean.ofReduceBool` axiom.

At that stage `ExactMSACertificate` proved only the Fourier/definitional
layer from the pure k-space residual axiom. Today its residual and Fourier
statements are both proved compatibility theorems, and the main scalar proof
is imported by the default target. The optional certificate target remains
available. The matrix certificate has not been retired by this work.

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

> **Historical checkpoint (2026-08-25; matrix-axiom status superseded 2026-10-09).** The matrix (mixture) exact-MSA; content name in code =
> `MSAMixture`. **.0/.3** positivity + root selection axiom-clean; **.1** matrix factorization CLOSED at
> equal σ (`matMSAmixture_equalDiam`), unequal σ (`matMSAmixture_unequalDiam_of_hcore`, `hHS` discharged
> by pure `ftilde` algebra), and in the physical `radial_fourier(Φ_HS)` form
> (`matMSAmixture_unequalDiam_physical`); **.2** the N=1-is-scalar capstone
> (`msaMixture_reduces_to_scalar_at_fin_one`); **.4/.5** the core + breakpoint structure; **.7** the first-order-equivalence analog of MSAEXACT.5 (`firstOrder_amplitude_eq_hardSphere_dressed_matrix`, axiom-clean). **.6** the matrix BH-root smoothness — **NOW CLOSED too, both diameters, unconditionally (2026-09-01)**;
> see the note below. **No open math
> item remains** — only the accepted grade-2 Baxter-Fourier axioms (`matExactMSAEqualDiam_hcore`,
> `matExactMSAUnequalDiam_hcore`, `matHSexactUnequalDiam_kspace`, `baxterConvCore_eq_matCoreUneq`); their
> grade-1 proof is the exactMSA-class ring, measured infeasible.
>
> **REOPENED 2026-08-25, RE-CLOSED 2026-09-01 — MSAEMIX.6.** "Fully closed" was true of the
> *factorization* chain throughout. MSAEMIX.6 is a different statement — the **differentiability of the
> solution family at zero coupling, at general `N`** (paper Theorem I.1's antecedent for mixtures), which
> lived on the FOEQ/MSAFAM side at `N = 1`. It is now CLOSED at **both** diameters and **unconditionally**:
> `exists_contDiffAt_matBhRoot_of_physical` (equal σ) and `exists_contDiffAt_matBhRootUneq_of_physical`
> (unequal σ), std-3, both HS-block dets reduced to `Q0_mat_phys` and discharged by M.4
> `Q0_mat_phys_isUnit_det` — no det hypothesis, no physics axiom. The only remaining grade is
> transcription faithfulness of the Blum–Høye system, exactly as at `N = 1` (not a MSAEMIX-specific gap).

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
| MSAEMIX.6 ⭐⭐ (**NEW 2026-08-25**) | the **matrix Blum–Høye root is `C^∞` at `K = 0`** — the general-`N` analogue of `exists_contDiffAt_bhRoot`, i.e. the hypothesis of paper Theorem I.1 for mixtures | ✅ **ALL 5 ITEMS DONE (2026-08-25, pushed, all std-3):** item 1 `exists_contDiffAt_root_of_prodDomain_ift` (`81f8c32`); item 2 `matBhResidual`+`_eq_zero_iff` (`643136d`); item 3 `contDiff_matBhResidual` (`8252071`); item 4 `matBhResidual_base_eq`+`exists_contDiffAt_matBhRoot` (`5a36c38`); item-5 **engine** `matBhJacobianCLM_isInvertible`+`…_of_blockJacobian` (`2194180`); item-5 **transcription** `matBhResidualShape_hasFDerivAt` (`0cf4c01`) + concrete `resG/resH/resD` → ⭐ **`exists_contDiffAt_matBhRoot_physical`** (`007fb7b`): `C^∞` family from `MixBHRoot` seed + the two HS-OZ blocks `resG/resH (0,Gt₀)` nonsingular. ⭐ **The dets are then DISCHARGED** (`70c35e6`): `resH (0,Gt₀) = 1−D_ρ·C`, `resG = 1−D_ρ·Cᵀ`, `Q0_mat_phys = 1−D_√ρ·C·D_√ρ` share the equal-σ Baxter core `C = p₁Q0phys+p₂Qppphys`, so by Sylvester `det(1−AB)=det(1−BA)` (+transpose) **`det resG = det resH = det Q0_mat_phys`** — giving `exists_contDiffAt_matBhRoot_of_Q0` (from `IsUnit Q0_mat_phys.det`) and `exists_contDiffAt_matBhRoot_of_diag_dom` (from `Q0_mat_phys_isUnit_det_of_diag_dom`), and ⭐⭐ **`exists_contDiffAt_matBhRoot_of_physical` (`fc6f2f9`) — FULLY UNCONDITIONAL, no det hypothesis**: discharges via the concurrent's now-unconditional M.4 `Q0_mat_phys_isUnit_det` (general `N`, std-3, rank-2 Weinstein–Aronszajn `Q0_moment_det_pos`), needing only physical params (`z>0`, `vacMix>0`, `ρ≥0`, `σ>0`) + `hσ` + HS seed — the exact matrix analogue of `N = 1`'s `η∈(0,1)`, `z>0`. **No Baxter-block det left.** ⭐⭐⭐ **UNEQUAL σ CLOSED TOO — UNCONDITIONALLY (2026-09-01, `7d9de76`, std-3, `MSAMixtureBHRootUneqSmooth.lean`):** `exists_contDiffAt_matBhRootUneq_of_physical` — the unequal-σ family is `C^∞` near `K=0` with NO det hypothesis. The "asymmetric row-diameter block breaks the rank-2 argument" worry was **WRONG**: recentering `qhatMixRuneq_recentered_eq_qhatMixR` (`e^{z·edgeLo}·qhatMixRuneq = qhatMixR` at the ROW diameter) gives `resHuneq(0,Gt₀)=1−D_ρ·hsCoreUneq`, `resGuneq=1−D_ρ·hsCoreUneqᵀ` (`hsCoreUneq_lj=p₁(σ_l)Q0phys_lj+p₂(σ_l)Qppphys_lj`); the physical `Q0_mat_phys z σ ρ = 1−D_{√ρ·e^{zσ/2}}·hsCoreUneq·D_{√ρ·e^{−zσ/2}}` — the Baxter shift `e^{−(σ_j−σ_l)z/2}=e^{zσ_l/2}·e^{−zσ_j/2}` is a **pure diagonal conjugation**, so Sylvester `det(1−AB)=det(1−BA)` recombines the two diagonals to `D_ρ` (exp's cancel — exactly the role `hσ` played at equal σ, now AUTOMATIC). ⇒ `detHuneq_eq_Q0`/`detGuneq_eq_Q0`: `det resGuneq = det resHuneq = det Q0_mat_phys` **unconditionally**, closed by the SAME M.4 `Q0_mat_phys_isUnit_det` (which was ALREADY general-σ — `Q0_mat_phys` is `q0_entry z (σ_i) ((σ_j−σ_i)/2)…`, the general unequal-σ matrix). **NO physics axiom** (not even `no_spinodal`). Gated in `ExactMSAProject.lean` §MSAEMIX.6 (`30752f1`). Same "two of three parts" grade as `N = 1` (transcription faithfulness of the BH system stays open), now at **BOTH** diameters |
| MSAEMIX.5 ⭐ | the unequal-σ core **breakpoint structure** — `σ_l`-independent, NO mediated (3-body) breakpoints, all `N` | **✓ DONE 2026-08-22** (`msaemix_uneq_core.py`/`msaemix_uneq_pieces.py`/`msaemix_uneq_n3.py`, parent repo, commits 18ef2da+e973781). The exact-MSA core `c_ij(r)` on `(0,σ_ij)` is **piecewise with interior breakpoint(s) drawn ONLY from `{\|λ_ij\|}`** (`λ_ij=(σ_i−σ_j)/2`), `σ_ij` the endpoint — **at every `N`**: diagonal (σ_i=σ_j) single-piece, off-diagonal 2-piece split at `\|λ_ij\|`, both pieces the 6-term g-basis `{1,r,r²,r⁴,e^{−zr},e^{+zr}}` (inner coeffs partly 0; `g:=2πr c`, g(0)=0 ⇒ c finite, no r³). ⭐⭐ **No mediated 3-body breakpoints**: the 4 t-kink crossings that set the r-breakpoints (`λ_li−λ_lj`, `σ_il−σ_jl`, `σ_il−λ_lj`, `λ_li−σ_jl`) are ALL `σ_l`-**independent** (σ_l enters `λ_li=(σ_l−σ_i)/2`, `λ_lj=(σ_l−σ_j)/2` symmetrically ⇒ cancels), so the intermediate species adds nothing — UNLIKE FMSA 1st order (`_compute_mediated`'s `r*=R[a,b]+R[i,a]`, which ARE σ-dependent). Verified N=2 and N=3 (σ=[1.0,1.4,1.9], all 6 off-diag cores 2-piece to 1e-13..1e-15) with breakpoint-aware quad (pass integrand kinks `t=λ_lj,σ_jl,λ_li−r,σ_il−r`; the earlier "piecewise hard" was quad error). ⇒ feeds MSAEMIX.4's unequal-σ Stage 3 (the piece structure is now fixed; only per-piece coefficients remain). ⭐⭐ **LEAN-FORMALIZED 2026-08-22** (`YukawaOZMix/MSAMixtureBreakpoints.lean`, in default target, NO custom axioms — footprint `[propext, Classical.choice, Quot.sound]`): `edgeLo/edgeHi` (the `Q_ab` support/poly edges) + `bp_loLo/hiHi/hiLo/loHi` (the four t-kink crossings, each = an `i,j`-only value with `σ_l` cancelled by `ring`) + `bp_*_indep` (the crossing is identical for any two intermediate species) + `breakpoints_sigma_l_free` (crossing set = `{±(σ_i−σ_j)/2, ±(σ_i+σ_j)/2}`, `σ_l`-free) + `interior_breakpoint_eq_absLam` (the UNIQUE crossing in the open core interval `(0,σ_ij)` is `\|λ_ij\|`, `σ_ij` the endpoint). So the "no mediated breakpoints" claim is a genuine Lean theorem; the analytic link (`edgeLo/Hi` = real `Q` supports; convolution kinks = these crossings) stays numeric/Stage-3. |
| MSAEMIX.7 ⭐ | mixture analog of MSAEXACT.5 — first-order MSA = HS-dressed for the *matrix* Baxter factors | **✓ DONE 2026-08-25** (`Closures/FirstOrderEquivalence.lean`, axiom-clean, footprint = std-3): `firstOrder_amplitude_eq_hardSphere_dressed_matrix` over any normed algebra `𝔸` (⇒ `Matrix (Fin N) (Fin N) ℝ` with an operator norm). From the self-consistency `D(K)·F(K)=G(K)` with `G 0=0` (physically `G K=K•C`, the linear Blum–Høye source ⇒ `G'=C`) and `F 0` a **unit**, the first-order slope is `D'·F 0 = G'` — it sees the HS factor `F 0` alone; `F'` (the tail's back-reaction on the Baxter factor) is **killed** by `D 0=0` (forced by `D 0·F 0=G 0=0` + `F 0` a unit). So freezing the propagator at hard sphere is forced at first order in the mixture, exactly as scalar MSAEXACT.5 (`𝔸=ℝ`, `G K=c·K`, `D'=c/F 0`). Proof = `HasDerivAt.mul` product rule + `HasDerivAt.unique` + `D 0=0` via `IsUnit.mul_left_eq_zero`. |

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

### ✅ MSAEMIX.6 — the matrix BH root is `C^∞` at `K = 0` (general `N`) — CLOSED, both diameters, unconditional

**Statement wanted.** The general-`N` analogue of `FMSA.MSASolutionFamily.exists_contDiffAt_bhRoot`:

```
∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
    ψ 0 = (0, Gt₀) ∧
    (∀ᶠ K in 𝓝 0, MixBHRootResidual z ρ σ K (ψ K) = 0) ∧
    ContDiffAt ℝ ∞ ψ 0
```

**Why it is worth doing.** It is the *only* thing between paper Theorem I.1 and an
unconditional general-`N` statement. The implication is already general `N` on both sides:

* `FMSA.FirstOrderEquivalence.oz_msa_taylor_eq_hierarchy` (FOEQ.8) is stated over an abstract
  `NormedRing 𝔸` ⇒ holds for `Matrix (Fin N) (Fin N) ℂ` at any `N`, every order;
* `FMSA.FirstOrderEquivalence.firstOrder_dcf_unique_on_core_of_oz` (FOEQ.4) is already stated at
  `Matrix (Fin N) (Fin N) ℂ` — the first-order line has a *unique* core solution.

So "if the family is `C^∞` at `τ = 0` then its first-order coefficient **is** the FMSA DCF" is
machine-checked at every `N`. Only the antecedent is missing, and only for `N > 1`.

**⭐ The Jacobian shape.** At `N = 1` the Jacobian step is `bhJacobianCLM_isInvertible`, whose
docstring records the shape that matters: the Jacobian is **block-triangular**, and nonsingular ⟺
`F₀ ≠ 0` with `F₀` the hard-sphere Baxter factor. The matrix analogue of the two diagonal blocks are
the physical hard-sphere OZ matrices `N₁_lj = δ_lj − ρ_l Q̂₀_jl`, `N₂_lj = δ_lj − ρ_l Q̂₀_lj` (real
Baxter factor at `s = z`). ✅ **`Q0_mat_phys` invertibility IS unconditional (M.4, `Q0DetRankTwo.lean`,
std-3).** The theorem is `FMSA.MatrixQ0.Q0_mat_phys_isUnit_det` (`det ≥ 1` via the rank-2
Weinstein–Aronszajn positivity `Q0_moment_det_pos`), for every physical mixture, at every `N`, **general
σ**. ⚠ Do not confuse it with the *free-`Qp`* `Q0_mat_isUnit_det` that WAS retired as false (adversarial
`Qp` untied from σ/ρ forces `det = 0`) — the **physical** matrix, with `Qp = Q0phys(ρ,σ)` tied to the
mixture, is the theorem. So the matrix `F₀ ≠ 0` analogue (`IsUnit N₁.det`, `IsUnit N₂.det`) IS discharged
unconditionally, the exact analogue of `N = 1`'s `F₀ ≠ 0` via `Q0_ne_zero_at_yukawa`.

**Work items** — ALL DONE (items 1–4, the item-5 engine, AND the item-5 fderiv transcription):

| # | item | size |
|---|---|---|
| 1 | ✓ **DONE** (`81f8c32`). Generalise `exists_contDiffAt_root_of_prodDomain_ift` from the concrete `g : ℝ × (ℝ × ℝ) → (ℝ × ℝ)` to `g : ℝ × E → E`, `E` a complete normed space. Mathlib's `ContDiffAt.implicitFunction` is *already* stated there, so this is a signature change and the same four lines | **small** |
| 2 | ✓ **DONE** (`643136d`, `matBhResidual`). The matrix residual map `g(K, (Dt, Gt))` whose zero set is `MixBHRoot` / `MixBHRootUneq`. The equations exist as a `Prop`; this is the same content as a function into `Matrix × Matrix` | **small** |
| 3 | ✓ **DONE** (`8252071`, `contDiff_matBhResidual`, std-3). `ContDiff ℝ ⊤ (matBhResidual …)` — amplitudes are polynomial in `(Dt, Gt)` entries; recipe = Frobenius local instance + `contDiff_matrix_entry`/`contDiff_matrix_of` + `@[fun_prop]` entry projections + `simp`-unfold + `fun_prop` | **medium (done)** |
| 4 | ✓ **DONE** (`5a36c38`, `matBhResidual_base_eq`) + capstone `exists_contDiffAt_matBhRoot` (takes item-5 `hjac` as hypothesis). At `Dt = 0` all amplitudes vanish (`∝ Dt`), so the base point is a residual root iff `Gt₀` is a zero-coupling BH root | **medium (done)** |
| 5 | ✅ **DONE.** **Engine** (`2194180`, std-3): `matMulRightCLM`, `matBhJacobianCLM N₁ N₂ Cpl`, `matBhJacobianCLM_isInvertible` (units `N₁,N₂` ⇒ invertible, `Cpl` drops out) = general-`N` analogue of `bhJacobianCLM_isInvertible`; `exists_contDiffAt_matBhRoot_of_blockJacobian` discharges `hjac` from (i) the fderiv **shape** + (ii) the two dets. **Transcription (i)** (`0cf4c01`+`007fb7b`, std-3): `matBhResidualShape_hasFDerivAt` computes the block-triangular fderiv from the BH shape (R1's `Dt·dG` vanishes at `Dt=0`; R2 split off the linear `p.2·N₂` so the correction's `<•` op-smul dies, then factored through `fst` via `id = inl·fst + inr·snd` + `H'/D' ∘L inr = 0`); the concrete `resG/resH/resD` (`matBhResidual_zero_eq` shape identity, `contDiff_res*` via the item-3 recipe, `res{H,D}_fderiv_inr` = Gt-constancy on the `Dt=0` slice) discharge its hypotheses; chain rule + `HasFDerivAt.unique` give the shape, assembled in `exists_contDiffAt_matBhRoot_physical`. ⚠ instance-diamond avoided by moving the whole `section Smooth` to `open scoped Matrix.Norms.Frobenius` (consistent Ring+Algebra+Space) | **the real work — DONE** |

**⚠ What it did and did not buy.** Exactly as at `N = 1`, this proves the statement for the
*transcribed* Blum–Høye system. Faithfulness of the transcription (that `matBhResidual` / the
`resG/resH/resD` really are the physical BH system) is the third part that `proof_notes` and the
paper's not-formalized section both still list as open. So the honest claim is "two of three parts,
at general `N`" — the same grade `N = 1` has, not a stronger one.

**Paper effect.** §I C's sentence *"What the mixture still lacks is the assembly …"* is **retired**:
the assembly is `exists_contDiffAt_matBhRoot_physical` (`007fb7b`), general `N`, std-3, fderiv
transcription proved internally; and the two physical HS-block dets are **discharged unconditionally**
onto `Q0_mat_phys` nonsingular via M.4 `Q0_mat_phys_isUnit_det` (`exists_contDiffAt_matBhRoot_of_physical`,
`fc6f2f9`), the mixture analogue of `η∈(0,1)`. Theorem I.1 stops being conditional for mixtures modulo the
transcription-faithfulness part only.

**⭐⭐⭐ Unequal σ — closed too, unconditionally (2026-09-01, `7d9de76`, std-3).**
`exists_contDiffAt_matBhRootUneq_of_physical` (`MSAMixtureBHRootUneqSmooth.lean`) is the exact unequal-σ
analogue, with NO det hypothesis. The route reduces the two *asymmetric* row-diameter blocks to the
**same** `Q0_mat_phys` the equal-σ case uses: the recentering `qhatMixRuneq_recentered_eq_qhatMixR` puts
the per-row `σ_l` inside (`resHuneq(0,Gt₀)=1−D_ρ·hsCoreUneq`, `resGuneq=1−D_ρ·hsCoreUneqᵀ`), and
`Q0_mat_phys = 1−D_{√ρ·e^{zσ/2}}·hsCoreUneq·D_{√ρ·e^{−zσ/2}}` — the Baxter shift being a **pure diagonal
conjugation** that Sylvester recombines to `D_ρ` (`detHuneq_eq_Q0`/`detGuneq_eq_Q0`). So M.4's general-σ
`Q0_mat_phys_isUnit_det` closes it with **no** physics axiom (in particular no `no_spinodal`). The worry
that "the asymmetric block breaks the equal-σ rank-2 argument" was unfounded — the asymmetry is a
determinant-invisible diagonal conjugation. Both diameters are now at the same grade as `N = 1`
(transcription faithfulness only), and both are gated in `ExactMSAProject.lean` §MSAEMIX.6 (`30752f1`).

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

---

## MSAMULTI — arbitrary finite Yukawa tails (2026-10-08)

**Starting scope:** scalar, single-Yukawa closure recovery and factorization are
already kernel-certified on their stated regular domain, at a given real BH
root. This extension uses an arbitrary `Fintype` for tails, separately from
`Fin N` for mixture species. It does not cover an infinite sum of Yukawa tails.
All rates are positive; coincident rates, zero-strength tails, and arbitrary
attractive/repulsive signs are allowed. No upper rate bound is assumed.

| Part | Formal result | Status and boundary |
|---|---|---|
| Pure-fluid BH dictionary | `MSAMultiTailSystem`: all cross denominators `s+zν`, finite-sum dressing, `Fin 1` specialization to the existing scalar system | Proved algebra and smoothness; physical transcription is also checked numerically |
| Actual pure Baxter transform | `MSAMultiTailBaxter.laplaceQ_eq_Qhat`, `laplaceQ_eq_integral` | Proved from actual core and improper tail integrals for `s>0`, all `zν>0` |
| Pure exterior closure | `MultiTail.correlation_exterior_of_root` | Proved from the first BH equations; the independently defined real-space convolution recovers `Σν Kν exp[-zν(r−1)]/r` for `r>1` |
| Pure core convolution | `MSAMultiTailCore.correlation_core_eq_closed`, `correlation_contDiffOn_core` | Actual integral equals a finite elementary expression and is spatially smooth on `0<r<1`; this is not a thermodynamic stability statement |
| Pure local real roots | `MultiTail.exists_contDiffAt_root` | Proved: for `0<ξ<1`, all positive rates and any signed coupling direction, a real `C∞` BH family exists near `τ=0`; actual partial Jacobian and its inverse are proved, not assumed |
| Finite-tail integral engine | `FiniteYukawa.integral_branchProduct` | Exact polynomial/exponential product integrals, independent left/right finite tail sets, including `1/(zν+zμ)` cross terms |
| Spectral algebra | `MSAMultiTailSpectralAlgebra` polynomial/polynomial, polynomial/tail and polarized tail/tail identities | Kernel-checked rational identities generated by SymPy; now connected to actual convolution integrals and Fourier moments by the ConvolutionBlocks/Assembly, BlockFourier/Fourier and Factorization modules |
| Pure full Fourier factorization | `MSAMultiTailFactorization.factorization`, `structureDen_nonneg`, `MSAMultiTailQFourier.factorization_integrals` | Actual real-space c and Q integrals, with all finite tail pairs, all positive rates and nonzero k; nonnegativity is not strict stability |
| Pure g-side OZ bridge | `MSAMultiTailOZ.second_equations_of_gside` | Actual source moment equals the second BH RHS; concrete Q support/L1/transform proved; RDF support, RDF L1/moments and OZ equation retained as premises |
| Actual scalar RDF/OZ reconstruction | `MSAMultiTailRDFRealSpace.reconstructedH_core_and_oz`, `_of_small_budget` | Actual excess L1, or internally sufficient exponential weighted-kernel norm<1; hard core pointwise, actual radial OZ a.e., all analytic bridge conditions discharged; strict D(k)>0 for k!=0 |
| Mixture real-space foundation | `MSAMultiTailMixtureBaxter.convolution_integrable` | Proved for arbitrary finite species/tail counts and nonnegative unequal additive diameters |
| Mixture BH dictionary | `MSAMultiTailMixtureSystem`: `residual_eq_zero_iff`, `residual_contDiff`, `W_add_C_exp` | Proved; first BH uses the transposed transform, second the untransposed transform with opposite support-edge recentering; `A_i⁰` in the `N_j` term of `qp_ij` retains its row index |
| Actual mixture transform and exterior | `MSAMultiTailMixtureTransform.laplaceQ_eq_Qhat`, `correlation_exterior_of_root` | Proved actual integrals and exterior closure at a BH root, with all mixed-rate terms retained; does not imply full matrix Fourier/core closure |
| Actual mixture complex/Fourier Q | `MSAMultiTailMixtureFourier.complexQ_integral_eq_Qhat`, `fourierQ_eq_QhatComplex`, `fourierQ_conj` | Actual full-line integral, negative lambda allowed; complex identification s!=0, Re(s)>=0; Fourier dictionary k!=0, actual integral/conjugation also at k=0 |
| Actual mixture Q cross-correlation and Gram | `MSAMultiTailMixtureSpectral.fourierQ_product_eq_corr`, `fourierFactor_gram_eq`, `_posSemidef`, `_posDef_of_isUnit` | Joint L1 internally discharged; density/transposition proved; Q-side spectral expression remains to be identified with actual radial DCF; physical reciprocity is separate |
| Mixture actual local BH family | `MSAMultiTailMixtureFamily.exists_contDiffAt_root` | Arbitrary finite tails/species and unequal positive diameters; all z>0, species densities>=0, vacMix>0; seed, actual Jacobian and both block determinants internally discharged; amplitudes local near tau=0, no full matrix RDF/OZ claim |

**Build gate:** `LeanCode/MultiTailMSAProject.lean` is imported by
`ExactMSAProject.lean`. Its 132 guarded results depend only on
`[propext, Classical.choice, Quot.sound]`. No new physics axiom, `sorry`,
`native_decide`, or `ofReduceBool` is used in these modules.

**Independent numerical checks:**
`scripts/msa_multitail_closure_check.py` computes c from actual piecewise
real-space Baxter convolutions, then integrates its core for comparison with
the independently supplied spectral formula. It checks 26 pure/binary states,
equal/unequal diameters, repeated rates, zero tails, and rates through `z=60`.
The actual Laplace moments, exterior tails, common-domain reciprocal entries,
and selected adaptive-quadrature convolutions agree to about `7e-15` or better;
the sampled Fourier comparison has relative scaled error at most `1.83e-9`
against a `2e-8` acceptance limit. It samples four nonzero wave numbers, not the
entire continuum. For unequal diameters, the larger-diameter species is the
row when recovering the full positive core; the other entry follows by species
exchange. Raw reciprocal entries are compared only on their common valid
domain. See `results/multitail_extension/independent_closure_checks.json` for
inputs, errors, and the orientation rule.

**Scalar finite-tail checkpoint:** the actual c-side Fourier integration and
assembly of all three spectral blocks are complete. `Qre_eq_integral` and
`Qim_eq_neg_integral` identify the dictionary with actual Q transforms;
`factorization_integrals` states the result entirely in real-space integrals.
The second BH equations can also be derived from the g-side OZ primitive with
explicit RDF support, weighted RDF integrability and moment identifications.
These are finite sums, not infinite Yukawa superpositions. Coincident rates
are allowed: c-side exterior sum closure fixes grouped amplitudes only, so it
cannot be inverted into independent per-tail BH equations without an additional
identifiability condition. The forward given-root exterior theorem has no such
restriction.

**Remaining obligations:** unrestricted given-root labelled Q/G identification and all-parameter physical RDF recovery; mixture actual radial DCF Fourier/core closure; and full matrix RDF/OZ recovery. The old scalar theorem name `hcore`
refers to a c-side core direct-correlation Fourier identity, not RDF h=-1.
L1 integrability does not by itself imply negative-half-line support; support
is either separately assumed for the RDF or proved by definition for Q.
Spatial and local coupling smoothness do not guarantee a global real branch
past a fold, all-parameter strict structure-denominator positivity, normal pressure loops,
or coexistence solutions for finite-order truncations. The complete c-side
closure/factorization scope can now include pure fluids with arbitrary finite
positive-rate Yukawa tails, at a supplied real BH root; any RDF/OZ claim must
carry actual excess L1 or the internal weighted-budget sufficient condition detailed below. Full build including actual RDF/radial OZ reconstruction: `multitail_rdf_mixture_family_build.log` (8870 jobs).


**RDF reconstruction audit and next interfaces (same finite-tail stage).**
`MSAMultiTailRDFBoundary` proves a counterexample to identifying an arbitrary
real BH root with the canonical Baxter/RDF moment data. At xi=1/4, z=1, K=0,

    Dt = 4*pi*(9*exp(-1)-2)/3,  G = 3/(9*exp(-1)-2),

is an exact real BH root, with positive Dt and G. Its factor is
`F_alt(s)=(s-1)/(s+1)*F_PY(s)`, and `F_alt(1)=0`. Its nonzero-k Fourier
structure denominator is exactly the PY denominator (`fourier_denominator_eq_hs`),
but its labelled G differs from the PY seed. `no_rdf_full_gside` proves that
measurability, the half-rate weighted moment L1 majorant, support, weighted
moments for s>1, the labelled G identification, and the full actual g-side OZ
primitive for all s>1 cannot hold together. Continuity of the moment follows
from dominated convergence; it is not assumed as a new physics axiom. No
hard-core condition is assumed in this contradiction. This is **not** a claim
that the same c has no hard-core RDF, and it is not a counterexample on the
canonical weak-coupling PY branch. It is a failure of unrestricted given-root
Q/G identification. Checking Fourier positivity alone cannot select the
causal phase.

`root_factor_ne_zero_at_active_rate` proves F(z_nu) != 0 whenever K_nu != 0.
This is a discrete-rate consequence only. At a zero-strength label, BH may
allow F=P=0 and the second equation then loses moment identifiability; a
continuous limiting moment must be checked separately. A zero-free closed
right-half-plane symbol is a condition for an L1 *causal inverse of that
particular Q factor*, not a necessary condition for the existence of some RDF
for a c that admits a different canonical factorization. The explicit
noncanonical example demonstrates this distinction.

`q_integrable` and `q_nonneg_weighted_integrable` discharge the concrete
finite-tail Baxter kernel's full-line L1 and nonnegative-rate weighted L1.
`existsUnique_causal_moment_window` constructs a unique continuous moment
density on every finite window from the actual q and actual gsource using the
proved Volterra theorem. This is genuine existence, not an assumed h=-1 RDF.
It does not imply global excess-correlation decay or integrability.

The remaining RDF spectral algebra has now also been discharged for arbitrary
finite positive-rate tails, including coincident rates. In
`MSAMultiTailRDFRationalBlocks`, `MSAMultiTailRDFNormalization`, and
`MSAMultiTailRDFSpectral`, define p(s)=rho*secondRHS(s) and the rational T by

    s*F(s) = T(s) + exp(-s)*p(s).

The finite-sum polynomial/tail and polarized tail/tail identities, the actual
BH moment normalization, and the actual second BH equations prove

    T(s)*T(-s) - p(s)*p(-s) = -s^2,
    s*(F(s)*F(-s)-1)
      = exp(-s)*p(s)*F(-s) - exp(s)*p(-s)*F(s).

These identities hold on the complex plane away from the stated finite
rational poles. `reconstructedFactor_ofReal` identifies the meromorphic
factor with the actual Baxter Laplace factor on its regular positive real
axis. The rational identity is a symbol theorem; the subsequent actual integral,
Abel-limit and radial inversion modules now prove its physical Fourier/OZ
interpretation under the explicit decay conditions below.

**Actual conditional RDF reconstruction — now closed and audited.**
`MSAMultiTailRDFGlobal` constructs one actual global causal moment y from the
real Volterra equation, proves uniqueness, actual Laplace transfer and regular
labelled G recovery. Here y(u)=(u+1)g_phys(u+1); its excess is
`e(u)=y(u)-(u+1)`. Raw y is linearly growing, not an L1 density.
`RDFMoments` proves the actual zero/first q moments and BH background
normalization. `RDFDecay` proves exact polynomial cancellation in the excess
source, and internal exponential excess decay/L1 from

    exists delta>0, all delta<z_nu,
    integral_0^infinity exp(delta*t)*abs(rho*q(t)) dt < 1.

`RDFComplex`, `RDFAxis`, `RDFFourier` and `RDFOZ` identify actual complex
Laplace integrals, the actual Abel boundary and the actual core-plus-excess
radial Fourier integral. This yields the Fourier OZ identity for the actual
constructed h. `RDFRegularity` and the new generic radial-kernel/continuity
modules discharge actual weighted moments, triangle-region Fubini, contact
jump regularity and Fourier injection. `RDFRealSpace` finally proves
`reconstructedH_core_and_oz`: supplied real BH root, positive rates,
1-xi!=0, rho!=0, and actual constructed excess L1 imply pointwise h=-1 on
0<r<1 jointly with actual radial3d_conv OZ a.e. on r>0. The theorem
`reconstructedH_core_and_oz_of_small_budget` supplies the L1 premise
internally from the displayed budget, with no separate RDF, hard-core, OZ,
inverse-transform, Fubini or continuity premise. Every real k!=0 then has
strictly positive D(k). These results use only the standard three axioms.
The older compact-kernel WienerRenewal axiom is not used.

The conditional chain is complete; unrestricted real-root reconstruction is
not claimed. Labelled G identification still requires F(z_nu)!=0; active
labels already supply this condition. Outside the explicit sufficient
region, general causal excess decay/canonical branch selection remains open.
No all-state, zero-k thermodynamic, RDF nonnegativity, pressure-loop or
binodal guarantee follows. Transport of the local amplitude family into a
uniform physical solution family still requires control of decay on that
family. Matrix work now includes the actual finite-tail unequal-diameter partial
Jacobian and explicit triangular inverse. `MSAMultiTailMixtureFamily`
reduces both distinct base-block determinants to the existing proved PY
physical determinant and constructs the actual seed internally. For all
positive rates/diameters, individual densities>=0 and vacMix>0,
`MultiTailMixture.exists_contDiffAt_root` constructs a real C-infinity BH
amplitude family near tau=0 for any signed matrix-tail direction, with
no remaining determinant, Jacobian or seed equation hypothesis. Actual matrix Q Fourier is now proved below; actual radial DCF factorization/core
and RDF/OZ recovery remain open. The archived draft in
results is superseded by this compiled module. FMSA_paper has received the
conditional scalar joint theorem and the final 94-guard/8870-job audit.

Primary literature context for the finite-tail Laplace route:
[Blum and Arias (2006)](https://arxiv.org/abs/cond-mat/0602477) give a general
multi-component/multi-Yukawa pair-correlation Laplace solution and an explicit
monodisperse continued-fraction solution. The reconstruction obligations above
are our formalization audit; they are not claims that the paper supplies Lean
proofs or resolves the branch-selection counterexample.


**Actual unequal-diameter matrix Q and cross-correlation — audited checkpoint.**
`MSAMultiTailMixtureFourier` proves complex-weighted full-line Q integrability
and identifies the finite-tail dictionary with that integral for s!=0,
Re(s)>=0. The lower edge lambda_ij=(sigma_j-sigma_i)/2 may be negative;
no causal truncation at zero is made. Its imaginary-axis specialization is
the actual Fourier integral for k!=0. The actual definition and conjugation
at opposite wave numbers also cover k=0, without evaluating the singular
closed dictionary there.

`MSAMultiTailMixtureSpectral` internally derives joint cross-correlation L1
from marginal weighted L1 by a volume-preserving reflection/shear. It then
proves the actual full-line correlation transform. For F=I-D*Qhat*D,
D=diag(sqrt(rho)), its Gram matrix F*F^H is positive semidefinite, and strictly
positive definite conditional on F being a unit. With rho>=0 the exact
entrywise density convention is F*F^H=I-D*C_Q*D, where C_Q is the Q-product
spectral coefficient. That expression is Hermitian; an entry is real iff it
is equal to its species-swapped entry.

C_Q has not yet been identified with the independently defined actual radial
DCF transform. In particular, Hermitian positivity does not establish real
physical reciprocity. The exterior reciprocity theorem uses per-label symmetric K as a sufficient
physical symmetry condition,
whereas the preceding algebraic local family accepts arbitrary matrix K.
The physical exchange relation must be proved, together with the unequal-
diameter core orientation and lower-edge terms. The old four matrix physics
axioms remain neither used by these proofs nor discharged. Actual matrix
RDF/core/OZ reconstruction is still open. The all-order local BH amplitude
family is not yet a first-order exact FMSA DCF identification.

Default full build targets LeanCode, ExactMSACertificate and
ExactMSASparseFeasibility pass: `results/multitail_extension/mixture_actual_Q_spectral_build.log`
(8872 jobs). All 108 guarded footprints are the standard three axioms.
A scan of 38 related source files finds no axiom declaration, sorry,
native_decide or ofReduceBool. The previous 94-guard/8870-job checkpoint
remains in its historical log; this is the new current audit.


**Actual boundary/primitive and first slopes — next audited checkpoint.**
`MSAMultiTailMixtureBoundary.qPrime_integral_boundary` proves the actual
ordinary derivative transform with its lower-edge correction:

    integral Qprime_ij(r)*exp(-s*r) dr
      = s*integral Q_ij(r)*exp(-s*r) dr
          - Q_ij(lambda_ij+)*exp(-s*lambda_ij).

It holds for s!=0, Re(s)>=0, positive finite-tail rates and nonnegative
additive diameters. `lowerEdge_partner_zero` and `_jump_product_zero` prove
that the jump partner vanishes at every positive r when sigma_j<=sigma_i;
`reflected_Q_zero_of_order` gives the reflected Q support result. This retains
the exact larger-diameter-row condition for the full positive core.

`MSAMultiTailMixturePrimitive` identifies C_Q with the actual full-line
Fourier integral of P=Q+Q^T(reflected)-weighted actual Q cross-correlation.
Its weighted L1, real-valuedness and transpose/reflection parity are proved,
including k=0. These facts still do not identify its derivative with radial c.
`MSAMultiTailMixturePrimitiveExterior` proves the actual exterior P at a BH
root, and exterior physical reciprocity/evenness with per-label K symmetry
as a sufficient condition. No diameter ordering is required outside contact.
The remaining species-antisymmetric P is supported on [-R_ij,R_ij], and
`spectralBaxterC_asym_eq_core_integral` reduces actual spectral reciprocity
to an actual integral over that finite core. Core reciprocity remains open.
Repeated rates are allowed; the per-label symmetry assumption is sufficient,
not asserted necessary for a physically symmetric total tail with repeated z.

`MSAMultiTailMixtureFirstOrder` proves the actual first BH derivative at the
PY seed, extracts the first Dt slope from the actual root germ, and uses the
already proved physical first-block inverse to identify it as

    Dt'(0) = rightBlock(inverseBlocks(baseFirst), 2*pi*K/z).

`exists_contDiffAt_root_with_firstOrder_exterior` internally supplies the
actual smooth family, its Dt derivative and the actual convolution-defined
exterior DCF derivative at tau=0. No derivative-existence, Jacobian, seed or
HS-block determinant premise remains in that existence result. Its parameter
range is the same positive z/sigma, rho_i>=0, vacMix>0 and arbitrary finite
species/tails/signed K as the previous family theorem. This is an actual
first-order amplitude and exterior DCF identification; actual first-order
core FMSA DCF and physical matrix RDF/OZ identification are still open.

Remaining mathematical pieces are now explicit: finite-core primitive
reciprocity; the actual ordered positive-r primitive derivative with contact
junction and lower-edge terms; radial DCF transform identification; actual
first-order core FMSA construction identification; and matrix RDF/OZ plus
decay/canonical branch control. The four old matrix physics axioms were
neither reused nor discharged by these results. Full default build passes
`mixture_boundary_primitive_firstorder_build.log` (8876 jobs), with 132 guarded
standard-three footprints and a clean forbidden-proof scan of 42 sources.


**Actual ordered DCF first variation, including the core — audited checkpoint.**
`MSAMultiTailMixtureBasis` expands actual Q and its ordinary derivative in
`Fin 2 ⊕ (tails ⊕ tails)`: two compact polynomial basis functions and two
per-label Yukawa basis functions. Every actual convolution equals the finite
quadratic expression in its amplitudes and fixed basis integrals; component
integrability is proved internally from positive rates and nonnegative
diameters. The actual convolution-defined DCF is C-infinity in coupling
amplitudes at each fixed spatial position, including core knots. This is
parameter smoothness, and does not assert spatial smoothness at a knot.

`MSAMultiTailMixtureLinearized` proves the actual coefficient slopes at
Dt(0)=0. Differentiating the actual W/C definitions eliminates every G'(0)
contribution, leaving W(D1,G0), C(D1,G0), and the corresponding polynomial
increments. Write Gamma0 for the basis coefficients at (0,G0) and Gamma1
for those at (D1,G0) minus Gamma0. The explicit first variation is

    2*pi*r*c1_ij(r) = -sum_b Gamma1_ij,b * Qprime_b,ij(r)
      + sum_l rho_l sum_b,c
          (Gamma1_il,b*Gamma0_jl,c + Gamma0_il,b*Gamma1_jl,c)
          * integral Qprime_b,il(t+r)*Q_c,jl(t) dt.

`linearizedCorrelation` is this fixed finite-integral formula, not a
derivative by definition. `correlation_hasDerivAt_seed` proves it equals
the actual first derivative along any differentiable coefficient family
through the seed, without assuming an improper-integral differentiation
rule. `exists_contDiffAt_root_with_linearizedCorrelation` internally supplies
the genuine local PY BH family and substitutes the already proved dressed
Dt slope. Its whole positive-core interpretation keeps the larger-diameter
species in the row, sigma_j<=sigma_i. The raw algebraic derivative is valid
at every fixed r; the totalized r=0 expression is not a physical origin
limit. Positive rates/diameters, rho_i>=0 and vacMix>0 suffice for the local
family, with arbitrary finite species/tails and arbitrary signed K.

The explicit variation equals the actual Frechet derivative applied to
(D1,0); additivity in K is consequently proved. The prescribed exterior
sum is also identified, without a diameter sorting condition there.
This certifies an actual ordered BH core first variation. Identifying it
with the independent double-propagator FMSA construction remains a separate
open obligation. In particular this does not prove full core primitive
reciprocity, the actual P' to radial-DCF transform bridge, matrix RDF/OZ,
global Taylor convergence or physical coexistence guarantees. The old
four matrix physics axioms remain neither reused nor discharged.

`scripts/msa_mixture_linearized_core_check.py` independently constructs D1
and G0 from the HS blocks, extracts the linear convolution term by exact
odd polarization at fixed G0, and compares it pointwise with the existing
closed double-propagator FMSA implementation. Five binary/ternary states
cover unequal diameters, signed tails, genuinely unmerged repeated BH
labels, z through 60, and 153 spatial positions including core knots and
mediated overlap locations. Maximum normalized DP defect is 4.694e-14;
actual nonlinear BH branch central differences on steps 1e-3 and 5e-4
converge quadratically, with maximum finer-step defect 3.069e-8. This is
finite numerical evidence for the remaining identity, not its Lean proof.

Current default three-target build passes 8878 jobs in
`results/multitail_extension/mixture_linearized_core_build.log`. All 143
guarded footprints are the standard three axioms. A forbidden-proof scan
of 44 related sources and `git diff --check` pass. Earlier audit logs above
are historical checkpoints; validation_summary.json and findings.txt record
this new current checkpoint.


**Actual ordered spatial primitive to DCF — audited checkpoint.**
`MSAMultiTailMixtureRegularity` supplies an explicit continuous right
extension of Q, using clipped compact polynomials and clipped exponentials.
For r below lambda_ij it retains Q(lambda_ij+), so it does not assume a false
vanishing lower boundary value. The extension is globally bounded and
Lipschitz for all positive finite-tail rates, nonnegative additive diameters
and arbitrary real A/qp/W/C. Those properties, component integrability and
the derivative off the two support edges are proved internally.

`qRight_product_eq_of_order` proves the extension changes no actual
Q_il(t+r)*Q_jl(t) product for sigma_j<=sigma_i and r>0: on the support of the
second factor, t+r lies strictly above the first lower edge. It is therefore
legitimate to differentiate the actual correlation via the continuous
extension. `MSAMultiTailMixtureDerivative` discharges its dominating
Lipschitz bound, weighted L1, a.e. derivatives and joint measurability
internally, rather than retaining an integral differentiation premise.
The actual positive-axis cross-correlation derivative is its actual
Qprime/Q integral. The null support/contact locations are explicitly
excluded in the pointwise-a.e. integral argument.

The actual full-line primitive on the ordered positive axis equals the
complex cast of orderedPrimitiveReal. Off contact it satisfies

    (Re P_ij)'(r) = -2*pi*r*c_ij(r),
    sigma_j<=sigma_i, r>0, r!=R_ij.

Both orderedPrimitiveReal and the actual Re P are continuous at every
positive r, including contact. Consequently
`baxterPrimitive_re_hasDerivAt_ae_positive` proves the derivative identity
almost everywhere on the entire positive axis. This is a genuine actual
spatial primitive-to-DCF bridge, valid before imposing BH roots or symmetry.
It does not identify the actual radial Fourier integral with C_Q without
the remaining core reciprocity/integration argument. Nor does it prove
the independent DP FMSA core identity or reconstruct matrix RDF/OZ.
These obligations remain open; the four old physics axioms are unused.

Current default build log is
`results/multitail_extension/mixture_spatial_derivative_build.log` (8880 jobs).
All 159 guarded footprints use only the standard three axioms; a forbidden-
proof scan of 46 related sources and git diff --check pass. The 143/8878
stage above is historical, and its independent core first-variation
numerical evidence remains unchanged.


**Actual radial Fourier bridge — audited checkpoint.**
`MSAMultiTailMixtureShell` proves a globally Lipschitz actual right primitive
and derives actual radius-weighted DCF integrability on compact positive
windows. Its shell identity holds for arbitrary a,b>0, including reversed
endpoints and intervals crossing contact:

    P_ij(a)-P_ij(b)=2*pi*integral_a^b r*c_ij(r).

`Analysis.OneContactCosine` proves cosine/sine integration by parts across
one contact derivative jump. It uses continuity at the contact and the
vanishing sine factor at the origin; no contact derivative is assumed.
`MSAMultiTailMixtureRadial` supplies its analytic premises internally: the
actual primitive is globally Lipschitz on its right extension, belongs to
L1 on the positive axis, decays to zero at a supplied BH root, and actual
r*c is globally L1 there from compact-core regularity and finite Yukawa
exterior decay. Thus the actual ordered cosine/sine identity is proved.

The actual full-line primitive Fourier transform already equals C_Q. Its
evenness now yields the actual ordered radial DCF Fourier coefficient:

    C_Q,ij(k) = radial_fourier(c_ij)(k), k!=0.

For every diagonal species entry, evenness is automatic from
P_ji(-r)=P_ij(r) with i=j, so this identification has no symmetry or core
reciprocity premise. For unlike species, exterior evenness follows from
the root and per-label K symmetry; the only remaining premise is actual
finite-core reciprocity P_ij(r)=P_ji(r) on [-R_ij,R_ij]. This premise is
explicit in `spectralBaxterC_eq_radial_of_core_reciprocity`, and is not
inferred from the BH root. Larger diameter must be the row for positive
core c; `orderedRadialCorrelation` selects that representative.

With core reciprocity for all pairs and nonnegative densities, the actual
ordered radial matrix satisfies the density-weighted Gram factorization
I-sqrt(rho_i*rho_j)*c_hat_ij=F*F^H and is positive semidefinite. It remains
a conditional result: finite-core reciprocity, strict positivity, zero-k
thermodynamics, actual matrix RDF/OZ, and the independent first-order DP
core identity are not discharged. Arbitrary finite species/tails, repeated
positive rates, unequal positive diameters and signed strengths remain
allowed; no upper z bound or global root/branch claim is introduced.

Current default three-target audit: `mixture_actual_radial_build.log`,
8883 jobs, 179 guarded footprints each using only propext, Classical.choice
and Quot.sound. Forbidden-proof scan of 49 related sources and git diff
check pass. The earlier 159/8880 stage and the 153-point DP comparison
remain historical checkpoints. The four old physics axioms remain unused.


**General-species actual PY seed reciprocity — audited checkpoint.**
`MSAMultiTailMixtureSeedReciprocity` now proves that the internally
constructed actual baseSeed is symmetric in its species indices. The
result is uniform over arbitrary finite species and tails, positive rates,
unequal positive additive diameters, nonnegative individual densities
and positive physical free volume. It needs no assumed G0 symmetry.

Let H be the recentered actual HS transform moment, J the actual HS
source, and B=I-diag(rho)*H the actual second HS block. Per-species
moment/source skew is an explicit multiple of sigma_l^2*(sigma_i-sigma_j);
the source skew is the same multiple of xi2*(sigma_i-sigma_j). Their
weighted finite sum cancels exactly, with no remaining exponentials,
yielding B.transpose*J=J.transpose*B. Thus J*B^-1 is symmetric. Its
invertibility is supplied by the earlier actual physical determinant
certificate, and actual baseSeed=(2*pi)^-1*J*B^-1 inherits the symmetry.
This supplies an actual canonical seed ingredient for DP matching; it is
not a proof of primitive core reciprocity, for either general roots or
the full local family, and not the independent DP first-order core identity.

Current default audit: mixture_seed_reciprocity_build.log, 8884 jobs,
186 standard-three guarded footprints. A forbidden-proof scan of 50
related sources and git diff --check pass; previous audits are historical.


**Actual lower-edge Q tangent and two-sided HS amplitude — audited checkpoint.**
`MSAMultiTailMixtureEdgePropagator` proves a genuine actual boundary
quantity, not a candidate defined to equal the desired result. Evaluate
the actual finite-tail Q at lambda_ij, substitute the actual BH amplitudes
and differentiate along an actual root family through the PY seed.
Each tail contributes

    E_nu = -sigma_i*delta_qp_ij + sigma_i^2/2*delta_A_j + W_nu,ij + C_nu,ij.

The polynomial moment combination sigma_j*M_j+2*N_j loses its j dependence:
its Dt weight is 2/z^2+sigma_l/z and its W weight is
[2-z*sigma_l-(2+z*sigma_l)*exp(-z*sigma_l)]/z^2. Actual C=Dt-exp(-z*sigma_i)*W
then factors E=T*Dt. A finite HS moment/source identity and the actual seed
equation identify T as the transposed inverse of the actual first HS block
B. The density-diagonal dual resolvent identity supplies the inverse; both
actual physical block determinants are internally discharged. Therefore

    E_nu=(2*pi/z_nu)*(B_nu^-1).transpose*K_nu*B_nu^-1.

The theorem for an actual local root germ derives the first Dt slope
internally, eliminates Gprime because Dt(0)=0, and proves the actual
Q(lambda+) derivative equals the finite sum of these matrices. The
existence capstone internally constructs the smooth local BH family and
all its boundary derivatives, retaining no family or differentiability
assumption. Arbitrary finite species/tails, unequal positive diameters,
positive rates without an upper bound, nonnegative densities, positive
vacMix, repeated labelled rates and signed strengths remain allowed.

For symmetric per-label K, every E_nu is pair-symmetric. Consequently
the actual pair-skew of lower-edge Q values has zero derivative at tau=0.
This is a concrete boundary tangent ingredient of the DP comparison. It
does not prove full core primitive reciprocity, equality with the
independent DP DCF at all core radii, reciprocity for arbitrary real BH
roots, or matrix RDF/OZ. The numerical 153-point independent core check
remains evidence for the open full identity rather than its substitute.

Current audit: mixture_edge_propagator_build.log, default three targets
PASS (8885 jobs), 207 guarded footprints using standard three axioms.
Forbidden-proof scan of 51 related sources and git diff --check pass.
The four old matrix physics axioms remain unused, not discharged/deleted.


**Actual arbitrary-species HS primitive reciprocity and endpoint correction — audited checkpoint.**
`Analysis/EvenCosine` proves the Fourier/cosine bridge under a.e. evenness,
by symmetrizing an actual L1 function without changing its integrals.
`MSAMultiTailMixtureRadial` now provides that weaker bridge as well as the
previous pointwise sufficient special case. The new
`MSAMultiTailMixtureAEReciprocity` supplies the all-pair actual radial
Q-factorization, actual matrix Gram identity and PSD with only a.e.
finite-core primitive reciprocity retained. Exterior reciprocity is
still internal at an actual root with symmetric per-label strengths.

This correction matters for unequal diameters. Both closed HS support
indicators can contribute at a size-asymmetry knot. A formal explicit
zero-density binary HS example with sigma=[1,2], no Yukawa tails and
r=1/2 gives P01=-4*pi, P10=-2*pi. It is a removable isolated point-value
spike: no change in an integral, no physical reciprocity violation and
no evidence of a higher-order branch or unstable phase. The older
pointwise conditional theorems are valid sufficient statements, but
their premise is too strong for the raw closed-window representative.

The actual new zero-Dt Q equals the independent general-N physMixN HS
kernel pointwise. At nonnegative densities, its actual primitive times
sqrt(rho_i*rho_j) equals the independent general-N matDCFfullN pointwise;
the correlation bridge uses the exact geometric-density product law.
The existing independently proved general-N HS Fourier injectivity
certificate then gives a.e. symmetry. At strictly positive individual
densities the weights cancel to yield full-line a.e. reciprocity of the
actual unweighted P0. This requires sigma_i>0 and vacMix!=0, not an
assumed seed/core reciprocity condition. Zero-density species are not
covered by this entrywise cancellation theorem.

With positive rates and vacMix>0, the actual PY BH seed root is supplied
internally by the actual seed/determinant theorem. All pairs now have
actual ordered radial Fourier factorization and a PSD matrix at nonzero
real k with no retained primitive symmetry premise at tau=0. This is a
zeroth-order full-space identification, not the first-order independent
DP core identity. The full first-order P1 a.e. reciprocity, nonzero-
coupling/arbitrary-root a.e. reciprocity and matrix RDF/OZ remain open.

Current audit: mixture_ae_seed_reciprocity_build.log, default three targets
PASS (8887 jobs), 222 guarded standard-three footprints. Forbidden-proof
scan of 53 related sources and git diff --check PASS. Previous 207/8885
and earlier stages remain historical. The four old matrix physics axioms
are still unused, not discharged or deleted.


**Actual full-space primitive tangent and its actual Fourier transform — audited checkpoint.**
`MSAMultiTailMixturePrimitiveTangent` supplies global boundedness of the actual Q,
L1 and bounds for each independent finite Q basis, and L1 of every fixed
basis-Q cross-correlation. The actual full-line primitive is proved equal
to a finite quadratic expression with these fixed real basisQQ integrals.
The explicit linearizedPrimitiveReal differentiates that finite expression
on an actual BH family through the PY seed; Gprime cancels internally.
The existence capstone constructs the family and its derivative at every
real spatial position, including all support/core knots, from actual
physical determinant/seed conditions. There is no derivative-under-an-
improper-integral hypothesis. P1_ji(-r)=P1_ij(r) is proved, as is the exact
exterior P1=sum_nu (2*pi*K_nu_ij/z_nu)*exp[-z_nu*(r-R_ij)].

`MSAMultiTailMixturePrimitiveTangentFourier` proves actual weighted basis-Q
and basisQQ L1 on the whole Fourier axis, actual basisQQ Fourier product,
and the actual finite-basis Q Fourier identity. The actual Q Fourier first
variation follows by differentiating only its finite coefficients. The
explicit full-space P1 is actually L1 under the Fourier weight for every
real k. Its actual Fourier integral equals an explicit finite spectral
tangent; that expression is proved equal to the actual Q-product first
variation C_Q1. Thus the Fourier integral of the explicit real-space
first variation equals the derivative of actual C_Q along the true local
BH family, with every analytic control internally discharged.

The joint exists_contDiffAt_root_with_primitive_fourier_tangent capstone
internally constructs one local smooth BH family through actual baseSeed,
its all-position actual P derivative and its all-wave-number C_Q derivative
as the actual P1 Fourier integral. Parameters: arbitrary finite species and
labelled tails; sigma_i>0, z_nu>0, rho_i>=0, vacMix>0; signed, zero and repeated
labelled tails allowed. No local family, derivative-existence or integral-
interchange premise remains. The auxiliary fixed-kernel statements only
need sigma_i>=0 and positive rates.

This is actual full-space first-order identification of the primitive and
its Q-side Fourier coefficient. It is not yet the independent DP core DCF
identity or P1 a.e. same-radius reciprocity. Reflection does not imply
P1 evenness; the Fourier coefficient need not be real from this theorem
alone. The canonical zeroth-order HS reciprocity, seed G0 symmetry and
symmetric first-order Q lower-edge amplitudes remain certified ingredients,
not substitutes for the missing whole-core P1 reciprocity/DP equality.
All-real-k primitive Fourier statements do not assert a zero-k thermodynamic
identification. Matrix RDF/OZ and arbitrary-root reciprocity remain open.

Current audit: mixture_primitive_tangent_fourier_build.log; default three
targets PASS (8889 jobs); 252 guarded standard-three footprints; forbidden-
proof scan of 55 related sources and git diff --check PASS. The 222/8887
AE-HS stage and 207/8885 boundary stage are historical. The four old matrix
physics axioms remain unused, not discharged or deleted.


**Independent DP amplitude dictionary and real-space target — audited checkpoint.**
`MSAMultiTailMixtureDPAmplitude` constructs the independent recentered HS
resolvent from the actual HS moment H and actual second HS block B2=I-R*H,
R=diag(rho): Ared=H*B2^-1, Tred=I+Ared*R. The physical determinant theorem
internally proves Tred=B1^-T. Independent bare DP amplitude
bbar=2*pi*Tred*K*Tred.transpose is proved equal to z*E, where E is the
previously certified actual lower-edge Q first slope. Its fourterm expansion
has precisely one rho factor for every internal species index. This is an
independent resolvent construction, not a definition using E or a free
propagator fixed to satisfy the desired identity.

The bare K in these Lean/BH theorems is the coefficient of the unweighted
c1 tail K*exp[-z*(r-R)]/r. In Python notation it is beta*k_bare. The paper's
weighted source is 2*pi*S*K*S, S=diag(sqrt(rho)). The weighted recentered
HS factor is Frec=I-S*H*S; its inverse is internally proved equal to
Tweighted=I+S*Ared*S. Intertwining Tweighted*S=S*Tred proves the exact
weighted amplitude dictionary, including zero-density species, with no
cancellation/division by density.

The actual HS factor is identified with its actual positive-real Q0
Laplace integral. Unequal-size phases are proved exactly:
Factual=Eplus*Frec*Eminus, Eplus_ii=exp(z*sigma_i/2), Eminus=Eplus^-1.
The actual inverse obeys the same phase conjugation, and
Factual^-1_ij*exp(z*lambda_ij)=Tweighted_ij. This is precisely the
phase-removed HS inverse in the bare propagator formula behind the
paper/Python fourterm b_ij construction (Python [LN] eq:bij). Rates are
per finite global label; repeated labels and zero entries are allowed.

`MSAMultiTailMixtureDPKernel` constructs the independent reduced source
B_mn(r)=sum_nu bbar_nu_mn*exp[-z_nu*(r-R_mn)] on r>=R_mn, with the actual
compact HS Q0. It defines the four actual convolution terms

  W_ij = B_ij - sum_n rho_n*(B_in * Q0_jn(-.))
              - sum_m rho_m*(Q0_im(-.) * B_mj)
              + sum_mn rho_m*rho_n*(Q0_im(-.) * B_mn * Q0_jn(-.)).

The reduced DCF target is [W_ij(r)-W_ij(-r)]/(2*pi*r), physically for r>0.
Measurability and global bounds of B, L1 of every single convolution and
all triple inner/outer/joint L1 are proved; the Fubini interchange is
internally justified. Symmetric per-label bare K implies pair symmetry
of independent B, W and this DCF target. Its lower support bound
W_ij(r)=0 for r<-R_ij follows from the actual compact HS support geometry.
These statements require z>0 and sigma>=0 for the independent kernel
controls; physical inverse/amplitude identification additionally uses
sigma>0, rho>=0 and vacMix>0. No upper z bound or tail-count bound occurs.

This provides the concrete independent core target and its correct
normalization, but still does not prove equality with the actual BH P1
or linearizedCorrelation throughout the core. Independent target symmetry
does not establish actual P1 a.e. reciprocity. Raw closed source windows
choose a contact value; compiled piece evaluators can choose a different
representative at contact, so the forthcoming comparison should use a.e.
equality or explicitly matched representatives. The previous 153-point
numerical comparison did not sample exact contact R; it remains finite
numerical evidence and does not discharge this missing identity.
Actual first-order radial FT, arbitrary-root a.e. reciprocity, matrix
RDF/OZ and all-parameter phase guarantees remain open. The manuscript's
claimed scope should stay at its accepted 222 checkpoint until the joint
actual-core identification is completed.

Current audit: mixture_dp_amplitude_kernel_build.log; default three targets
PASS (8891 jobs); 282 standard-three guards; forbidden-proof scan of 57
related sources and git diff --check PASS. Earlier 252/8889 actual P1 Fourier,
222/8887 HS a.e. and 207/8885 boundary audits remain historical. Four old
matrix physics axioms remain unused, not discharged or deleted.


**Actual Q tangent decomposition and actual P1 a.e. reciprocity — audited checkpoint.**
The five new modules `MSAMultiTailMixtureDPQTangent`, `MSAMultiTailMixtureHSParity`,
`MSAMultiTailMixtureDPQTransform`, `MSAMultiTailMixtureDPFactorTangent`, and
`MSAMultiTailMixtureTangentReciprocity` connect the actual BH coefficients to
an explicit two-sided HS tangent and prove actual first-order reciprocity.
This supersedes the first-order reciprocity obstruction in earlier checkpoints;
the independent real-space DP identity and arbitrary-root reciprocity remain open.

For each label, H is the actual recentered HS moment, J the actual HS source,
R=diag(rho), E=(2*pi/z)*B1^-T*K*B1^-1. The actual coefficients satisfy
D1=(I-H*R)*E and W1=(J*R*E)/z. Internally reducing DeltaA and DeltaQp gives

  DeltaA_j = -sum_m rho_m*(A0_m/z + 2*pi*sigma_m/vacMix)*E_mj,
  DeltaQp_ij = sum_m rho_m*[(1/z^2-sigma_i/(2*z))*A0_m
                         +(pi*sigma_m/vacMix)*(1/z-sigma_i)]*E_mj.

The compact quadratic correction has coefficient

  c_j = [DeltaA_j + sum_m rho_m*A0_m*E_mj/z]/2
      = -(pi/vacMix)*sum_m rho_m*sigma_m*E_mj.

It cannot be silently dropped. This is a proved identity of actual BH
coefficients; no independent convolution representation is assumed.
The actual complex HS moments satisfy the exact rank-one parity identity

  H(s)_im - exp(-s*sigma_i)*H(-s)_im
    = (pi*sigma_m/vacMix)*[2-s*sigma_i-(2+s*sigma_i)*exp(-s*sigma_i)]/s^2.

With the unweighted right-density HS factor F(s)=I-Q0hat(s)*R, define
L_nu(s)_ij=exp(-s*lambda_ij)*E_nu_ij and
M_nu(s)_ij=exp(-s*R_ij)*E_nu_ij. The actual single-label Q tangent is

  Q1_nu(s) = F(s)*L_nu(s)/s
             - z_nu*F(-s)*M_nu(s)/(s*(s+z_nu)).

This is identified with the actual finite-basis Fourier derivative at
s=i*k, k!=0, along every differentiable actual BH germ through the physical
PY seed. A joint existence theorem internally supplies a smooth root germ.
The complex algebraic statement uses s!=0 and s+z_nu!=0; it is not an
assertion of full-line Laplace convergence for every such complex s.

Symmetric K implies L_nu(-s)^T=L_nu(s) and M_nu(s)^T=M_nu(s).
The cross term in the actual Baxter product cancels. Its actual P1 transform is

  sum_nu z_nu/[s*(z_nu-s)] * F(s)*M_nu(-s)*F(s)^T
       - z_nu/[s*(s+z_nu)] * F(-s)*M_nu(s)*F(-s)^T.

Both sandwiches are pair symmetric. This is the actual Q-product/primitive
spectral tangent, not yet an integral identification for independent dpW.
The K_BH=beta*k_bare, paper K=2*pi*S*K_BH*S, support-edge phase, and explicit
internal rho dictionaries from the previous DP-amplitude checkpoint remain
part of the correspondence; F in this display is the unweighted right-density
factor, not the sqrt-density Gram factor.

Actual Q is continuous off its lower support edge. Every fixed basis QQ
is continuous on the full axis, using its actual L1 first factor, bounded
second factor, dominated convergence, and the measure-zero translated support
edge. Hence actual P1 is L1 and continuous a.e. Fourier injectivity, with
frequency zero recovered by continuity, proves actual P1_ij=P1_ji a.e.
throughout the core and exterior. Reflection then gives actual P1 a.e. evenness.
No core-reciprocity premise remains in these first-order theorems.

Parameters: arbitrary finite labelled tails/species; z_nu>0 with no upper bound;
unequal positive additive diameters; rho_i>=0, including zero species densities;
vacMix>0; arbitrary signed strengths. Per-label symmetric K is needed for
P1 reciprocity, not for the actual Q tangent decomposition. Repeated rates
and zero strengths are permitted. This does not certify reciprocal arbitrary
nonzero-coupling BH roots, physical radial c1 Fourier coefficients, independent
real-space DP core identity, matrix RDF/OZ, or phase-diagram/positivity guarantees.
The manuscript should await the joint real-space core identification before
asserting exact first-order mixture-MSA/FMSA DCF equivalence.

Current audit: mixture_dp_tangent_reciprocity_build.log; default three targets
PASS (8896 jobs); 337 guarded standard-three footprints; forbidden-proof scan
of 62 related sources and git diff --check PASS. The 282/8891 DP-target audit
and earlier audits are historical. Four old matrix physics axioms remain
unused, not discharged or deleted.

### Joint actual first-order mixture DCF / independent DP core identification

The five modules `MSAMultiTailMixtureDPKernelFourier`,
`MSAMultiTailMixtureDPPrimitive`, `MSAMultiTailMixtureDPRegularity`,
`MSAMultiTailMixtureDPIdentification`, and
`MSAMultiTailMixtureDPFirstOrderRadial` complete the joint stage that was
still open at the 337-guard checkpoint. This is an actual integral and
actual BH first-variation correspondence, including the entire positive
core; no independently supplied DP core equality remains.

The independent source, reflected single convolutions, and double
convolutions have internally proved Fourier-axis L1, including zero
frequency. Change of variables and actual joint Fubini integrability give
the fourterm W transform. With the unweighted right-density factor
F(s)=I-Q0hat(s)*diag(rho), its nonzero-frequency dictionary is

  W_hat(k) = F(-i*k)*B_hat(k)*F(-i*k)^T,
  B_hat(k) = sum_nu z_nu/(i*k+z_nu)*M_nu(i*k).

The previously proved actual P1 tangent sandwich therefore becomes an
equality between actual integrals:

  Fourier(P1)(k) = [W_hat(-k)-W_hat(k)]/(i*k),  k != 0.

Define V(r)=W(r)-W(-r) and define the independent DP primitive by
DP_P(r)=integral_(t>r) V(t). The real-space identification does not assume
that DP_P is L1 or that W has a first moment. For each h>=0, convolve V
with the actual interval indicator on [0,h]. Its Fourier integral is
V_hat(k)*(exp(i*k*h)-1)/(i*k). Fourier injectivity then gives

  P1(r+h)-P1(r) = -integral_r^(r+h) V(t) dt   a.e. in r.

A countable intersection for natural h, the actual finite exponential
exterior of P1, and convergence of the improper V integral fix the
constant: actual P1=DP_P a.e. on the whole real line. L1 of DP_P follows
from this equality and actual P1 L1. The independent DP primitive is
continuous; actual P1 is continuous off its lower support edge, so the
identity is pointwise away from that edge.

The actual fixed-G0 BH coefficients are affine in D. Odd polarization of
the actual finite quadratic expressions gives exactly

  P1(D) = [P(D,G0)-P(-D,G0)]/2,
  c1(D) = [c(D,G0)-c(-D,G0)]/2.

Applying the already proved actual ordered primitive spatial derivative
to both terms proves P1'(r)=-2*pi*r*c1(r), for sigma_j<=sigma_i, r>0 and
r!=R_ij. Independently, dominated convergence proves continuity of every
single and double DP convolution. W is continuous off its source contact;
the fundamental theorem of calculus gives DP_P'(r)=-V(r) on the same
positive off-contact domain. Uniqueness of derivatives yields

  actual c1_ij(r) = [W_ij(r)-W_ij(-r)]/(2*pi*r) = dpCorrelation_ij(r).

The pointwise statement excludes contact; the whole positive axis has
a.e. equality. The actual raw BH radial formula must put the larger
diameter in the row. `orderedLinearizedCorrelation` makes this convention
explicit and supplies all physical pairs using proved DP reciprocity.
No equality is asserted for an unordered raw inner-core representative.

Actual P1 a.e. evenness, the cosine/sine integration by parts across
contact, DP_P decay, and internal radius-weighted c1 L1 give the actual
radial Fourier coefficient of both DP and the canonically ordered actual
c1. It equals the actual Baxter product spectral derivative at every
nonzero real k. The actual local C-infinity BH germ also has dpCorrelation
as its ordered radial derivative at tau=0.

Domain: arbitrary finite labelled tails and species; unequal positive
additive diameters; positive rates with no upper bound; rho_i>=0 and
vacMix>0; symmetric per-label real signed K. Repeated rates and zero
strengths/densities are permitted. K_BH=beta*k_bare, paper
K=2*pi*S*K_BH*S, support-edge phases, internal density factors, and the
compact quadratic Q1 correction remain part of the actual dictionary.

This completes the first-order actual mixture-MSA / independent DP FMSA
DCF core and nonzero-k radial Fourier correspondence. Nonlinear arbitrary
nonzero-coupling root reciprocity, unconditional nonlinear radial matrix
factorization, matrix RDF/hard-core/OZ reconstruction, global branches,
zero-k thermodynamics, strict stability and phase-diagram guarantees are
still open at this historical checkpoint. Those structural gaps are
superseded by the later automatic completion record, and all four old
matrix physics axioms are retired by the final migration record below.

Joint audit: `mixture_dp_joint_identification_build.log`; default targets
LeanCode, ExactMSACertificate and ExactMSASparseFeasibility PASS (8901
jobs); 403 guarded standard-three axiom footprints. The forbidden-proof
scan covers 67 certified sources with no axiom declarations, sorry,
native_decide or ofReduceBool; git diff --check PASS. The 337/8896 and
earlier audits are historical.


**Actual first-order mixture RDF/core/radial OZ — conditional joint certificate.**

The independent DP c1 is now connected to an actual constructed h1, with
pointwise hard-core support and actual radial matrix OZ in the same theorem.
This adds a conditional first-order RDF result; it does not extend the
nonlinear arbitrary-root certificate or establish all-state decay.

The new source modules are `MSAMultiTailMixtureRDFCausal`,
`MSAMultiTailMixtureRDFCausalFourier`, `MSAMultiTailMixtureRDFMoment`,
`MSAMultiTailMixtureRDFPhase`, `MSAMultiTailMixtureRDFReference`,
`MSAMultiTailMixtureRDFSpectralOZ`, `MSAMultiTailMixtureRDFRegularity`,
`MSAMultiTailMixtureRDFDCFRegularity`, and
`MSAMultiTailMixtureRDFCertificate`, under `LeanCode/YukawaOZMix/`,
with `LeanCode/Analysis/RadialMixtureFirstOrder.lean` for the actual radial
matrix convolution/Fourier/injectivity transfer. All are in the default
aggregate through the certificate import; 87 new theorem footprints are guarded.

**Exact conditional domain and actual reference.** Arbitrary finite species
and labelled tails are allowed, with unequal positive additive diameters,
positive rates without an upper bound, repeated rates, and signed symmetric
per-label K. The current RDF capstone requires rho_i>0 and vacMix>0, because
it uses the existing actual HS c0 radial certificate with strictly positive
species densities. The previously certified actual c1/DP result remains valid
for rho_i>=0; zero-density extension of this RDF capstone is not claimed.

`ValidRadialHSReference` is a transparent actual-function interface. Its h0
is a supplied real radial function, not an abstract spectral matrix. It
requires precisely:

* actual canonical HS c0 has integral |r*c0_ij(r)| on r>0 finite;
* r*h0_ij(r) is measurable and globally L1 (a zero extension at negative r
  may be used, since the radial OZ equation only reads positive radii);
* h0_ij(r)=-1 pointwise for 0<r<R_ij;
* h0_ij=c0_ij+sum_m rho_m radial3d_conv(c0_im,h0_mj) a.e. on r>0,
  with the actual `radial3d_conv` integrals.

Here c0 is the actual canonical ordered Baxter correlation at the constructed
zero-coupling PY seed. These reference conditions are retained, not proved to
hold for an independently constructed arbitrary-species HS RDF in this stage.
The hard-core reference field is used for the total h0+tau*h1 core statement;
the first-order OZ proof needs the reference OZ and analytic fields. The
conditions are explicit sufficient conditions for this certificate, not a
claim of mathematically necessary minimal assumptions.

**Actual causal construction.** Recenter the actual HS Q0 by its unequal-size
lower edge lambda_ij=(sigma_j-sigma_i)/2. On t>=0 the continuous causal
kernel is Qc_ij(t)=Q0_ij(t+lambda_ij), supported in [0,sigma_i]. Put
Kc_ij(t)=rho_i*Qc_ij(t), with the LEFT density factor. The actual source is
B0_ij(t)=sum_nu bbar_nu,ij exp(-z_nu*t), using the already certified
independent resolvent-dressed `dpBareAmplitude`. Two actual Banach-Volterra
constructions give continuous Y and U:

    Y_ij(r)=B0_ij(r)+sum_m integral_0^r Kc_mi(r-t)*Y_mj(t) dt,
    U_ij(r)=Y_ij(r)+sum_m integral_0^r U_im(t)*Kc_mj(r-t) dt.

These equations and the construction are valid on every finite positive
interval without an infinite-domain decay or Fourier-inverse premise.
The only first-order infinite-domain condition retained in the capstone is
U_ij in L1(Ioi 0). Actual renewal then proves Y_ij in L1(Ioi 0) internally;
Y L1 is not a second independent decay premise. Kernel and source L1 and
all relevant actual Laplace convolution Fubini conditions are internal.
No all-state U L1 assertion or new small-budget sufficient condition is made.

Define the actual same h1 by

    h1_ij(r)=1_{r>=R_ij} U_ij(r-R_ij)/(2*pi*r),
    R_ij=(sigma_i+sigma_j)/2.

The theorem proves h1=0 POINTWISE for r<R_ij and global L1 of r*h1 under
U L1. For the supplied physical reference, h0+tau*h1=-1 POINTWISE in the
open positive core for every tau. This is a hard-core property of the
linear truncation; it is not a nonlinear finite-tau OZ or g>=0 theorem.
No contact representative identity is asserted.

**Actual transforms and unequal-size phases.** Actual full/half-line
translation invariance, causal convolution Fubini, and actual sine/radial
Fourier integrals identify the constructed h1 transform. Put
E_ii(s)=exp(-s*sigma_i/2), D=diag(rho), Fc=I-Laplace(Kc), and
Fleft=I-D*Q0hat, Fright=I-Q0hat*D. The actual integral dictionary proves

    E*Fleft=Fc*E,
    Bhat=E*B0hat*E,
    physical moment transform=E*Uhat*E.

All support shifts and phases are retained. Actual renewal gives
Fc.transpose*Uhat*Fc=B0hat without assuming an inverse or a determinant
condition. The actual HS radial certificate supplies
T0=I-C0*D=Fright(s)*Fleft(-s).transpose and the equivalent reversed-sign
factorization. It follows internally that

    T0*H1*T0.transpose=C1,

where H1 and C1 are ACTUAL radial Fourier integrals of the constructed h1
and certified canonical actual c1, not symbols assigned by definition to
spectral products. The valid actual reference has H0=C0+C0*D*H0; actual C0
symmetry then supplies T0.transpose*(I+D*H0)=I. Right multiplication yields

    H1=C1+C0*D*H1+C1*D*H0                 (k != 0).

Consequently no extra inverse/determinant hypothesis is needed in this
first-order capstone. This does not prove a global reference determinant or
stability theorem, and involves no division by species density.

**Actual radial transfer.** Actual c1 measurability, its first radius moment,
odd-moment a.e. continuity, and SECOND radius moment are supplied internally.
The second moment follows by bounded multiplication of the already certified
first moment on the finite core and the actual prescribed Yukawa exterior.
For actual c0, measurability and exterior zero are internal; its second
moment follows from the explicit reference first moment and compact support.
For the same h1, global radius L1 and odd-moment a.e. continuity are internal.
Actual finite species sums, radial-convolution Fubini, radius integrability
and continuity, and radial Fourier injectivity give

    h1_ij = c1_ij
          +sum_m rho_m radial3d_conv(c0_im,h1_mj)
          +sum_m rho_m radial3d_conv(c1_im,h0_mj)   a.e. on r>0.

This is the actual integral OZ equation. First-order real-space OZ, core
zero, inverse-transform identification, and convolution identities do not
occur as premises. Fourier identities are certified for k!=0; injectivity
uses the algebraic zero-frequency value of the Lean radial transform and
does not certify a k->0 thermodynamic/compressibility limit. Real-space OZ
is a.e.; hard-core zero and the h0+tau*h1 open-core statement are pointwise.

**Audit and paper boundary.** `firstOrderMixtureRDF_certificate` packages the
same construction's pointwise core with actual a.e. first-order radial OZ.
Default targets LeanCode, ExactMSACertificate and ExactMSASparseFeasibility
PASS in `results/multitail_extension/mixture_actual_rdf_oz_build.log`
(8911 jobs). There are 490 guarded footprints, all using only propext,
Classical.choice and Quot.sound, including all 87 new theorem footprints.
The 77-source scan has no axiom declarations, sorry, native_decide or
ofReduceBool; its manifest is `mixture_actual_rdf_oz_source_scan.json`.
The 403/8901 actual DP DCF audit and earlier checkpoints are historical.
Four old matrix physics axioms remain unused and have not been removed.

Paper language may now say: for finite-tail mixtures with a valid actual HS
reference and integrable constructed causal solution, the independently
certified actual first-order DP/MSA DCF admits a constructed hard-core RDF
satisfying actual linearized radial matrix OZ. Do not claim unconditional
all-state decay, an independently constructed general HS reference,
zero-density RDF extension, nonlinear arbitrary-root RDF/OZ or reciprocity,
strict finite-k stability, g>=0, global Taylor convergence, zero-k
thermodynamic identification, or phase-diagram correctness from this theorem.


**Explicit mixture weighted decay budget and internal HS c0 radius L1.**

The previous 490/8911 conditional RDF checkpoint is strengthened in two
ways. `MSAMultiTailMixtureHSRadius.lean` proves the actual HS c0 first radius
moment internally. At zero coupling actual Q0prime is a bounded compact
polynomial; actual Q0 is globally L1. Bounding the actual correlation
numerator and using actual exterior zero gives canonical c0 radius L1.
Its second radius moment was already reduced to this first moment and
compact support. `ValidRadialHSReference.c0_radius_integrable` is removed.
The actual reference now retains only four fields: measurable r*h0,
global r*h0 L1, pointwise open-core h0=-1, and actual zeroth-order radial
matrix OZ a.e. No reference c0 analytic condition is supplied.

`LeanCode/Analysis/MatrixCausalRenewalBound.lean` uses the total entry
absolute sum ||M||_entry=sum_i sum_j |M_ij| as a continuous scalar majorant.
It is unchanged by transposition, and the actual entrywise matrix Volterra
renewal supplies a scalar norm inequality. The scalar compact-maximum
argument in `CausalRenewalBound.lean` is generalized from equality to this
inequality; the existing scalar equality theorems remain corollaries.
No Wiener-algebra inversion or physics theorem is assumed.

`MSAMultiTailMixtureRDFBudget.lean` identifies the ACTUAL weighted kernel
budget with the following explicit finite-window expression:

    A_delta = sum_i sum_j integral_0^sigma_i exp(delta*t) *
      |rho_i * [Q0phys_ij*(t-sigma_i)
               +Qppphys_jj/2*(t-sigma_i)^2]| dt.

This is not an abstract operator budget. The real LEFT density rho_i and
row support [0,sigma_i] are retained. Absolute values make one common
budget sufficient for both kernel-transposed Volterra steps. The theorem
proves the finite-window identity and actual weighted kernel L1 internally.
For delta>0, delta<=each labelled z_nu, and A_delta<1, put
B=sum_i sum_j sum_nu |actual dpBareAmplitude_nu,ij|. The actual source obeys
exp(delta*r)*||B0(r)||_entry<=B and the actual constructed solutions obey

    exp(delta*r)*||Yc(r)||_entry <= B/(1-A_delta),
    exp(delta*r)*||Uc(r)||_entry <= B/(1-A_delta)^2,   r>=0.

Consequently Uc entry L1 follows INTERNALLY from exponential domination.
`firstOrderMixtureRDF_certificate_of_weighted_budget` assembles this with
the same actual h1, pointwise hard-core zero, pointwise h0+tau*h1 open core,
and actual first-order radial matrix OZ a.e. It has no Uc/Yc decay premise,
no supplied c0 radius moment, and no extra determinant premise. A valid
actual HS reference remains required. The budget is sufficient, not
necessary; its failure does not imply nonintegrability, instability or a
nonphysical state. The criterion is not asserted for every physical state.

A numerical evaluator is `scripts/msa_mixture_rdf_budget_check.py`:

    python3 scripts/msa_mixture_rdf_budget_check.py --rho '[0.01,0.015]' \
      --sigma '[1,1.6]' --rates '[0.6,1.8,1.8]' --delta 0.2

It evaluates the certified finite-window formula with the exact physical
Q0phys/Qppphys parameter dictionary. Default examples are saved in
`results/multitail_extension/mixture_rdf_budget_examples.json`. Their A_delta
values are 0.04605435623 (one species), 0.32717223592 (two unequal species),
0.08011509244 (three unequal species), and 1.37653414070 (denser one-species
example). These are floating-point quadrature checks, not kernel-checked
interval proofs or HS-reference existence/stability certificates. The last
example shows only that this sufficient budget does not apply.

**Independent actual HS reference construction — inspected boundary.**
The old equal-diameter actual existence result
`FMSA.MixtureBaxter.matOzStar_equalDiam_phys` has a standard-three footprint.
It can be a useful future reference-construction entry, but it still needs
the actual unweighted canonical c0 dictionary and global radius moment
transport to instantiate the present reference interface. The unequal-size
Wertheim–Thiele seed terminus remains an explicit missing identity in
`MixtureCorrectedSeed.lean`; its earlier numerical confirmation does not
supply the actual general-N reference theorem. A dependency audit in
`hs_reference_existing_dependency_audit.log` proves that
`matOzStar_unique` and `matOzStar_equalDiam_unique` additionally depend on
`FMSA.matRadialShell_bounded_injective`. Hence their prose labels cannot be
used as evidence of a standard-three general reference construction. None
of these extra-axiom uniqueness results is imported into the new RDF capstone.
The new budget settles first-order causal decay in its sufficient region;
it does not by itself settle the independent actual unequal-size HS h0.

Default targets LeanCode, ExactMSACertificate and ExactMSASparseFeasibility
PASS in `mixture_rdf_weighted_budget_build.log` (8914 jobs). There are now
513 guarded footprints, all using only propext, Classical.choice and
Quot.sound; the 23 new theorem footprints and the refactored scalar
footprints are included. The 80-source forbidden-proof scan and git diff
--check PASS; source manifest is `mixture_rdf_weighted_budget_source_scan.json`.
The 490/8911 and 403/8901 checkpoints are historical. Four old matrix physics
axioms remain unused and have not been removed. All prior nonlinear,
zero-density RDF, contact, zero-k thermodynamic, positivity/stability and
phase-diagram boundaries remain in force.

## 2026-10-09: independent equal-diameter actual HS reference (533 guards)

The equal-diameter first-order mixture capstone no longer takes a supplied
`h0` or a `ValidRadialHSReference` hypothesis. For arbitrary positive finite
species count, strictly positive species densities, a common diameter s>0,
and positive free volume, the actual reference is constructed as

    h0_ij(r) = baxterPsi(etaMix, s, sum_i rho_i)(r) / r.

`HardSphere/BaxterWeightedDecay.lean` proves actual global `baxterPsi` L1
under delta>0 and the scalar weighted kernel mass below one. The proof
recentres the constructed exterior Volterra solution at s, bounds its compact
forcing on a finite interval, and applies the standard-three weighted renewal
bound. Compact core integrability and odd reflection supply global L1;
measurability and global L1 of r*(baxterPsi/r) follow. No symbol nonvanishing,
Wiener inversion or bounded radial-shell injectivity premise is used.

`MSAMultiTailMixtureHSEqualDCF.lean` proves the actual canonical c0 dictionary
directly. Actual zero-amplitude Q and Qprime collapse to the clipped scalar
PY quadratic and its derivative. Their actual improper convolution is the
finite interval [r,s] integral in `baxter_factorization_inner`. The physical
total density is retained and cancelled using its nonzero value. Consequently
`rdfActualHS_ij(r)=c_HS(etaMix,s,r)` throughout 0<r<s and a.e. on r>0.
The open-core pointwise identity and positive-axis a.e. identity intentionally
avoid a pointwise claim at contact, where the raw closed-window Qprime
representative can carry an isolated spike.

`MSAMultiTailMixtureHSEqualReference.lean` proves the scalar kernel is the
actual Kc column sum at equal diameters:

    q0_poly(etaMix,s,sum_i rho_i)(t) = sum_i Kc_ij(t),
    Kc_ij(t) = rho_i * Qc_ij(t).

Thus the scalar weighted mass is bounded by the existing total matrix
entry-absolute-sum budget A_delta. The SAME condition A_delta<1 supplies
HS-reference global radius L1 and both actual first-order causal stages.
Actual scalar `baxterPsi_ozstar`, the proved canonical c0 dictionary and
the actual species sum give zero-order radial matrix OZ a.e. without an
HS OZ or uniqueness assumption. Pointwise open-core h0=-1 is definitional.
All four `ValidRadialHSReference` fields are therefore discharged internally.

The resulting theorem is
`firstOrderMixtureRDF_equalDiam_certificate_of_weighted_budget`. Its inputs
are physical parameters, per-label symmetric finite signed strengths,
delta>0, delta<=every labelled z_nu and A_delta<1. It returns the SAME actual
constructed h1 with pointwise h1=0 inside contact, pointwise
h0+tau*h1=-1 in the positive open core for every tau, and actual first-order
radial matrix OZ a.e. Positive rates may repeat and have no upper bound.
This certifies the structural linear-order equations in the stated sufficient
region; it does not assert g>=0 or a full nonlinear OZ equation at finite tau.

For general unequal diameters, the exact unproved endpoint is still the
constructed corrected full-space HS seed identity
`matBaxterUQmSymFullExt = r*Phi`, where Phi must be the actual canonical
HS DCF, together with global radius L1 transport for that constructed h0.
`MixtureCorrectedSeed.lean` explicitly reduces this to its Wertheim--Thiele
`hseed`; the three-region expression retains unequal-edge outer-Volterra
couplings and cannot be replaced by a common scalar row sum. Numerical
agreement of that seed does not supply the Lean identity. The old
`matOzStar_unique` route additionally depends on
`FMSA.matRadialShell_bounded_injective`, as recorded in the previous dependency
audit, and is not used here. The existing unequal-diameter first-order
capstone still applies whenever an actual `ValidRadialHSReference` is supplied
and the explicit A_delta criterion holds; failure of the criterion proves
neither instability nor failure of the HS reference.

The numerical budget checker now distinguishes equal and unequal diameters.
In `mixture_equal_hs_reference_budget_examples.json`, the two-species
equal-size example rho=(0.01,0.015), s=1, delta=0.2 has A_delta about
0.1156773283; the three-species equal-size example
rho=(0.0003,0.0005,0.0008), s=1.4, delta=0.35 has A_delta about
0.03352897389. These are floating-point quadratures, not Lean interval
certificates. The exact Lean theorem remains conditional on the stated
integral inequality.

Joint default build `lake build LeanCode ExactMSACertificate
ExactMSASparseFeasibility` PASS in `mixture_equal_hs_reference_build.log`
(8917 jobs). All 533 guarded theorem footprints, including all 20 new
footprints, use only propext, Classical.choice and Quot.sound. The 83-source
forbidden-proof scan and git diff --check PASS; manifest:
`mixture_equal_hs_reference_source_scan.json`. The 513/8914 checkpoint above
is historical. No all-state, general unequal-size independent reference,
nonlinear arbitrary-root, zero-density RDF, contact, zero-k thermodynamic,
RDF positivity, finite-k phase-stability or binodal certificate is claimed.

## 2026-10-09: actual unequal pair-contact HS candidate and radius L1 (565 guards)

The new `MSAMultiTailMixtureHSPairCausal.lean` constructs an actual HS
candidate for arbitrary finite species and unequal positive additive diameters.
It supplies pointwise pair hard core, measurable global radius moment,
global radius L1 under the SAME A_delta<1 budget, and the physical full-support
exterior Baxter renewal. It does NOT yet supply actual canonical radial OZ.
The valid-reference wrapper now retains precisely that actual OZ equation
for this fixed constructed candidate, rather than an arbitrary supplied h0
with four separate reference conditions.

An important old-interface limitation was found. The three-region seed
lemmas in `MixtureCorrectedSeed.lean` assume a common core radius sigma and
`Psi_kj(v)=-v` on (-sigma,sigma), for every pair. These are valid conditional
generic lemmas. They cannot directly instantiate physical unequal pair
contacts: a global maximum contact would overextend smaller-pair cores,
whereas a minimum contact would not give all-pair outer vanishing at sigma.
No existing theorem is refuted by this diagnosis. The new candidate uses
each actual R_ij and each actual lower Q edge lambda_mi instead.

For r=R_ij+u and t=lambda_mi+v, additive geometry gives exactly

    r-t = R_mj+u-v.

The exterior unknown is YHS_ij(u)=Psi_ij(R_ij+u), u>=0. Its actual kernel is
Kc_mi(v)=rho_m*Qc_mi(v), retaining LEFT density rho_m and the true row
support [0,sigma_m]. The forcing is the actual contribution from v>u,
where the sampled pair m,j lies in its own core:

    FHS_ij(u) = sum_m rho_m * integral_min(u,sigma_m)^sigma_m
                Qc_mi(v) * (v-u-R_mj) dv.

The definition is a difference of two actual finite interval integrals;
continuity and compact support on the nonnegative axis are internal.
The actual global Banach--Volterra construction satisfies

    YHS = FHS + Kc.transpose causal-convolved with YHS.

Compact forcing supplies a finite exponential weighted bound for every delta.
For delta>0 and A_delta<1, actual YHS entry half-line L1 follows from the
standard-three matrix renewal estimate. The full Psi is glued as -r on
(-R_ij,R_ij), YHS(r-R_ij) on r>=R_ij, and odd reflected exterior on r<=-R_ij.
Compact core plus shifted exterior and reflection give GLOBAL Psi L1.
Consequently h0_ij=Psi_ij/r has internally proved measurable global r*h0 L1
and pointwise h0=-1 on every actual positive open core. These HS-only
analytic results need no delta<=z condition; that tail-rate restriction is
still needed when applying the first-order Yukawa RDF budget capstone.

The source/core split is proved with interval identities that exclude the
contact sample where necessary; no raw pointwise core value is silently
substituted at contact. Change of variables and the actual recentered-Q
indicator dictionary then prove the full physical exterior renewal:

    Psi_ij(r) = sum_m rho_m * integral_R Q_mi(t)*Psi_mj(r-t) dt,
    r>=R_ij,

where Q is the actual dpSeedQ, with its lower support edge retained.

`MSAMultiTailMixtureHSPairSeed.lean` defines the actual physical seed:

    U_ij(r) = Psi_ij(r) - sum_m rho_m integral_R Q_mi(t)*Psi_mj(r-t) dt,
    Seed_ij(r) = U_ij(r) - sum_m rho_m integral_R Q_im(t)*U_mj(r+t) dt.

The reflected first arm and both density weights are explicit. The physical
exterior renewal gives U_ij=0 for r>=R_ij. On actual Q_im support,
r+lambda_im>=R_mj for r>=R_ij, so the actual Seed ALSO vanishes at each
own pair contact and beyond. Thus the outer WT identity
Seed_ij=r*canonical c0_ij is internal for r>R_ij. No common-sigma outer gap
remains in this pairwise construction. The explicit Prop
`HSPairCoreSeedIdentity` retains the still-unproved actual identity a.e. on
each finite Ioo(0,R_ij); its extension to the positive axis is conditionally
proved, excluding the isolated contact. The remaining task is the genuine
finite-core physical WT identity and the actual seed/shell expansion to
radial OZ, or an independent actual Fourier OZ proof. None is supplied by
the radius L1 or exterior theorem alone. The old extra-WH-axiom uniqueness
route is not used.

`MSAMultiTailMixtureHSCommonCoreDiagnostic.lean` gives an exact interface
counterexample: sigma=(1,2), all rho=0, common trial core S=2. For pair 0,0,
on EVERY r in (1,2), the trial is -1, actual canonical c0 is 0 and the
density-weighted radial convolution is 0, hence actual radial OZ fails.
The newly constructed pair-contact exterior is exactly zero at zero density
and the new pair candidate is zero on that same interval. This is a
zero-density definition/interface diagnostic; it is not extrapolated to
a finite positive-density physical counterexample or a failure of the
generic conditional seed theorems.

The reproducible checker `scripts/msa_mixture_hs_pair_check.py` evaluates
the corrected candidate using the actual left-density kernel and analytic
core-tail source, and checks actual canonical radial OZ numerically.
In `mixture_pair_hs_numerical_diagnostic.json`, rho=(0.01,0.015),
sigma=(1,1.6) gives maximum sampled OZ residual 1.3035183e-7 at step .003
and 3.3156710e-8 at step .0015; its maximum reciprocity residual is below
1.8e-9. The three-species unequal example rho=(.0003,.0005,.0008),
sigma=(1,1.4,2.3) gives maximum OZ residual 1.2996870e-8. The checker
records one quadrature roundoff warning; grid refinement is diagnostic
implementation evidence, NOT a Lean WT/OZ or interval-budget certificate.

Joint default build `lake build LeanCode ExactMSACertificate
ExactMSASparseFeasibility` PASS in `mixture_pair_hs_causal_build.log`
(8920 jobs). All 565 guarded theorem footprints, including all 32 new
footprints in this phase, use only propext, Classical.choice and Quot.sound.
The 86-source forbidden-proof scan and git diff --check PASS; manifest:
`mixture_pair_hs_causal_source_scan.json`. The 533/8917 checkpoint above
is historical. The independent VALID unequal-size HS reference remains
uncertified until its actual radial OZ is proved; all nonlinear, all-state,
zero-density first-order RDF, RDF positivity, stability and binodal limits
remain in force.


## Independent actual unequal-diameter HS reference: completed Fourier route

The 565/8920/86 checkpoint above is historical. The actual pair-contact
candidate now satisfies zeroth-order radial OZ internally, under the sufficient
weighted budget. The completed route is independent actual Fourier OZ; it does
not require `HSPairCoreSeedIdentity`, a common-core seed instance, a supplied
HS reference, an inverse-transform premise, or the old extra uniqueness axiom.

For arbitrary finite species, positive additive diameters, strictly positive
species densities and vacMix>0, choose delta>0 with actual A_delta<1. The already
constructed YHS and Psi retain the actual lambda_mi shift, left rho_m, each
pair contact R_ij and odd reflection. The same actual h0=Psi/r has pointwise
h0=-1 for 0<r<R_ij and a measurable global r*h0 in L1.

Ten new modules carry the proof from actual integrals to actual radial OZ:
HSPairSymbolAlgebra, HSPairMoments, HSPairLaplace, HSPairSourceTransfer,
HSPairFourier, HSPairPhysicalSymbol, HSPairMatrixSymbol, HSPairSpectralOZ,
HSPairHSRegularity and HSPairReference (all with the MSAMultiTailMixture prefix).
The existing triangle Fubini lemma in Analysis/IntervalIntegralSwap is
codomain-generalized to a complete real normed space, covering complex-valued
integrals while preserving its real uses.

Actual HS coefficient identities give

    Qc_mi(v)=(v-sigma_m)*(a_i*v/2+b_i),
    a_i=Qppphys_ii, b_i=pi*sigma_i/vacMix,
    1-sum_m rho_m M0_mi=a_i/(2*pi),
    R_ij+sum_m rho_m(M1_mi-R_mj*M0_mi)
      =sigma_i/(2*vacMix)+sigma_j*a_i/(4*pi).

Here M0 and M1 are the actual finite integrals of Qc and v*Qc, not abstract
moments. Actual compact-source triangle Fubini then completes the actual
Volterra transfer:

    Fc(s).transpose*(YhatHS(s)+B(s))=D(s),
    B_ij(s)=(1+s*R_ij)/s^2,
    D_ij(s)=a_i/(2*pi*s^2)
      +(sigma_i/(2*vacMix)+sigma_j*a_i/(4*pi))/s.

This holds for Re(s)>=0,s!=0; the actual YHS L1 premise is discharged by the
budget. The actual radial Fourier integral of h0 is the phase-preserving
positive-moment difference, including the compact -r core. The finite symbol
identity retains the right inverse phase. Its residual factors through
`a*(a*m2-4*c)`, with a=2*pi/vacMix, c=pi*xi2/(2*vacMix), m2=xi2; the physical
relation a*m2=4*c is proved. Rank-two finite sums and actual coefficient/phase
dictionaries identify this symbol with the actual HS Baxter product and
actual canonical c0 radial Fourier transform. Consequently

    H0(k)=C0(k)+C0(k)*diag(rho)*H0(k), k!=0,

is a theorem about actual radial Fourier integrals. Polynomial Qprime is
continuous away from its two support edges; its actual correlation integral
is continuous by dominated convergence using the proved Qprime bound and Q L1.
The canonical larger-diameter row therefore supplies actual c0 continuity off
pair contact. Actual c0 radius/second moments and actual global h0 radius L1
supply radial convolution Fubini, continuity and the proved Fourier injectivity
bridge. The result is actual h0=c0+radialMixtureConv(c0,h0,rho), a.e. on Ioi0.

`rdfHSPairCandidate_valid_of_weighted_budget` now supplies ALL FOUR actual
reference fields internally. `firstOrderMixtureRDF_pairContact_certificate_of_weighted_budget`
adds arbitrary finite signed symmetric labelled Yukawa tails, positive rates
without an upper bound, repeated rates and zero strengths, with delta<=every
rate. It jointly proves the same constructed h1 has pointwise core zero,
h0+tau*h1=-1 on each open pair core for every tau, and actual first-order
radial OZ a.e. No supplied h0/reference OZ/decay premise remains.

The particular finite-core actual Seed WT identity remains unproved as a
separate algebraic statement; the completed independent Fourier route avoids
it. This does not certify nonlinear arbitrary-root mixture RDF/OZ, arbitrary
finite tau, all-state decay, zero-density extension of the first-order RDF
capstone, contact identities, k=0 thermodynamic limits, g>=0, stability,
Maxwell/binodal correctness or phase diagrams. A_delta<1 is sufficient, not
necessary. Numerical quadrature/refinement remains diagnostic only; no
floating-point budget value is promoted to an exact interval certificate.

Joint default build `lake build LeanCode ExactMSACertificate
ExactMSASparseFeasibility` PASS: 8930 jobs in
`results/multitail_extension/mixture_pair_hs_reference_build.log`. All 625
guarded footprints (59 new pair-route theorems plus the generalized triangle
Fubini gate) use only propext, Classical.choice and Quot.sound. The 97-source
scan finds no axiom declarations, sorry, native_decide or ofReduceBool after
nested-comment stripping; manifest `mixture_pair_hs_reference_source_scan.json`.
`git diff --check` PASS. Old FMSA.matRadialShell_bounded_injective and the four
matrix physics axioms are unused by the new reference/capstone, and are not
removed. The budget checker metadata is updated and its six numerical cases
regenerated; its sufficient-condition failure interpretation is unchanged.


Final scope/dependency metadata reconciliation: validation_summary.json's
full_build_log points to mixture_pair_hs_reference_build.log, matching the
625/8930/97 checkpoint. The three actual radial-OZ/reference/first-order
capstone footprints were separately rechecked with standard-three guards;
the reproducible harness and log are mixture_pair_hs_final_dependency_audit.lean.txt
and mixture_pair_hs_final_dependency_audit.log. These repeat checks do not
increase the 625 default gate count. The first-order RDF/reference capstone
retains rho_i>0, distinct from the earlier DCF/DP rho_i>=0 scope. Metadata,
build completion, source manifest and the absence of supplied reference/OZ
premises in the new capstone were reconciled successfully. No nonlinear,
zero-density RDF or wider-decay extension is included in this final cleanup.

## Nonlinear mixture reconstruction and exact dilute boundary (2026-10-09)

The current default checkpoint is **1074 axiom guards / 8991 build jobs /
158 selected Lean sources** (including the thermodynamic-scope module below).
Sixty `MSAMultiTailMixtureNonlinear*.lean` modules contribute 438 guarded
nonlinear theorem footprints, plus 11 thermodynamic scope footprints. The
completed unequal-diameter first-order certificate above is retained.
**Automatic algebraic admissibility of arbitrary finite-mixture actual BH
roots is now proved.** For positive rates, symmetric K and `vacMix != 0`,
the finite Wronskian certificate follows from the actual root without an
independent coefficient or unknown-G reciprocity premise. The actual RDF,
radial OZ and nonzero-k positive definiteness capstone retains its explicit
weighted decay budget and physical diameter/density assumptions. This is
structural closure on that stated domain, not global root existence,
all-state decay, g positivity or thermodynamic route consistency.
See the automatic completion checkpoint below.

The finite tail labels and species indices remain independent. All rates are
positive, with no upper bound and no distinctness requirement. Pair contacts
are `R_ij=(sigma_i+sigma_j)/2`, support edges are
`lambda_ij=(sigma_j-sigma_i)/2`, and diameters may be unequal. Signed and zero
amplitudes are permitted. The reconstruction proofs require positive pair
contacts (positive individual diameters in the capstone), `vacMix != 0`, an
actual BH root where actual label-moment recovery is asserted, and the
sufficient **actual nonlinear** budget below. Analytic construction alone does
not need a density-sign assumption; physical mixture applications use
`rho_i>=0` and `vacMix>0`. Zero-density species are not divided out.

### Actual nonlinear normalization, construction and label moments

`NonlinearMoments` proves the actual BH rank-two coefficient dictionary
`qp_ij=A_j*sigma_i/2+B_j`, and both background normalization identities.
`NonlinearKernel` identifies the zero and first recentered moments with their
actual half-line Lebesgue integrals; no supplied moment premise remains.
The recentered Q is `Q_ij(t+lambda_ij)` for `t>=0`, continuously extended
using its clipped polynomial/exponential formula.

`NonlinearSource`, `NonlinearDecay` and `NonlinearRDF` construct a global
continuous right Volterra solution, with the actual left density inside K:

```
K_ij(t) = rho_i * Q_ij(t+lambda_ij)
GSource_ij(u) = [A_j*u+qp_ij+sum_nu z_nu*C_nu,ij*exp(-z_nu*u)]/(2*pi)
Yg = GSource + Yg causal-convolved with K
E_ij(u) = Yg_ij(u) - (u+R_ij)
g_ij(r) = 0 (r<R_ij), Yg_ij(r-R_ij)/r (r>=R_ij)
h_ij(r) = -1 (0<r<R_ij), E_ij(r-R_ij)/r (r>=R_ij)
```

The hard core is pointwise, with each pair's own contact. The same actual
constructed g satisfies `g=1+h` on positive radii. Its full-line odd radius
moment is measurable and L1 under

```
0 < delta < every z_nu
A_delta = integral_Ioi0 exp(delta*t) * sum_ij abs(K_ij(t)) < 1.
```

This is the nonlinear Q budget, NOT the previously certified compact HS
kernel budget. Its weighted integral exists internally. The forcing's exact
far tail is a finite exponential sum; compact continuity plus that identity
supplies its weighted bound and actual excess L1. `A_delta<1` is sufficient,
not necessary; its failure does not prove absence of a root, decay or physics.

`NonlinearLaplace` proves actual convolution Fubini and the actual matrix
Laplace renewal. `NonlinearGIdentification` identifies the actual BH second
block with `I-Laplace(K)(z_nu)`, and derives its unit property from the same
budget. The first block determinant equals the second block determinant by
the matrix Sylvester identity, so its unit property is also internal, including
zero species densities. These two multiplication blocks are NOT the full
nonlinear amplitude Jacobian; no absence-of-fold theorem follows.

At an actual BH root the same constructed g satisfies

```
integral_Ioi0 exp(-z_nu*r) * r*g_ij(r)
    = exp(-z_nu*R_ij)*G_nu,ij.
```

No G-moment premise, inverse transform, matrix physics axiom or separately
supplied RDF is used. Equal labelled rates force equal G matrices in this
region. `nonlinearMixtureRDF_core_moments_decay_certificate` packages core,
actual radius L1 and actual labelled moments. It has no positive-density OZ
field. The scalar noncanonical-root obstruction remains relevant outside this
sufficient budget region; the result does not declare arbitrary real roots
physical or canonical.

### Finite necessary reciprocity test

`NonlinearReciprocity` defines actual finite rational matrices, with
`b_ij=Q_ij(lambda_ij+)`:

```
J_ij(s) = A_j/s^2 + qp_ij/s + sum_nu z_nu*C_nu,ij/(s+z_nu)
L_ij(s) = A_j/s^2 + (qp_ij-sigma_i*A_j)/s + b_ij
          - sum_nu z_nu*W_nu,ij/(s+z_nu)
s*Laplace(Q_recentered)_ij(s) = L_ij(s)-exp(-s*sigma_i)*J_ij(s)
H(s) = J-J^T + [J^T*diag(rho)*L-L^T*diag(rho)*J]/s.
```

The row contact exponentials cancel exactly in H. Under the actual budget,
`H(s)=0` is equivalent to symmetry of the actual Yg Laplace matrix at `s>0`.
A nonzero residual strictly excludes pointwise pair reciprocity of the same
constructed g. No root premise is needed for this diagnostic equivalence.

`NonlinearFiniteTest` clears the denominators with
`D(s)=s^2*product_nu(s+z_nu)` and constructs an explicit finite polynomial
matrix P with `P_ij(s)=s*D(s)^2*H_ij(s)`. A finite exact coefficient check of
P is equivalent to H vanishing on the entire positive real axis. Repeated
rates are handled as separate factors, without a limiting prescription.
Failure of the coefficient certificate therefore excludes actual RDF pair
reciprocity under the budget. `NonlinearComplexFinite` evaluates the same
real coefficient polynomial at complex s. `NonlinearComplexReciprocity`
proves symmetry of the actual complex Laplace matrix for Re(s)>0.
`NonlinearPointwise` applies ordinary Fourier inversion to the causal
functions after multiplying by exp(-t). Continuous functions with these
equal damped transforms agree on t>0, and closure gives equality at t=0.
Consequently the finite exact coefficient certificate is **equivalent to
actual pointwise g_ij(r)=g_ji(r) for every r>0, including contact**. This
requires positive diameters, vacMix!=0 and the stated nonlinear budget;
it needs neither a BH root nor a density-sign assumption. It does not prove
core primitive reciprocity, nonlinear radial OZ, nonnegative g, or phase
stability. Automatic passage by a general actual BH root remains unproved.

### Actual complex transforms and finite-k factor invertibility

`NonlinearComplex` proves the actual right-renewal transform identity and
actual affine/exponential source integrals for Re(s)>0. The background is
retained explicitly, rather than asserted to be integrable without damping.
`NonlinearComplexKernel` identifies the actual recentered Q integral with
the full QhatComplex dictionary for Re(s)>=0, s!=0, and proves its rational
J/L decomposition. The actual kernel transform norm sum is bounded by the
same A_delta for every Re(s)>=0. Thus I-Khat(s) is a unit throughout the
closed right half-plane; delta>=0 already suffices for this unit theorem.

`NonlinearFiniteK` transfers this to the actual density-weighted Fourier
factor using contact phase cancellation and Sylvester's determinant identity.
The factor is a unit at **all real k, including zero**, when rho_i>=0;
zero-density species are allowed. With an actual BH root, symmetric K,
positive diameters and explicit AECorePrimitiveReciprocity, the existing
actual radial DCF Gram identity then gives a **strictly positive definite**
matrix I-sqrt(rho)*radialFourier(c)(k)*sqrt(rho) for every k!=0. The primitive
core premise remains explicit. This is neither an automatic-core theorem nor
a full amplitude-Jacobian, fold, zero-k radial thermodynamic or binodal result.

`NonlinearFourier` proves the actual nonlinear radius-moment half-line
integrals and actual radial sine/Fourier formula on the imaginary axis.
The source Wronskian identity and its derivation from physical BH root data
are the next remaining step toward general positive-density radial OZ.

### Fully closed nonlinear zero-density boundary and negative-RDF example

`NonlinearBoundary` proves the actual zero-density BH root is uniquely

```
Dt_nu,ij = 2*pi*K_nu,ij/z_nu
G_nu,ij = (1+z_nu*R_ij)/z_nu^2 + sum_mu K_mu,ij/(z_nu+z_mu).
```

For this root the same actual construction has
`g_ij(r)=1+sum_nu K_nu,ij*exp[-z_nu*(r-R_ij)]/r` outside the core, and
`h=-1` inside. For positive diameters, positive rates and symmetric labelled
strengths, `nonlinear_zero_density_certificate` jointly proves the root,
pointwise hard core, actual G moments, global radius L1, and actual radial
OZ AE with the actual canonical ordered Baxter DCF. No core reciprocity or
OZ premise is supplied. The nonlinear kernel is zero and its budget is zero;
an admissible positive delta is constructed internally even with no labels.

For positive pair contact the general actual finite-density contact formula is
`g_ij(R_ij)=[qp_ij+sum_nu z_nu*C_nu,ij]/(2*pi*R_ij)`. A negative numerator
implies actual g is negative on a nonempty interval outside contact, by
continuity of Yg. At zero density the exact negative-contact condition is
`sum_nu K_nu,ij < -R_ij`. Purely attractive nonnegative strengths instead
give nonnegative zero-density g; that boundary result is not an all-density
positivity theorem.

The joint theorem
`nonlinear_long_attraction_short_repulsion_OZ_counterexample` uses any positive
additive diameters, all densities zero, `z=(1,20)`,
`K_long,ij=R_ij` and `K_short,ij=-3*R_ij`. Both strength matrices are symmetric;
the long tail is attractive and the short tail repulsive. The actual unique
root above, the same g/h, and the same ordered DCF satisfy actual radial OZ
AE, while `g_ij(R_ij)=-1` and g is negative on an outside interval for every
pair. This is an MSA mathematical closure solution, not a nonnegative
Boltzmann RDF. It refutes an unrestricted signed-tail physical-positivity
claim; it does not establish a positive-density multiphase/binodal pathology
or a universal finite-order thermodynamic threshold.

At zero density, `nonlinearG_zero_density_coupling_affine` additionally proves
the same constructed g is affine in coupling for every real tau, with the
actual unique root supplied internally at every tau. Thus the negative-g
obstruction in this dilute signed-tail example cannot be repaired by adding
higher Taylor orders. It is not a positive-density pressure-loop, spinodal-A,
binodal or universal thermodynamic order-threshold theorem.

### Joint verification and outstanding positive-density work

All 842 default guards use only subsets of `propext`, `Classical.choice`,
`Quot.sound`; two generic ring identities need only `propext`, `Quot.sound`.
The three-target default build passes with 8959 jobs, logged in
`mixture_nonlinear_reconstruction_build.log`. The independent 217-theorem
dependency audit is reproducible from `mixture_nonlinear_dependency_audit.lean.txt`
and its log. The 126-source scan has zero actual axiom declarations, sorry,
native_decide or ofReduceBool after nested-comment stripping; its manifest
also records source SHA-256 values. `git diff --check` passes. The four old
matrix physics axioms and old radial-shell injectivity axiom remain unused
by these new capstones and are not deleted.

`scripts/msa_mixture_nonlinear_rdf_check.py` records six finite numerical
diagnostics, including unequal binary and ternary mixtures, z=60, repeated
rates, signed strengths, a grid refinement and the exact dilute negative-g
case. Root residuals and the rational residual test pass the numerical checks;
the labelled-moment refinement error decreases by a factor of about four.
Positive-density sampled radial OZ errors are at most 1.253e-6 (the refined
binary error is 5.350e-8); the dilute sharp-tail interpolation error is
1.971e-5. These are truncated floating-point diagnostics, NOT Lean OZ or
interval budget certificates. The numerical artifact records truncation and
grid limitations explicitly.

Remaining for a theorem covering the canonical nonzero-coupling BH branch:
prove that this branch automatically passes the finite Wronskian coefficient
check; the separate RDF reciprocity check follows internally (see below).
The actual phased Wronskian, actual primitive/core reciprocity, and actual
radial OZ transfer with internal regularity are completed under those checks.
Global branch existence, all-state decay, zero-k thermodynamics, g positivity,
Maxwell/binodal correctness and phase stability remain separate questions.
The new result is a finite-admissibility nonlinear mixture closure certificate,
not an unconditional all-root or all-state mixture closure theorem.

### Actual nonlinear radial OZ under finite admissibility (822 checkpoint)

`NonlinearWronskianAlgebra` proves the phased matrix source identity with
explicit rational residuals

```
U(s) = -L(s)+L(-s)^T
       +[J(-s)*diag(rho)*J(s)^T-L(s)*diag(rho)*L(-s)^T]/s
V(s) = J(s)-J(s)^T
       +[J(s)*diag(rho)*L(-s)^T-L(-s)*diag(rho)*J(s)^T]/s.
```

`NonlinearWronskianFinite` clears these denominators with
`s*D(s)*D(-s)` and defines `NonlinearFiniteWronskianCertificate` by the
exact vanishing of all coefficients of the two finite real polynomial
matrices. Rates may repeat; no distinctness or density division is used.
These are checks on the actual BH coefficients, not assumed functional OZ
or core identities.

`NonlinearAbel` proves the imaginary-axis renewal identity by a dominated
Abel limit of the actual integrable excess; the affine background is retained
explicitly. `NonlinearWronskian` derives the actual spectral primitive
reciprocity from the finite checks. `NonlinearCoreCertificate` uses ordinary
Fourier injectivity and continuity at zero frequency to derive full-space
primitive AE reciprocity, hence the previously external core condition.
The actual radial stability theorem
`nonlinear_actualRadial_posDef_of_finite_certificate_and_budget` replaces that
external condition with the finite Wronskian certificate. It needs rho>=0,
an actual root, symmetric K, positive diameters and the budget, but does not
need the separate RDF reciprocity certificate.

`NonlinearSpectralOZ` combines the actual Abel renewal identity, the two
finite certificates and the actual phased Wronskian to prove actual matrix
Fourier OZ. `NonlinearRegularity` proves the same constructed DCF's first
and second radial moments and AE continuity, and the same h's AE continuity.
`NonlinearRadialOZ` transfers actual Fourier OZ to the actual three-dimensional
radial mixture convolution. Its capstone
`nonlinearMixtureRDF_finite_admissibility_certificate` proves simultaneously
for the same constructed g/h/c: pointwise hard core, global radius L1, actual
normalized labelled G moments, pointwise g reciprocity including contact,
and actual radial OZ AE for r>0. All analytic and core reciprocity premises
are derived internally. The explicit assumptions are positive diameters and
rates, vacMix!=0, an actual BH root, symmetric signed K, delta>0 below every
rate, actual A_delta<1, and both finite coefficient certificates. No density
sign restriction is used by this analytic joint theorem. Physical
applications additionally use rho>=0 and vacMix>0.

The 777/8948/115 and 742/8941/108 counts above are historical checkpoints.
The independent audit now prints all 217 nonlinear theorem footprints;
215 footprints have exactly the standard three axioms and two generic ring
identities use only propext/Quot.sound. Automatic passage of
a canonical nonzero-coupling branch through both finite checks remains open.

### Automatic PY starting-point admissibility (834 checkpoint)

`NonlinearHSAdmissibility` proves all three residual polynomial matrices
identically zero for Dt=0 and arbitrary G, densities, unequal diameters and
finite tail labels. Set a=pi/vacMix, c=pi*xi2/(2*vacMix). The HS polynomial
numerators share the finite rate product and have the reduced forms

```
j(x,y,s) = 2*a*(1+c*y)+a*(y+x*(1+c*y))*s
l(x,y,s) = 2*a*(1+c*y)+a*(y-x*(1+c*y))*s-a*x*y*s^2.
```

Their three residual sums factor through a*xi2-2*c, which is identically
zero for the actual PY coefficients. This algebra needs no supplied root,
rate positivity, density sign or budget.
`nonlinear_zero_coupling_Dt_eq_zero_of_budget` additionally proves that any
actual K=0 BH root in the budget domain has Dt=0, using the proved unit
first multiplication block. Thus every such zero-coupling root automatically
passes both coefficient certificates, without an externally selected seed.
`nonlinearHS_base_actual_root` constructs the actual physical PY root, and
`nonlinearHS_actual_joint_certificate` applies the same nonlinear g/h/c
construction: hard core, radius L1, normalized labelled G moments, pointwise
reciprocity and actual radial OZ AE are proved with root and both finite
checks discharged internally. Its sufficient decay budget remains explicit;
this is not an all-state decay theorem. Nonzero-coupling canonical branch
admissibility still needs a proof.

The six numerical diagnostics now include imaginary-axis U/V samples and
actual Q Fourier-factor Gram samples, including k=0. Maximum U/V residuals
are 1.439e-11 / 1.819e-11 (small-frequency cancellation); the minimum sampled
Gram eigenvalue is 0.98461. These are floating-point diagnostics only, not
exact coefficient certificates, an all-k proof, or a k=0 radial thermodynamic
identity. Current audit counts are 834/8957/124; 822/8956/123 is historical.

### One independent finite admissibility certificate (842 checkpoint)

`NonlinearSymplectic` proves a stronger algebraic implication. Write P=diag(rho)
and, at any nonzero complex s, form the finite block matrix

```
A = I-P*L(s)/s,     M = -P*J(-s)*P/s
B = J(s)/s,         D = I+L(-s)*P/s
T = [[A,M],[B,D]].
```

U(s)=0 and V(s)=V(-s)=0 give T*Omega*T^T=Omega. The finite symplectic
transpose theorem gives T^T*Omega*T=Omega. Its upper-left block is
s^(-1)*R(s)=0, hence R(s)=0. **No density division or square root is used**
in this general block construction: arbitrary signed densities and absent
(zero-density) species are included.

`NonlinearAdmissibilityReduction` applies this to the actual complex J/L
dictionaries on the nonzero imaginary axis. The reciprocal polynomial then
has infinitely many complex roots, so its real coefficients all vanish.
`nonlinear_finite_wronskian_implies_finite_reciprocity` therefore requires
only positive rates and the finite U/V certificate, with no supplied BH root,
budget, density sign or diameter assumptions for this algebraic implication.
The separate RDF reciprocity coefficient certificate can be removed from
the nonlinear OZ capstone's independent assumptions.

`nonlinearH_actual_radial_OZ_of_finite_wronskian` gives actual same-constructed
radial OZ with one independent finite certificate, with no density sign
restriction. `nonlinearMixtureRDF_single_finite_admissibility_certificate`
combines hard core, global radius L1, actual normalized G moments, pointwise
RDF reciprocity, actual radial OZ AE and strict actual radial matrix positive
definiteness at every k!=0. The latter combined physical theorem uses
rho>=0, including zero-density species; the root, symmetric signed K, positive
diameters/rates, vacMix!=0 and explicit positive weighted decay budget remain.

This completes the structural and analytic closure chain for finitely admissible
mixtures. Automatic Wronskian admissibility of canonical nonzero-coupling BH
branches is still unproved. A smooth branch and admissibility at tau=0 alone
do not establish that implication. The joint certificate also gives no
universal RDF positivity, Maxwell/binodal correctness, zero-k thermodynamic
identity, full nonlinear Jacobian invertibility or all-state continuation.
Current audit: 842 guards, 8959 jobs, 126 scanned sources; 217 independent
nonlinear theorem footprints, all within the standard axiom set.


### Thermodynamic scope and mixture coexistence (853 checkpoint)

`MSAMixtureThermodynamicScope.lean` adds eleven kernel-checked theorems,
all using exactly the standard three axioms. These delimit the physical
claims of the preceding structural reconstruction rather than supply
thermodynamic route consistency.

A positive semidefinite structural inverse-susceptibility matrix (in
particular a real Baxter Gram matrix) cannot equal a thermodynamic Hessian
that has a negative curvature direction. The comparison is meaningful only
in the same density coordinates and normalization. No such identification
between our actual DCF and an energy-route Hessian is supplied by the
structural OZ theorem. Its strict finite-k positivity is conditional on
finite admissibility and the decay budget; it is not an all-state stability
or thermodynamic coexistence theorem.

For mixtures P = sum_i rho_i mu_i - f. With the full chemical-potential
vector fixed, pressure equality is equivalent to equality of tangent-plane
intercepts. A kernel-checked binary example f(rho1,rho2)=rho1^2-rho2^2 has
actual partial derivatives mu=(2rho1,-2rho2). At (1,1) and (2,2), pressure
and equimolar weighted chemical potential agree, and the density-ray
free energy/pressure vanish identically, but the component chemical
potentials differ. This is a general thermodynamic counterexample, NOT
an actual MSA state or a measured MSA binodal failure. A fixed-composition
scalar Maxwell construction cannot establish full mixture coexistence.

For prescribed standard PY mixture pressure formulas scaled by pi/6,
with packing moments m_k=(pi/6) sum_i rho_i sigma_i^k and eta=m_3,

```
p_c = m0/(1-eta) + 3m1m2/(1-eta)^2 + 3m2^3/(1-eta)^3
p_v = m0/(1-eta) + 3m1m2/(1-eta)^2 + 3m2^3/(1-eta)^2
p_c-p_v = 3eta*m2^3/(1-eta)^3 > 0  (0<eta<1, m2>0).
```

The exact difference and strict inequality are proved. Every finite coupling
jet retaining these seed values still differs at tau=0; higher coupling order
cannot fix that seed discrepancy. This is coefficient/formula algebra,
NOT a Lean identification of both pressure formulas with our reconstructed
RDF/DCF integrals. It does not apply to a separately corrected common HS
reference such as a prescribed Carnahan-Starling/BMCSL free energy.

RDF nonnegativity is an independent issue: the previously proved actual
long-attraction/short-repulsion dilute OZ counterexample has negative g on
an outer interval and an exactly affine coupling dependence. No higher
Taylor order repairs that dilute example. The exact finite-density contact
criterion also provides a computable failure test; a proof of a particular
positive-density canonical-root failure region remains separate.

Paper wording: do not claim Maxwell is universally mathematically invalid,
that a route-specific binodal is necessarily wrong, or that SCOZA is the
only possible remedy. Ordinary MSA/FMSA does not guarantee agreement
between routes or accurate coexistence. Within one specified free energy,
pressure/chemical potential and common tangents must be derived consistently;
for mixtures all species chemical potentials must match. SCOZA enforces
selected route consistency, normally compressibility versus energy, but is
not a proof of all-route equality, universal g>=0, accurate arbitrary-mixture
phase diagrams, or physically acceptable spinodal-interior correlations.
It is not implemented or certified by this Lean work.

Primary sources checked for this scope correction:
- Santos, PRL 109, 120601 (2012), https://arxiv.org/html/1204.4551v2
  (PY route inconsistency, pure/mixture extension).
- Lebowitz, Phys. Rev. 133, A895 (1964), https://doi.org/10.1103/PhysRev.133.A895
  (additive hard-sphere mixture PY solution and distinct pressure routes).
- Pini, Stell and Wilding (1998), https://arxiv.org/html/cond-mat/9801277v1
  (Sec. 2, compressibility/energy consistency; spinodal-interior exclusion;
  Sec. 3, coexistence via equal pressure and chemical potential).
- Reiner and Hoye, JCP 128, 114507 (2008), https://arxiv.org/abs/0712.3739
  (further virial-route consistency and short-range limitations).

Final structural status remains conditional: automatic finite Wronskian
admissibility of canonical nonzero-coupling BH branches is unproved. It must
remain an explicit hypothesis/open step in the paper, even when universal
thermodynamic and RDF-positivity guarantees are excluded from the scope.
Audit: 853 default guards, 8960 jobs, 127 source hashes; 217 nonlinear plus
11 thermodynamic-scope footprints. Build and combined audit logs are
`mixture_thermodynamic_scope_build.log` and
`mixture_thermodynamic_scope_dependency_audit.log`.


### Automatic dilute admissibility at finite coupling (861 checkpoint)

`MSAMultiTailMixtureNonlinearDiluteAdmissibility.lean` adds eight guarded
standard-three theorems. At rho=0, W=0, C=Dt, A=2pi, qp=2pi R_ij and
b_ij=-pi sigma_i sigma_j+sum_u Dt_uij. If Dt is symmetric, J(s) is symmetric
and L(s)=L(-s)^T. Thus all three finite residual polynomial matrices vanish
identically, for arbitrary finite/repeated tail labels, diameters and G.
No root, rate positivity, or budget assumption is needed for this polynomial
algebra. For an actual dilute BH root, symmetry of K implies symmetry of Dt
through Dt_uij=2pi K_uij/z_u, so both exact coefficient certificates are
automatic, including nonzero coupling. This completes automatic admissibility
on the entire dilute boundary, not along positive-density nonzero-coupling
canonical branches.

The capstone `nonlinearDilute_finitely_admissible_negative_RDF_counterexample`
combines the SAME actual long-attractive/short-repulsive dilute root, the finite
Wronskian certificate, zero weighted budget, actual radial OZ, strict structural
matrix positive definiteness (at zero density that matrix is the identity),
and g<0 on an interval outside every positive pair core. Thus even passing
the full structural admissibility test cannot imply universal RDF positivity.
No positive-density failure region or phase-diagram conclusion is inferred.
The earlier exact affine-in-coupling result still applies to this example.

Current final audit: 861 default guards, 8961 three-target build jobs,
128 scanned source hashes; 225 nonlinear plus 11 thermodynamic-scope independent
footprints (236 total), all within the standard axiom set. Logs:
`mixture_dilute_admissibility_build.log` and
`mixture_dilute_admissibility_dependency_audit.log`. Automatic admissibility
of positive-density canonical nonzero-coupling branches remains unproved.


### BH root Yukawa-pole cancellation and exact completion probes (875 checkpoint)

Two new modules remove the finite Yukawa-pole part of the automatic
positive-density admissibility problem:

- `MSAMultiTailMixtureNonlinearPoleCancellation.lean`: nine theorems,
  including the actual-root capstones
  `nonlinearRoot_all_yukawa_pole_defects_zero` and
  `nonlinearRoot_yukawa_residue_matrices_zero`.
- `MSAMultiTailMixtureNonlinearPolePolynomial.lean`: five theorems,
  including `nonlinearRoot_wronskian_polynomials_zero_at_all_rates`.

The normalized matrices at a rate `z_u` are
`H=(2*pi/z_u)G_u`, `P=diag(rho)`, `E=diag(exp(-z_u*sigma))`,
`Q=Qbar(z_u)`, `B=Dt_u*(I-P*Q.transpose)`,
`W=H*P*Dt_u`, `C=Dt_u-E*W`, `J=H*(I-P*Q)`, `L=Q+E*J`.
Here `J,L` are the actual rational matrices divided by `z_u`.
The first BH block and symmetric K imply `B.transpose=B`; the second
BH block supplies the displayed J identity. Exact noncommutative algebra gives

```
U_plus = (I-E*H*P)*(B.transpose-B)*P*H.transpose
V_plus = H*P*(B.transpose-B)*P*H.transpose.
```

Transposition gives `U_minus=0`. With those identities,
`V_minus=B-B.transpose+E*V_plus*E.transpose=0` as well.
Consequently all four unnormalized Yukawa residue matrices vanish directly
from the actual BH root. No symmetry of unknown G, contact-selection equation,
density inverse, weighted decay budget, free-volume hypothesis, or supplied
Wronskian coefficient certificate occurs in this step. Positive rates ensure
that the actual rational matrices are defined at the positive labels.
The proof permits arbitrary finite species/tail types, arbitrary density and
amplitude signs, unequal diameters, zero-density species, and repeated rates.

The polynomial module further proves that both actual U/V numerator matrices
vanish at every `+z_u` and `-z_u`. This is a *necessary part* of admissibility,
not the whole coefficient certificate. For repeated labels some point-zero
conditions can be automatic from surplus denominator factors; their required
multiplicity must not be inferred from point values alone.

`scripts/msa_mixture_ward_symbolic_probe.py` now supplies reproducible exact
completion certificates for three finite rational instances, over independent
normalized C/W variables. Its density inputs are `r_i=pi*rho_i` and its
amplitudes are divided by pi, so no growing or approximate contact exponential
enters this algebraic completion problem. The exact linear-span checks give:

| instance | r | diameters | rates | independent pole values | coefficient identities |
|---|---|---|---|---:|---:|
| binary single tail | 1/50, 1/100 | 1, 3 | 1 | 6 | 22 |
| binary two tails | 1/50, 1/100 | 1, 3 | 1, 5 | 12 | 32 |
| ternary single tail | 1/100, 1/200, 1/300 | 1, 2, 3 | 2 | 15 | 60 |

Every one of these 114 coefficient identities is expanded and checked with
exact Sympy arithmetic; the rational multipliers are saved in
`results/multitail_extension/mixture_ward_symbolic_probe.json`.
This is finite-instance symbolic evidence, not an arbitrary-parameter Lean
completion theorem, an interval stability test, or a phase calculation.

**Still unresolved:** derive a uniform completion lemma from the actual
amplitude/moment dictionary, including the remaining origin and polynomial
terms, and handle coincident-rate multiplicity without extra assumptions.
Then compose it with the already certified root/budget reconstruction theorem.
The finite Wronskian hypothesis remains in the general positive-density
capstone, and `full_mixture_closure_certificate` and
`mixture_automatic_canonical_nonlinear_admissibility` remain false.
No all-state existence, thermodynamic route agreement, RDF nonnegativity,
Maxwell/binodal accuracy, or universal expansion-order pathology threshold
follows from this pole result.

Pole checkpoint validation: **875 default axiom guards, 8963 three-target build jobs,
130 selected source hashes; 250 independent theorem footprints (239 nonlinear
plus 11 thermodynamic), standard axiom subsets only; nested-comment source scan
and `git diff --check` pass.** The full automatic mixture certificate remains open.


### Uniform HS-normalized origin completion (900 checkpoint)

Three additional modules, with **25 kernel-checked theorems**, replace the
finite-instance origin calculations by uniform algebra:

- `MSAMultiTailMixtureNonlinearCompletion.lean`: arbitrary finite-dimensional
  Lagrangian origin algebra, double-pole cancellation, residue factorization,
  and polynomial finite-pole completion.
- `MSAMultiTailMixtureNonlinearOriginJet.lean`: 2-by-2 **block-position** kernel
  identities. These are not a binary-species specialization: the species sum
  is an arbitrary real linear functional on an arbitrary index type.
- `MSAMultiTailMixtureNonlinearOriginDictionary.lean`: actual BH M/N/A/B and
  weighted C/W moment bridges, and the actual order-three/order-two origin
  coefficient cancellation and residue kernel shape. Tail rates need only be
  nonzero for these identities; repeated labels are allowed. No root, symmetry
  of unknown G, positivity of densities, or density inverse is used.

Let P=diag(rho), k=pi/vacMix, m2=xi2, e=(1,...,1), x=sigma,
a=A, b=nonlinearB, and C_p=sum_u C_u/z_u^p,
W_p=sum_u W_u/z_u^p. The actual dictionary now proves

    R_j = sum_m rho_m [(W_2+C_2)_mj
                       - sigma_m (W_1-C_1)_mj/2],
    b = k*x + 2*k*R,
    a = 2*k*(e+M) + k*m2*b.

The corresponding HS values are b0=k*x and a0=2*k*e+k^2*m2*x.
Use q=x*a^T/2+e*b^T, p=-x*a^T/2+e*b^T,
A=e*a^T and L_0=C_0-x*b^T. The rational Baxter blocks have origin jets

    J(s)=A/s^2+q/s+C_0-C_1*s+C_2*s^2-C_3*s^3+...,
    L(s)=A/s^2+p/s+L_0+W_1*s-W_2*s^2+W_3*s^3+....

With Omega=[[0,I],[-I,0]], set

    T(s) = [[I-P L(s)/s, -P J(-s)P/s],
            [J(s)/s,      I+L(-s)P/s]],
    Tn(s) = T0(s)^(-1) T(s),
    V=[-P;I], U=[I,P].

T0 is the already certified HS symplectic reference. Its inverse has only
orders 1,2,3 at the origin. The new kernel identities prove that the possible
orders 6,5,4 in the formal coefficient product vanish **pointwise before the
species sum**. Order 3 vanishes by the actual a/M/b relation; order 2 by both
a and b relations. The remaining residue kernel is [[-X,-X],[X,X]], yielding
the species-matrix shape V X U after reinstating the density factors. The
constant Lagrangian projection vanishes pointwise as well.

The general completion lemma is proved for a polynomial matrix F and a finite
set S of **distinct nonzero pole values**: all F(s)=0 for s in S, entry degrees
at most |S|, a strictly stronger lower-right block bound (or zero block),
U F(0)=0, and skew F(0), imply F=0. The lower-right entries vanish by root
counting; the origin block lemma then forces F(0)=0; the additional zero at
0 finishes root counting. This also covers an empty S using the zero-block
alternative and requires no inverse of P.

**Completion argument to implement, not yet a proved actual-root capstone:**
The origin jet suggests Tn=R0/s+Treg+O(s), R0=V X U and U Treg V=0.
Thus the order-two pole in En=Tn Omega Tn^T-Omega is zero, and its remaining
origin residue lies in V*(matrix)*V^T. The actual BH root already cancels
all finite reflected Yukawa pole residues in the original defect. Multiplying
by the HS inverse does not introduce finite nonzero poles. At infinity En is
O(1/s), while its lower-right block is O(1/s^2). A rational defect with these
bounds and only a simple origin pole must be R/s; the lower-right residue is
zero, so the Lagrangian origin structure forces R=0. This is the intended
uniform completion mechanism.

The actual rational/polynomial bridge still has to establish these jets and
bounds as statements about the actual defect numerator, including cancellation
of surplus denominator factors and the transfer back to the existing U/V
coefficient certificate. **Neither full_mixture_closure_certificate nor
mixture_automatic_canonical_nonlinear_admissibility is set true.** The new
coefficient definitions are verified kernels of the normalization calculation,
not a replacement for this remaining denominator/degree proof.

For repeated rates, a promising simplification is to form the rational
common denominator over the finite image of rate values, rather than over
labels. J(s) and L(s) are sums of simple fractions; repeated labels do not
create higher-order poles in these sums. Since all rates are positive, the
poles of J/L at -z and of the reflected J/L at +z are disjoint. U/V therefore
have at most simple finite poles. At a repeated pole, its residue is the sum
of the already certified per-label residue expressions. This observation
must still be formalized; point zeros of the old label-product numerator
alone do not establish the necessary factor multiplicities.

The physical scope is unchanged: structural completion cannot imply g>=0,
thermodynamic route consistency, global branch continuation, correct Maxwell
or binodal predictions, or a universal expansion-order pathology threshold.

Origin checkpoint validation: **900 default guards / 8966 three-target build jobs / 133 selected source hashes / 275 independent footprints** (264 nonlinear plus 11 thermodynamic). All use standard axiom subsets; 273 use the full three, and two generic HS ring identities omit Classical.choice. Nested-comment/string source scan and git diff check pass. Build and dependency logs are `mixture_origin_completion_build.log` and `mixture_origin_completion_dependency_audit.log`.


### Distinct-rate cancellation and fixed origin reduction (951 checkpoint)

Seven modules add 51 guarded theorems. Let S be the finite image of positive
rate values, m=|S|, P(X)=product_{r in S}(X+r), D(X)=X^2 P(X), and
F(X)=product_{r in S union (-S)}(X-r). Every tail label remains in the J/L
numerator sums. Repeated labels contribute once to the denominator and all
their amplitudes to the residue at their shared rate. The actual rational
J/L denominator identities, including arbitrary real evaluation away from
poles, are proved in `NonlinearDistinctPoles`.

`NonlinearDistinctResidues` proves that residues collect by rate fibre, then
sums the four already proved BH-root residue identities. No symmetry of the
unknown G, inverse density, equal diameter, or distinctness of rates is
assumed. `NonlinearDistinctWronskian` obtains zeros at every +r and -r for
the actual deduplicated U/V numerator polynomials.

Since S and -S are disjoint, |S union (-S)|=2m. The reflected linear factors
are pairwise coprime. `NonlinearDistinctReduction` therefore proves F divides
both actual numerator polynomials. It also proves deg U<=2m+5 and deg V<=2m+4.
Consequently U=F*u and V=F*v with deg u<=5 and deg v<=4. F is monic and F(0)
is nonzero. These are actual-root theorems, valid uniformly for arbitrary
finite tail/species sets, including repeated rates and the empty tail set.

`NonlinearDistinctCertificate` defines u=U /_monic F and v=V /_monic F.
The checks coeff_n(u)=0 for n=0,...,5 and coeff_n(v)=0 for n=0,...,4 are
**equivalent to the previous full finite Wronskian certificate at a supplied
actual BH root with symmetric K and positive rates**. Polynomial cross
identities transfer between the deduplicated and original labelled
Wronskians, even when the old label product has surplus factors. The equivalence
proves that eleven checks per ordered species pair suffice regardless of
tail count; it does not assert that arbitrary roots pass those checks.

`NonlinearFixedOriginAdmissibility` connects the new fixed certificate to the
existing joint actual RDF certificate: hard core, integrability, recovery of
all labelled G moments, pointwise reciprocity, radial OZ almost everywhere,
and positive definiteness for every real k!=0 under the actual weighted
budget. Positive diameters, rho>=0, vacMix!=0, delta>0 below every z, and the
actual nonlinear budget <1 remain the capstone hypotheses.

`NonlinearOriginExpansion` proves an exact finite expansion for every n:

    z/(s+z) = sum_{p=0}^{n-1}(-s/z)^p + (-s/z)^n*z/(s+z).

It proves the corresponding actual J/L expressions with moments C_p/W_p
and explicit rational remainders. These are exact identities for z!=0,
s+z!=0, without an infinite-series convergence assumption. The remainder
at s=0 equals the next actual moment, directly connecting the rational
functions to the moment dictionary used by the earlier origin kernels.

**Still unfinished:** lift the exact J/L finite expansions to the actual
HS-normalized matrix defect, then use the certified kernel cancellations
and fixed degree bounds to show the eleven quotient coefficients vanish
from the BH equations/dictionary alone. The earlier 900-checkpoint description
of deduplication as unformalized is superseded by this section; the full
HS-normalized rational defect bridge remains unproved. Both
`full_mixture_closure_certificate` and
`mixture_automatic_canonical_nonlinear_admissibility` remain false.

No RDF positivity, route consistency, universal fold/expansion-order result,
or correct Maxwell/binodal prediction follows from these structural identities.

Validation: **951 default guards / 8973 three-target build jobs / 140 selected
source hashes / 326 independent footprints** (315 nonlinear and 11 thermodynamic).
324 footprints use the standard three axioms; two generic HS ring identities
omit Classical.choice. Nested-comment/string source scan and git diff check
pass. Logs: `mixture_distinct_origin_build.log` and
`mixture_distinct_origin_dependency_audit.log`.


### Automatic arbitrary-finite mixture completion (1074 checkpoint)

Eighteen modules add 123 guarded theorems. The algebraic gap recorded at the
951 checkpoint is closed. `nonlinearRoot_automatic_finite_wronskian` proves
that a supplied actual BH root with symmetric tail strengths K, positive
rates, and nonzero vacMix automatically passes the full finite Wronskian
certificate. This covers arbitrary finite species/tail label sets, repeated
rates and rates without an upper bound. Its algebraic proof does not assume
equal diameters, positive/invertible densities, or symmetry of unknown G.
Zero-density species rows remain present.

The proof uses the **unscaled** 2N-by-2N kernel H, density matrix
R=diag(rho,rho), and skew matrix Omega=[[0,I],[-I,0]]. Products keep R
explicitly inserted. This matters: proving only the density-scaled defect
would erase the conditions for zero-density rows. The intrinsic defect is
H Omega + Omega H^T + H R Omega H^T.

Let P be the deduplicated rate polynomial, Q=P(X)P(-X), and let D denote
the numerator of the HS inverse kernel with denominator X^3. The exact
finite J/L origin expansion is lifted to the actual polynomial matrix.
The normalized numerator N=X^3 Q D+X^3 Hnum+D R Hnum factors as X^5 M.
Its two lowest coefficients are M0=Q0 A and M1=Q0 S+Q1 A, where
A=V B U, U=[I,I], V=[-I;I], and U S V=0. The actual moment dictionary
proves these facts with no root or unknown G symmetry premise.

The reduced normalized defect is

```
Fn = X Q (M Omega + Omega M^T) + M R Omega M^T.
```

Its constant coefficient is zero and U times its first coefficient is
zero. It is skew. At an actual symmetric-K root, the reflected finite-pole
factor F divides each actual U/V Wronskian numerator. The cleared affine
normalization identity, together with the HS defect identity, gives
X^10 Fn = B (Q W) B^T, B=X^3 I+D R, where W is the unscaled actual
Wronskian block matrix. Because (Q F)(0) is nonzero, the origin power cancels
and Q F divides every entry of Fn, including zero-density rows.

If m is the number of distinct rates, deg(QF)=4m, deg Fn_ij<=4m+1, and
its lower block has degree <=4m. The quotient therefore has degree at most
one, and its lower block is constant. Zero constant coefficient, skewness
and the Lagrangian first-coefficient projection force the entire quotient
to vanish. These degree arguments also cover an empty tail label set.

To transport zero defect back to the actual unnormalized Wronskians,
B has degree-three leading coefficient I. A generic determinant top-
coefficient lemma proves det B is nonzero; the polynomial adjugate cancels
the congruence B E B^T. No inverse density is used. Hence the actual U and
V Wronskian polynomials vanish and the old finite certificate follows.

`nonlinearMixtureRDF_automatic_admissibility_certificate` connects this
automatic theorem to the existing actual constructed nonlinear g/h/c:
pointwise core, global radial L1, all label G Laplace moments, pointwise
species reciprocity, radial OZ almost everywhere, and positive definiteness
of the density-weighted structural matrix for every nonzero real k. Its
analytic assumptions remain sigma_i>0, rho_i>=0, vacMix!=0, and the explicit
actual weighted kernel budget <1 at a positive delta below every rate.

This completion does **not** certify global BH root existence/continuation,
unconditional passage of the decay budget, g>=0, thermodynamic route
consistency, Maxwell/binodal physical accuracy, universal finite-order
anomaly thresholds, or SCOZA. Earlier conditional capstones are retained
for compatibility; their independent Wronskian premise is now discharged
by the new actual-root theorem.

Validation: 1074 default guards; three-target build PASS; 158 selected Lean
source hashes current; 449 independent theorem footprints (447 use the
standard three axioms, two generic HS ring identities use propext and
Quot.sound). The selected nested-comment/string scan contains no custom
axiom, sorry, native_decide or ofReduceBool, and git diff --check passes.
Logs: `mixture_automatic_completion_build.log` and
`mixture_automatic_completion_dependency_audit.log`.


### Legacy matrix interface migration and four-axiom retirement (2026-10-09)

All four declarations are now **theorems**, with exactly one declaration
of each public name and no retained axiom wrapper:

- `MSAMixture.matExactMSAEqualDiam_hcore`
- `FMSA.ExactMSA.MatEqualDiamCertificate.matExactMSAEqualDiam_kspace_residual`
- `MSAMixture.matExactMSAUnequalDiam_hcore`
- `MSAMixture.matHSexactUnequalDiam_kspace`

The old `matMSACoreCorr`, `matCoreCorrUneq`, `matCoreHSuneq`, factor
products and closed cos/sin/exp residual are unchanged. No equality or
compatibility certificate was added as an input. The former Fourier
certificate is now imported and guarded in the default ExactMSA target.

To avoid an import cycle, BH-root definitions, recentering, and Baxter
Laplace transforms were separated from closure-recovery capstones.
`MSAMixtureLegacySingleTail` proves the actual singleton-tail root,
Q/Qprime, amplitude and factor dictionaries. The actual automatic finite
Wronskian theorem then supplies primitive reciprocity and the actual
radial matrix Gram identity. Checked radius integrability and the proved
piecewise Baxter convolution identify the legacy nonlinear DCF almost
everywhere and split its actual Fourier integral into HS, core correction
and tail. The actual zero-strength HS seed supplies the HS Fourier anchor;
subtracting the two Gram relations proves the original unequal hcore.

At equal diameters, the raw outer numerator is reciprocal at the origin.
Its symmetric sum is identified by the sixth coefficient of the actual
U Wronskian numerator, which vanishes automatically at the root. Hence
cC0o=-cEmo-cEpo: the possible extra 1/r term is absent. The three
polynomial coefficients reduce directly to 2*pi times coreC1/coreC2/coreC3;
row independence of qp eliminates the cubic numerator term. Species
contractions of both BH equations reduce the two exponential coefficients
exactly to the old coreC4 and coreC5 expressions. This proves equality
of the original five-coefficient and unequal convolution cores for every
positive radius, including contact, and hence equality of their actual
Fourier integrals. The equal hcore follows from the unequal theorem.
Finally the already proved scalar Fourier formulas yield the original
closed matrix residual. SymPy is no longer a logical premise at any step.

The migrated legacy Fourier domain is explicit: z>0, k!=0, sigma_i>0,
rho_i>=0, vacMix>0, symmetric K, and a supplied actual BH root; equal
interfaces also require sigma_i=sig>0. The HS anchor uses the internal
zero-strength root and therefore takes no nonlinear root premise. These
Fourier identities require **no weighted RDF decay-budget hypothesis**.
Their HS subtraction does use positive free volume. They do not assert a
root exists at every state. The general finite-tail automatic theorem and
RDF/OZ capstone keep their previously stated domains; the four legacy
interfaces are faithful single-tail specializations of that construction.

All consumers are migrated: equal/unequal factorization, the physical HS
anchor, Fin-1 reduction and the OZ-derived capstones. The Fin-1 interface
now explicitly requires z>0; nonnegative density, positive free volume
and K symmetry follow from its scalar premises and singleton indices.

Validation: `lake build LeanCode ExactMSACertificate
ExactMSASparseFeasibility MatExactMSAEqualDiamCertificate` passes (9008 jobs).
The default import adds 77 guarded standard-three dependency footprints,
including all four retired names and their migrated public callers, to
1074 existing multitail guards (1151 tracked guards; other project gates
are additional). The independent 526-theorem joint audit reports 524
standard-three footprints and two existing generic HS standard-two
footprints. The nested-comment/string-aware scan covers 182 current Lean
source hashes with no axiom declarations, sorry, native_decide or
ofReduceBool. `git diff --check` passes. Reproduction:
`scripts/msa_mixture_legacy_retirement_audit.py` after the stored build and
dependency-audit commands. Logs and exact domain are in
`results/multitail_extension/mixture_legacy_retirement_validation.json`.

Retirement is structural proof completion, not a new claim of g>=0,
thermodynamic route consistency, accurate Maxwell/binodal coexistence,
global root continuation, universal finite-order anomaly thresholds or
SCOZA. The unrelated shell-injectivity axiom is outside this retirement
and is absent from every audited footprint above.


### Package boundary migration (2026-10-10)

The Lean workspace now contains three independent scientific packages:
MSA_and_1st_Truncation (the recorded completed foundation), Other_Closures
(PY/PYE/HNCB consumers), and SCOZA (separate MSA-SCOZA and FMSA-SCOZA import
boundaries, with no SCOZA theorem claimed yet). The foundation owns the
original LeanCode modules and imports neither downstream package. The
original LeanCode source paths remain compatibility symlinks. Public
mathematical declaration names, statements and proof bodies are retained;
the mixed DP/closure files have been partitioned at declaration boundaries.

This migration changes project ownership and build isolation, not the
scope, hypotheses or axiom status of any existing mathematical result.
The four retired matrix axioms remain theorems. Historical conditional
FMSA contour/contact/no-spinodal results retain their explicit extra
assumptions. New SCOZA claims must be proved and gated downstream.

The foundation release manifest records the source/configuration baseline;
both downstream projects lock its digest and version. Boundary checks
verify source ownership, absence of reverse/sibling dependencies, actual
Lake environments, and preservation of the split declarations and closure
gates. Current build/validation results are in
results/project_split/validation.json; reproduce with
scripts/build_lean_projects.py and scripts/lean_project_boundary_audit.py.
