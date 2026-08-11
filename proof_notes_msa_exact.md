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
| MSAEXACT.1 | `msaBaxter_factorization_of_closure` — coefficients satisfying the algebraic system ⇒ `Q̂(s)·Q̂(−s) = 1 − ρĉ(s)` | ◑ **down-payment DONE 2026-08-10** (`YukawaOZ/MSABaxterTransform.lean`, axiom-clean): the Baxter-function ansatz `msaBaxterFn` (`q0_poly` + Yukawa), `D→0 ⇒ q0_poly`, and the two Yukawa transform lemmas (`yukawa_laplace_unit`, `yukawa_tail_laplace`). ⚠ **The full factorization (closure recovery) is the remaining analytic core** — a multi-file effort re-running `baxter_wiener_hopf_factorization` with the tails |
| MSAEXACT.2 | elimination at one tail — degree 8, **REDUCIBLE = two quartics**; the physical branch is a quartic | ◑ **DONE 2026-08-10** (`YukawaOZ/MSAElimination.lean`, axiom-clean; Python `msax_elimination.py`). ⚠ **Corrects the earlier "irreducible"** — that was a float + uncorrected-Eq(2) artefact |
| MSAEXACT.3 ⭐ | `msaRoot_unique_of_coupling_lt` — **exactly one physical root below an explicit coupling threshold** | ◑ **provable core DONE 2026-08-10** (`MSAClosedForm.lean`, axiom-clean): positivity/(39) selection + `physical_baxter_factor_unique` + the **capstone** `msaRoot_unique_of_coupling_lt` (physical uniqueness given the measured monotone coupling). ⚠ The monotonicity of `a` in `K` on the physical branch, and the explicit `βK≈3` threshold, stay **measured** (branch of a transcendental quartic — outside `ring`) |
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

**Opens only when Group MSAX's MSAX.5 returns GO.** The gating is deliberate: MSAEMIX stacks a
genuinely new difficulty (which matrix root) on an algebra that must already be right.

| Task | Title | Status |
|------|-------|--------|
| MSAEMIX.1 | `msaMixture_factorization` — the matrix form of MSAEXACT.1 at general `N` | ☐ gated on MSAX.5 |
| MSAEMIX.2 | `msaMixture_reduces_to_scalar_at_fin_one` — the `N = 1` specialisation **is** MSAEXACT.1 | ☐ gated |
| MSAEMIX.3 | mixture root selection | ☐ deliberately left open pending MSAEXACT.3 |

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
