# General-Purpose Math Axioms (`LeanCode/Analysis/`)

Registry for **general-purpose mathematical axioms**: classical, textbook-citable theorems with
long-standing external proofs that are simply not in the pinned Mathlib (`v4.31.0`, commit
`fabf563a`) yet. This is formalization debt, not open mathematics. Distinct from the project's
**physics axioms** — now **exactly one (1)**, and it is *pre-placed with no consumer*:
`pyhs_mixture_no_spinodal` (`HSMixture/MixtureNoSpinodal.lean`, added 2026-07-19), the
**multicomponent** structure-factor nonsingularity for the not-yet-built mixture track.
Full inventory: `todo_lean.md`'s
Axioms table. Lean home: `LeanCode/Analysis/`.

**Admissibility.** (a) a *named* classical theorem, true independently of this project; (b)
confirmed absent from Mathlib by a reconnaissance pass (source search + Mathlib's `docs/1000.yaml`
unformalized tracker); (c) the *narrowest* statement closing the gap, with anything derivable from
existing Mathlib split off as a genuine theorem. **Prove first, axiomatize only on failure** — 7
axiom candidates have been retired by proving (MA.2/4/5/9/10/11/12), and the proof attempt caught a
statement bug in 4 of those (see *Statement bugs*). MA.12 is the sharpest case: the scoping brief
expected an axiom, but the positive-symbol specialization proved derivable via Plancherel coercivity. Deliberately **rejected**: an "arc-vanishing" axiom for `h_explicit`'s
specific `Ĥ` (`proof_notes_ozfix.md` `OZFIX.10`) — that assumes the hard part of the theorem being
proved rather than citing established mathematics.

## The axioms (4)

All four are contour/boundary facts blocked by one shared gap: Mathlib has no winding numbers, no
residue theorem, no Rouché, no general contour API (all tracked unformalized in `docs/1000.yaml`).
Its only nearby result, `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`,
covers a *single concentric* hole. **All four retire together when Mathlib gains winding
numbers / homotopy invariance.**

### Axiom 1 — `circleIntegral_eq_sum_of_small_circles`
`ContourDeformation.lean` (2026-07-15). Keyhole/slit deformation: for `f` continuous on a closed
disk minus finitely many disjoint open holes and differentiable off a countable set, the big
circle's integral = the sum of the hole circles'. **Derives** (genuine theorem)
`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles`, the finite residue-sum formula, via Mathlib's
existing disk Cauchy integral formula. **Consumers:** `OZFIX.10`, MZERO Route B.

### Axiom 2 — `halfDiskBoundary_eq_sum_of_small_circles`
`ContourDeformation.lean` (2026-07-15). Same content for the **upper half-disk boundary** (`[-R,R]`
diameter + arc, parametrized to compose with `jordan_lemma_arc_bound`); holes confined to the open
upper half-disk. Fourier-inversion arguments close a semicircle, not a circle, and Axiom 1 is
deliberately circles-only. **Derives** `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`.

*Not reducible to Axiom 1* (2026-07-16): Axiom 1 needs `f` controlled on the *full* disk; here `f`
is uncontrolled below the axis and no general extension exists (Schwarz reflection needs `ℂ`-valued
`f` real on the axis; this is general-`E`). The implication runs the other way. Retirement paths:
(1) hole-free half-disk Cauchy is provable *today* via Mathlib's own `exp`-of-rectangle trick
(~200–400 lines; shrinks but does not remove the axiom); (2) a single off-center hole reduces to
the annulus theorem by a Möbius change of variables — but does not survive the half-disk shape (the
conformal map isn't Möbius; hole circles stop being circles); (3) multiple holes needs
cross-cut/subdivision invariance = the shared missing core.

*Soundness review (2026-07-16).* No value-set hypotheses (continuity is demanded on the closed
region minus **open** holes, so the hole circles are covered); finite identity, so no
convergence-mode trap; orientation closes correctly. `hd` demands differentiability on the *closed*
region — deliberately stronger than Mathlib's annulus analogue, harmless for consumers, relaxable
later (Axiom 1 shares this). Checked against the exact statement (`axiom2_check.py`): `f` with 3
poles inside plus poles outside the region, `|LHS−RHS| ≈ 3e-8`.

### Axiom 3 — `sokhotski_plemelj_upper`
`SokhotskiPlemelj.lean` (2026-07-15, pre-placed on request; **no consumer yet**). Integrated upper
boundary value: given the symmetric-truncation principal value exists with value `L`,
`lim_{ε→0⁺} ∫ f(x)/(x−x₀−iε) dx = L + iπ·f(x₀)`. P.V. existence is a *hypothesis* (a plain
`Tendsto`), so the axiom asserts only the boundary relation — no distribution theory, no Hölder
existence theory; upper version only. Mathlib has no Hilbert transform / P.V. API (Y1.3 was
re-routed around this gap). Checked on 3 test functions (linear-in-`ε` convergence). **Retires**
when Mathlib gains a Hilbert-transform/P.V. API.

### Axiom 4 — `contourIntegral_eq_of_homotopic_loops`
`HomotopyInvariance.lean` (2026-07-16, pre-placed on request; **no consumer yet**). Homotopy form
of Cauchy's theorem (Ahlfors Ch. 4 Thm 16): `C¹` loops freely homotopic **through loops** inside an
open `U` on which `f` is holomorphic off a countable set have equal contour integrals. The
`hHloop` condition is essential — the statement is false without it. **Derives**
`contourIntegral_eq_zero_of_null_homotopic`, plus the axiom-free bridge
`circleIntegral_eq_unitLoop_integral`. Checked with positive, null-homotopic, **and negative**
controls (loops in different homotopy classes differ by exactly `|2πi·res₁|`, so the hypothesis
does real work).

*An addition, not a replacement.* It is the principle behind Axioms 1/2, which are classical
corollaries via keyhole homotopies — but those derivations are **open follow-on work**, so all
three stand. Pre-placed against a recommendation to keep the two narrow axioms: a general "unified
residue theorem" cannot even be *stated* in current Mathlib vocabulary, and this statement
quantifies over all homotopies, so it cannot be spot-checked the way Axioms 1/2 were.

## The axioms — Wiener / Hermite–Biehler (2, awaiting processing, added 2026-07-18)

Two analysis gaps blocking **general-`η` `POLE.11`** (Baxter poles in the open UHP ⇒ `baxterPsi`
decay). Both regimes' *dilute* (`η < (3−√7)/2`) cases are already unconditional theorems
(`BaxterDilutePoleLocation.lean`, `BaxterDiluteDecay.lean`); these axioms are invoked only for
`η ≥ (3−√7)/2`. The **conditional reductions** consuming them are axiom-clean
(`baxter_pole_im_pos_of_symbol_ne_one`; `baxterPsi_bounded_Ici_of_tendsto_zero` /
`r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero`, `BaxterExteriorDecayReduction.lean`), so the
axioms enter only where the analysis genuinely does. **Trade rationale:** each retires (part of) a
*physics* axiom (`baxter_exterior_regularity`'s decay clauses; the `POLE.11` premise feeding
`oz_fixed_pt_unique`) with a *math* axiom — a net epistemic gain (a classical, externally-proved
theorem replaces an opaque physics assertion).

**End-to-end loop CLOSED 2026-07-18** (`HardSphere/BaxterExteriorRegularityGeneral.lean`): the
symbol bridge `qhat_symbol_nonvanishing` (`z = i k`: `∫₀^σ q0_poly·e^{−zt} = Q̂(−iz)`,
`Re z ≥ 0 ⟺ Im(−iz) ≤ 0`; `z=0` removable) feeds MA.14 into MA.13's wiring, giving the general-`η`
`baxterPsi_bounded_Ici` + `r_mul_ozBaxterFixedPt_tendsto_zero` (the two exterior clauses of
`baxter_exterior_regularity`). `#print axioms` of both = **exactly `{propext, Classical.choice,
Quot.sound, volterra_renewal_tendsto_zero (MA.13), G_baxter_ne_zero_on_lower_core (MA.14 core)}`** —
no other axioms. So for all physical `η<1` those two clauses now rest on just the two Wiener/HB math
axioms (dilute `η<(3−√7)/2`: unconditional theorems).

### Axiom 5 — `volterra_renewal_tendsto_zero` (MA.13, Paley–Wiener renewal) — ✅ PROCESSED 2026-07-18
`Analysis/WienerRenewal.lean`. Project-independent (abstract `q, g, ψ`, Mathlib vocabulary only):
a right-compactly-supported kernel whose Laplace symbol `1 − q̂(z)` is nonvanishing on `{Re z ≥ 0}`
gives a decaying renewal/Volterra solution.

**Processing outcome — kept as an axiom, verified + wired (NOT proved).** Unlike MA.10/11/12 this is
a **legitimate axiom**: reconnaissance (2026-07-18) confirmed Mathlib has no Wiener `1/f`
(Gelfand-for-`L¹`) theorem, no `L¹` convolution Banach algebra, no Laplace transform, no
Paley–Wiener/renewal theory — and, decisively, **no elementary shortcut** (contrast MA.12's
Plancherel-coercivity). Mathlib *does* have the abstract half —
`WeakDual.CharacterSpace.exists_apply_eq_zero` (nonvanishing on the character space ⇒ invertible, for
a general commutative complex Banach algebra) — but the concrete Wiener algebra `ℂδ⊕L¹` and its
character-space = compactified-half-plane identification are absent, and that identification is the
hard analytic core. So it is registered as an axiom, not proved.

**Numerically verified before landing** (`ma13_verify.py`, `ma13_dense.py`), the essential safety
step for an axiom I cannot prove: dense **negative** kernels (`‖q‖₁ ≥ 1`, matching `q0_poly`'s sign)
with symbol nonvanishing on the RHP have `ψ → 0`; any RHP zero of `1 − q̂` gives exponential growth.
So the statement is true, the symbol hypothesis is load-bearing, and it is **non-vacuous for the dense
regime** (the dilute case is already a theorem, `BaxterDiluteDecay.lean`).

**Statement fix (caught while wiring — the MA discipline's "attempt catches bugs" pattern).** The
axiom originally required `∀ t, t < 0 ∨ S < t → q t = 0`. The `t < 0` disjunct is **unsatisfiable by
the intended instance `q0_poly`** (a nonzero polynomial for `t < 0`, only `= 0` for `t > σ`), and is
mathematically inert — the equation evaluates `q` only at `r − t ≥ 0` and the symbol integrates only
`[0, S]`, so `q`'s values on `(−∞, 0)` never enter. Weakened to `∀ t, S < t → q t = 0` (strictly
stronger theorem, still true, now instantiable via `q0_poly_outer`).

**Wiring done** (`HardSphere/BaxterRenewalDecay.lean`, `#print axioms` = this axiom + standard three):
`baxterPsiOuter_tendsto_zero_of_symbol` instantiates the axiom at `q := q0_poly`, `g := baxterForcing`,
`ψ := baxterPsiOuter` after the `[σ,∞) → [0,∞)` shift (change-of-variables `t ↦ t+σ` in the renewal
integral; forcing tail-vanishing from `baxterForcing_eq_zero_of_two_sigma_le`; support from
`q0_poly_outer`), giving `baxterPsiOuter → 0` from the concrete symbol nonvanishing. Helper
`baxterPsiOuter_continuousOn_Ici` (axiom-clean). The symbol hypothesis (`1 − ∫₀^σ q0_poly·e^{−zt} ≠ 0`
on `{Re z ≥ 0}`, ⟺ `Q̂ ≠ 1` on `{Im k ≤ 0}` via `z = ik`) is **MA.14**'s output, left as an explicit
hypothesis so the wiring is independent of MA.14's in-progress file. Discharges the
`Tendsto baxterPsiOuter atTop 0` hypothesis of `BaxterExteriorDecayReduction.lean`.

### Axiom 6 — MA.14 — **`baxter_no_open_lhp_pole_core` FULLY RETIRED → theorem 2026-07-21; MA.14 is now the abstract `zeroFree_lowerHalfPlane_of_homotopy`**

> **2026-07-21 — MA.14 retired and re-homed.** The domain axiom `baxter_no_open_lhp_pole_core` is now
> a **theorem** (`BaxterHermiteBiehler.lean`), proved from the `η`-homotopy of the open-lower-half-plane
> zero count (`Qhat_complex_ne_one_of_im_neg`, `BaxterLowerHalfPlane.lean`).  Its only residual input
> is the new **pure-analysis, project-independent** axiom `zeroFree_lowerHalfPlane_of_homotopy`
> (`Analysis/ZeroCountHomotopy.lean`, `FMSA.Analysis`): a jointly-continuous family of entire functions
> whose closed-LHP zeros stay in `‖z‖<R` and never touch the real axis keeps its open-LHP zero-freeness
> along the homotopy (argument principle / Hurwitz — Mathlib has neither Rouché nor the parametric
> argument principle).  Four inputs assembled: base case (dilute `η<(3−√7)/2`), real axis (the `k⁶`
> identity, `G_baxter_ne_zero_of_real`), origin (`one_sub_Qhat_complex_zero_ne_zero`, the exact triple
> zero `c₃=i(1+2η)/(1−η)²`), uniform escape (`exists_uniform_escape_radius`).  Working on the entire
> `H=1−Q̂` (not `G_baxter`) makes the origin a regular boundary point.  **Consequences:** `HardSphere/`
> now has **no domain-referencing axiom**; the ledger is unchanged at 8 (7 math, all in `Analysis/`, +
> 1 physics `pyhs_mixture_no_spinodal`), but MA.14 is now general math, not domain-specific.  Bonus:
> the real-axis discharge routes through the elementary `k⁶` identity, so `G_baxter_ne_zero_of_im_nonpos`
> no longer depends on the no-spinodal axiom either.  Numerical witness `verify_ma14_route.py`; full
> record `proof_notes_pole.md` → "POLE.11-general / MA.14".  The 2026-07-18 disposition below is kept
> for provenance — its "keep MA.14 concrete / winding bridge dis-recommended" call was superseded once
> the homotopy route (which needs only a *general* zero-count-invariance axiom, discharging the
> real-axis obstacle via `k⁶` rather than a winding count) was found to close.

### Axiom 6 (historical) — MA.14 Hermite–Biehler root location — **RETIRED & SPLIT into 2 PHYSICS axioms 2026-07-18**

**Update (2026-07-18): `G_baxter_ne_zero_on_lower_core` is RETIRED.** Per the physics-contingent
finding (MA.14 = "no spinodal" + plus-factor validity, NOT abstractable), it is split into two
*named physics facts*, and MA.14's `G_baxter_ne_zero_of_im_nonpos` / `qhat_complex_ne_one_of_im_nonpos`
are now THEOREMS on them:
1. **`pyhs_no_spinodal`** (`BaxterNoSpinodalEquiv.lean`) — the real-axis PY-HS structure-factor
   positivity `∀ k≠0, 0 < 1−ρĈ(k)` (= Task `OZ.20`/`BAXTER.16`). Equivalent forms
   (`qhat_complex_ne_one_of_real`, `one_sub_rho_radial_fourier_c_HS_pos`) are theorems via the
   axiom-clean equivalence `qhat_complex_ne_one_iff_no_spinodal`. `#print axioms` of BAXTER.16 =
   `{standard three, pyhs_no_spinodal}`.
2. **`baxter_no_open_lhp_pole_core`** (`BaxterHermiteBiehler.lean`) — the *strict* open-LHP bounded
   core `{Im k<0, k≠0, ‖Npoly‖≤‖Dpoly‖} ⇒ G_baxter≠0` (the winding / canonical-plus-factor content
   not covered by no-spinodal or the norm bound).

**Classification (user directive 2026-07-18: only ONE physics axiom, more math axioms OK):**
(1) `pyhs_no_spinodal` is the **single PHYSICS axiom** — the PY-*closure* property "no spinodal"
(structure-factor positivity; a different closure could have one).  (2)
`baxter_no_open_lhp_pole_core` **stays a MATH axiom = `MA.14`** — a determinate *root-location* fact
about the explicit Baxter symbol (provable in principle via `MA.11` + winding), the same
domain-referencing math axiom `MA.14` always was.  So this line adds **exactly one physics axiom**
and keeps one (reshaped) math axiom.  The historical shrunk-core writeup is kept below for provenance.

**ROUTE TRIAGE (2026-07-21) — dedicated pass; statement CONFIRMED TRUE, two elementary routes
REFUTED, one complete route found.**  Full record: `proof_notes_pole.md`, "POLE.11-general / MA.14".
* **Not a statement bug.**  Deflated argument-principle count gives open-LHP zero count `0` robustly
  (`R∈{15,40,100}`, `ε∈{1e-3,1e-6}`, `η∈[0.02,0.97]`).  The raw count is *garbage* until the exact
  **triple zero of `G_baxter` at `k=0`** (the `(−ik)³` factor) is divided out — it sits on the contour.
* **REFUTED: "`Npoly` Hurwitz-stable + max-modulus."**  `k=iu` does make `Npoly(iu)=u³+P0u²−P1u+2P2`
  a *real* cubic, and the Routh–Hurwitz step is a two-line `nlinarith` — but the sign conditions
  **fail**: `Npoly` has exactly **one** open-LHP root, purely imaginary at `k=−i t₀`
  (`t₀ ≈ 0.79→1.97`).  Phragmén–Lindelöf on `Dpoly/Npoly` is therefore inapplicable.
* **REFUTED: "modulus only", i.e. `‖Npoly‖ > ‖Dpoly‖e^{σ Im k}` on the open LHP.**  False, and it
  fails at exactly the same point (`‖Npoly(−it₀)‖ = 0`).  ⇒ **MA.14 is irreducibly topological**: it
  needs a zero *count*, never a pointwise bound.
* **COMPLETE route: homotopy in `η`** (count locally constant, `0` at small `η`).  Inputs 1/2 already
  PROVEN in-repo (dilute base case; real-axis `‖N‖²−‖D‖²=k⁶`), input 4 elementary; **input 3 derived
  this pass in closed form** — `G_baxter`'s `k⁰,k¹,k²` coefficients cancel identically (the `k²` one
  *via* `baxterP0P1P2_sum_zero`) and `c₃ = i(1+2η)/(1−η)²`, σ- and ρ-free, `≠0` on `η∈(0,1)`.
* **Blocker = machinery, not content.**  Mathlib has **neither Rouché nor Hurwitz** (verified).  So
  MA.14's designated retirement is the *abstraction*: a pure-math `Analysis/` axiom for **parametric
  Rouché / Hurwitz zero-count stability**, with MA.14 derived from it + inputs 1–4.  ⚠ Not added yet
  **by design** — an unconsumed axiom worsens the ledger, and the tempting "Krein canonical
  factorization" phrasing carries a winding-number-0 hypothesis that **cannot be discharged** here,
  i.e. it would be a *fake* retirement of the vacuous kind the 2026-07-17 audit flagged.

**[Historical, pre-split] `G_baxter_ne_zero_on_lower_core` (shrunk to a bounded core):**
`HardSphere/BaxterHermiteBiehler.lean`. **The one non-Mathlib-vocabulary MA axiom** — references the
*defined* `Npoly`/`Dpoly`/`G_baxter` (parametrised over all physical `η,σ,ρ`).  **NOT abstractable —
physics-contingent, not merely deferred** (user note 2026-07-18): the property is *equivalent* to the
PY-HS structure factor having **no spinodal** (plus the Baxter factorization being the canonical
Wiener–Hopf plus-factor).  A spinodal ⟺ `1−ρĈ(k₀)=0` for some *real* `k₀` ⟺ `Q̂(k₀)=1` on the real
axis (via `1−ρĈ=(1−Q̂(k))(1−Q̂(−k))`) ⟺ a Baxter pole *on* `{Im k=0}` — so `{Im k≤0}`-nonvanishing
already *contains* "no spinodal".  A general-coefficient `cubic−linear·e^{−ikσ}` modelling a
*spinodal-bearing* system therefore **violates** the statement; only for PY-HS (spinodal-free =
`BAXTER.16`) does it hold.  So any `Analysis/` abstraction would have to **carry a no-spinodal /
structure-factor-positivity hypothesis** (`= BAXTER.16`) — retire-by-abstracting is off the table;
retire-by-proving (for *this* symbol, via `MA.11` + winding, subsuming `BAXTER.16`) stays open.
**Equivalence formalized** (step 1 of the decomposition): `qhat_complex_ne_one_iff_no_spinodal`
(`HardSphere/BaxterNoSpinodalEquiv.lean`, axiom-clean) — real-axis `Q̂ ≠ 1 ⟺ 1−ρĈ > 0`.
**Shrunk from the whole closed LHP to a bounded core:**
`G_baxter ≠ 0` only on `{Im k ≤ 0, k≠0, ‖Npoly(k)‖ ≤ ‖Dpoly(k)‖}`. The **outer region**
`‖Dpoly‖ < ‖Npoly‖` is now an axiom-clean THEOREM `G_baxter_ne_zero_of_norm_dominant` (a zero forces
`‖Npoly‖ = ‖Dpoly‖·e^{σ·Im k} ≤ ‖Dpoly‖`), and the core is **bounded** (`‖Npoly‖∼‖k‖³` overtakes
`‖Dpoly‖∼‖k‖`). The former whole-LHP `qhat_complex_ne_one_of_im_nonpos` is now a THEOREM (core axiom +
outer theorem + the `(-ik)³` bridge). **Safe:** true for all `η<1`; numerically confirmed incl. the
worst ray (`G_baxter(−bi)` is *real* and `<0` ∀`b>0`), the negative imaginary axis where the norm
bound fails and nonvanishing is a phase (Hermite–Biehler) fact. **HB looks provable** via `MA.11`
(done) + an explicit winding count on a lower semicircle (needs the real-axis case `BAXTER.16`), or
classical interlacing. **Processing (retire-by-proving only — abstraction ruled out above):** prove
the core for the PY-HS symbol via the 3-step decomposition — (1) the no-spinodal equivalence
(`qhat_complex_ne_one_iff_no_spinodal`, ✓ done); (2) **prove PY-HS has no spinodal** (`BAXTER.16`,
`1−ρĈ>0 ∀k` — research-scale, elementary routes fail); (3) the open-LHP/winding exclusion (argument
principle, given (2) as the real-axis boundary input); then assemble.

## The axioms — exterior OZ regularity (2 = 7a + 7b, added 2026-07-18, `HardSphere/`)

> **6h retired 2026-07-19** — `ozExterior_triple_shell_sin_integrable` is now a theorem (see
> "Axiom 8 — RETIRED" below), so this cluster is 7a + 7b only.

**`baxter_exterior_regularity` RETIRED as a physics axiom 2026-07-18 → now a THEOREM**
(`OzCoreClosure.lean`). Its 6th conjunct (an exterior "derivative bundle" for `ozBaxterFixedPt`) had
a **false** clause `∀ r ∈ Ici σ, HasDerivAt ozBaxterFixedPt (g' r) r`: `ozBaxterFixedPt` *jumps* at
the contact point σ (`-1` on the core, `baxterPsiOuter/·` on the exterior; contact value
`σ·η(5−2η)/(2(1−η)²) > 0 ≠ -σ`), so it is not differentiable there — formalized as
`ozBaxterFixedPt_deriv_bundle_endpoint_false` (`BaxterExteriorDerivBundle.lean`, axiom-clean). The
fix follows `radial_fourier_jump_asymptotic`'s own design: use a **smooth** `C¹` exterior
representative `g` (= `ozBaxterFixedPt` on `(σ,∞)`, linearly extended below σ) for the derivative
clause, keeping the jumping `ozBaxterFixedPt` as the transform argument `f`. The other five conjuncts
are theorems (`baxterPsi_ozstar` = OZ★, `baxterPsi_bounded_Ici`, exterior continuity, the two OZ
integrands). Net: retires the physics axiom `baxter_exterior_regularity`, at the cost of 2 true math
axioms below (the 2026-07-19 split of the former `ozExterior_smooth_deriv` into 7a
`ozExterior_smooth_repr` + 7b `ozExterior_deriv_integrable`, plus 6h; 6j was later derived from 6h).
**Of those, 7a, 7b and 6h have ALL since been RETIRED to theorems — the cluster costs no axioms.** Consumers
re-scoped: `oz_h_exterior_regularity`, `g0_HS_contact_value_of_oz_h_regularity`,
`g0_HS_contact_value` (`JumpAsymptotic.lean`).

### Axiom 7 — SPLIT (2026-07-19) into 7a + 7b; **BOTH since RETIRED to theorems** (`OzExteriorSmooth.lean`)
The former single `ozExterior_smooth_deriv` bundled two unrelated claims; split so each is separately
attackable ("split, don't abstract"). Both are pure real analysis about the constructed Volterra
renewal solution `baxterPsiOuter/·`; no physics. The jump is entirely in the `-1` core clamp of
`ozBaxterFixedPt`, not in `baxterPsiOuter/·`. Feed the (corrected) clauses 6a/6d via
`ozBaxterFixedPt_smooth_deriv_bundle`.

* **7a `ozExterior_smooth_repr` — ✓ RETIRED 2026-07-19 → THEOREM** (`#print axioms` = standard three).
  Proved via **(★DIFF)** (`OZFIX.25`): `ozExterior_smooth_repr_proved`, `BaxterRenewalDiff.lean`.
  **No linear extension was needed** — the renewal equation itself supplies the smooth representative
  `Ψ := baxterForcing + Φ`, which is differentiable on *all* of `ℝ` and equals `ψ` on `[σ,∞)`; then
  `g := Ψ/·` (dividing by `r ≥ σ > 0` is harmless).
* **7b `ozExterior_deriv_integrable`** — *integrability*, stated for **any** such representative:
  `IntegrableOn (g + r·g') (Ioi σ)`. Representative-independent, since `g + r·g' = (r·g)' = ψ'` on
  `(σ,∞)` for every valid `g`.  ✅ **RETIRED 2026-07-19 → theorem** (`ozExterior_deriv_integrable_proved`).
  ⚠ **Statement bug fixed 2026-07-19**: it carried only `hsigma`, i.e. asserted the bound for
  *arbitrary* `eta, rho`, where it is **FALSE** (without `heta_def` the renewal kernel mass scales in
  `ρ`, so `baxterPsiOuter` grows exponentially and is not `L¹`). The physical hypotheses its sole
  consumer already supplies were added, at no cost.  **Progress (`OZFIX.25`,
  `BaxterExteriorDerivIntegrable.lean`, axiom-clean, 0 `sorry`):** two of the three (★DIFF) summands
  are proved — the convolution term via Mathlib's Young `Integrable.integrable_convolution`
  (no hand-rolled Tonelli needed), and the `q0(0)·ψ̃` term; plus `forcingDeriv_eq_zero_of_gt`.
  Remaining: the routine bound for `baxterForcing'` on `Ioc σ (2σ)` (measurability is free — the
  function **is** `deriv (baxterForcing …)`), then assemble.

**KEY FINDING — both reduce to ONE shared lemma, so proving it retires BOTH outright.** Differentiating
the renewal `ψ(r) = baxterForcing(r) + ∫_σ^r q0(r−t)ψ(t)dt` (Leibniz: variable upper limit **and**
`r`-dependent integrand) gives
`ψ'(r) = baxterForcing'(r) + q0(0)·ψ(r) + ∫_σ^r q0'(r−t)·ψ(t)dt` **(★DIFF)**. Then **7a** follows (RHS
continuous ⇒ `ψ` is `C¹` on `[σ,∞)` ⇒ so is `ψ/·`; extend linearly), and **7b** follows summand-wise:
`baxterForcing'` is compactly supported (`baxterForcing = 0` for `r ≥ 2σ`), `q0(0)·ψ` is `L¹` because
**`IntegrableOn ψ (Ioi σ)` is ALREADY PROVEN** (`baxterPsiOuter_integrableOn`, from MA.13's
strengthened conclusion), and `q0' ⋆ ψ` is `L¹` by Young (compactly-supported bounded `q0'`). Tooling:
`hasDerivAt_integral_of_dominated_loc_of_lip` + `intervalIntegral.integral_hasDerivAt_right` — the
pattern already used for `hasDerivAt_tIntegral_shell` (`BaxterRenewal.lean`, OZFIX.16). **Do (★DIFF)
next; it is worth more than relocating either half.**

### Axiom 8 — `ozExterior_triple_shell_sin_integrable` (6h) — **RETIRED 2026-07-19 → THEOREM**

(`BaxterExteriorConvIntegrable.lean`.)  **Axiom DELETED; same name and signature, now a theorem.**
It was axiomatized on an *effort* argument ("formalizing the triple `lintegral` chain from Mathlib
primitives is substantial"), not a gap argument — which put it in tension with admissibility rule (c)
(anything derivable from existing Mathlib is split off as a genuine theorem).  It belonged to the
same category as MA.10/11/12, all of which were retired by proving; and its third ingredient
(exterior `L¹`) had just been supplied by MA.13's strengthened `IntegrableOn`.  Proving it — rather
than abstracting a side condition — was the right move, and it went through exactly as the old
docstring's own sketch predicted.

The proof is the sketch, formalized in four named steps (all in the same file):

| Step | Lemma | Content |
|---|---|---|
| shell slice | `volume_ozShell_slice_le` | `{a : \|a−t\| ≤ s ≤ a+t} ⊆ Icc \|s−t\| (s+t)`, of length `s+t−\|s−t\| = 2·min(s,t) ≤ 2t` (as `s−t ≤ \|s−t\|`). Axiom-clean (standard three). |
| `t` factor | `lintegral_shell_weight_c_HS_lt_top` | `∫_t 2t·\|t·c_HS t\| < ∞`: integrand `= 0` for `t ≥ σ` (`c_HS_outer`), `≤ 2σ·(σ·C)` on `(0,σ]` (`c_HS_bddOn`). |
| `s` factor | `r_mul_ozBaxterFixedPt_integrableOn_Ioi_zero` | `IntegrableOn (s·ozBFP s) (Ioi 0)`: core `(0,σ]` bounded on a finite-measure set (`ozBaxterFixedPt_bounded`) `∪` exterior `r_mul_ozBaxterFixedPt_integrableOn` — **MA.13's strengthened `IntegrableOn`**. |
| assembly | `lintegral_ozShellMajorant_lt_top` | `lintegral_prod_symm` puts the `a`-integral **innermost**, where it evaluates to `C(t,s)·volume(slice) ≤ C(t,s)·2t`; `lintegral_prod_mul` then splits the `(t,s)`-integral into the product of the two finite factors. |

The main theorem dominates the 6h integrand by `ozShellMajorant` (`sin` dropped via `|sin| ≤ 1`, the
`Icc`-indicator re-read as the shell region `ozShellRegion` constraining `a`) and applies
`lintegral_mono`.  Two small `def`s (`ozShellRegion`, `ozShellMajorant`) name the region and the
majorant.  **The `a`-innermost swap is the whole trick**: taken in the measure's own order the
`a`-integral is outermost over an unbounded axis and the estimate does not close.

`#print axioms ozExterior_triple_shell_sin_integrable` → standard three +
`volterra_renewal_tendsto_zero` (MA.13) + `baxter_no_open_lhp_pole_core` (MA.14), both **pre-existing
upstream** and reached only through the exterior-`L¹` ingredient — no new axiom, and no downstream
consumer's footprint grew (`ozExterior_conv_sin_integrable` has the identical list).

**Clause 6g (`ozBaxterExterior_shell_integrable`) was PROVED** (finite support + boundedness, same
file), not axiomatized.  **Clause 6j (`ozExterior_conv_sin_integrable`) is a THEOREM DERIVED from
6h** (2026-07-19): `r·(c_HS ⊛₃ ozBFP)(r)·sin(kr) = 2π·` the `(t,s)`-marginal of the 6h integrand, so
`Integrable.integral_prod_left` + Fubini (`integral_prod`) + the `radial3d_conv` unfold gives its
integrability from 6h.  So this cluster is now **zero** axioms — 6g, 6h, 6j are all theorems.

## The PHYSICS axiom (1, pre-placed 2026-07-19, `YukawaDCF/`) — mixture track only

### `pyhs_mixture_no_spinodal` (`HSMixture/MixtureNoSpinodal.lean`)
`det (Q0_mat_c_phys (I·k) sigma rho) ≠ 0` for real `k ≠ 0`, given `0 < σᵢ`, `0 < ρᵢ`,
`etaMix < 1`.  The **N-component** generalisation of the (now proven) scalar `pyhs_no_spinodal`:
on the Fourier axis the physical multicomponent Baxter matrix is nonsingular, i.e. the PY-HS
*mixture* structure factor never diverges (`S⁻¹ = Q̂†Q̂ ⪰ 0` is automatic from the factorization;
strict positive-definiteness ⟺ `det Q̂ ≠ 0`).

* **`k ≠ 0` required** — `q0_entry_c` divides by `s²`/`s³`, so `s = 0` is Lean junk (as in the
  scalar axiom).
* **Physical coefficients required — with free `Qp`/`Qpp` the statement is FALSE.**  Stated via
  `Q0_mat_c_phys` (`rhoGeoPhys`/`Q0phys`/`Qppphys`), *not* `Q0_mat_c` with free arguments; the
  counterexample is in `MatrixQ0.lean`'s M.3 docstring (`n=2`, equal diameters, `rho_geo≡0.1`,
  `Qpp≡0`, `Qp≈−13.59` ⇒ `det = 0` with all hypotheses holding).
* **Numerics (2026-07-19):** `det` computed two independent ways (direct `n×n` vs. rank-2
  `det(I₂−M)`) agree to `2·10⁻¹⁵` over 300 mixtures × 4 `k`, `N=1..4`; 800 random mixtures
  (`N=2,3`, `η≤0.55`, ratio ≤6.7) give `min_k|det| ≥ 0.517`; a harsher 250-trial run
  (`η∈[0.40,0.62]`, ratio ≤20, `N≤4`) gives `≥ 0.375`.  Never approaches 0.
* **Not provable by the scalar route.**  The scalar proof clears the poles with `k³`, leaving a
  *single* exponential, so `|e^{−ikσ}|=1` yields `‖N‖²−‖D‖²=k⁶`.  For `N` species the determinant
  carries ~`(N²+3N)/2` exponentials, and both natural certificates fail: term-wise dominance over
  the marks `tᵢ=e^{−ikσᵢ}` is negative in 300/300 trials for `N≥2` even at size ratio ≈1.00
  (splitting a species into two identical halves leaves `det` fixed but flips the margin ⇒ an
  artifact of discarding phase), and `ρ(M)<1` fails even at `N=1` (77%) since `M` has `k→0` poles
  while `det` stays bounded.  A proof needs a phase/winding argument — same difficulty class as
  MA.14.
* **No consumer yet** (pre-placed, like MA.8).  ✅ **The `n = 1` bridge is DONE 2026-07-19**
  (`HSMixture/MixtureNoSpinodalN1.lean`): `pyhs_mixture_no_spinodal_n1` restates the axiom at `Fin 1`
  and proves it **without** the axiom, from the scalar `pyhs_no_spinodal`; `#print axioms` =
  **standard three only**.  So on the one-component slice the axiom is *redundant*, not merely
  consistent.  This matters because a consumer-less axiom has no downstream use that could expose a
  mis-statement — and four axioms in this project were false *as stated*, each caught only by a proof
  attempt.  The bridge is the one mechanical check such an axiom admits; it found **no** statement
  bug.  Chain: `etaMix_n1` (yields exactly the scalar `heta_def` coupling) → `Q0phys_n1`/`Qppphys_n1`
  (the Lebowitz mixture coefficients *are* `q_prime_py`/`q_doubleprime_py`, closing the loop on the
  latter's docstring, which derives it *from* the multicomponent formula) →
  `qhat_complex_eq_mixture_kernel` (the two Laplace kernels reassemble `Q̂`) → `Matrix.det_fin_one`.

## Retired — the last *single-component* physics axiom `pyhs_no_spinodal` (2026-07-19)

**`pyhs_no_spinodal` RETIRED (axiom DELETED) 2026-07-19 → theorem** (`BaxterNoSpinodalEquiv.lean`,
same name and signature).  The earlier "no elementary proof / no SOS certificate" assessment applied
to a *direct* attack on `1−ρĈ(k)`; the **Baxter `N/D` route sidesteps it entirely**.

Under the physical coupling `η = πρσ³/6` the PY coefficients collapse to `P0 = -6η/(σ(1-η))`,
`P1 = -18η²/(σ²(1-η)²)`, `P2 = 6η(1+2η)/(σ³(1-η)²)`, and the two combinations entering
`‖Npoly‖²−‖Dpoly‖²` on the real axis vanish **identically**:
`P0²+2P1 = 0` and `P1²-4P0P2-(P1+2P2σ)² = 0` (`baxterP_sq_collapse`, `BaxterPoles.lean`).
Since for real `k`, `Re N = -P0k²+2P2`, `Im N = k³+P1k`, `Re D = 2P2`, `Im D = (P1+2P2σ)k`,

  **`normSq (Npoly k) − normSq (Dpoly k) = k⁶ + (P0²+2P1)k⁴ + (P1²-4P0P2-(P1+2P2σ)²)k² = k⁶`**

(`Npoly_normSq_sub_Dpoly_normSq_real`).  Hence `‖Dpoly‖ < ‖Npoly‖` for real `k ≠ 0`
(`Dpoly_norm_lt_Npoly_norm_of_real`), so `G_baxter(k) ≠ 0` there (`G_baxter_ne_zero_of_real`: a zero
would force `‖Npoly‖ = ‖Dpoly‖`, as `‖e^{-ikσ}‖ = 1` on the real axis).  `Qhat_pole_iff_G_baxter_zero`
then gives `Q̂(k) ≠ 1`, and `qhat_complex_ne_one_iff_no_spinodal` converts that to positivity.
Needs only `0 < σ`, `η < 1`, `η = πρσ³/6` (`0 < η`, `0 < ρ` are kept for signature compatibility).

**`baxter_no_open_lhp_pole_core` (MA.14) is NOT affected** and stays a math axiom: it is the strict
**open-LHP** complement, which this does not imply — at `k = 0`, `Npoly(0) = 2P2 = Dpoly(0)`, so the
dominance degenerates off the real axis.

## Bounded Wiener–Hopf uniqueness — `oz_fixed_pt_unique` retired (axiom now MA.15 in `Analysis/`)

> *Header updated 2026-07-19*: this cluster's axiom was originally added in `HardSphere/`
> (2026-07-18) as the concrete `oz_linear_op_bounded_injective`; it has since been **abstracted and
> migrated to `Analysis/RadialWienerHopf.lean` as MA.15 `radialShell_bounded_injective`** (Axiom 10
> below), and the concrete statement is now a **theorem**. This section records the retirement; the
> axiom itself is counted once, under MA.15.

**`oz_fixed_pt_unique` RETIRED (axiom DELETED) 2026-07-18 → theorem `oz_fixed_pt_unique_thm`**
(`OzWienerHopfBounded.lean`).  `oz_h` was redefined via `Classical.choose` over the *existence Prop*
itself (`Classical.choice` only, no reference to any `oz_fixed_pt_*`); the existence (`hex`) and
uniqueness (`∃!`, `huniq`) are threaded through the `oz_h`/bridge/`oz_core_closure` chain and
supplied downstream from `oz_fixed_pt_exists`/`oz_fixed_pt_unique_thm`.  **Existence** is the
constructed `ozBaxterFixedPt`; **uniqueness** reduces, by
linearity of `oz_linear_op` on the exterior (`oz_linear_op_sub_of_continuousOn`), to injectivity of
`I − oz_linear_op` on bounded exterior-continuous functions vanishing on the core.  That injectivity
is `oz_linear_op_bounded_injective` — since 2026-07-19 a **theorem**, instantiating the abstract
math axiom `radialShell_bounded_injective` (`MA.15`, Axiom 10 below); its coercivity hypothesis is **proved**
from `pyhs_no_spinodal` (`one_sub_rho_radial_fourier_c_HS_coercive`, `OzSymbolCoercive.lean` —
sign-argument near `0`, continuity+compactness middle, `Ĉ = O(1/k²)` tail), so **no new physics
axiom**.  After this, the OZ cluster's only physics axiom is `pyhs_no_spinodal`.

### Axiom 10 — `radialShell_bounded_injective` (MA.15, bounded/`L∞` Wiener–Hopf injectivity)
`Analysis/RadialWienerHopf.lean` — **abstracted and migrated out of `HardSphere/` 2026-07-19.**
Project-independent: an arbitrary kernel `C` supported in `[0,σ]` and arbitrary `ρ`, no FMSA
definitions. A radial shell operator with coercive symbol `1 − ρĈ ≥ ε > 0` is injective on bounded
functions continuous on `[σ,∞)` that vanish on the core.

**Why this is an axiom while its `L²` twin is a theorem.** `MA.12`
(`wienerHopf_positive_symbol_injective`) proves exactly this statement **on `L²`**, cheaply, by
Plancherel coercivity `⟪(I−K)u,u⟫ = ∫a(ξ)|û(ξ)|²dξ ≥ ε‖u‖²`. That argument does **not** survive the
passage to `L∞`: a bounded function need not be `L²`, and there is no Plancherel pairing to run. The
classical bounded route needs Wiener-algebra resolvent inversion — the same gap that makes `MA.13` an
axiom. The `L²`/`L∞` asymmetry is about the function space, not the physics.

**⚠ `hCsupp` is load-bearing** (caught while abstracting): the operator integrates `C` only over
`[0,σ]`, but the symbol `Ĉ` integrates over `(0,∞)`. Without the support hypothesis, coercivity could
be supplied entirely by mass of `C` beyond `σ` that the operator never sees — the statement would be
false. It is what forces symbol and operator to refer to the same kernel.

**Consumer.** Instantiated at `C := c_HS eta sigma` (support discharged by `c_HS_outer`;
`radial_fourier` and `oz_linear_op` unfold definitionally) to give the concrete
`oz_linear_op_bounded_injective`, **now a THEOREM** in `HardSphere/OzWienerHopfBounded.lean` — the
spectral input that retired the physics axiom `oz_fixed_pt_unique` to `oz_fixed_pt_unique_thm`.
Coercivity is discharged there from `pyhs_no_spinodal`, so **no physics enters `Analysis/`**.

## Proved — no axiom (`Analysis/`)

| Theorem(s) | File | Note |
|---|---|---|
| `jordan_lemma_arc_bound` | `JordanLemma.lean` | `‖∫_arc g·e^{iaz}‖ ≤ πM/a`. Mathlib has `Real.mul_le_sin` (docstringed "One half of Jordan's inequality") + the ML inequality. |
| `fourier_kernel_one_pole` | `MittagLeffler.lean` | `∫_{-R}^{R} e^{ixr}/(x−k₀)dx → 2πi·e^{ik₀r}`. Axiom 2 + Jordan (amplitude `1/(z−k₀)` decays — the case Jordan serves). |
| `mittagLeffler_expansion_of_bounded_on_circles` | `MittagLeffler.lean` | **Axiom retired 2026-07-16**: derived from Axiom 1 (~430 lines) — finite residue-sum on `f(w)/(w(w−z))`, holes `Fin κ ⊕ Bool`, then the ML inequality kills the circle integral. Answers "combine Axioms 1+3?" — it *was* a consequence of Axiom 1. Bug 2. |
| `circleAverage_log_norm_le_of_finite_zeros` | `JensenCounting.lean` | **Axiom retired 2026-07-15**: ~90 lines from Mathlib's `MeromorphicOn.circleAverage_log_norm`. Bug 1. |
| `vanDerCorput_first_derivative_test` | `VanDerCorput.lean` | **Axiom retired 2026-07-16**, restated at `C²` (~370 lines: IVT single-signedness, slope-limit `φ''`-sign, double IBP). Bug 3. |
| `fourier_of_odd`, `fourier_of_even` | `RadialFourierInversion.lean` | `𝓕` of odd = `−2i`·sine transform; of even = `2`·cosine transform. General, reusable. |
| `sine_inversion_of_odd`, `cosine_inversion_of_even` | `RadialFourierInversion.lean` | Classical half-line inversions. |
| `radial_inversion` | `RadialFourierInversion.lean` | **Never axiomatized** (MA.9's target): `f r = (1/(2π²r))∫₀^∞ k F(k) sin(kr) dk`, from Mathlib's `fourierInv_fourier_eq`. The `4π/k` prefactor cancels ⇒ radial inversion *is* the sine inversion + ~20 lines. Stated with `F`+`hF` as hypotheses (consumer passes `rfl`), so `Analysis/` stays physics-free. |
| `hasDerivAt_integral_Ioi`, `cosineTransform_of_hasDerivAt`, `radial_inversion_antideriv(_of_tail)` | `RadialFourierInversion.lean` | Antiderivative form, **fully closed** (no `hC` hypothesis): FTC for the tail integral + improper IBP against `sin(k·)/k` (`integral_Ioi_mul_deriv_eq_deriv_mul`) — cleaner than the anticipated Fubini swap. Needed because the pointwise form's `Integrable (𝓕 f)` fails at a contact jump (`k·F ~ 1/k`, confirmed numerically). Bug 4. |
| `volterra_existsUnique(_of_continuous)`, `volterra_convolution_existsUnique` | `Volterra.lean` | **Never axiomatized** (MA.10's target): Volterra 2nd kind `u = g + Vu` has a unique solution in `C(Icc a b, ℝ)`, unconditionally. Iterate bound `Mⁿ(r−a)ⁿ/n!` ⇒ some `T^[n]` is a contraction. |
| `circleIntegral_logDeriv_zpow_smul_eq`, `logDeriv_zpow_smul_eq` | `ArgumentPrinciple.lean` | **Never axiomatized** (MA.11's per-circle bridge): `∮_{C(k,r)} logDeriv((·−k)^n·g) = 2πi·n` for `g` analytic-nonzero. `#print axioms` = standard three. Split `logDeriv = n·(z−k)⁻¹ + logDeriv g` + `integral_sub_center_inv` + Cauchy–Goursat. |
| `argumentPrinciple_sum`, `argumentPrinciple_count` | `ArgumentPrinciple.lean` | MA.11 assembled: `∮_{C(c,R)} logDeriv f = 2πi·∑ nᵢ` (`Z − P` for simple zeros/poles). `#print axioms` = MA.1's `circleIntegral_eq_sum_of_small_circles` + standard three — **no new axiom**. |
| `wienerHopf_positive_symbol_injective`, `fourierMul_coercive`, `mulLp_coercive` | `WienerHopf.lean` | **Never axiomatized** (MA.12's target): half-line Wiener–Hopf operator with real symbol `a ≥ ε > 0` is injective on `L²(0,∞)`. Coercivity `⟪T_a u,u⟫ = ∫a|û|² ≥ ε‖u‖²` via Plancherel (`Lp.inner_fourier_eq`) — no winding number. The spec expected an axiom; the positive-symbol case is provable. |

## Statement bugs caught by proof attempts

Each was found *only* by attempting the proof — invisible to review, to `#print axioms`, to the
build, and (1, 2, 4) to the numerical pre-check.

1. **`circleAverage_log_norm_le_of_finite_zeros` (MA.5) — false.** Hypothesized finiteness of the
   *literal* zero set `{f = 0}` instead of the divisor support: under junk values a `sin` modified
   to equal `1` at every `nπ` is still `MeromorphicOn` with `divisor ≥ 0` and has an *empty* zero
   set, yet its circle average grows like `R`. Fixed: `(divisor f univ).support.Finite`.
2. **`mittagLeffler_expansion_of_bounded_on_circles` (MA.2) — false.** Concluded *ordered* partial
   sums; the classical theorem only controls **circle-grouped** sums (a pole pair `p, p+ε` with
   cancelling residues `±C/ε` between consecutive circles breaks any initial segment splitting it).
   Fixed: counting function `k` with `hk : n < k N ↔ ‖pₙ‖ < R N`, plus `hoff`.
3. **`vanDerCorput_first_derivative_test` (MA.4) — true but unprovable as stated.** Textbook
   `C¹`-with-monotone-`φ'` generality needs Riemann–Stieltjes IBP or the second mean value theorem;
   Mathlib has neither. Restated at `C²` (free — no consumers) and proved.
4. **`radial_inversion_antideriv` (MA.9) — vacuous.** `hC : ∀ k, cosineTransform Ψ k = F k/(4π)` is
   *unsatisfiable*: at `k = 0` junk `4π/0 = 0` forces `F 0 = 0`, but
   `cosineTransform Ψ 0 = ∫₀^∞ s²f(s)ds ≠ 0` (the relation holds only as a limit at 0). Fixed:
   `∀ k ∈ Ioi 0`, the domain the inversion integral actually uses. Contrast `radial_inversion`'s
   `hF : ∀ k`, which *is* satisfiable because `radial_fourier` carries the same junk (`rfl` works).

## Group MA — task records

Charter: survey missing-Mathlib machinery, prove what's provable, pre-place admissible axioms
(numerically pre-checked, narrowest form). Task table: `todo_lean.md` (Group MA).

| Task | Outcome |
|---|---|
| MA.1 | Founding pieces re-filed from the `OZFIX.10` effort: Axioms 1/2 + the axiom-free `jordan_lemma_arc_bound`. |
| MA.2 | Mittag-Leffler — **axiom retired, proved from Axiom 1**; bug 2. |
| MA.3 | `fourier_kernel_one_pole` — genuine theorem (Axiom 2 + Jordan). |
| MA.4 | Van der Corput — **axiom retired, proved** at `C²`; bug 3. |
| MA.5 | Jensen counting — **axiom retired, proved**; bug 1. Discharges `MZERO.11`'s `hJensen` (done 2026-07-16, `detC_jensen_log_bound`) ⇒ MZERO Route B's only open input is `DetBoundaryGrowth` (MZERO.10). |
| MA.6 | Relocated misfiled pure math `HardSphere/ → Analysis/` (`ResidueAtSimplePole`, `BanachPoleFamily`): `import Mathlib`-only, zero project deps; namespaces kept, 5 consumer imports updated. |
| MA.7 | Sokhotski–Plemelj — Axiom 3, pre-placed. |
| MA.8 | Homotopy-invariance Cauchy — Axiom 4, pre-placed. Open follow-ons: keyhole-homotopy derivations of Axioms 1/2 from it. |
| MA.9 | Radial Fourier inversion — **never axiomatized, proved**; bug 4. Fully closed (antiderivative form needs no `hC`). |
| MA.10 | Volterra 2nd kind existence/uniqueness — **never axiomatized, proved** (~130 lines). Discharges `OZFIX.15`(A)'s and `OZFIX.17`'s conditional hypotheses; route to `OZ.10`. |
| MA.11 | Argument principle / signed zero-pole count — **never axiomatized, proved** (~90 lines). Per-circle bridge `∮ logDeriv((·−k)^n·g) = 2πi·n` axiom-clean; assembled via MA.1 into `∮ logDeriv f = 2πi·∑ nᵢ`. Rouché not included (needs winding-number machinery Mathlib lacks). |
| MA.12 | **✓ DONE 2026-07-17 — PROVED, no new axiom** (`WienerHopf.lean`, ~110 lines, axiom-clean). Wiener–Hopf half-line **injectivity** for a **positive symbol**. The spec's "prove-first is hopeless" premise was **wrong for the positive-symbol case**: `⟪T_a u,u⟫ = ∫a|û|² ≥ ε‖u‖²` via Plancherel is elementary, no winding number. (The *full index theorem* would still need the missing Toeplitz/winding machinery — that part of the premise holds.) Caveats preserved: multiplier form (not convolution), L² (not bounded — bridge stays), positive-symbol only ⇒ **makes OZ.10 citable, not free**. Detailed record below. |
| MA.13 | **Paley–Wiener renewal decay — AXIOM (legitimate), PROCESSED 2026-07-18** (`Analysis/WienerRenewal.lean` + `HardSphere/BaxterRenewalDecay.lean`, Axiom 5 above). `volterra_renewal_tendsto_zero`: right-compactly-supported kernel + symbol nonvanishing on `{Re z ≥ 0}` ⇒ renewal solution `→ 0`. **Kept as an axiom** (recon confirmed no Mathlib Wiener-algebra/character-space and no elementary shortcut, unlike MA.12) but **verified + wired, not left bare**: (i) numerically verified true + non-vacuous for the dense regime (`ma13_verify.py`/`ma13_dense.py`); (ii) statement fixed (dropped the inert, `q0_poly`-unsatisfiable `t<0` support clause); (iii) wired to the concrete FMSA data — `baxterPsiOuter_tendsto_zero_of_symbol` (+ axiom-clean `baxterPsiOuter_continuousOn_Ici`), `#print axioms` = this axiom + std 3, discharging `BaxterExteriorDecayReduction.lean`'s `Tendsto baxterPsiOuter atTop 0` hypothesis (→ general-`η` `POLE.11` decay) modulo the symbol nonvanishing = MA.14's output. |
| MA.14 | **Hermite–Biehler root location — RETIRED & SPLIT into 2 PHYSICS axioms** (2026-07-18, Axiom 6 above). `G_baxter_ne_zero_on_lower_core` retired ⇒ (1) `pyhs_no_spinodal` (real-axis `1−ρĈ>0`, = OZ.20/BAXTER.16, `BaxterNoSpinodalEquiv.lean`) + (2) `baxter_no_open_lhp_pole_core` (strict open-LHP bounded core, `BaxterHermiteBiehler.lean`). MA.14's `G_baxter_ne_zero_of_im_nonpos`/`qhat_complex_ne_one_of_im_nonpos`/`baxter_pole_im_pos` now THEOREMS on the two (real axis via no-spinodal + equivalence `qhat_complex_ne_one_iff_no_spinodal`; strict-LHP via (2); norm-dominant covers `‖D‖<‖N‖`). Reclassified out of the math-MA registry (physics-contingent — spinodal-bearing systems violate it). No-spinodal itself has NO elementary/SOS proof (min→0 as η→1, no uniform gap; OZ.20); future route = η-parametric interval arithmetic (not pursued). `#print axioms` BAXTER.16 = `{std three, pyhs_no_spinodal}`. |
| MA.15 | Bounded (`L∞`) radial Wiener–Hopf injectivity — **axiom**, created 2026-07-19 by abstracting the former OZ.10 axiom `oz_linear_op_bounded_injective` and migrating it to `Analysis/RadialWienerHopf.lean`; that concrete result is now a **theorem** instantiating it at `C := c_HS`. The `L∞` twin of the *proved* MA.12 — the function space, not the physics, is why this one is assumed (Plancherel coercivity fails on `L∞`; needs Wiener-algebra inversion, as MA.13). ⚠ the kernel-support hypothesis is load-bearing (false without it). Consumer chain: OZ.10 ⇒ retired `oz_fixed_pt_unique`. |
| MA.16 | **✓ DONE 2026-07-19 — PROVED, no new axiom** (`Analysis/ConvolutionLeibniz.lean`, ~200 lines, axiom-clean: `#print axioms` = standard three for all three results). Leibniz rule with a variable upper limit AND an `r`-dependent integrand: `hasDerivAt_intervalIntegral_convolution` — `d/dr ∫_a^r K(r−t)·φ(t)dt = K 0 · φ r + ∫_a^r K'(r−t)·φ(t)dt`, with `K` differentiable only **a.e.** (`hK'`) plus `LipschitzOnWith C K` on the window `Icc (−δ) (r₀+δ−a)` of arguments that can occur. The spec's prediction held: the Lipschitz/dominated form is mandatory (`q0_poly`'s kink at `σ`) and no axiom is needed. **Two design choices that differ from the spec sketch, both deliberate:** (i) the recommended `r ↦ (r,r)` chain rule was NOT used — it needs *joint* differentiability of `(x,y) ↦ ∫_a^y K(x−t)φ`, which does not follow from the two partials without extra work; the **split at the base point** `∫_a^r = ∫_a^{r₀} + ∫_{r₀}^r` gives the same result from two independent single-variable facts. (ii) The moving-endpoint half avoids an ε-δ uniform-continuity argument entirely: subtracting the constant `K 0` leaves a remainder bounded by `C·M·|x−r₀|²` — the **same** Lipschitz hypothesis already needed for the parametric half — which is `o(|x−r₀|)` by a one-line `IsLittleO`. So the whole lemma runs on *one* regularity hypothesis. **Factored into two reusable halves**, not one monolith: `hasDerivAt_intervalIntegral_param` is stated with an **arbitrary** upper limit `b` (not `b = r₀`), so it is simultaneously OZFIX.25 step 2 (`baxterForcing' `, a fixed `[0,σ]` window) and step 3 — one lemma covers both. `hasDerivAt_intervalIntegral_moving_endpoint` supplies the boundary term. **Instantiation smoke-tested** against the real consumer before closing (`q0_poly` kernel + `q0PolyDeriv` + the `max`-clamped continuous representative of `baxterPsiOuter`): interfaces compose, leaving exactly the Lipschitz + `Measurable q0PolyDeriv` side conditions, which are consumer-side (OZFIX.25 step 3). ⚠ `Continuous φ` is a genuine constraint — `baxterPsiOuter` jumps at `σ` — so the consumer must pass `fun r => baxterPsiOuter (max r σ)` (the pattern already used in `BaxterOzStar.lean`) and transfer by `HasDerivAt.congr_of_eventuallyEq`; this is why `r₀ > σ` strictly. **Consumer:** `OZFIX.25` (★DIFF) ⇒ retires 7a `ozExterior_smooth_repr` + 7b `ozExterior_deriv_integrable`. |

**Lean notes worth reusing.** `Real.fourier_eq'` + `RCLike.inner_apply` unfolds `𝓕` on `ℝ`;
`integral_comp_neg_Ioi` + `integral_add_compl`/`compl_Iic` give the odd/even half-line split;
`𝓕⁻ f w = 𝓕 f (-w)`; `integral_comp_mul_left_Ioi` rescales `k = 2πv`; `integral_complex_ofReal`
moves the cast. `HasDerivAt.inv` is `𝕜 → 𝕜` only — use `HasDerivAt.fun_div` for `ℝ → ℂ`
reciprocals; `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` (interior-only hypotheses) avoids
endpoint FTC-1 pain. **Pitfall hit repeatedly:** `ring`/`field_simp` cannot normalize *inside*
`Complex.exp`/`Real.sin` arguments (they are atoms), and `field_simp` silently reorders
`cos (k*u)` to `cos (u*k)`, breaking the match — canonicalize exponents with an explicit
`rw [show … by push_cast; ring]` first, and `set` the final integral opaque before `field_simp`.
Applying a lemma with a higher-order argument (`jordan_lemma_arc_bound`'s `g`) via bare `apply`
can hit a `whnf` heartbeat timeout; supply the implicits explicitly with `refine`.

## MA.10 — Volterra integral equation of the second kind: existence & uniqueness

**Status: ✓ DONE 2026-07-17 — PROVED, never axiomatized, axiom-clean (~130 lines).**
**File:** `LeanCode/Analysis/Volterra.lean`.

**What was proved.** For continuous `K` on `[a,b]²` and continuous `g`, the Volterra equation of the
second kind `u(r) = g(r) + ∫ₐ^r K(r,t)·u(t) dt` has a **unique** solution in `C(Icc a b, ℝ)` —
unconditionally, with no smallness assumption on `K` and no bound on `b − a`. Landed as four
results: `volterra_iterate_bound` (the engine), `volterra_existsUnique` (explicit bound `M`),
`volterra_existsUnique_of_continuous` (**the consumer-facing form** — `M` comes from compactness of
`[a,b]²`, stated pointwise), `volterra_convolution_existsUnique` (renewal kernel `K(r,t) = q(r−t)`,
the shape OZ–Baxter produces).

**Route taken: iterate bound, not Bielecki.** The plan above offered the Bielecki weighted sup-norm
or the iterate bound as alternatives; the iterate bound won because `C(Icc a b, ℝ)`'s existing
metric instance is reused as-is (no new normed structure to build). The induction proves
`|Tⁿu(r) − Tⁿw(r)| ≤ Mⁿ(r−a)ⁿ/n! · dist u w` with `(r−a)ⁿ`, **not** `(b−a)ⁿ` — the sharper local
form is what makes the induction close, since the integral only accumulates up to `r`; the sup form
`(M(b−a))ⁿ/n!` is then a one-line weakening. `FloorSemiring.tendsto_pow_div_factorial_atTop` picks
`n` with the constant `< 1/2`, giving `ContractingWith (1/2) T^[n]`, and
`ContractingWith.isFixedPt_fixedPoint_iterate` + `fixedPoint_unique` finish. **No statement bug** —
the first stated form was the one proved (contrast MA.2/4/5/9).

**Genuinely absent from Mathlib, but not a formalization gap** (reconnaissance 2026-07-17): zero
occurrences of `Volterra`. It is also *not* in `docs/1000.yaml` — that list tracks *famous* theorems
(Picard–Lindelöf is on it, and formalized). `Analysis/ODE/PicardLindelof.lean` is ODE-only so it
cannot be reused directly, but it **is a worked in-tree precedent** for the identical `(M·L)ⁿ/n!`
iterate-contraction skeleton, which is precisely why this was provable rather than axiom-worthy.
Axiomatizing would also have been a **losing trade**: MA.10's consumers exist to *retire physics
axioms*, so spending a math axiom to retire a physics axiom is no net gain.

**Consumers — one lemma, two physics axioms.**
* `OZFIX.15` claim (A): construct `ψ` on `(σ,∞)` as the unique solution of the renewal equation
  `ψ(r) = ∫₀^σ q0(t)·ψ(r−t) dt` ⇒ `u := ψ ⋆ Q₊ ≡ 0` there **by construction**. Retires
  `oz_core_closure` (via `OZFIX.17`).
* `OZ.10` (`oz_fixed_pt_unique`): Baxter factorization gives `(I−K) = (I−K₊)(I−K₋)` with each
  one-sided factor **Volterra (spectral radius 0) ⇒ invertible with no compactness/Fredholm at all**
  ⇒ `(I−K)` invertible ⇒ existence + uniqueness. (`oz_linear_op`'s `K` *is* a non-compact half-line
  Wiener–Hopf operator, so Mathlib's compact Fredholm genuinely does not apply — but the route never
  needed it. Compactness was a red herring.)
Retiring OZ.10 in turn unblocks `OZ.3` (`oz_h_exterior_regularity`), whose only obstruction is that
`oz_h` is an opaque `Classical.choose` object: the Volterra solution is explicit.

**Discharging the conditional hypotheses is now follow-on work.** `OZFIX.15`(A) and `OZFIX.17` were
completed *conditionally*, carrying existence/uniqueness as an explicit hypothesis; MA.10 can now
discharge them by instantiating `volterra_convolution_existsUnique` at `q := q0_poly` on `[σ,R]`.
That instantiation is FMSA-specific and belongs to those tasks, not to `Analysis/`.

**Lean notes.** `open Nat` makes `φ` the totient notation — rename bound variables (`φ`→`u`).
`Function.IsFixedPt f x` unfolds to `f x = x`, so a hypothesis of the latter shape is *defeq* but
dot notation fails on it (`Eq.iterate` doesn't exist) — apply `Function.IsFixedPt.iterate` with the
function named explicitly. `intervalIntegral.integral_sub`'s two `IntervalIntegrable` side goals want
`Continuous.intervalIntegrable`; `ContinuousMap.dist_apply_le_dist` gives `dist (u r) (w r) ≤ dist u w`
where the goal wants `|u r − w r|` (`simpa [Real.dist_eq]`); and `← integral_sub` will not fire on
`(g r + A) − (g r + B)` until `add_sub_add_left_eq_sub` strips the common summand.
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` supplies continuity of
`r ↦ ∫ₐ^r …` in the *variable upper limit* — the one nontrivial ingredient for `volterraT`'s
well-definedness.

## MA.11 — Argument principle / signed zero-pole count: PROVED, no new axiom

**Status: ✓ DONE 2026-07-17 — DERIVED THEOREM, never axiomatized. File:**
`LeanCode/Analysis/ArgumentPrinciple.lean` (~90 code lines).

**What was proved.** For `F = logDeriv f` the contour integral counts the interior zeros/poles:
`∮_{C(c,R)} F = 2πi·∑ᵢ nᵢ` (`argumentPrinciple_count`), where each `nᵢ` is the order at the `i`-th
singularity — `Z − P` when the zeros/poles are simple (`nᵢ = ±1`). Exactly as the task forecast, it
is **MA.1 applied to `logDeriv f`**, and it introduces **no new axiom** (`#print axioms` =
`circleIntegral_eq_sum_of_small_circles` + the standard three).

**The genuinely new content — the per-circle bridge** `circleIntegral_logDeriv_zpow_smul_eq`
(**axiom-clean**, standard three only): `∮_{C(k,r)} logDeriv((·−k)ⁿ·g) = 2πi·n` for `g` analytic and
nonzero on the closed disk. Proof is the log-derivative split
`logDeriv((·−k)ⁿ·g) = n·(z−k)⁻¹ + logDeriv g` (`logDeriv_zpow_smul_eq`, from `logDeriv_mul` +
`logDeriv_fun_zpow`), then integrate: `∮ n·(z−k)⁻¹ = n·2πi` (`circleIntegral.integral_sub_center_inv`)
and `∮ logDeriv g = 0` by Cauchy–Goursat (`logDeriv g = deriv g / g` is analytic on the disk since
`g` is analytic and nonzero — `AnalyticAt.deriv` + `AnalyticAt.div`).

**Design decision (the one real judgment call).** Mathlib's `meromorphicOrderAt` factorization
`f =ᶠ[𝓝[≠] k] (·−k)ⁿ·g` is a **punctured-neighborhood-of-center** fact; it does *not* hold on the
outer contour `C(k,r)`, so it cannot be fed directly to the bridge. Rather than prove the
removable-singularity gluing that would extend `g`'s analyticity to the whole disk (out of scope for
an off-critical-path task), the local factorization is taken as an **explicit hypothesis** per
singularity — exactly the pattern `ContourDeformation.lean`'s
`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles` already uses (it takes each pole's numerator as
input). This is the honest general statement.

**Rouché NOT included.** The task mentioned "and the Rouché corollary", but Rouché is *not* "MA.1
applied to f'/f" — it needs winding-number / homotopy-invariance of the zero count (that a boundary
curve staying in a half-plane has winding 0), machinery Mathlib lacks. A separate task if wanted.

**Consumer status.** MA.11 is **necessary but not sufficient** for `POLE.10` (pole-family
exhaustion): it delivers the *count* once the contour is known to avoid all zeros and enclose exactly
the construction disks, but POLE.10 still needs `|G_baxter|>0` on a pole-avoiding contour (POLE.5
partial) and one-zero-per-disk (POLE.8/9) to supply the bridge's hypotheses. And POLE.10 itself only
serves `OZFIX.14`'s circular Fourier routes, so MA.11's real value is general/future (mixture MZERO
exact counting, `h_explicit = ψ/r`).

**Lean notes.** A bare `(π : ℂ)` in a statement auto-binds a *fresh implicit variable* `π` (not
`Real.pi`) — write `(Real.pi : ℂ)` explicitly, or `ring` fails to unify `↑Real.pi` with the phantom
`π`. `Metric.ne_of_mem_sphere hz hr.ne'` gives `z ≠ k` on `sphere k r` (`r>0`);
`DifferentiableAt.zpow` takes `f a ≠ 0 ∨ 0 ≤ n`; `ContinuousOn.inv₀` needs pointwise-nonzero on the
set; `circleIntegral.integral_congr` rewrites the integrand from an `EqOn … (sphere c R)`.

## MA.12 candidate — Wiener–Hopf / Krein half-line solvability (DETAILED SPEC for the MA Session)

> **✅ RESOLVED 2026-07-17 — PROVED, no axiom.** File `LeanCode/Analysis/WienerHopf.lean`
> (~110 lines, axiom-clean: `propext`/`Classical.choice`/`Quot.sound`). Main theorem
> `wienerHopf_positive_symbol_injective`. The open questions below were resolved as:
> **(Q1)** on `L²` (the bounded bridge stays separate); **(Q2)** index-free positive-symbol —
> chosen and, crucially, this is what makes it **provable** (see next paragraph); **(Q3)**
> injectivity/uniqueness only; **(Q4)** absence of WH/Toeplitz/index/winding **confirmed** (all
> unformalized in `docs/1000.yaml`); **(Q5)** the OZ→1-D-WH reduction is consumer-side (theorem
> stated in Fourier-**multiplier** form `T_a=𝓕⁻¹(a·𝓕)`); **(Q6)** general `a∈L∞` (real, bounded).
>
> **The brief's "prove-first is hopeless" was WRONG for the chosen (positive-symbol) case.** That is
> true for the *full Krein index theorem* (needs the missing winding/Toeplitz machinery), but the
> positive-symbol specialization has an elementary route the general theorem lacks — **coercivity via
> Plancherel**: for `u∈L²` supported on `[0,∞)`, `⟪T_a u,u⟫ = ∫ a(ξ)|û(ξ)|² dξ ≥ ε‖u‖²`
> (`Lp.inner_fourier_eq` + `L2.inner_def`), and if `T_a u=0` on `[0,∞)` the pairing vanishes ⇒ `u=0`.
> No winding number. Verified numerically first (`wh_coercivity_check.py`: the operator's lower bound
> equals the symbol infimum). **Scope simplification found:** the half-line aspect needs **no
> Hardy-space subspace** — it is a *support hypothesis* on `u`, since the ℝ-pairing collapses to the
> `[0,∞)`-pairing. **Caveat (spec §5) preserved:** on `L²`, not bounded; the `L²→bounded` passage
> re-introduces exterior decay (`baxter_exterior_regularity`), so MA.12 makes **OZ.10 citable, not
> free** — the decay bridge is separate follow-on work. The rest of this brief is kept for the record
> (disambiguation, candidate forms, citations) since it documents *why* this specific form was chosen.

**Purpose.** Supply the one theorem that would let `OZ.10` (`oz_fixed_pt_unique`, the *sole surviving*
OZ physics axiom after OZFIX.22) be **derived** rather than assumed. This is a scoping brief: the MA
Session must first **confirm exactly which theorem and on which space**, because "Krein / Wiener–Hopf"
is badly overloaded. **Do not implement before resolving the "Open questions" below.**

### 0. Disambiguation — "Krein's theorem" refers to several unrelated results
Only ONE is relevant. Rule out the others explicitly:
- ❌ Krein–Milman, Krein–Rutman, Krein–Smulian, Krein's condition (moments), Krein string,
  Markov–Krein — **none** of these.
- The relevant one is **Krein's theorem on Wiener–Hopf integral equations on a half-line** (a.k.a. the
  *symbol/index criterion* for half-line convolution operators).

Even within "Wiener–Hopf" there are **distinct objects** — separate what we HAVE from what we NEED:
| # | Object | Statement | Status in this project |
|---|--------|-----------|------------------------|
| A | WH **factorization of the symbol** | `𝒜(ξ)=𝒜₊(ξ)𝒜₋(ξ)`, `𝒜₊` analytic+nonzero in UHP, `𝒜₋` in LHP | ✅ **HAVE it, concretely** — Baxter `1−ρĈ=(1−Q̂(k))(1−Q̂(−k))` (`baxter_wiener_hopf_complex`), with `𝒜₊=1−Q̂` nonzero/analytic in the closed UHP (Baxter poles in LHP) |
| B | **spectral (positive) factorization** | `𝒜(ξ)>0 ⇒ 𝒜=\|𝒜₊\|²`, `𝒜₊` outer in `H²(UHP)` | ✅ essentially HAVE — `baxter_wiener_hopf_complex_real`: `1−ρĈ(ξ)=(1−ReQ̂)²+(ImQ̂)²=\|1−Q̂(ξ)\|²` |
| C | **Krein's operator SOLVABILITY / index theorem** | `𝒜(ξ)≠0 ∀ξ` & winding `ν=0` ⇒ `I−K` **invertible** on the chosen function space (unique solvability) | ❌ **MISSING — this is MA.12** |
| D | Gohberg–Krein systems / Toeplitz operator theory | same as C, general (systems, Banach-algebra symbols) | ❌ missing (more than we need) |

**Key point:** we already possess the *factorization* (A/B); the gap is the **operator consequence**
(C): "nonvanishing symbol + index 0 ⇒ `I−K` invertible ⇒ half-line equation uniquely solvable".

### 1. What `OZ.10` actually needs, precisely
`oz_fixed_pt_unique`: the OZ operator `T[h]=oz_forcing+oz_linear_op[h]` has a **unique** fixed point
among `h` that are **bounded** (`∃C,∀r,|h r|≤C`) and `ContinuousOn (Ici σ)`. Uniqueness ⟺ the
homogeneous `(I−ρK)d=0` has only `d=0` in that class, where `K=oz_linear_op` is the exterior OZ
convolution. Via `oddExt`/Baxter-`K` (`OZFIX.18/19`) this `K` is the **1-D half-line Wiener–Hopf
operator** with kernel `q0_poly` (support `[0,σ]`), symbol `𝒜=1−ρĈ`.

### 2. Candidate statements to choose among (with trade-offs)
1. **(i) Full Krein, `L^p(0,∞)`, with index.** Faithful/citable; needs winding-number/index machinery
   Mathlib **lacks** (MA.11 has the argument-principle count, not winding number) ⇒ heavy.
2. **(ii) Positive-symbol specialization (index-free).** For real `𝒜(ξ)>0` the winding number is
   trivially 0, so state: *`𝒜=1−k̂` real, `≥ε>0` ⇒ `I−K` invertible on `X`*. **Avoids the winding-number
   gap entirely** — recommended core.
3. **(iii) "Canonical factorization ⇒ inversion".** *Given `I−K=(I−K₊)(I−K₋)` with `K₊` causal, `K₋`
   anti-causal, one-sided ⇒ `I−K` invertible with `(I−K)⁻¹=(I−K₋)⁻¹(I−K₊)⁻¹`.* Closest to what we
   HAVE (explicit factors), but the one-sided factor inversion on the **half-line among bounded
   functions** is exactly the Route-3 wall (`OZFIX.23`): Volterra invertibility is free on **compacts**
   (`MA.10`) but half-line boundedness needs decay when `∫₀^σ|q0|≥1`.
4. **(iv) Narrowest: bounded injectivity.** *symbol `≠0`, index 0 ⇒ `ker(I−K)=0` on bounded `X`* — this
   is uniqueness only (all OZ.10's uniqueness half needs), but is close to restating the need (weakly
   citable).

### 3. THE decisive open questions for the MA Session
- **(Q1) Function space?** Krein is classically `L^p(0,∞)`, `1≤p<∞` — **NOT** `L^∞`/bounded, which is
  what `oz_fixed_pt_unique` uses. The `L^p → bounded` passage re-introduces the **exterior decay**
  (same content as `baxter_exterior_regularity`). So MA.12 on `L^p` does **not** by itself retire OZ.10;
  it needs a companion bounded/regularity bridge. Decide: axiomatize on `L^p` + prove the bridge, or
  axiomatize directly on the bounded/`BC` space (less standard, closer to restating OZ.10).
- **(Q2) General (with index) vs positive-symbol (index-free)?** Recommend index-free (ii): here
  `𝒜=|1−Q̂|²≥0`, so index 0 is FREE and Mathlib's missing winding-number theory is sidestepped.
- **(Q3) Existence too, or uniqueness only?** OZ.10 is `∃!`. `baxter_exterior_regularity` already gives
  existence (constructed `baxterPsi/·`); MA.12 could be scoped to **uniqueness/injectivity only**.
- **(Q4) Confirm Mathlib absence + `docs/1000.yaml`.** No Toeplitz/WH operators, no operator index, no
  winding number, no half-plane Hardy spaces in usable form; `K` is **not compact** so the compact-
  Fredholm alternative does not apply. Confirm the specific theorem is not tracked in `docs/1000.yaml`.
- **(Q5) The OZ→1-D-WH translation is application-side, not the axiom.** The axiom should be a clean
  general statement about half-line convolution operators; the reduction of `oz_linear_op` to that form
  (via `oddExt` + `baxterK`, `OZFIX.18/19`, and `Chat_complex_eq_radial_fourier`) is a *consumer-side*
  lemma, kept out of the axiom.
- **(Q6) Kernel class.** General `k∈L¹(ℝ)`, or specialize to **compact-support** kernels (our `q0`
  has support `[0,σ]` — a *band* WH operator)? Compact support may permit a cleaner statement and is all
  the project needs.

### 4. Citations (for the MA Session to verify absence/admissibility)
- N. Wiener, E. Hopf, *Über eine Klasse singulärer Integralgleichungen*, Sitzungsber. Preuss. Akad.
  Wiss. (1931) 696–706. — origin.
- **M.G. Krein, *Integral equations on a half-line with kernel depending upon the difference of the
  arguments*, Uspekhi Mat. Nauk 13:5 (1958) 3–120; Engl. AMS Transl. (2) 22 (1962) 163–288.** — the
  canonical solvability/index theorem (object C).
- I.C. Gohberg, M.G. Krein, *Systems of integral equations on a half line…*, Uspekhi Mat. Nauk 13:2
  (1958); AMS Transl. (2) 14 (1960) 217–287. — systems version (object D).
- A. Böttcher, B. Silbermann, *Analysis of Toeplitz Operators*, Springer (2006). — modern textbook.
- R.J. Baxter, *Ornstein–Zernike relation for a disordered fluid*, Aust. J. Phys. 21 (1968) 563. —
  the physics-specific factorization we already formalized.

### 5. Recommendation + honest caveat
**Recommend (ii)+(Q3): an index-free, uniqueness-scoped Krein statement** — "a half-line WH operator
`I−K`, `k∈L¹` (or compact-support), with real symbol `1−k̂(ξ) ≥ ε > 0`, is injective on `X`" — because
the index-0 hypothesis is free here (`|1−Q̂|²`) and existence is already covered by
`baxter_exterior_regularity`. **Caveat (from `OZFIX.23`):** whatever the form, the `L^p ↔ bounded`
bridge means MA.12 **upgrades OZ.10's pedigree (domain claim → citable classical theorem)** and lets it
be derived, but does **not** eliminate the exterior-decay content — that stays, whether inside MA.12's
space choice or in a companion bridge lemma. The MA Session should treat MA.12 as "make OZ.10 citable",
not "make OZ.10 free". Numerical/analytic backing for the wall: `verify_wienerhopf_wall.py`,
`proof_notes_ozfix.md` `OZFIX.23` (elementary reach is exactly `M(η)=η(4−η)/(1−η)²<1`, `η<(3−√7)/2`).
