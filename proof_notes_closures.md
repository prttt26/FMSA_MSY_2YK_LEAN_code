# Proof Notes: First-Order PY / HNCB Closures of the YK-Tail FMSA-DP Construction (Groups PYE / HNCB)

Proof records for the **closure identity** of the shipped YK-tail FMSA-DP construction: at the
zeroth pull-back rung it **is** the first-order PY DCF (**Group PYE**), and the full fixed-rate
first-order HNCB is **finite linear algebra** on top of it (**Group HNCB**). Both groups sit on
Groups **MRS** (finite closed-form DCF, `proof_notes_mixture_dcf.md`) and **Y1**
(`proof_notes_yukawa_wh.md`); the *exact* self-consistent HNCB-1 is the RDF, so it hits the
**MZERO/MML.5** wall (`proof_notes_mixture_rdf.md`) — recorded as a boundary, not a target.

**Source.** `numerical_notes/results/single_point/hncb_first_order.md`, `HNCB_FMSA_dp.py`
(`g_hs_ref='py'`, `pullback_passes` incl. `'solve'`), `compare_hncb_ntails.py`,
`probe_py_reproduction.py` (numerical oracle). Lean identifiers are content-descriptive (no task
IDs in source). Reuses **Group Y1** (`bMulti` linear in `K`, `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)`,
`Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`) and **Group MRS** (the (★) `Ĉ₁` form + finite closed form).

## Shared background — the first-order closure and the constructions

**The closure (`hncb_first_order.md` §1).** The HNCB outer closure
`c = exp(−βu + γ + B_HS) − 1 − γ` (Lado reference-HNC, **coupling-independent** HS bridge `B_HS`),
expanded in the Yukawa coupling `s` (u → s·u; at `s=0` the system is pure HS, so `g₀ = g_HS`,
`c₀(r>R) = 0`, `γ₀ = h_HS`), gives two algebraically equivalent first-order outer forms:

```
    c₁(r>R) = g_HS·(−βu) + h_HS·γ₁ = −βu + B·h₁,      B := h_HS/g_HS = 1 − 1/g_HS
```

Inside the core `h₁ = 0` at every order (exact hard-core condition), so `c₁(r<R)` is *solved for*.
**Setting `γ₁ = 0` collapses the outer to the PY-level `g_HS·(−βu)` — exactly PY's first-order
outer** (Group PYE). Keeping the bridge gives `−βu + B·h₁` (Group HNCB). `−βu` alone is bare
MSA/FMSA first order.

**Constructions (`HNCB_FMSA_dp.py`).** `g_HS` from one OZ inversion of the White-Bear FMT `c_HS`;
the outer closure is refit as `m_eff` **fixed-rate** effective Yukawa tails and run through the
FMSA-DP double-propagation assembly (which solves the inner core, Group MRS). A predictor–corrector
`pullback_passes` reintroduces the bridge: **pass 0** = γ₁≡0 = PY-level (Group PYE); **pass ≥1**
updates the outer to `−βu + B·h₁` via one linear OZ apply `H̃₁ = S₀·C̃₁·S₀ = F⁻¹·C̃₁·F⁻¹`;
**`'solve'`** reaches the fixed point in one linear solve (Group HNCB). Every rung stays a **finite
closed form**; the only reference input is `g_HS`; no fit to simulation data. (Iterate the
`−βu + B·h₁` form — `B<1`, contractive; the `g_HS·(−βu) + h_HS·γ₁` form has a `−h_HS·c₁` feedback,
`h_HS≳1`, Picard-unstable.)

---

## Group PYE — No-Pull-Back Construction ≡ First-Order PY

**Claim.** The `pullback_passes=0` construction (γ₁≡0, outer `g_HS·(−βu)`) **is** the first-order
PY DCF, and the *only* error versus true first-order PY is the finite-Yukawa-tail re-approximation
of the outer closure. Originally four tasks (**PYE.3** was the recommended entry point); **PYE.5**
(the `k→r` bridge) and **PYE.6** (the zeroth-order factor is PY's) were added 2026-08-03 when the
k-space-only scope and the "same `Q̂₀` on both sides" assumption were identified as the two gaps
between PYE.3/PYE.4 and the physical claim "the inner-core DCF is the first-order PY one".

| Task | Title | Status |
|------|-------|--------|
| PYE.1 | PY closure to O(coupling): outer `c₁ = g_HS·(−βu)` | ✓ DONE (2026-07-31, axiom-clean; re-measured 2026-08-02) |
| PYE.2 | DP first-order solution map is **linear** in the outer closure | ✓ DONE (2026-07-31, axiom-clean) |
| PYE.3 ⭐ | DCF error = DP-map applied to the finite-tail fit residual (*recommended first*) | ✓ DONE (2026-07-31, axiom-clean) — boundedness **proved, not assumed** |
| PYE.4 | Abstract equivalence: `DP-map[g_HS·(−βu)] = OZ+PY first order` | ◑ **substantially reduced (2026-08-03)** — the lift is built except for ONE named classical input: `TailFitWHConvergent` is now *derived* from `L¹` convergence + an `L¹`-bounded WH projection (`WHProjectionL1`, MA.13/MA.15-class, non-vacuity certified) |
| PYE.5 | **`k → r` bridge**: k-space identity ⇒ real-space DCF on the core `(0,R)` | ✓ DONE (2026-08-03, axiom-clean) |
| PYE.6 | the zeroth-order factor **is** the PY hard-sphere Baxter factor | ✓ DONE at `N = 1` (2026-08-03, from BAXTER.3 + MRS.0b); general `N` = **MRS.8**, open |
| PYE.7 | density of finite Yukawa-tail fits ⇒ the residual → 0 on the outer window | ✓ DONE (2026-08-03, axiom-clean) — via Weierstrass after `t = e^{−r}`, **not** Stone-Weierstrass; ⚠ was called "PYE.5" in the 08-02 note |

**Lean home.** All of Group PYE lives in **`LeanCode/Closures/ClosureExpansions.lean`**
(namespace `FMSA.FirstOrderClosure`), wired into `LeanCode.lean` after `ContactMatching`. Directory
choice: the DP map is Yukawa-tail data, so `Closures/DPClosureMap` (the closure algebra of PYE.1 alone would be
`Analysis/`-general, but it is not worth splitting a dozen lines). Reuses Y1.5's `bMulti`
(`SpectralAmplitude.lean`) and MRS.2/MRS.3's `star_of_first_order_oz` / `star_entry_eq`
(`MixtureRealSpace.lean`). **No new axiom.**

## Audit 2026-08-02 — re-measured, and one gap closed

**Measured, not inherited.** `#print axioms` on **all declarations** of the file (39 at the time of
this audit; 58 after the 2026-08-03 PYE.5/PYE.6 additions — re-measure, do not quote) returns
`[propext, Classical.choice, Quot.sound]` — **every one**. No `sorry` in the file. Full build green,
8718 jobs. So "PYE.1–3 ✓, no new axiom" survives contact with the current tree.

**⚠ Gap found and closed: the physical-form cluster had no non-vacuity certificate.**
`dp_sub_py_first_order_eq_conj_residual`, `dp_eq_py_first_order_of_exact_fit` and
`dp_tendsto_py_first_order` each carry MRS.2's **five simultaneous matrix equations**
(`hoz`, `hTS`, `hfact`, `hT0symm`, `hB1`). Five coupled equations are easy to state and easy to make
unsatisfiable; had they been, all three theorems would have been **vacuously true** and `#print
axioms`, the build and review would all have stayed silent — the exact failure mode of
`b4_origin_bc_abstract`, `b9_d_ij_nonzero_example` and GAP.8's `poly_coeff_from_laurent`. A witness
is now recorded as a Lean `example` in the file, deliberately **non-degenerate** (`Qm ≠ 1`,
`C₁^PY ≠ 0`, so it is not the trivial `Q̂₀ = I` dilute point where `Ĉ₀ = 0`):

```
Q = !![2] ,  T₀ = Q·Qᵀ = !![4] ,  S₀ = T₀⁻¹ = !![1/4] ,
B₁^PY = !![1] ,  C₁^PY = Q·B₁·Qᵀ = !![4] ,  H₁ = (Qᵀ)⁻¹·B₁·Q⁻¹ = !![1/4]
```

Worth noting *why* it is easy: **`hT0symm` is automatic whenever `Qp = Qm`**, since
`(Q·Qᵀ)ᵀ = Q·Qᵀ`. That is precisely what the physical case does *not* enjoy — there the two factors
are the genuinely distinct `Q̂₀(k)` and `Q̂₀(−k)`, which is why MRS.7 needed the KEY-1/KEY-2
Lebowitz relations and a five-exponential cancellation to get `hT0symm` at all. So the witness
certifies non-vacuity but must **not** be read as evidence that the cluster is easy to satisfy
physically.

**Also landed (2026-08-02):** `hncb_base_point_gamma_eq` + its non-vacuity `example` — see the
Group HNCB inventory below; they live in the PYE.1 block because that is where the HNCB expansion
sits.

**Two findings from the formalization.**

1. **The planned analytic input `wh_solution_operator_bounded` was NOT needed as an axiom.** At the
   finite-tail level the WH solution operator is bounded with an *explicit* constant (`whOperatorBound`
   below); boundedness only becomes real analysis in PYE.4's function-space lift. (Same shape as the
   Group-MA triage rule: an axiom justified by effort is a retirement target.)
2. **Linearity is exactly what the fixed-rate refit buys.** With the rates free the map is *not*
   linear — the rates sit in the denominators `s + z_mp` — so PYE.2/PYE.3 hold only for
   `tail_mode='linear'`. The numerics had forced fixed rates for an unrelated reason
   (`hncb_first_order.md` §4(b): degenerate rate pairs ⇒ `e^{+z̃R}` overflow in the inner core); the
   two justifications now agree.

---

### Task PYE.1 — PY closure to first order: outer `c₁ = g_HS·(−βu)`

**Statement.** The PY closure `c = (e^{−βu} − 1)·y` expanded to `O(coupling)` gives, in the outer
region `r > R`, `c₁ = y₀·(−βu) = g_HS·(−βu)` — because `y₀ = g_HS` (the cavity function at `s=0`
equals `g_HS`, since `c₀(r>R) = 0`, `g₀ = g_HS`).

**Route.** Elementary closure algebra: `e^{−βu} − 1 = −βu + O((βu)²)` times `y = y₀ + s·y₁ + …`,
first-order coefficient `y₀·(−βu)`. Needs the cavity function `y = g·e^{βu}` in Lean (or `y₀`
introduced directly as `g_HS`). (MSA analogue: outer `c₁ = −βu`, i.e. `y₀ ↦ 1`.)

**Depends on.** `g_HS` as an available object (HS reference; Group OZ / White-Bear).

**DONE (2026-07-31, axiom-clean), `LeanCode/Closures/ClosureExpansions.lean`.** The whole task is
one product rule at `s = 0`; the physics is in *which* factor survives.

- `mayerF beta u s = exp(−β s u) − 1`, with `mayerF_zero` (`f(0) = 0`, i.e. `c₀(r>R) = 0`) and
  `hasDerivAt_couplingExponent` / `hasDerivAt_mayerF` (`f′(0) = −βu`).
- **`py_first_order_outer`** — `HasDerivAt (fun s => mayerF beta u s * y s) (gHS * -(beta*u)) 0`
  given `HasDerivAt y y1 0` and `y 0 = gHS`. The `y₁` term drops **because `f(0) = 0`**: only the
  zeroth-order cavity value survives, which is the entire content of "`c₁ = y₀·(−βu)`".
- **`cavity_zero_coupling`** — from `y s = g s · e^{βsu}`, `y 0 = g 0 = g_HS`; `py_first_order_outer_cavity`
  is the assembled `c₁(r>R) = g_HS·(−βu)`.
- `msa_first_order_outer` — the `y₀ ↦ 1` case (bare `−βu`), i.e. the missing `g_HS` enhancement that
  makes FMSA undershoot by ~2.5× on (1,1) in `hncb_first_order.md` §3.

**Also landed here (the γ₁-collapse, the Group-PYE identification proper):**

- `hncbClosure beta u B gamma s = exp(−β s u + γ(s) + B_HS) − 1 − γ(s)`;
- `hncb_outer_zeroth_order_eq_zero` — the base point is consistent: with `exp(γ₀+B_HS) = 1 + γ₀`
  (i.e. `g_HS = 1 + h_HS` at `γ₀ = h_HS`) the zeroth-order outer HNCB DCF **vanishes**, matching PY's
  `mayerF_zero`;
- `hncb_first_order_outer` — first-order coefficient `g_HS·(−βu) + h_HS·γ₁`, `h_HS = g_HS − 1`;
- **`pass_zero_eq_py_first_order`** ⭐ — at `γ₁ ≡ 0` the HNCB and PY first-order outer coefficients are
  *the same object* `g_HS·(−βu)`. This is the closure-level half of "pass 0 **is** first-order PY";
  the solver-level half is PYE.3/PYE.4. (Cross-reference: this also lands the `exp`-form half of
  **HNCB.1** — see the note in Group HNCB below.)

**Status.** ✓ DONE (axiom-clean).

---

### Task PYE.2 — The DP first-order solution map is linear in the outer closure

**Statement.** The Wiener–Hopf / DP first-order solution map — outer closure `↦` first-order DCF,
subject to the core condition `h₁(r<R) = 0` — is **linear** in the outer closure.

**Route.** Corollary of Group Y1: `bMulti` is linear in `K`, and `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` is
linear in `B₁`; the composite (closure ↦ tails/`B₁` ↦ `Ĉ₁`) is linear. Extract/expose the
linearity already present in Y1 rather than re-deriving.

**Depends on.** Group Y1 (`bMulti` linearity, `Ĉ₁` assembly), Group MRS (the (★) `Ĉ₁` form).

**DONE (2026-07-31, axiom-clean), `LeanCode/Closures/ClosureExpansions.lean`.** The map is landed
stage by stage, each stage bundled as a genuine `→ₗ[ℂ]` so that PYE.3 is `map_sub`:

| stage | object | Lean |
|---|---|---|
| 1 — outer transform ([LN] Eq. 46, Y1.2) | `U₁(k) = K·e^{−ikR}/(ik+z)` | `outerTransform`, `outerTransform_add`, `outerTransform_smul` (Y1.2's `outerDCF_transform` is what identifies it with the half-line integral) |
| 2 — WH causal projection (Y1.3/Y1.5) | `K ↦ B₁` | `b1OfCoupling`, `bMulti_add_K`, `bMulti_smul_K`, **`b1OfCouplingLinear`** |
| 3 — the (★) assembly (MRS.3) | `B₁ ↦ Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` | **`starConjLinear`** |
| composite | `K ↦ Ĉ₁` | `dpDCF`, **`dpDCFLinear`**, and the fixed-rate tail family **`dpTailsLinear`** (+ `dpTailsLinear_apply`) |

⚠ **`dpTailsLinear` is linear in the *amplitudes* with the rates FROZEN.** Free rates enter the
denominators `s + z_mp`, so the free-rate refit is not a linear map at all — the same fixed-rate
discipline the numerics arrived at independently (`hncb_first_order.md` §4(b)).

**Status.** ✓ DONE (axiom-clean).

---

### Task PYE.3 — ⭐ DCF error equals the DP map applied to the finite-tail fit residual *(recommended first)*

**Statement.** With exact `g_HS`, the DCF error of the no-pull-back construction **equals** the DP
solution map applied to the finite-Yukawa-tail *fit residual* of the outer closure:

```
    DP[fitted YK tails] − DP[g_HS·(−βu)] = DP[fit residual],
    ‖error‖ ≤ ‖residual‖ · ‖WH-solution-operator‖.
```

The formal statement **"the only error source is the YK re-approximation"**: the DP construction is
exact; the sole approximation is representing the outer closure by finitely many Yukawa tails.

**Route.** Immediate from PYE.2 (linearity): `DP[A] − DP[B] = DP[A − B]`. New analytic input: a
**boundedness** bound `wh_solution_operator_bounded`. Reuses Y1 linearity + MRS.5 finite closed
form. Assumes `g_HS` exact (the numerical oracle's residual also carries a `g_HS`-inversion + grid
component, idealized away here — consistent with the hypothesis).

**Why recommended first.** Clean, self-contained, high-value: needs only PYE.2 + one boundedness
bound, and delivers the headline equivalence without PYE.4's function-space lift.

**Depends on.** PYE.2, Group MRS.5; new: `wh_solution_operator_bounded`.

**DONE (2026-07-31, axiom-clean), `LeanCode/Closures/ClosureExpansions.lean`.** Both halves:

- **the identity** — `dp_error_eq_dp_of_residual`: `DP[fit] − DP[exact] = DP[fit − exact]`, one
  `map_sub` on `dpTailsLinear` (PYE.2). This is the formal "the DP construction is exact; the sole
  approximation is representing the outer closure by finitely many Yukawa tails".
- **the bound** — `bMulti_entry_norm_le` (stage 2: `‖B₁(K)_{ij}‖ ≤ N²·Ab²·Kb/δ`) ∘
  `starConj_entry_norm_le` (stage 3: `‖(Q·X·Qᵀ)_{ij}‖ ≤ N²·Qb²·Xb`, via MRS.3's `star_entry_eq`)
  ⇒ `dpDCF_entry_norm_le` and, over a `T`-tail family, `dpTails_entry_norm_le` with the named
  constant

  ```
      whOperatorBound N T Qb Ab δ = T·N⁴·Qb²·Ab²/δ
  ```

  (`Qb` bounds the entries of `Q̂₀(−k)`, `Ab` those of `Q̂₀(z)⁻¹ = I + A`, and `δ ≤ ‖s + z_mp‖` is the
  distance from the evaluation point to the Yukawa poles).
- **the headline** — `dp_error_entry_norm_le`:
  `‖DCF error‖_∞ ≤ whOperatorBound · ‖fit residual‖_∞`.
- **the physical form** — `dp_sub_py_first_order_eq_conj_residual`: against the *exact* first-order
  PY DCF (characterized by MRS.2's `star_of_first_order_oz`), the error is the (★) assembly applied
  to the WH-datum residual, `DP[fit] − C₁^PY = Q̂₀(−k)·(B₁^fit − B₁^PY)·Q̂₀ᵀ(−k)`.

**⚠ `wh_solution_operator_bounded` did not need to be an axiom — it is a THEOREM.** The plan listed
it as a *new analytic input*; at the finite-tail level it is the elementary entrywise estimate above,
with an explicit constant (better content than an abstract "finite-dimensional ⇒ bounded", which
would also have sufficed). Boundedness is genuine analysis only in PYE.4's function-space lift. So
**Group PYE adds no axiom.**

**Idealization retained (as planned).** `g_HS` is assumed exact; the numerical oracle's residual
(`probe_py_reproduction.py`) additionally carries a `g_HS`-inversion and grid component.

**Status.** ✓ DONE (axiom-clean).

---

### Task PYE.4 — Abstract equivalence: `DP-map[g_HS·(−βu)] = OZ+PY first order`

**Statement.** The DP solution map at the PY-level outer `g_HS·(−βu)` equals the first-order term
of the OZ+PY solution: `DP-map[g_HS·(−βu)] = (OZ+PY)₁`.

**Route.** Needs the WH solution map lifted from finite-Yukawa-pole closures to a **function-space**
(`L¹`/`L²`) outer closure. The map is linear and bounded (PYE.2/PYE.3), so this is the natural
completion — a genuine analytic lift beyond the finite-pole DP form (infinite-tail / function-space,
not a finite closed form).

**Depends on.** PYE.1, PYE.2, PYE.3 (boundedness for the completion).

**PARTIAL (2026-07-31, axiom-clean), `LeanCode/Closures/ClosureExpansions.lean`.** The two halves
that do *not* need the lift are proved, and the lift is isolated as a hypothesis:

- **exact-fit half** — `dp_eq_py_first_order_of_exact_fit`: a fit that is exact *in WH data*
  (`B₁^fit = B₁^PY`) gives `DP-map[g_HS·(−βu)] = (OZ+PY)₁` **exactly**. (Immediate from
  `dp_sub_py_first_order_eq_conj_residual`.)
- **limit half** — `dpDCF_entry_tendsto` (the (★) assembly is entrywise continuous in its WH datum,
  being a finite sum of products) and `dp_tendsto_py_first_order`: if the finite-tail WH data
  converge to the PY one, the DP DCFs converge entrywise to `(OZ+PY)₁`. With PYE.3's
  `dp_error_entry_norm_le` supplying the *rate*, this is the abstract equivalence modulo the lift.
- **the remaining input, as a `Prop`** — `TailFitWHConvergent l B1fam B1py` (entrywise convergence
  along a filter). **Deliberately not an axiom** (the `MixRDFInnerCollapse` discipline,
  `MixtureInnerDCF.lean`): held as a hypothesis it is discharged only by an actual approximating
  family, whereas an axiom form would silently assert both that `B₁^PY` *exists* for the non-Yukawa
  outer closure `g_HS·(−βu)` and that it is the finite-pole limit.

**What is genuinely left.** Exactly that existence-plus-commutation statement: `g_HS·(−βu)` is not a
finite Yukawa sum, so its WH projection lives in an `L¹`/`L²` completion of the finite-pole class,
and one must show the projection of the limit is the limit of the projections. That is the real
analytic content of PYE.4 and it is untouched.

**Sub-piece `PYE.7` — DONE 2026-08-03** (⚠ renumbered; it was called "PYE.5" in the 08-02 note,
and `PYE.5` is now the landed k→r bridge). It makes PYE.3's residual "arbitrarily small on the
window". Its two shortfalls were then **both addressed the same day** in the PYE.4 work below:
the window-vs-half-line gap is closed outright (`exists_yukawa_tail_fit_halfLine` /
`exists_yukawa_tail_fit_L1`), and the residual-vs-WH-datum gap is reduced to the single hypothesis
`WHProjectionL1`.

**Status.** ◑ partial — exact-fit and limit halves DONE (axiom-clean); the function-space lift
remains and is the real content.

---

### Task PYE.4 (continued) — the function-space lift, built down to one classical input

**Work of 2026-08-03**, `LeanCode/Closures/ClosureExpansions.lean`, all axiom-clean.

**⚠ Finding 1 — the amplitude route is a DEAD END, and this is why the lift needs `L¹`.**  PYE.3
bounds the error by `whOperatorBound·‖K^fit − K^exact‖`, an *amplitude* distance.  That cannot be
lifted to a function-space statement, because the map `closure ↦ amplitudes` is **unbounded**:
near-degenerate rates represent a small function with huge cancelling amplitudes — the numerics
measured exactly this (`hncb_first_order.md` §4(b): `z̃ = [18.23, 18.35]`, `K̃ = [−441, +435]`).  The
lift must therefore bound the WH data **directly in the closure's `L¹` norm**, with no amplitudes
anywhere.  Everything below follows that route.

**What is now proved.**

- `exists_yukawa_tail_fit_halfLine` — **PYE.7's window gap, closed.**  A closure continuous on
  `[R,∞)` and *vanishing at infinity* is uniformly approximable **on the whole half-line** by a
  Yukawa-tail sum with integer rates `≥ 1`.  Same `t = e^{−r}` substitution as PYE.7, but on the
  **closed** interval `[0, e^{−R}]` — the half-line maps *into* it, so one Weierstrass application
  controls all of `[R,∞)`.  Vanishing at infinity is exactly continuity of the substituted function
  at `t = 0` with value `0`, which is also what lets the polynomial's constant term be dropped
  (leaving only strictly positive rates).
- `exists_yukawa_tail_fit_L1` — the **`L¹` version** for an exponentially decaying closure (the
  physical case): fit the *weighted* closure `e^{a(r−R)}Ψ(r)` uniformly on the half-line, then absorb
  the weight into the rates (`e^{−a(r−R)}e^{−kr}` is again a tail, of rate `k+a`).  The weighted
  uniform error integrates: `‖·‖₁ ≤ (εa)·(1/a) = ε`.  Also exports `Ψ ∈ L¹([R,∞))`.
  Supporting: `integral_exp_neg_shift` (`∫_R^∞ e^{−a(r−R)} = 1/a`), `integrableOn_exp_neg_shift`,
  `integrableOn_tailSum`.
- `norm_transform_le_L1` — the **transform stage**: `‖Û₁(k)‖ ≤ ‖Ψ‖_{L¹}`, *uniformly in `k`*.  This
  is the estimate that replaces PYE.3's amplitude bound.
- `WHProjectionL1` (hypothesis) + `tailFitWHConvergent_of_L1_tendsto` + `exists_tailFit_whConvergent`
  — **the reduction**: `TailFitWHConvergent`, previously an unexplained assumption of
  `dp_tendsto_py_first_order`, is now *derived* from `L¹` convergence of the closures plus one
  operator bound; and PYE.4b *supplies* the `L¹`-convergent family.  So the abstract equivalence
  rests on `WHProjectionL1` alone.

**⚠ Finding 2 — the norm is forced, and the "obvious" hypothesis would have been false.**  On the
Fourier side the causal projection is a Riesz-projection-type operator and is **not** sup-norm
bounded, so a "uniformly in `k`" boundedness hypothesis would be the wrong statement.  In *real
space* every stage is `L¹`-bounded — the causal restriction is multiplication by an indicator
(norm ≤ 1), the conjugation is convolution with `Q̂₀⁻¹`'s kernel — so `L¹` is the right norm, and it
is the one `WHProjectionL1` uses.

**⚠ Finding 3 — a vacuity trap, live for one iteration.**  `WHProjectionL1` was first stated
quantifying over **all** `Ψ : ℝ → ℝ`.  That silently forces `B1of ≡ 0`: for non-integrable `Ψ` the
junk value `∫|Ψ| = 0` makes the bound read `B1of Ψ = 0`, and `map_sub` on two non-integrable
functions with integrable difference then kills `B1of` on every integrable function as well — the
consumers would have been true only of the zero projection.  Restricting both fields to integrable
inputs fixes it, and a Lean `example` now certifies the class is inhabited **non-degenerately**
(`B1of Ψ = (∫_R^∞ Ψ)·I`, `C = 1`, nonzero on `Ψ = e^{−(r−R)}`).  Same failure family as the 08-02
audit's five-equation cluster.

**What is genuinely left.**  Exactly `WHProjectionL1`: that `Q̂₀⁻¹`'s real-space kernel is `L¹`, i.e.
**Wiener's `1/f` theorem for the causal convolution algebra** — the MA.13 (`wiener_causal_resolvent`)
/ MA.15 (`radialShell_bounded_injective`) family, kept as axioms in this project precisely because
Mathlib has no Wiener algebra.  It is held as a **hypothesis**: adding a second copy of an MA-class
axiom inside a physics file would be the wrong move.  ⇒ **PYE.4 stays ◑**, but the gap is now one
named classical theorem rather than an opaque convergence assumption.

---

### Task PYE.5 — the `k → r` bridge: from the k-space identity to the real-space inner core

**Statement.** PYE.3/PYE.4 are equalities of the **k-space matrices** `Ĉ₁`. The physical claim
"the inner-core DCF of the construction is the first-order PY one" is about `c₁(r)` on `0 < r < R`.
The bridge converts one into the other.

**DONE (2026-08-03, axiom-clean), `LeanCode/Closures/ClosureExpansions.lean`.**

- `radial_fourier_injective` — two real radial functions with the same radial (sine) transform agree
  at every `r > 0` where both satisfy the inversion hypotheses. Built on the project's **own**
  `radial_inversion` (`Analysis/RadialFourierInversion.lean`) — a *theorem*, not the MA.9 axiom once
  contemplated for it, so the bridge costs no axiom.
- `IsRadialEntry` + `radial_fourier_eq_of_entry_eq` — the k-space ⇄ real-space dictionary for one
  species pair, `Ĉ_{ij}(k) = a·𝓕_r[c_{ij}](k)` with `a = √(ρᵢρⱼ)` ([LN] Eq. 46's prefactor). Kept as
  an explicit hypothesis, because the PYE theorems characterize `Ĉ₁` *axiomatically* (through the
  OZ/WH equations) and never define it as a transform — so the convention is the consumer's.
- `inner_core_dcf_eq_of_khat_eq` — equal k-space matrices ⇒ **pointwise equality on `(0, R)`**.
- `inner_core_dcf_eq_of_exact_fit` — the capstone: MRS.2 equations at every real `k` + exact fit in
  WH data ⇒ `c₁^fit(r) = c₁^PY(r)` for all `0 < r < R`. Non-vacuity of the structural cluster
  (five MRS.2 equations *plus* the two dictionaries, for an arbitrary `c`, with `Qm ≠ 1`) is
  certified by a Lean `example`, per the 08-02 audit discipline.

**⚠ Two deliberate limitations, both real.**

1. **The open core `(0,R)`, not `[0,∞)`.** The DCF **jumps at contact** (`JumpAsymptotic.lean`) and
   `radial_inversion` needs continuity at the evaluation point — the documented trap that
   `radial_inversion_antideriv` exists for. Inside the core the FMSA-DP closed form is `C⁰` (only
   the `λ_ij` kink, IB.9/MRS.4), so the continuity hypotheses are discharge-able exactly where the
   theorem is stated.
2. **No real-space *error* bound.** Only the equal-transform/exact-fit statement crosses. Turning
   PYE.3's bound into a bound on `c₁(r)` needs `k·Ĉ₁(k) ∈ L¹`, and `whOperatorBound` is uniform in
   `k`: at large real `k` the pole distance `δ ~ ‖k‖` makes the entry bound `~1/k`, so `k·Ĉ₁(k)` is
   `O(1)` — not integrable. A real-space error bound needs a *weighted* k-space estimate; not in
   Group PYE.

**Status.** ✓ DONE (axiom-clean).

---

### Task PYE.6 — the zeroth-order factor **is** the PY hard-sphere Baxter factor

**Statement.** Every physical-form PYE theorem puts the *same* `Q̂₀` on both sides — the
construction's zeroth-order Baxter factor and PY's. That is not an assumption: it is a theorem
**already in the library**, and `N = 1` is now wired into Group PYE.

**DONE at `N = 1` (2026-08-03, axiom-clean), `FirstOrderClosures.lean`; general `N` = MRS.8, open.**

The library facts (all pre-existing, found 2026-08-03 — do not re-derive):

- **BAXTER.3 `baxter_wiener_hopf_complex`** (`HardSphere/BaxterWienerHopfComplex.lean`):
  `(1 − q̂₀(k))·(1 − q̂₀(−k)) = 1 − ρ·Ĉ_PY(k)`, where `q̂₀` is the transform of `q0_poly` — whose
  coefficients are the Wertheim-Thiele `q_prime_py` / `q_doubleprime_py` — and `Ĉ_PY` is the
  transform of `c_HS` (`py_a0/a1/a3`, `PYDCF.lean`). I.e. `T₀ = Q̂₀(k)Q̂₀ᵀ(−k) = I − Ĉ₀` with `Ĉ₀`
  the **actual PY hard-sphere DCF**: this is **MRS.8 at `N = 1`**.
- **`pyhs_no_spinodal`** (OZ.20, `BaxterNoSpinodalEquiv.lean`): `1 − ρĈ_PY(k) > 0` for real `k ≠ 0`
  — axiom-clean since 2026-07-19.
- **MRS.0b chain** (`HSMixture/MixtureNoSpinodalN1.lean`): `Q0phys_n1` / `Qppphys_n1` /
  `qhat_complex_eq_mixture_kernel` — the *physical mixture* Baxter coefficients collapse **exactly**
  to `q_prime_py` / `q_doubleprime_py` at one component, so the scalar `Q̂₀` above really is the
  mixture `Q̂₀` the DP construction uses.

Landed in the PYE file on top of them:

- `pyBaxterMat`, `pyT0Mat` — `Q̂₀ = 1 − q̂₀` and `T₀ = Q̂₀(k)Q̂₀ᵀ(−k)` as `1×1` matrices;
- `pyT0Mat_entry` — `T₀ = 1 − ρĈ_PY(k)` (BAXTER.3 in matrix form);
- `fin1_transpose_eq` — `hT0symm` is free at `N = 1`;
- `pyT0Mat_isUnit_det` — `hTS` from `pyhs_no_spinodal`;
- `dp_zeroth_order_is_py_n1` — the four zeroth-order facts bundled;
- **`dp_eq_py_first_order_n1`** — PYE.4's exact-fit statement with the *physical PY* zeroth order:
  `hfact`/`hT0symm`/`hTS` all discharged, so **only `hoz` (the first-order OZ equation) remains a
  physical input**. Non-vacuity certified for every `H₁` by a Lean `example` (`C₁ = T₀H₁T₀`,
  `B₁ = Q̂₀ᵀH₁Q̂₀`) — and unlike the 08-02 `Qp = Qm = !![2]` witness this one has the genuinely
  distinct `Q̂₀(k)`, `Q̂₀(−k)`.

**⚠ General `N` is exactly MRS.8 and is still open.** `Cmix0_factorization` (MRS.6) gives
`Q̂₀(k)Q̂₀ᵀ(−k) = I − Ĉ₀` by *definition* of `Ĉ₀`; identifying that `Ĉ₀` with the physical Lebowitz
mixture PY DCF is MRS.8, deferred. So the "same `Q̂₀` on both sides" caveat is **discharged at
`N = 1`, still a caveat for `N ≥ 2`**.

**Status.** ✓ `N = 1` DONE (axiom-clean); general `N` blocked on MRS.8 (off the critical path per
`proof_notes_mixture_dcf.md`).

---

### Task PYE.7 — finite Yukawa-tail fits are dense: the fit residual can be driven to zero

**Statement.** Every function continuous on the outer window `[R, R+L]` is uniformly approximable
there, to any accuracy `ε`, by a finite Yukawa-tail sum `Σ_{t<n} A_t e^{−z_t r}` with **strictly
positive, strictly increasing** rates. So PYE.3's residual — the quantity its bound multiplies — is
not bounded away from zero.

**DONE (2026-08-03, axiom-clean), `LeanCode/Closures/ClosureExpansions.lean`.**

- `exists_yukawa_tail_fit` — the density theorem;
- `exists_yukawa_tail_fit_pyOuter` — the same for the target the `pullback_passes = 0` construction
  actually fits, `r·c₁(r) = r·g_HS(r)·(−βu(r))` (PYE.1; the `r·` is [LN] Eq. 46's factor, the one
  that cancels the tail's `1/r`);
- `exp_pow_eq` — the `(e^x)^k = e^{kx}` step.

**⚠ Route note: the plan's Stone-Weierstrass sketch was NOT the cheapest route, and was not used.**
The substitution `t = e^{−r}` carries `[R, R+L]` homeomorphically onto `[e^{−(R+L)}, e^{−R}]` and
turns *polynomials in `t`* into *exponential sums* `Σ_k c_k e^{−k r}`. So Mathlib's classical
Weierstrass (`exists_polynomial_near_of_continuousOn`) already gives the density directly — no
subalgebra construction, no `SeparatesPoints`, and no `Algebra.adjoin`-to-span extraction (which is
where the Stone-Weierstrass route would have spent its effort: recovering an explicit *finite sum*
from an abstract adjoin membership). Only one extra step is needed: a `δ`-shift `k ↦ k + δ` to make
the `k = 0` term (a constant — not a legal Yukawa tail) strictly decaying, at cost
`≤ (Σ|c_k|)·δ·(R+L)`.

**Bonus, and it matches the numerics.** The rates produced are `z_k = k + δ`: **unit-spaced**, hence
automatically distinct and well separated — the `tail_mode='linear'` discipline that
`hncb_first_order.md` §4(b) arrived at for a completely different reason (a free nonlinear fit
collapses to near-degenerate rates with cancelling amplitudes; the `e^{+z̃R}` inner-core shift factors
then overflow). Third independent argument for fixed, separated rates (cf. PYE.2's linearity).

**⚠ What PYE.7 does NOT do — it does not close PYE.4.** Two gaps remain, both real:

1. ~~**window, not half-line.**~~ **CLOSED same day** by `exists_yukawa_tail_fit_halfLine` /
   `exists_yukawa_tail_fit_L1` (see the PYE.4 section): with the substituted interval taken *closed*
   at `t = 0`, one Weierstrass application controls the whole half-line, and the weighted version
   gives `L¹([R,∞))`.
2. **function residual, not WH datum.** PYE.3's bound consumes `‖K^fit − K^exact‖`, a distance
   between *coupling matrices*. Converting a function residual into that distance is exactly the
   function-space WH projection — **now reduced** (not closed) to the single hypothesis
   `WHProjectionL1`; see PYE.4.

**Status.** ✓ DONE (axiom-clean). PYE.4 remains ◑.

---

## Group HNCB — First-Order HNCB Bridge Pull-Back Construction

**Claim.** The whole **fixed-rate** first-order HNCB (`pullback_passes='solve'`) is closure
expansion + a finite `(I−L)⁻¹` solve + the DP map + a linear OZ apply — **finite linear algebra**,
the finite-tail truncation being the only approximation. The *exact* self-consistent HNCB-1 is the
RDF and is out of finite-closed-form scope (HNCB.4, record-only).

| Task | Title | Status |
|------|-------|--------|
| HNCB.1 | HNCB closure to O(coupling): outer `c₁ = −βu + B·h₁` | ✓ **DONE (2026-08-03, axiom-clean)** — pivot + `B<1` contraction proved |
| HNCB.2 | Fixed-rate pull-back map is **affine**: `K̃' = a + L·K̃` | ☐ not started |
| HNCB.3 | Fixed point `K̃* = (I−L)⁻¹a`; `(I−L)` invertible | ☐ not started |
| HNCB.4 | *(record only)* Exact HNCB-1 carries the RDF `h₁` ⇒ HS poles ⇒ not a finite closed form | ☐ boundary *(by design — not a target)* |

---

## Inventory — what Group HNCB actually has (audited 2026-08-02)

**Everything below is in `LeanCode/Closures/ClosureExpansions.lean` (ns `FMSA.FirstOrderClosure`).**
Results 1–4 landed as by-products of PYE.1 — proving PYE's γ₁-collapse *required* the HNCB expansion,
so the HNCB half arrived first; results 5–9 were added by this audit (2026-08-02/03). **No `sorry` in
the file, full build green, `#print axioms` = `[propext, Classical.choice, Quot.sound]` on every
one.**

| # | declaration | what it says |
|---|---|---|
| 1 | `hncbClosure` (def) | `c(s) = exp(−βsu + γ(s) + B_HS) − 1 − γ(s)` — Lado reference-HNC with a **coupling-independent** bridge |
| 2 | `hncb_outer_zeroth_order_eq_zero` | **the base point is consistent**: `c₀(r>R) = 0`, given `exp(γ₀+B) = 1+γ₀` |
| 3 | **`hncb_first_order_outer`** | **the group's one real theorem so far**: `c₁ = g_HS·(−βu) + (g_HS−1)·γ₁`, i.e. `g_HS·(−βu) + h_HS·γ₁`, given `exp(γ₀+B) = g_HS` |
| 4 | `pass_zero_eq_py_first_order` | at `γ₁ ≡ 0` the HNCB coefficient **equals** PY's `g_HS·(−βu)` (PYE's headline; half of it is HNCB content) |
| 5 | `hncb_base_point_gamma_eq` *(new)* | the two hypotheses together force `γ₀ = g_HS − 1 = h_HS` |
| 6 | `bridgeCoeff` (def) *(new)* | `B = h_HS/g_HS = 1 − 1/g_HS` |
| 7 | **`hncb_contractive_pivot`** *(new)* | **HNCB.1's target**: `c₁ = −βu + B·h₁` |
| 8 | `hncb_first_order_outer_contractive` *(new)* | the pivot at derivative level — what HNCB.2/3 iterate |
| 9 | `bridgeCoeff_mem_Ico` / `exp_form_feedback_ge_one` *(new)* | `B ∈ [0,1)` contracts; `h_HS ≥ 1` does not |

Supporting, shared with PY: `mayerF`, `mayerF_zero`, `hasDerivAt_couplingExponent`,
`hasDerivAt_mayerF`. The whole expansion is **one chain rule at `s = 0`** — the exponential gives
`g_HS·(−βu + γ₁)` and the explicit `−γ(s)` subtracts one `γ₁`.

### Two things the audit established that were not recorded

**(a) The two hypotheses are not independent — together they pin the base point.**
`hncb_outer_zeroth_order_eq_zero` asks for `exp(γ₀+B) = 1+γ₀`; `hncb_first_order_outer` asks for
`exp(γ₀+B) = g_HS`. Held together they **force `γ₀ = g_HS − 1 = h_HS`** — the physical statement
that at zero coupling the indirect correlation *is* `h_HS`, which is exactly why `h_HS` (`= g_HS−1`)
comes out as the `γ₁` coefficient in result 3. Nothing in the file says so, and the two can be
instantiated inconsistently as things stand. Verified, one line, ready to paste into the PYE.1
block (⚠ it belongs in that file — deliberately not landed here to avoid a merge collision with
work in progress):

```lean
/-- **HNCB base point.**  The zeroth-order consistency `exp(γ₀+B) = 1+γ₀` and the `g_HS`
identification `exp(γ₀+B) = g_HS` together force `γ₀ = h_HS = g_HS − 1` — why `h_HS` is the `γ₁`
coefficient of `hncb_first_order_outer`. -/
theorem hncb_base_point_gamma_eq {beta u B gHS : ℝ} (gamma : ℝ → ℝ)
    (hbase : Real.exp (gamma 0 + B) = 1 + gamma 0) (hgHS : Real.exp (gamma 0 + B) = gHS) :
    gamma 0 = gHS - 1 ∧ hncbClosure beta u B gamma 0 = 0 :=
  ⟨by rw [hgHS] at hbase; linarith, hncb_outer_zeroth_order_eq_zero gamma hbase⟩
```

**(b) The hypotheses are non-vacuous** — checked, because this project has shipped true-but-empty
statements before (`b4_origin_bc_abstract`, `b9_d_ij_nonzero_example`, GAP.8). Witness with
`g_HS ≠ 1` (so the theorem is not being read at the ideal-gas point): `γ ≡ 1`, `B = log 2 − 1`,
`g_HS = 2` satisfies `HasDerivAt γ 0 0`, `exp(γ₀+B) = 2 = g_HS` and `= 1 + γ₀`.

### ✅ The pivot to the contractive form — DONE (2026-08-03)

HNCB.1's stated target `c₁ = −βu + B·h₁` is now proved, axiom-clean, in the same file:

| declaration | content |
|---|---|
| `bridgeCoeff` (def) | `B = h_HS/g_HS = 1 − 1/g_HS` |
| **`hncb_contractive_pivot`** | the algebra: `c₁ = g_HS(−βu) + (g_HS−1)γ₁` ∧ `h₁ = γ₁ + c₁` ∧ `g_HS ≠ 0` ⇒ `c₁ = −βu + B·h₁` |
| **`hncb_first_order_outer_contractive`** | the same at derivative level: `HasDerivAt (hncbClosure …) (−βu + B·h₁) 0` — the form HNCB.2/3 iterate |
| `bridgeCoeff_mem_Ico` | `g_HS ≥ 1 ⇒ B ∈ [0,1)` — the Picard contraction |
| `exp_form_feedback_ge_one` | `g_HS ≥ 2 ⇒ h_HS ≥ 1` — the `exp` form's feedback, i.e. why it diverges |

**The two inputs it needed, and nothing else:** the OZ relation `h = γ + c` (as `γ₁ = h₁ − c₁`) and
`g_HS ≠ 0`. Both enter as explicit hypotheses.

⚠ **`h_HS = g_HS − 1` is not an extra assumption.** It is already the `γ₁` coefficient that
`hncb_first_order_outer` produces, and `1 + h_HS = g_HS` is exactly what collapses `c₁ + h_HS·c₁`
to `g_HS·c₁`. The base-point lemma above says the same thing from the other direction.

**The `B < 1` remark is now a theorem pair, not a remark** — and it is the whole reason the pivot
exists. Iterating the `exp` form directly is Picard-**unstable where the theory is actually used**:
its feedback coefficient on `c₁` is `h_HS = g_HS − 1`, and `g_HS` at contact exceeds 2 for any
moderately dense hard-sphere fluid. The contractive form stays in `[0,1)` for every `g_HS ≥ 1`:

| `g_HS` | 1.0 | 1.5 | 2.0 | 3.0 | 5.0 |
|---|---|---|---|---|---|
| `exp`-form feedback `h_HS` | 0.000 | 0.500 | **1.000** | **2.000** | **4.000** |
| contractive `B` | 0.000 | 0.333 | 0.500 | 0.667 | 0.800 |

**Cross-checked numerically** (independent of the Lean proof): over 10⁵ random
`(g_HS, βu, γ₁)` draws the two forms agree to `7.1e-15` — the pivot is an identity, not an
approximation, so no sign or factor slipped in.

### Scope note — HNCB.4 is not "unstarted work"

The table's `☐` on HNCB.4 reads like a to-do; it is not. HNCB.4 is a **boundary marker**: the exact
self-consistent HNCB-1 carries the RDF `h₁`, whose `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` has the `Q̂₀` inverses,
hence HS poles, hence no finite closed form. It sits on the far side of the project-wide DCF/RDF
dividing line (Group MRS vs. Groups MML/MZERO). Nothing is to be proved there.

---

### Task HNCB.1 — HNCB closure to first order: outer `c₁ = −βu + B·h₁`

**Statement.** The HNCB closure `c = exp(−βu + γ + B_HS) − 1 − γ` (Lado, coupling-independent
`B_HS`) expanded to `O(coupling)` gives the outer first-order form `c₁ = −βu + B·h₁` with
`B := h_HS/g_HS = 1 − 1/g_HS`, and inside the core `h₁ = 0`.

**Route.** Closure-expansion algebra at `s=0` (`g₀=g_HS`, `γ₀=h_HS`, `c₀(r>R)=0`). Land the
**contractive** `−βu + B·h₁` form (`B<1`); note as a remark that the equivalent
`g_HS·(−βu) + h_HS·γ₁` form carries a `−h_HS·c₁` feedback (`h_HS≳1`, Picard-unstable) — motivates
iterating the `B·h₁` form, not needed for the `'solve'` route.

**Depends on.** `g_HS`, `h_HS` (HS reference); the closure definition.

**See the Inventory section above** for the full audited list (now 9 HNCB declarations + 4 shared,
all axiom-clean), the base-point fact `γ₀ = h_HS`, and the contraction table.

**The pivot, in full** (`hncb_contractive_pivot`, and `hncb_first_order_outer_contractive` at
derivative level):

```
    c₁ = g_HS·(−βu) + h_HS·γ₁     [hncb_first_order_outer]
    γ₁ = h₁ − c₁                   ⇒  c₁(1 + h_HS) = g_HS·(−βu) + h_HS·h₁
    1 + h_HS = g_HS                ⇒  c₁ = −βu + B·h₁ ,  B = h_HS/g_HS = 1 − 1/g_HS
```

**Status.** ✓ **DONE (2026-08-03), axiom-clean.**  Both halves are in
`FirstOrderClosures.lean`: the `exp`-form (via PYE.1) and the contractive pivot with its contraction
bound — see the inventory above.

---

### Task HNCB.2 — The fixed-rate pull-back map is affine: `K̃' = a + L·K̃`

**Statement.** With the tail **rates fixed**, one predictor–corrector rung is affine on the finite
amplitude vector `K̃`:

```
    K̃' = a + L·K̃ ,   a = refit(−βu),   L·K̃ = refit( 2π√(ρᵢρⱼ)·r·B·h₁[K̃] ).
```

Each sub-step — b-tables → `C̃₁` → `h₁ = F⁻¹·C̃₁·F⁻¹` → `B·h₁` → fixed-rate linear refit — is linear
in `K̃`.

**Route.** Reuses Y1's `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` and the linear OZ apply; the fixed-rate refit
(rates frozen) is a linear least-squares projection onto the fixed Yukawa basis. `L` is built
column-by-column (`D = m_eff·#pairs`, small).

**Depends on.** HNCB.1 (the `−βu + B·h₁` outer), PYE.2 (DP linearity), Y1 (`Ĥ₁` apply).
**Status.** ☐ not started.

---

### Task HNCB.3 — Fixed point `K̃* = (I−L)⁻¹a`; `(I−L)` invertible

**Statement.** The affine map (HNCB.2) has the unique fixed point `K̃* = (I−L)⁻¹a`, provided the
concrete **finite matrix** `(I−L)` is invertible (or `‖L‖<1`, a contraction away from a spinodal).
So the whole fixed-rate first-order HNCB = closure expansion (HNCB.1) + finite `(I−L)⁻¹` + the DP
map + a linear OZ apply.

**Route.** `pullback_fixed_point_eq_inv_solve` (fixed point of an affine map) + `one_minus_L_invertible`
(concrete `Matrix.det (1 − L) ≠ 0`, or `‖L‖<1`). Finite-dimensional ⇒ very tractable; the `'solve'`
mode is exactly this.

**Depends on.** HNCB.2.
**Status.** ☐ not started.

---

### Task HNCB.4 — *(record only)* Exact HNCB-1 is not a finite closed form — the DCF/RDF boundary

**Statement.** The **exact** self-consistent first-order HNCB (`c₁ = −βu + B·h₁`, `h₁=0` inside,
one linear OZ fixed point — the infinite-pole limit the fixed-rate iteration converges to) carries
the **RDF** `h₁`, whose `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` HAS the `det Q̂₀` inverses ⇒ **HS poles** ⇒ **not
a finite closed form**. It hits the project-wide **DCF/RDF dividing line**: exact HNCB-1 runs into
the **MZERO / MML.5** wall (still load-bearing for the RDF, `proof_notes_mixture_rdf.md`).

**Disposition.** Record-only — do **not** attempt a finite-closed-form proof; it is the hard
boundary of the HNCB group. The finite results are HNCB.1–HNCB.3 (fixed-rate); the exact
self-consistent HNCB-1 is out of finite-closed-form scope by the same inverses that separate the
DCF (MRS) from the RDF (MML/MZERO).

**Depends on.** Conceptually on MML/MZERO (the RDF HS-pole series); nothing to prove here.
**Status.** ☐ record-only (boundary marker, not a proof target).
