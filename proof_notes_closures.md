# Proof Notes: First-Order PY / HNCB Closures of the YK-Tail FMSA-DP Construction (Groups PYE / HNCB / FOEQ / MSAFAM)

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
| PYE.6 | the zeroth-order factor **is** the PY hard-sphere Baxter factor | ✓ DONE at `N = 1` (2026-08-03, axiom-clean); **general `N` DONE (2026-08-19)** — `dp_zeroth_order_is_py_N` / `dp_eq_py_first_order_N`, carries `pyhs_mixture_no_spinodal` via `hTS` |
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

**✅ General `N` — DONE (2026-08-19), `Closures/DPClosureMap.lean`.**  `mixBaxterMat`/`mixT0Mat`
lift the `N = 1` wiring to the physical `N`-component Baxter matrix `Q̂₀(ik) = Q0_mat_c_phys(i·k)`:
`mixT0Mat_factorization` = `hfact` (`Cmix0_factorization`, MRS.6); `mixT0Mat_isSymm` = `hT0symm`
(momentum-space `Ĉ₀ᵀ = Ĉ₀` from MRS.7 `Cmix0_phys_swap`'s rank-2 KEY relations — **`#print axioms`
= std-3, axiom-clean**); `mixT0Mat_isUnit_det` = `hTS` (from `pyhs_mixture_no_spinodal`,
`det Q̂₀(ik) ≠ 0`).  Bundled as `dp_zeroth_order_is_py_N`, and `dp_eq_py_first_order_N` applies
MRS.2 (`dp_eq_py_first_order_of_exact_fit`) leaving only `hoz`.

**Status.** ✓ `N = 1` DONE (axiom-clean); ✅ **general `N` DONE** — `dp_zeroth_order_is_py_N` /
`dp_eq_py_first_order_N`, `#print axioms` = **std-3 + the single physics axiom
`pyhs_mixture_no_spinodal`** (via `hTS`; `hfact`/`hT0symm` are std-3).  The value-route
identification `Ĉ₀ = Cmix0 =` physical Lebowitz DCF is MRS.8 (`shellForcing_eq_cMixDCFN`) with
`Cmix0 = 𝓕(matDCFfull)` (`MixtureDCFAEInjective`).

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

---

# Group FOEQ — The Two Definitions of "First Order" Agree

**Opened 2026-08-10.** Source: paper §IV (`FMSA_dp_output/tex/fmsa_dp_theory.tex`), working notes
`FMSA_dp_output/md/theory_first_order_definitions.md`; numerical partner
`numerical_notes/theory/waisman_msa_closed_form.md` §"The Blum–Høye arbitration".

## The claim

Two definitions of "first order in the coupling" are in circulation. They are **not the same
statement**, and this project has always *claimed* the second while always *building* the first.

| | **(D1)** truncation of the hierarchy | **(D2)** derivative of the exact solution |
|---|---|---|
| construction | post a formal power series in the coupling, substitute into OZ+MSA, collect order by order | scale the tail `U ↦ sU`, solve **exact** MSA at each `s`, differentiate the nonlinear family at `s=0` |
| content, order `γ` | `H̃_γ(I−C̃₀) = (I+H̃₀)C̃_γ + ∑_{m=1}^{γ−1} H̃_m C̃_{γ−m}` | `c⁽ᵞ⁾ := (1/γ!)·d^γ/ds^γ[c_MSA(s·K)]│_{s=0}` |
| at `γ=1` | `H̃₁(I−C̃₀) = (I+H̃₀)C̃₁` — what the WH construction (Groups Y1/MRS) builds | what a reader means by "the first-order term of MSA" |
| precondition | **none** — each order is a linear problem, solvable whether or not the series converges anywhere | `s ↦ c_MSA(sK)` **`γ`-fold differentiable** at `s=0` |

⚠ **The precondition row is where this is easy to get backwards.** (D2) needs *differentiability*,
not convergence. An argument bounding the radius of convergence of the coupling series says nothing
about whether the derivative exists — and this project once reasoned in exactly that wrong direction
(the retracted `R_c ~ e^{−zR} ≈ 10⁻⁶` claim, which was an artifact of the singly-propagated
`(1−G²)/A²` split and not of perturbation theory). Even demanding *every* order asks only for
`C^∞`, which still does not imply analyticity.

### ⭐⭐ It holds at every order — ✅ FORMALIZED (2026-08-10)

FOEQ.6/7/8/9 all landed in `Closures/FirstOrderEquivalence.lean`, axiom-clean: `msaOuter_iteratedDeriv_terminates`
(FOEQ.6), `oz_taylor_coeff_eq_cauchy_convolution` (FOEQ.7 ⭐ — the Leibniz convolution, via Mathlib's
`iteratedDeriv_mul` on the constant OZ product), `oz_msa_taylor_eq_hierarchy` + the `γ=1` corollary
`oz_deriv_eq_firstOrderLine_of_taylor` (FOEQ.8), `cauchy_convolution_middle_empty_iff` (FOEQ.9).

The group was opened at `γ=1`; **nothing in the argument is first-order-specific**, and the
generalisation is not harder. Facts 1–3 below go through verbatim with the product rule replaced by
the general Leibniz rule, and `iteratedDeriv_mul` is already in Mathlib. Tasks **FOEQ.6–8** carry
it; they are *additive* to the landed `γ=1` rows FOEQ.1/FOEQ.3, which stay as the instances the
rest of the paper consumes.

⭐ **The payoff is a sharper statement of what first order actually is.** The convolution
`∑_{m=1}^{γ−1} H̃_m C̃_{γ−m}` is **empty at `γ=1` and nowhere else** (FOEQ.9). That emptiness — not
anything about the expansion — is what makes the solution map linear (PYE.2) and the residue sum
terminate. From `γ=2` the sum drags in `h⁽¹⁾`, which is built from `[Q̂₀]⁻¹` by construction, and
that is exactly §XII's obstruction. So:

> **The perturbation theory is equally well defined at every order; only its solvability in
> finitely many polynomial × exponential pieces is special to `γ=1`.**

Any reading in which higher orders are *ill-defined*, or in which first order is privileged by the
expansion itself rather than by what the expansion can be solved in, is a reading this group
excludes. Worth stating because the paper's §XII ("why second order forfeits the closed form")
invites precisely that misreading.

## Why a separate group

**Not MSAEXACT.** MSAEXACT.5 `fmsa_eq_firstOrder_msa` is the *formal linearisation* — expand the
self-consistency in `K`, recover FMSA-DP's HS-dressed amplitudes. It does not assert the derivative
exists; it assumes it. That assumption is FOEQ.5. Filing FOEQ under MSAEXACT would also gate
FOEQ.1–4 behind the degree-8 elimination (MSAEXACT.2) and the root-uniqueness theorem
(MSAEXACT.3), and **FOEQ.1–4 are not gated on anything** — they are statements about the OZ
hierarchy, provable with no Blum–Høye algebra at all. Only FOEQ.5 touches that track.

**Not PYE.** PYE identifies *which closure* the construction solves (first-order **PY**, not MSA, at
`pullback_passes=0`). FOEQ asks what "first order" means for any of them. PYE.1's
`py_first_order_outer` is a **`HasDerivAt`** statement, i.e. PYE already works in (D2)'s language —
which is why FOEQ.1 is small and why the closure layer is not the gap.

## Status (2026-08-10) — `LeanCode/Closures/FirstOrderEquivalence.lean`, full tree build 8760 jobs

| task | statement | status |
|---|---|---|
| FOEQ.1 | `msaOuter_hasDerivAt`, `msaOuter_eq_smul_deriv`, `mayerF_ne_msaOuter` | **✓ DONE** |
| FOEQ.2 | supports are `s`-free | ✓ discharged by construction (record-only) |
| FOEQ.3 ⭐ | `oz_deriv_eq_firstOrderLine` | **✓ DONE** |
| FOEQ.4 | `firstOrder_dcf_of_oz_deriv` (algebraic) **+** `firstOrder_khat_unique` / `firstOrder_dcf_unique_on_core` / **`firstOrder_dcf_unique_on_core_of_oz`** (WH-uniqueness) | **✓ DONE** — both halves; real-space core uniqueness via PYE.5. **2026-08-11: the left inverse is no longer assumed** — `_of_oz` derives it from the zeroth-order OZ `(1+H̃₀)(1−C̃₀)=1` (`Matrix.mul_eq_one_comm`), so it rests only on OZ + the `γ=1` line + injectivity |
| FOEQ.5 ⭐⭐ | existence of the derivative | ✅ **DONE at `N=1, γ=1` (2026-08-19)** — Jacobian ✓, IFT ✓, C¹ upgrade ✓ (2026-08-11) gave `msa_amplitude_differentiable_of_bh_shape` (from `F,P` `C¹` + vanishing-`G`-derivative + `F₀≠0` + PY base equation, no abstract `f₂`). **Item (i)'s residue (a), the literal BH transcription, is now discharged in MSAFAM.1–2**: `MSASolutionFamily.msa_amplitude_differentiableAt_yukawa` produces the derivative from `ξ∈(0,1)`, `z>0` alone. General `N` still gated (MSAFAM.7 ← MSAEMIX) |
| MSAEXACT.5 ⭐ | `firstOrder_amplitude_eq_hardSphere_dressed` | **✓ DONE** (same file) |

`#print axioms` = the standard three on **all** theorems, the FOEQ.4/5 additions included (verified
2026-08-10). Raw `grep -rn "^axiom "` reads prose false positives (docstring lines beginning
"axiom "); the real ledger is unchanged at **8 = 7 math + 1 physics**. ⚠ Quote the classified count,
never the raw one.

⚠ **Item (i), and the two gaps beyond it, now live in Group MSAFAM (opened 2026-08-19, below).**
FOEQ.5's residue is not the whole of Theorem I.1's hypothesis — it is one of three gaps (the
transcription), and the other two (`γ=1` → every `γ`; amplitude → *solution family*) were never
FOEQ tasks. MSAFAM carries all three because the third is gated on MSAEXACT.1, which FOEQ by
charter does not depend on. **FOEQ's own status is unchanged**: it stays ◑ until MSAFAM.2 lands,
at which point FOEQ.5's capstone becomes hypothesis-free at `γ = 1` and the group closes.

⚠ **The group is STILL NOT closed — but only by item (i).** FOEQ.1–4 are now fully done, and FOEQ.5's
two *provable* halves (the block-triangular Jacobian condition and the IFT application) landed
2026-08-10 as `bhJacobian_det` / `bhJacobianCLM_isInvertible` and
`exists_hasDerivAt_root_of_bivariate_ift` / `msa_amplitude_differentiable_of_bh_system`. What remains
is **item (i)**: that the abstract residual map `f` fed to the IFT engine *is* the Blum–Høye system,
with `∂₂f(0,p₀)` the block-triangular Jacobian — the faithful transcription of `F, A, q′, γ, Q̂` in
`(Dt, G)`. Until that is supplied (it is polynomials + `exp`, no analysis, but genuine algebra with
three known print errors in the source), the group's headline stays the conditional "(D1)=(D2) as
soon as the derivative exists", and §"What is *not* formalized" must keep saying so.

### ⚠ A Lean trap worth the line: do not state FOEQ.3 at `Matrix`

The natural statement is over `Matrix (Fin N) (Fin N) ℂ`, and it does not work. Matrices carry
several competing normed structures, all **scoped on purpose**; the `HasDerivAt` hypotheses in the
statement elaborate with the ambient (`Pi`-derived) topology while `HasDerivAt.mul` inside the proof
supplies `Matrix.linftyOp*`, and the two are not defeq — two pages of instance mismatch about
nothing, since no step of the argument is about matrices. **Stated over an abstract
`[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]` it goes through immediately**, and matrices are recovered by
`open scoped Matrix.Norms.Operator` (which turns on `linftyOpNormedRing` *and*
`linftyOpNormedAlgebra` together) plus instantiation. The note's original Lean route was right about
*which* instances exist and wrong about needing them.

Two smaller ones: a doc comment `/-- … -/` cannot attach to `variable` (use `/-! … -/`); and
`simpa [f]` will not unfold a partially-applied `f` in the goal — `rw` the function to its lambda
first, or `show`.

## The three structural facts (FOEQ.1–3) and the one analytic input (FOEQ.5)

**FOEQ.1 — the MSA exterior is linear in the coupling to begin with.** For `r > R_ij` the closure
reads `c_ij = −βs·U_ij`. Its `s`-derivative is `−βU_ij` at *every* `s`, second derivative zero. On
the exterior (D1) and (D2) are not merely equal, they are the same expression.

⚠ **`msa_first_order_outer` does not already say this.** It is
`HasDerivAt (fun s => mayerF β u s * 1) (1 * −(βu)) 0` — the `y₀ ↦ 1` case of the **Mayer** factor
`e^{−βsu}−1`. That agrees with MSA at first order but is *not* the MSA closure, and it carries an
honest `O(s²)` tail that MSA does not have. The distinction is the whole point of FOEQ.1: it is
where MSA is structurally simpler than PY/HNC, and for PY/HNC the exterior agreement is a theorem
with content (which `py_first_order_outer` supplies) rather than an identity.

**FOEQ.2 — the domains do not move with the coupling.** `h_ij(r) = −1` on `r < R_ij` is exact at
every `s`, and `R_ij` is core data, not tail data, so the two supports on which the WH split acts
are `s`-independent. **Discharged by construction** — every WH statement in the tree already has
`s`-free supports, so there is nothing to prove. Recorded because it is exactly the hypothesis a
*moving-boundary* perturbation problem violates, and there order-by-order solution and
differentiation do not commute. Cf. HNCB.4: a named boundary is not padding, an unnamed one is a
trap.

**FOEQ.3 ⭐ — OZ is quadratic, so differentiating it is exact.** Differentiate `(I+H̃)(I−C̃) = I` at
`s=0` with `H̃₀, C̃₀` the hard-sphere solution: the product rule returns the `γ=1` line term for
term, with no truncation and no neglected remainder. The hierarchy's first line is not merely
*consistent with* the derivative — it **is** the derivative equation.

*Lean route (checked against the pinned Mathlib, not guessed).* `HasDerivAt.mul` needs
`[NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]`, and `Matrix (Fin N) (Fin N) ℂ` gets both from
`Mathlib/Analysis/Matrix/Normed.lean`: **`open scoped Matrix.Norms.Operator`** turns on
`Matrix.linftyOpNormedRing` *and* `Matrix.linftyOpNormedAlgebra` (plus the additive/`NormedSpace`
prerequisites) in one line. `Matrix.Norms.Frobenius` is the alternative and carries the same pair.
⚠ These are **scoped, deliberately not global** — several natural matrix norms exist, so nothing
fires without the `open scoped`. Everything else in FOEQ.3 is `HasDerivAt.sub` / `.const`. No new
axiom, no analysis beyond the product rule. **This is the load-bearing task and it is available
now.**

**FOEQ.4 — the `γ=1` equation determines the answer. ✓ DONE 2026-08-10.** Two halves. The
*algebraic* half `firstOrder_dcf_of_oz_deriv` (given a left inverse of `1+H̃₀`, the `γ=1` line pins
`C̃₁` in `k` space) was already there. The **WH-uniqueness half** is now closed:
`firstOrder_khat_unique` gives `k`-space uniqueness (two solutions of the *same* `γ=1` line with a
common left inverse coincide — `Chat = Hinv·H̃₁(1−C̃₀)` both), and `firstOrder_dcf_unique_on_core`
transports it to *real space on the open core* `(0,R)` by composing with PYE.5's
`inner_core_dcf_eq_of_khat_eq` (transform injectivity + the `IsRadialEntry` dictionary). So (D1)'s
construction output *is* the OZ derivative `C̃₁`, as pair functions `c_ij(r)`, not merely in `k`.
⚠ The `γ=1` relation is taken as the hypothesis `hoz1`/`hoz2` — which is exactly what FOEQ.3
produces — so no re-differentiation at `Matrix` is needed, keeping this off the scoped-norm trap.
Uses FOEQ.2's `s`-free supports to invert on the *fixed* core.

⇒ FOEQ.1–4 give **(D1) = (D2) as soon as the derivative exists**, and that exhausts what algebra can
supply.

**FOEQ.5 ⭐⭐ — existence of the derivative.** That `s ↦ c_MSA(sK)` is differentiable at the
hard-sphere end point is a property of a solution never written down. Route: the implicit function
theorem on the Blum–Høye algebraic system, with the Jacobian nonsingular at the PY point. MSAEXACT.4
✓ already establishes that `K=0` *is* the PY point (the PY coefficients annihilate all three of
Waisman's equations), so the base point is in hand. Mathlib has the IFT (`ImplicitFunctionData`,
`HasStrictFDerivAt.implicitFunction`).

### ✅ The Jacobian condition is discharged — in closed form (2026-08-10)

Write the `N = 1`, `n`-tail Blum–Høye system unscaled, in the variables of
`waisman_msa_closed_form.md` §7g (`Dt_t = D_t e^{−z_t}`, `G_t = ĝ(z_t)e^{z_t}`):

    R1_u = Dt_u·F(z_u) − 2πK_u/z_u
    R2_u = 2π G_u·F(z_u) − [A + z_u q′ + Σ_t (z_u²z_t/(z_u+z_t))·γ_t·Dt_t]/z_u²

**At `K = 0` the base point has `Dt = 0`, and that kills every `G`-dependence at once**: `G` enters
`M` and `N` only through the factor `Dt_t` (§7g), so `M = N = 0`, hence `A = A⁰`, `q′ = q⁰′`, the
tail term of `Q̂` vanishes, and `F(z_u) = F₀(z_u) = 1 − ρ[φ₁(z_u)q⁰′ + φ₂(z_u)A⁰]` — the **hard
sphere** Baxter factor, independent of `G`. Therefore

    ∂R1_u/∂Dt_t = δ_ut F₀(z_u) + Dt_u·(∂F/∂Dt_t) = δ_ut F₀(z_u)
    ∂R1_u/∂G_t  = Dt_u·(∂F/∂G_t)                 = 0
    ∂R2_u/∂G_t  = 2π δ_ut F₀(z_u)

so `J` is **block lower-triangular** and

    ⭐  det J |_{K=0}  =  (2π)^n · ∏_u F₀(z_u)²

**Verified numerically to 6e-11 … 9e-10** against a central-difference Jacobian, over
`ξ ∈ {0.05, 0.20, 0.40, 0.49}` × `n ∈ {1, 2, 3}` (`z = [1.8]`, `[2.9637, 14.0167]`, `[1, 5, 14]`).

⇒ **`det J ≠ 0` ⟺ `F₀(z_u) ≠ 0` at every tail rate**, and that is not a new obligation: it is
`Q0_ne_zero_at_yukawa` in `HardSphere/BaxterFactor.lean`, **already proved**. The IFT's hypothesis
is therefore in hand for every `n` and every physical `ξ`, with no new analysis and no new axiom.

### ✅ The Jacobian condition and the IFT application are both FORMALIZED (2026-08-10)

Both are now in `Closures/FirstOrderEquivalence.lean`, `#print axioms` = the standard three.

* **The Jacobian, in Lean.** `bhJacobian F₀ c = !![F₀, 0; c, 2π F₀]` (the `N=1` single-tail block
  above), `bhJacobian_det : det = 2π F₀²` (`Matrix.det_fin_two_of`, the off-diagonal `c` drops out),
  `bhJacobian_nonsingular_iff : det ≠ 0 ↔ F₀ ≠ 0`. As the object the IFT actually consumes,
  `bhJacobianCLM F₀ c : (ℝ×ℝ) →L[ℝ] (ℝ×ℝ)` with `bhJacobianCLM_isInvertible : F₀ ≠ 0 → IsInvertible`
  (explicit inverse via `ContinuousLinearEquiv.equivOfInverse`). A worked `example` discharges the
  `F₀ ≠ 0` premise from **`FMSA.HardSphere.Q0_ne_zero_at_yukawa`** on the *actual* HS Baxter
  denominator — the IFT hypothesis is met, not assumed, for every physical `η ∈ (0,1)`, `z > 0`.
* **The IFT application (item ii), in Lean.** `exists_hasDerivAt_root_of_bivariate_ift`: a `C¹`
  bivariate residual system `f : ℝ → (ℝ×ℝ) → (ℝ×ℝ)` with `f 0 p₀ = 0` and `(∂₂f)(0,p₀)` invertible
  has a *differentiable* implicit root `ψ` (`ψ 0 = p₀`, `f K (ψ K) = 0` near 0, `HasDerivAt ψ ψ' 0`),
  via Mathlib's `hasStrictFDerivAt_implicitFunctionOfBivariate`. The capstone
  `msa_amplitude_differentiable_of_bh_system` composes it with `bhJacobianCLM_isInvertible`: if
  `∂₂f(0,p₀) = bhJacobianCLM F₀ c` and `F₀ ≠ 0`, the amplitude `K ↦ Dt(K)·e^z` is **differentiable at
  `K = 0`** — the derivative FOEQ.1–4 and MSAEXACT.5 take as a hypothesis, here *produced*.

⚠ It is **not** gated on MSAEXACT.2/3: the degree-8 elimination and root uniqueness are about *which*
root is physical, while the IFT only needs *a* root with nonsingular Jacobian, and `K = 0` supplies it
(MSAEXACT.4).

**Item (i)'s STRUCTURAL core is now proved (2026-08-11):** `bhResidualShape_hasFDerivAt`. The
block-triangular Jacobian is not an accident of the Blum–Høye algebra but a consequence of its
*shape*: for a residual map `f(Dt,G) = (Dt·F − 2πK/z, 2πG·F − P/z²)`, IF `F` and `P` have vanishing
`G`-directional derivative at the base point (`F'(0,1)=0`, `P'(0,1)=0` — precisely "`G` enters both
only through `Dt`"), then `∂₂f(0,G₀) = bhJacobianCLM F₀ c` with `c = 2π G₀ F'(1,0) − P'(1,0)`. Proved
via `HasFDerivAt.mul`/`.prodMk` and `clm_apply_of_snd_zero` (a linear functional killing the second
coordinate acts as `p.1·L(1,0)`), axiom-clean. So the ⭐ "`Dt=0` kills every `G`-dependence" insight
is now a theorem, and it *supplies the `hJac` input* of `msa_amplitude_differentiable_of_bh_system`.

**The C¹ upgrade (b) is now done (2026-08-11):** `msa_amplitude_differentiable_of_bh_shape`. Rather
than feed the curried bivariate IFT its four partial-derivative hypotheses, it uses the **uncurried
prod-domain IFT** (`exists_hasDerivAt_root_of_prodDomain_ift`, wrapping
`HasStrictFDerivAt.implicitFunctionOfProdDomain`), which consumes a *single* strict derivative — and a
`C¹` map supplies that. The coupling-scaled BH map `g(K,Dt,G) = (Dt·F − 2πK/z, 2π·G·F − P)` is `C¹`
(`fun_prop` from `ContDiff F`, `ContDiff P`), its second-factor partial `∂₂g(0,p₀) = g' ∘L inr` at the
PY point equals the block-triangular `bhResidualShape_hasFDerivAt` Jacobian (`HasFDerivAt.comp` with
`inr`, then `HasFDerivAt.unique`), invertible from `F₀≠0`; the IFT gives the differentiable root. So
the whole analytic half — strict differentiability, the eventual solve, continuity — is discharged.

**The residue of item (i) is therefore only (a):** the *literal* transcription of the BH `F, P` in
`(Dt, G)` (`waisman_msa_closed_form.md` §7f–§7g — polynomials and `exp`, three known print errors, the
`2×2` `N=1` system where every `e^{z}` cancels — **this is MSAFAM.1–2**) **plus** their `C¹`-ness and the two facts the capstone
takes as hypotheses: the vanishing-`G`-derivative property (`fderiv F/P (0,G₀) (0,1)=0`) and the PY
base equation `2π G₀ F₀ = P₀`. That is pure algebra/transcription, no analysis. General `N` gated on
MSAEMIX. Until (a) lands, `F, P` and those two facts are still the capstone's hypotheses.

## Numerical witnesses — and what they do *not* establish

| check | evaluates | agreement |
|---|---|---|
| central difference in `±s` of converged OZ+MSA | (D2), numerically | rel **5e-6**; estimator itself linear in `s` to 2e-5 between `s=1e-4` and `1e-5` |
| ⭐ **BH exact MSA, linearised in the amplitudes** | (D2), **analytically**, from a non-perturbative closed form | **6.4e-7 … 2.8e-5** over 25 states, `η ∈ [0.05,0.40]`, `z ∈ [1.8,28.75]`, on `∂_K(∂βp/∂ρ)` at `N=1` |
| `N=1` anchor vs Tang & Lu's single-component form | (D1), independent derivation | rel 7.7e-9 … 2.7e-8 |

⚠ **Both (D2) rows presuppose the derivative rather than establishing it.** A central difference
that converges, and a linearisation that matches, are consistent with differentiability; neither
proves it. They are why FOEQ.5 is believed, not why it would be closed.

⚠ **The BH row is not reproducible from the paper as printed** — three typographical errors in Blum
& Høye, *J. Stat. Phys.* **19**, 317 (1978): (36) drops a power of `z` versus (21) (and the correct
powers are **mixed**, `1/z` in `M` and `1/z²` in `N`, which is why a four-way scan could not reach
it); (35) inverts `z` versus (27); (29) omits the `e^{zσ_ij}` that its own contact-normalised
Eq. (3) forces. Each is fixed by the paper's internal consistency and confirmed dimensionally. Full
derivations in `waisman_msa_closed_form.md`.

## Constraints and boundaries

* **No new axiom** — verified. FOEQ.1–4 and FOEQ.6–9 are calculus and finite linear algebra; FOEQ.5
  is the IFT on an algebraic system over `ℝ` with `e^{−zσ}` a parameter. All landed theorems have
  `#print axioms` = the standard three. Needing an axiom means a route was abandoned somewhere.
* ⚠ **Do not mark the group closed on the algebraic tasks alone.** FOEQ.1–4 and FOEQ.6–9 give a
  *conditional* headline — "(D1)=(D2) as soon as the derivatives exist" — which is not the claim the
  paper makes. Until FOEQ.5's **item (i)** (the BH transcription) is discharged, the paper's
  §"What is *not* formalized" must keep saying that the analytic half is measured rather than proved.
* ✅ **The general-order statement is now formalized (2026-08-10).** What was previously unformalized
  here — the *Leibniz sum* rather than the bare product rule — is now `oz_taylor_coeff_eq_cauchy_convolution`
  (FOEQ.7) and `oz_msa_taylor_eq_hierarchy` (FOEQ.8, `∀ m ≥ 1`), so Theorem IV.1 is machine-checked at
  **every** order, not just `γ = 1`. The `γ = 1` corollary `oz_deriv_eq_firstOrderLine_of_taylor`
  reproduces FOEQ.3, confirming the general theorem subsumes the instance the rest of the paper uses.
  The one thing still unformalized is the FOEQ.5 hypothesis (item i), not the order.
* ⚠ **The numerical witnesses are `γ=1` only.** They say nothing about FOEQ.6–9 (which are now proved
  outright, so need no witness), and the paper keeps them in Part III (with the assembly checks)
  rather than in §IV, so that first-order measurements are not read as support for the derivative's
  *existence* (FOEQ.5), which they do not establish.
* **Scope boundary.** FOEQ says nothing about how *good* first order is. That is the truncation cost
  (paper §XI: 20–37 % pointwise at full coupling, 8.4/1.3/1.4 % in `ĉ_ij(0)`, 15–20 % near a
  spinodal) and it is a measurement, not a theorem target.

---

# Group MSAFAM — The MSA Solution Family in the Coupling: Constructed, and Smooth at Zero

**Opened 2026-08-19.** Source: paper Theorem `thm:firstorder`
(`FMSA_dp_output/tex/fmsa_dp_theory.tex:303`) and its disclosure bullet in §"What is *not*
formalized" (`:1600`). Numerical partner: `numerical_notes/theory/waisman_msa_closed_form.md`
§7f–§7g and `numerical_notes/results/msa_exact/coupling_series_radius.md`.

**Purpose, in one line: remove Theorem I.1's hypothesis. Not weaken it, not witness it.**

> **Status 2026-08-19 — MSAFAM.1–4 LANDED, axiom-clean, full build 8784 jobs.** Homes:
> `YukawaOZ/MSABlumHoyeSystem.lean` (MSAFAM.1–2, ns `FMSA.MSAExact`),
> `Closures/MSASolutionFamily.lean` (MSAFAM.3 + the `γ=1` payoff, ns `FMSA.MSASolutionFamily`),
> `Closures/FirstOrderEquivalence.lean` edited in place (MSAFAM.4). Gaps (A) transcription and
> (B) order are **closed**; FOEQ.5 is hypothesis-free at `N=1, γ=1`. **The group is NOT closed:**
> gap (C) — the pair family (MSAFAM.5, ← MSAEXACT.1) — and MSAFAM.6/.7 remain, so the paper's
> §"What is *not* formalized" Theorem-I.1 bullet **stays** (see the closing condition below).

## What the hypothesis *is*, exactly

The paper: *"Fix `γ ≥ 1` and let `τ ↦ (H̃(τ), C̃(τ))` solve OZ+MSA at coupling `τK`, `γ` times
differentiable at `τ = 0`."* In Lean that is not a paraphrase — it is literally the three
hypotheses of FOEQ.7 `oz_taylor_coeff_eq_cauchy_convolution`:

    (h1)  hH  : ContDiffAt ℝ γ H 0
    (h2)  hC  : ContDiffAt ℝ γ C 0
    (h3)  hOZ : ∀ s, (1 + H s) * (1 - C s) = 1

So the target is unambiguous: **construct `H C : ℝ → 𝔸` from the model data and prove (h1)–(h3).**
Anything less leaves the hypothesis standing; nothing more is needed to retire it.

⚠ **This is NOT what FOEQ.5 produces, and the difference is two thirds of the work.** FOEQ.5's
capstone `msa_amplitude_differentiable_of_bh_shape` returns `∃ D : ℝ → ℝ, D 0 = 0 ∧
DifferentiableAt ℝ D 0` — **one real unknown** of the Blum–Høye system, at **`γ = 1`**, with `F, P`
still hypotheses. The paper's hypothesis is about the **pair family** at **every `γ`**. Reading
FOEQ.5's residue as "the hypothesis, modulo a transcription" understates it by two gaps:

| gap | from | to | depth |
|---|---|---|---|
| **(A) transcription** | abstract `F, P` with four assumed properties | the concrete BH `F, P` of theory note §7g | algebra only, no analysis |
| **(B) order** | `DifferentiableAt … 0` (`γ = 1`) | `ContDiffAt ℝ γ … 0` for every `γ` | ⭐ **free — Mathlib has it** |
| **(C) family** | the amplitude `Dt(K)` | the pair `(H̃(τ), C̃(τ))` obeying OZ | the real depth; gated on **MSAEXACT.1** |

Gap (C) is why the group exists at all. An amplitude that moves differentiably is not a solution
family: nothing in FOEQ.5 says the numbers it produces *solve* OZ+MSA, and that step is exactly
MSAEXACT.1's factorization `Q̂(s)Q̂(−s) = 1 − ρĉ(s)` — whose full closure-recovery half is the
open analytic core of that group.

## Why a separate group

**Not FOEQ.10.** FOEQ's charter is explicit that it depends on nothing: *"Filing FOEQ under
MSAEXACT would gate FOEQ.1–4 behind the degree-8 elimination … and FOEQ.1–4 are not gated on
anything."* MSAFAM.5 **is** gated on MSAEXACT.1. Filing this under FOEQ would import that gate
into the one group whose value is that it has none — and would move FOEQ from "◑ one transcription
short" to "◑ blocked on a multi-file analytic core", which is a worse description of both.

**Not MSAEXACT.6.** MSAEXACT answers *what the exact solution is* — closed form, elimination,
which root is physical. MSAFAM answers *that a solution family exists and moves smoothly with the
coupling*. The closed form does not state that, and MSAEXACT.3's uniqueness does not give it: a
unique root at each `K` says nothing about regularity in `K`.

**The deliverable is a constructed object, not another conditional lemma** — and only a
construction can retire a hypothesis. That is the structural reason it is its own group rather than
a row appended to either neighbour.

⭐ **Closing condition, stated once so it cannot drift.** When MSAFAM.6 lands, the paper's
§"What is *not* formalized" loses its Theorem-I.1 bullet and the theorem becomes unconditional at
`N = 1`. Until then that bullet stays, **including** its "what is measured, in place of proof"
paragraph. Landing MSAFAM.1–4 alone does *not* license editing it — they close (A) and (B), and
the bullet's subject is the hypothesis as a whole.

## Tasks

| task | statement | depends on | status |
|---|---|---|---|
| MSAFAM.1 | `bhF`, `bhP : ℝ × ℝ → ℝ` — the *concrete* Blum–Høye residual data in `(Dt, G)` at `N = 1`, one tail, plus `ContDiff ℝ ∞` for both | theory note §7g | ✅ **2026-08-19** — `YukawaOZ/MSABlumHoyeSystem.lean`: `bhF`/`bhP` in the factored form `base + Dt·rest(G)` (validated == `_bh_pieces` for arbitrary `(Dt,G,w)`), `G0` the closed-form PY base point; `bhF_contDiff`/`bhP_contDiff` at `∞` |
| MSAFAM.2 ⭐ | the four properties FOEQ.5's capstone assumes, **proved for `bhF`/`bhP`**: vanishing `G`-derivative, `bhF (0,G₀) = 1 − ρQ̂₀(z)`, `F₀ ≠ 0` from `Q0_ne_zero_at_yukawa`, and the PY base equation `2π·G₀·F₀ = bhP (0,G₀)` | MSAFAM.1; MSAEXACT.4; an `N=1` HS identity | ✅ **2026-08-19** — `bhF_fderiv_snd`/`bhP_fderiv_snd` (vanishing `G`-deriv, via the `⭐ Dt=0` structural lemma `fderiv_fst_factor_snd_apply`), `bhF_base`, `bhF_base_ne_zero` (via base eqn + `bhP₀>0`), `bh_base_eq` (⭐ **rational identity in `w=e^{−z}`, `field_simp; ring`; no transcendental fact — only `Q0_ne_zero_at_yukawa` for the denominator**). Assembled: `MSASolutionFamily.msa_amplitude_differentiableAt_yukawa` — **closes gap (A); FOEQ.5 hypothesis-free at `γ=1`** |
| MSAFAM.3 ⭐ | `exists_contDiffAt_root_of_prodDomain_ift` — the `C^n` implicit function, replacing `exists_hasDerivAt_root_of_prodDomain_ift` | Mathlib `ContDiffAt.contDiffAt_implicitFunction` | ✅ **2026-08-19** — `Closures/MSASolutionFamily.lean`, drop-in from `ContDiffAt.{implicitFunction, implicitFunction_apply_self, eventually_apply_implicitFunction, contDiffAt_implicitFunction}`; **closes gap (B); ceiling was NOT real** (cf. `feedback_stale_blockers`) |
| MSAFAM.4 ⚠ | weaken FOEQ.7/FOEQ.8's `hOZ` from `∀ s` to `∀ᶠ s in 𝓝 0` | `Filter.EventuallyEq.iteratedDeriv_eq` | ✅ **2026-08-19** — `Closures/FirstOrderEquivalence.lean` in place: `hconst` funext → `hev` `EventuallyEq` + `hev.iteratedDeriv_eq γ`; `oz_deriv_eq_firstOrderLine_of_taylor` re-wraps with `Eventually.of_forall`. Both still axiom-clean |
| MSAFAM.5 ⭐⭐ | `msaSolutionFamily` — from the root `ψ(τ)` to `H C : ℝ → ℂ` at fixed real `k`, with `ContDiff` and `∀ᶠ τ, (1+H τ)(1−C τ) = 1` | **MSAEXACT.1 (full)**; MSAFAM.1–4 | ☐ — gap (C), the real depth |
| MSAFAM.6 ⭐⭐ | Theorem I.1 with **no hypothesis**: `oz_msa_taylor_eq_hierarchy` applied to the constructed family, `N = 1` | MSAFAM.2/3/4/5 | ☐ — the capstone |
| MSAFAM.7 | the same at general `N` | **gated on MSAEMIX**, deliberately | ☐ |

Home: `YukawaOZ/MSABlumHoyeSystem.lean` (L3, namespace `FMSA.MSAExact`, beside `MSAClosedForm.lean`)
for MSAFAM.1–2; `Closures/MSASolutionFamily.lean` (L5, new namespace `FMSA.MSASolutionFamily`) for
MSAFAM.3–6. MSAFAM.4 edits `Closures/FirstOrderEquivalence.lean` in place.

## The three gaps, in order of depth

### (A) Transcription — MSAFAM.1/2, algebra with no analysis in it

Theory note §7g, at one tail, in the variables where every `e^{z}` cancels:

    bhF (Dt, G) = 1 − ρ·Q̂(z)                                  … the Baxter factor
    bhP (Dt, G) = A + z·q′ + (z²/2)·γ·Dt ,   γ = 1 − 2πρ·G·e^{−z}/z

with `Q̂(z) = φ₁(z)q′ + φ₂(z)A + {[2πρ·Dt·G/z + γ·Dt·e^{−z}]/(2z) + γ·Dt(1−e^{−z})/z}`, and `A`,
`q′` themselves depending on `(Dt, G)` through `M`, `N`. Polynomials, `exp`, and division by
nonzero constants — `ContDiff ℝ ∞` is `fun_prop`.

The four properties MSAFAM.2 owes are not equally sized:

* **vanishing `G`-derivative** (`fderiv bhF (0,G₀) (0,1) = 0`, same for `bhP`) — the ⭐ insight
  already recorded: `G` enters both **only** through the factor `Dt`, and `Dt = 0` at the base
  point. With `bhF`/`bhP` written as above this should fall to `fderiv` computation, because every
  `G`-bearing monomial carries a literal `Dt` factor. ⚠ Write them so that this is *syntactically*
  visible; a formulation that expands `γ·Dt` into `Dt − 2πρ·G·Dt·e^{−z}/z` is equally true and much
  worse to differentiate.
* **`bhF (0,G₀) = 1 − ρQ̂₀(z)`** — the load-bearing one, and the *only* place the transcription
  touches the rest of the library. Without it `F₀ ≠ 0` cannot be discharged from
  `HardSphere.Q0_ne_zero_at_yukawa` and the whole chain reverts to an assumption.
* **the PY base equation `2π·G₀·F₀ = bhP (0,G₀)`** — ⚠ **this is a hard-sphere identity, not a
  Yukawa one.** At `Dt = 0` it reads `2π·ĝ_PY(z)e^{z}·(1−ρQ̂₀(z)) = (A⁰ + z·q⁰′)/z²`: a relation
  among the PY Baxter factor, the PY `g`'s Laplace transform, and the PY coefficients, with no tail
  in it. **Locate it before deriving it** — `HardSphere/{BaxterWienerHopf,BaxterRenewal,RadialLaplace}.lean`
  and MSAEXACT.4's `y0_py_eq_contact` are where an equivalent is most likely already sitting. If it
  genuinely is absent it is a small HS task, and it should be *filed as one*, not smuggled in here.
* **`G₀` must be a `def`, not a variable.** FOEQ.5's capstone leaves `G₀` free; the concrete version
  has to name it (`G₀ = ĝ_PY(z)·e^{z}`), which is what makes the base equation a theorem rather
  than a hypothesis with a suggestive name.

⚠ **Three known print errors in the source** (Blum & Høye 1978: (36) drops a power of `z` vs (21),
with the correct powers *mixed*; (35) inverts `z` vs (27); (29) omits `e^{zσ_ij}`). The
transcription must be against `waisman_msa_closed_form.md`'s corrected forms, **never** against the
printed equations. This is the one place in the group where a wrong character is not caught by any
type.

### (B) Order — MSAFAM.3, and it is free

⭐ **The pinned Mathlib already has the `C^n` implicit function theorem, in exactly the ProdDomain
form this project consumes.** `Mathlib/Analysis/Calculus/ImplicitContDiff.lean`:

    ContDiffAt.contDiffAt_implicitFunction
      (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0)
      (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
      ContDiffAt 𝕜 n (cdf.implicitFunction pn if₂) u.1

with `implicitFunction_apply_self` and `eventually_apply_implicitFunction` beside it — the same
three facts `exists_hasDerivAt_root_of_prodDomain_ift` extracts, one smoothness class up. Since the
BH map is `C^∞`, the root is `C^∞` at `τ = 0`, which is what Theorem I.1's `∀γ` needs.

So MSAFAM.3 is a drop-in: same shape, `HasStrictFDerivAt` → `ContDiffAt`, `HasDerivAt ψ ψ' 0` →
`ContDiffAt ℝ n ψ 0`. Keep the `HasDerivAt` version — FOEQ.5's `γ=1` capstone consumes it and there
is no reason to churn a landed theorem.

⚠ Per `feedback_stale_blockers`: the `γ = 1` ceiling was never argued as a Mathlib gap, but it was
never lifted either, and it has been quietly setting the group's scope since 2026-08-10. **Check
the library before assuming the ceiling is real** — this is the same lesson as MA.8.

### (C) Family — MSAFAM.5, the real remaining depth

The root `ψ(τ) = (Dt(τ), G(τ))` is a pair of numbers. Theorem I.1 wants functions obeying OZ. Two
halves:

* **the identity**, pointwise in `τ`: coefficients satisfying the algebraic system ⇒ Baxter
  factorization ⇒ OZ with the MSA closure. **This is MSAEXACT.1**, and its closure-recovery half is
  that group's open analytic core (a multi-file effort re-running `baxter_wiener_hopf_factorization`
  with the tails). MSAFAM does not attempt it; it consumes it.
* **the transport**, in `τ`: with the identity in hand, `C̃(k,τ)` is explicit in `(Dt(τ), G(τ))`
  — polynomial and `exp` — so `ContDiff` composes. `H̃ = (1−C̃)⁻¹ − 1` needs `1 − C̃(k,τ) ≠ 0`,
  which on the real `k` axis is `Q̂(k)Q̂(−k) = |Q̂(k)|² > 0`. ⚠ That nonvanishing is *not* free and
  is not the same fact as `F₀ ≠ 0`: it is the no-spinodal statement, and at finite coupling it is
  MSAEXACT.3 territory (physical branch only). **Take `k` fixed and real, and state the family at
  `𝔸 = ℂ`** — Theorem I.1 is pointwise in `k`, so no `L¹`/operator-norm question arises and none
  should be invented.

### ⚠ MSAFAM.4 — the `∀ s` trap, which would surface only at the last step

FOEQ.7 takes `hOZ : ∀ s, (1 + H s) * (1 - C s) = 1`, **globally in the coupling**. No implicit
function theorem produces a global root — Mathlib's gives `∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u`, and it
could not give more, since the branch folds at finite `τ` (`coupling_series_radius.md`). So **as
written, FOEQ.7 is unusable by any construction of the kind MSAFAM.5 must perform**, and the
mismatch appears only when the last piece is being fitted.

The proofs support the weakening in substance — `iteratedDeriv … 0` is local — but not as written:
`hconst` is proved by `funext s`. Route: make `hconst` a `Filter.EventuallyEq` and rewrite through
`Filter.EventuallyEq.iteratedDeriv_eq` (`Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:439`),
then `iteratedDeriv_const`. Do this **first**, before MSAFAM.5 — it is an hour, and doing it last
means discovering it with the expensive part already built against the wrong signature.

⚠ It also improves the *paper*: `∀ s` claims OZ+MSA has a solution at every coupling, which is
false past the fold. The theorem should say what it needs, which is a neighbourhood of zero.

## Constraints and boundaries

* **No new axiom is admissible in MSAFAM.1–4.** They are algebra over `ℝ` with `e^{−z}` a parameter
  plus one Mathlib IFT — the same rule MSAEXACT states for itself. Needing an axiom means a route
  was abandoned. MSAFAM.5 inherits whatever MSAEXACT.1 carries, and nothing beyond it.
* ⚠ **Do not let MSAFAM.1–4 be reported as "the hypothesis is discharged".** They close (A) and (B);
  the hypothesis is (A)+(B)+(C). The honest interim headline is *"FOEQ.5's capstone is now
  hypothesis-free at `γ = 1`, and holds at every `γ`; it still produces an amplitude, not a
  solution family."*
* ⚠ **The measured evidence is not a partial proof and does not shrink the target.** Analyticity in
  a measured disc with fortieth-order reconstruction to `6e-16` (SI, `coupling_series_radius.md`)
  covers the hypothesis *as stated* — which is why the paper can lean on it — but it is evidence.
  It is also the reason MSAFAM is worth opening rather than living with: the measurement says the
  statement is true, so the only question left is formalization cost.
* **Scope.** MSAFAM says nothing about `τ = 1`. The fold, the radius, the divergence of the summed
  series are all statements at physical coupling; this group is entirely at `τ = 0`. Cf. the
  paper's *"What does not bear on it"* paragraph — keep them separate here too.
* **General `N` is deliberately gated.** MSAFAM.7 stacks the matrix root question on an algebra
  that must already be right, exactly as MSAEMIX does; the paper's Theorem I.1 is stated at general
  `N`, so `N = 1` closes the *hypothesis's substance*, not its full generality. Say so rather than
  rounding up.
