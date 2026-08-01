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
of the outer closure. Four tasks; **PYE.3 is the recommended, high-value starting point**.

| Task | Title | Status |
|------|-------|--------|
| PYE.1 | PY closure to O(coupling): outer `c₁ = g_HS·(−βu)` | ☐ not started |
| PYE.2 | DP first-order solution map is **linear** in the outer closure | ☐ not started |
| PYE.3 ⭐ | DCF error = DP-map applied to the finite-tail fit residual (*recommended first*) | ☐ not started |
| PYE.4 | Abstract equivalence: `DP-map[g_HS·(−βu)] = OZ+PY first order` | ☐ not started |

---

### Task PYE.1 — PY closure to first order: outer `c₁ = g_HS·(−βu)`

**Statement.** The PY closure `c = (e^{−βu} − 1)·y` expanded to `O(coupling)` gives, in the outer
region `r > R`, `c₁ = y₀·(−βu) = g_HS·(−βu)` — because `y₀ = g_HS` (the cavity function at `s=0`
equals `g_HS`, since `c₀(r>R) = 0`, `g₀ = g_HS`).

**Route.** Elementary closure algebra: `e^{−βu} − 1 = −βu + O((βu)²)` times `y = y₀ + s·y₁ + …`,
first-order coefficient `y₀·(−βu)`. Needs the cavity function `y = g·e^{βu}` in Lean (or `y₀`
introduced directly as `g_HS`). (MSA analogue: outer `c₁ = −βu`, i.e. `y₀ ↦ 1`.)

**Depends on.** `g_HS` as an available object (HS reference; Group OZ / White-Bear).
**Status.** ☐ not started.

---

### Task PYE.2 — The DP first-order solution map is linear in the outer closure

**Statement.** The Wiener–Hopf / DP first-order solution map — outer closure `↦` first-order DCF,
subject to the core condition `h₁(r<R) = 0` — is **linear** in the outer closure.

**Route.** Corollary of Group Y1: `bMulti` is linear in `K`, and `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` is
linear in `B₁`; the composite (closure ↦ tails/`B₁` ↦ `Ĉ₁`) is linear. Extract/expose the
linearity already present in Y1 rather than re-deriving.

**Depends on.** Group Y1 (`bMulti` linearity, `Ĉ₁` assembly), Group MRS (the (★) `Ĉ₁` form).
**Status.** ☐ not started.

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
**Status.** ☐ not started — **recommended starting point**.

---

### Task PYE.4 — Abstract equivalence: `DP-map[g_HS·(−βu)] = OZ+PY first order`

**Statement.** The DP solution map at the PY-level outer `g_HS·(−βu)` equals the first-order term
of the OZ+PY solution: `DP-map[g_HS·(−βu)] = (OZ+PY)₁`.

**Route.** Needs the WH solution map lifted from finite-Yukawa-pole closures to a **function-space**
(`L¹`/`L²`) outer closure. The map is linear and bounded (PYE.2/PYE.3), so this is the natural
completion — a genuine analytic lift beyond the finite-pole DP form (infinite-tail / function-space,
not a finite closed form).

**Depends on.** PYE.1, PYE.2, PYE.3 (boundedness for the completion).
**Status.** ☐ not started — harder than PYE.3 (the function-space lift is the real content).

---

## Group HNCB — First-Order HNCB Bridge Pull-Back Construction

**Claim.** The whole **fixed-rate** first-order HNCB (`pullback_passes='solve'`) is closure
expansion + a finite `(I−L)⁻¹` solve + the DP map + a linear OZ apply — **finite linear algebra**,
the finite-tail truncation being the only approximation. The *exact* self-consistent HNCB-1 is the
RDF and is out of finite-closed-form scope (HNCB.4, record-only).

| Task | Title | Status |
|------|-------|--------|
| HNCB.1 | HNCB closure to O(coupling): outer `c₁ = −βu + B·h₁` | ☐ not started |
| HNCB.2 | Fixed-rate pull-back map is **affine**: `K̃' = a + L·K̃` | ☐ not started |
| HNCB.3 | Fixed point `K̃* = (I−L)⁻¹a`; `(I−L)` invertible | ☐ not started |
| HNCB.4 | *(record only)* Exact HNCB-1 carries the RDF `h₁` ⇒ HS poles ⇒ not a finite closed form | ☐ boundary |

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
**Status.** ☐ not started.

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
