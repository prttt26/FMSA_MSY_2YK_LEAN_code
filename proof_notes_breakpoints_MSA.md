# Proof Notes: Breakpoint Structure of the *Exact* MSA DCF (Group BRK)

Proof records for **Group BRK** — the knot structure of the mixture DCF core, at **every
order in the coupling** and at **every `N`**. Companion to
[proof_notes_breakpoints.md](proof_notes_breakpoints.md) (Group IB), which covers the
*first-order* / stepwise-polynomial side; see [todo/to_Lean.md](../todo/to_Lean.md) for the
status index.

**Source:** `msaemix_uneq_core.py`, `msaemix_uneq_pieces.py`, `msaemix_uneq_n3.py` (parent
repo, commits 18ef2da + e973781) — the numerical characterisation recorded as **MSAEMIX.5**
in [proof_notes_msa_exact.md](proof_notes_msa_exact.md). This group is the formalisation of
that characterisation plus the corollary it forces.

---

## ⚠ Why this is a separate group and not more of IB

IB is about the **mediated** knots `r* = R_ab + R_ia`, `r** = r* + (3d_b − d_j)/2` — objects
that carry a *third* species index and exist only at `N ≥ 3`. Its own header already draws
the line: those are features of the stepwise-polynomial decomposition and of the **RDF**, and
a formalisation asserting a mediated *DCF* breakpoint would be **false** (see IB.9).

BRK is about the opposite claim, on a different object: that the **exact** MSA core carries
no mediated knot either, so the absence is not special to first order. IB.9 is the
first-order half of the same statement and is deliberately **not** restated here — BRK.3
points at it and derives it, rather than duplicating it.

⚠ **Do not merge the two files.** IB proves things *about* `r*`; BRK proves `r*` is *absent*.
Sharing a file invites a future reader to lift an IB lemma into a BRK context, where it is
about the wrong function.

---

## ⚠ BRK.2 and BRK.3 are FORMALISATION SLOTS for tasks that already exist

Neither restates its source. Each is the Lean half of a task owned by another group, and the
substance stays where it is:

| BRK slot | is the Lean half of | owner file | status there |
|---|---|---|---|
| **BRK.2** (exact MSA) | **MSAEMIX.5** | [proof_notes_msa_exact.md](proof_notes_msa_exact.md) | ✓ DONE 2026-08-22, **fully Lean** (`MSAEMixBreakpoints.lean`, std-3) |
| **BRK.3** (first order) | **IB.9** | [proof_notes_breakpoints.md](proof_notes_breakpoints.md) | ✓ DONE — `MixtureConvolution.pbp_breakpoints_subset` + `MixtureDCFSmooth.dcfOdd_contDiffOn_*` |

⚠ **Edit the owner, not the copy.** If MSAEMIX.5's numbers or scope change, they change in
`proof_notes_msa_exact.md`; this file carries only what the *proof* needs. Two records of one
measurement drift apart, and the one in the file nobody runs is the one that goes stale.

---

## Status

| task | statement | status |
|---|---|---|
| **BRK.1** | convolution knot-closure: knots of `f ⋆ g` ⊆ sums of knots of `f`, `g` | ✓ **COVERED — point, no new development.** Mathlib `support_convolution_subset` + the reusable Minkowski helpers `Ici_add_Icc_subset` / `Icc_add_Ici_subset` (`YukawaOZMix/MixtureConvolution.lean`) already provide it; the mixture uses them at `bConvP_support_subset` / `pbpConv_support_subset` |
| **BRK.2** ⭐ | the four `t`-kink crossings are `σ_l`-**independent** | ✓ **DONE — fully Lean, std-3; point (owner = MSAEMIX.5).** The four crossings + capstone are `MSAEMixBreakpoints.{bp_loLo_indep, bp_hiHi_indep, bp_hiLo_indep, bp_loHi_indep, breakpoints_sigma_l_free}` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Same `ring` cancellation as the first-order `MixtureConvolution.lean` edge identities |
| **BRK.3** | first order as an *instance*: IB.9 / `dcfOdd_contDiffOn_*` from BRK.1+BRK.2 | ✓ **DONE — point (owner = IB.9).** `MixtureConvolution.pbp_breakpoints_subset` (breakpoint set `{±λ_ij, ±R_ij}`, `m,n` cancel, all N) + `MixtureDCFSmooth.dcfOdd_contDiffOn_upper/_lower/_like` |
| **BRK.4** | order-by-order corollary: `J(K) ≡ 0` on an interval ⇒ every `J_n = 0` | ✓ **DONE 2026-08-22, std-3** — `YukawaOZMix/MSAEMixBreakpointOrders.jump_all_orders_vanish` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`): `J` real-analytic on a preconnected open coupling-domain `U` and `= 0` on a subinterval `(a,b) ⊆ U` ⇒ `iteratedDeriv n J x₀ = 0` for all `n` at every `x₀ ∈ U` (every Taylor coeff `J_n = 0`), via Mathlib's identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. Physics input (analyticity in `K` + `J = 0` on an interval) = BRK.5 + BRK.2's `K`-independence; not re-proved here (BRK.4 predicts the cancellation, does not exhibit `c^{(2)}`) |
| **BRK.5** | the `n = 2` witness (numerical) — falsification test for BRK.4 | ◑ **witnessed 2026-08-22** (`brk5_witness.py`, parent repo): exact-MSA `c_ij` from the Baxter `Q`. ⭐ **correct mediated candidate `r* = R[a,b] + R[i,a]`** (TWO intermediates a,b), active INSIDE the core iff **(A) `2σ_a+σ_b < σ_j`** and **(B) `σ_j < 3σ_b`** (`verify_mediated_breakpoints.py`) — so it genuinely CAN sit inside `(0,σ_ij)`, where the FMSA/stepwise term kinks. Tested 3 σ-sets: `[1,4,8]` (1 distinct + 1 degenerate), `[1,2,3,6]` (3 distinct), `[1,2,4,10]` (4 distinct) = **8 distinct active intra-core `r*`; exact MSA SMOOTH at EVERY one** (single-piece straddle within the enclosing piece, worst **1.9e-14** rel) ⇒ the FMSA mediated kink is ABSENT — BRK.4 cancellation witnessed **non-vacuously**. ⚠ `[1,4,8]` alone is a WEAK test (only 1 distinct); N=4 activates more. ⚠ caught a quad lower-limit bug (support starts at `λ=(min σ−max σ)/2`, below the old `−3`). ⚠ still fixed-`K` points, but breakpoint *locations* are geometric/`K`-independent (BRK.2) ⇒ robust in `K` |

---

### Task BRK.1 — Knots of a convolution are sums of the factors' knots

The paper's `lem:closure`: a product with `n₁` and `n₂` pieces has at most `n₁+n₂−1`, and its
breakpoints are sums of the factors'. Used inline there; wanted here as a reusable lemma,
since BRK.2/BRK.3 and (probably) the RDF work all need it.

⚠ **Check MA.16 `ConvolutionLeibniz.lean` before writing anything.** The support arithmetic
for `supp(f ⋆ g) ⊆ supp f + supp g` is already there for the first-order work; the knot
statement may be a short corollary of what exists rather than a new development. Re-deriving
it would repeat the mistake logged in `feedback_stale_blockers`.

---

### Task BRK.2 ⭐ — The intermediate species cancels out of the knot locations

> **≡ MSAEMIX.5**, the exact-MSA task ([proof_notes_msa_exact.md](proof_notes_msa_exact.md)) —
> ✓ DONE there **numerically** (N = 2 and N = 3, σ = [1.0, 1.4, 1.9], all six off-diagonal
> cores 2-piece to 1e-13…1e-15). BRK.2 is the *formalisation* of that result and adds no new
> physics; the scope, the piece structure and the basis are recorded there, not here.

**The crux of the group, and it is arithmetic.** In the Baxter convolution

```
2π r c_ij(r) = −Q'_ij(r) + Σ_l ρ_l ∫₀^∞ Q'_il(t+r) Q_jl(t) dt
```

the integrand has kinks in `t` at `λ_lj`, `σ_jl`, `λ_li − r`, `σ_il − r`. The `r`-breakpoints
of `c_ij` are set by the four crossings of those kinks, and with
`λ_ab = (σ_a − σ_b)/2`, `σ_ab = (σ_a + σ_b)/2`:

```
λ_li − λ_lj = λ_ji        σ_il − σ_jl = λ_ij
σ_il − λ_lj = σ_ij        λ_li − σ_jl = −σ_ij
```

Every `σ_l` cancels — it enters `λ_li` and `λ_lj` symmetrically and drops out of the
difference. So the crossing set is `{±λ_ij, ±σ_ij}`, **independent of the intermediate
species, for every `N`**.

⭐ **No analysis, no integrability side conditions, no new axiom** — substitute the two
definitions and `ring`. This is what converts MSAEMIX.5's *knot locations* from numerical to
proved, which is the half the paper actually cites.

⚠ **It does NOT prove the piece count or the basis.** MSAEMIX.5 also records that the
diagonal is single-piece, the off-diagonal 2-piece, and both pieces sit on
`{1, r, r², r⁴, e^{±zr}}` with `g := 2πr c`, `g(0)=0`. Those are statements about the
*coefficients*, they belong to MSAEMIX.4 Stage 3, and BRK.2 must not be written as if it
delivered them.

⚠ Sequence with **MSAEMIX.4 Stage 3** — both need the real-space `Q_ij` set up. Doing them
apart means building that twice.

---

### Task BRK.3 — First order is an instance, not a coincidence

> **≡ IB.9** ([proof_notes_breakpoints.md](proof_notes_breakpoints.md)) — "the first-order
> **DCF** has only the `λ_ij` knot; mediated `r*` add none, for all N", currently marked
> *optional*. BRK.3 is that task, re-sited so it is derived rather than proved standalone.

Restate the paper's `thm:breakpoints` so that IB.9 and
`dcfOdd_contDiffOn_upper/_lower/_like` follow from BRK.1 + the BRK.2 cancellation, instead of
being proved on their own.

The first-order proof already *is* this cancellation in another guise: every `σ_m`, `σ_n`
cancels identically in the four edges of `P_im ⋆ B_mn ⋆ P_jn`. Two constructions, one
mechanism. Stating it once makes the paper's §`sec:breakpoints` a structural result rather
than a first-order curiosity.

⚠ **Points at IB.9, does not restate it.** If IB.9 lands first, BRK.3 is a corollary; if BRK
lands first, IB.9 should be *re-pointed at BRK.3* rather than kept as an independent proof.
Decide which before either is written, or the tree ends up with two proofs of one fact.

---

### Task BRK.4 — Every order, not just the first

> ✓ **DONE 2026-08-22, std-3** — `YukawaOZMix/MSAEMixBreakpointOrders.jump_all_orders_vanish`.
> The identity-theorem corollary is now Lean: `J` analytic on a preconnected open `U`, `= 0` on a
> subinterval `⇒ iteratedDeriv n J x₀ = 0` ∀`n` (every `J_n = 0`). The `K`-range worry below is
> resolved two ways: BRK.5 witnesses `J = 0` on a range numerically (8 distinct active intra-core
> `r*`, ≤1.9e-14), and BRK.2's breakpoint *locations* are geometric/`K`-independent, so `J ≡ 0`.

Let `J(K)` be the jump of `c_ij` in whatever derivative first sees a candidate mediated knot,
and `J(K) = Σ_n K^n J_n` with `J_n` the jump carried by `c^(n)`. MSAEMIX.5 gives `J(K) = 0`.
If that holds on an **interval** of `K`, the identity theorem forces every `J_n = 0`.

⭐ The consequence is the one the paper wants: mediated knots cannot cancel *across* orders —
they must cancel **within each order**, among the terms composing `c^(n)`. First order is
where the mechanism is visible (BRK.3); every higher order is obliged to do the same thing.

⚠⚠ **This rests entirely on `K`-range, and that has not been checked.** MSAEMIX.5's scripts
were run at parameter values, not swept as a function of coupling. Before BRK.4 is written:
establish what range of `z`, `ρ` and coupling `msaemix_uneq_n3.py` actually covers. **If the
evidence is isolated points, BRK.4 is unsupported and BRK.5 becomes a prerequisite rather
than a confirmation.** A power series argument from finitely many `K` values proves nothing.

⚠ The formal expression for `c^(2)` *does* contain RDF-type convolutions and therefore
candidate mediated knots term by term. BRK.4 predicts they cancel; it does not exhibit the
cancellation. Do not write it as though it did.

---

### Task BRK.5 — The `n = 2` witness, and the falsification test

Compute `c^(2)` for an unequal-`σ` **ternary** and look for a kink at `r* = R_ab + R_ia`.

- **No kink** ⇒ BRK.4's predicted second-order cancellation is witnessed once, and the
  paper can say so.
- **A kink** ⇒ MSAEMIX.5's numerics do not hold on an open `K`-set, BRK.4 is false as
  stated, and the whole chain needs revisiting.

⚠ **The system must be non-degenerate.** `σ = [1, 1.5, 2]` is a trap: `σ₁₃ = σ₂₂ = 1.5`, so
two pairs share a rate and the very degeneracy being tested for is hidden. 
uses `[1, 4, 8]` for this reason.

⚠ **Breakpoint-aware quadrature is mandatory.** MSAEMIX.5 records that the earlier
"piecewise is hard" reading was **quadrature error**, not physics: the convolution integrand
has kinks at `t = λ_lj, σ_jl, λ_li − r, σ_il − r`, and passing them to `quad` via `points=`
takes every piece from a poor fit to 1e-14. A smooth-integrand `quad` here will manufacture a
spurious kink and "refute" a true statement.

⚠ Needs a real-space `c_ij(r)` for the exact solution, which `msa_exact_mix` does not have —
the same gap that makes exact MSA's bar in the paper's Fig. 6(a) a lower bound. Build it from
the Baxter `Q` directly; an inverse **transform** would smear precisely the derivative
discontinuity being looked for.

---

### Task BRK.6 ⭐⭐ — Discharge `hzero`: `J(K) ≡ 0` as a theorem, not a measurement

`jump_all_orders_vanish` (BRK.4, landed) takes `hzero : EqOn J 0 (Ioo a b)` as a
**hypothesis**. Everything downstream — the all-orders claim, and hence the paper's
§`sec:breakpoints` rewrite — rests on that premise, which is currently carried by
MSAEMIX.5's *numerics*. BRK.6 is to prove it.

**The route, and why it should be short.** BRK.2's cancellation is pure `σ`-arithmetic:

```
λ_li − λ_lj = λ_ji        σ_il − σ_jl = λ_ij
σ_il − λ_lj = σ_ij        λ_li − σ_jl = −σ_ij
```

⭐ **No `K` appears anywhere in it.** The crossing set is `{±λ_ij, ±σ_ij}` at *every*
coupling, not at the couplings that happened to be tested. If the knot set is `K`-free, then
there is no mediated knot at any `K`, so `J(K)` is identically zero because **there is no
jump for it to measure** — `hzero` follows with no interval, no sweep, and no appeal to
MSAEMIX.5's numerics.

⇒ If this works, BRK.6 supersedes the `K`-range question entirely and **BRK.5 drops from
prerequisite to confirmation**.

⚠ **What still has to be shown, and it is not nothing.** BRK.2 gives the *candidate crossing
set*. Going from "`r*` is not in the crossing set" to "`c_ij` is smooth at `r*`" needs the
crossing set to be the **complete** set of knots, not merely to contain them — i.e. BRK.1's
closure lemma applied so that no knot can arise from anywhere else in the convolution.
Without that, BRK.6 proves the mediated distance is not among a list, which is weaker than
what `hzero` needs.

⚠ **Degenerate coincidences must be handled explicitly.** `r* = (σ_i + 2σ_a + σ_b)/2` is
`σ_a`-dependent and the crossing set is not, so generically `r* ∉ {±λ_ij, ±σ_ij}` — but for
special diameters they can coincide numerically. At such a point there IS a knot at `r*`; it
simply is not a *mediated* one, and the statement must be phrased so that this is not a
counterexample. (Same class of trap as `σ = [1, 1.5, 2]` in BRK.5, where `σ₁₃ = σ₂₂`.)

⚠ If BRK.6 lands, the weakened form of BRK.4 noted below is also available — with `hzero`
holding on **every** interval including one containing `K = 0`, the analyticity,
connectedness and openness hypotheses of `jump_all_orders_vanish` are not needed, and the
result follows from smoothness at the origin alone.

---

## ⭐⭐⭐ BRK.7 — THE COMPLETE SCHEME: every order, directly, with no `K`-analysis

**This supersedes the BRK.4/BRK.6 route for the all-orders claim.** That route reasons about
the resummed `J(K)` and therefore drags in analyticity, a `K`-interval and an identity
theorem. None of it is necessary. The right statement is structural:

> **Piece BOUNDARIES are geometric; piece COEFFICIENTS are dynamical.**
> `K` moves the coefficients and can never move a boundary.

Differentiating in `K` therefore cannot create a knot, and the whole thing falls out order by
order with no analysis at all.

### Step 1 — Geometric support/knot lemma for the Baxter factor

For every coupling, `Q_ab(·)` is supported on `[λ_ba, ∞)`, is smooth on `(λ_ba, σ_ab)` and on
`(σ_ab, ∞)`, and its only possible knots are `λ_ba` and `σ_ab` — **both pure functions of the
diameters**. This is Wiener–Hopf/Baxter structure, not closure-specific.

*Existing material:* `MatBaxterFactorization`, `matFourierFactor`, the mixture-RDF WH atoms;
`msaemix_uneq_core.py` validated the real-space `Q_ij` (support `[λ_ji,∞)`, poly on
`[λ_ji,σ_ij]` of width `σ_i`, C̃ box) to ~1e-8.

### Step 2 ⭐ — `K`-independence of the knot set (the crux)

`Q_ab(r;K)` has the parametric form

```
[ poly(r) + W_ab e^{−zr} + Ct_ab ] · 1_{[λ_ba, σ_ab]}(r)   +   [ tail ] · 1_{[σ_ab, ∞)}(r)
```

with `K` entering **only** through the scalar amplitudes (`A_j`, `q'_ij`, `W`, `Ct`, `Gt`).
The indicators carry no `K`. Hence `∂ⁿ_K Q_ab` has knots ⊆ `{λ_ba, σ_ab}` for every `n`.

⚠ **This is where the actual work is.** Steps 1, 3, 4, 5 are bookkeeping; Step 2 is the
theorem. In a development that *defines* `Q` by this form (as `MSAEMixCore` does via
`coreC1..coreC5`) it is close to definitional — but then the content moves to showing the
BH root really has that form at unequal `σ`, general `N`, which is MSAEMIX.4 Stage 3's job.
**Do not let Step 2 be assumed on one side and proved on the other.**

⚠ Guard the endpoints at `σ ≠ 1`: the poly piece has width `σ_i` *shifted by* `λ_ji`. The
`σ=1` masking bug (commit 5ded95d, spurious `σ` in the C̃ box) came from exactly this class.

### Step 3 — Convolution knot closure  ⟵ **BRK.1**

`knots(f ⋆ g) ⊆ knots(f) + knots(g)`, endpoints included.

### Step 4 — The `σ_l` cancellation  ⟵ **BRK.2**

Feed Step 1's knot sets into Step 3 for `Σ_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt`: the four crossings
collapse to `{±λ_ij, ±σ_ij}`, with every `σ_l` gone.

### Step 5 — Assembly by Leibniz  ⟵ **MA.16 `ConvolutionLeibniz`**

`c^(n)_ij = (1/n!) ∂ⁿ_K c_ij`. Differentiate the Baxter relation `n` times; by Leibniz,
`∂ⁿ_K` of the convolution is a **finite sum** of convolutions of `∂ᵖ_K Q'_il` with
`∂^q_K Q_jl`, `p+q=n`. Every factor has knots ⊆ `{λ, σ}` by Step 2, so every term has knots
⊆ `{±λ_ij, ±σ_ij}` by Steps 3–4. Finite sums do not enlarge a knot set.

⇒ **For every `n`, every `N`, every `(i,j)`: the interior knot of `c^(n)_ij` on `(0,σ_ij)` is
`|λ_ij|` and nothing else.** No mediated distance can appear at any order, because no object
in the chain ever had a `σ_l`-dependent boundary to begin with.

### What this buys, and what it costs

- **No `hzero`, no `K`-range sweep, no analyticity, no `IsPreconnected`.** BRK.4 and BRK.6
  are no longer on the critical path for this claim (BRK.4 stays useful as a general lemma).
- **BRK.5 becomes a pure sanity check** — worth running anyway, since a kink at `r*` in
  `c^(2)` would mean Step 2 is false and the scheme has a hole.
- **The whole load moves onto Step 2**, which is the honest place for it: it is the one
  statement that is about the MSA solution rather than about convolution bookkeeping.

⚠ Degenerate `σ` where `r*` coincides with `σ_ij` numerically are not counterexamples — there
is a knot there, but it is not a *mediated* one. Phrase the theorem as "the knot set is
`{±λ_ij, ±σ_ij}`", never as "`r*` is not a knot".

---

### BRK.8–12 — BRK.7's five steps as concrete tasks (Step `k` → BRK.`7+k`)

| task | step | discharged by | status |
|---|---|---|---|
| **BRK.8** | Step 1 — geometric smoothness of a core piece | ✓ **DONE, std-3** — `MSAEMixBreakpointScheme.contDiff_gForm`: each core piece `gForm` (polynomial + exponentials) is `ContDiff ℝ ⊤` (entire), so the core's only interior knot is the geometric `|λ_ij|` where `matCoreUneq` switches pieces |
| **BRK.9** ⭐⭐ | Step 2 — `K`-independence of the knot set (`K` enters only the amplitudes; the indicators `1_{[λ,σ]}` carry no `K`, so `∂ⁿ_K Q` keeps knots ⊆ `{λ,σ}`) | **abstract half DONE** (`MSAEMixBreakpointOrders.contDiffOn_paramDeriv_coeffBasis`, std-3): `K` in coefficients only ⇒ every `∂ⁿ_K (Σ_k c_k(K)·b_k)` is `ContDiffOn` on the basis's smooth set — no new knot. **CONCRETE half DONE** (`MSAEMixBreakpointScheme.gForm_paramDeriv_contDiffOn`, std-3): now that MSAEMIX.4 Stage 3 (`MSAEMixCoreUneq`) supplies both pieces as the single form `gForm` in the shared 7-basis `{1,r,r²,r³,r⁴,e^{∓zr}}` with K-free boundaries (inner = `c2=c3=c4=0`), the abstract lemma instantiates on that basis ⇒ every `∂ⁿ_K` of the core form is `ContDiffOn` on each piece — no interior knot beyond `|λ_ij|` at any order. Only residual input = amplitudes `ContDiff` in `K` (BH root, carried as an explicit hyp) | ✓ **DONE — both halves, std-3.** Step 2 proved, not assumed, on both sides (abstract `contDiffOn_paramDeriv_coeffBasis` + concrete against Stage 3's `MSAEMixCoreUneq`) |
| **BRK.10** | Step 3 — convolution knot closure `knots(f⋆g) ⊆ knots f + knots g` (⟵ BRK.1) | Mathlib `support_convolution_subset` (+ mixture's `*_contDiffOn_*` for endpoints) | ✓ point |
| **BRK.11** | Step 4 — the `σ_l` cancellation (⟵ BRK.2) | `MSAEMixBreakpoints.breakpoints_sigma_l_free` (std-3) | ✓ done, point |
| **BRK.12** | Step 5 — every order: `∂ⁿ_K c` keeps its knot set `{|λ_ij|}` | ✓ **DONE, std-3** — `MSAEMixBreakpointScheme.coreForm_paramDeriv_contDiffOn`: `∂ⁿ_K` of the core `c = gForm/(2π r)` (`matCoreUneq`) is `ContDiffOn` away from `r=0`, every order ⇒ no interior knot beyond `|λ_ij|`. ⭐ **the closed-form core (Stage 3) makes the `n`-fold convolution/Leibniz resummation UNNECESSARY** — it follows from BRK.9 + the smooth `1/(2π r)` factor, not MA.16's `∂ⁿ` of a convolution |

**Completable now:** BRK.10, BRK.11 (pointers to existing green lemmas), BRK.12's `n=1` base — recorded
above. **The gap left for MSEMIX:** BRK.9 (Step 2), the K-independence of the *concrete* BH-root `Q` at
unequal σ / general N = MSAEMIX.4 Stage 3. The full assembly (BRK.10+11+12 ⇒ all-orders knot set,
*conditional on* BRK.8+9) is the remaining new Lean, gated on BRK.9 — write it once Stage 3 supplies
the piecewise-with-`K`-free-boundaries form of `Q`, so Step 2 is proved, not assumed, on both sides.

---

## ⏸ PENDING: the paper's §`sec:breakpoints` rewrite — GATED ON BRK.4

**Do not start this until BRK.4 is settled.** Recorded here so the plan survives the wait.

⚠ **Nothing in the paper is wrong today.** `thm:breakpoints` is stated for `c^(1)` and is
proved for `c^(1)`. The rewrite is an *upgrade*, not a correction, so waiting costs nothing
and rewriting early would put an unverified corollary into a published claim.

**What changes if BRK.4 lands.** The section stops being a first-order result and becomes a
statement about the MSA solution:

- the knot set of the DCF core is `{|λ_ij|}` (endpoint `σ_ij`) at **every order and every N**;
- the mediated distances are present **term by term** in the formal expression for `c^(n)`,
  `n ≥ 2` — they come in through the RDF-type convolutions — and must **cancel identically
  within each order**, since `K` is free and a vanishing power series has vanishing
  coefficients;
- the existing proof (every `σ_m`, `σ_n` cancels in the four edges of `P ⋆ B ⋆ P`) is then
  the **visible `n = 1` instance** of that cancellation, not a lucky feature of first order;
- the RDF contrast is unchanged and stays as written: mediated knots are real there, and the
  DCF's immunity is the surprise.

⇒ The one-line version the section should end up making: **the DCF's knot structure is fixed
by pair geometry alone, at every order and every `N`, while the RDF's is not.**

**What changes if BRK.4 fails** (a kink appears at `r*` in BRK.5's `n = 2` check): the
section stays as it is, and MSAEMIX.5's scope narrows to the parameter values actually
tested. That outcome is also worth a sentence in the paper, since "no mediated knot at first
order, but they return at second" is a sharper statement about the truncation than silence.

⚠ **Try BRK.6 first, and the range check only if it fails.** BRK.6 discharges `hzero`
outright from `K`-free arithmetic; if it lands, the `K`-range question disappears and the
rewrite is unblocked with no numerical premise anywhere in the chain. If BRK.6 stalls on the
completeness step, fall back to establishing the `K`/`z`/`ρ` range `msaemix_uneq_n3.py`
actually swept — a `grep` and a read — and note that what matters is **whether it reaches
`K = 0`**, not how wide it is: an interval containing the origin makes BRK.4 need only
smoothness, while one sitting at physical couplings keeps the full analytic statement and the
fold-straddling caveat.
