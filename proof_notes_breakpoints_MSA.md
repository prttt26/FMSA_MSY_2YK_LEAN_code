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
| **BRK.2** (exact MSA) | **MSAEMIX.5** | [proof_notes_msa_exact.md](proof_notes_msa_exact.md) | ✓ DONE 2026-08-22, **fully Lean** (`MSAMixtureBreakpoints.lean`, std-3) |
| **BRK.3** (first order) | **IB.9** | [proof_notes_breakpoints.md](proof_notes_breakpoints.md) | ✓ DONE — `MixtureConvolution.pbp_breakpoints_subset` + `MixtureDCFSmooth.dcfOdd_contDiffOn_*` |

⚠ **Edit the owner, not the copy.** If MSAEMIX.5's numbers or scope change, they change in
`proof_notes_msa_exact.md`; this file carries only what the *proof* needs. Two records of one
measurement drift apart, and the one in the file nobody runs is the one that goes stale.

---

## Status

| task | statement | status |
|---|---|---|
| **BRK.1** | convolution knot-closure: knots of `f ⋆ g` ⊆ sums of knots of `f`, `g` | ✓ **COVERED — point, no new development.** Mathlib `support_convolution_subset` + the reusable Minkowski helpers `Ici_add_Icc_subset` / `Icc_add_Ici_subset` (`YukawaOZMix/MixtureConvolution.lean`) already provide it; the mixture uses them at `bConvP_support_subset` / `pbpConv_support_subset` |
| **BRK.2** ⭐ | the four `t`-kink crossings are `σ_l`-**independent** | ✓ **DONE — fully Lean, std-3; point (owner = MSAEMIX.5).** The four crossings + capstone are `MSAMixtureBreakpoints.{bp_loLo_indep, bp_hiHi_indep, bp_hiLo_indep, bp_loHi_indep, breakpoints_sigma_l_free}` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Same `ring` cancellation as the first-order `MixtureConvolution.lean` edge identities |
| **BRK.3** | first order as an *instance*: IB.9 / `dcfOdd_contDiffOn_*` from BRK.1+BRK.2 | ✓ **DONE — point (owner = IB.9).** `MixtureConvolution.pbp_breakpoints_subset` (breakpoint set `{±λ_ij, ±R_ij}`, `m,n` cancel, all N) + `MixtureDCFSmooth.dcfOdd_contDiffOn_upper/_lower/_like` |
| **BRK.4** | order-by-order corollary: `J(K) ≡ 0` on an interval ⇒ every `J_n = 0` | ✓ **DONE 2026-08-22, std-3** — `YukawaOZMix/MSAMixtureBreakpointOrders.jump_all_orders_vanish` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`): `J` real-analytic on a preconnected open coupling-domain `U` and `= 0` on a subinterval `(a,b) ⊆ U` ⇒ `iteratedDeriv n J x₀ = 0` for all `n` at every `x₀ ∈ U` (every Taylor coeff `J_n = 0`), via Mathlib's identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. Physics input (analyticity in `K` + `J = 0` on an interval) = BRK.5 + BRK.2's `K`-independence; not re-proved here (BRK.4 predicts the cancellation, does not exhibit `c^{(2)}`) |
| **BRK.5** | the `n = 2` witness (numerical) — falsification test for BRK.4 | ◑ **witnessed 2026-08-22** (`brk5_witness.py`, parent repo): exact-MSA `c_ij` from the Baxter `Q`. ⭐ **correct mediated candidate `r* = R[a,b] + R[i,a]`** (TWO intermediates a,b), active INSIDE the core iff **(A) `2σ_a+σ_b < σ_j`** and **(B) `σ_j < 3σ_b`** (`verify_mediated_breakpoints.py`) — so it genuinely CAN sit inside `(0,σ_ij)`, where the FMSA/stepwise term kinks. Tested 3 σ-sets: `[1,4,8]` (1 distinct + 1 degenerate), `[1,2,3,6]` (3 distinct), `[1,2,4,10]` (4 distinct) = **8 distinct active intra-core `r*`; exact MSA SMOOTH at EVERY one** (single-piece straddle within the enclosing piece, worst **1.9e-14** rel) ⇒ the FMSA mediated kink is ABSENT — BRK.4 cancellation witnessed **non-vacuously**. ⚠ `[1,4,8]` alone is a WEAK test (only 1 distinct); N=4 activates more. ⚠ caught a quad lower-limit bug (support starts at `λ=(min σ−max σ)/2`, below the old `−3`). ⚠ still fixed-`K` points, but breakpoint *locations* are geometric/`K`-independent (BRK.2) ⇒ robust in `K` |
| **BRK.6** ⭐⭐ | discharge `hzero`: `J(K) ≡ 0` as a theorem | ✓ **COMPLETENESS HALF CLOSED 2026-08-25** — the enumeration is exhaustive **by counting** (below), and confirmed by a kink scan that looks for breakpoints *wherever they are* rather than testing predicted ones (`brk_completeness.py`): **25 `(i,j)` pairs over `σ = [1,4,8]` and `[1,2,3,6]`, every detected kink in `{\|λ_ij\|, R_ij}`, ZERO unexplained**. ⇒ `hzero` no longer rests on MSAEMIX.5's numerics and **BRK.5 drops to confirmation**, exactly as this group predicted. Remaining = the Lean assembly, which is BRK.8–12, not new mathematics |
| **BRK.7** | the complete scheme (Steps 1–5), superseding the `K`-analysis route | ◑ **argument COMPLETE, Lean assembly open** — Steps 1–5 are stated below; Step 2 is the only theorem, the rest is bookkeeping. Tracked as BRK.8–12 |


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

> ✓ **DONE 2026-08-22, std-3** — `YukawaOZMix/MSAMixtureBreakpointOrders.jump_all_orders_vanish`.
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

### ✓ The completeness gap is closed (2026-08-25)

The caveat that used to stand here — *"BRK.2 gives the candidate crossing set; going from
'`r*` is not in the crossing set' to '`c_ij` is smooth at `r*`' needs the crossing set to be
the **complete** set of knots, not merely to contain them"* — is answered twice over.

**(a) Exhaustive by counting.** The DCF is

    c_ij(r) = −Q′_ij(r) + Σ_l ρ_l ∫ dt Q′_il(t+r) Q_jl(t)

`Q_jl(t)` is piecewise with **exactly two** knots — `t = λ_jl` and `t = R_jl` (zero below the
first, poly+exp between, pure exp above). `Q′_il(t+r)` carries the same two, shifted:
`t = λ_il − r` and `t = R_il − r`. By BRK.1 a convolution kinks only where a **moving** knot
meets a **fixed** one, so the integral's knot set is exactly the `2 × 2 = 4` crossings — and
BRK.2 evaluates *all four*:

    λ_il − r = λ_jl  ⇒  r = λ_ij        R_il − r = R_jl   ⇒  r = λ_ij
    R_il − r = λ_jl  ⇒  r = R_ij        λ_il − r = R_jl   ⇒  r = −R_ij

There is no fifth crossing to miss: the count is `2 × 2`, not "the ones we thought of". The
direct term `−Q′_ij(r)` contributes its own two knots at the same `{λ_ij, R_ij}`. ⇒ no `σ_l`
survives anywhere, so **no mediated knot exists at any coupling** — which is precisely
`hzero`, with no interval, no sweep and no appeal to MSAEMIX.5.

**(b) Confirmed by a scan that does not know the answer.** `brk_completeness.py` samples
`c_ij(r)` on a uniform grid across the whole support and flags kinks by the raw 4th finite
difference (`O(h⁴)` where `c` is smooth, `O(jump)` at a break of any order ≤ 3 — deliberately
*not* divided by `h⁴`, which would restore the noise the small `h` suppresses). It then asks
whether every peak lies in `{|λ_ij|, R_ij}`:

| case | pairs | unexplained kinks |
|---|---|---|
| `σ = [1, 4, 8]`, `N = 3` | 9 | **0** |
| `σ = [1, 2, 3, 6]`, `N = 4` | 16 | **0** |

⚠ This is a different test from BRK.5. BRK.5 evaluates smoothness **at predicted `r*`**; this
scans for breakpoints **wherever they are**. Only the second can falsify completeness, and it
is the one the old caveat was asking for.

⇒ **BRK.5 drops from prerequisite to confirmation**, as this section anticipated, and the
`K`-range question disappears. What remains is the *Lean assembly* of Steps 1–5 (BRK.8–12) —
bookkeeping around Step 2, not new mathematics.

⚠ **Still live — degenerate coincidences must be handled explicitly.** (Unaffected by the
closure above: the counting argument bounds *where* knots can be, not whether two of the
allowed locations collide.) `r* = (σ_i + 2σ_a + σ_b)/2` is
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
theorem. In a development that *defines* `Q` by this form (as `MSAMixtureCore` does via
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

### ⚠⚠ BRK.9 IS MIS-SIZED — scope span-membership before conceding it to sympy

**Do not write BRK.9 off as "too large for Lean" until this has been scoped.** The deferral
was priced against the wrong target.

`contDiffOn_paramDeriv_coeffBasis` (landed) requires only

```lean
(hc : ∀ k ∈ I, ContDiff ℝ ⊤ (c k))      -- c_k smooth in K
(hb : ∀ k ∈ I, ContDiffOn ℝ ⊤ (b k) s)  -- b_k smooth in r on the piece
```

⭐⭐ **The VALUES of `c₁..c₅` never enter.** Step 2 needs only that *some* decomposition
`Σ_k c_k(K)·b_k(r)` exists with `K`-free boundaries. So the Lean obligation is **not**
MSAEMIX.4 Stage 3's closed-form coefficient derivation. It is the weaker structural claim:

> on each piece the Baxter factor lies in the **span of a fixed, `K`-independent finite
> basis** in `r` — `{1, r, r², r⁴, e^{±zr}}` — with boundaries `λ_ji`, `σ_ij` functions of
> `σ` alone.

Two different jobs, and only the second is on the breakpoint critical path:

| | needed by | cost |
|---|---|---|
| **which** element of the span (`c₁..c₅` closed forms) | MSAEMIX.4, the physics | large — sympy's, and reasonably so |
| **that** it lies in the span, boundaries `K`-free | BRK.7 Step 2 | ☐ **unscoped** — plausibly small |

Span-membership and boundary-freeness are statements about the **form** of the Baxter
equations — they produce `Q` from polynomial and exponential data on fixed intervals — so
they may be provable without ever solving for the coefficients.

⚠ **The project's own record says price this before believing it.** Effort-justified gaps
have repeatedly fallen here: MA.10/11/12 were all deferred as too large and all fell in about
six hours (`feedback_effort_vs_gap_axioms`: an axiom justified by *effort* is a retirement
target; only genuine-Mathlib-gap arguments stay). "Derive a multi-hundred-term closed form in
Lean" is genuinely infeasible; "show membership in a five-element span" is a different task,
and the deferral was priced against the first.

**Scope task:** establish whether span-membership + `K`-free boundaries can be proved from
the Baxter/WH structure already in the tree (`MatBaxterFactorization`, `matFourierFactor`,
`MSAMixtureCore`'s basis) without the coefficient derivation. Outcome decides the paper's
wording:

- **small** ⇒ the breakpoint claim becomes fully Lean; sympy keeps the coefficients, which
  the breakpoint result never needed.
- **large** ⇒ the seam is real, and the paper says so explicitly: *the `σ_l`-cancellation and
  the order-lifting are machine-checked in Lean; the closed form of the Baxter factor is
  established by exact symbolic computation.* Still stronger provenance than any comparable
  paper — but never under an umbrella "formally verified".

⚠ Whichever way it goes, the general-`N` step needs checking too: sympy does not handle `Σ_l`
over an unspecified index range, so "general `N`" rests on the recorded argument *"one generic
pairwise `(i,l),(j,l)`, summed over `l`"* plus instantiation at `N = 2, 3`. That is a human
argument between two machine-checked links, and it is the step carrying "for all `N`".

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
| **BRK.8** | Step 1 — geometric smoothness of a core piece | ✓ **DONE, std-3** — `MSAMixtureBreakpointScheme.contDiff_gForm`: each core piece `gForm` (polynomial + exponentials) is `ContDiff ℝ ⊤` (entire), so the core's only interior knot is the geometric `|λ_ij|` where `matCoreUneq` switches pieces |
| **BRK.9** ⭐⭐ | Step 2 — `K`-independence of the knot set (`K` enters only the amplitudes; the indicators `1_{[λ,σ]}` carry no `K`, so `∂ⁿ_K Q` keeps knots ⊆ `{λ,σ}`) | **abstract half DONE** (`MSAMixtureBreakpointOrders.contDiffOn_paramDeriv_coeffBasis`, std-3): `K` in coefficients only ⇒ every `∂ⁿ_K (Σ_k c_k(K)·b_k)` is `ContDiffOn` on the basis's smooth set — no new knot. **CONCRETE half DONE** (`MSAMixtureBreakpointScheme.gForm_paramDeriv_contDiffOn`, std-3): now that MSAEMIX.4 Stage 3 (`MSAMixtureCoreUneq`) supplies both pieces as the single form `gForm` in the shared 7-basis `{1,r,r²,r³,r⁴,e^{∓zr}}` with K-free boundaries (inner = `c2=c3=c4=0`), the abstract lemma instantiates on that basis ⇒ every `∂ⁿ_K` of the core form is `ContDiffOn` on each piece — no interior knot beyond `|λ_ij|` at any order. Only residual input = amplitudes `ContDiff` in `K` (BH root, carried as an explicit hyp) | ✓ **DONE — both halves, std-3.** Step 2 proved, not assumed, on both sides (abstract `contDiffOn_paramDeriv_coeffBasis` + concrete against Stage 3's `MSAMixtureCoreUneq`) |
| **BRK.10** | Step 3 — convolution knot closure `knots(f⋆g) ⊆ knots f + knots g` (⟵ BRK.1) | Mathlib `support_convolution_subset` (+ mixture's `*_contDiffOn_*` for endpoints) | ✓ point |
| **BRK.11** | Step 4 — the `σ_l` cancellation (⟵ BRK.2) | `MSAMixtureBreakpoints.breakpoints_sigma_l_free` (std-3) | ✓ done, point |
| **BRK.12** | Step 5 — every order: `∂ⁿ_K c` keeps its knot set `{|λ_ij|}` | ✓ **DONE, std-3** — `MSAMixtureBreakpointScheme.coreForm_paramDeriv_contDiffOn`: `∂ⁿ_K` of the core `c = gForm/(2π r)` (`matCoreUneq`) is `ContDiffOn` away from `r=0`, every order ⇒ no interior knot beyond `|λ_ij|`. ⭐ **the closed-form core (Stage 3) makes the `n`-fold convolution/Leibniz resummation UNNECESSARY** — it follows from BRK.9 + the smooth `1/(2π r)` factor, not MA.16's `∂ⁿ` of a convolution |

**Completable now:** BRK.10, BRK.11 (pointers to existing green lemmas), BRK.12's `n=1` base — recorded
above. **The gap left for MSEMIX:** BRK.9 (Step 2), the K-independence of the *concrete* BH-root `Q` at
unequal σ / general N = MSAEMIX.4 Stage 3. The full assembly (BRK.10+11+12 ⇒ all-orders knot set,
*conditional on* BRK.8+9) is the remaining new Lean, gated on BRK.9 — write it once Stage 3 supplies
the piecewise-with-`K`-free-boundaries form of `Q`, so Step 2 is proved, not assumed, on both sides.

### ⭐ Connected to the concrete Stage-3 core `matCoreUneq` (2026-08-22)

The BRK.8/9/12 lemmas above are about the *abstract* piece form `gForm` / `gForm/(2π r)`. With
MSAEMIX.4 Stage 3 now complete (`MSAMixtureCoreUneq.matCoreUneq` = the concrete 2-piece exact-MSA core,
`K`-free geometric split at `lamA σ i j = |λ_ij|`), they are discharged **against the actual core**
in `MSAMixtureBreakpointScheme.lean` (all std-3 `[propext, Classical.choice, Quot.sound]`):

* `matCoreUneq_contDiffOn_inner` / `_outer` — value level: `matCoreUneq` is `ContDiffOn ℝ ⊤` on
  `(0,|λ_ij|)` and on `(|λ_ij|,σ_ij)` (each piece reduces to `gForm/(2π r)`, `r ≠ 0`).
* `matCoreUneq_smooth_off_absLam` ⭐ — capstone: for `σ_i,σ_j>0`, `σ_i≠σ_j`, `matCoreUneq` is smooth
  on all of `(0,σ_ij)` except at the single interior breakpoint `|λ_ij|`, which MSAEMIX.5's
  `interior_breakpoint_eq_absLam` shows is the **unique** `σ_l`-free interior crossing.
* `matCoreUneq_paramDeriv_contDiffOn_inner` / `_outer` ⭐ — all orders: with every amplitude
  `ContDiff` in `K` (BH root, explicit hyps), every `∂ⁿ_K matCoreUneq` is `ContDiffOn ℝ ⊤` on each
  side of `|λ_ij|`. So no order, and no intermediate species, adds a knot beyond `|λ_ij|`, **about
  the actual Stage-3 core** — not just the abstract `gForm`. (The amplitude-`ContDiff`-in-`K` facts
  reduce to `unfold cC*; fun_prop`.)

⚠ **The one link still carried numerically:** that this closed-form `matCoreUneq` *equals* the Baxter
convolution `−Q'_ij + Σ_l ρ_l Q'_il ⋆ Q_jl` — MSAEMIX.4 Stage 3's symbolic-`σ` derivation, validated
to `1e-14`. A Lean proof of that identity is a separate piecewise-convolution task (define real `Q`,
its supports, differentiate under the integral) and is *not* what BRK closes; BRK now gives the knot
structure **of `matCoreUneq` as defined**.

---

## ⭐⭐ POLICY (2026-08-24, user): one consolidated axiom, everything else a **seam**

> *能归约到的公理全部归约到一起，其他的全部用 seam。*

Two rules, and they are not the same rule:

1. **Reducible ⇒ reduce.** If axiom `B` is a specialisation of axiom `A`, `B` is *deleted* and
   re-proved from `A`. The footprint shrinks to one entry, not two related ones.
2. **Irreducible ⇒ seam, not axiom.** Anything else is carried as an **explicit hypothesis**
   on the theorems that need it, with the external certificate named in the docstring.
   `#print axioms` then stays std-3 and the assumption is visible in the *signature* rather
   than hidden in the environment.

⭐ **Rule 2 already has precedent in this very group.** BRK.8–12 need "the BH-root amplitudes
are `ContDiff` in `K`" and carry it as an explicit hyp — `MSAMixtureBreakpointScheme` is std-3
throughout. That is the pattern to generalise, not a special case.

**Test for a new `axiom`:** it is admissible only if the statement is needed by *many*
downstream results *and* cannot be threaded as a hypothesis without infecting every signature
in the file. Failing either test, it is a seam.

### ⛔ DECLINED (user, 2026-08-24): the equal-σ / unequal-σ pair is **kept as two**

*……算了，等径-不等径这两个我还真不打算彻底归约到一起……*

Rule 1 is **not** applied to this pair. The sizing below is retained as reference — it is
correct, and it is what makes the cross-check in the next section cheap — but AXCON.1–3 are
**not scheduled**. Reasons to keep them separate, recorded so this is not revisited blindly:

- **The two axioms have independent certificates.** Equal σ rests on `msaemix_core_coeffs.py`
  (five coefficients, held-out residual ~1e-12); unequal σ on `symbolic_{outer,inner}.py`
  (per-piece kernels, 1e-14). Deriving one from the other **spends** that independence instead
  of banking it: a common-mode error in the unequal-σ derivation would then be invisible
  everywhere.
- **It would re-route the clean chain through the fragile one.** `MSAMixtureFinOne`'s `N = 1`
  results currently reduce to the scalar `msaCoreCorr` directly. Under consolidation they would
  travel through a 2-piece 7-basis object whose inner piece is *empty* at equal σ — strictly
  more machinery to reach a strictly weaker-stated result.
- **The count is not the point.** Two axioms of the *same kind*, each root-gated and each
  separately certified, are not "over-adding axioms" in the sense rule 1 targets. Rule 1 exists
  to stop a family from growing one axiom per special case; it is not a mandate to minimise the
  integer.

⇒ Both stay. Rule 2 (seam, not axiom, for everything new) is **unaffected** and remains in force.

### Reference only — how the reduction would go, and the cross-check it makes cheap

`MSAMixtureBHRoot.lean:137`  `axiom matExactMSA6_hcore   … (hσ : ∀ i, sigma i = sig) …`
`MSAMixtureBHRootUneq.lean:113`  `axiom matExactMSAUneq_hcore … ` — **no `hσ`**, fully general in σ

Same statement, two σ-generalities; the unequal-σ one is strictly stronger. **Not being done**
— see the DECLINED box above. What survives is the *last clause*: the reduction's algebra is
also a cross-check of two independently derived coefficient sets, and that check is worth
running on its own, **in sympy, with no Lean and no consolidation**. Kept as the single live
item of Group AXCON in `todo/to_Lean.md`.

### The algebra (reference), and the part still worth running

At `∀ i, σ i = sig`: `lamA σ i j = |edgeLo σ i j| = 0`, so `matCoreUneq`'s `if r ≤ lamA` is
**false for every `r > 0`** — the inner piece is empty and only the OUTER `gForm` survives on
`(0, σ_ij)`. Both sides are then single-piece and the whole reduction is one algebraic identity.
Clearing the `1/(2π r)`:

```
cC0o + cC1o·r + cC2o·r² + cC3o·r³ + cC4o·r⁴ + cEmo·e^{−zr} + cEpo·e^{zr}
  = 2π[ c₁·r + c₂·r² + c₃·r⁴ + c₄(1−e^{−zr}) + c₅·coshRatio(z,r) ]
```

Matching in the 7-basis `{1, r, r², r³, r⁴, e^{∓zr}}` (independent on an interval):

| basis element | obligation |
|---|---|
| `r³` | ⭐ **`cC3o = 0` at `a = b`** — the one with content |
| `r`, `r²`, `r⁴` | `cC1o = 2π c₁`, `cC2o = 2π c₂`, `cC4o = 2π c₃` |
| `1`, `e^{−zr}`, `e^{+zr}` | `c₄(1−e^{−zr}) + c₅·coshRatio` reproduces `cC0o, cEmo, cEpo` |

⚠⚠ **The K-elimination is unavoidable.** `matMSACoreCorr` takes `K` **explicitly** (`coreC5 =
−(8π²/z²) Σ_l Σ_m ρ_l ρ_m Gt_il K_lm Gt_jm`); `matCoreCorrUneq` has **no `K` argument** — `K`
reaches it only through `AVec`/`qpMat`/`Wt`/`Ct`. So the two can only agree *at a root*, with
`K` eliminated by (29′) `Σ_l Dt_il(δ_lj − ρ_l Q̂_jl(z)) = 2πK_ij/z`. Same gating the axioms
already carry, so nothing new is assumed — but it means the identity is not a free-variable
`ring` identity even in sympy: `K` must be substituted out first.

### ⛔⛔ RESULT (2026-08-24): the cross-check FOUND A BUG — `matExactMSA6_hcore` is FALSE for `sig ≠ 1`

**Script:** [`../check_core_sigma_powers.py`](../check_core_sigma_powers.py) (3 stages, self-contained).

The corroboration check was expected to agree. It did not. Two independent `σ = 1` hardcodes:

| # | defect | file | status |
|---|---|---|---|
| 1 ⭐⭐ | `coshRatio` has **σ hardcoded to 1** | `YukawaOZ/MSACoreTransform.lean:78` | **SCALAR layer** — not a mixture bug |
| 2 | `c1pair`/`coreC1` short **three σ powers** | `MSAMixtureCore.lean:64` | mixture layer |

**(1)** `coshRatio z r := ½(e^{z(r−1)} + e^{−z(r+1))}) − e^{−z}`. Correct is
`½(e^{z(r−σ)} + e^{−z(r+σ)}) − e^{−zσ} = e^{−zσ}(cosh zr − 1)` — the published form is off by the
constant `e^{−z(σ−1)}`. ⭐ **Visible structurally, with no numerics:** `coreCorrection (c1..c5 z
sigma) r` *takes* `sigma`, uses it for the `if r ≤ sigma` support boundary, and then calls
`coshRatio z r` **without passing it**. Python carries the identical hardcode in
`msaemix_hcore_cert.basis_transforms` term `I5` (`np.exp(-z)` where `sig` belongs) — which is
exactly why the two implementations agree with each other and both pass at `σ = 1`.

**(2)** In `c1pair`: `A_l²` has `1/6` (should be `σ³/6`), `A_l q'_jl` has `−1/2` (should be
`−σ²/2`), `A_l C̃_jl` has `1` (should be `σ`). Residual against `cC1o` is
`Σ_l ρ_l[(s³−1)(A²−A₀²)/6 − (s²−1)(Aq'_j − A₀q'⁰_j)/2 + (s−1)AC̃_j]`, ≡ 0 at `σ = 1`.

**`c2, c3, c4, c5` are correct at every σ** — `c2`/`c3` by exact symbolic match against
`cC2o`/`cC4o`; `c4`/`c5` by least-squares fit. `c5`'s ratio published/fitted reproduces
`e^{z(σ−1)}` to six digits at σ = 1.4 and 2.0, pinning the whole `c5` discrepancy on the basis
function rather than on `c5`'s formula.

**Measured** (the equal-σ certificate's *own* held-out harness, N = 2 and 3):

| σ | published | c1 fixed | basis fixed | **both** |
|---|---|---|---|---|
| 1.0 | 8.5e-12 | 8.5e-12 | 8.5e-12 | 8.5e-12 |
| 0.8 | 3.6e-01 | 1.8e-01 | 1.8e-01 | **4.4e-09** |
| 1.4 | 2.2e+00 | 9.5e-01 | 1.3e+00 | **9.6e-11** |
| 2.0 | 9.0e+00 | 4.1e+00 | 4.9e+00 | **3.5e-09** |

⚠ **Neither repair alone suffices; both together restore it.** A half-fix would have looked
like progress and still left an O(1) error.

#### ⭐⭐ It is a SCOPING problem, on a different axis from the `fff009a` rename

`fff009a` renamed the pair `matExactMSA6_hcore → matExactMSAEqualDiam_hcore`,
`matExactMSAUneq_hcore → matExactMSAUnequalDiam_hcore`, flagging the **equal vs unequal**
diameter axis. The defect is on the orthogonal axis — **unit vs general** diameter — so the
rename does not close it:

- `matExactMSAEqualDiam_hcore` still binds `sig : ℝ` **free**; nothing in the chain pins it.
- `matExactMSAEqualDiam_kspace_residual` (`MatExactMSAEqualDiamCertificate.lean:59`, new in
  a159cf3) binds `(z sig : ℝ)` too ⇒ **inherits the same defect one layer down.**

⭐ **And `coshRatio` is not a bug in its own layer.** The scalar development is unit-diameter *by
construction*: `msaCoreCorr (Dt G K : ℝ)` takes **no σ argument at all**, and `exactMSA_hcore`
uses `cMSAtail K z 1` — a literal `1`. So `coshRatio z r` is a correct **unit-diameter** object
whose *name and signature do not say so*, and the fault is that the mixture's `coreCorrection`
— which does carry `sigma`, and uses it for the support boundary — consumes it at free `sig`.
A σ=1-only helper reached by a σ-general caller.

#### ⭐⭐⭐ BEST FIX (user, 2026-08-24): a SCALING LEMMA — no pinning, no coverage gap

*等径情况应该是可以约化为 sigma=1 的，相当于选定直径作为单位长度……应该可以用单位分析完美解决.*

At equal diameters σ is a free choice of length unit, so the general-`sig` statement is the
σ = 1 statement **pulled back**, and every σ-power found above is a unit conversion. Read off
`coreCorrection` directly with `c̃(r̃) = c(σ r̃)`, `z̃ = zσ`, `ρ̃ = ρσ³`, `K̃ = K/σ`:

```
c̃₁ = c₁      c̃₂ = σ c₂      c̃₃ = σ³ c₃      c̃₄ = c₄/σ      c̃₅ = c₅/σ
```

⭐ **The corrected `coshRatio` is exactly the scale-INVARIANT one:**
`e^{−zσ}(cosh zr − 1) ↦ e^{−z̃}(cosh z̃ r̃ − 1)`. The published `e^{−z}(cosh zr − 1)` is not.
So the defect is not an arithmetic slip — it is a **broken covariance**, and dimensional
analysis determines the repair uniquely rather than by guesswork.

**Verified** (same reduced system re-expressed at three diameters; ratio of each coefficient to
its predicted rescaling, corrected basis):

| σ | c₁ | c₂ | c₃ | c₄ | c₅ | |
|---|---|---|---|---|---|---|
| 1.4 | 1.0000 | 1.0001 | 0.9998 | 1.0000 | 0.9997 | true core |
| 1.4 | **0.9082** | 1.0001 | 0.9998 | 1.0000 | 0.9997 | published |
| 2.0 | **0.8175** | 1.0001 | 0.9998 | 1.0000 | 0.9997 | published |
| 2.0 | 1.0000 | 1.0001 | 0.9998 | 1.0000 | 0.9997 | c₁-repaired |

⇒ **`c₂..c₅` are already scale-covariant**; `c1pair` is the sole formula that breaks it.
⭐ **Two independent routes agree:** the `c₁` correction derived from `cC1o` (the unequal-σ
kernels) is exactly the one the scaling law demands — the three σ-powers are over-determined.

**The resulting plan, strictly better than pinning:**

1. Give `coshRatio` its `σ` (or replace it by the scale-invariant form) and thread it from
   `coreCorrection`; fix `c1pair`'s three kernels. ⚠ Without these the scaling lemma is **false
   as the code stands** — it is the prerequisite, not an alternative.
2. State the axiom at **σ = 1** (matching the scalar layer, which is unit-diameter by
   construction — honest, and the narrowest thing actually certified).
3. **Derive** the general-`sig` equal-diameter statement from it as a *theorem* via the scaling
   lemma. No coverage gap, and — importantly — **no dependence on the in-progress
   unequal-diameter development**.

⚠ Still true regardless: `radial_fourier_coreCorrection`'s closed form integrates this basis
function, so its σ-dependence must be re-derived, not re-typechecked. The scaling lemma is
also the cheapest way to *check* that re-derivation.

#### The fallback if the scaling lemma stalls: pin the equal-diameter axioms to UNIT diameter

Rename `EqualDiam → UnitDiam` on both axioms and add `hsig : sig = 1` (or drop `sig` and use `1`),
matching the scalar layer's convention. This removes the false statement immediately, which is
the part that cannot wait.

**What it costs: the equal-but-non-unit-σ case, TEMPORARILY.** `matExactMSAUnequalDiam_hcore`
carries no `hσ` and so covers that case in principle — `lamA σ i j = 0`, inner piece empty on
`r > 0`, outer kernels live — ⚠ **but the unequal-diameter development is still in progress
(user, 2026-08-24)**, so this is *deferred* coverage, not free coverage. Do not write the
pinning up as lossless; write it as "σ ≠ 1 at equal diameters is carried by the unequal-diameter
route once that lands".

⭐ **The deferred coverage is at least verified to be sound** — by this very check. `c1-fixed`
*is* `cC1o` at `a = b = σ`, and it matches the exact factor-product core to 7 digits at σ = 1.4
and 2.0 (stage 3, `fit/fixed = 1.0000`); `cC2o`, `cC4o` match `coreC2`, `coreC3` symbolically at
general `a = b = s`. So the unequal-diameter *kernels* are demonstrably right at equal σ ≠ 1;
what is outstanding is the Lean development around them, not their correctness.

⚠ **Nothing downstream is waiting on it.** The paper cites none of these declarations (`grep`
over all `.tex`: no `exactMSA`, `coreCorrection`, `coshRatio`, `msaCoreCorr`, `matMSACoreCorr`),
and every numerical result in the tree is in reduced units with σ = 1. So the gap is real but
currently unloaded.

Repairing `coshRatio`/`c1pair` to be σ-general (option B) is the alternative, but it touches the
scalar layer and forces `radial_fourier_coreCorrection`'s closed form to be re-derived. Pinning
is strictly cheaper and leaves no false statement anywhere.

#### ⚠⚠ What this means for the axiom

`matExactMSA6_hcore` is stated for an **arbitrary** common diameter `sig` (`hσ : ∀ i, sigma i =
sig`, with `sig` a free variable) and its RHS is `radial_fourier (matMSACoreCorr …)`. With
either defect present the identity is **false for `sig ≠ 1`**. So it is not an unproven-but-true
axiom: **as stated it is refuted**, and anything derived from it is unsound off `sig = 1`.
Sound options: add `sig = 1` to the axiom, or land both repairs.

⭐ **The unequal-σ axiom `matExactMSAUneq_hcore` is NOT affected.** `cC0o..cEpo` carry `a`, `b`
explicitly in every kernel and `matCoreUneq` never calls `coshRatio`. This is precisely why the
comparison worked: the two derivations were genuinely independent.

⚠ **Blast radius of (1) reaches the scalar layer.** `coshRatio`/`coreCorrection` are used by
`YukawaOZ/MSAFullFactorization.lean` (`msaCoreCorr`, the `N = 1` core), `ExactMSACertificate.lean`,
`MatExactMSAEqualDiamCertificate.lean`, `MSAMixtureCore.lean`. Whether the scalar results are
affected depends on whether their σ is free or pinned to 1 — **check before repairing**, and check
`radial_fourier_coreCorrection`'s closed form too, since it integrates this basis function.

⚠ **This is the exact failure `feedback_sigma_one_masks_bugs` was written about**, one commit
after it caught a spurious σ-factor in `qhatMixC`'s C̃ box (5ded95d). The note says: validate every
term at σ ≠ 1 and at unequal σ. The equal-σ certificate ran `sigma=[1,1]`, `[1,1,1]`, `[1,1]`.

### ⭐ Why the cross-check was the right instrument (retained)

`coreC1..coreC5` (`msaemix_core_coeffs.py`, held-out residual ~1e-12) and `cC*o`
(`symbolic_outer.py`, 1e-14) are **two independent symbolic derivations of the same object**.
Each was validated against its own numerical target; **neither has ever been compared to the
other.** Keeping the axioms separate is precisely what makes that comparison informative — it
stays a genuine second opinion rather than a tautology.

Specialise `cC3o` to `a = b` and confirm it vanishes, then `cC1o/2π` against `coreC1`. Minutes.

- **agree** ⇒ the two certificates corroborate each other, and *that* is the thing to say in
  the paper — stronger than either residual alone, and it costs no Lean.
- **disagree** ⇒ a discrepancy between two certified derivations, which must be resolved before
  either axiom is trusted further. ⚠ This outcome is not hypothetical enough to skip the check:
  the two agree only up to the `K`-elimination via (29′), so a sign or factor error in that
  substitution would show up here and nowhere else.

### What stays a seam, explicitly

`matCoreUneq` = the Baxter convolution `−Q'_ij + Σ_l ρ_l Q'_il ⋆ Q_jl` — MSAEMIX.4 Stage 3's
symbolic-σ derivation, validated to 1e-14. Under rule 2 this does **not** become a third axiom.
It is the certificate *behind* `matExactMSAUneq_hcore`, and the paper says so in words.

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

## ✅ DONE (BRK.13) — the closure seam, discharged by the MSAEMIX group (grade 2)

**✅ DONE (grade 2) — MSAEMIX supplied the hypothesis; BRK is closed about the physical core.**
Discharged 2026-08-24 (commit `175b6cc`, `MSAMixtureBaxterConv.lean`, out-of-`defaultTargets` lib
`MSAMixtureBaxterConvCertificate`). It defines the real-space `baxterQ` / `baxterQ'` and the physical
core `baxterConvCore = (−Q'_ij + Σ_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt)/(2π r)`, states the grade-2 seam
axiom `baxterConvCore_eq_matCoreUneq` (`c = matCoreUneq` on the two open pieces, orientation
`σ_j ≤ σ_i`), and feeds it into the scaffolding below. Verified — independent `#print axioms` of
`baxterConvCore_smooth_off_unique_breakpoint` /
`baxterConvCoreK_paramDeriv_contDiffOn_{inner,outer}` =
`[propext, Classical.choice, Quot.sound, baxterConvCore_eq_matCoreUneq]`; a normal `lake build`
stays std-3 (the lib is out of the `LeanCode` root). The two-grade record below is the plan; grade
2 was taken (grade 1 = the exactMSA-class infeasible convolution ring).

**The hypothesis.** That the physical exact-MSA core `c` — the real-space Baxter convolution
`(−Q'_ij + Σ_l ρ_l Q'_il ⋆ Q_jl)/(2π r)` — equals the closed form `matCoreUneq` on `(0, σ_ij)`.
This is MSAEMIX.4 Stage 3's symbolic-`σ` derivation, validated to `1e-14`
(`symbolic_{inner,outer}.py` / `verify_{inner,outer}.py`).

**What BRK already ships against it** — `MSAMixtureBreakpointScheme.lean`, all std-3
`[propext, Classical.choice, Quot.sound]`; the hypothesis enters as a *typed argument*, never an
axiom:

- `contDiffOn_off_absLam_of_eqOn` — value level. Consumes
  `hc_in : EqOn c matCoreUneq (Ioo 0 (lamA σ i j))` and
  `hc_out : EqOn c matCoreUneq (Ioo (lamA σ i j) (edgeHi σ i j))`.
- `exactCore_smooth_off_unique_breakpoint_of_eqOn` ⭐ — same two, plus MSAEMIX.5's
  `interior_breakpoint_eq_absLam`: `c` smooth on `(0, σ_ij)` except the *unique* interior
  breakpoint `|λ_ij|`.
- `paramDeriv_contDiffOn_{inner,outer}_of_eqOn` — all orders. Consumes the `K`-family identity
  `hcK : ∀ r, (fun K => cK K r) = (fun K => matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r)`

**What discharges it** (this task, MSAEMIX-owned): define the real-space Baxter `Q` + the core `c`
(and its `K`-family `cK`), then close `hc_in` / `hc_out` / `hcK`. Two grades, matching the POLICY:

1. **Prove** `c = matCoreUneq` — define `Q`, its supports, differentiate under the integral ⇒ BRK
   closes **unconditional std-3**. Heavy: a piecewise-convolution integral identity.
2. **Or** assert it as one sympy-backed axiom, mirroring the `hcore` certificate's
   `matExactMSAEqualDiam_kspace_residual` ⇒ BRK closes **std-3 + one convolution-identity axiom**
   (the seam collapsed to a single named numerical fact — the POLICY's "one consolidated axiom").

**Wiring cost on the BRK side once supplied: one line** — feed the discharged hypothesis into
`exactCore_smooth_off_unique_breakpoint_of_eqOn` / `paramDeriv_..._of_eqOn`. ⚠ Do **not** define a
parallel `Q` / `c` on the BRK side: that duplicates MSAEMIX.4 Stage 3's object and carries
false-axiom risk (`feedback_mirror_reference_semantics` — a wrong `def` + `= matCoreUneq` builds
green, only reading the sympy reference catches it). The `Q` / convolution `def` is Stage 3's.

---

## ⭐ BRK.14 / BRK.15 — the all-orders result by MATHEMATICAL INDUCTION (alternative proof, 2026-08-26)

The all-orders "in-core breakpoints all at `|λ_ij|`, no other breakpoints" result
(`matCoreUneq_paramDeriv_contDiffOn_{inner,outer}`, BRK.9/12) is proved above via the
**coefficient/basis separation** — a *one-shot* (`contDiffOn_paramDeriv_coeffBasis`) that cites
Mathlib's `iteratedDeriv_fun_sum` / `iteratedDeriv_const_mul`, with no explicit induction.  On
request, this is the **explicit-induction** proof of the same result, new file
`YukawaOZMix/MSAMixtureBreakpointInduction.lean` (all std-3, `#print axioms` verified; wired into
`LeanCode.lean`, build green).

- **BRK.14 ✅ — `iteratedDeriv_coeffBasis_eq` (the crux, by induction on `n`).**  For a `K`-free
  `r`-basis `b k`: `∂ⁿ_K (Σ_k c k(K)·b k(r)) = Σ_k (∂ⁿ_K c k)(K)·b k(r)`.  **Base** `n=0`:
  `iteratedDeriv 0 = id`.  **Step** `n→n+1`: `∂^{n+1}=∂∘∂ⁿ` (`iteratedDeriv_succ`), then `∂`
  distributes over the finite sum (`deriv_fun_sum`; each summand differentiable via
  `ContDiff.differentiable_iteratedDeriv`) and past the `K`-constant `b k r` (`deriv_mul_const`),
  giving `∂^{n+1}_K c k`.  Re-derives, by hand, exactly what the one-shot delegates to Mathlib.

- **BRK.15 ✅ — the chain, by induction.**  `contDiffOn_paramDeriv_coeffBasis_byInduction` (abstract
  Step 2, same statement as the one-shot but built on BRK.14) →
  `gForm_paramDeriv_contDiffOn_byInduction` (the 7-basis `{1,r,r²,r³,r⁴,e^{∓zr}}` instantiation) →
  `coreForm_paramDeriv_contDiffOn_byInduction` (÷ `2π r`) →
  `matCoreUneq_paramDeriv_contDiffOn_{inner,outer}_byInduction` (the actual BRK result, off each side
  of `|λ_ij|`).  Same statements as the scheme's, std-3.

**Verdict.**  Induction WORKS and is clean here — precisely because `K` enters only the amplitudes
`c k(K)`, never the `r`-basis or the boundary `|λ_ij|`, so the inductive step never moves a knot.
That is the *same* structural reason the one-shot works; the induction just makes the amplitude
bookkeeping explicit (base + step) instead of delegating to `iteratedDeriv_fun_sum`.  ⚠ This is an
**alternative** proof of an already-`DONE` result (BRK.9/12) — redundant for the theorem, kept as the
requested induction-form demonstration.  (The genuinely *different* induction would be the
Leibniz/convolution route — `knots(f⋆g) ⊆ knots f + knots g` (BRK.1) applied `n` times to the raw
Baxter convolution, BRK.7 Step 5 — which the closed form made unnecessary, BRK.12.)

---

## ☐ BRK.16 — axiom-REDUCTION: prove `baxterConvCore`'s breakpoints DIRECTLY (drop the sympy axiom)

**Goal.**  `baxterConvCore_smooth_off_unique_breakpoint` currently = std-3 + the sympy axiom
`baxterConvCore_eq_matCoreUneq` (breakpoints transferred from the closed form).  Prove the SAME
breakpoint structure DIRECTLY from the convolution `baxterConvCore = (−Q'_ij + Σ_l ρ_l Q'_il ⋆
Q_jl)/(2π r)`, making the breakpoint claim **std-3**.  Legitimate because the breakpoint is
*structural* — interior knot `= |λ_ij|`, a support-edge geometric fact, independent of the
coefficient VALUES; the closed form is not needed for it.  (The axiom stays for the value claims.)

**Structural reduction (key).**  `baxterQ' = d/dr baxterQ`, so `∫ Q'_il(t+r) Q_jl(t) dt =
d/dr ∫ Q_il(t+r) Q_jl(t) dt` (differentiate under the integral, MA.16).  Hence `baxterConvCore·2π r`
is the `r`-derivative of a `Q⋆Q` convolution; ContDiffOn on a piece follows from the `Q⋆Q`
convolution being ContDiffOn there (a `deriv` of `ContDiffOn ⊤` is `ContDiffOn ⊤`).

**⚠ Feasibility (2026-08-26): the FULL hard route — existing infra does NOT reuse.**  The MML.8/DCF
convolution smoothness (`qpConv_contDiffOn_upper/_lower`, `matCorrFull_contDiffOn_*`) is for
`q0MixEntry` — the PY-HS factor, a QUADRATIC of COMPACT support `[λ,R]`, no exponential.  But
`baxterConvCore` uses `baxterQ` — the exact-MSA factor with an EXPONENTIAL tail (→∞).  So the `Q⋆Q`
smoothness must be re-proved for the exp-tailed `baxterQ` from scratch (infinite-tail integrals) —
exactly the BRK.7-Step-5 route the closed form was introduced to avoid.

**Sub-tasks.**
- BRK.16a — `baxterQ`/`baxterQ'` piecewise smoothness (ContDiffOn on each open piece; `fun_prop`).
- BRK.16b ⭐⭐ **(load-bearing)** — `∫ Q_il(t+r) Q_jl(t) dt` ContDiffOn on `(0,λ_ij)` and
  `(λ_ij,σ_ij)`: split the exp-tailed integrand at the knots; differentiate under the integral off
  the knot-alignment `r`-values.  The hard analytic core (no existing infra).
- BRK.16c — `Q'⋆Q = d/dr(Q⋆Q)` (MA.16) ⇒ `baxterConvCore` ContDiffOn off `|λ_ij|`.
- BRK.16d — `∂ⁿ_K` all orders (amplitude/geometry separation, BRK.14-style) + `breakpoints_sigma_l_free`
  (BRK.2, std-3) ⇒ interior knot `= |λ_ij|` only, std-3.

**Status (smoothness route): SCOPED.**  Research-scale; drops the axiom from the breakpoint
sub-result only.  SUPERSEDED as the primary target by the VALUE-identity route below, which retires
the axiom ENTIRELY (value ⇒ smoothness).

### BRK.16 — the VALUE-identity route (retire the axiom entirely, 2026-08-26)

**Goal (stronger).**  Prove `baxterConvCore = matCoreUneq` on the two core pieces DIRECTLY, retiring
the sympy axiom `baxterConvCore_eq_matCoreUneq` completely (not just its breakpoint corollary) —
`baxterConvCore_smooth_off_unique_breakpoint` and all downstream then become std-3.

**Key reduction (per-`l`, load-bearing insight).**  `matCoreUneq` KEEPS `∑_l ρ_l·(…)` EXPLICIT with
**σ_l-free per-`l` kernels** (`MSAMixtureCoreUneq.lean` docstring, lines 21–25).  So the seam splits
by `Finset.sum_congr` into:
- **(a) diagonal** `−Q'_ij(r) = gForm(diagonal coeffs)(r)` — ✅ **DONE** (`neg_baxterQ'_eq_diag`,
  std-3).  Matches `cC0i`/`cC1i`/`cEmi` diagonal terms exactly on the core support; NO integral.
- **(b) per-`l` convolution** `∫ Q'_il(t+r) Q_jl(t) dt = gForm(kernel_l)(r)` — the SOLE remaining
  seam, ONE identity (parametrised by amplitudes `qp_il,A_l,Wt_il,Ct_il / qp_jl,A_l,Wt_jl,Ct_jl` and
  diameters `σ_i,σ_j,σ_l`), on each piece.  The `∑_l` and `ρ_l`-weights wrap trivially.

**Feasibility CORRECTION.**  The `MSAMixtureBaxterConv.lean` docstring calls this "the same class as
the MSAEXACT.6 hcore ring (measured infeasible)".  That conflates two objects: the infeasible one is
the **k-space degree-22** ring reassembly (`project_msaexact6_ring_infeasible`).  The **real-space**
per-`l` convolution (b) is instead the **MML.8/MRS.5 class** — poly⋆exp closed forms whose primitives
ALREADY EXIST as the concurrent session's `MixtureRealSpace.lean` (`integral_poly_exp_conv`,
`integral_quadratic_exp_conv`; poly⋆poly = `integral_quad_mul_quad`).  Tractable, not ring-infeasible.

**Progress.**
- ✅ BRK.16a — `baxterQ`/`baxterQ'` piecewise `ContDiffOn ⊤` (foundation).
- ✅ BRK.16b item 1 — integrability: `baxterQ_integrable`, `baxterQ'_bounded`, `baxterQ'_measurable`,
  `baxterConvIntegrand_integrable` (exp-tail handled; each `∫_l` well-defined).
- ✅ BRK.16b diagonal half — `neg_baxterQ'_eq_diag` (part (a) above).
- ◐ BRK.16b part (b) — the per-`l` convolution closed form.  The whole EVALUATION INFRASTRUCTURE is
  now BUILT + validated (all std-3, `MSAMixtureBreakpointConvDirect.lean`):
  - ✅ `baxterConv_eq_setIntegral_Ici` — support reduction `∫_ℝ = ∫_{[edgeLo σ j l,∞)}`.
  - ✅ ordering lemmas (`edgeLo_lt_edgeHi`, `edgeLo_lt_edgeHi_sub_r`, `edgeHi_lt_edgeHi_sub_r_inner`,
    `edgeHi_sub_r_lt_edgeHi_outer`, `lamA_eq_of_le`) — the inner/outer 3-region geometry
    (`Lj < Hj < Hi−r` inner, `Lj < Hi−r < Hj` outer; middle flips at `r = |λ_ij|`).
  - ✅ `setIntegral_Ici_split3` — the 3-way split (two bounded pieces + improper tail).
  - ✅ interval primitives `integral_exp_linear`/`integral_id_mul_exp`/`integral_sq_mul_exp`
    (`∫ tᵏe^{ct}`, k=0,1,2, antiderivative+FTC).
  - ✅ `integral_tailtail` — the `tail·tail` region closed form (pure `e^{−2zt}` → `integral_exp_mul_Ioi`).
  - ✅ `canonAntider`/`canonAntider_hasDerivAt`/`integral_canonical` — the canonical bounded-region
    integral `∫_a^b (cubic + quadratic·e^{−zt} + K·e^{−2zt})`; the single evaluator all 3 bounded
    regions reduce to.  (`HasDerivAt.congr_deriv` sidesteps the convert/instance plumbing.)
  - ☐ REMAINING: (i) the 3 bounded-region reductions — pointwise-rewrite each branch product into the
    canonical integrand (atom-basis split + `ring`, à la `integral_tailtail`'s `hpt`), giving explicit
    `cᵢ/dᵢ/K`, then `integral_canonical`; (ii) 2 assembly theorems (inner/outer) — `setIntegral_Ici_split3`
    + `Ioc/Icc → a..b` + sum the 3 region values; (iii) the final `= gForm(kernel_l)(r)` match where the
    σ_l-dependence CANCELS (`field_simp;ring`, exp atoms); (iv) wrap `∑_l` (`sum_congr`) + diagonal
    (`neg_baxterQ'_eq_diag`) + `/2πr` ⇒ `baxterConvCore = matCoreUneq`, retiring the axiom.
  Mechanical/downhill now (infra done, technique validated on `tail·tail`); still multi-session for the
  coefficient bookkeeping.  ⚠ overlaps concurrent MSAEMIX Group MRS — coordinate.

  **⭐ END-TO-END SYMBOLIC VALIDATION (`scripts/verify_baxterconv_decomposition.py`, 2026-08-26).**
  The 3-region decomposition sums EXACTLY to the `matCoreUneq` per-`l` kernel on BOTH pieces
  (`INNER diff = 0`, `OUTER diff = 0`, `sympy.simplify`), with the σ_l dependence CANCELLING.  So the
  Lean identity `baxterConvCore = matCoreUneq` is a TRUE, `ring`-closable identity region-by-region;
  the pins are: INNER `[Lj,Hj]`,`[Hj,Hi−r]`,`[Hi−r,∞)`; OUTER `[Lj,Hi−r]`,`[Hi−r,Hj]`,`[Hj,∞)`.
  Also measured: the core·core pointwise `ring` (full ~20-term canonical coeffs) closes in 7 s ⇒ the
  Lean region reductions are computationally feasible (NOT k-space-ring-infeasible).  The remaining is
  pure transcription/assembly of a validated identity: state each region's pointwise-to-canonical
  (`integral_canonical`) / tail (`integral_tailtail`), sum over the 3 regions, `ring`-match the kernel.

  **BUILT since (all std-3, committed):**
  - ✅ ALL 3 bounded-region pointwise-to-canonical identities: `region_corecore_pointwise`,
    `region_coretail_pointwise`, `region_tailcore_pointwise` (branch product = `cubic + quadratic·e^(−zt)
    + K·e^(−2zt)`; sympy coeffs, atom-split + `ring`, ~7 s each; `set_option maxHeartbeats 800000`).
  - ✅ branch-eval lemmas (`baxterQ_core_eq`, `baxterQ_tail_eq`, `baxterQ'_shift_core_eq`,
    `baxterQ'_shift_tail_eq`) + `edgeLo_sub_r_lt_edgeLo` + `setIntegral_Icc_eq_uIcc`/`_Ioc_eq_uIcc`.
  - ✅ **region-evaluation chain validated END-TO-END** on core·core with the real `baxterQ`/`baxterQ'`:
    `∫_{Icc Lj Hj} baxterQ'·baxterQ` → (Icc→interval) → (branch congr) → (`region_..._pointwise` congr)
    → `integral_canonical` (coefficients inferred by unification, no re-typing).  The `rw` chain works.
  - ✅ `scripts/verify_baxterconv_decomposition.py`: `R1+R2+R3 − target = 0` via the ACTUAL
    `sympy.integrate` region integrals (not just the kernel form).

  **REMAINING (mechanical wiring of validated pieces):**
  1. inner/outer per-`l` theorems: `baxterConv_eq_setIntegral_Ici` → `setIntegral_Ici_split3` → the 3
     region evals (R1 core·core, R2 core/tail, R3 tail·tail via `integral_tailtail`) → sum.
  2. the final-match `ring`: `simp only [canonAntider]`, split all `e^(±z·edge)` to the half-atom basis
     `{e^(zσᵢ/2),e^(zσⱼ/2),e^(zσₗ/2),e^(zr/2)}`, `field_simp; ring` (validated true; empirically confirm
     it closes in reasonable time — the one thing left to measure).
  3. wrap: `∑_l ρ_l` (`Finset.sum_congr`) + diagonal (`neg_baxterQ'_eq_diag`) + `/2πr` ⇒
     `baxterConvCore = matCoreUneq`, retiring the axiom (whole physical core → std-3).
