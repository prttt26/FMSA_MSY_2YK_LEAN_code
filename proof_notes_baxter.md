# Proof Notes: Group BAXTER — Baxter Q-Factor Foundations

Detailed proof records for Group BAXTER: Baxter's classical real-space Q-factor identity and its
real-`k` Wiener–Hopf factorization — the foundational machinery reused by every downstream group
below. This group depends on Group OZ's definitions and results (`oz_h`, `c_HS`, `radial_fourier`,
`oz_core_closure`, etc.); Group OZ does not depend on anything here. See `todo_lean.md` for task
status summary.

Split off from `proof_notes_oz.md`/`proof_notes_hard_sphere.md`'s old Group OZ (which had grown
to 18 tasks, 1455 lines) once this sub-family's own scope — pole existence/asymptotics for an
exponential-polynomial entire function, residue calculus, `OzFixedPt` construction — turned out
to need genuinely different (complex-analysis) machinery from the rest of Group OZ. Task IDs
below were renumbered from their original `OZ.*` names to the `BAXTER.*` prefix (matching how
`Group OZ`/`Group F`/`Group M`/`Group B` all have their ID prefix match their group name); the
renumbering is recorded in each task's own text where it was originally introduced under the old
name.

**Group split by topic, 2026-07-15.** Group BAXTER itself grew to 15 task numbers spanning
several genuinely unrelated mathematical areas (real-space Q-factor, contact-value derivation,
complex-analytic pole/residue construction, `h_explicit`/`OzFixedPt` assembly), so it was split
into four independent groups, each with its own ID prefix and its own proof-notes file. **Group
BAXTER itself is now slimmed to just the foundational `BAXTER.1`–`3`** (this file); everything
else moved out, per the mapping below (old ID → new ID → new group/file):

| Old ID | New ID | New Group | File |
|---|---|---|---|
| `BAXTER.1` | `BAXTER.1` | `BAXTER` (unchanged) | this file |
| `BAXTER.2` | `BAXTER.2` | `BAXTER` (unchanged, historical staging pointer) | this file |
| `BAXTER.3` | `BAXTER.3` | `BAXTER` (unchanged) | this file |
| `BAXTER.4` | `CONTACT.1` | `CONTACT` | `proof_notes_contact.md` |
| `BAXTER.5` | `CONTACT.2` | `CONTACT` | `proof_notes_contact.md` |
| `BAXTER.6` | `CONTACT.3` | `CONTACT` | `proof_notes_contact.md` |
| `BAXTER.7` | `CONTACT.4` | `CONTACT` | `proof_notes_contact.md` |
| `BAXTER.8` | `CONTACT.5` | `CONTACT` | `proof_notes_contact.md` |
| `BAXTER.9` | `POLE.1` | `POLE` | `proof_notes_pole.md` |
| `BAXTER.10` | `POLE.2` | `POLE` | `proof_notes_pole.md` |
| `BAXTER.11` | `POLE.3` | `POLE` | `proof_notes_pole.md` |
| `BAXTER.12` | `POLE.4` | `POLE` | `proof_notes_pole.md` |
| `BAXTER.14` | `POLE.5` | `POLE` | `proof_notes_pole.md` |
| `BAXTER.13` (`B.0`–`B.4`) | `OZFIX.1`–`OZFIX.4` | `OZFIX` | `proof_notes_ozfix.md` |
| `BAXTER.15` (`B.3`(outer)/`B.5`/`B.6`/`B.7`) | `OZFIX.5`–`OZFIX.8` | `OZFIX` | `proof_notes_ozfix.md` |

`BAXTER.13`/`BAXTER.15` are retired outright — no pointer stub kept at those numbers; this table
is the single source of truth for where old IDs went. See each new file's own header for its
group's scope and dependencies.

## Group BAXTER — Baxter Q-Factor & Wiener–Hopf Factorization Foundations

### Task BAXTER.1 — Baxter real-space convolution identity *(formerly Task OZ.5)*

**Statement (Wertheim 1963; Baxter 1970; [chsY] Eq. 46):**

For `r ∈ (0, σ)`, the PY hard-sphere DCF satisfies the real-space Wiener-Hopf identity:
```
2π·ρ·r·c_HS(r) = ∫_r^σ q0_poly(r'−r)·q0_poly'(r') dr' − q0_poly'(r)
```
where:
- `q0_poly(r) = α·(r−σ) + β·(r−σ)²/2` with `α = ρ·q_prime_py`, `β = ρ·q_doubleprime_py`
- `q0_poly'(r) = α + β·(r−σ)` is the derivative of q0_poly w.r.t. r
- `q0_poly = 2πρ·Q` where Q is the Wertheim Q-function for diameter σ

**Physical origin (Wertheim 1963):** The Wiener-Hopf factorization `1−ρĈ(s) = Q̂(s)Q̂(−s)` gives
the real-space identity `−r·c(r) = Q'(r) − 2πρ ∫_0^{σ-r} Q(t)·Q'(t+r) dt`. With Q = q0_poly/(2πρ)
and Q' = q0_poly'/(2πρ), multiplying by −2πρ and changing variables t → r'−r gives the Lean form.

**Numerical verification at η=0.4, σ=1, r=0.5, ρ=2.4/π:**

| Quantity | Value |
|---|---|
| 2πρ·r·c_HS(0.5) (LHS) | 2π·(2.4/π)·0.5·(−295/24) = −29.5 |
| q0_poly'(0.5) = α+β(r−σ) | 4 |
| ∫_r^σ q0_poly(r'−r)·q0_poly'(r') dr' | −25.5 (exact via antiderivative) |
| RHS = −25.5 − 4 | −29.5 ✓ |

**In Lean:** `baxter_factorization_inner` in `LeanCode/HardSphere/BaxterRealSpace.lean`:
```lean
theorem baxter_factorization_inner {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (_heta0 : 0 <= eta) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ r ∈ Set.Ioo 0 sigma,
    2 * Real.pi * rho * r * c_HS eta sigma r =
    (∫ r' in r..sigma, q0_poly eta sigma rho (r' - r) *
      (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r' - sigma))) -
    (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r - sigma))
```

**Proof approach (polynomial FTC + ring):**
1. Rewrite integral via `integral_congr`: substitute `q0_poly_inner` + `← hα_def`, `← hβ_def`.
2. Compute `∫_r^σ q0_poly(r'−r)·q0_poly'(r') dr'` via FTC on the 7-term degree-4 antiderivative:
   ```
   F(x) = α²/2·(x−σ−r)² + αβ/3·(x−σ)³ − αβr/2·(x−σ)² + αβ/6·(x−σ−r)³
         + β²/8·(x−σ)⁴ − β²r/3·(x−σ)³ + β²r²/4·(x−σ)²
   ```
3. Apply `HasDerivAt` chain (7 terms) + `integral_eq_sub_of_hasDerivAt`; F(σ) evaluates cleanly.
4. Substitute η = π·ρ·σ³/6; clear denominators with `field_simp [hsigma.ne', h1e]`; close by `ring`.

**Key Lean 4 patterns:**
- `HasDerivAt.congr_of_eventuallyEq` takes ONE explicit arg → `refine (hchain.congr_of_eventuallyEq ?_).congr_deriv ?_`
- `Filter.Eventually.of_forall` (not the deprecated `Filter.eventually_of_forall`)
- After `rw [q0_poly_inner ..., ← hα_def, ← hβ_def]`, the `integral_congr` goal closes automatically (no `ring` needed)

**Prerequisites:**
- `q0_poly_inner`, `c_HS_inner` (proved, `proof_notes_hard_sphere.md` Group OZ)
- `q_prime_py`, `q_doubleprime_py` (defined)
- `eta = pi*rho*sigma^3/6` (`heta_def`)

**Note on `hParseval` (Task F.4):** This is the **hard-sphere** Baxter identity.  Task F.4's
`hParseval` is a **Yukawa** Baxter identity: `∫_0^d b_ij(r)dr = K(1+A)²/z` where `b_ij(r)` is
the chsY inner-core function from [chsY] Eq. 41.  That requires a separate task using `I1`/`I2`
integrals and the MSA closure for `A`.

**Status:** ✓ PROVED — `LeanCode/HardSphere/BaxterRealSpace.lean`, no sorry.

---

### Task BAXTER.2 — Re-derive Baxter's second relation (Route B) from a primary source *(formerly Task OZ.11)*

**Statement (as originally recorded, found broken — see below):**
```
r·h(r) = -Q'(r)/(2π) + ρ·∫₀^σ Q(t)·(r-t)·h(|r-t|) dt      for r > 0
```
where `Q(t) = q_prime_py·(t-σ) + q_doubleprime_py·(t-σ)²/2` for `0≤t≤σ` (0 outside) — the
same `Q` underlying `q0_poly`/`BAXTER.1` (`q0_poly(t) = ρ·Q(t)`; this relation uses `Q` itself).
*If* correctly derived, this would unlock `g0_HS_contact_value` (specializing at `r=σ`) and
reproduce `oz_core_closure` as a corollary rather than a direct axiom — more powerful and closer
to Baxter's actual classical derivation than Route A's direct axiom.

**Depends on:** Task `BAXTER.3` — **now DONE** (`BaxterWienerHopf.lean`, no sorry/axiom). Baxter's
second relation is classically *derived from* the Wiener–Hopf factorization `(1-ρQ̂(k))(1-ρQ̂(-k))
=1-ρĈ_sine(k)`, not independent of it.

**2026 — checked whether `BAXTER.3`'s factor is the canonical (zero-free) one; initial check was
wrong, corrected version says yes.** The classical Wiener–Hopf/residue-calculus construction of
`h(r)` needs `1-ρQ̂(k)` to be **zero-free** in the physically-relevant half of the complex
`k`-plane (the "outer function" property) — that's what lets the splitting argument pin down
`Ĥ(k)` via a Liouville-type gluing. A first pass checked the **upper** half-plane and found zeros
(`k≈-12.197+2.892i`, confirmed via winding number and direct root-search) — but that was the
wrong half-plane: the physically relevant region, matching the `s=ik`/`Re(s)>0` causal convention
already used elsewhere in this project (`C_HS_laplace`), is the **lower** half `k`-plane
(`Im(k)<0`). Re-checked there: winding number is exactly `0` across `η=0.05`–`0.8` and contour
radii `20`/`50`/`100`, and a direct root-search (`a∈[-30,30]`, `b∈[-30,-0.1]`) finds nothing.
`q0_poly`/`Q_old` (the same function satisfying Relation 1 *and* `BAXTER.3`'s real-axis identity)
is therefore very plausibly the genuine canonical zero-free Baxter factor after all — no need to
construct a separate outer function from scratch.

**Consequence:** the classical splitting argument is concretely describable using machinery
already proved in Lean (`BAXTER.3`):
```
Ĥ(k)(1-ρQ̂(k))(1-ρQ̂(-k)) = Ĉ(k)      [OZ equation × BAXTER.3]
⟹ Ĥ(k)(1-ρQ̂(k)) = Ĉ(k)/(1-ρQ̂(-k))
```
`1-ρQ̂(-k)` is zero-free in the *upper* half-plane (mirror of the result above), so the RHS is
analytic there (`Ĉ` is entire). If the LHS is similarly analytic in the *lower* half-plane, both
sides glue into an entire function, forced to a low-degree polynomial by Liouville's theorem once
growth is bounded — pinning down `Ĥ(k)` exactly.

**2026 — mapped the full zero set; the "one open piece" is more subtle than first stated.**
Extended the root search (not just the single point found first): `1-ρQ̂(k)` has **infinitely
many** zeros in the upper half-plane, in mirrored `±` pairs with slowly increasing imaginary
part as `|Re(k)|` grows (closest pair `k≈±6.058+1.437i`, then `±12.197+2.892i`, `±18.515+3.727i`,
… out past `±502+10.3i`), all confirmed zero-free in the lower half-plane (consistent with the
winding-number result). Checking the ground-truth `h(r)`'s actual decay against this: it does
decay for large `r`, with an oscillating envelope (sign changes, consistent with contributions
from complex-conjugate-pair poles) — but a crude fit to `log|h(r)|` gives a slower rate (~0.5)
than a rough single-pole estimate would suggest, itself consistent with multiple interfering
exponentials rather than one clean rate, as expected given how many poles are this close together.
More importantly, working through *why* `Ĥ(k)(1-ρQ̂(k))` should be lower-half-plane analytic
surfaces a real subtlety I hadn't accounted for: if `Ĥ`'s own poles (wherever `1-ρĈ(k)=0` *and*
`Ĉ(k)` doesn't also vanish there) sit at zeros of `1-ρQ̂(-k)` — which, mirroring the zeros found
above, lie in the **lower** half-plane — then multiplying by `(1-ρQ̂(k))` (zero-free there) does
**not** cancel them, and naively `Ĥ(k)(1-ρQ̂(k))` would still have poles in the lower half-plane,
contradicting what the argument needs. The classical resolution (if it holds here) is that `Ĉ(k)`
has exactly matching zeros at those same points, making them removable rather than genuine poles
— this is a *specific, checkable* claim (`Ĉ(k)=0` wherever `1-ρQ̂(-k)=0` in the lower half-plane).
**Checked directly: it's false.** `Ĉ(k)` at those mirrored points (e.g. `k=-6.058-1.437i`,
`k=6.058-1.437i`, `k=±12.197-2.892i`) evaluates to exactly `1/ρ` in every case (not `0`) — which
is just the algebraic restatement of `1-ρĈ(k)=0` there (forced by `Ĉ(k)=1/ρ`), not a
cancellation. So `Ĥ(k)=Ĉ(k)/(1-ρĈ(k))`, taken as the literal algebraic continuation of the OZ
equation off the real axis, has **genuine poles** in the lower half-plane too — multiplying by
`(1-ρQ̂(k))` (zero-free there) does not remove them, so the naive gluing argument as set up above
does not go through as stated.

**However** — this test implicitly assumed the *true* analytic continuation of `Ĥ(k)` (built from
the actual, physical `h(r)`) literally equals the algebraic expression `Ĉ(k)/(1-ρĈ(k))` once
extended off the real axis. That's exactly the assumption Baxter's classical construction is
built to either justify or route around, not something to take for granted — the real `Ĥ(k)`'s
analytic domain is a property of `h(r)`'s actual decay/support, independent of this algebraic
manipulation, and might not coincide with the naive continuation wherever the two would disagree.

**2026 — reframed: `Ĥ(k)` (sine-transform) is only strip-analytic, and that's the resolution, not
a further obstruction.** `radial_fourier`'s kernel `sin(kr)=(e^{ikr}-e^{-ikr})/2i` mixes both
exponential directions — for complex `k` the defining integral only converges (so `Ĥ` is only
analytic) within a **bounded strip** `|Im(k)|<γ` set by `h(r)`'s actual decay rate `γ`, not an
unbounded half-plane; the earlier framing implicitly assumed the stronger, unjustified claim.
Fit the ground-truth `h(r)`'s tail (`r∈[4,16]`) to a damped-oscillation model
`h(r)≈A·e^{-γr}cos(ωr+φ)` (nonlinear fit, not the earlier noise-prone log-linear one): got
`γ≈1.665`, `ω≈6.066`, matching the closest zero pair of `1-ρQ̂(k)` (`k≈±6.058+1.437i`) almost
exactly in frequency (`6.066` vs `6.058`) with a tiny residual (RMS `4.8×10⁻⁶` against RMS
`|h|≈2.7×10⁻⁴` — the single closest pole pair explains >98% of the tail's variance). This is a
clean, independent confirmation that `Ĥ`'s nearest singularity really is at `Im(k)≈1.44`, exactly
where `1-ρQ̂(-k))=0` predicts, i.e. `Ĥ`'s pole structure (both half-planes) is *fully consistent*
with the meromorphic continuation `Ĥ(k)=Ĉ(k)/(1-ρĈ(k))` — the earlier "genuine poles" finding
isn't a contradiction, it's the **expected, correct** picture once the strip-only framing replaces
the wrong half-plane-unbounded one.

**Consequence — this changes the strategy entirely, in a good way.** Given
`1-ρQ̂(k)`/`1-ρQ̂(-k)` and `Ĉ(k)` are *already fully known in closed form*
(`BAXTER.1`/OZ.8/`BAXTER.3`), `Ĥ(k)=Ĉ(k)/[(1-ρQ̂(k))(1-ρQ̂(-k))]` is a **completely explicit
meromorphic function** — no Liouville/growth argument is needed to "solve for" it; the formula
already *is* the answer, sight unseen. The real remaining question isn't complex-analytic at all:
it's whether the *already-axiomatized* `oz_h` (`Classical.choose` of `oz_fixed_pt_unique`) equals
the function this meromorphic `Ĥ(k)` inverse-transforms to. That's exactly what
`oz_fixed_pt_unique`'s **uniqueness** clause is for: construct `h_explicit(r)` (a residue series
over the known, explicit poles — a sum of decaying exponentials, standard classical PY closed
form), show it satisfies `OzFixedPt` plus the required regularity (bounded, continuous on
`[σ,∞)`), and uniqueness forces `oz_h = h_explicit` — after which `oz_core_closure`/
`g0_HS_contact_value` become direct computations on an explicit, closed-form function, not
further complex analysis. This sidesteps the half-plane-analyticity question entirely rather than
resolving it head-on. **Not yet built** — constructing `h_explicit`, proving convergence of the
residue series (infinitely many poles, found out past `k≈502+10.3i`, growing but with
presumably-shrinking residues — not yet checked), and proving it satisfies `OzFixedPt` is a
substantial further undertaking, but now a concretely-scoped one rather than an open-ended
complex-analysis question. See Task `CONTACT.2` (narrower target, prioritized first) for the
concrete next step, if pursued further.

**History — two bugs found, none from a primary source:** the *first* reconstruction attempted
(from general memory of Baxter 1970, not a primary source) was structurally right but off by a
factor of `2π`, caught and fixed at the time. A 2026 re-examination found two further things:

1. **For `r<σ`, the relation is redundant, not new content.** Every argument `|r-t|` appearing
   on the RHS for `t∈[0,σ]`, `r∈(0,σ)` stays strictly inside `(0,σ)` — i.e. it only ever calls
   `h` where `h≡-1` is *already proved* (`oz_h_core`, no axiom). Substituting `h≡-1` throughout
   (both sides), the relation collapses to a pure polynomial identity in `Q` alone:
   ```
   2πρ ∫₀^σ Q(t)(r-t) dt = 2πr - Q'(r)
   ```
   confirmed to machine precision (~1e-15) at three η (0.1, 0.3, 0.45) and several `r`. This is
   almost certainly provable in Lean by the same `HasDerivAt`+FTC technique as
   `baxter_factorization_inner` — but it supplies **no** new information toward
   `oz_core_closure`: it's automatically satisfied by facts already on record, not an
   independent constraint on `h`.
2. **For `r>σ` — where the relation would need to do genuine work — it does not hold as
   documented.** Built an independent, high-precision ground-truth `h(r)` (exact `sympy`-derived
   closed form for `Ĉ(k) = radial_fourier(c_HS)(k)`, sine-transform inversion
   `h(r) = (1/2π²r)∫₀^∞ k·Ĥ(k)·sin(kr) dk` with `Ĥ=Ĉ/(1-ρĈ)`, `k_max` up to 3000 with 6×10⁵
   points) — first validated that it correctly reproduces the known contact-value jump
   (`h(σ⁻)=-1` → `h(σ⁺)≈(1+η/2)/(1-η)²-1`, η=0.3 gives 1.347, matches). Plugging this ground
   truth into Route B's RHS at `r=1.01,…,1.6` (η=0.3) gives residuals of order 15–27 — large,
   systematic, and *growing* with `r`, not shrinking numerical-truncation noise. Four quick
   variants were tried (reflecting `Q(t)→Q(σ-t)`, bounding the integral at `min(r,σ)` instead of
   `σ`, flipping the sign of the `Q'(r)` term) and none closed the gap, so this is not a one-line
   convention slip — the relation as documented is most likely missing a term or otherwise
   mis-derived. Verification scripts not committed (scratchpad only); rerunnable from this
   description (closed-form `Ĉ(k)` first via `sympy.integrate`, then sine-transform inversion,
   then direct residual check against the relation above).

**Conclusion:** not currently a safe foundation to build on. The redundant `r<σ` sub-case is
fine as a standalone fact but doesn't help; the `r>σ` case, where the actual content would need
to live, fails a direct numerical test. No access to the primary source (Baxter 1970) in this
environment — any re-derivation has to go through first-principles complex analysis /
computer-algebra verification (Task `BAXTER.3`'s own approach, now proved out — see below), not
recalled literature content, which has caused two bugs here already.

**2026 — residue series built and numerically validated; strategy confirmed sound.** Enumerated
poles of `1-ρQ̂(k)` systematically out to `|k|<1000` (318 found, in mirrored `±` pairs, `Im(k_n)`
growing slowly — from `1.44` to `11.7` — consistent with an entire function of exponential type).
Derived the residue formula for `h_explicit(r) = (1/2πr)·Re[Σ_n Res_n]`,
`Res_n = k_n·e^{ik_n r}/[ρ²·Q̂'(k_n)·(1-ρQ̂(-k_n))]` (from closing the sine-transform inversion
contour in the upper half-plane and summing residues of `k·Ĥ(k)·e^{ikr}`). First attempt had a
clean overall sign error — caught by cross-checking one residue against a direct numerical
contour integral (ratio came out to exactly `-1`, not close-but-off, confirming a algebra slip
rather than a deeper problem) — corrected. With the sign fixed, the truncated series (318 pole
pairs) matches the ground-truth `h(r)` solver **closely across the full range tested**:
```
  r      ground_truth   h_explicit    diff
 1.02      1.247569      1.234334   -1.3e-02   (near boundary, slow convergence expected)
 1.05      1.101465      1.095460   -6.0e-03
 1.10      0.885066      0.882216   -2.8e-03
 1.20      0.519896      0.519227   -6.7e-04
 1.50     -0.065677     -0.065815   -1.4e-04
 2.00      0.005711      0.005663   -4.8e-05
 3.00     -0.001837     -0.001851   -1.3e-05
 6.00     -0.000073     -0.000070    2.7e-06
```
Convergence is slower near `r=σ` (both `h_explicit` and the ground truth itself show
Gibbs-phenomenon-like behavior approaching the jump — expected, not a red flag) but the trend as
`r→σ⁺` (checked `r=1.005,1.01,1.02,1.05`) clearly heads toward the known contact value `1.347`,
consistent with both methods converging to the same limit. Away from the boundary (`r≥1.2`), the
match is excellent (relative error `<0.15%`, shrinking further with `r`).

**2026 — quantitative convergence law, and an independent real-space confirmation.** Pushed the
groundwork further (still numerical/analytical only, no Lean):

1. **Pole growth law, precisely characterized.** Extended the enumeration to `|k|<1000` (159
   positive-`Re` poles). `Re(k_n)` spacing converges to *exactly* `2π/σ` (measured `6.2845` vs.
   `2π=6.2832`) — the classical period of the `e^{-ikσ}` term in `Q̂`'s closed form. `Im(k_n)`
   fits `2·ln(Re(k_n)) − 2.12` with RMS residual `0.004` — essentially exact logarithmic growth,
   the standard asymptotic for zeros of an exponential-polynomial entire function (polynomial
   `+` polynomial`·e^{-ikσ}`, which is exactly `Q̂`'s shape). The residue prefactor
   `|k_n/(ρ²Q̂'(k_n)(1-ρQ̂(-k_n)))|` grows like `Re(k_n)^{0.997}` — linearly, to high precision.
   **Combined, term magnitude at radius `r` scales like `n^{1-2r}`**: absolutely convergent for
   every `r>σ` (rate improving with `r`, matching the observed tightening match above), but only
   *marginally* (`~1/n`, borderline conditionally-convergent) exactly at `r=σ` — a precise,
   quantitative explanation for the slow near-boundary convergence already observed, not just an
   empirical curiosity.
2. **Boundary-value acceleration attempted, found genuinely hard, not swept under the rug.**
   Tried Richardson extrapolation in `r→σ⁺` (using the well-converged `r>σ` series) and Cesàro
   averaging of the partial sums in `n` — neither cleanly accelerates convergence to the known
   contact value `1.347`: Richardson's fitted power-law exponent is unstable across successive
   triples (`0.77, 1.02, 1.66`, not a clean single power), and Cesàro averaging barely moves the
   raw partial sums. This is consistent with (not contradicting) the `~1/n` marginal-convergence
   finding above — a simple power-law or Cesàro assumption isn't the right tool for a log-type
   boundary singularity; proper treatment likely needs a bespoke Abel-type summation matched to
   the actual `n^{1-2r}` law, not attempted here.
3. **Independent real-space OZ-equation check — the strongest confirmation yet.** Plugged
   `h_explicit` (residue series for `r≥σ`, spliced with the known `h=-1` core value for `r<σ`)
   directly into the actual real-space exterior OZ equation
   `h(r) = c_HS(r) + ρ·radial3d_conv(c_HS,h)(r)` (the literal statement `OzFixedPt`/
   `oz_h_satisfies_conv_ext` use) via nested numerical quadrature — a check that's *independent*
   of the Fourier-domain ground-truth solver used above (real-space integral, not another
   spectral construction). Result:
   ```
   r      LHS=h_explicit   RHS=ρ·conv(c_HS,h)    rel. error
   1.20     0.519227          0.519490            0.051%
   1.50    -0.065815         -0.065811             0.007%
   2.00     0.005663          0.005663             0.001%
   2.50    -0.001195         -0.001195            ~0.000%
   3.00    -0.001851         -0.001851            ~0.000%
   ```
   Far tighter than Route A's own original numerical check for `oz_core_closure` (~1–2%,
   `proof_notes_hard_sphere.md` Task OZ.9) — strong, independent evidence `h_explicit` genuinely
   satisfies the exterior OZ equation, not just an artifact of matching one Fourier-based
   construction against another.

**Status:** ☐ not started (Lean), but the numerical construction is now validated — genuine,
concrete evidence the residue-series strategy is sound, now including an independent real-space
OZ-equation check (~0.05% at `r=1.2`, `→0.000%` by `r=2.5`, tighter than Route A's own original
`oz_core_closure` check). `BAXTER.3`'s factor confirmed zero-free in the correct (lower)
half-plane; `Ĥ`'s "genuine poles" are the *expected* consequence of it being only strip-analytic
(not a contradiction), and the pole-growth law is now precisely characterized (`Re` spacing
`=2π/σ` exactly, `Im(k_n)~2ln(Re(k_n))`, term decay `~n^{1-2r}`). **Remaining work is now
well-scoped, not open-ended**: (1) prove the residue series converges for `r>σ` (the `n^{1-2r}`
law above is the concrete estimate this needs — boundary case `r=σ` itself needs a separate,
harder argument, not yet found), (2) show `h_explicit` satisfies `OzFixedPt` + regularity, (3)
invoke `oz_fixed_pt_unique`'s uniqueness to get `oz_h=h_explicit`. Still substantial — this would
be new complex-analysis Lean work with no precedent in this project — but the math itself is no
longer in question the way it was earlier in this investigation, and is now backed by three
independent numerical confirmations (ground-truth solver match, pole-growth law, real-space OZ
equation). Deferred behind the narrower `CONTACT.2`, which needs only the `r→σ⁺` limit, not
convergence/`OzFixedPt` for every `r`. **2026 update:** pushed the boundary limit further —
extended pole enumeration to 3000 pairs (`|k|<19000`, seeded by the now-precise growth law) and
tried Shanks-transform acceleration; the raw boundary value stayed `~3–10%` off even with
thousands of terms, confirming (not contradicting) the predicted marginal `~1/n` convergence
right at `r=σ`. This pushed toward a genuinely better route for the contact value specifically —
a real-analysis jump-asymptotic argument on `Ĥ(k)`'s large-`k` behavior that sidesteps the
residue series entirely, checked numerically to 6+ digits and built almost entirely from
already-proved facts. See Task `CONTACT.2`'s 2026 update for the full argument — likely the
better path to `g0_HS_contact_value` specifically, though this task's *full* `h(r)` construction
is still needed for `oz_core_closure`/Route B (this task's own original target) if that's
pursued.

**2026 — scoping pass, Mathlib capability checked; `g0_HS_contact_value` payoff now moot for this
task.** Task `CONTACT.2` (split into `CONTACT.3`/`CONTACT.4`/`CONTACT.5`) succeeded via the
jump-asymptotic route — `g0_HS_contact_value` is now a proved theorem (conditional on explicit
`oz_h` exterior-regularity hypotheses, see `CONTACT.5`), with **no residue series needed at all**.
So this task's only remaining payoff is retiring `oz_core_closure` itself as a *derived* theorem
instead of a numerically-verified axiom — a real but purely axiom-hygiene goal, not blocking
anything else in the project.

Checked what this pass's step (1) above (pole existence/asymptotics for the entire function
`1-ρQ̂(k)=1-ρ[A(k)+B(k)e^{-ikσ}]`, an "exponential polynomial" in the classical
Pólya/Titchmarsh sense) would actually need from Mathlib. `Mathlib/Analysis/Meromorphic/`
(`Divisor.lean`) and `Mathlib/Analysis/Complex/JensenFormula.lean` exist and could help with
*counting* bounds (how many zeros in a disk of radius `R`, via boundary growth), but not
*existence* — the classical tool for that is Rouché's theorem / the Cauchy argument principle.
**Grepped the full Mathlib snapshot (filenames and contents, case-insensitive) for
`winding`/`WindingNumber`/"argument principle": zero hits.** This Mathlib snapshot has no
winding-number or argument-principle machinery at all — the pole-existence proof needed for
step (1) would have to build that infrastructure from scratch on top of Cauchy's integral
formula first, a substantial standalone complex-analysis formalization project in its own right,
*before* any of this task's own residue-series content could begin.

**2026 — deeper reconnaissance: Cauchy's integral formula/circle-integral API exist, but no
residue theorem, Rouché, or argument principle; a lower-risk alternative found.** Checked more
precisely what Mathlib's complex-analysis foundations actually offer:
`Mathlib/Analysis/Complex/CauchyIntegral.lean` has a genuine, usable Cauchy integral formula for
disks (`DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul` and variants), and
`Mathlib/MeasureTheory/Integral/CircleIntegral.lean` has a working circle-integral API
(linearity, `integral_sub_zpow_of_ne : ∮ z in C(c,R), (z-c)^n = 0` for `n≠-1`, `=2πi` for
`n=-1`) — these are the raw ingredients a residue theorem/argument principle would be built from,
but nothing assembles them into either. Also confirmed: there is **no existing `Qhat : ℂ → ℂ`**
definition anywhere in the codebase — `BaxterWienerHopf.lean` only has the real-`k` closed forms
(`q0poly_cos_integral_formula`/`q0poly_sin_integral_formula`); extending to complex `k` is new
work, not a rename.

**Promising lower-risk alternative to Rouché, not yet verified:** this project's own
`OzFixedPtDilute.lean` already proves an existence/uniqueness result via Banach's
contraction-mapping theorem (used for `oz_fixed_pt_unique_dilute`) — trusted, working
infrastructure this codebase already relies on. Each pole of `1-ρQ̂(k)` is individually a
solution of `e^{-ikσ} = (1-ρA(k))/(ρB(k))` near a known-good numerical guess (`Re(k_n)≈2πn/σ`,
`Im(k_n)≈2ln(Re(k_n))-2.12`). For large `n` this is plausibly closeable as a **local
Banach/Newton contraction argument per pole**, reusing the *same* technique already trusted here,
rather than importing/building general argument-principle machinery from scratch. Genuinely
unverified — no Lipschitz bound has been derived or checked yet — but the most promising
lower-risk path found so far, and exactly the kind of claim this project's discipline says to
check numerically/symbolically before writing any Lean for it (see `POLE.2`).

**Status:** ☐ staged, in progress — not attempted wholesale. Split into pure-numeric sub-tasks,
now Group POLE's `POLE.1`–`5` (`proof_notes_pole.md`) plus Group OZFIX's `OZFIX.1`–`8`
(`proof_notes_ozfix.md`) for the final `h_explicit`/`OzFixedPt` assembly, to be attempted in
order with explicit go/no-go checkpoints (the pole-existence step, `POLE.3`, is a genuine open
research question, not a scoped implementation task).

---

### Task BAXTER.3 — Baxter's Wiener–Hopf factorization: `(1-ρQ̂(k))·(1-ρQ̂(-k)) = 1-ρĈ_sine(k)` *(formerly Task OZ.12)*

**Statement:** the transform-domain (structure-factor) factorization underlying Baxter's whole
method — `1-ρĈ_sine(k)` (the real sine-transform of `c_HS`, `radial_fourier(c_HS)(k)`, Task OZ.8,
already known exactly) factors as `(1-ρQ̂(k))(1-ρQ̂(-k))` for real `k`, where `Q̂(k)` is the Fourier
transform (evaluated at `s=ik`) of `Q_old = q0_poly/ρ`, the *same* function
`baxter_factorization_inner` (Task `BAXTER.1`, proved) already uses. **Resolved below** —
originally misstated (wrong sign, wrong axis), now a confirmed closed-form identity.
`baxter_factorization_inner` is this identity's real-space shadow restricted to `r∈(0,σ)`, not
the full transform-domain statement.

**Depended on by:** Task `BAXTER.2` (needs this as its core technique); would plausibly also give
a direct route to `g0_HS_contact_value` via the `r=σ` specialization, independent of `CONTACT.1`.

**What's been tried, found broken (2026):** guessed `Q̂(s) = 1 + q0_poly_laplace(s)` (Laplace
transform of `δ(r)+q0_poly(r)`, using the *already-defined* `q0_poly`/`q_prime_py`/
`q_doubleprime_py`) and checked `Q̂(s)Q̂(-s)` against `1-ρĈ_HS(s)` — **fails**, large and
non-uniform disagreement across `η,σ,s` (e.g. η=0.3, σ=1, s=0.7: guessed product ≈1.50 vs. true
≈1.91; grows far apart at larger `|s|`). Traced analytically to why: Laplace-transforming
Relation 1's double integral `D(r) = ∫_r^σ q0_poly(r'-r)q0_poly'(r')dr'` and swapping
integration order hits the **same triangle-truncation obstruction that already falsified
`radial_laplace_conv`** elsewhere in this project — the inner integral's upper limit is `r'`
(not `σ`), so `D(r)`'s transform is *not* a clean product of two one-sided Laplace transforms;
there's an uncomputed extra term. Directly verified: `L[D(r)-q0_poly'(r)](s)` matches
`L[2πρr·c(r)](s)` exactly (Relation 1 itself Laplace-transforms consistently, as it must), but
`L[D](s)` alone does not equal `q0_poly_laplace(s)·q0p_laplace(-s)` (η=0.3, σ=1, s=0.7: −4.385
vs. −8.149).

A further asymptotic check (`s→+∞`) shows the naive ansatz is even more fundamentally off: for
`Q` with *exact* compact support on `[0,σ]`, `Q̂(-s)=∫₀^σQ(t)e^{st}dt` grows like `e^{sσ}` as
`s→+∞` (dominated by `t` near `σ`), while `1-ρĈ_HS(s)→1`. For `Q̂(s)Q̂(-s)` to match, either the
growing piece must cancel exactly against something in `Q̂(s)`, or the "exact compact support"
ansatz for `Q` itself needs revisiting.

**2026 — resolved: the identity holds on the physical axis `s=ik`, using the *same* `Q` as
Relation 1 (`q0_poly`), with a corrected sign.** The asymptotic problem above is specific to
testing along the real `s` axis; Baxter's factorization is really a statement about the structure
factor, i.e. real `k` via `s=ik`, where `Q̂(-ik)=conj(Q̂(ik))` for real `Q` (bounded, no blow-up)
and the target on the RHS must correspondingly be the **real** sine-transform
`Ĉ_sine(k) = radial_fourier(c_HS)(k)` (Task OZ.8), *not* `C_HS_laplace` evaluated at `s=ik` (which
is complex-valued and can't equal a modulus-squared quantity — checked directly: `C_HS_laplace(ik)`
has a nonzero imaginary part in general, so `Q̂(ik)Q̂(-ik)`, always real for real `Q`, can never
match it).

A first attempt at fixing this (least-squares fit of a general quadratic `Q(t)=c0+c1t+c2t²`
against `|1+Q̂(ik)|²=1-ρĈ_sine(k)`) found *a* valid closed form, but one that didn't satisfy
Relation 1 the way `q0_poly` does — apparently two different `Q`'s, contradicting classical Baxter
theory. **That was a red herring from a second bug, not a real puzzle:** the original naive
attempt (`Q̂=1+q0_poly_laplace(s)`) had the **sign backwards**. Testing the already-defined
`q0_poly`/`Q_old` itself (`Q_old(t)=q_prime_py·(t-σ)+q_doubleprime_py·(t-σ)²/2`, the *same*
function `baxter_factorization_inner` already uses) with the corrected sign:
```
(1 - ρ·Q̂_old(k))·(1 - ρ·Q̂_old(-k)) = 1 - ρ·Ĉ_sine(k)
```
— confirmed **symbolically** (`sympy`, exact, not just numeric): with
```
Re[Q̂_old(k)] = π(ηkσcos(kσ) + 3ηkσ − 4ηsin(kσ) + 2kσcos(kσ) − 2sin(kσ)) / (k³(1-η)²)
Im[Q̂_old(k)] = π(−ηk²σ² − ηkσsin(kσ) − 4ηcos(kσ) + 4η + k²σ² − 2kσsin(kσ) − 2cos(kσ) + 2) / (k³(1-η)²)
```
(derived directly via `sp.integrate(Qold*cos(k*t),(t,0,sigma))`/`sp.integrate(Qold*sin(k*t),...)`,
matching this project's `phi1_real`/`phi2_real`-style moment integrals), the expression
`(1-ρRe)² + (ρIm)² − (1-ρĈ_sine(k))`, after substituting `ρ = 6η/(πσ³)`, `sympy.simplify`s to
**exactly `0`** — a genuine closed-form algebraic identity, not a numerical coincidence. (The
quadratic-fit `Q` from the first attempt was a real but *different* valid factorization —
Wiener–Hopf factorizations of a given real quantity aren't unique without an extra normalization
condition — not a second physical object; it's superseded by this result and not used further.)

Also reconfirmed with the corrected sign: the identity still fails against `C_HS_laplace` on the
general real/complex-`s` axis — it genuinely only lives on `s=ik` against `Ĉ_sine`, as expected
physically (a structure-factor statement, not a general Laplace-domain claim).

**Formalized in Lean (2026) — `LeanCode/HardSphere/BaxterWienerHopf.lean`, no sorry, no axiom.**
`q0_poly`'s Fourier moments reduce to the `{1,r,r²}×{sin,cos}` basis (`q0_poly_inner` is exact on
all of `[0,σ]`, not just a.e., since it only needs `r≤σ`); `ψ1`/`ψ2` (sine, degree 1/2) already
existed in `RadialFourierCHS.lean`, so this file supplies the missing pieces
(`chi0_formula`/`chi1_formula`/`chi2_formula`, cosine degree 0/1/2, and `psi0_formula`, sine
degree 0 — same `HasDerivAt`+FTC technique throughout) plus a generic `{1,r,r²}` assembly helper
(`integral_quadratic_cos`/`integral_quadratic_sin`) reused for both `Re`/`Im`. Main theorem
`baxter_wiener_hopf_factorization`: eliminates `ρ` (not `η`) via `heta_def` so the pre-existing
`(1-η)`-power denominators stay simple, then `field_simp` + `ring_nf` +
(`sin²x=1-cos²x`, applied via a universally-quantified rewrite so it matches regardless of how
`ring_nf` nests/reorders the argument) + `ring` — mirrors `baxter_factorization_inner`'s own
closing technique, just needing the extra Pythagorean step since this identity is genuinely
trigonometric (`Ĉ_sine`), not polynomial-in-`e^{-sσ}` like Relation 1.

**Status:** ✓ **DONE** — closed form found, symbolically confirmed (`sympy`), and formalized as a
genuine Lean theorem: `(1-ρQ̂_old(k))(1-ρQ̂_old(-k)) = 1-ρĈ_sine(k)`, no sorry, no axiom, using the
existing `q0_poly`/`Q_old` (no new function needed).

---

