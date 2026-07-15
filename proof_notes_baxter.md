# Proof Notes: Group BAXTER — Baxter Q-Factor & Wiener–Hopf Route to the PY Closed Form

Detailed proof records for Group BAXTER: Baxter's classical *constructive* method (real-space
Q-factor, Wiener–Hopf factorization, residue calculus, jump asymptotics) for **deriving** —
fully or partially — the results Group OZ's `oz_core_closure`/`g0_HS_contact_value` axioms
currently supply directly (see `proof_notes_hard_sphere.md`, Group OZ). This group depends on
Group OZ's definitions and results (`oz_h`, `c_HS`, `radial_fourier`, `oz_core_closure`, etc.);
Group OZ does not depend on anything here. See `todo_lean.md` for task status summary.

Split off from `proof_notes_oz.md`/`proof_notes_hard_sphere.md`'s old Group OZ (which had grown
to 18 tasks, 1455 lines) once this sub-family's own scope — pole existence/asymptotics for an
exponential-polynomial entire function, residue calculus, `OzFixedPt` construction — turned out
to need genuinely different (complex-analysis) machinery from the rest of Group OZ. Task IDs
below were renumbered from their original `OZ.*` names to the `BAXTER.*` prefix (matching how
`Group OZ`/`Group F`/`Group M`/`Group B` all have their ID prefix match their group name); the
renumbering is recorded in each task's own text where it was originally introduced under the old
name.

## Group BAXTER — Baxter Q-Factor, Wiener–Hopf Factorization & PY Closed-Form Derivations

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
complex-analysis question. See Task `BAXTER.5` (narrower target, prioritized first) for the
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
equation). Deferred behind the narrower `BAXTER.5`, which needs only the `r→σ⁺` limit, not
convergence/`OzFixedPt` for every `r`. **2026 update:** pushed the boundary limit further —
extended pole enumeration to 3000 pairs (`|k|<19000`, seeded by the now-precise growth law) and
tried Shanks-transform acceleration; the raw boundary value stayed `~3–10%` off even with
thousands of terms, confirming (not contradicting) the predicted marginal `~1/n` convergence
right at `r=σ`. This pushed toward a genuinely better route for the contact value specifically —
a real-analysis jump-asymptotic argument on `Ĥ(k)`'s large-`k` behavior that sidesteps the
residue series entirely, checked numerically to 6+ digits and built almost entirely from
already-proved facts. See Task `BAXTER.5`'s 2026 update for the full argument — likely the
better path to `g0_HS_contact_value` specifically, though this task's *full* `h(r)` construction
is still needed for `oz_core_closure`/Route B (this task's own original target) if that's
pursued.

**2026 — scoping pass, Mathlib capability checked; `g0_HS_contact_value` payoff now moot for this
task.** Task `BAXTER.5` (split into `BAXTER.6`/`BAXTER.7`/`BAXTER.8`) succeeded via the
jump-asymptotic route — `g0_HS_contact_value` is now a proved theorem (conditional on explicit
`oz_h` exterior-regularity hypotheses, see `BAXTER.8`), with **no residue series needed at all**.
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
check numerically/symbolically before writing any Lean for it (see `BAXTER.10`).

**Status:** ☐ staged, in progress — not attempted wholesale. Split into pure-numeric sub-tasks
`BAXTER.9`–`BAXTER.13` below, to be attempted in order with explicit go/no-go checkpoints (the
pole-existence step, `BAXTER.11`, is a genuine open research question, not a scoped
implementation task).

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
a direct route to `g0_HS_contact_value` via the `r=σ` specialization, independent of `BAXTER.4`.

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

### Task BAXTER.4 — `g0_HS_contact_value` via OZ.8's Fourier-domain closed form (full residue calculus) *(formerly Task OZ.13)*

**Statement:** OZ.8 (`radial_fourier_c_HS_formula` + `radial_fourier_c_HS_eq_C_HS_laplace_expr`,
both proved, no sorry/axiom, `proof_notes_hard_sphere.md`) gives the Fourier-domain OZ solution
in closed form as a function of `k`. Inverting this back to real space (residue calculus on the
closed-form-in-`k` structure factor, essentially reconstructing the classical PY closed-form
solution for `g0_HS(r)` for *every* `r`, not just the contact point) would give
`g0_HS_contact_value` directly.

**Depends on:** Task OZ.8 (done; this is OZ.8's originally-scoped "Part C", deliberately split
off — see OZ.8's writeup, `proof_notes_hard_sphere.md`) and effectively Task `BAXTER.5`'s
groundwork.

**2026 — not actually independent of Task `BAXTER.2`/`BAXTER.5`, and superseded in priority by
`BAXTER.5`.** The original framing ("a route independent of Task `BAXTER.2`/`BAXTER.3`'s
Baxter-`Q` machinery") was wrong: `BAXTER.3`'s identity `1-ρĈ_sine(k) = (1-ρQ̂(k))(1-ρQ̂(-k))`
holds for all complex `k`, so `Ĥ(k)=Ĉ(k)/(1-ρĈ(k))`'s pole structure is governed by the *same*
factor `BAXTER.2`/`BAXTER.5` analyze — this task shares their analyticity question, not a
separate one. Since this task additionally needs the full inversion (not just the contact-point
boundary data), `BAXTER.5` is strictly smaller and is the one to attempt first.

**2026 — fully subsumed by `BAXTER.2` now, no independent content.** `BAXTER.5` succeeded (split
into `BAXTER.6`/`BAXTER.7`/`BAXTER.8`, `g0_HS_contact_value` now a proved theorem) via a route
that needed *none* of this task's residue-calculus machinery — so the "revisit once `BAXTER.5`
clarifies the analyticity blocker" condition above has resolved in the direction that removes
this task's reason to exist: its narrower payoff (the contact value) is already done elsewhere,
and its only remaining content (full inversion of `Ĥ(k)` back to `g0_HS(r)` for every `r`) is
exactly `BAXTER.2`'s own full scope, not a distinct task. See `BAXTER.2`'s 2026 scoping-pass note
for the Mathlib capability check and staged sub-task split (`BAXTER.9`–`13`).

**Status:** ☐ deliberately parked — no independent content left; fully absorbed into `BAXTER.2`'s
scope. Do not treat as a separate task going forward.

---

### Task BAXTER.5 — `g0_HS_contact_value` from the Wiener–Hopf splitting's boundary data (narrower target) *(formerly Task OZ.14)*

**Statement:** rather than constructing the full `h(r)` for every `r` (Task `BAXTER.2`) or the
full residue-calculus inversion (Task `BAXTER.4` below), extract *just*
`g0_HS_contact_value` from the splitting argument's boundary/Liouville data. This is the actual
target needed for the `oz_core_closure`/`g0_HS_contact_value` axioms and is substantially smaller
than either.

**Depends on:** Task `BAXTER.3` (done — supplies the zero-free factor and the splitting setup).

**2026 — much smaller, purely-real-analysis route found, bypassing the residue series entirely.**
The residue-series construction (Task `BAXTER.2`) was pushed hard this session (pole-growth law,
extended enumeration, Shanks acceleration) and the `r→σ⁺` boundary value proved stubbornly hard
to extract that way — pushing toward a different question: does `Ĥ(k)`'s own large-`k`
asymptotics hand over the contact value directly? They do, via classical real analysis (no
complex analysis, no residue calculus): for a function `f` with a jump `J` at `r=σ`,
`radial_fourier[f](k) = 4πσJ·cos(kσ)/k² + O(1/k³)` as `k→∞`. Confirmed **exactly** (`sympy`, not
just numerically) on two independent test functions (a plain step function; `c_HS` itself via its
full closed-form expansion) — full derivation and numbers in Tasks `BAXTER.6`/`BAXTER.7` below,
where the work is now split into separate, pure-numeric task IDs (this task bundled several
logically distinct pieces of different difficulty, same splitting pattern as
`OZ.9-RouteB`→`OZ.11`–`OZ.14` earlier this session).

**Status:** ✓ **DONE** as a whole — **split into `BAXTER.6`/`BAXTER.7`/`BAXTER.8`** below, all
three now ✓ **DONE** (no sorry/axiom). `BAXTER.8`'s final theorem is conditional on `oz_h`'s
exterior regularity/decay (see `BAXTER.8`'s writeup for the exact, honestly-scoped remaining gap)
— it does not unconditionally retire the `g0_HS_contact_value` axiom, but reduces its truth to
that strictly smaller, physically well-motivated open question.

---

### Task BAXTER.6 — General jump-asymptotic lemma for `radial_fourier` *(formerly Task OZ.15)*

**Statement:** for `f:(0,∞)→ℝ` "nice" (piecewise-`C¹`, exact hypothesis still to be pinned down)
with a jump of size `J` at `r=σ` (i.e. `f` has one-sided limits `f(σ⁻)`, `f(σ⁺)` with
`f(σ⁺)-f(σ⁻)=J`), `radial_fourier f k = 4πσJ·cos(kσ)/k² + O(1/k³)` as `k→∞`. A reusable, abstract
real-analysis fact — no reference to `oz_h` or `c_HS` — matching how OZ.6
(`radial_fourier_conv`, `proof_notes_hard_sphere.md`) is a general transform-theory fact
independent of any specific function.

**Confirmed exactly (not just numerically) on two independent test functions before attempting
Lean:**
- **Plain step function.** `f(r)=𝟙_{r<σ}` (jump `J=-1`) has
  `radial_fourier[f](k) = -4πσ·cos(kσ)/k² + 4π·sin(kσ)/k³` **exactly** (`sympy`, elementary
  closed form, no approximation). Leading term matches `4πσJ·cos(kσ)/k²` exactly; the *entire*
  remainder is exactly the `4π·sin(kσ)/k³` term.
- **`c_HS`, via full symbolic expansion of the already-proved closed form
  (`radial_fourier_c_HS_formula`, Task OZ.8).** The `cos(kσ)` coefficient is an *exact*, finite
  series in **even** powers of `1/k`:
  `4πσ(α0+α1+α3)/k² − 8π(α1+6α3)/(σk⁴) + 96πα3/(σ³k⁶)` (no further terms — `c_HS` is an exact
  cubic, so this is a closed algebraic expansion, not an open-ended asymptotic tail); the
  `sin(kσ)` coefficient is exact in **odd** powers: `−4π(α0+2α1+4α3)/k³ + 96πα3/(σ²k⁵)`. So the
  remainder past the leading `1/k²` term is exactly `−4π(α0+2α1+4α3)·sin(kσ)/k³ + O(1/k⁴)` — the
  **same `O(1/k³)` rate as the step function**, on a wholly unrelated test case. Cross-checked
  numerically too (residual `×k³/sin(kσ)` converges to the predicted `34.80` at `η=0.3` by
  `k=3200`, matching to `<0.3%`).
- **Physical meaning of the `1/k³` coefficient — not identified.** `α0+2α1+4α3` doesn't obviously
  match `c_HS`'s derivative jump (`c_HS'(σ⁻)=-(α1+3α3)/σ`) or its value at the origin
  (`c_HS(0)=-α0`); not needed for `BAXTER.5`'s own target (only the leading term matters), flagged
  as an open, lower-priority question (e.g. relevant if this technique is ever extended toward
  `oz_core_closure`/`BAXTER.2`).

**The main open risk, as originally stated:** the two test cases above both have `f≡0` for `r>σ`
(compact support ending exactly at the jump). `oz_h` does **not** — it's the full, nontrivial
exterior solution for `r>σ`. The standard theory says a jump still dominates the large-`k`
asymptotic *provided* `f` is suitably regular and decaying on `(σ,∞)`, but `oz_fixed_pt_unique`
currently only gives **boundedness**, not decay/regularity, for `oz_h`'s exterior branch.

**2026 — resolved via a genuine real-analysis proof, with the risk correctly identified and then
honestly isolated (not assumed away).** The general lemma **is now proved** (no sorry/axiom) as
`radial_fourier_jump_asymptotic` in `HardSphere/JumpAsymptotic.lean`, for `f` equal to a constant
`c` on `(0,σ)` and equal to `g` on `(σ,∞)`:
`k² · (radial_fourier f k - 4πσ(g(σ)-c)·cos(kσ)/k²) → 0` as `k → ∞` — a `Tendsto`/`o(1/k²)`
statement rather than the originally-hoped explicit `O(1/k³)` bound (see below for why `o(1/k²)`
turned out to be exactly what's needed, no more, no less). Built from three independently-proved
pieces:
- **`tendsto_integral_mul_cos_sin_atTop`** — real `cos`/`sin` Riemann–Lebesgue lemma, `k→∞`, for
  `h∈L¹(ℝ)`. Derived from Mathlib's *general* Riemann–Lebesgue lemma
  (`Real.tendsto_integral_exp_smul_cocompact`, `Analysis/Fourier/RiemannLebesgueLemma.lean`) —
  contrary to the original note above, Mathlib *does* have this (searched under the wrong name
  the first time); unpacked via the circle-valued Fourier character into real `cos`/`sin`,
  restricted `cocompact ℝ` to `atTop` (`atTop_le_cocompact`), reparametrized `w↦k=2πw`.
- **`ibp_ioi_identity`/`right_piece_asymptotic`** — the exterior `(a,∞)` piece: one integration by
  parts (`HasDerivAt`+FTC, using Mathlib's `integral_Ioi_of_hasDerivAt_of_tendsto'` for the
  improper-integral boundary term at `+∞`) turns `∫_{(a,∞)} r g(r) sin(kr) dr` into a boundary
  term `a g(a) cos(ka)/k` plus `(1/k)∫(g+rg')cos(kr)dr`; Riemann–Lebesgue then makes the *second*
  term genuinely `o(1/k)`, not just `O(1/k)` — this is what makes `o(1/k²)` achievable with only
  **one** IBP (not two/C², as originally estimated), under **4 clean, `k`-independent
  hypotheses**: `g` differentiable on `[a,∞)`, `r·g(r)→0`, and `r·g(r)`/`g(r)+r·g'(r)` both
  absolutely integrable on `(a,∞)`.
- **`radial_fourier_split`/`left_piece_const`** — the interior `(0,σ)` piece splits off exactly
  (measure-zero boundary point) and, for `f≡c` constant there (`oz_h`'s actual shape), is
  computed in **exact closed form** via the already-proved `psi1_formula` (Task OZ.8) — no
  asymptotic argument needed on that side at all.

**Why `o(1/k²)` (not the originally-hoped `O(1/k³)`) turned out to be exactly sufficient:**
`BAXTER.8`'s actual argument doesn't need matching *rates* on both sides of the leading-coefficient
comparison — it needs `(k²·radial_fourier[f](k)) - 4πσJ·cos(kσ) → 0` as a genuine limit, then
evaluates that limit along the explicit subsequence `k_n=2πn/σ` (where `cos(k_nσ)=1` identically)
to conclude `J` is pinned down exactly — no density/equidistribution argument, no rate comparison,
needed. See `BAXTER.8` below.

**Status:** ✓ **DONE** — `radial_fourier_jump_asymptotic`, genuine theorem, no sorry/axiom, in
`HardSphere/JumpAsymptotic.lean`.

---

### Task BAXTER.7 — Concrete closed-form asymptotic of `Ĥ(k)` *(formerly Task OZ.16)*

**Statement:** `Ĥ(k) = Ĉ(k)/(1-ρĈ(k))` has leading large-`k` asymptotic
`4πσ(α0+α1+α3)·cos(kσ)/k² + O(1/k³)`, hence (via the already-proved algebraic identity
`py_f1_eq`, `HardSphere/PYDCF.lean`: `α0+α1+α3=(1+η/2)/(1-η)²`) leading coefficient
`4πσ(1+η/2)/(1-η)²` — numerically `29.4925` at `η=0.3,σ=1`, matching this session's direct
numerical check to 6+ significant figures.

**Proof sketch (pure algebra/limits on already-proved closed forms — no new technique):**
1. `Ĉ(k)→0` as `k→∞` (immediate from `radial_fourier_c_HS_formula`'s explicit `1/k²`-and-higher
   form), so `1/(1-ρĈ(k)) = 1+O(Ĉ(k)) = 1+O(1/k²)` — the correction doesn't disturb the leading
   `1/k²` order of `Ĥ(k)` relative to `Ĉ(k)`.
2. Read the `cos(kσ)/k²` coefficient directly off `radial_fourier_c_HS_formula` (already proved,
   `RadialFourierCHS.lean`) — this session's full symbolic expansion (see `BAXTER.6`) already has
   it in closed form.
3. Apply `py_f1_eq` (already proved) to simplify `α0+α1+α3` to `(1+η/2)/(1-η)²`.

**Depends on:** `radial_fourier_c_HS_formula` (Task OZ.8, done), `py_f1_eq` (`PYDCF.lean`, done).
Independent of `BAXTER.6` — can proceed immediately.

**Status:** ✓ **DONE** — proved as `Hhat_closed_asymptotic` in
`HardSphere/RadialFourierCHS.lean` ("Piece C"), no sorry/axiom. Formalized as an explicit,
threshold-based bound rather than `Asymptotics.IsBigO` (matching this codebase's established
style of carrying side conditions explicitly, e.g. `S0`/`oz_laplace_oz_eq`'s `hne`, rather than
via Mathlib's asymptotic-filter API, which this project had not used before): for
`k ≥ 1+2|ρ|·cHS_bound(η,σ)`,
`|Ĥ(k) - 4πσ(α0+α1+α3)·cos(kσ)/k²| ≤ (2|ρ|·cHS_bound(η,σ)² + 4π·cHS_remainder_bound(η,σ))/k³`.
Built from the ground up: `radial_fourier_c_HS_remainder_eq` (exact algebraic identity for
`Ĉ(k)`'s remainder, cross-checked with `sympy` before the Lean write-up),
`cHS_remainder_bracket_bound`/`radial_fourier_c_HS_remainder_le` (explicit `O(1/k³)` bound on
`Ĉ(k)`'s remainder), `radial_fourier_c_HS_le` (`Ĉ(k)=O(1/k²)`), then `Hhat_closed` (`:=
Ĉ(k)/(1-ρĈ(k))`) and the final bound via `Ĥ-Ĉ = ρĈ²/(1-ρĈ)` combined with a self-contained
(no external hypothesis) derivation that `|1-ρĈ(k)| ≥ 1/2` for `k` past the threshold. All
constants (`cHS_bound`, `cHS_remainder_bound`) are explicit closed-form functions of `η,σ`, not
existentials — directly usable by `BAXTER.8`.

---

### Task BAXTER.8 — Assembly: `g0_HS_contact_value` from `BAXTER.6`+`BAXTER.7` *(formerly Task OZ.17)*

**Statement:** apply `BAXTER.6` to `f=oz_h` — jump `J=oz_h(σ)+1=g0_HS(σ)` at `σ` (using
`oz_h_core`, already proved, for the `-1` core value) — giving
`radial_fourier[oz_h](k) ~ 4πσJ·cos(kσ)/k²` (as a genuine `Tendsto`/`o(1/k²)` statement).
Separately identify `radial_fourier[oz_h](k)` with `Ĥ(k)=Hhat_closed` via
`oz_fourier_oz_eq_of_PY_core` (Task OZ.9b: `H·(1-ρC)=C`, so `H=C/(1-ρC)` whenever `1-ρC≠0`), then
transfer `BAXTER.7`'s asymptotic across that identification. Match the two resulting asymptotic
expansions of the *same* function `radial_fourier[oz_h](k)`: their leading coefficients must
agree, forcing `J=(1+η/2)/(1-η)²` — closing the axiom.

**2026 — DONE, conditionally on `oz_h`'s exterior regularity/decay.** Proved as
`g0_HS_contact_value_of_oz_h_regularity` in `HardSphere/JumpAsymptotic.lean`, no sorry/axiom.
The "uniqueness of the leading coefficient" step turned out not to need any
`Filter.Tendsto`/`Asymptotics.IsBigO` uniqueness *lemma* from Mathlib — it's proved directly
(`eq_zero_of_tendsto_mul_cos`) by evaluating the difference-of-asymptotics `Tendsto` statement
along the explicit subsequence `k_n=2πn/σ` (`cos(k_nσ)=cos(2πn)=1` identically), reducing
"`A·cos(kσ)→0` as `k→∞`" directly to "`A=0`" via uniqueness of limits
(`tendsto_nhds_unique`) — no density/equidistribution machinery needed.

**Assembly, concretely (all pieces already proved, no new machinery in this step):**
1. `hFactA`: `radial_fourier[oz_h](k)=Hhat_closed(k)` for `k` past the same explicit threshold
   `BAXTER.7`'s own proof uses (`one_sub_rho_mul_radial_fourier_c_HS_ne_zero`, extracted from
   `Hhat_closed_asymptotic`'s proof as its own reusable fact, `RadialFourierCHS.lean`),
   transferred across `BAXTER.7`'s `Hhat_closed_asymptotic_tendsto` (the explicit-bound
   `Hhat_closed_asymptotic` repackaged as a `Tendsto`, pure squeeze argument).
2. `hFactB`: `BAXTER.6`'s `radial_fourier_jump_asymptotic` applied directly to `f:=oz_h`, `c:=-1`.
3. `hFactB.sub hFactA` + `eq_zero_of_tendsto_mul_cos` ⟹ `oz_h(σ)+1 = (1+η/2)/(1-η)²` (via
   `py_f1_eq`) ⟹ `g0_HS(σ) = (1+η/2)/(1-η)²`.

**Honest remaining gap — what "conditionally" means:** the final theorem's hypothesis list
carries, as explicit premises (not derived): (a) `oz_h`'s exterior branch is differentiable on
`[σ,∞)` with some derivative `g'`; (b) `r·oz_h(r)→0` as `r→∞`; (c) `r·oz_h(r)` and
`oz_h(r)+r·g'(r)` are absolutely integrable on `(σ,∞)`; (d) `oz_fourier_oz_eq_of_PY_core`'s six
"routine integrability" hypotheses, now for *all* `k>0` (not just one fixed `k`). None of these
are proved elsewhere in this codebase — they are genuinely open, physically well-motivated
(real OZ correlation functions decay) facts about `oz_h`, carried explicitly rather than silently
assumed, exactly matching how `oz_fourier_oz_eq_of_PY_core` itself already carries its six
hypotheses.

**2026-07-15 — the bare `g0_HS_contact_value` axiom is now RETIRED (Task OZ.3 closed).** The
"conditionally" above is now discharged at the axiom level, not just described: the hypothesis
bundle (a)–(d) is packaged as a single named axiom `oz_h_exterior_regularity`
(`JumpAsymptotic.lean`, existential over the exterior derivative `g'`), and
`theorem g0_HS_contact_value` (same name, same namespace `FMSA.HardSphere`, same statement
`g0_HS(σ)=(1+η/2)/(1-η)²` as the retired axiom) is proved unconditionally by feeding
`oz_h_exterior_regularity`'s witnesses into `g0_HS_contact_value_of_oz_h_regularity`. The old bare
`axiom g0_HS_contact_value` (a direct physical-number assertion) is **deleted** from
`PYOZ_GHS.lean`. Net: `#print axioms g0_HS_contact_value` →
`[propext, Classical.choice, Quot.sound, oz_core_closure, oz_fixed_pt_unique,
oz_h_exterior_regularity]` — the specific PY number is now *derived* (through the actual OZ solution
machinery, which the old standalone axiom bypassed entirely), and the only assumption specific to it
is the analytic regularity/decay of the opaque `Classical.choose`-built `oz_h` — a strictly weaker,
more physically legible axiom. There are no term-level callers of the old axiom, so nothing
downstream broke; full `lake build` clean.

**Depends on:** `BAXTER.6` and `BAXTER.7` (both done), `OZ.9b` (`oz_fourier_oz_eq_of_PY_core`,
done, `proof_notes_hard_sphere.md`).

**Status:** ✓ **DONE** — conditional theorem `g0_HS_contact_value_of_oz_h_regularity` **plus** the
unconditional `theorem g0_HS_contact_value` (via the `oz_h_exterior_regularity` axiom), both genuine
theorems, no sorry, in `HardSphere/JumpAsymptotic.lean`. The old physical-number axiom is retired.

---

### Tasks BAXTER.9–14 — staged plan for `BAXTER.2`'s full construction

Numerically-ID'd sub-tasks for `BAXTER.2`'s remaining scope (retiring `oz_core_closure` as a
derived theorem), attempted **in order**, each with an explicit go/no-go checkpoint before
starting the next — see `BAXTER.2`'s own writeup above for the full reconnaissance this split is
based on. Each task now has its own section below (previously combined into one).

### Task BAXTER.9 — `Qhat_complex : ℂ → ℂ` in closed form, proved entire

✓ **DONE** — `LeanCode/HardSphere/BaxterZeros.lean`, no `sorry`/`axiom`. `Qhat_complex eta sigma
rho k := ∫₀^σ q0_poly(r)·e^{-ikr} dr`. Two independent halves:

- **Entireness** (`Qhat_complex_entire`, unconditional on `k`): via a new general lemma
  `entire_poly_exp_integral` (any continuous `P : ℝ → ℝ`, `k ↦ ∫₀^σ P(r)e^{-ikr}dr` is entire),
  proved with `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  (`Mathlib.Analysis.Calculus.ParametricIntervalIntegral`) — the dominating bound comes from
  `‖e^{-ikr}‖ = exp(r·Im k)` plus a ball-membership estimate on `Im k` (`Complex.abs_im_le_norm`,
  `Metric.mem_ball` + `dist_eq_norm`). Applied to the quadratic `P` that `q0_poly_inner` gives on
  `[0,σ]` — proof works from the **raw integral**, so the closed form's spurious `k=0`
  singularity never enters.
- **Closed form** (`Qhat_complex_formula`, `k ≠ 0`): complex analogue of
  `q0poly_cos_integral_formula`/`_sin_integral_formula`, derived directly against
  `Complex.exp(-ikr)` (not split into `cos`/`sin`) via three new moment lemmas `zeta0_formula`/
  `zeta1_formula`/`zeta2_formula` (`HasDerivAt`+FTC on `{1,r,r²}`, using
  `HasDerivAt.comp_ofReal` to bridge the holomorphic-in-`z` derivative to a real-variable-`r`
  derivative — the key idiom this task needed that hadn't been used elsewhere in the project).
- **Verification:** `lake build` clean, zero warnings. Numerically cross-checked
  (`check_qhat_complex.py`, scratch): closed form agrees with the raw integral to ~1e-15 at six
  complex test points (including near the known pole `k≈6.058+1.437i`); agrees exactly with
  `q0poly_cos_integral_formula`/`_sin_integral_formula`'s `Re`/`-Im` at real `k`; the raw integral
  is numerically smooth through `k=0` despite the closed form's individual `1/k`,`1/k²`,`1/k³`
  terms (confirms entireness is not an artifact of the specific proof route).

**Status:** ✓ DONE.

### Task BAXTER.10 — Numerical/symbolic feasibility check for the Banach-pole-existence strategy

Python/sympy, *not* Lean — matches this project's "verify before formalizing" rule.

With `BAXTER.9`'s exact closed form for `Qhat_complex` now in hand, built `F(k) = 1-ρQ̂(k)` and
`F'(k)` symbolically (`sympy`) and tested the concrete two-stage argument `BAXTER.11` would need:

1. **Explicit guess** `k0(n) = 2πn/σ + i·(2·ln(2πn/σ)−2.12)` (the measured asymptotic law from
   `BAXTER.2`'s writeup).
2. **One plain (non-chord) Newton step**, `k1 = k0 − F(k0)/F'(k0)` — purely algebraic, no
   analysis needed to justify in Lean.
3. **Chord-Newton contraction** `g(k) = k − F(k)/F'(k1)` on `disk(k1, r)`, `r = 0.05·(2π/σ)` (a
   **fixed, n-independent** radius tied to the pole spacing, not to `|k1|` — an initial attempt
   using `r ∝ |k1|` spuriously blew up `max|1−F'(k)/F'(k1)|` to `~10^150` by `n=1000` because it
   let `Im(k)` range absurdly far within the disk; switching to a fixed radius fixes this).

- **Result (η=0.3, σ=1, swept `n=1..5000`):** for **all `n≥10`**, both Banach sufficient
  conditions hold: `Lip(g) ≤ max_L ≈ 0.369 < 1` on `disk(k1,r)` (margin `1−L≈0.63`), **and**
  the self-map condition `|g(k1)−k1| ≤ r(1−L)` (margin stabilizes at `≈18–20%`, e.g. `n=1000`:
  step `1.63e-1` vs. bound `1.98e-1`). Both quantities **converge to fixed constants as `n→∞`**
  (not degrading) — `max_L→0.36911`, self-map margin `→0.198` — i.e. genuinely **uniform**, not
  just "eventually true with a shrinking margin." `n=1..5` fail this specific two-step recipe
  (the raw asymptotic guess isn't quite good enough there) but that's harmless: only finitely
  many small-`n` exceptions, coverable individually (interval arithmetic or direct numerical
  bounds) without threatening the "infinitely many poles" existence claim `BAXTER.11` needs.
- **Robustness:** re-checked at `η∈{0.05,0.1,0.3,0.45}` (all give `max_L∈[0.28,0.37]`, same
  ballpark) and `σ∈{0.3,1,5}` (consistent once the radius is scaled by `2π/σ` as above; two
  parameter combinations hit floating-point overflow in the naive `sympy`/`numpy` double-precision
  evaluation at very large `n` — a numerical-precision artifact of the check script, not a
  mathematical failure, not pursued further since the core result is already unambiguous from
  the dozens of other data points).
- **Go/no-go verdict: GO.** A genuine, uniform (`n`-independent for `n≥10`) contraction bound
  exists with comfortable margin on both Banach conditions. Proceed to `BAXTER.11`.
- Scratch scripts (not committed): `baxter10_feasibility.py`, `baxter10_radius_sweep.py`,
  `baxter10_final_check.py`, `baxter10_onestep.py` — rerunnable from this description (build
  `F`/`F'` symbolically from `BAXTER.9`'s closed form via `sympy`, no external data needed).

**Status:** ✓ DONE — GO, proceed to `BAXTER.11`.

### Task BAXTER.11 — Pole existence for `1-ρQ̂(k)` in Lean via Banach contraction

Only attempted since `BAXTER.10` passed. Prove existence (and the asymptotic bracket, not
necessarily the precise fitted constants) of infinitely many zeros of `1-ρQ̂(k)` via the
Banach-contraction argument validated in `BAXTER.10`.

**Status:** ✓ **DONE, conditionally** — `LeanCode/HardSphere/BaxterPoles.lean`, no `sorry`/`axiom`
anywhere in the file. Final theorem `Qhat_complex_zeros_infinite`: `{k : ℂ | 1 -
ρ·Qhat_complex eta sigma rho k = 0}.Infinite`, conditional on **one** explicit, isolated,
numerically-validated (`BAXTER.10`) hypothesis (`hstep`, the "good guess" quality — see below);
every other piece of the argument is proved unconditionally, for general `η∈(0,1), σ>0, ρ≠0`.
Built in five stages (A.1–A.5), all landed:

- **Exponential-polynomial reduction (done, the main structural result this pass).**
  `Qhat_complex_formula` regroups (pure `ring`) into `A(k)+B(k)e^{-ikσ}`; clearing each of
  `A`, `B`'s `1/c,1/c²,1/c³` denominators separately (`field_simp`, no `exp` mixed in — the key
  trick that made this tractable, after an earlier attempt mixing `exp` and non-`exp` terms
  before clearing denominators produced an unmanageable `field_simp` normal form) and using the
  algebraic identity `P0+P1σ+P2σ²=0` (already implicit in `q0_poly_inner`, now isolated as
  `baxterP0P1P2_sum_zero`, closed by one `linear_combination`) collapses
  `(-ik)³·(1-ρQ̂(k))` to a clean **cubic-minus-(linear-times-exponential)** exponential
  polynomial `G_baxter(k) = Npoly(k) - Dpoly(k)·e^{-ikσ}` — exactly the classical
  Pólya/Titchmarsh form `BAXTER.2`'s own notes anticipated, and *far* easier to estimate than
  `Qhat_complex`'s own closed form. `Dpoly`'s naive `c²`-order term cancels identically via the
  same `P0+P1σ+P2σ²=0` identity, leaving it genuinely linear. Proved: `baxter_cube_mul_F_eq_G`
  (the identity), `Qhat_pole_iff_G_baxter_zero` (the `k≠0` equivalence `1-ρQ̂(k)=0 ↔
  G_baxter(k)=0`), `G_baxter_entire` (trivial: polynomial × entire exponential − polynomial,
  `fun_prop` one-liner — no dominated-convergence machinery needed here at all, unlike
  `BAXTER.9`'s `Qhat_complex`).
- **A.1 — Magnitude bounds, DONE.** `baxterP1+2·baxterP2·σ = ρ·q_prime_py(η,σ)` collapses
  `Dpoly(k)` to the clean affine form `iμk+ν`, `μ:=ρ²q_prime_py(η,σ)>0`,
  `ν:=ρ²q_doubleprime_py(η)>0` (`Dpoly_eq_affine`, `baxterMu_pos`, `baxterNu_pos`). Reverse-
  triangle-inequality ("half the leading term") bounds `Npoly_lower_bound`
  (`‖Npoly(k)‖≥‖k‖³/2`), `Dpoly_lower_bound` (`‖Dpoly(k)‖≥μ‖k‖-ν`), `Npoly_deriv_bound`
  (`‖Npoly'(k)‖≤(3+2a+b)‖k‖²`), `Dpoly_hasDerivAt` (`Dpoly'(k)=iμ`, exact, constant) combine
  into `R_deriv_ratio_bound`: `‖N'(k)/N(k)-D'(k)/D(k)‖ ≤ C/‖k‖`, `C:=8+4a+2b` — the single
  estimate everything else builds on.
- **A.2 — Branch-safety, DONE (the highest-risk piece, closed cleanly).** `baxterPhi`'s log
  needs `R(k):=Npoly(k)/Dpoly(k) ∈ Complex.slitPlane`; sufficient that `Re(R(k))>0`, i.e.
  `Re(Npoly(k)·conj(Dpoly(k)))>0`. Found a cleaner route than raw `x,y`-expansion: writing
  `Npoly=ik³+E1` (`E1` the lower-order correction, already bounded for A.1), the product's
  leading term `μ‖k‖²k²` has `Re = μ‖k‖²·Re(k²)`; the remaining `bracket` term is bounded in
  *magnitude only* (`‖bracket‖≤D‖k‖³`, no separate `Re`/`Im` tracking needed) and
  `Re(z)≥-‖z‖` finishes it. Gives `Npoly_mul_conj_Dpoly_re_pos` (positive once
  `D‖k‖<μ·Re(k²)`, an explicit threshold) and `R_mem_slitPlane`.
- **A.3 — Differentiability + Lipschitz via the mean-value inequality, DONE.**
  `baxterPhi_hasDerivAt`: `HasDerivAt.div` (quotient rule) chained with `HasDerivAt.clog`
  (needs A.2's `slitPlane` fact) gives `baxterPhi`'s derivative in closed form. Combined with
  A.1's bound (`baxterPhi_deriv_bound`) and Mathlib's `Convex.lipschitzOnWith_of_nnnorm_deriv_le`
  (confirmed present, avoids the numerical *sampling* `BAXTER.10` needed — a disk is provably
  convex) gives `baxterPhi_lipschitzOnWith`: a genuine `LipschitzOnWith` fact on any disk
  where A.1/A.2's threshold hypotheses hold throughout.
- **A.4 — Self-map lemma, DONE.** `mapsTo_closedBall_of_lipschitzOnWith_of_dist_le`: generic
  fact (not `baxterPhi`-specific) that a `K`-Lipschitz map moving its center by `≤r(1-K)` maps
  `closedBall` into itself — the standard Banach sufficient condition.
- **A.5 — Assembly, distinctness, infinitude, DONE.** `baxter_G_zero_exists_for_n` composes
  A.1–A.4 with `G_baxter_pole_exists_of_bounds` and the already-unconditional
  `baxterPhi_fixedPt_implies_zero` to get a zero of `G_baxter` in `disk(k1,r)` for a single
  `n`. `G_baxter_pole_family_exists` (added `BAXTER.12` pass, see that task) extracts the
  witness-choice function across a sequence of disks as a standalone reusable name, proves
  **injectivity** from disk disjointness (`r<π/σ`, i.e. diameter `<` the exact pole spacing
  `2π/σ`, plus `Re(k1 n)=2πn/σ` — `Complex.abs_re_le_norm` turns this into a clean real-part-
  separation argument); `G_baxter_zeros_infinite` is a thin corollary via
  `Set.infinite_of_injective_forall_mem`. `Qhat_complex_zeros_infinite` transfers through
  `Qhat_pole_iff_G_baxter_zero` (valid for `k≠0`; removing the single point `0` from an infinite
  set via `Set.Infinite.sdiff`/`.mono` keeps it infinite) to state the final result about
  `1-ρQ̂(k)` directly.
- **The one remaining gap (by design, not oversight): `hstep`, the "good guess" hypothesis.**
  Every theorem above is fully general and unconditional (`η∈(0,1)`, `σ>0`, `ρ≠0`, arbitrary
  disk satisfying the stated thresholds). What's *not* proved in Lean is that the specific
  numerically-fitted asymptotic guess `k1(n) = 2πn/σ + i·(2·ln(2πn/σ)-2.12)` (found by curve-
  fitting in the original `BAXTER.2` investigation, not derived) is actually good enough
  (`dist(k1(n), baxterPhi(k1(n))) ≤ r(1-K)`) — this is a *different kind* of estimate (bounding
  a specific transcendental asymptotic formula's error, not a general algebraic inequality) and
  was flagged as a real risk in the execution plan before starting. `Qhat_complex_zeros_infinite`
  takes this as an explicit hypothesis (`hstep`) rather than proving it, matching this project's
  established pattern for partially-open problems (`g0_HS_contact_value_of_oz_h_regularity`,
  `BAXTER.8`) — a genuine, `sorry`-free conditional theorem with the gap isolated to one
  numerically-validated (`BAXTER.10`: checked `η∈{0.05,0.1,0.3,0.45}`, `n` up to `10000`,
  margins `≈18-20%` and improving) fact, not a re-opened research question. Discharging `hstep`
  for the specific guess formula (or substituting a cruder but analytically-bounded guess) is
  the one item that would make `BAXTER.11` unconditional; not attempted this pass. **Update
  (`BAXTER.14`, if/when landed): the same pass that would discharge `hstep` is closely related to
  `BAXTER.14`'s rigorous exponent derivation**, since both need genuine control of `Im(k_n)`'s
  growth — worth revisiting together.
- Scratch work (not committed): `baxter11`-prefixed sympy/numpy checks in the same session
  confirming the log-fixed-point strategy, the `Dpoly` coefficient simplification, and the
  `Re(Npoly·conj(Dpoly))>0` leading-order estimate.

### Task BAXTER.12 — Residue formula + `h_explicit` definition, convergence (conditional)

**Status:** ◐ in progress. `LeanCode/HardSphere/BaxterResidue.lean` (new file), no
`sorry`/`axiom`:

- **B.1 — residue-at-a-simple-pole fact: DONE, and simpler than planned.** The original scope
  called for deriving this from Cauchy's integral formula + the circle-integral API (both
  confirmed present in Mathlib but unused anywhere in this codebase). Turned out
  **unnecessary**: the classical alternative characterization `Res_{z0}[f] = lim_{z→z0}
  (z-z0)·f(z)` follows directly from `HasDerivAt`'s own definition
  (`hasDerivAt_iff_tendsto_slope`) plus elementary limit algebra (`Filter.Tendsto.inv₀`/`.mul`)
  — no circle integrals, no Cauchy's formula, no new Mathlib subsystem needed.
  `residue_of_simple_pole` is fully general (any `N,D:ℂ→ℂ` with `D` having a simple zero),
  not tied to `G_baxter` specifics.
- **`Chat_complex` — the complex-valued `Ĉ`: DONE.** `LeanCode/HardSphere/
  RadialFourierCHSComplex.lean` (new file), no `sorry`/`axiom`. `Ĉ(k) :=
  radial_fourier(c_HS eta sigma) k` (Task OZ.8) was only defined for **real** `k`; this file
  extends it, mirroring `Qhat_complex`'s construction (`BAXTER.9`) but for `c_HS`'s **cubic**
  inner polynomial (vs. `q0_poly`'s quadratic) and `radial_fourier`'s **`sin`** kernel with an
  extra `1/k` prefactor (vs. `Qhat_complex`'s bare `exp` integral):
  - `Chat_poly` — the polynomial expansion of `r·c_HS(r)` (`-(a0r+(a1/σ)r²+(a3/σ³)r⁴)`,
    globally continuous, sidestepping `c_HS`'s own jump at `r=σ`, same trick as
    `Qhat_complex_eq_poly`).
  - `Chat_F(k) := ∫r·c_HS(r)·e^{-ikr}dr` (via `Chat_poly`), proved **entire**
    (`entire_poly_exp_integral`, reused directly from `BaxterZeros.lean`) with an explicit
    closed form (`Chat_F_formula`) via new `zeta4_formula` (degree-4 complex-exponential
    moment — `zeta0`–`zeta2` already existed from `BAXTER.9`; `c_HS`'s cubic term needs degree
    4 once multiplied by the kernel's extra `r`) alongside the existing `zeta1`/`zeta2`.
  - `Chat_J(k) := (Chat_F(-k)-Chat_F(k))/(2i)` — the `sin`-kernel integral via
    `sin(z)=(e^{iz}-e^{-iz})/(2i)`; entire for free (difference of two entire functions, one
    precomposed with negation).
  - `Chat_complex(k) := (4π/k)·Chat_J(k)`, differentiable for `k≠0` (deliberately **not**
    claimed entire — `BAXTER.11`'s poles all have `Re(k_n)=2πn/σ>0`, so `k≠0` is all the
    residue formula needs; no removable-singularity argument at `k=0` attempted).
  - **Verified** (scratch, not committed): numerically cross-checked against
    `radial_fourier(c_HS)`'s direct real-space quadrature at several real `k` — agreement to
    `~1e-9`.
- **Residue formula assembly: DONE.** `G_baxter_deriv`/`G_baxter_hasDerivAt` (added to
  `BaxterPoles.lean`, product rule via `Npoly_hasDerivAt`/`Dpoly_hasDerivAt`) plus
  `Hhat_residue_at_pole` (`BaxterResidue.lean`): rewrote the target
  `Res_{k_n}[k·Ĉ(k)·e^{ikr}/((1-ρQ̂(k))(1-ρQ̂(-k)))]` **purely in terms of `G_baxter`** via
  `baxter_cube_mul_F_eq_G` and the identity `(-ik)³(ik)³=k⁶` — `k·Ĉ(k)e^{ikr}/[(1-ρQ̂(k))
  (1-ρQ̂(-k))] = k⁷·Ĉ(k)e^{ikr}/[G_baxter(k)·G_baxter(-k)]` — then `residue_of_simple_pole`
  applies directly with `D:=G_baxter`, `N(k):=k⁷Ĉ(k)e^{ikr}/G_baxter(-k)`. Two non-degeneracy
  hypotheses (`G_baxter_deriv(k_n)≠0`; `-k_n` isn't itself a zero) are stated as explicit
  hypotheses in `Hhat_residue_at_pole`'s signature and are **now discharged in general**, see
  below.
- **B.2 — mirror pole family: DONE, and cleaner than planned.** The plan called for
  numerically checking the symmetry claim first, then re-deriving `BAXTER.11`'s whole
  existence argument for the mirror family if needed. Turned out **unnecessary**: `Npoly`,
  `Dpoly`'s coefficients are all real, giving a clean algebraic identity
  `conj(G_baxter(k)) = G_baxter(-conj(k))` (`G_baxter_conj`, confirmed symbolically via
  `sympy` before formalizing, then closed in Lean via `simp [map_sub, map_add, map_mul,
  Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_conj]` + `ring_nf` — no new estimates
  needed at all). Immediate corollary `G_baxter_zero_mirror`: **any** zero `k` of `G_baxter`
  has a mirror zero `-conj(k)` (for `k=x+iy`, this is `-x+iy` — exactly the classical
  "mirrored `±Re(k)`, same `Im(k)`" pole-pair structure `BAXTER.2`'s original numerics found,
  `k≈±6.058+1.437i`). Applying this to each `k_n` from `BAXTER.11`'s
  `Qhat_complex_zeros_infinite` immediately gives the negative-real-part family too — no need
  to redo `BAXTER.11`'s Banach argument a second time.
  - **Note:** this symmetry is about `-conj(k)` (the mirror across the imaginary axis, upper
    half-plane), *not* `-k` (`Hhat_residue_at_pole`'s `hGneg_ne` hypothesis, about the lower
    half-plane) — a different point; discharging `hGneg_ne` needed a separate argument, see
    `G_baxter_neg_ne_zero_of_large` below.
- **B.3 — `h_explicit` definition + convergence: DONE, conditionally.** `BaxterResidue.lean`
  additions, no `sorry`/`axiom`:
  - `residue_term eta sigma rho r k_n := k_n^7·Ĉ(k_n)·e^{ik_nr}/[G_baxter(-k_n)·
    G_baxter_deriv(k_n)]` — literally `Hhat_residue_at_pole`'s limit value, extracted as a
    standalone def.
  - `h_explicit_term eta sigma rho r kfam n := residue_term(kfam n) +
    residue_term(-conj(kfam n))` — pairs each pole with its `B.2` mirror, over an **abstract**
    pole family `kfam : ℕ → ℂ` (stated generically; `BAXTER.11`'s concrete witness function is
    now separately exposed, see below).
  - `h_explicit eta sigma rho r kfam := (1/2πr)·Re[∑' n, h_explicit_term ... n]`.
  - `h_explicit_summable`: **conditional** theorem — `r>σ` plus an explicit magnitude-bound
    hypothesis `‖h_explicit_term n‖ ≤ C·(n+1)^{1-2r/σ}` gives `Summable (h_explicit_term ...)`,
    via `Real.summable_nat_rpow` (`Summable (n↦n^p) ↔ p<-1`, so `p:=1-2r/σ<-1 ⟺ r>σ`),
    `summable_nat_add_iff` (index-shift by 1) and `Summable.of_norm_bounded` (comparison test).
    **The `r>σ` threshold is exactly the physical exterior domain — no gap left open.**
- **Non-degeneracy, discharged in general: DONE.** Both of `Hhat_residue_at_pole`'s
  hypotheses are now standalone, unconditional-in-`η,σ,ρ` magnitude-bound theorems (same style
  as `A.1`/`A.2` — plain `‖k‖`-past-a-threshold estimates, no asymptotic/logarithmic control on
  `Im(k)` needed), added to `BaxterPoles.lean`:
  - `G_baxter_deriv_ne_zero_of_large`: if `G_baxter(k)=0` and `‖k‖` exceeds an explicit
    threshold, `G_baxter_deriv(k)≠0` (simple zero). Proof: substituting the zero condition into
    `G_baxter_deriv`'s formula and bounding the resulting `Dpoly'·e^{-ikσ}` correction by
    `2‖Npoly(k)‖/‖k‖` (via `Dpoly`'s lower bound) forces `‖Npoly'(k)‖≥σ‖k‖³/4` if the derivative
    *did* vanish, contradicting `Npoly_deriv_bound`'s quadratic upper bound once `‖k‖` is large.
  - `G_baxter_neg_ne_zero_of_large`: if `Im(k)≥0` (the only sign fact needed — **no** growth-rate
    control on `Im(k)`, unlike the original plan's sketch) and `‖k‖` exceeds an explicit
    threshold, `G_baxter(-k)≠0`. Proof: `|e^{-i(-k)σ}|=|e^{ikσ}|=e^{-σ\cdot Im(k)}≤1` since
    `Im(k)≥0`, so `‖Dpoly(-k)e^{-i(-k)σ}‖≤‖Dpoly(-k)‖≤μ‖k‖+ν` (affine upper bound), dominated by
    `Npoly(-k)`'s cubic lower bound `‖k‖³/2` once `‖k‖` is large.

  Both are standalone (take `G_baxter(k)=0` as a *hypothesis*, not threaded through the huge
  existing assembly signatures), so they compose directly with any future concrete pole family
  without needing to touch `baxter_G_zero_exists_for_n`/`G_baxter_zeros_infinite`.
- **Pole family exposed as a standalone name: DONE.** `G_baxter_pole_family_exists`
  (`BaxterPoles.lean`) extracts the witness-choice function that was previously buried inside
  `G_baxter_zeros_infinite`'s proof (an internal `choose`) as a reusable named object: `∃ g : ℕ →
  ℂ, Injective g ∧ (∀n, g n ∈ closedBall (k1(n+N)) r) ∧ (∀n, G_baxter(g n)=0)`.
  `G_baxter_zeros_infinite` is now a thin corollary (`Set.infinite_of_injective_forall_mem`
  applied to this). `Qhat_complex_zeros_infinite` unchanged.
- **Symbolic exponent — corrected and heuristically derived.** The magnitude-bound hypothesis's
  exponent was re-examined: an **earlier numerical check only tested `σ=1`**, where `1-2r` and
  the true general exponent `1-2r/σ` coincide, masking the `σ`-dependence. Re-verified
  numerically at `σ∈{1,2,0.5}` (`η=0.3`, poles up to `n=320`, Newton-refined): the exponent is
  `1-2r/σ`, confirmed to 3 decimal places at every tested `σ` (`σ=2,r=3⇒slope≈-2.000`;
  `σ=0.5,r=1⇒slope≈-3.00`). **Heuristic (`Θ`-level, not yet a rigorous inequality) symbolic
  derivation:** at a pole `k_n`, `G_baxter(k_n)=0` forces `|e^{-ik_nσ}| =
  ‖Npoly(k_n)‖/‖Dpoly(k_n)‖ = Θ(n²)`, i.e. `Im(k_n)=Θ((2/σ)\ln n)` — a **consequence** of the
  pole equation itself, not an independently-fitted asymptotic (resolving where the original
  `BAXTER.2` investigation's `2\ln(x)-2.12` guess-formula's log-growth actually comes from).
  Propagating this: `Chat_complex(k_n)=Θ(1)`, `G_baxter(±k_n)=G_baxter_deriv(k_n)=Θ(n³)` (matches
  the two non-degeneracy theorems' own cubic lower bounds), `k_n^7=Θ(n^7)`, giving
  `|residue\_term(k_n)| = Θ(n)\cdot e^{-r\cdot Im(k_n)} = Θ(n^{1-2r/σ})`. `h_explicit_summable`
  now uses this corrected exponent.
- **What's left for `BAXTER.12`: promoted to its own task, `BAXTER.14` (below).** The remaining
  gap (rigorous exponent bound + concrete instantiation) is different in *kind* from the rest of
  `BAXTER.12` (an asymptotic-estimate task, not an assembly/definition task), so it gets its own
  section rather than staying folded into `BAXTER.12`'s status.

**Status:** ◐ in progress — everything except the rigorous exponent bound is done; see
`BAXTER.14`.

### Task BAXTER.13 — `h_explicit` satisfies `OzFixedPt`; retire `oz_core_closure`

Assembly-style, following `OzFixedPtDilute.lean`'s existing three-lemma pattern
(`isFixedPt`/`continuousOn`/`bounded`, `proof_notes_hard_sphere.md` Task OZ.10-dilute) as a
template. Retires `oz_core_closure`.

Scoped as **Phase C** in the original plan, and flagged as likely the largest single estimate in
the whole three-phase undertaking. Checked this pass: `oz_core_closure`'s actual content is about
the OZ convolution identity holding **inside** the hard core (`0<r<σ`), not the exterior — the
only existing bridge theorem, `oz_fourier_oz_eq_of_core_closure` (`OZFourierBridge.lean`), runs
the **wrong direction** (assumes core-closure, derives the Fourier-domain identity), and that
file's own doc-comment independently flags Fourier inversion as "separate, much larger future
work... not attempted." So `BAXTER.13` needs a genuine new Fourier-inversion/contour-integration
argument, with no existing shortcut in the codebase.

**Status:** ☐ not started, blocked on `BAXTER.12`/`BAXTER.14`.

### Task BAXTER.14 — Rigorous `n^{1-2r/σ}` magnitude bound + concrete `h_explicit` instantiation

Split out from `BAXTER.12`'s "what's left" list (previously two informal bullet points) since it
is a genuinely different *kind* of task (an asymptotic magnitude estimate, in the same family as
`BAXTER.11`'s `hstep`) from the rest of `BAXTER.12` (definitions + assembly). Two sub-parts:

1. **Fully rigorous (inequality-level) symbolic derivation of the `n^{1-2r/σ}` exponent.**
   `BAXTER.12`'s heuristic `Θ`-derivation (at a pole `k_n`, `G_baxter(k_n)=0` forces
   `Im(k_n)=Θ((2/σ)\ln n)`, propagating to `|residue\_term(k_n)|=Θ(n^{1-2r/σ})`) is not yet a
   Lean-formalizable two-sided bound. Needs explicit upper/lower bounds on `Chat_complex(k_n)`'s
   magnitude (from `Chat_F_formula`'s closed form) combined with `G_baxter_deriv_ne_zero_of_large`/
   `G_baxter_neg_ne_zero_of_large`'s cubic bounds, all evaluated *at* a concrete pole from
   `G_baxter_pole_family_exists`. Likely related to discharging `BAXTER.11`'s own `hstep`
   hypothesis (both need genuine control of `Im(k_n)`'s growth) — worth attempting together.
2. **Instantiate `h_explicit_summable` with `G_baxter_pole_family_exists`'s concrete `g`**, once
   (1) supplies the magnitude bound, giving an actual `Summable` fact (not just a conditional
   schema) — needed before `BAXTER.13` can use a genuinely concrete `h_explicit`. Mechanical once
   (1) is done.

Neither is harder *in kind* than `BAXTER.9`–`12`'s own techniques so far (closed-form complex
extensions, `HasDerivAt`+FTC estimates, `Summable`/`tsum` comparison tests) — but (1) especially
is a genuine, multi-lemma undertaking, not a quick corollary.

**Status:** ☐ not started, blocked on `BAXTER.12` (done except for this).

---
