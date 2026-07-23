# Proof Notes: Group POLE — Complex-Analytic Pole/Residue Construction for the Baxter Q-Factor

Detailed proof records for Group POLE: the complex-analytic machinery that constructs the
pole/residue data underlying `h_explicit` — `Qhat_complex`'s closed form and entireness, the
Banach-contraction pole-existence argument for `1-ρQ̂(k)=0`, the residue formula, and the rigorous
magnitude bound feeding `h_explicit`'s summability. Split out of Group BAXTER (2026-07-15, by
topic, when that group grew to 15+ tasks spanning several unrelated areas) — task IDs `POLE.1`–`5`
were `BAXTER.9`, `10`, `11`, `12`, `14` respectively; see the mapping table at the top of
`proof_notes_baxter.md`. Depends on Group BAXTER (`BAXTER.1`–`3`, the real-space Q-factor and
real-`k` Wiener–Hopf factorization) and feeds Group OZFIX (`h_explicit`'s closed-form assembly
into `OzFixedPt`, `proof_notes_ozfix.md`). See `todo_lean.md` for task status summary.

## Group POLE — Pole Existence, Residue Formula & Magnitude Bounds

### Tasks POLE.1–5 — staged plan for `BAXTER.2`'s full construction *(formerly `BAXTER.9`–`14`)*

Numerically-ID'd sub-tasks for `BAXTER.2`'s remaining scope (retiring `oz_core_closure` as a
derived theorem), attempted **in order**, each with an explicit go/no-go checkpoint before
starting the next — see `BAXTER.2`'s own writeup above for the full reconnaissance this split is
based on. Each task now has its own section below (previously combined into one). Renamed to the
`POLE` prefix (2026-07-15) when Group BAXTER was split by topic into `BAXTER`/`CONTACT`/`POLE`/
`OZFIX` — see the mapping table at the top of `proof_notes_baxter.md`.

### Task POLE.1 — `Qhat_complex : ℂ → ℂ` in closed form, proved entire

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

### Task POLE.2 — Numerical/symbolic feasibility check for the Banach-pole-existence strategy

Python/sympy, *not* Lean — matches this project's "verify before formalizing" rule.

With `POLE.1`'s exact closed form for `Qhat_complex` now in hand, built `F(k) = 1-ρQ̂(k)` and
`F'(k)` symbolically (`sympy`) and tested the concrete two-stage argument `POLE.3` would need:

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
  bounds) without threatening the "infinitely many poles" existence claim `POLE.3` needs.
- **Robustness:** re-checked at `η∈{0.05,0.1,0.3,0.45}` (all give `max_L∈[0.28,0.37]`, same
  ballpark) and `σ∈{0.3,1,5}` (consistent once the radius is scaled by `2π/σ` as above; two
  parameter combinations hit floating-point overflow in the naive `sympy`/`numpy` double-precision
  evaluation at very large `n` — a numerical-precision artifact of the check script, not a
  mathematical failure, not pursued further since the core result is already unambiguous from
  the dozens of other data points).
- **Go/no-go verdict: GO.** A genuine, uniform (`n`-independent for `n≥10`) contraction bound
  exists with comfortable margin on both Banach conditions. Proceed to `POLE.3`.
- Scratch scripts (not committed): `baxter10_feasibility.py`, `baxter10_radius_sweep.py`,
  `baxter10_final_check.py`, `baxter10_onestep.py` — rerunnable from this description (build
  `F`/`F'` symbolically from `POLE.1`'s closed form via `sympy`, no external data needed).

**Status:** ✓ DONE — GO, proceed to `POLE.3`.

### Task POLE.3 — Pole existence for `1-ρQ̂(k)` in Lean via Banach contraction

Only attempted since `POLE.2` passed. Prove existence (and the asymptotic bracket, not
necessarily the precise fitted constants) of infinitely many zeros of `1-ρQ̂(k)` via the
Banach-contraction argument validated in `POLE.2`.

---

**🔴 2026-07-15 — CRITICAL FINDING (during `OZFIX.6`'s Phase-2 numerical feasibility check):
`G_baxter`'s zero condition uses the wrong `ρ`-scaling — its zeros do *not* match the
physically-correct Baxter pole family.** Discovered while numerically verifying a Jordan's-lemma
vanishing estimate for a new contour-deformation axiom (`LeanCode/Analysis/ContourDeformation.lean`,
general-purpose, unaffected by this finding). Three independent numerical checks (`η=0.3,σ=1`,
scratch scripts, not committed), all consistent:

1. **The Wiener–Hopf scaling test.** `baxter_wiener_hopf_complex` (`OZFIX.2`, proven, no
   `sorry`/axiom) states `(1-Qhat_complex(k))·(1-Qhat_complex(-k)) = 1-ρ·Chat_complex(k)` — **no
   extra `ρ`** multiplying `Qhat_complex`. Checked numerically at several real `k`: this holds
   exactly (machine precision). The *alternative* scaling `(1-ρ·Qhat_complex(k))·(1-ρ·Qhat_complex(-k))`
   (matching `G_baxter`'s own zero condition, see below) does **not** equal `1-ρ·Chat_complex(k)` —
   clearly different numeric values at every test point.
2. **Historical ground-truth cross-check.** `BAXTER.2`'s very first, pre-Lean numerical
   investigation (`proof_notes_baxter.md`) found the first Baxter pole at `k≈6.058+1.437i`
   (η=0.3,σ=1). Newton-refining a root of `1-Qhat_complex(k)=0` (**no** extra `ρ`) from that
   seed converges to `k=6.058015+1.436794i` — matching to 6 significant figures. `G_baxter`
   itself at that exact point evaluates to `|G_baxter|≈103`, nowhere near zero — `G_baxter`'s
   own "first pole" (found via its own Banach/Newton construction) is at a *different* point,
   `k≈5.646+1.916i`.
3. **The underlying algebra is not at fault.** `baxter_cube_mul_F_eq_G`
   (`(-ik)³·(1-ρ·Qhat_complex(k)) = G_baxter(k)`) was independently re-verified numerically and
   holds exactly — `G_baxter` correctly, faithfully represents `(-ik)³·(1-ρ·Qhat_complex(k))` as
   designed. The issue is *upstream* of the algebra: `1-ρ·Qhat_complex(k)=0` was chosen as
   `G_baxter`'s target equation (see `Qhat_pole_iff_G_baxter_zero`'s own doc-comment: "Reduces the
   zero set of `1-ρ·Qhat_complex`…"), but this is very likely a **double-counted `ρ`** — `q0_poly`
   (which `Qhat_complex` is the Fourier transform of) *already* has `ρ` baked in linearly
   (`q0_poly = ρ·q_prime_py·φ₁+ρ·q_doubleprime_py·φ₂`, i.e. `q0_poly = ρ·Q` in Wertheim's own
   notation per `BAXTER.1`'s docstring), so `Qhat_complex` already represents `ρ·Q̂`, not the bare
   `Q̂`. The classical pole condition `1-ρQ̂(k)=0` should therefore translate to
   **`1-Qhat_complex(k)=0`** (no further `ρ`) — exactly the scaling `baxter_wiener_hopf_complex`
   independently uses, and exactly what matches the historical ground-truth pole. `G_baxter`'s
   `1-ρ·Qhat_complex(k)=0` applies the `ρ` a second time.

**Scope of the problem.** This affects every theorem downstream of `G_baxter`'s zero set:
`Qhat_complex_zeros_infinite`, `G_baxter_pole_family_exists` (this task), `POLE.4`'s
`residue_term`/`h_explicit` (built on `G_baxter`'s zeros as the pole family), `POLE.5`'s magnitude
bounds, and all of **Group OZFIX** (`h_explicit`'s `OzFixedPt` assembly) — none of these are
individually *wrong* as formal derivations from `G_baxter`'s definition (the Lean proofs are
sound), but `G_baxter`'s zero set is not the physically-relevant one, so `h_explicit` as currently
built does not represent the actual PY exterior solution. This likely also explains `OZFIX.6`'s
earlier "per-pole collapse is false (ratio -2.72)" finding — not because the collapse is
inherently non-termwise, but because the pole family itself was wrong, so no collapse identity
(termwise or aggregate) can be expected to close correctly against the true `h_explicit`.

**✅ FIXED 2026-07-15.** User confirmed ("OK, fix the ρ-scaling now") and the repair landed:
`Npoly`/`Dpoly` now target `(-ik)³·(1-Qhat_complex(k))` (no extra `ρ`); `baxterP0/1/2` themselves
are unchanged (each already carries exactly one `ρ` from `q_prime_py`/`q_doubleprime_py`).
Mechanically: every `rho * baxterPn eta sigma rho` collapsed to `baxterPn eta sigma rho`, every
`rho ^ 2 * q_prime_py/q_doubleprime_py` collapsed to `rho * q_prime_py/q_doubleprime_py`
(`Dpoly`'s affine coefficients `μ,ν` lose one power of `ρ`), and `baxter_cube_mul_F_eq_G`'s proof
was hand-rederived for the new target (same `field_simp`+`linear_combination` skeleton, `ring`
closed the residual `expand1` step without needing `hcdef`). `baxterMu_pos`/`baxterNu_pos`'s sign
caveat was resolved by strengthening `hrho : rho ≠ 0 → hrho : 0 < rho` throughout
`BaxterPoles.lean`, `BaxterResidue.lean`, `OzFixedPtHExplicit.lean`, `HExplicitRegularity.lean`,
`OzFixedPtHExplicitFinal.lean` (confirmed via grep: `rho ≠ 0` appeared *only* as `hrho`'s type in
every one of these files, so the strengthening is uniform and doesn't touch any other hypothesis;
physically justified since `ρ` is a number density, always `>0`). Full project `lake build`
green (8628 jobs, zero errors, only pre-existing unrelated line-length lint warnings).
`#print axioms` on `baxter_cube_mul_F_eq_G`, `Qhat_pole_iff_G_baxter_zero`, `baxterMu_pos`,
`baxterNu_pos`, `G_baxter_zeros_infinite`, `Qhat_complex_zeros_infinite`,
`oz_h_eq_spliced_h_explicit` shows no new axioms/`sorry` (same sets as before the fix: the
standard three, plus `oz_fixed_pt_unique` for the last one only).

**Numerical re-confirmation (η=0.3,σ=1, scratch script, not committed):**
- `G_baxter`'s **own** first pole (found via its own Newton iteration on the corrected `G_baxter`,
  no separate no-ρ workaround needed) is `6.0580150867934455+1.4367944597364082j`, matching
  `BAXTER.2`'s historical ground truth `6.058015086793445+1.436794459736408j` to machine precision
  (`diff≈9e-16`), and `|G_baxter|` there is `≈1e-13`.
- The corrected `baxter_cube_mul_F_eq_G` identity `(-ik)³·(1-Qhat_complex(k))=G_baxter(k)` holds
  exactly at several generic points (`diff≈1e-12`–`1e-14`).
- `h_explicit(2.0)`, rebuilt on the corrected pole family via unchanged `residue_term`/`A(k)`
  machinery, converges `0.005976→0.005722→0.005673→0.005664→0.005663` as poles used go
  `5→10→20→40→60`, landing exactly on the known ground-truth value `0.005663`.

**⚠ Scope note — this fixes Group POLE only, not Group OZFIX's separate aggregate-identity gap.**
The last numerical point above (`h_explicit`'s *values* now match ground truth) is a different,
weaker claim than the OZFIX.9 cross-check immediately below (does `h_explicit` satisfy the OZ
*fixed-point equation* `oz_forcing+oz_linear_op[h_explicit]=h_explicit` termwise/aggregately,
which is what `OZFIX.6`'s `hcollapse` hypothesis and `oz_h_eq_spliced_h_explicit`'s Lean statement
actually need). That gap is **not** resolved by this pass — re-run OZFIX.9's aggregate check
against the corrected pole family before concluding anything about `OZFIX.6`/`hcollapse`.

**✅ Cross-check from the OZFIX.9 (Route A) scoping — the fix IS sufficient for the aggregate identity
(corrects an earlier note here).** An independent numerical scoping for `OZFIX.9` (η=0.3, σ=1),
re-run against the **now-fixed** `G_baxter = (-ik)³·(1-Q̂)` code, confirms: (1) the corrected `n=0`
pole `6.0580+1.4368i` = ground truth exactly (family denser, `≈2π` spacing), and `h_explicit(2.0) =
0.005688` matches the ground-truth `0.005663`; (2) **the aggregate fixed-point identity
`oz_forcing + oz_linear_op[h_explicit] = h_explicit` now HOLDS** — *exactly* (to machine precision,
per-pole, at every N) for `r ≥ 2σ` where `oz_forcing = 0`, and *slowly convergent to 0* for
`σ ≤ r < 2σ` where `oz_forcing ≠ 0` (at `r=1.5`, diff `0.0385→0.0197→0.0133→0.0101→0.0094` as poles
`N: 10→45`, → 0 like `~1/N` — the `n^{1-2r/σ}=n^{-2}` tail). **A previous version of this note wrongly
concluded "the fix still fails ~50%, residue normalization needs re-deriving" — that was a truncation
artifact** (only `N=11` poles at the slow-converging `r=1.5`); the residue *normalization* is fine, and
correcting the pole/`G` target (as done) is sufficient. The `radial3d_conv` acceptance test (BAXTER.2,
0.05%) is thus **passed** by the fixed construction, consistent with this per-pole/aggregate re-check.

---

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
  `POLE.1`'s `Qhat_complex`).
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
  (confirmed present, avoids the numerical *sampling* `POLE.2` needed — a disk is provably
  convex) gives `baxterPhi_lipschitzOnWith`: a genuine `LipschitzOnWith` fact on any disk
  where A.1/A.2's threshold hypotheses hold throughout.
- **A.4 — Self-map lemma, DONE.** `mapsTo_closedBall_of_lipschitzOnWith_of_dist_le`: generic
  fact (not `baxterPhi`-specific) that a `K`-Lipschitz map moving its center by `≤r(1-K)` maps
  `closedBall` into itself — the standard Banach sufficient condition.
- **A.5 — Assembly, distinctness, infinitude, DONE.** `baxter_G_zero_exists_for_n` composes
  A.1–A.4 with `G_baxter_pole_exists_of_bounds` and the already-unconditional
  `baxterPhi_fixedPt_implies_zero` to get a zero of `G_baxter` in `disk(k1,r)` for a single
  `n`. `G_baxter_pole_family_exists` (added `POLE.4` pass, see that task) extracts the
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
  `CONTACT.5`) — a genuine, `sorry`-free conditional theorem with the gap isolated to one
  numerically-validated (`POLE.2`: checked `η∈{0.05,0.1,0.3,0.45}`, `n` up to `10000`,
  margins `≈18-20%` and improving) fact, not a re-opened research question. Discharging `hstep`
  for the specific guess formula (or substituting a cruder but analytically-bounded guess) is
  the one item that would make `POLE.3` unconditional; not attempted this pass. **Update
  (`POLE.5`, if/when landed): the same pass that would discharge `hstep` is closely related to
  `POLE.5`'s rigorous exponent derivation**, since both need genuine control of `Im(k_n)`'s
  growth — worth revisiting together. **Update 2026-07-15 — `hstep` unified with the mixture MZERO.5
  gap under a shared predicate.** The generic chord-Newton engine + `ChordPoleFamily F` bundle +
  `zeros_infinite_of_chordPoleFamily` now live in `Analysis/BanachPoleFamily.lean`; a chord-Newton
  route `G_baxter_zeros_infinite_of_chordPoleFamily` (this file) consumes it, as does the mixture
  `FMSA.MixtureHSPoles.Q0_det_c_zeros_infinite`. So POLE.3-`hstep` (construct `ChordPoleFamily
  G_baxter`) and **MZERO.5** (construct `ChordPoleFamily det_c`) are now the **same obligation**: `det_c`
  is an `e^{±λs}`-free 2-frequency exp-polynomial in the same Baxter brackets as `G_baxter`
  (`detC_lam_free`), so one asymptotic-family lemma discharges both — close them together. (NB: `POLE.5`
  did land, as the `n^{1−2r/σ}` summability bound; it does *not* discharge `hstep`, but its magnitude
  machinery `abs_exp_neg_ikn_sigma_*`/`G_baxter_deriv_lower_bound_of_zero` is the reusable technique.)
- **Dependency-map update (2026-07-15, post ρ-fix survey): `hstep` is the single abstract→concrete
  gate for the entire `h_explicit` line.** A full-project survey (after the ρ-fix and the numerical
  re-confirmation of `h_explicit`) established: every `h_explicit` theorem (`POLE.5` summability,
  `OZFIX.3` derivative/integral, `OZFIX.5` assembly, `OZFIX.7` regularity, `OZFIX.8`
  `oz_h_eq_spliced_h_explicit`) is stated over an *abstract* family `kfam : ℕ → ℂ` with
  `hkfam_zero`/`hkfam_im`/`hkfam_re` — none depends on `hstep`. But the **only** constructor of a
  concrete indexed family carrying the zero + linear-growth data is
  `G_baxter_pole_family_exists_growth`, which carries `hstep` (`ChordPoleFamily` alone outputs
  `Set.Infinite`, *not* an indexed `kfam` with `Im ≥ 0` + growth). Hence discharging `hstep`
  simultaneously unlocks: `POLE.3` unconditional, `MZERO.5`/`MZERO.7` unconditional (shared
  obligation), concrete instantiation of the whole OZFIX chain, and — together with `hcollapse`
  (Route B, independent of `hstep`) and the `σ`-endpoint (`hcont_sigma`/`hint`) — the retirement
  chain for the `oz_core_closure`/`oz_h_exterior_regularity` axioms, plus `OZ.10`'s mid/high-density
  case and, transitively, `MML.3`/`GA.4`. Items *not* touched by `hstep` or the ρ-fix: `M.4`
  (`Q0_moment_det_pos`), `hslope`, `hblum`, `ha`, `hB`, `hJensen`, `CONTACT.2` (real-analysis route).
  **Hidden gap found and fixed (`POLE.6` below):** `G_baxter_pole_family_exists_growth`'s conclusion
  does *not* carry `hkfam_im : 0 ≤ Im(g n)`, which every `h_explicit` lemma consumes — surfaced from
  the centres and pre-wired into the summability consumer.
- **`hstep` scoping (2026-07-15) — verdict GO; discharge task opened as `POLE.7`.** Python scoping
  (scratch `hstep_scoping.py`/`hstep_scoping2.py`, rerunnable from `POLE.1`'s closed form) found a
  **fit-free, derivable guess** that supersedes the fitted `2·ln(2πn/σ)−2.12` constant:
  `k1(n) := 2πn/σ + (i/σ)·ln|Npoly(x_n)/Dpoly(x_n)|` with `x_n := 2πn/σ` — the modulus part of one
  log-map application at the real point `x_n`. Key numbers (σ=1, `η∈{.05,.1,.3,.45}`, `n` to `10⁴`):
  (i) `Re(k1 n) = 2πn/σ` **exactly** (`hk1re` holds by construction — the fitted guess also had this,
  but the naive full log-lift `φ_n(x_n)` would not); (ii) residual `|φ_n(k1)−k1| ≈ 3.5·ln(x_n)/x_n → 0`,
  matching the true pole distance `|k1−k*|` to 3 digits; (iii) the **elementary mean-value chain**
  `res ≤ sup_seg|φ′|·|k1−x_n| + |arg(N/D)(x_n)|/σ` is *tight* (equality to 3 digits at low `η`, ≤2×
  conservative at `η=0.45`) — every ingredient is `POLE.5`-style `Npoly/Dpoly` triangle-inequality
  material; (iv) checked against the **Lean `K` formula** (`hC`: `K=(8+4|P0|+2|P1|)/(σM)`, `M=x_n−r`)
  plus all admissibility thresholds (`hkN`/`hkD`/`hM1`/`K<1`), `r=1`: `hstep` holds for all `n ≥ N`
  with explicit minimal `N = 4/4/6/17` at `η=.05/.1/.3/.45` (spot-checked to `n=10⁴`); (v) branch
  safety `Re(N/D) ≥ 1.1` over all sampled disks+segments, growing like `x²/(P1+2P2σ)`;
  (vi) `Im(k1 n) ≥ r=1` already from `n≤2` — so `POLE.6`'s `hk1im` is automatic at the `N` above.
  **Chord-route cross-check** (shared `ChordPoleFamily` obligation with `MZERO.5`): at fixed `r=0.3`
  the chord constant is `n`-independent `K≈0.35` and the same guess satisfies the chord `hstep` for
  `n ≥ N = 17/15/9/2` (`r=0.15`: `K≈0.16`, `N = 29/26/17/8`) — one asymptotic analysis feeds both
  routes; `r=1` chord fails (`K≈1.72>1`, the `e^{±σr}` modulus swing), so the chord family must use
  small disks. See Task `POLE.7` below for the Lean discharge plan.
- **✅ 2026-07-16 — `POLE.3` CLOSED UNCONDITIONALLY via `POLE.7`+`POLE.8`:**
  `Qhat_complex_zeros_infinite_unconditional` / `G_baxter_zeros_infinite_unconditional`
  (`HardSphere/BaxterPoleFamilyConcrete.lean`, axiom-clean, hypotheses = physical parameters
  only). The `hstep` gap was discharged by the derived log-lift guess (`POLE.7`,
  `k1_guess_hstep_eventually`), and the remaining family hypotheses (`hMball`/`hkN`/`hkD`/
  `hC`/`hK1`/`hDball`) by `POLE.8`'s concrete `r, M, K, N` instantiation. No fitted constant,
  no conditional hypothesis, no new axiom anywhere in the chain.
- Scratch work (not committed): `baxter11`-prefixed sympy/numpy checks in the same session
  confirming the log-fixed-point strategy, the `Dpoly` coefficient simplification, and the
  `Re(Npoly·conj(Dpoly))>0` leading-order estimate.

### Task POLE.4 — Residue formula + `h_explicit` definition, convergence (conditional)

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
  not tied to `G_baxter` specifics. **Relocated (2026-07-15) to its own stable file**
  `LeanCode/Analysis/ResidueAtSimplePole.lean` (imports only `Mathlib`), since it's a reuse
  target for the mixture groups MML/MZERO (`HSMixture/MixtureHSPoles.lean`, `YukawaDCF/YukawaPoleResidue.lean`)
  which should not need to rebuild alongside the actively-changing `BaxterResidue.lean`.
- **`Chat_complex` — the complex-valued `Ĉ`: DONE.** `LeanCode/HardSphere/
  RadialFourierCHSComplex.lean` (new file), no `sorry`/`axiom`. `Ĉ(k) :=
  radial_fourier(c_HS eta sigma) k` (Task OZ.8) was only defined for **real** `k`; this file
  extends it, mirroring `Qhat_complex`'s construction (`POLE.1`) but for `c_HS`'s **cubic**
  inner polynomial (vs. `q0_poly`'s quadratic) and `radial_fourier`'s **`sin`** kernel with an
  extra `1/k` prefactor (vs. `Qhat_complex`'s bare `exp` integral):
  - `Chat_poly` — the polynomial expansion of `r·c_HS(r)` (`-(a0r+(a1/σ)r²+(a3/σ³)r⁴)`,
    globally continuous, sidestepping `c_HS`'s own jump at `r=σ`, same trick as
    `Qhat_complex_eq_poly`).
  - `Chat_F(k) := ∫r·c_HS(r)·e^{-ikr}dr` (via `Chat_poly`), proved **entire**
    (`entire_poly_exp_integral`, reused directly from `BaxterZeros.lean`) with an explicit
    closed form (`Chat_F_formula`) via new `zeta4_formula` (degree-4 complex-exponential
    moment — `zeta0`–`zeta2` already existed from `POLE.1`; `c_HS`'s cubic term needs degree
    4 once multiplied by the kernel's extra `r`) alongside the existing `zeta1`/`zeta2`.
  - `Chat_J(k) := (Chat_F(-k)-Chat_F(k))/(2i)` — the `sin`-kernel integral via
    `sin(z)=(e^{iz}-e^{-iz})/(2i)`; entire for free (difference of two entire functions, one
    precomposed with negation).
  - `Chat_complex(k) := (4π/k)·Chat_J(k)`, differentiable for `k≠0` (deliberately **not**
    claimed entire — `POLE.3`'s poles all have `Re(k_n)=2πn/σ>0`, so `k≠0` is all the
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
  numerically checking the symmetry claim first, then re-deriving `POLE.3`'s whole
  existence argument for the mirror family if needed. Turned out **unnecessary**: `Npoly`,
  `Dpoly`'s coefficients are all real, giving a clean algebraic identity
  `conj(G_baxter(k)) = G_baxter(-conj(k))` (`G_baxter_conj`, confirmed symbolically via
  `sympy` before formalizing, then closed in Lean via `simp [map_sub, map_add, map_mul,
  Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_conj]` + `ring_nf` — no new estimates
  needed at all). Immediate corollary `G_baxter_zero_mirror`: **any** zero `k` of `G_baxter`
  has a mirror zero `-conj(k)` (for `k=x+iy`, this is `-x+iy` — exactly the classical
  "mirrored `±Re(k)`, same `Im(k)`" pole-pair structure `BAXTER.2`'s original numerics found,
  `k≈±6.058+1.437i`). Applying this to each `k_n` from `POLE.3`'s
  `Qhat_complex_zeros_infinite` immediately gives the negative-real-part family too — no need
  to redo `POLE.3`'s Banach argument a second time.
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
    pole family `kfam : ℕ → ℂ` (stated generically; `POLE.3`'s concrete witness function is
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
- **What's left for `POLE.4`: promoted to its own task, `POLE.5` (below).** The remaining
  gap (rigorous exponent bound + concrete instantiation) is different in *kind* from the rest of
  `POLE.4` (an asymptotic-estimate task, not an assembly/definition task), so it gets its own
  section rather than staying folded into `POLE.4`'s status.

**Status:** ✓ **DONE.** Everything is now in place, including the rigorous exponent bound
(`POLE.5`, below) — no remaining gap in `POLE.4` itself.

---

### Task POLE.5 — Rigorous `n^{1-2r/σ}` magnitude bound + concrete `h_explicit` instantiation

Split out from `POLE.4`'s "what's left" list since it's a genuinely different *kind* of task
(an asymptotic magnitude estimate, in the same family as `POLE.3`'s still-open `hstep`) from
the rest of `POLE.4` (definitions + assembly).

**Status:** ✓ **DONE.** Both sub-parts landed in `LeanCode/HardSphere/BaxterPoles.lean`,
`RadialFourierCHSComplex.lean`, `BaxterResidue.lean` — no `sorry`/`axiom`, `lake build` clean.

- **Rigorous (inequality-level, not `Θ`-heuristic) magnitude bound: DONE.**
  `residue_term_norm_bound` (`BaxterResidue.lean`): at a zero `k` of `G_baxter` with `Im(k)≥0`
  and `‖k‖` past an *existential* threshold, `‖residue_term(k)‖ ≤ C·‖k‖^{1-2r/σ}` for some
  explicit-but-existential `C`. Assembled from:
  - `Npoly_upper_bound`/`Dpoly_upper_bound` (`BaxterPoles.lean`) — the missing upper-bound
    direction of A.1's magnitude estimates (`‖Npoly(k)‖≤(1+a+b+c)‖k‖³`, `‖Dpoly(k)‖≤μ‖k‖+ν`),
    plain triangle-inequality one-liners, not new estimates.
  - `G_baxter_deriv_lower_bound_of_zero`/`G_baxter_neg_lower_bound` — the two non-degeneracy
    theorems (`POLE.4`) **re-derived as direct magnitude *lower bounds*** (`≥σ‖k‖³/8`,
    `≥‖k‖³/4` respectively) rather than by-contradiction non-vanishing facts; the OLD
    `G_baxter_deriv_ne_zero_of_large`/`G_baxter_neg_ne_zero_of_large` are now one-line
    corollaries of these.
  - `abs_exp_neg_ikn_sigma_lower`/`abs_exp_neg_ikn_sigma_upper` (`BaxterPoles.lean`) — two-sided
    `Θ(‖k‖²)` bound on `|e^{-ik_nσ}|` at a zero, from `Npoly(k_n)=Dpoly(k_n)e^{-ik_nσ}`
    (`G_baxter(k_n)=0`, rearranged) plus the A.1 bounds.
  - `abs_exp_ikr_eq_rpow`/`abs_exp_ikr_upper_of_zero` — `|e^{ikr}|=|e^{-ikσ}|^{-r/σ}` (via
    `Real.rpow`, **no** `Complex.log`/branch-cut manipulation needed — the key simplification
    over the original `Θ`-heuristic write-up's `Im(k_n)~\ln n` detour) combined with the lower
    bound above (`Real.rpow_le_rpow_iff_of_neg`'s antitone-in-base direction for negative
    exponents).
  - `Chat_F_norm_bound`/`Chat_complex_norm_bound` (`RadialFourierCHSComplex.lean`) — magnitude
    bound on `Chat_F`/`Chat_complex` given an explicit bound `E` on `|e^{-ikσ}|`, kept symbolic
    in `E`/`‖k‖` (not prematurely simplified) so the caller can cancel `E`'s `Θ(‖k‖²)` growth
    against `Chat_complex_norm_bound`'s `1/‖k‖²` factor to get a genuine `Θ(1)` bound —
    reused for both `Chat_complex(k)` (growing `E`) and `Chat_complex(-k)` (bounded `E≤1`, via
    `Im(k)≥0` alone, no growth control needed, same simplification as `G_baxter_neg_lower_bound`).
  - `exists_hkN_hkT_threshold`/`exists_D_for_exp_neg_bound` (`BaxterPoles.lean`) — **existential
    wrappers** working around a genuine cross-file constraint: `baxterP0`/`baxterP1`/`baxterP2`
    are `private` to `BaxterPoles.lean`, so `BaxterResidue.lean` cannot name them directly even
    though several of the above theorems' *hypotheses* (not conclusions) are stated in terms of
    them. Wrapping the needed thresholds/constants behind `∃` lets `BaxterResidue.lean` use them
    as opaque values without ever writing `baxterP0` itself — a reusable pattern for any future
    cross-file combination of `BaxterPoles.lean`-internal estimates.
  - `h_explicit_term_norm_bound` — the pole+mirror pairing (`residue_term(k)+
    residue_term(-conj k)`), via `G_baxter_zero_mirror` for the zero condition and
    `‖-conj(k)‖=‖k‖`/`(-conj(k)).im=k.im` for the threshold/sign conditions (no new estimate).
  - **Note:** the assembly proof (`residue_term_norm_bound`) needed
    `set_option maxHeartbeats 4000000` — a genuine Lean *performance* issue (many accumulated
    `set`-introduced local constants), not a mathematical one; every individual step is a short,
    ordinary tactic call.
- **Concrete `Summable` instantiation: DONE, as a general reusable theorem.**
  `h_explicit_summable_of_pole_family` (`BaxterResidue.lean`): given *any* pole family `kfam`
  that is a zero set of `G_baxter` with `Im≥0` and `‖kfam n‖` growing at least linearly
  (`c·n+d≤‖kfam n‖`, `c,d>0` — exactly the shape `G_baxter_pole_family_exists`'s
  `hgmem`+`hk1re` data provides), `h_explicit_term` is genuinely `Summable`. Converts
  `residue_term_norm_bound`'s `‖k‖`-based bound to an `n`-based one via the same negative-exponent
  `rpow` antitone technique (`(c·n+d)^{1-2r/σ} ≤ (\min(c,d))^{1-2r/σ}·(n+1)^{1-2r/σ}`), then
  `Summable.of_norm_bounded_eventually` (only finitely many small `n`, where the linear bound
  might fall short of `residue_term_norm_bound`'s own existential threshold `M`, need excluding —
  avoids an awkward `max`-based threshold-matching that an earlier "for all `n`" attempt got stuck
  on). **Not yet wired to a fully concrete `kfam`**: instantiating with
  `G_baxter_pole_family_exists`'s actual witness `g` (extracting `c,d` from its `hk1re`/`hgmem`
  data) is mechanical but not attempted this pass — `g` is still conditional on `POLE.3`'s own
  `hstep`, so a fully unconditional concrete instance isn't available yet regardless.

**What's left:** only the mechanical "instantiate `h_explicit_summable_of_pole_family` with
`G_baxter_pole_family_exists`'s `g`" wiring — a short follow-on, not attempted this pass.
**Update 2026-07-15: DONE as `POLE.6`** (`h_explicit_summable_concrete`,
`HardSphere/HExplicitConcrete.lean`) — see the `POLE.6` record below.

---

### Task POLE.6 — Concrete pole family wired into `h_explicit`'s summability

**Status:** ✓ DONE, axiom-clean (`[propext, Classical.choice, Quot.sound]` for both theorems),
full `lake build` green. New file `LeanCode/HardSphere/HExplicitConcrete.lean` (deliberately *not*
`BaxterResidue.lean`, which a concurrent process edits).

The "short mechanical follow-on" left open by `POLE.5`: instantiate
`h_explicit_summable_of_pole_family` with `G_baxter_pole_family_exists_growth`'s concrete
witness. Two results:

- `pole_family_im_nonneg` — **the `hkfam_im` hidden-gap fix.** The growth theorem's conclusion
  supplies `Injective`, ball-membership, `G_baxter (g n) = 0`, and `c·n+d ≤ ‖g n‖`, but **not**
  the upper-half-plane fact `0 ≤ Im(g n)` that every `h_explicit` lemma consumes (`hkfam_im`) —
  found by the 2026-07-15 dependency survey, invisible until an actual instantiation was
  attempted. Recovered from a new centre hypothesis `hk1im : ∀ n ≥ N, r ≤ Im(k1 n)`
  (numerically comfortable — the fitted centres have `Im(k1 n) = 2·ln(2πn/σ) − 2.12`, already
  `≈ 1.44` at the first pole and growing, vs. `r < π/σ`) via `Complex.abs_im_le_norm`, mirroring
  the growth theorem's own `Complex.abs_re_le_norm` real-part argument.
- `h_explicit_summable_concrete` — the wiring: consumes the growth theorem's *conclusion tuple*
  (`hfam`) plus `hk1im`, and produces `∃ g` injective, `G_baxter`-zero,
  upper-half-plane, with `Summable (h_explicit_term eta sigma rho y g)` for every radial
  distance `y > σ` — the complete hypothesis package downstream `h_explicit` lemmas consume.

**Design note (why the family enters existentially):** `G_baxter_pole_family_exists_growth`'s own
*hypotheses* (`hkN`/`hkD`/`hDball`/`hC`) are stated in terms of the `private` `baxterP0/1/2`, so a
new file cannot restate them — the same cross-file privacy constraint `POLE.5` hit (there solved
by existential wrappers). `h_explicit_summable_concrete` therefore takes that theorem's
*conclusion* (`hfam`, exactly its output shape) as a hypothesis. The conditional chain is
unchanged: the moment `POLE.3`'s `hstep` is discharged, `G_baxter_pole_family_exists_growth`
fires, its conclusion discharges `hfam`, and the concrete summability here becomes unconditional
— `POLE.6` is the pre-wired consumer waiting on the `hstep` gate.

---

### Task POLE.7 — Discharge `hstep` via the derived log-lift guess (Lean)

**Status:** ◐ in progress (opened 2026-07-15 after the `POLE.3` scoping — verdict GO, see the
scoping bullet in `POLE.3` above). New file `LeanCode/HardSphere/BaxterPoleGuess.lean`
(deliberately not `BaxterPoles.lean`/`BaxterResidue.lean` — concurrent processes; note
`BanachPoleFamily`/`ResidueAtSimplePole` moved to `LeanCode/Analysis/` on 2026-07-15).
**Cluster (a) ✓ DONE** (axiom-clean, full build green): `guessP0/1/2` public mirrors +
`Npoly_eq_guess`/`Dpoly_eq_guess` **`rfl` privacy bridges** (a third pattern for the cross-file
privacy constraint — privacy is name-visibility, not kernel-level, so byte-identical public
mirrors are definitionally equal and the bridge closes by `rfl`; complements `POLE.5`'s
existential wrappers and `POLE.6`'s conclusion-tuple hypotheses), `Dpoly_lead_eq`
(`P1+2P2σ = ρ·q_prime_py` — the cancellation making `‖Dpoly(x)‖ ~ ρQ′·x`),
`Npoly_ofReal`/`Dpoly_ofReal` (+`_re`/`_im`) real-axis decompositions, the four two-sided norm
bounds `Npoly_norm_lower/upper`, `Dpoly_norm_lower/upper`, the guess `k1_guess` itself,
`k1_guess_re` (`hk1re` by construction), and `k1_guess_im_ge_of` (`hk1im` reduced to the explicit
real inequality `exp(σr)·(ρQ′xₙ+2|P2|) ≤ xₙ³−|P1|xₙ`).
**Clusters (b)/(c)/(d) ✓ DONE + (e) MASTER THEOREM ✓ DONE** (2026-07-16, all axiom-clean, full
build green): cluster (b) = `Npoly_deriv_norm_le` (reuses `BaxterPoles.lean`'s existing
`Npoly_hasDerivAt` through the `rfl`-bridge — a `guessP`-form `HasDerivAt` goal is *definitionally*
the `baxterP`-form fact, so `exact` accepts it), `Npoly_vertical_diff_le` (segment MVT via
`norm_image_sub_le_of_norm_deriv_le_segment_01'` on the path `t ↦ N(x+t·yi)`), `Dpoly_offReal`
(+`_re`/`_im`, exact affine decomposition via `linear_combination … * Complex.I_mul_I`),
`Dpoly_offReal_norm_lower` (**`y`-independent** lower bound `ρQ′x ≤ ‖D(x+yi)‖` — the off-axis `D`
never needs an MVT), `Dpoly_vertical_diff_le` (exact `ρQ′y`); cluster (c)/(d) helpers =
`abs_log_sub_log_le` (`|log a − log b| ≤ Δ/(b−Δ)`), `abs_arg_le_jordan`
(`|arg w| ≤ (π/2)|Im w|/‖w‖` for `Re w ≥ 0`, via `Complex.sin_arg` + Jordan `Real.mul_le_sin`),
`arg_div_eq_arg_mul_conj`, `mul_conj_perturb_norm_le`, `NconjD_re`/`NconjD_im`; cluster (e) =
budget definitions `deltaN/lowN/upN/deltaD/lowD/upD/wRe/wIm/deltaW`, `log_sub_ofReal_norm_le`
(**key simplification: `Complex.log`'s definition `log W = log‖W‖ + arg(W)·i` splits the residual
exactly — no branch-cut analysis or log-MVT along the segment is ever needed**), `k1_guess_eq`,
and the **master theorem `k1_guess_hstep_of`**: `dist(k1_guess n, φₙ(k1_guess n)) ≤ rr·(1−KK)`
from five explicit real hypotheses (`hNgap : deltaN < lowN`, `hDgap : deltaD < lowD`,
`hwgap : deltaW < wRe`, `hy0`, and the three-part `hbudget`) — `hstep` is now reduced to
elementary per-`n` arithmetic. Plus the threshold-pass inputs `k1_guess_im_le_of`
(`Im ≤ log(upN/lowD)/σ`, the `~3·log x/σ` cap) and `k1_guess_im_nonneg_of`. **THRESHOLD THEOREM ✓ DONE (2026-07-16) — `hstep` PROVED (eventually form), axiom-clean:**

```
k1_guess_hstep_eventually (eta sigma rho rr KK : ℝ) (hsigma : 0 < sigma)
    (hQp : 0 < rho * q_prime_py eta sigma) (htarget : 0 < rr * (1 - KK)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      dist (k1_guess eta sigma rho n) (baxterPhi eta sigma rho n (k1_guess eta sigma rho n)) ≤
        rr * (1 - KK)
```

— for **every** positive target `rr(1−KK)` and **all** physical parameters. `#print axioms` =
`[propext, Classical.choice, Quot.sound]`; full `lake build` green (8638 jobs); no `sorry`.
This is verbatim the log-map `hstep` shape `G_baxter_pole_family_exists` consumes (instantiate
`k1 := k1_guess`, `hk1re := k1_guess_re`). Proof machinery (appended to `BaxterPoleGuess.lean`):
envelope constants `guessCN/CU/CD/CW/CR/CI` (+ sign lemmas), `div_le_div_bound`,
`eventually_log_cap` (`c + 2·log x ≤ ε·x` eventually, via
`Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero`), seven envelope bounds
(`deltaN_le_of` … `deltaW_le_of`, all with linear thresholds `2|P1| ≤ x`, `2·CR/Q ≤ x`), the
per-`n` step `k1_guess_hstep_of_thresholds` (`ε`-conditions `4CNε ≤ 1`, `4CWε ≤ Q`, `ε ≤ 1/2` +
budget split), and the final assembly with
`ε := min(1/2, 1/(4CN), Q/(4CW), στ/(2Ks))`, `Ks := 4CN+2+2πCW/Q` (`ε`-block ≤ τ/2, `x`-block
threshold `x ≥ 4πCI/(σQτ)`). Implementation notes: raw `nlinarith` hit the heartbeat limit in
the fat-context per-`n` theorem — replaced throughout by `linarith` with explicit product hints
(no `maxHeartbeats` bump anywhere); `hy0` from `k1_guess_im_nonneg_of` with `upD ≤ CD·x ≤ x³/2 ≤
lowN` (threshold `2·CD ≤ x`).

**Verdict: `hstep` CONFIRMED.** The `POLE.2`-era fitted-guess gap is closed by the
derived guess — no numerically-fitted constant remains anywhere in the chain.

**What's left (separate follow-on, NOT `hstep`):** the fully unconditional `POLE.3`
instantiation must also discharge `G_baxter_pole_family_exists`'s remaining hypotheses for a
concrete `M`, `K`, `r` — `hMball` (easy: `‖k‖ ≥ Re k ≥ x_N − r`), `hkN`/`hkD`/`hC`/`hK1`
(threshold choices), and `hDball` (a disk inequality on `Re(k²)` — same envelope style as the
cluster (b) bounds, needs the `y`-cap on disks). These were never the flagged `hstep` gap but
are needed to fire the family existence; the `guessP`-`rfl` bridge makes them stateable here.

**Goal.** Prove `hstep` — `dist (k1 n) (baxterPhi eta sigma rho n (k1 n)) ≤ r·(1−K)` for all
`n ≥ N` — for the **concrete, fit-free guess**

```
k1(n) := 2πn/σ + (i/σ)·Real.log ‖Npoly(x_n)/Dpoly(x_n)‖,   x_n := 2πn/σ,
```

with an explicit threshold `N(η,σ,ρ)`. This makes `G_baxter_pole_family_exists(_growth)`,
`Qhat_complex_zeros_infinite` (`POLE.3`), and — through `POLE.6`'s pre-wired consumer — the
concrete `h_explicit` summability all **unconditional**. (The other family hypotheses `hk1re`,
`hk1im`, `hMball`, `hDball`, `hkN`, `hkD`, `hC` must be discharged for the same concrete `k1` —
`hk1re` is by construction, the rest are elementary disk-geometry estimates, included in the
clusters below.)

**Sub-lemma clusters** (from the scoping's tight elementary chain
`res ≤ sup_seg|φ′|·|k1−x_n| + |arg(N/D)(x_n)|/σ`):

- **(a) Real-axis two-sided bounds.** For `x ≥ x₀` explicit: `x³·(1−c₁/x) ≤ ‖Npoly(x)‖ ≤
  x³·(1+c₁/x)` and `(P1+2P2σ)·x·(1−c₂/x) ≤ ‖Dpoly(x)‖ ≤ (P1+2P2σ)·x·(1+c₂/x)` — pure triangle
  inequalities on the coefficients (`POLE.5`'s `Npoly_upper_bound`/`Dpoly_upper_bound` style).
  Feeds `Im(k1 n) = ln‖N/D‖/σ ∈ [(2·ln x_n − c₃)/σ, (2·ln x_n + c₃)/σ]` (`hk1im` + the segment
  geometry).
- **(b) `|φ′| ≤ c₄/‖k‖` off the real axis.** `φ′ = (i/σ)(N′/N − D′/D)`; needs `N`,`D` *lower*
  bounds on the segment `[x_n, k1 n]` and the disk `closedBall (k1 n) r` (all points there have
  `‖k‖ ≥ x_n − r` and `0 ≤ Im k ≤ (2 ln x_n + c₃)/σ`). Partially existing machinery:
  `G_baxter_deriv_lower_bound_of_zero`'s `Npoly/Dpoly` estimates.
- **(c) Argument bound.** `|arg(N(x)/D(x))| ≤ c₅/x` at real `x`: for `Re z > 0`,
  `|arg z| ≤ |Im z|/Re z`, applied to `N(x)·conj(D(x))` (avoids `Complex.arg` subtleties —
  state via `‖log-lift − full log‖` directly, or bound `‖Im(Log w)‖` for `w` near the positive
  real axis).
- **(d) Branch safety.** `Re(N/D) > 0` on segment + disk (numerically `≥1.1`, growth
  `~x²/(P1+2P2σ)`) — needed both for `baxterPhi`'s log to stay on the principal branch (the
  existing converse-direction requirement flagged in `baxterPhi_fixedPt_implies_zero`'s
  docstring) and for (c).
- **(e) Assembly.** Mean-value segment estimate (Mathlib
  `Complex/norm_image_sub_le_of_norm_deriv_le_segment`, already used in `POLE.3`'s Lipschitz/MVT
  work) + (a)–(d) ⇒ `res(n) ≤ (c₆·ln x_n + c₇)/x_n`; then `ln x ≤ x^{1/2}`-type Mathlib bounds
  give an explicit `N` with `res ≤ r·(1−K)` for `n ≥ N`, `K` from `hC`'s formula. Numerical
  targets to beat (σ=1, r=1): minimal `N = 4/4/6/17` at `η=.05/.1/.3/.45`; the Lean constants
  may land at somewhat larger `N` — any explicit `N` suffices for `POLE.3`.

**Bridge to `MZERO.5`.** The same (a)–(e) analysis with small disks (`r=0.3`: chord `K≈0.35`,
`N=17/15/9/2`) discharges the chord `ChordPoleFamily (G_baxter)` `hstep`/`hbound`; the mixture
`det_c` version is the 2-frequency extension (`detC_lam_free`'s exp-polynomial class) — planned
as the follow-on after the 1-frequency case lands.

---

### Task POLE.8 — Fire the log-route family: `POLE.3` unconditional (Lean)

**Status:** ✓ **DONE (2026-07-16) — `POLE.3` CLOSED UNCONDITIONALLY.** Axiom-clean, sorry-free,
first build green. `LeanCode/HardSphere/BaxterPoleFamilyConcrete.lean` (imports `BaxterPoleGuess`;
`BaxterPoles.lean` read-only — hypotheses stated via `guessP0/1/2`, applied by defeq through the
`rfl`-bridge, silently at the final `exact`). Headline theorems (hypotheses = physical parameters
only; `#print axioms` = `[propext, Classical.choice, Quot.sound]` for all):

```
Qhat_complex_zeros_infinite_unconditional : {k | 1 - Qhat_complex eta sigma rho k = 0}.Infinite
G_baxter_zeros_infinite_unconditional     : {k | G_baxter eta sigma rho k = 0}.Infinite
h_explicit_summable_unconditional         : ∃ g, Injective g ∧ (∀ n, G_baxter … (g n) = 0) ∧
                                              (∀ n, 0 ≤ (g n).im) ∧
                                              Summable (h_explicit_term eta sigma rho y g)  (y > σ)
```

The third fires `POLE.6`'s pre-wired consumer — the **concrete `h_explicit` pole family with
summability is now fully unconditional**. Construction: helpers `mem_closedBall_re_ge`/
`_abs_im_le`/`_norm_le`, `k1_guess_Mball`, `dball_key_of` + `k1_guess_Dball_of` (disk inequality
via `(k²).re = k.re²−k.im²` + disk geometry + `y ≤ x/2` cap), `im_key_of`,
`k1_guess_im_bounds_of` (ε=1/2 replica of the POLE.7 log-cap assembly), and the 12-conjunct
package `k1_guess_family_conditions` with witnesses `r = min 1 (π/2σ)`,
`M = max(max 1 (2S))(max (2ρQ″/ρQ′) (2(8+4A+2B)/σ))`, `K = toNNReal((8+4A+2B)/(σM)) ≤ 1/2`,
`N = max(max N₁ N₂) 1` (N₁ = hstep threshold from `k1_guess_hstep_eventually`, N₂ = 7-fact
`filter_upwards` bundle pushed along `2πn/σ → ∞`).

**Goal.** Discharge the remaining hypothesis block of `G_baxter_pole_family_exists(_growth)` /
`G_baxter_zeros_infinite` / `Qhat_complex_zeros_infinite` (byte-identical across the four; all
consumed in `baxter_G_zero_exists_for_n`) for `k1 := k1_guess`, with concrete parameter-dependent
constants — concluding **`Qhat_complex_zeros_infinite_unconditional`** (hypotheses = physical
parameters only) ⇒ `POLE.3` closed unconditionally, plus the `POLE.6` payoff
`h_explicit_summable_unconditional`.

**Constant choices (no quantifier circularity).** `r := min 1 (π/(2σ))`;
`M := max(1, hkN-bound, hkD-bound, 2(8+4A+2B)/σ)` (A,B := |guessP0|,|guessP1|);
`K := Real.toNNReal((8+4A+2B)/(σM))` — `hC` by construction, `≤ 1/2 < 1` by the `M` choice;
`N := max` over the finitely many eventually-thresholds (`hstep` from
`k1_guess_hstep_eventually` at target `r(1−K) > 0`; `hMball`: `xₙ − r ≥ M`; `hDball`;
`Im ≥ r` for POLE.6's `hk1im`).

**Numerical scoping (2026-07-16, `pole89_scoping.py`) — GO.** At `r = min(1, π/2σ) = 1`
(σ=1): `hDball` margins `Q·Re(k²) − CL·‖k‖` are hugely positive from small `n` and grow `~x⁴`
(η=.05/.1/.3/.45: first-good `n = 2/2/8/22`, margin at `n=10⁴` ≈ `2.7e9/6.1e9/3.3e10/8.6e10`);
concrete `M = 18.7/22.2/49.8/103.5`, `K = 0.5` exactly (by design), `hMball` threshold
`n ≥ 4/4/9/17`; `hstep` residual at the combined threshold ≤ `r(1−K) = 0.5` everywhere except
η=.05 needs a slightly larger `N` (the ∃N absorbs it).

**Lemma inventory.** (1) disk-geometry helpers (`Re k ≥ Re c − r`, `|Im k| ≤ |Im c| + r`,
`‖k‖ ≤ ‖c‖ + r` on `closedBall c r` — the inline reverse-triangle pattern of
`G_baxter_pole_family_exists_growth` extracted as named lemmas); (2) `k1_guess_Mball`
(`‖k‖ ≥ Re k ≥ xₙ − r ≥ M`); (3) `k1_guess_Dball` — the real work: `CL·‖k‖ < Q·Re(k²)` on the
ball with `CL := Q″ + Q·S + Q″·S`, `S := A+B+2C`, via `Re(k²) = (Re k)²−(Im k)² ≥
(xₙ−r)²−(yₙ+r)²`, `‖k‖ ≤ xₙ+yₙ+r`, and the sublinear cap `yₙ ≤ ε·xₙ`
(`k1_guess_im_le_of` + `eventually_log_cap`, both existing); (4) `Im(k1_guess n) ≥ r`
eventually (log lower bound `log(lowN/upD)/σ → ∞`); (5) final assembly theorems.

---

### Task POLE.9 — Chord `ChordPoleFamily (G_baxter)` (shared `MZERO.5` obligation)

**Status:** ✓ **DONE (2026-07-16)** — axiom-clean, sorry-free, zero warnings, full `lake build`
green. `LeanCode/HardSphere/BaxterChordFamily.lean` (1211 lines) constructs the
`ChordPoleFamily (G_baxter eta sigma rho)` for all physical parameters and fires
`G_baxter_zeros_infinite_of_chordPoleFamily`:

```
chordPoleFamily_G_baxter_exists : Nonempty (ChordPoleFamily (G_baxter eta sigma rho))
G_baxter_zeros_infinite_chord   : {k | G_baxter eta sigma rho k = 0}.Infinite
```

The **1-frequency chord obligation (≡ POLE.3-side of the shared `ChordPoleFamily` predicate) is
closed**; the 2-frequency `det_c` extension (the actual `MZERO.5` discharge, "MZERO.12") is the
mixture-session follow-on, now with a complete worked template. Deliverables: `rfl` bridge
`G_baxter_deriv_eq_guess`; exact affine `Dpoly_sub_eq`; **`exp_at_k1_guess`** (the phase kill,
via `Complex.exp_int_mul_two_pi_mul_I` at `m := −n` + `Real.exp_log`); the purely algebraic
**`norm_sub_ratio_mul_le`** (`‖A − (‖A‖/‖B‖)B‖ ≤ 2|Im(A·conj B)|/‖B‖` for `Re(A·conj B) ≥ 0` —
normSq expansion, NO arg/trig); per-`n` estimates `Npoly_x_norm_half_cubic`, `t_ratio_lower`
(`x² ≤ 2·guessCD·t`), `G_baxter_deriv_k1_norm_lower` (`(σ/2)Qxt ≤ ‖G′(k1)‖`),
`G_baxter_deriv_ball_diff_le` (`≤ (σ/4)Qxt` on the disk, via `Complex.norm_exp_sub_one_le`),
`G_baxter_k1_norm_le` (`≤ (1/40)Qxt`); assembly `chord_conditions_eventually` (eleven
thresholds + log-cap) and `k1_guess_dist_gt` (separation from the exact `2π/σ` spacing,
`Real.pi_gt_three`). Constants: `r := 1/(10σ)` (σr = 1/10 — tightened from the scoping's 0.15,
as required once `Complex.norm_exp_sub_one_le`'s factor-2 enters), `K := 1/2`, budget splits
`hbound = 1/5 + 1/50 + 3/100 = 1/4` and `hstep = (1/40)Qxt = (r/2)·(σ/2)Qxt` exactly.
Lean lesson (recorded): a single-step `calc` whose proof is a multi-line `by` block, used as the
last tactic of a `have`, mis-parses (swallows following tactics) — use direct `exact`.

**Two structural facts (2026-07-16 planning) that make this tractable:**
1. **Exact phase kill:** `e^{−i·k1_guess(n)·σ} = ((‖N(xₙ)‖/‖D(xₙ)‖ : ℝ) : ℂ)` — REAL POSITIVE
   exactly (`Re k1 = 2πn/σ` ⇒ `e^{−i·2πn} = 1`; `e^{σy} = ‖N‖/‖D‖` by `Real.exp_log`). The
   chord numerator becomes `G(k1) = N(k1) − D(k1)·(‖N(x)‖/‖D(x)‖)`, dominant part
   `‖N(x)‖·(unit-phase difference)` ≈ `‖N(x)‖·|arg(N·conj D)|` — `POLE.7`'s cluster-(c) arg
   machinery applies; chord step `~ log x/x → 0`.
2. **`G′` at the guess:** `‖e^{−ik1σ}‖ = ‖N(x)‖/‖D(x)‖ ~ x²/Q` exactly ⇒ the `iσD·e^{−ikσ}`
   term dominates `G_baxter_deriv`: `‖G′(k1)‖ ≳ σx³` (⇒ `hFp1`). `hbound`'s `K` is driven by
   the exp-factor variation `|e^{−i(s−k1)σ} − 1| ≤ σr·e^{σr}` on radius-`r` disks ⇒ `r := c₀/σ`
   with `c₀ ≈ 0.3` (numerics: `K≈0.35`, thresholds `N = 17/15/9/2` at `η=.05/.1/.3/.45`).

**Numerical scoping (2026-07-16, `pole89_scoping.py`) — GO.** At `r_c = 0.3/σ`: the exact
phase kill confirmed to machine precision (`|e^{−ik1σ} − ‖N‖/‖D‖| ~ 1e-13`, only float roundoff
at huge `n`); `‖G′(k1)‖/(σ·(‖N(x)‖/‖D(x)‖)·Q·x) → 1.000` (the envelope IS the asymptotic
magnitude); `K_chord ≈ 0.350` and is **entirely** the exp-factor variation
(`max |e^{−i(s−k1)σ}−1| = e^{0.3}−1 = 0.3499` — polynomial parts negligible); chord step ≤
`r_c(1−K)` from `n ≈ 20/20/10/2` at `η=.05/.1/.3/.45`. Choose `K := 1/2` for slack.

**Fields plan.** `s1 n := k1_guess (n+N₀)`, `F′ := G_baxter_deriv`, `Fp1 n := G_baxter_deriv (s1 n)`,
`hderiv := G_baxter_hasDerivAt` (free), `hsep` from the exact `2π/σ` real-part spacing (`> 2r`).
De-scope discipline: if the `G′` bounds resist after honest effort, record partials + scoping and
stop — the chord route is redundant for `POLE.3` (its value is the `MZERO.5` bridge).

## Task POLE.11 — Baxter poles in the open half-plane ⇒ `baxterPsi` decay — DILUTE DONE BOTH WAYS (`η<0.177`: premise poles-in-UHP ✓ + decay ✓), general-`η` OPEN/research-scale (task b)

**Goal.** Every zero of `1 − ρ·Qhat_complex(z)` (the Baxter poles) lies in the open half-plane whose
sign gives decay ⇒ the constructed `baxterPsi` **decays** on `[σ,∞)`. This is the analytic **core of
the axiom `baxter_exterior_regularity`** (OZFIX.22): its boundedness/`→0` clauses ARE this decay.

**Nature.** A **Hurwitz / root-location (stability)** statement for the explicit transcendental
`1−ρQ̂(z)` (polynomial × exp). Techniques: Hermite–Biehler, or the POLE group's own machinery —
`MA.11` (argument principle, DONE) + a half-plane lower bound `|1−ρQ̂| > 0` (POLE.5 partial) + the
pole-family control (`pole_family_im_nonneg`, POLE.8/9). **Overlaps but exceeds POLE.4/8/10**: those
give *infinitude* and one UHP family, NOT *all zeros located in one open half-plane*. Research-scale
— recommend its **own session** (like the MA.12 Krein task).

**Payoff if done.** (i) ⇒ `BAXTER.16` (task a: no real zeros of the symbol). (ii) Supplies the decay
clauses of `baxter_exterior_regularity` — full retirement of that axiom additionally needs discharging
`OZ★`'s integrability (making `baxterPsi_eq_phi_add_rho_conv` unconditional) + the remaining
regularity clauses. (iii) **May help `oz_fixed_pt_unique` directly**: with poles in the open half-plane
the bounded homogeneous OZ solutions are all *decaying* modes, and a decaying homogeneous solution that
also vanishes on the core is forced to `0` — a decay-based uniqueness that could reduce reliance on the
`MA.12` Krein inversion (Route 3's wall was precisely the *absence* of this decay control for merely
bounded `d`; see `proof_notes_ozfix.md` OZFIX.23). Worth checking whether (b) alone closes uniqueness.
Home: `HardSphere/BaxterPoles.lean` / `BaxterZeros.lean` / new.

**✅ 2026-07-18 — DILUTE REGIME `η < (3−√7)/2 ≈ 0.177` DONE (axiom-clean), via a DIFFERENT
(elementary) route that BYPASSES pole-location entirely.** New file
`HardSphere/BaxterDiluteDecay.lean` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`,
no `sorry`). Instead of locating the zeros of `1−ρQ̂`, work **directly on the constructed Volterra
solution** `baxterPsiOuter` (the exact object in `baxter_exterior_regularity`, sidestepping the
`oz_fixed_pt_unique`/`hcollapse` circularity that blocks the `h_explicit` route):
- **Kernel is `L¹`-contractive in the dilute regime.** `q0_poly ≤ 0` on `[0,σ]`
  (`q0_poly_nonpos_of_nonneg`; factor `ρ(r−σ)·π(σ(1−η)+r(1+2η))/(1−η)²`, both non-`ρ,(r−σ)` factors
  `>0`), `q0_poly = 0` on `[σ,∞)` closed (`q0_poly_eq_zero_of_ge`). **Closed form**
  `M := ∫₀^σ|q0_poly| = η(4−η)/(1−η)²` (`q0AbsL1_eq`, FTC of the cleared quadratic + `πρσ³=6η`),
  and `M < 1 ⟺ 2η²−6η+1 > 0 ⟺ η < (3−√7)/2` (`q0AbsL1_lt_one_of_dilute`).
- **Forcing has compact support `[σ,2σ]`.** `baxterForcing = 0` for `r ≥ 2σ`
  (`baxterForcing_eq_zero_of_two_sigma_le`; for `s∈[0,σ]`, `r−s ≥ σ` ⇒ kernel `0`), hence bounded on
  `[σ,∞)` by its max on the compact support (`baxterForcing_bounded_on_Ici`).
- **Boundedness** `∃C, ∀ r≥σ, |baxterPsi r| ≤ C = Φ/(1−M)` (`baxterPsi_bounded_of_dilute`):
  max-point argument — on any `[σ,b]`, continuous `|ψ|` attains max `S` at `rs`, renewal eq gives
  `S ≤ Φ + M·S` (kernel integral `≤ M·S` via `∫₀^a|q0| ≤ M`, `q0_abs_integral_le_L1`), so
  `S ≤ Φ/(1−M)`, uniform in `b`.
- **Decay** `baxterPsiOuter → 0` (`baxterPsi_tendsto_zero_of_dilute`): geometric window induction —
  for `r ≥ 2σ` the forcing vanishes, so `|ψ(r)| ≤ M·sup_{[r−σ,r]}|ψ|` (pointwise
  `|q0(r−t)||ψ(t)| ≤ |q0(r−t)|·(MⁿCb)` — either kernel `0` or `t` deep enough for the IH); iterating
  gives `|ψ(r)| ≤ Mⁿ·Cb` for `r ≥ 2σ+nσ`, and `Mⁿ→0`.
- **Axiom clauses discharged** (dilute): `baxterPsi_bounded_Ici_of_dilute` (= clause 2 of
  `baxter_exterior_regularity`), `r_mul_ozBaxterFixedPt_tendsto_zero_of_dilute` (= the `Tendsto
  (r·ozBaxterFixedPt) atTop 0` decay inside clause 6, via `ozBaxterFixedPt = baxterPsi/·`). Physical
  wrappers `*_of_eta_dilute` take `η < (3−√7)/2` directly.

**Why this doesn't extend to full `η<1` (the genuine research wall stands):** the argument is pure
`L¹` contraction, and `M = η(4−η)/(1−η)² ≥ 1` for `η ≳ 0.177` — the kernel mass exceeds `1`, so no
weighted-Neumann/Grönwall bound reaches the dense regime (`e^{δu}` weighting only makes `M` larger).
Decay there is **genuinely spectral** (cancellation/oscillation in `q0`, i.e. zeros of `1−ρQ̂` off the
real Laplace axis), which is exactly the Hermite–Biehler/Paley–Wiener input POLE.11-general needs and
Mathlib lacks. So: **dilute base case = elementary + done; general `η` = still the Wiener–Hopf
research task.** The dilute file also supplies the `q0_poly ≤ 0` sign lemma that BAXTER.16's own
dilute route (`proof_notes_baxter.md`) was missing.

**✅ 2026-07-18 (cont.) — ROOT-LOCATION PREMISE proven for dilute (axiom-clean).** New file
`HardSphere/BaxterDilutePoleLocation.lean` proves POLE.11's actual *premise* (poles-in-open-UHP),
not just the decay conclusion. Key: the same `L¹` mass bound extends to the **closed lower
half-plane** because `‖e^{−ikr}‖ = e^{r·Im k} ≤ 1` for `Im k ≤ 0`, `r ≥ 0`:
`‖Q̂(k)‖ = ‖∫₀^σ q0 e^{−ikr}‖ ≤ ∫₀^σ|q0|e^{r·Im k} ≤ ∫₀^σ|q0| = M < 1` (`Qhat_complex_norm_le_L1_of_im_nonpos`)
⇒ `Q̂(k) ≠ 1` (`Qhat_complex_ne_one_of_im_nonpos_of_dilute`) ⇒ `G_baxter(k) ≠ 0` for `k≠0`
(`G_baxter_ne_zero_of_im_nonpos_of_dilute`, via `baxter_cube_mul_F_eq_G`: `G=(-ik)³(1−Q̂)`) ⇒
**`baxter_pole_im_pos_of_dilute`: every nonzero `G_baxter` zero has `0 < Im k`** (open UHP). So for
`η<(3−√7)/2` the dilute picture is COMPLETE both ways: premise (all poles in open UHP) ✓ AND
conclusion (decay) ✓ — mutually consistent, and the premise is non-vacuous.

**General-`η` scoping (the precise wall).** Two halves, both Mathlib-absent:
1. **Root-location** (all zeros of `G_baxter` in open UHP). The elementary `‖Q̂‖≤M` bound is tight on
   the real axis (`Im k=0`, gives exactly `M`), so it caps at `M<1` ⇔ `η<0.177`. Beyond, the real-axis
   case = full BAXTER.16 (coupled Re/Im trig-positivity, research-scale); the strict-LHP case would
   still hold (`‖Q̂(k)‖ ≤ ∫|q0|e^{r·Im k} < M` for `Im k<0`, and `→0` as `Im k→−∞` — poles can't be
   deep in the LHP for ANY `η`, a free strip bound `Im k > −s*(η)`), but that does NOT reach `Im k>0`
   near the real axis. Genuine tool = **Hermite–Biehler** for the exp-polynomial `Npoly−Dpoly·e^{−ikσ}`
   (not in Mathlib), or an indented-contour argument principle (MA.11 ✓) needing real-axis
   nonvanishing (= BAXTER.16) as the contour-boundary input — chicken-and-egg with half 1.
2. **Root-location ⇒ decay** of the Volterra `baxterPsiOuter`. Even GIVEN all poles in open UHP, the
   decay needs either (a) the residue/Mittag-Leffler representation `baxterPsi = r·Σ Bₙe^{ikₙr}` to
   equal the Volterra solution (inverse-Laplace identity, hard), or (b) a **Paley–Wiener/Wiener-algebra
   renewal theorem** (resolvent kernel `∈ L¹` ⇐ symbol `1−q̂0` nonvanishing on closed RHP) — neither in
   Mathlib. The transfer-operator view: decay ⇔ spectral radius of a fixed compact integral operator on
   `C([0,σ])` is `<1`; `M<1` gives `‖·‖<1` (dilute), general needs `spr<1` = the pole condition.
**Verdict:** both halves are genuinely research-scale and need Mathlib-absent analysis
(Hermite–Biehler / Paley–Wiener). The dilute regime is the complete elementary base case; no
elementary middle ground extends meaningfully past `η<0.177`. Recommend general-`η` as its own
program (Hermite–Biehler formalization first).

**✅ 2026-07-18 (cont.) — GENERAL-`η` SCAFFOLD LANDED: axiom-clean conditional reductions + the two
hard inputs registered as MA-group axioms (awaiting processing).** The general-`η` architecture is
now in place, with the two Mathlib-absent theorems isolated behind explicit interfaces:
- **Root-location reduction** `baxter_pole_im_pos_of_symbol_ne_one` (`BaxterDilutePoleLocation.lean`,
  axiom-clean): `Q̂ ≠ 1` on closed LHP ⇒ all Baxter poles in open UHP. The dilute theorem is now its
  instance. General-`η` `baxter_pole_im_pos` (`BaxterHermiteBiehler.lean`) discharges the hypothesis
  via **MA.14** — now **shrunk to a bounded core**: the outer region `‖Dpoly‖<‖Npoly‖` is a THEOREM
  `G_baxter_ne_zero_of_norm_dominant` (axiom-clean, all `η`; a zero forces
  `‖Npoly‖=‖Dpoly‖e^{σ·Im k}≤‖Dpoly‖`), leaving only the **bounded core** `{‖Npoly‖≤‖Dpoly‖}` as the
  axiom `G_baxter_ne_zero_on_lower_core` (`qhat_complex_ne_one_of_im_nonpos` is now a *theorem*).
  Verified true incl. the worst ray (`G_baxter(−bi)` real, `<0 ∀b>0`).
- **Decay reduction** `baxterPsi_bounded_Ici_of_tendsto_zero` +
  `r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero` (`BaxterExteriorDecayReduction.lean`,
  axiom-clean): **both** `baxter_exterior_regularity` clauses (boundedness + the `r·ozBaxterFixedPt`
  decay) follow from the single fact `baxterPsiOuter → 0` (boundedness = `→0` + compact-continuity).
  That fact is supplied by **MA.13** `volterra_renewal_tendsto_zero` (Paley–Wiener, abstract axiom in
  `Analysis/WienerRenewal.lean`), **wired** to `baxterPsiOuter` in `BaxterRenewalDecay.lean`
  (`baxterPsiOuter_tendsto_zero_of_symbol`, the `[σ,∞)→[0,∞)` shift; MA.13 statement-fix dropped the
  unsatisfiable `t<0` support clause).
- **✅ END-TO-END LOOP CLOSED (2026-07-18)** — `BaxterExteriorRegularityGeneral.lean`: the symbol
  bridge `qhat_symbol_nonvanishing` (`z=ik`: `∫₀^σ q0_poly·e^{−zt}=Q̂(−iz)`, `Re z≥0 ⟺ Im(−iz)≤0`;
  `z=0` removable via `Q̂(0)=∫q0≤0≠1`) feeds MA.14 into MA.13's wiring ⇒ general-`η`
  `baxterPsi_bounded_Ici` + `r_mul_ozBaxterFixedPt_tendsto_zero`. **`#print axioms` of both = exactly
  `{standard three, MA.13 volterra_renewal_tendsto_zero, MA.14 core G_baxter_ne_zero_on_lower_core}`**
  — the two exterior clauses of `baxter_exterior_regularity` now rest, for all physical `η<1`, on just
  the two Wiener/HB math axioms.
- **MA.13/MA.14 registered** in `MATH_AXIOMS.md` (Axioms 5/6, task records). Trade rationale: each is
  a classical *math* theorem retiring (part of) a *physics* axiom — a net epistemic gain. Both are
  invoked ONLY for `η ≥ (3−√7)/2` (the dilute cases are unconditional theorems). MA.14 is the one
  domain-referencing MA axiom (mentions `Qhat_complex`); full abstraction to a Pontryagin
  quasi-polynomial HB statement is deferred to avoid a guessed-hypothesis false axiom.

So: **dilute = fully unconditional (both halves); general-`η` = axiom-clean reductions + 2 named
math axioms awaiting proof.** The remaining work is exactly proving MA.13 (Wiener algebra) and MA.14
(HB via MA.11 + winding), each a self-contained classical-analysis formalization.

### POLE.11 as the MASTER KEY — full retirement roadmap (2026-07-18, post-MA.12)

After **MA.12** (`wienerHopf_positive_symbol_injective`, PROVED via Plancherel coercivity — NOT an
axiom) plus the dilute machinery above, **POLE.11-general is the single remaining bottleneck** whose
proof cascades to retire BOTH surviving physics axioms (`oz_fixed_pt_unique` +
`baxter_exterior_regularity`), i.e. **2 → 0**. Handoff map for the session proving it:

**The cascade (what POLE.11-general unlocks):**
```
POLE.11-general  (all zeros of 1−Q̂(z) off ℝ / in one open half-plane, all η<1)
  ⟹ (a)  1−ρĈ(k) = |1−Q̂(k)|² ≥ ε > 0  ∀k     [= BAXTER.16 uniform symbol positivity]
  ⟹ (b)  baxterPsi decays on [σ,∞)             [= baxter_exterior_regularity load-bearing clauses]
 (a) + MA.12 + OZ→WH bridge                ⟹  retire  oz_fixed_pt_unique
 (b) + discharge OZ★ integrability + rest  ⟹  retire  baxter_exterior_regularity
```

**NO NEW MATH AXIOM is required.** MA.12's coercivity route removed the only candidate (Krein's
index theorem — the positive-symbol case needs coercivity, not the winding-number/index machinery).
Two sub-routes for POLE.11-general, both new-axiom-free:
- **(i) complex root-location via the argument principle** — `MA.11` (`argumentPrinciple_count`,
  PROVED) counts zeros of `1−Q̂` inside a contour; show the count off the physical half-plane is `0`
  via magnitude bounds on the contour (`POLE.5` partial `|G_baxter|` estimates + `Npoly`/`Dpoly`
  leading behaviour). ⚠ CONSUMES the EXISTING axiom `MA.1` (`circleIntegral_eq_sum_of_small_circles`,
  which `MA.11` rests on) — adds NONE. Rouché, if needed, is derivable from `MA.11`, not a new axiom.
- **(ii) direct real-variable BAXTER.16 positivity** — prove `1−ρĈ(k) > 0` on the compact range
  `[0, 1+2|ρ|·cHS_bound]` (large-`k` already done: `one_sub_rho_mul_radial_fourier_c_HS_ne_zero`)
  from the explicit trig-rational closed form `radial_fourier_c_HS_formula`. Pure real analysis,
  consumes NOT EVEN `MA.1` — but harder (coupled `sin/cos/k`; `1−A` changes sign for η≳0.45, so the
  strict positivity genuinely couples Re and Im).

**The OZ→WH bridge** (the one other genuinely-missing formalization piece, no axiom): connect the
concrete OZ operator / `oz_fixed_pt_unique` setup to MA.12's abstract `fourierMul a` on
`Lp ℂ 2 volume` with matching WH boundary conditions (`u=0` on `x≤0`, `Tu=0` on `x≥0`). Uses Mathlib
Fourier/Plancherel (`MeasureTheory.L2.fourierTransformₗᵢ`) + the codebase oddExt/baxterK reduction
(OZFIX.18/19). This also closes the L²↔bounded gap — the difference of two bounded fixed points must
land in `L²`, supplied by (b) (decay).

**DISCIPLINE — do NOT axiomatize POLE.11 itself.** It is the hard core / physics-specific ("Baxter
WH factor zero-free in the closed half-plane" = PY no-spinodal), exactly the "assumes the hard part"
kind the project rejects (cf. the rejected arc-vanishing axiom, `MATH_AXIOMS.md`). Prove it (route i
or ii) or record partials + scoping; do not shortcut with an axiom.

**Available pieces (PROVED/axiom-clean unless noted):** `MA.11` argument principle; `MA.12` coercivity
engine; `baxter_wiener_hopf_factorization` (`1−ρĈ=(1−A)²+B²`); large-`k` nonvanishing; `q0_poly≤0`
sign lemma + `q0AbsL1=η(4−η)/(1−η)²`; dilute decay/boundedness (this file); explicit symbol
`radial_fourier_c_HS_formula`. Missing: POLE.11-general (this task) + the OZ→WH bridge.

### POLE.11-general / `MA.14` — route triage (2026-07-21): TWO elementary routes REFUTED, one COMPLETE route found

Dedicated pass on `baxter_no_open_lhp_pole_core`, the sole remaining domain-referencing axiom
(`HardSphere/`).  Statement: `G_baxter ≠ 0` on `{Im k < 0, k ≠ 0, ‖Npoly‖ ≤ ‖Dpoly‖}`, where
`G_baxter = Npoly − Dpoly·e^{−ikσ}`, `Npoly` **cubic**, `Dpoly` **linear**.

**Status of the statement itself: TRUE, no bug.**  Verified by a deflated argument-principle count
(`verify_ma14_route.py`): `G` has an *exact triple* zero at `k=0` (from the `(−ik)³` factor), which
poisons any naive contour count — after dividing it out, the open-LHP zero count is **0**, robustly
across `R ∈ {15,40,100}`, `ε ∈ {1e-3,1e-6}` and `η ∈ [0.02,0.97]`.  (Contour orientation was
calibrated against `f(z)=z−z₀` first.)  For contrast the *upper* half-plane carries 4 zeros inside
`|k|<15` and 12 inside `|k|<40` — the Baxter pole family of Group POLE.  So this is **not** a fifth
statement bug; unlike clause 6a and axiom 7b, MA.14 says what it should.

**REFUTED route A — "`Npoly` is Hurwitz-stable, then max-modulus on `Dpoly·e^{−ikσ}/Npoly`."**
The substitution `k = iu` makes `Npoly(iu) = u³ + P0u² − P1u + 2P2` a **real** cubic (`Im k = Re u`),
so root location *looks* like a Routh–Hurwitz sign check — and the elementary
"`v³+a₂v²+a₁v+a₀`, all `aᵢ>0`, `a₂a₁>a₀` ⇒ no root with `Re v ≥ 0`" is a two-line `nlinarith`
(`y=0` case immediate; `y≠0` case substitute `y² = 3x²+2a₂x+a₁` into the real part, everything is
`≤ 0` plus `a₀−a₂a₁ < 0`).  **But the sign conditions fail**: `Npoly` has **exactly one root in the
open LHP**, purely imaginary at `k = −i t₀` with `t₀ ≈ 0.79 (η=0.05) → 1.97 (η=0.95)`.  So `Dpoly/Npoly`
has a pole in the region and Phragmén–Lindelöf is inapplicable.  *Do not retry this.*

**REFUTED route B — "modulus only: `‖Npoly‖ > ‖Dpoly‖·e^{σ·Im k}` on the whole open LHP."**
This would make MA.14 phase-free.  It is **false**, and fails exactly at route A's obstruction: at
`k = −i t₀` the left side is `0`.  Measured `min(‖N‖−‖D‖e^{σ Im k})/|k|` = `−0.72 (η=0.05)` down to
`−1879 (η=0.95)`, always attained at `k = −i t₀`.  **MA.14 is irreducibly topological** — it needs a
zero *count*, not a pointwise bound.  (`G ≠ 0` at `−i t₀` holds only because `Dpoly(−it₀) ≠ 0`.)

**COMPLETE route C — homotopy in `η` (zero count is locally constant).**  The open-LHP zero count of
`G_baxter` is an integer-valued continuous function of `η ∈ (0,1)`; it is `0` at small `η`; hence `0`
throughout.  All four inputs are now identified, and **three of the four already exist**:

| # | input | status |
|---|---|---|
| 1 | base case `η < η* = (3−√7)/2 ≈ 0.1771` | ✅ **PROVEN** `G_baxter_ne_zero_of_im_nonpos_of_dilute` (`BaxterDilutePoleLocation.lean`) |
| 2 | no crossing through `ℝ\{0}`: `‖Npoly‖²−‖Dpoly‖² = k⁶ > 0` | ✅ **PROVEN** (`BaxterPoles.lean`; also what retired `pyhs_no_spinodal`) |
| 3 | no zero emerges from the boundary point `k=0` | ✅ **FORMALIZED, axiom-clean** — `BaxterOriginTripleZero.lean` |
| 4 | no escape to `∞`: `‖Npoly‖>‖Dpoly‖` for `\|k\|≥R(η)` | elementary polynomial bound; `R ≈ 1.26 (η=.05) → 34.9 (η=.99)` |
| — | **machinery**: parametric Rouché / Hurwitz zero-count stability | ❌ **Mathlib has NEITHER Rouché NOR Hurwitz** (checked) ⇒ this is the axiom to introduce |

**Input 3, derived and verified this pass.**  Expanding `e^{−ikσ}` and using the *already-present*
lemma `baxterP0P1P2_sum_zero` (`P0+P1σ+P2σ²=0`), the `k⁰`, `k¹` **and `k²`** coefficients of
`G_baxter` all cancel identically, and the cubic coefficient is

  `c₃ = i·(1 + P1σ²/2 + 2P2σ³/3) = i·(1+2η)/(1−η)²`   —  **σ- and ρ-free, manifestly ≠ 0 on `η ∈ (0,1)`.**

(The `k²` cancellation is precisely *why* `baxterP0P1P2_sum_zero` is in the file.)  Verified to
`≲1e-6` for `η ∈ [0.01,0.99] × σ ∈ {0.7,1.0,2.3}`.  So `G_baxter` has an **exact** order-3 zero at
the origin for every physical parameter — no zero can split off into the LHP there, and the triple
zero is exactly what must be deflated before any contour count.

**Disposition.**  Route C is a genuine, complete proof strategy, but its *machinery* input is a
famous theorem Mathlib lacks.  Per the triage heuristic this is a **gap** argument, not an **effort**
argument, so the correct next move is the abstraction the user authorised: introduce
**parametric Rouché / Hurwitz zero-count stability** as a pure-math axiom in `Analysis/` and derive
`baxter_no_open_lhp_pole_core` from it plus inputs 1–4, converting the last domain-referencing axiom
into a theorem.  ⚠ **Do not add the abstract axiom until the reduction is written** — an unconsumed
axiom makes the ledger strictly worse, and a version whose hypotheses cannot be discharged (e.g. the
"Krein canonical factorization with winding-number-0 hypothesis" formulation, considered and
rejected here) would be a *fake* retirement of exactly the vacuous kind the 2026-07-17 audit flagged.


#### Input 3 FORMALIZED (2026-07-21) — `HardSphere/BaxterOriginTripleZero.lean`, axiom-clean

`#print axioms` = `[propext, Classical.choice, Quot.sound]` for all four results; full build green
(8689 jobs), 0 `sorry`.  Ledger unchanged at 8 (this adds theorems, no axiom).

**The formalization is far cheaper than the derivation suggested, because the cube never has to be
re-derived.**  The tempting route expands `exp(-ikσ)` to third order and then fights an `O(k³)` Peano
remainder — which in Lean means either a `tsum` reindex of the exponential series or three nested
removable-singularity arguments, both substantial.  Unnecessary: the *already-present* bridge
`baxter_cube_mul_F_eq_G` factors the cube out **exactly**, and `(-i)³ = i`, giving

  `G_baxter k / k³ = i·(1 - Qhat_complex k)`  for `k ≠ 0`   (`G_baxter_div_cube`)

as an **identity, not a limit**.  The leading coefficient is then just `i·(1 - Qhat_complex 0)`, and
at `k=0` the exponential in `Qhat_complex` is `1`, so it is a plain polynomial integral.  The whole
transcendental difficulty evaporates.  Shipped:

| theorem | statement |
|---|---|
| `integral_q0_poly_zero_sigma` | `∫₀^σ q0_poly = -ρq'σ²/2 + ρq''σ³/6` (FTC on the inner quadratic) |
| `Qhat_complex_zero` | `Qhat_complex 0` = that integral, cast to `ℂ` |
| `one_sub_Qhat_complex_zero` | **`1 - Qhat_complex 0 = (1+2η)/(1−η)²`** — `σ`- and `ρ`-free |
| `one_sub_Qhat_complex_zero_ne_zero` | `≠ 0` on `η ∈ (0,1)` ⇒ order is **exactly** 3, uniformly |
| `G_baxter_eq_I_mul_cube`, `G_baxter_div_cube` | the exact cube factorization |
| `G_baxter_div_cube_tendsto_origin` | `G_baxter k / k³ → i(1+2η)/(1−η)²` as `k→0` |

**Cross-check that fell out**: the closed form says `Qhat_complex 0 = -η(4−η)/(1−η)²`, so
`‖Qhat_complex 0‖ = M(η)`, the dilute-route kernel mass `∫₀^σ|q0_poly|` — as it must be, `q0_poly`
being single-signed on the core.  Two independently-computed quantities agreeing is a real check on
both.  It also explains *why* input 3 alone cannot finish the job: `M(η) < 1` only up to
`η* = (3−√7)/2`, which is precisely the dilute wall.

**Lean pitfall (new instance of a known one).** `HasDerivAt.pow` yields the *pointwise function*
power `(fun x => x - σ) ^ 2`, which neither matches `fun x => (x - σ) ^ 2` definitionally nor carries
the same module instance (`Real.normedCommRing.toAddCommGroup` vs `Real.instAddCommGroup`), so
`simpa using hbase.pow 2` fails with an instance mismatch.  Fix: build powers by `.mul` with the
target type **pinned by an explicit `have` annotation** — the same remedy already recorded for
`.const_mul`/`.div`/`.mul` in `feedback_lean4_patterns`.

**Remaining for MA.14**: input 4 (elementary escape bound) + the **machinery** — parametric
Rouché / Hurwitz zero-count stability, absent from Mathlib, to be added as the pure-math
`Analysis/` axiom *together with* the reduction (never before it).

### POLE.11-general / `MA.14` — **RETIRED 2026-07-21** (axiom → theorem via `η`-homotopy)

`baxter_no_open_lhp_pole_core` is now a **theorem** (`BaxterHermiteBiehler.lean`), proved from the
homotopy route.  Full build green (8691 jobs), 0 `sorry`.  `#print axioms baxter_no_open_lhp_pole_core`
= `{propext, Classical.choice, Quot.sound, zeroFree_lowerHalfPlane_of_homotopy}` — the domain axiom is
gone, replaced by ONE **pure-analysis, fully general** axiom (`Analysis/ZeroCountHomotopy.lean`,
`FMSA.Analysis` namespace).  **`HardSphere/` now contains no domain-referencing axiom at all.**

**What landed (all four inputs + the reduction), files:**
* `BaxterOriginTripleZero.lean` — input 3 (origin), axiom-clean (prior pass).
* `BaxterPoles.lean` — input 4: `Dpoly_norm_lt_Npoly_norm_of_coeff_bound` (norm-domination from
  coefficient bounds) → `Dpoly_norm_lt_Npoly_norm_of_large` (∃R, single point) →
  `exists_uniform_escape_radius` (uniform R over a compact `η`-interval, via continuity of the
  coefficient magnitudes + `IsCompact.exists_isMaxOn`).  `G_baxter_ne_zero_of_norm_dominant` moved
  here from `BaxterHermiteBiehler` (elementary, belongs with `Npoly`/`Dpoly`).
* `Analysis/ZeroCountHomotopy.lean` — the abstract axiom `zeroFree_lowerHalfPlane_of_homotopy`:
  jointly-continuous family of entire functions `H t`, zeros in the closed LHP bounded by `R`, never
  vanishing on the real axis, zero-free at `t=a` ⇒ zero-free at `t=b`.  A faithful statement of
  homotopy invariance of the zero count (argument principle / Hurwitz), which Mathlib lacks.
* `BaxterLowerHalfPlane.lean` — the reduction `Qhat_complex_ne_one_of_im_neg`.  Key device: work on
  the **entire** `H = 1−Q̂`, not `G_baxter`, so the origin (input 3 ⇒ `H(0)≠0`) is a regular boundary
  point, no contour indentation.  Joint continuity is trivialised by the factorization
  `Q̂ = (ρq')·qKernel1 + (ρq'')·qKernel2` (`φ1,φ2` are `η`-free on `[0,σ]`).  Dischargers:
  `hbase` = dilute base case at `η*/2`; `hreal` = input 2 (`k⁶`, `G_baxter_ne_zero_of_real`) off the
  origin + input 3 at the origin; `hbound` = uniform escape + norm-domination; `hcont` = the
  factorization; `hholo` = `Qhat_complex_entire`.  For `η < η* = (3−√7)/2` the dilute result is used
  directly (no homotopy).

**Bonus:** the real-axis case is discharged by the *elementary* `k⁶` identity, so
`G_baxter_ne_zero_of_im_nonpos` no longer routes through the no-spinodal physics axiom either — its
`#print axioms` is now `{std, zeroFree_lowerHalfPlane_of_homotopy}`.

**Net axiom ledger: 8 → 8, but the character improved decisively** — the last *domain-referencing*
axiom became a general pure-math one.  All 7 math axioms now live in `Analysis/`; the sole physics
axiom `pyhs_mixture_no_spinodal` is the multi-component one (no consumer on the single-component
track).  This is the "correct abstraction to a pure-math axiom" disposition, exactly as scoped in the
triage pass above (Mathlib genuinely lacks Rouché / the parametric argument principle).

**Lean pitfalls recorded:** `Complex.norm_real` gives the *real norm* `‖r‖`, needs `Real.norm_eq_abs`
to reach `|r|`; `HasDerivAt.pow`/`ContinuousOn` fold-direction issues with `set` (kept coefficients
raw); a `private def` for the wall `η*` broke defeq unification with the dilute lemma's literal
`(3−√7)/2` — inlined the literal and carried `√7<3` / `1<√7` as `nlinarith` facts instead.
