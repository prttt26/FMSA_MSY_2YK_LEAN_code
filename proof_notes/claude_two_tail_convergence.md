# Convergence set of a mixed-sign two-Yukawa tail, one component (numerics)

Claude, 2026-10-26; updated 2026-10-27 (full mechanism classification, multi-scale `R_c`).
This note **supersedes** foundation `proof_notes/proof_notes_msa_exact.md` §8e (commit 41796bb).
That section's numbers came from a build with defects 1–4 under *Build history*. Defect 5 affects them
too. On the free-`z1` grid it moved `f*` by at most 6e-4. The slice brackets were rechecked
and stand (*Results*). Its z1 = 1.8 and LJ tables survive almost unchanged. Its mechanism statements
do not. The foundation is frozen at 1.0.17, so §8e is not edited there; the correction is
carried over at the single merge-back.

Everything here is float64 evidence, not proof. The certified statements are Codex's and are
cited as such.

## Question and reduction

Future plan (b) asks which tails make the coupling series converge at the physical coupling for
every stable state at every density `0 < η < η_max`. The stable domain is the initial interval
only (user decision, handoff 003). Re-entrant stable states after a closed instability interval
are a separate follow-up (see *Open*).

On that domain, convergence is equivalent to `R_c ≥ τ_inst`. This is
`StableIntervalRadius` (foundation 1.0.12, Codex). Here:

* `τ_inst` is the first loss of canonicity along the PY-seeded real branch: a `det F(0)` zero
  (`k = 0`) or a winding change of `det F(ik)` (`k ≠ 0`);
* `R_c` is the modulus of the nearest physical-sheet singularity of the branch germ.

Equality is admissible. `τ_inst = ∞` needs an entire germ, so a density with no instability at
any `τ` fails: the stable range is not capped (user decision). §8c gives `τ_inst ≤ τ_f`, the
weak inequality; strictness is open there. So a binding real fold always passes, and a failure
needs one of two things:

* a complex pair with `|τ*| < τ_inst`; or
* `τ_inst > R_c`, including `τ_inst = ∞`.

**Family.** `K = (1, w)` at rates `z = (z1, z2)`, `z2 > z1`: a long-range attraction and a
short-range repulsion, the shape of an LJ fit. The amplitude is the cancelled fraction of the
tail integral, `f = w/w0`, with `w0 = −(1/z1 + 1/z1²)/(1/z2 + 1/z2²)`.

## Method

Scripts are in `scripts/two_tail/` (see its README); results are in `results/two_tail/`. Every
log and JSON header carries the command line.

* `two_tail_margin.py`, for one state:
  1. Compute `R_c` first. Padé candidates are taken at a scale grown or shrunk geometrically to
     the root-test estimate. Fold refinement uses a Hadamard-relative residual. The sheet test
     approaches along `√d`, with a retry for near-real complex folds.
  2. Trace the real branch (`msa_exact_mix.trace_coupling_mix`) only to
     `cap = min(lam_max, 1.02 R_c)`.
  3. Report a status:
     * `crossing_bracket`: a crossing was found, and the margin is `R_c/τ_inst − 1`;
     * `no_crossing_up_to_cap`: then `τ_inst > 1.02 R_c`, a failure. This is Codex's
       `nonconvergence_witness_before`. The reported margin is the upper bound `−0.0196`;
     * `trace_stalled` and `R_unresolved` mean unknown. Unknown is never read as pass or fail.

  No crossing beyond `R_c` is ever needed. "No crossing up to the cap" is a statement about this
  detector, which samples the traced branch. An exact tangential touch (`F0 = 0` with
  `F0' = 0`) counts as a finite first loss (Codex, 004), but the sign-change detector misses
  it. It has measure zero in `f`.

  4. Since 2026-10-27: when a real fold binds with margin in `[0, 1e-3)`, `R_c` is the smallest
     `|τ*|` over 8 Padé scales (0.6 … 1.3 × the series scale). See build history item 5.
* `two_tail_scan.py`, per cell `(z1, z2, η)`: evaluates a 14-point `f` grid
  (0.01 … 0.95), counts sign changes (so monotonicity is measured, not assumed), and bisects the
  first change to `Δf < 2e-3`. `lam_max = 160`, scaled up by `I(1.8)/I(z1)` for `z1 > 1.8`,
  where `I(z) = 1/z + 1/z²`.
* `two_tail_m2_locate.py`: Newton on Codex's 10-equation zero-mode touch system (004 §3–4),
  transcribed independently:

      P(u) − τ b(w) = 0,   J(u) v − b(w) = 0,   F0(u) = 0,   g(u)·v = 0,

  with unknowns `u = (D1, D2, G1, G2)`, `τ`, `w` and `v`. It returns `f_M2`, `τ_touch`, the
  curvature `F0''` and the transversality `m_f`. At Codex's control it reproduces
  `f = 0.5044323206321593`, `τ = 5.613571646217654`, `F0'' = 0.99087` and `m_f = 202.334`. All
  four lie inside the certified boxes of 009/011.
* `two_tail_classify.py`, per free-`z1` cell: 9 points across the scan bracket. Each point is
  typed `R` (pass, real fold binds), `C+` (pass, complex pair binds), `F1` (fail, crossing at
  `τ_inst > R_c`), `Fc` (fail, no crossing up to the cap but `det F(0) < 0` before `1.3 R_c`),
  `Finf` (fail, `det F(0) > 0` up to `1.3 R_c`) or `U` (unknown). The pair (last pass `p`, first
  fail `q`) gives the mechanism: `(R, F1)` with the fold alive at `q` is M1, `(C+, F1)` is M3,
  and `(C+, Finf)` is M2 or M3 by the touch locator (`τ_touch` against `R_c` interpolated across
  `[p, q]`). A `C+` pass whose fold satisfies `τ_f ≤ R_c` counts as `R`, because the finder
  returned the farther singularity. Any other pair is refined with 7 new points, up to 3
  levels. `--below D` searches `[lo − D, lo]`.
* `two_tail_recheck_real.py` redoes every pass of a classify run at 8 Padé scales and flags the
  points that have a singularity inside `τ_inst`. `two_tail_classify_correct.py` turns flagged
  passes into fails, recomputes the brackets and verdicts, and substitutes the `--below` runs.

## Results

Every cell in every table has exactly one sign change in `f`, and none has an unknown
evaluation. At fixed `(z1, z2, η)` the convergence set is therefore the interval `f < f*`.
The tables are printed by `scripts/two_tail/two_tail_tables.py`.

**Free `z1`.** Each entry is the midpoint of the classifier bracket `[p, q]` after the
multi-scale recheck (`results/two_tail/two_tail_classify_corrected_free_z1.*`), followed by
the mechanism. The bracket width is `2.0e-4`, or `2.4e-5` in refined cells and `2.5e-4` in the
five `--below` cells.

`η = 0.49` (columns are `z2/z1`):

| `z1` \ `z2/z1` | 1.4 | 2 | 3 | 5 | 8 |
|---|---|---|---|---|---|
| 0.6 | 0.8382 M1 | 0.6687 M1 | 0.5007 M1 | 0.3177 M1 | 0.1979 M1 |
| 1 | 0.7923 M1 | 0.5899 M1 | 0.3983 M1 | 0.2310 M1 | 0.1438 M1 |
| 1.8 | 0.7245 M1 | 0.4915 M1 | 0.3097 M1 | 0.1821 M1 | 0.1247 M1 |
| 3 | 0.6782 M1 | 0.4462 M1 | 0.2896 M1 | 0.1886 M1 | 0.1426 M1 |
| 4.5 | 0.6716 M1 | 0.4563 M1 | 0.3175 M1 | 0.2266 M2 | 0.1841 M2 |
| 7 | 0.7009 M1 | 0.5115 M3 | 0.3874 M2 | 0.3038 M2 | 0.2632 M2 |

`η = 0.47`:

| `z1` \ `z2/z1` | 1.4 | 2 | 3 | 5 | 8 |
|---|---|---|---|---|---|
| 0.6 | 0.8397 M1 | 0.6769 M1 | 0.5061 M1 | 0.3255 M1 | 0.2065 M1 |
| 1 | 0.7952 M1 | 0.5962 M1 | 0.4067 M1 | 0.2407 M1 | 0.1530 M1 |
| 1.8 | 0.7304 M1 | 0.5013 M1 | 0.3214 M1 | 0.1936 M1 | 0.1353 M1 |
| 3 | 0.6868 M1 | 0.4593 M1 | 0.3040 M1 | 0.2024 M1 | 0.1553 M3 |
| 4.5 | 0.6823 M1 | 0.4720 M1 | 0.3343 M1 | 0.2431 M2 | 0.1999 M2 |
| 7 | 0.7127 M3 | 0.5284 M2 | 0.4063 M2 | 0.3235 M2 | 0.2827 M2 |

The eight extra `z1 = 1.8` cells of the free scan (`z2` = 2.5, 3, 4, 6, 8, 12, 16, 24) are all
M1 at both densities.

Relative to the previous build's single-scale scan brackets, the correction moves `f*` down in
25 of the 76 cells, all of them M1, by 2e-5 to 5.9e-4 (largest at `z = (0.6, 0.84)`). In five
cells the scan's lower end was itself a false pass, so `f*` lies just below the scan bracket.
The previous build's 3-decimal scan midpoints differ from these by at most 0.001 in all 76 cells:
44 cells agree, 20 were high and 12 low. Most of that difference comes from the finer bracket,
not from the correction.

**Slices** (scan brackets, width `1.6e-3`). These were rechecked on 2026-10-28
(`two_tail_recheck_lo.py`, `results/two_tail/two_tail_recheck_lo_slices.*`).

The defect only creates false passes, because a smaller `R_c` can only turn a pass into a fail.
So a scan bracket `[lo, hi]` stands iff its pass end `lo` is a true pass. The pass ends of all
79 slice cells (72 at `z1 = 1.8`, 7 LJ) were redone at 8 Padé scales:
* none is flagged;
* no scale found any singularity nearer than the original `R_c`;
* the smallest margin after the recheck is `3e-6`.

The brackets and the midpoints below are therefore unchanged.

**`z1 = 1.8` slice:**

| `z2` \ `η` | 0.02 | 0.05 | 0.1 | 0.2 | 0.3 | 0.4 | 0.45 | 0.47 | 0.49 |
|---|---|---|---|---|---|---|---|---|---|
| 2.5 | 0.907 | 0.893 | 0.870 | 0.829 | 0.791 | 0.757 | 0.741 | 0.737 | 0.730 |
| 3 | 0.859 | 0.838 | 0.805 | 0.743 | 0.688 | 0.640 | 0.618 | 0.610 | 0.602 |
| 4 | 0.791 | 0.762 | 0.713 | 0.627 | 0.551 | 0.487 | 0.457 | 0.446 | 0.437 |
| 6 | 0.715 | 0.674 | 0.612 | 0.502 | 0.410 | 0.332 | 0.299 | 0.287 | 0.276 |
| 8 | 0.674 | 0.629 | 0.557 | 0.438 | 0.340 | 0.262 | 0.227 | 0.216 | 0.204 |
| 12 | 0.635 | 0.584 | 0.504 | 0.374 | 0.274 | 0.198 | 0.165 | 0.154 | 0.143 |
| 16 | 0.615 | 0.560 | 0.479 | 0.345 | 0.245 | 0.168 | 0.138 | 0.127 | 0.116 |
| 24 | 0.595 | 0.538 | 0.454 | 0.316 | 0.215 | 0.141 | 0.113 | 0.102 | 0.093 |

**LJ two-Yukawa fit**, `z = (2.9637, 14.0167)`, `w = −1`, so `f = 0.169`:

| `η` | 0.1 | 0.2 | 0.3 | 0.4 | 0.45 | 0.47 | 0.49 |
|---|---|---|---|---|---|---|---|
| `f*` | 0.590 | 0.460 | 0.352 | 0.263 | 0.224 | 0.210 | 0.196 |

The fit is inside. At `η = 0.49` the bracket is `[0.1953, 0.1969]`, so the margin in `f` is
0.027, about 14 %.

### Observed patterns (not proved)

* **`f*` decreases in `η` in every cell measured.** The test covers the 8 `z2` values of the
  `z1 = 1.8` slice at 9 densities, the LJ cell at 7 densities, and 0.47 → 0.49 on all 38
  free-`z1` cells (corrected brackets). In every case the bracket at the higher density lies
  entirely below the one at the lower density. The condition is therefore set at the high-density
  end, `f < f*(z1, z2; η_max)`. It has not saturated: between 0.47 and 0.49 the gap between the
  brackets is still 0.0014 (`z = (0.6, 0.84)`, seven bracket widths) up to 0.020 (`z1 = 7`), so
  the condition depends explicitly on `η_max`.
* **`f*` decreases in `z2/z1`** in every row, at both densities, including the eight extra
  `z1 = 1.8` cells (corrected brackets). Per unit of cancelled tail integral, a
  shorter-range repulsion does more damage. As `z2 → z1` the tail becomes one attractive tail
  of amplitude `1 − f`, where 1.0.13 gives convergence, so `f* → 1` is expected in that limit.
  The ratio-1.4 column (0.67–0.84) is still far from it.
* **`f*` is not monotone in `z1`** at fixed `z2/z1`. At both densities the minimum over the six
  `z1` values lies at:
  * `z1 = 4.5` for ratio 1.4;
  * `z1 = 3` for ratios 2 and 3;
  * `z1 = 1.8` for ratios 5 and 8.

  For example, ratio 8 at `η = 0.49` gives 0.1979, 0.1438, 0.1247, 0.1426, 0.1841, 0.2632. The
  minimiser moves to smaller `z1` as the ratio grows.
* The previous build's z1 = 1.8 table moves by at most 0.003 in every cell, except
  `z2 = 2.5` at `η = 0.49` (0.726 → 0.730) and `η = 0.02` (0.896 → 0.907).

## Boundary mechanisms

At scan-bracket resolution (`Δf = 1.6e-3`), every `η = 0.49` cell looks the same. On the inner
side a real fold binds, with `τ_inst ≤ τ_f = R_c`; on the outer side a complex pair binds, with
`τ_inst > R_c`, either finite or beyond the cap. That alone does not say which inequality broke
first.

Twelve cells were resolved further, to `Δf ≈ 2e-4`, and two of them to `2e-5`
(`two_tail_m2_fine.py`; logs `two_tail_m2_fine.log`, `…_eta0.49_b.log`, `…_eta0.49_c.log`).
The fine step also records whether the fold still exists (`tau_f`) and whether the branch
still has a zero-mode crossing (`min det F(0)` up to `1.3 R_c`). Three mechanisms appear:

* **M1, complex overtake of a live fold.** A complex pair moves inside `τ_inst` while the real
  fold still exists: `|τ*_c| < τ_inst ≤ τ_f`. Before this, `τ_inst` and `τ_f` agree to a relative
  `3e-8` at `z1 ≤ 1` and to `3e-5` at `z1 = 1.8`. Numerically, the zero-mode crossing sits
  almost on the fold (cf. §8c, where strictness is open).
* **M2, zero-mode disappearance.** First the fold pair annihilates at a cusp, and a complex pair
  takes over with a *positive* margin. Then the minimum of `det F(0)` along `τ` rises through 0
  at `f_M2`, so `τ_inst` jumps to ∞. M2 sets the boundary only if `τ_touch < R_c(f_M2)`,
  because as `f → f_M2⁻`, `τ_inst → τ_touch`.
* **M3, continuous overtake of a complex pair.** The complex pair already binds with positive
  margin: the fold has vanished or lies beyond it. `τ_inst` then rises continuously through
  `|τ*_c|` before the zero mode disappears. This happens when `τ_touch > R_c`, or while the
  fold is still alive but farther than the pair.

The two evidence rows for (0.6, 3) and (1, 2) were corrected on 2026-10-27. The previous build's
inner points (f = 0.31797 and 0.59004) were false passes (build history item 5).

| cell `(z1, z2)` | mechanism | evidence (`η = 0.49`) |
|---|---|---|
| (0.6, 3) | M1 | f = 0.31758 → 0.31777: real, margin 3e-8 → complex `R = 3.1295 < τ_inst = 3.1362 = τ_f` |
| (1, 2) | M1 | f = 0.58984 → 0.59004: real, margin 2e-7 → complex `R = 11.168 < τ_inst = 11.177 = τ_f` |
| (1.8, 12) | M1 | f = 0.14238 → 0.14258: `R = 15.633 < τ_inst = 15.648 < τ_f = 15.649` |
| (3, 24) | M1 | f = 0.142637 → 0.142656: `R = 28.044 < τ_inst = 28.324 < τ_f = 28.416`. `f_M2 = 0.14270` lies beyond, with `τ_touch = 29.72 > R` |
| (4.5, 13.5) | M1 | f = 0.31738 → 0.31758: `R = 44.20 < τ_inst = 44.88 < τ_f = 45.03` |
| (7, 9.8) | M1 | f = 0.70078 → 0.70098: `R = 141.58 < τ_inst = 142.10 < τ_f = 143.26` |
| (7, 14) | M3 | The complex pair binds with positive margin while the fold is still there (`R = 83.79 < τ_f = 84.34`). The fold then vanishes. `τ_inst` rises 81.95 → 83.38 → 84.03 against `R ≈ 83.75`, and the margin changes sign between f = 0.511445 and 0.511465. `f_M2 = 0.511515` (`τ_touch = 87.67`) comes after |
| (7, 21) | M2 | cusp between f = 0.3869 and 0.3871, then margin +0.092, +0.039. `f_M2 = 0.387339`, `τ_touch = 59.09 < R = 59.5` |
| (7, 35) | M2 | cusp between f = 0.3033 and 0.3035, then +0.11, +0.08. `f_M2 = 0.303902`, `τ_touch = 45.19 < R = 45.7` |
| (7, 56) | M2 | cusp between f = 0.2626 and 0.2628, then +0.11 … +0.03. `f_M2 = 0.263210`, `τ_touch = 39.37 < R = 39.86` |
| (4.5, 22.5) | M2 | cusp between f = 0.2264 and 0.2266, then +0.020. `f_M2 = 0.226608`, `τ_touch = 39.29 < R = 39.36` |
| (4.5, 36) | M2 | cusp between f = 0.18379 and 0.18398, then +0.028. `f_M2 = 0.184001`, `τ_touch = 32.90 < R = 32.95` |

**All 76 free-`z1` cells**, at both densities, are classified by `two_tail_classify.py` after
the multi-scale correction. No cell is left with an unknown evaluation or an unresolved verdict.
The classifier reproduces all 12 hand-resolved cells above. The mechanisms are in the free-`z1`
tables under *Results*:

| `η` | M1 | M2 | M3 |
|---|---|---|---|
| 0.49 | 32 | 5: (4.5, 22.5), (4.5, 36), (7, 21), (7, 35), (7, 56) | 1: (7, 14) |
| 0.47 | 30 | 6: the five above and (7, 14) | 2: (3, 24), (7, 9.8) |

* M1 holds in every cell with `z1 ≤ 1.8` at both densities, including the eight extra
  `z1 = 1.8` cells.
* M2 needs both a large `z1` and a large ratio:
  * at `η = 0.49`, `z1 = 7` with `z2/z1 ≥ 3`, and `z1 = 4.5` with `z2/z1 ≥ 5`;
  * at `η = 0.47`, the `z1 = 7` group extends down to ratio 2.
* M3 sits on the edge of the M2 region, and the edge moves with `η`. Going 0.47 → 0.49:
  * (7, 14) changes from M2 to M3;
  * (7, 9.8) and (3, 24) change from M3 to M1.
* The two `η = 0.47` M3 cells differ:
  * (3, 24) is `(C+, Finf)` with `τ_touch = 25.79 > R_c = 25.54`;
  * (7, 9.8) is `(C+, F1)` with the fold still alive, but farther than the pair:
    `τ_inst = 133.90 < R = 134.38 < τ_f = 135.60`, then `τ_inst = 134.43 > R = 134.36` one
    step (2.4e-5) later.

Handoff 007, and my first chat summary of the M2 batch, reported "f_M2 inside the bracket" on
nine cells as M2. That test is necessary but not sufficient. Three of the nine (3/24, 4.5/13.5,
7/14) have `τ_touch > R_c`, and a fourth (7/9.8) has `f_M2` just outside the bracket.

**Candidates for certification**, i.e. M2 boundary points with the float margin
`R_c/τ_touch − 1`:

| `η` | `(z1, z2)` | `f_M2` | `τ_touch` | `F0''` | `m_f` | `R_c/τ_touch − 1` |
|---|---|---|---|---|---|---|
| 0.49 | (7, 56) | 0.263210 | 39.368 | 0.0577 | 983 | 1.24 % |
| 0.49 | (7, 35) | 0.303902 | 45.190 | 0.0457 | 1119 | 1.04 % |
| 0.49 | (7, 21) | 0.387339 | 59.088 | 0.0296 | 1464 | 0.74 % |
| 0.49 | (4.5, 22.5) | 0.226608 | 39.288 | 0.1261 | 3714 | 0.18 % |
| 0.49 | (4.5, 36) | 0.184001 | 32.896 | 0.1639 | 3117 | 0.24 % |
| 0.47 | (7, 56) | 0.282661 | 36.402 | 0.0572 | 768 | 1.49 % |
| 0.47 | (7, 35) | 0.323509 | 41.629 | 0.0454 | 873 | 1.26 % |
| 0.47 | (7, 21) | 0.406428 | 54.056 | 0.0296 | 1136 | 0.92 % |
| 0.47 | (7, 14) | 0.528401 | 79.510 | 0.0159 | 1715 | 0.43 % |
| 0.47 | (4.5, 22.5) | 0.242985 | 34.856 | 0.1300 | 2726 | 0.23 % |
| 0.47 | (4.5, 36) | 0.199851 | 29.396 | 0.1679 | 2299 | 0.30 % |

Newton residuals are `< 2e-10`, and `det J` is 22–34. In this table `R_c` is interpolated
across the classifier bracket `[p, q]`. The note's previous `η = 0.49` margins came from the
fine log and differ in the second digit. The full `(u, τ, w, v)` vectors are in two places:
`results/two_tail/m2_free_z1_eta0.49.json` for `η = 0.49`, and the classify JSON's `touch`
entries for both densities.

The `R_c` at the bracketing pass `p` of every M2 cell was rechecked at 8 Padé scales. The
smallest modulus found agrees with the single-scale value to a relative 2e-14, so the binding pair is
not scale-sensitive there. The `(4.5, ·)` margins are thin enough that a certified radius bound
may not separate them.

## Certified anchor (Codex)

At `η = 0.1`, `z = (1.8, 12)`, Codex certified the following chain at the zero-mode touch
`f ∈ [0.50443232062607, 0.50443232063825]`, `τ_touch ≈ 5.6135716`:

* 009: the 10-equation root, with an interval chain linking it to the PY seed;
* 011: it is the first zero of `F0` along the branch;
* 013: every real `k ≠ 0` is excluded up to `τ_touch`;
* 019: a complete complex-disk atlas proves `R ≥ 5.614 > τ_inst = τ_touch`.

So the series converges on the whole initial interval at this parameter. That parameter lies in
the scan bracket `[0.5031, 0.5047]` of the `(z2 = 12, η = 0.1)` cell, so it is an M2 boundary
point there. Not certified: that states beyond `f_M2` fail, the exact nearest singularity (float
`|τ*| = 5.63119`, a complex fold at `5.6240 ± 0.2851i`), and anything about other densities.

The single-tail theorem (1.0.13, `SingleTailSpinodal`, Codex) proves that for one attractive tail,
`det F(0)` vanishes strictly before the fold, so `τ_inst < R_c` unconditionally.
`scripts/two_tail/single_tail_sweep.py` checks this on 42 states,
`z ∈ {0.2, 0.6, 1.8, 4, 10, 25}` × `η ∈ {0.005 … 0.62}`, and finds no counterexample.

Since 131 (c3ae9a0) the whole single-attractive-tail question is a theorem, for one species with
`ρ > 0`. The data-constructed maximal canonical branch has `β < R = τ_f`, and the series converges
on the entire initial canonical interval (`maximal_whole_initial_interval_hasSum`). So for one
attractive tail, the answer to this note's question is yes at every stable state. The open case
is the mixed-sign two-tail family studied here.

## Build history (why §8e is superseded)

1. **Trace cap `lam_max = 40`.** At large `z1` this made outer bracket points "unknown" or
   fake-M2. Fixed by computing `R_c` first and tracing to `1.02 R_c`.
2. **Padé scale could only shrink**, so a singularity at `|τ| ≈ 84` was invisible from scale 5.
   Fixed by geometric growth toward the root-test estimate.
3. **Seed-determinant residual tolerance** rejected a true on-sheet complex fold
   (`z = (0.6, 0.84)`, `f = 0.9`: `τ* = −7.321 ± 0.372i`). Fixed with the Hadamard-relative test,
   `rP < 1e-9` and `rD = |det J|/∏‖J_col‖ < 1e-6`. The finite-difference Jacobian of
   `refine_fold` floors `rD` near `1e-8`.
4. **The `√d` sheet test rejected near-real complex folds** (Codex 015): it returned 7.643
   instead of 5.631, a false PASS. Fixed by retrying with steps down to `1e-6`. The retry
   requires monotone distances and the last two slopes within 0.05 of 1/2.

5. **One Padé candidate decided pass/fail where a real fold binds at `τ_inst`** (2026-10-27,
   found by the classifier). `nearest_singularity` follows a single candidate. In the M1 regime,
   `R_c = τ_f ≈ τ_inst`, and the complex pair that ends the convergence set approaches with
   nearly the same modulus. Whether the finder returns the pair or the fold then depends on the
   scale. At `z = (0.6, 0.84)`, `η = 0.49`, `f = 0.8386719`, scales 0.6, 0.7 and 0.9 returned the
   fold at 9.789, while 0.8 and 1.0 returned the pair at `−9.69 ± 0.57i` (`|τ*| = 9.71`). The
   classifier saw three sign changes there.
   * Recheck: all 313 `R` passes and all 27 `C+` passes of the 76-cell run were redone at
     8 scales (`two_tail_recheck_real.py`). 31 `R` passes were false, in 25 M1 cells; all had
     margin `< 1.4e-4`. No `C+` pass was false.
   * Fix: `margin` now takes the smallest `|τ*|` over the 8 scales whenever a real fold binds
     with margin `< 1e-3`.
   * Two `C+` passes, at (0.6, 1.8) and (3, 9) at `η = 0.49`, showed the reverse error: a
     complex pair farther than the fold was reported. This is harmless for pass/fail, because
     `τ_inst ≤ τ_f`. The classifier treats a `C+` pass with `τ_f ≤ R_c` as `R`.
   * The scan JSONs predate the fix. The slice brackets were rechecked at their pass ends and stand
     (*Results*).

Handoff 007's claim that "M2 sets the η = 0.49 boundary at z1 ≥ 3" came from defects 1–2. It
is replaced by the section above. §8e's "M1 sets the final boundary on both slices" holds for the
cells listed there as M1 and nowhere else.

## Caveat for §8c (Codex, 026; updated 046–198)

The tangent spectral OZ used in §8c's proof differentiates OZ along a kernel vector at a root that
may be singular. That needs an off-root identity first.

**Proved in `MSAConvergence`** (pieces of it):
* `ActualRDFTangent`, `PoleResidual` and `ResidualJets`.
* The finite-polynomial part, closed in 046 (f719230). For a vector killed by the actual
  fixed-`t` amplitude Jacobian at an actual BH root, both tangent `U`/`V` polynomials vanish
  identically (`actual_kernel_tangent_polynomials_zero`). Hypotheses: positive rates, nonzero
  `vacMix` and free volume, symmetric `K`. No canonical or invertibility hypothesis is used.
* The complex-frequency and source part, in 048 (b98d3c6). Two results, each along the same
  kernel vector:
  * the complex Wronskian derivatives vanish at nonzero imaginary frequency
    (`actual_kernel_complex_wronskian_fderiv_zero`);
  * the Fourier `Q`/`C` source-defect derivative vanishes at every real `k ≠ 0`
    (`actual_kernel_sourceDefect_fderiv_zero`). From this, the tangent of the spectral Baxter
    `C(k)` is symmetric (`actual_kernel_fourierC_fderiv_symmetric`). These Fourier statements
    also assume nonnegative diameters.
* The radial bridge, in 050 (fe7c940):
  * The genuine spectral-`C` derivative equals the radial Fourier transform of
    `JacobianExterior.orderedVariation`, for all species pairs and every real `k ≠ 0`
    (`actual_kernel_fourierC_fderiv_eq_ordered_radial`, positive diameters).
  * The actual primitive tangent is reciprocal and a.e. even, and the spectral-`C` tangent
    symmetry now includes `k = 0`.
  * The cosine/radial-sine identity is proved at arbitrary amplitudes before differentiating. It
    is never differentiated along an assumed root curve.
* The far-right-half-plane Laplace transcription, in 052 (57e33e4):
  * All actual causal `G` entries and their amplitude tangents have global exponential order,
    with a computed damping rate `γ = M + 1` rather than a small-kernel-budget premise
    (`actual_causal_entries_exponential_order`).
  * The integrated tangent renewal holds:
    `Laplace(δY)(I − Laplace(q)) = Laplace(δF) + Laplace(Y) Laplace(δq)`
    (`actual_tangent_laplace_renewal`).
  * The damping and block order were checked on paper in handoff 053.
  * Exponential order allows growth; it is not decay.
* The whole-family Laplace parameter derivative, in 055 (7ffe302). On a constructed far right
  half-plane, `Laplace(δY)` is the genuine amplitude Fréchet derivative of the Laplace family
  (`actual_causalVariation_laplace_fderiv`). One cutoff depending on `p`, not on the direction,
  serves every direction (`actual_causal_laplace_fderiv_all_directions`). The route goes
  through `Ŷ = F̂(I − q̂)⁻¹` on a common neighbourhood half-plane, not through the
  dominated-convergence route of 053.
* Transfer to the `r·h` moment, in 058 (a1fcde3), on the same far right half-plane:
  * `Laplace(r h)(s) = −1/s² + e^{−s R_ij} Laplace(Y_ij)(s)`, with genuine amplitude
    derivatives.
  * For additive contacts, `R_ij = (σ_i + σ_j)/2`, the tangent is `D · D_p Laplace(Y)[v] · D`
    with `D = diag(e^{−s σ_i/2})` (`additive_contact_phase_sandwich`; non-additive contacts are
    not covered).
  * Eliminating `Ŷ` gives the resolvent form
    `Laplace(r δh) = D ((δF̂ + F̂ T⁻¹ δq̂) T⁻¹) D`, `T = I − q̂`
    (`actual_hVariation_laplace_resolvent`). This was checked on paper from `Ŷ = F̂ T⁻¹`.
* Frequency-side canonical estimates, in 060 (d731051):
  * The kernel Laplace integral exists for `Re s > −min z_u`.
  * On `Re s ≥ −δ`, `Q(s) = q(0)/s + O(1/|s|²)`.
  * If `I − Q(s)` is a unit on the *whole* closed right half-plane, a zero-free strip
    `Re s ≥ −δ'` follows (`actual_canonical_kernel_strip_gap`). There `(I − Q)⁻¹` is
    continuous and uniformly bounded, with `|s|² |U − I − q(0)/s| ≤ B`
    (`actual_canonical_resolvent_control`).
  * These are frequency bounds, not a time-decay theorem. The later source application needs
    `vacMix ≠ 0`.
* Resolvent holomorphy and vertical-line `L¹`, in 062 (cc012fd), under the same full-canonicity
  premise:
  * `Q` and `U = (I − Q)⁻¹` are holomorphic on `Re s > −δ`. The origin is a removable point,
    so the integral value is kept there.
  * The remainder `W_b = U − I − q(0)/(s+b)`, with `b = δ + 1`, satisfies
    `(1+k²) Σ|W_b(a+ik)| ≤ C` with one `C` for every `a ≥ −δ`. Hence every vertical line is
    absolutely integrable (`actual_canonical_regularized_resolvent_analysis`).
* Contour shift and causal support, in 065 (cdd4789), under the same premise. These concern the
  unnormalised inversion integral `V_a(t)` of `W_b`:
  * `V_a(t)` does not depend on the line `a > −δ`, for every real `t`.
  * `|V_a(t)| ≤ π C e^{at}`.
  * `V_a(t)` vanishes for `t ≤ 0`.
  * `V_a(t)` is continuous in `t`, and `e^{−γt} V_a(t)` is in `L¹` for `γ > −δ/2`
    (`actual_canonical_contour_integrals`). On `a = −δ/2` the envelope is `π C e^{−δt/2}`.
* The causal resolvent field, in 067 (eac7c11), under the same premise
  (`actual_canonical_resolvent_field`). For each species pair it constructs a causal field
  `r_ij(t)` with these properties:
  * `r_ij` is continuous on `t ≥ 0`, with `r_ij(0) = q_ij(0)`;
  * it decays: `|r_ij(t)| ≤ B e^{−δt/2}`;
  * its transform is exact, `∫_0^∞ r_ij e^{−st} dt = ((I − Q(s))⁻¹ − I)_ij` for every
    `Re s > −δ/2`, which includes the Fourier axis.

  `r` is the Laplace-side resolvent kernel.
* Volterra identification of the kernel resolvent, in 070 (48a3811):
  * Causal Laplace uniqueness is proved for complex fields at any common real damping
    (`causal_laplace_injective`).
  * The real resolvent `r = q + r∗q` is built from the existing constructor
    `matBaxterPsiOuterFun`. With full canonicity it equals the 067 field on `t ≥ 0`
    (`actual_kernel_resolvent_canonical`).
  * So the actual real resolvent decays as `B e^{−δt/2}` and has the exact transform
    `(I − Q)⁻¹ − I` on `Re s > −δ/2`. The identification holds on `t ≥ 0` only.
* Decay of the actual RDF excess, in 072 (b5426d8):
  * `X = S + S∗r` on `t ≥ 0` for `nonlinearRDFExcess` and its cancelled source
    (`actual_excess_resolvent_formula`). This needs `vacMix ≠ 0` but no canonicity.
  * With full canonicity, `X` decays exponentially (`actual_excess_canonical_decay`, envelope
    rate `δ/4`) and is in `L¹` (`actual_excess_canonical_integrable`).
  * `X̂ = Ŝ (I − Q)⁻¹` holds as an honest integral on `Re s > −δ/2`, including the Fourier axis
    (`actual_excess_canonical_laplace`).
  * The affine background of `G` does not decay, and no decay is claimed for it.
* Decay of the excess amplitude tangent, in 074 (91f28ef), with full canonicity at the base point
  only:
  * The tangent satisfies the renewal `δX = δS + δX∗q + X∗δq` on `t ≥ 0`
    (`actual_excess_tangent_renewal`).
  * Hence `δX = A + A∗r` with `A = δS + X∗δq` (`actual_excess_tangent_resolvent_formula`).
  * `|δX(t)| ≤ D e^{−εt}` (`actual_excess_tangent_canonical_decay`), and `δX` is in `L¹`.
  * `(δX)^ = Â (I − Q)⁻¹` holds on `Re s ≥ 0` (`actual_excess_tangent_boundary_laplace`). This is
    the transform of the existing Fréchet tangent, not an interchange of differentiation with the
    boundary Laplace family.
* The global `h`-tangent `L²` field, in 076 (13d5175):
  * `|r δh(r)| ≤ B e^{−εr}`, so the odd radial lift is in `L¹ ∩ L²`.
  * `actualHL2Field` is exactly the `hQ` representative required by
    `RadialVariationL2.actual_kernel_DCF_ae_zero_of_L2_OZ`, so that premise is discharged.
  * `actual_kernel_DCF_ae_zero_of_radial_tangent_OZ` reduces DCF cancellation to one explicit
    remaining identity, the radial tangent OZ `δH = S δC S` a.e. at `k = 2πw`.
* The `h`-tangent response on the Fourier boundary, in 079 (a7993f2):
  * `δG = δX` holds, so `Laplace(r δh) = P (δX)^ P` with honest integrals on `Re s ≥ 0`, zero
    included, and without a limit.
  * The cancelled-source boundary identities and a kernel derivative interchange valid on the
    axis give `Laplace(r δh) = P ((δJ/2π + (J/2π) U δK) U) P` with `U = (I − K)⁻¹`, at every
    nonzero `Re s ≥ 0` (`actual_h_tangent_JL_boundary_response`).
  * The cancellation of `B̂ δq̂` in that formula was checked on paper.
  * At `s = 0` only the forcing/phase form is used.
* Tangent reciprocity, in 081 (94c96b3):
  * A first-order symplectic identity uses only base-point constraints and their zero
    derivatives. It gives a zero value and a zero Fréchet derivative of
    `nonlinearComplexReciprocityResidual` at every `s ≠ 0` on the imaginary axis, along a
    BH-Jacobian kernel vector at a symmetric-strength root. No canonicity is needed.
  * With `Y = J (I − q̂)⁻¹`, this yields `Yᵀ = Y` and `(δY)ᵀ = δY`.
  * Since `Laplace(r δh) = P δY P/2π` at every nonzero `Re s ≥ 0`, `Laplace(r δh)` is
    transpose-symmetric at every nonzero imaginary frequency
    (`actual_kernel_h_tangent_boundary_reciprocity`, full base-point canonicity).
  * The step from the source residual to `Yᵀ = Y` was checked on paper.
* **Radial tangent OZ and active-pair DCF cancellation**, in 083 (b6f212b):
  * The finite symbol `H = (E(−s) − E(s))/s` satisfies `(I − CR) H = C` and
    `(I − CR) δH = δC + δC R H` through an exact all-amplitude defect decomposition.
  * It is identified with the actual radial `h` tangent.
  * `actual_radial_tangent_OZ` proves `δH = S δC S` at every real `k ≠ 0`.
  * The premise `hF` is derived rather than assumed. `physical_fourier_factor_unit_of_kernel_unit`
    holds off-root at every real `k`, including 0, via `det(I − S Q S) = det(I − R Q)`, so no
    density is inverted.
  * Result: `actual_kernel_DCF_ae_zero` gives `orderedVariation_ij = 0` a.e. on `r > 0` for every
    pair with `ρ_i, ρ_j > 0`. It needs a BH root, a Jacobian-kernel direction and full
    base-point canonicity, with no `hQ`, tangent-OZ or `hF` premise.
  * The tangent-OZ differentiation and the determinant swap were checked on paper.
* **Weighted canonical kernel recovery**, in 087 (8ffda00), under the same premises:
  * Differentiating the all-amplitude factorisation `F(k) F(−k)ᵀ = I − S C S` gives
    `B(k) + B(−k)ᵀ = 0`, with `B = F⁻¹ δF`. This step was checked on paper.
  * The resulting causal response has supports that only touch at `edgeLo_ij`, with the source
    convention `edgeLo = (σ_j − σ_i)/2` (handoffs 085/086, guarded at `σ = (1, 1/2)`).
  * Reflection and Fourier inversion therefore force it to vanish.
  * Result: `δq(t) · diag(ρ) = 0` for `t ≥ 0` (`actual_weighted_kernel_variation_zero`). The
    kernel tangent vanishes in every positive-density column.
  * Not concluded: tracer rows, which carry the row-density weight, and zero-density columns.
* **Positive-density canonical BH regularity**, in 091 (53948b8):
  * The weighted results allow `ρ_i ≥ 0`: `δD_t R = 0` (all rows), `R δJ R = 0`, and
    `R δG R = 0`.
  * The `G` step differentiates the all-amplitude second residual `(2πG)(I − RQ) − J`. It then
    cancels `I − QR` by a determinant swap; this step was checked on paper.
  * If every `ρ_i > 0`, the amplitude Jacobian is invertible:
    `actual_residual_partial_isInvertible_of_positive_densities`. Its premises are an actual BH
    root at any coupling and full base-point canonicity, with no root curve, supplied inverse or
    kernel budget.
  * The conclusion is exactly the partial-derivative premise of the frozen local-branch
    theorem. So in the abstract stable-interval criterion, that premise can be replaced by
    canonicity when all densities are positive. The branch, interval and radius premises are not
    discharged.
* **General nonnegative densities**, in 096 (9875a70): the premise is relaxed to `ρ_i ≥ 0`,
  including zero-density tracer rows and columns
  (`actual_residual_partial_isInvertible`). The steps:
  * the DCF tangent is zero for all pairs, with left and right weighted zeros obtained
    separately (handoff 093), and then `δh = 0`;
  * `δG = 0` from the second BH residual;
  * column locality of the root transform at fixed `G` gives `δQ R = 0`, and then full
    `δD_t = 0`.
* **Canonical branch, first loss on the axis, path bridge**, in 102 (64fbf9e):
  * Full canonicity is open in amplitudes (`canonical_amplitudes_isOpen`).
  * Canonical roots carry local two-sided analytic canonical germs.
  * The series criterion `exists_canonical_series_extension`:
    for a continuous canonical root branch on `[0, bound)`, the series sums to the branch iff
    `bound ≤ amplitudeRadius` of the true extension germ. This is the Lean form of this note's
    `R_c ≥ τ_inst`.
  * First loss (handoff 099, proved by a maximum-modulus argument rather than Hurwitz,
    `actual_first_loss_exists_real_frequency`): a continuous branch canonical on `[0, t*)`, with
    `t* > 0`, and not canonical at `t*` has `det F(k) = 0` at some real `k`, possibly 0.
  * With a transverse fold on the same branch, `t* ≤ τ_f`
    (`actual_first_loss_zero_and_le_transverse_fold`). This is §8c's weak inequality, with
    the instability on the Fourier axis.
  * Path bridge (`canonical_path_of_physical_factor_units`): one canonical seed plus
    `det F(k) ≠ 0` at every real `k` along a connected path gives canonicity along the whole
    path. This is the logic behind this note's `τ_inst` detector. The detector samples a finite
    `k` grid, so it does not discharge the quantified premise.
* **Initial HS canonicity near vacuum**, in 107 (843ce71):
  * An explicit coefficient budget `B < 1` implies full closed-right-half-plane canonicity of
    the HS seed (`hs_canonical_of_explicit_budget`). `B` is sufficient, not necessary.
  * There is an open density ball around vacuum, including tracer compositions, on which the
    seed is canonical and has a local analytic canonical branch for every finite `K`
    (`exists_low_density_analytic_canonical_hs_branch`).
  * The local Taylor sums converge on some `|τ| < b`. This `b` is local and is not the stable
    interval.
  * This does not certify `η = 0.47`–`0.49`.
* **One-component HS canonicity at every `η < 1`**, in 109 (c4b6be1):
  * The frozen pure-analysis axiom `zeroFree_lowerHalfPlane_of_homotopy` is now proved as a
    research theorem, by compact-tube openness and maximum-modulus closure.
  * The actual one-component kernel equals the scalar `q0_poly`, and its Laplace symbol is
    `Q̂(−is)`, including `s = 0`.
  * `actual_scalar_hs_canonical`: for one species and every `η < 1`, the HS seed is fully
    canonical on the closed right half-plane, for any positive finite tail rates. This covers
    every cell of this note at `η = 0.47`–`0.49`.
  * `exists_scalar_series_extension_of_physical_axis_units` removes the seed-canonicity premise
    from the full-interval criterion. What it still needs: a continuous root branch,
    `det F(k) ≠ 0` at every real `k` along it, and the complex-radius inequality.
* **Endpoint alternatives and an escape bound on the radius**, in 112 (040fe8a):
  * Boundary alternatives (`finite_prefix_boundary_alternatives`). A continuous canonical root
    prefix on `[0, b)`, with no endpoint value assumed, does one of three things:
    * it extends;
    * its amplitudes become arbitrarily large near `b`;
    * it has a finite cluster root at `b` with `det F(k) = 0` for some real `k`.
  * A canonical cluster forces the full one-sided limit, through IFT graph uniqueness and
    connected uniqueness.
  * Escape bounds the radius (`amplitude_radius_le_escape_endpoint`): if the amplitudes escape
    at `b`, the true same-seed germ has `R ≤ b`. This is an upper bound only. A bounded
    Fourier-zero cluster does not by itself obstruct the Taylor series.
  * Here `F` is the density-weighted Baxter factor `I − S Q̂ S`, not a Gram product (111).
* **The maximal initial canonical branch**, in 118 (ec29510):
  * The branch is constructed, not supplied: coherent prefixes are glued up to the supremum
    `β ∈ (0, ∞]` of admissible lengths.
  * Every admissible prefix is contained in it. Its endpoint, values, Taylor coefficients and
    radius are intrinsic.
  * `exists_scalar_hs_maximal_branch` constructs it from physical data alone for one species at
    every `η < 1`. This covers every state of this note.
  * At a finite `β`, either the amplitudes escape (then `R ≤ β`), or there is a bounded cluster
    root with `det F(k) = 0` at some real `k` (`maximal_finite_endpoint_boundary`).
  * The convergence criterion on the whole interval stays `β ≤ R`.
* **No finite amplitude escape for one species**, in 121 (eee0d7f), on the route of
  handoffs 115–117:
  * `canonical_roots_uniformly_bounded`: all one-species canonical roots are uniformly bounded
    over any bounded set of strengths. This holds for any tail signs and repeated rates, and at
    any `ρ ≥ 0`, vacuum included.
  * The proof normalises the frame `(1, q)`, uses zero-free closure of the limiting scalar factor,
    and uses the linear bound of the second source by the kernel.
  * Hence `no_finite_canonical_amplitude_escape`.
  * `exists_hs_maximal_branch_with_finite_axis_cluster`: from physical HS data alone at every
    `η < 1`, if the maximal branch has a finite endpoint `β`, then `β` carries a cluster root of
    the branch with `det F(k) = 0` at some real `k`.
  * This is a cluster root, not `p(β)` or a unique limit. `β = ∞` remains possible. A bounded
    Fourier-zero root can be a regular BH root, so the series may continue through the loss of
    canonicity, which is the convergent case `R_c ≥ τ_inst`.
  * The matrix case is open: normalised matrix factors can have identically singular limits.
* **General-mixture HS canonicity**, in 125 (4c15f86):
  * The HS seed is fully canonical for any finite `N`, `ρ ≥ 0` (tracers included), unequal
    diameters and `η < 1` (`seed_factor_closed_right_isUnit`, `actual_mixture_hs_canonical`).
  * The proof is a clopen argument on the convex density region:
    * open, by inverse perturbation;
    * closed, by zero-free closure in `Re s > 0` together with the collective axis identity
      (handoffs 122/123) and the static origin.
  * `exists_mixture_hs_maximal_branch` constructs the maximal initial branch from mixture data
    alone.
  * `MixtureHSNoSpinodal.pyhs_mixture_no_spinodal` proves the exact statement of the frozen
    physics axiom. The frozen declaration is unchanged.
  * The clopen logic and the legacy-matrix dictionary were checked independently: by algebra,
    and in floats against the literal `Q0_mat_c_phys` (handoffs 123, 126).
* **Regular endpoints, and the single attractive tail**, in 131 (c3ae9a0):
  * `regular_cluster_gives_extension`: one regular, i.e. Jacobian-invertible, cluster at a finite
    endpoint gives the unique full left limit and an analytic *root* extension. The canonical
    domain is unchanged. Without a full limit, every cluster is singular. The singular case is
    not identified with a nondegenerate fold, nor with `τ_inst = τ_f` (handoffs 128/129).
  * One species with one attractive tail and `ρ > 0`:
    * `0 < β < R = τ_f`, proved by matching the maximal branch with the frozen explicit branch and
      its zero-mode point `t < R`;
    * the series converges on the whole initial canonical interval
      (`maximal_whole_initial_interval_hasSum`);
    * the endpoint limit is the explicit root, with a physical Fourier zero;
    * the HS coefficients sum to the explicit root for every `0 ≤ τ < τ_f`.
  * The first instability is not identified as `k = 0`.
* **Isolated endpoints and fiber certificates**, in 137 (0aad956) and 143 (768caf6):
  * A cluster that is isolated among the endpoint roots in canonical closure has a full left
    limit, even when it is singular.
  * The BH residual is an exact multivariate polynomial. Checkable `CoordinateFiberCertificate`s
    give a finite relevant fiber, and hence the full limit.
  * For one species, the substitution `X = Dt·G` makes the system quadratic.
  * A first concrete certificate family exists, at zero density. The positive-density
    certificates are open.
* **External interval certificates at three endpoint controls** (Claude, 2026-10-28; handoffs
  138–142; these are not Lean proofs). For one species with two tails, the Jacobian of the literal
  Lean residual was computed by AD in 192-bit intervals.
  * M2 (`η = 0.1`, z = (1.8, 12)): on Codex's certified root box, `‖I − CJ‖ ≤ 3.5e-8`, replayed
    independently in Arb (139).
  * M1 (0.6/0.84, `η = 0.49`) and M3 (7/14, `η = 0.49`): Krawczyk root boxes with a uniformly
    invertible Jacobian.
  * At both M1 and M3, the float bisection brackets of the `det F(0)` sign change turned out to
    be wrong. The rigorous brackets are relative `1e-11` (M1) and `1e-13` (M3).
  * At M3 one parametric box covers the bracket, so a single continuous branch changes sign
    there. Its analytic enclosures were then recomputed independently (handoff 147): SymPy
    transcription of the Lean polynomials, exact derivatives, centered Taylor forms in Arb. All
    six stored M3 witnesses hold with `‖I − CJ‖ < 0.020943` (the AD bound was 0.355). Tiny Arb
    Krawczyk boxes at both bracket ends lie inside the parametric box, with `A` signs `+` / `−`.
    Codex replayed it at 256 and 384 bits and checked it with its own Fraction checker (148,
    3d1f754). Codex's `--symbolic` mode also matches the transcription exactly against its
    independent model. This gives at least one zero of `det F(0)` on the branch inside the
    bracket; uniqueness of that zero is not proved.
  * At M1, τ is a bad parameter: near the fold the root sensitivity is of order `1e6`. The same
    statement was certified instead by parametrising the branch by `Dt_1`, with `τ` as an
    unknown (handoff 144): 4 mean-value Krawczyk slabs, chained, containing both endpoint roots.
    Codex then proved, on the same boxes, `1.37e-4 < dτ/dDt_1 < 1.76e-4` (146, ae73a68). So `τ` is
    strictly increasing along the arc, and the zero of `det F(0)` lies in the narrow rigorous
    bracket on that one branch.
  * **M1 and M3 are now on the PY-seeded branch (handoff 157).** This uses chained
    parametrised Krawczyk slabs in Arb (centered Taylor forms, mean-value form in the parameter,
    radius-weighted contraction `q < 1`) from the exact HS seed (`Dt = 0`, closed-form `G`) at
    `τ = 0` to `τ_hi`.
    * M3 uses 664 `τ` slabs, max `q ≤ 0.50`.
    * M1 uses 238 `τ` slabs up to `τ = 9.5`, then 1325 slabs in `p = Dt_1`. Near the fold `τ` is a
      poor parameter. Every `p` slab carries `dτ/dp > 0` (lower bounds `≥ 4e-7`). This makes the
      curve a graph over `τ` and `J_u` invertible on it, since the kernel of `[J_u | R_τ]` is the
      tangent.
    * Link boxes join adjacent slabs. `A > 0` holds on every slab up to `τ_lo` (for M1, up to
      `p_star`, which is at least the `p` range of the `τ_lo` box). Tiny boxes at the exact
      `τ_lo` and `τ_hi` give `A` signs `+` / `−`.
    * So the **first** zero of `det F(0)` along the PY-seeded branch lies in the rigorous bracket,
      for both controls.
    * Not covered: first loss (complex `s` with `Re s ≥ 0`), uniqueness of the zero, Taylor radii.
    * This supersedes, for this purpose, the M1 fold-branch (144) and M3 parametric-box
      statements.
  * **First loss of full canonicity for M1 and M3 lies in the bracket (handoff 167).**
    * Lean interface: `CanonicalFirstLoss.canonical_path_of_physical_factor_units`. A continuous
      path from a canonical seed stays canonical if the physical Fourier factor is a unit at every
      point and every real `k`.
    * Seed: `ScalarCanonicalSeed.actual_scalar_hs_canonical` makes `(0, G)` canonical for every `G`.
    * The factor: for `N = 1`, `F(u, k) = 1 − ρ∫q(r)e^{−ikr}dr`, a polynomial in `u` with explicit
      complex coefficients. `F(−k) = conj F(k)`. `F(u, 0) = A(u)/2π` at every `u`
      (`scalar_fourierFactor_zero`), checked here symbolically. The closed form also matches
      direct quadrature of the Lean `q`.
    * External Arb certificate on every chain slab box covering `[0, τ_lo]`, for every `k ≥ 0`:
      * large `k`: a tail bound `ρ(|q(0)|/k + B2/k² + 2|A|/k³) < 1/2`;
      * finite `k`: a march with `m − d h − L2 h²/2 > 0`, where `L2 ≥ ρ∫r²|q|`;
      * groups of slabs are hulled, and split on failure.
    * Size: M3 has 481 records and 1.05e5 `k` steps. M1 has 75 records and 3.5e5 `k` steps.
      These are the 167 numbers. In the regeneration (173), each step instead uses
      `min(L2, H2(k))`, where `H2` is a decreasing bound on `|F''|` derived from exact
      second-derivative identities that are checked symbolically. This cuts the steps to 4.8e4
      (M3) and 1.03e4 (M1).
    * The stdlib checker and 9 negative controls behave as expected.
    * Conclusion: the PY-seeded branch is fully canonical on `[0, τ_lo]`. With the chain, the
      first loss of full canonicity lies in `(τ_lo, τ_hi)`, for both controls.
    * Not covered: which `k` carries the first loss, uniqueness of the zero, Taylor radii. A Lean
      instance would need the per-step `|F|` bounds proved in the kernel.
    * **Independently replayed by Codex (169, 3471b0c, `codex_first_loss_arb_audit.py`).**
      * All 456 510 steps and all hull bounds were replayed in Arb at 384 bits, using Codex's own
        coefficient rows and Fourier values; none of the two_tail code is imported.
      * Exact arithmetic re-checks the march and the coverage. 8 corruptions per control are
        rejected.
      * Pending documentation fix: the generator docstring writes
        `L2 >= rho int r^2 |q| = rho[...]`. The `=` should be `<=`, since the coefficient sum is a
        triangle upper bound. The computed budget is unaffected. The source is hash-pinned, so the
        fix waits for a coordinated regeneration.
    * **Lean, high-frequency part (171, 254e4cb, `ScalarFourierTail.lean`).** For one species of
      unit diameter, any finite positive rates and any `ρ ≥ 0`, the kernel proves the same tail bound
      `|F(k) − 1| ≤ ρ(|q0|/|k| + B2/|k|² + 2|A|/|k|³)`. It also proves that the explicit cutoff
      `K = 1 + 4ρ(|q0| + B2 + 2|A|)` gives matrix units for all `|k| ≥ K`.
      * Still external for an M1/M3 kernel instance (at 171): the finite-`k` bounds (`m`, `d`,
        `L2` with the sharp `h²/2`), the hull enclosures, and the PY chain.
    * **Lean, finite-frequency interfaces (175, 6438c5f).**
      * The modules are `QuadraticFrequencyStep`, `ScalarFourierMoments` and
        `ScalarFourierDerivatives`.
      * For all `k`, including 0, the kernel proves `F' = ρiΦ1` and `F'' = ρΦ2`, with
        `|F''| ≤ ρ∫|r²q|`.
      * Given point budgets `m ≤ |F(a)|` and `|F'(a)| ≤ d` with `m − dh − ρM2 h²/2 > 0`, the
        factor is a matrix unit on the whole closed step `[a, a + h]`.
      * Still open: the explicit coefficient bound on `M2`, `H2` as a Lean bound, the numerical
        point and hull enclosures, and the PY chain.
    * **Codex replay of the compressed files (175).** All 58 149 steps, the hull bounds and every
      `min(L2, H2)` step were recomputed at 384 bits. Ten corruption controls are rejected; the
      understated `|C1|` is caught by the analytic check. The receipt binds the current files.
      * The `C` terms of my `H2` and Codex 171's are not ordered globally. Their difference is
        `(4k + 2z² − 6z)/k⁴`. Each is valid; the replay verifies mine directly.
    * **Lean, absolute-moment budgets (176/178, 6b20168, `ScalarAbsoluteMoments.lean`).** For
      arbitrary signed finite tails, the kernel proves the explicit coefficient budgets (`S2`, `S3`),
      `|F''(k)| ≤ ρS2` at every `k` including 0, monotone hull budgets, and matrix units on a
      closed quadratic march step with the literal `Dt`/`G` amplitudes. The global `L2` bound is
      thereby closed in Lean. Full validation: 1136 axiom guards, 104 modules, exit 0.
      * Still open (at 178): `H2` as a Lean bound, the numerical point and hull instances, and the
        PY chain in the kernel.
    * **Lean, the compressed step (186/190, f86fb56, `ScalarFrequencyCurvature.lean`,
      `ActualFrequencyCurvature.lean`, 1220 guards, 111 modules).**
      * `actual_interval_units_of_stepBudget` covers exactly the inequality my rational checker tests
        per step. The hypotheses are:
        * upper bounds on `|qp|, |A|, |W|, |C|` and `ρ`;
        * `L ≥ stepBudget(k0)`, which is `S2` at 0 and `min(S2, H2(k0))` otherwise;
        * `m ≤ |F(k0)|` and `|F'(k0)| ≤ d`;
        * `m − dh − Lh²/2 > 0`.

        The conclusion: the original physical factor is a matrix unit on all of `[k0, k0 + h]`.
      * `H2` is exactly my 173 formula, including my `C` term. The true derivatives are recovered
        through the closed symbol and derivative uniqueness.
      * Still open: the Arb-side inputs as Lean facts (per-step `m` and `d`, the hull coefficient
        bounds), and the PY chain.
  * **M3: a real, fully canonical state where the coupling series diverges (Codex 177/178,
    6b20168 and 97aa792, `proof_notes/codex_m3_monodromy_radius.md`).** EXTERNAL Arb interval
    certificate, not a Lean proof.
    * Method: monodromy. From the HS seed, a parametrised complex Krawczyk chain (4210 slabs,
      384-bit generator, independent 512-bit replay, 10 corruption controls) follows the root
      along a polygon in the complex `τ` plane that stays in `|τ| < 84`: a straight prefix, then
      one loop around a small rectangle near `τ ≈ −20.8 + 81.0i`. The root box after the loop is
      disjoint from the one before it. If the amplitude series converged on `|τ| < 84`, its sum
      would be a single-valued holomorphic root there and the loop would return to the same root.
      Hence the common Taylor radius satisfies `R ≤ 84`.
    * With the first-loss certificate above (canonical on `[0, τ_lo]`):
      `R ≤ 84 < 337/4 < τ_lo = 231952160772086804783922789/2748779069440000000000000 ≈ 84.38370451479815`.
      At `τ = 337/4` the original PY-seeded branch is real and fully canonical, and the vector
      amplitude series does not converge there (at least one component).
    * Endpoint: 177 cited the nearby historical diagnostic `taus.tau_lo` (`≈ 84.38370451480296`);
      178 corrects this to `rigorous_bracket.lo.tau`, the endpoint the 657 required slabs
      actually cover. I re-checked from the chain file that the 657 required M3 slabs end exactly
      there. The difference (≈ 4.8e-12) does not affect the comparison.
    * Unit final coupling: with fixed strengths `K' = (337/4, −141203/1536)` and `τ = (337/4)λ`, the
      radius in `λ` is `≤ 336/337 < 1`, while `λ = 1` lies inside the initial canonical interval.
      This is an exact reparametrisation.
    * The sheet change also changes `F(7)` (via `Dt1 F(7) = 2πτ/7`), so it is not a relabelling of
      an unchanged Baxter representation.
    * At `η = 0.49`: a density cap such as `η ≤ 0.8` does not by itself give convergence on the whole
      initial canonical interval.
    * Not claimed: the exact `R`, the nearest singularity, divergence of every component, the
      first-loss frequency, RDF positivity.
    * **Lean, the generic monodromy implication (180/182, 7f67489, `ComplexPathMonodromy.lean`).**
      * `radius_le_of_changed_lift`: take a smooth residual `R`, analytic on `ball(0, r) × E`, and
        a continuous regular root lift over a continuous path in `|γ| < r` that contains a closed
        subpath with unequal lifted end values. Then any formal-series germ that solves `R` near 0
        and matches the seed has radius `≤ r`.
      * Supporting results: uniqueness of regular lifts (`regular_lifts_eq`), and exclusion of a
        single-valued continuous root or of an analytic germ.
      * `not_summable_of_radius_lt_norm`: outside the radius the vector series is not even
        conditionally summable.
      * Validation: 1141 guards, 105 modules, exit 0.
      * Still external (at 182): the complex BH dictionary, the HS-germ coefficient matching, and
        the M3 numerical path instance (roots, links, regularity).
    * **Lean, the actual complex BH bridge (191/194, 4fd2834, `ComplexPolynomialSystem.lean`,
      `ParametricContraction.lean`, `ActualComplexBH.lean`, 1268 guards, 114 modules).**
      * The original residual is complexified with all original `Dt`/`G` coordinates, and so are its
        true Jacobian and determinant. The real slices recover the original roots and determinant.
      * Real regularity constructs the complex inverse. The complex IFT constructs a holomorphic
        HS germ. Real and complex coefficients coincide, so the true radii are equal.
      * A seed-linked changed regular complex lift then bounds the original **real** common radius
        and excludes ordinary, even conditional, convergence outside the disc.
      * Physical HS data at `η < 1` discharge the seed-canonicity, germ and inverse premises.
      * The parametric contraction module constructs continuous unique Newton roots from derivative
        defects, with no inverse premise.
      * Still open: the M3 numerical path instance (root boxes, regularity, links, gluing).
      * Feasibility (193, external diagnostic only): with only kernel-proved rational constants (π
        to 20 digits, `e^{−1/2}` to 21) and the old endpoint boxes widened, all 8420 boxes pass a
        direct polynomial Newton self-map. The minimum relative margin is ≈ 1.8e-5 and the defect is
        < 3/5. Structural links and loop disjointness are rechecked.
    * **Lean, the literal M3 model and rectangle lifts (195/196, effd46c, 1314 guards, 118 modules).**
      * `M3ResidualModel`: the M3 data (`η = 49/100`, `z = (7, 14)`, `K = (1, −419/384)`) are
        substituted into the BH polynomials. The result is proved identical to the original BH
        polynomials by polynomial extensionality. It is not a surrogate valid only on roots, and
        there is no rescaling.
        * This gives exact dictionaries for the complex residual, the roots, the true Jacobian and
          the determinant.
        * The original HS data are `Q0 = 8300π/867` and `Q'' = 4400π/289`.
      * `ComplexRectangleNewton`: whole-rectangle Newton self-maps plus weighted real row defects
        construct a continuous, unique, regular complex root lift.
      * `ComplexRectangularCoordinates` and `M3PhysicalBounds` (π, `e^{−1/2}`, `e^{−7k}`) are now
        in the package.
      * Still open: the numerical instance itself.
      * Feasibility (external, private): one 4762-instruction integer program at 128-bit fixed scale
        passes all 8420 map and derivative checks. The worst row bound is ≈ 0.391 and the minimum
        margin ≈ 0.079. A first-cell `decide +kernel` trial is in progress.
      * **Integer-program soundness (197/198, 622b460, 1341 guards, 120 modules).**
        `ScaledIntegerIntervals` proves that signed outward integer arithmetic and shared-register
        programs are sound for every positive scale. `ScaledRectangleCertificates` proves scaled
        midpoint/radius, strict-interior and weighted row inequalities, ending in the normalized
        complex rectangle that the root constructor takes. Neither instantiates M3 numbers.
      * The first kernel runs of the concrete 4762-operation program are expensive. One monolithic
        reduction was stopped at 28 GB with no result. Per-operation local traces are now being
        tried instead.
  * M2's second real root (relative distance 0.04) is a separate regular root, disjoint from the
    certified one. For each fixed `w`, the two local root graphs are disjoint over a `τ` window
    of ±1e-4. With Codex's 009/011 chain this means it is not on the PY-seeded graph (handoffs
    145, 146). It does not show that the two lie in different global components, and it says
    nothing about the canonicity of the second root. Float continuation shows that branch folding near
    `τ ≈ −0.035` and running to large `G_1` as `τ → 0`.
  * The witnesses are exact rationals and were re-checked with stdlib fractions (143). None is
    yet an `EndpointRegular` instance in Lean, or tied to the PY-seeded canonical endpoint.
  * Lean side of that bridge (151, bb3a8bc, `BHPolynomialJacobian.lean`):
    * the formal partials of the literal residual polynomials equal the actual derivative, at every
      point;
    * `EndpointRegular` is equivalent to `det J ≠ 0`;
    * `endpoint_regular_of_row_defect`: every row sum of `|1 − C·J|` below 1 implies
      `EndpointRegular`. This is exactly the form of the external `‖I − CJ‖_∞ < 1` bounds;
    * the vacuum case is instantiated with an explicit exact inverse.

    A numerical instance at M1/M2/M3 still needs kernel enclosures of `π` and `exp`, interval
    bounds of `J` proved in Lean, and the coordinate-order translation.
  * **M2 is now kernel-proved for regularity (152, 952d867, `M2KernelCertificate.lean`).**
    * `actual_regular_on_box` gives `EndpointRegular` at every amplitude point of Codex's widened
      rational root box. The data are `η = 1/10` and `z = (9/5, 12)`, and the coupling and
      strengths are arbitrary.
    * The bound proved is a row defect `< 1e-6`.
    * The ingredients are proved in Lean: the 16 Jacobian entries from the literal polynomials,
      bounds on `π`, and `exp` via a series with its remainder.
    * This is the first positive-density numerical-to-Lean regularity instance.
    * Still external at that stage: that a root lies in that box, the PY-prefix
      identification, first loss, and all of M1 and M3.
  * **M2 root existence is kernel-proved at one fixed rational state (154, 1fa6f4c,
    `M2RootExistence.lean`).**
    * `exists_unique_actual_root` constructs exactly one root inside the same rational box. It
      uses a generic Newton-box criterion (`NewtonBoxExistence`: mean-value contraction plus
      Banach fixed point) with `‖C F(center)‖ ≤ 1e-12`, face margin 1e-10, radius 2e-9, and the
      152 defect `< 1e-6`.
    * The state is `τ = 11227143292458953/2·10^15`, `w = −9657507677060143/2·10^15`. These are
      the exact midpoints of the old τ and w boxes; I checked this.
    * `exists_actual_regular_root` combines this root with 152's regularity.
    * Not covered: the joint zero-mode/tangency conditions, so this τ is not certified as the
      endpoint. The external witness for those is ten-dimensional, as Codex corrected in 155.
      Its unknowns are `(Dt1, Dt2, G1, G2, τ, w, v)`. Its equations are `R = 0`,
      `J v = forcing(w)`, `F0 = 0` and `∇F0·v = 0`. Also not covered: uniqueness outside the box, PY
      membership, first loss, Taylor radius.
  * **The ten-dimensional M2 stationary contact is kernel-proved (156, eb0c269,
    `M2TangencyExistence.lean`).**
    * `exists_unique_system_zero`: a unique zero of all ten equations in a widened rational box.
      The Lean proof uses the full 10×10 Jacobian bounds (every row `< 1e-6`) and the Newton-box
      criterion.
    * `exists_actual_regular_noncanonical_root`: a BH root with `b > 0`, `w < 0` and
      `EndpointRegular`, at which `renewalDet(0) = 0` and the Fourier factor at 0 vanishes. So
      regularity does not imply canonicity.
    * `exists_actual_stationary_branch`: a two-sided analytic root curve at fixed `w`, along
      which the zero-mode factor and its first derivative vanish.
    * Not covered (at 156): positive curvature, weight transversality, first contact, PY/HS
      membership, Taylor radius.
  * **M2 positive curvature and a strict local minimum in coupling are kernel-proved (161,
    f18d28b, `M2Curvature.lean`).**
    * Along the constructed analytic root curve through the contact, the zero-mode observable
      satisfies `f(b) = f'(b) = 0` and `f''(b) = κ > 4/5`.
    * Near `b`, `f(t) ≥ (t − b)²/10`.
    * The acceleration comes from differentiating the actual velocity equations through the
      proved 10×10 Jacobian. `PreconditionedLinearError` supplies the error estimate.
    * Still open (at 161): weight transversality, first contact, HS/PY membership, all-wave
      first loss, Taylor radius.
  * **M2 weight transversality is kernel-proved (163, 893d309, `M2WeightTransversality.lean`).**
    * At the same unique boxed contact, with the coupling `b` fixed, there is an analytic root
      germ in the second-tail weight. Along it, `F0 = 0` at `w` and `dF0/dw < −19`; the numerical
      value is about −21.1.
    * The IFT invertibility comes from the old 4-D row defect.
    * The tangent equation `J p' = b (0, π/6, 0, 0)` is derived by differentiating nearby roots,
      not assumed.
    * With 161, the contact is a strict minimum in `b` and transversal in `w`.
    * Still open (at 163): the joint two-parameter germ and zero contour, first contact, HS/PY
      identification, all-wave first loss, the old narrow box, Taylor radius.
  * **M2 joint zero contour is kernel-proved (165, 5ce451f, `M2JointZeroContour.lean`).**
    * `exists_actual_strict_minimum_zero_contour` constructs one jointly analytic root germ
      `P(b, w)` and an analytic contour `w = ψ(b)`, with `ψ(b0) = w0`, `ψ'(b0) = 0`, and
      `ψ(b) > w0` for nearby `b ≠ b0`.
    * Near `(b0, w0)`, `F0(P) > 0 ⇔ w < ψ(b)`, `F0(P) < 0 ⇔ w > ψ(b)`, and
      `F0(P) = 0 ⇔ w = ψ(b)`.
    * Along the contour the roots are noncanonical, with a zero Laplace factor at 0.
    * Both the curvature in `b` and the slope in `w` are derived on the same `P`.
    * Read the `ContourData` definition: it matches the statement above.
    * Still open (at 165): canonicity on the `F0 > 0` side, first contact, HS/PY matching,
      all-wave first loss, contour curvature `ψ''`, global root count, Taylor radius.
  * **M2 contour curvature and local bifurcation are kernel-proved (168, 039a2c6,
    `M2LocalBifurcation.lean`).**
    * `κ + d ψ'' = 0`, from differentiating the actual contour identity twice. This gives
      `ψ'' = −κ/d > 1/20000`, with `−10001 < d < −19`.
    * On the germ `P`, near `(b0, w0)`:
      * for `w < w0`, `F0 > 0` throughout;
      * for `w = w0`, the only zero is at `b0`;
      * for `w > w0`, there are exactly two zero couplings `l < b0 < r`, with `F0 < 0` between them.
    * These are zero-mode zeros on one germ, not a count of MSA roots. The amplitude Jacobian
      stays regular.
    * Still open: canonicity on the `F0 > 0` side, first contact, HS/PY matching, all-wave first
      loss, global root count, Taylor radius.

**Still open:**
* exclusion of finite amplitude escape for mixtures (matrix case). One species is done (121);
* the full endpoint limit at a *singular*, non-isolated cluster for mixtures. Regular and isolated
  clusters were done in 131 and 137.
  * **One species is closed (183/185, 467a37e, `SelectedBranchAlgebraicity.lean`,
    `ActualAlgebraicEndpoint.lean`, 1178 guards, 107 modules).**
    `exists_scalar_hs_maximal_branch_with_finite_endpoint_limit` holds for every `η < 1`, every
    finite tail set and `ρ ≥ 0`. It constructs the HS maximal canonical branch. If the endpoint
    `b` is finite, then `b > 0` and there is a unique `a` with four properties:
    * `a` is a BH root at `b`;
    * `a` lies in the closure of the canonical amplitudes but is not canonical;
    * `a` is the left limit of the path;
    * `det F(a, k) = 0` at some real `k`.
  * No isolation or finiteness of the endpoint fiber is assumed. The proof constructs primitive
    coordinate relations `d_i det(J)^n P_i(x_i) ∈ (residual ideal)` over `ℝ[t]`. These make the
    candidate fiber of the selected path finite.
  * "Unique" refers to this path's limit only. The original endpoint fiber may contain other roots
    or nonisolated components.
  * For mixtures, the same limit follows once a uniform amplitude bound is supplied. Without a
    bound, the finite endpoint of the HS maximal branch has two possible outcomes (186/190,
    f86fb56, `ActualEndpointEscape.lean`): a full physical limit with a real-wave Fourier zero, or
    amplitude norm → ∞ along the whole left filter. Excluding the norm escape is still open;
* a lower bound on the complex Taylor radius for several tails. One attractive tail is done (131).
  Real-axis canonicity does not give `R_c ≥ τ_inst`: at M3, `R ≤ 84 < τ_lo` (177/178, external);
* the Taylor-convergence and tail-shape classification, which is this note's own question.

Everything from 060 on assumes full closed-right-half-plane canonicity at the base point.

**Status of §8c's `τ_inst ≤ τ_f`:**

* The tangent-OZ dependency named in 026 is discharged by 083. It holds for `k ≠ 0`, which
  suffices for the a.e. cancellation.
* Factor and amplitude recovery is done for all nonnegative densities (091, 096). So a
  canonical BH root has an invertible amplitude Jacobian and cannot be a fold. This holds for
  mixtures as well as for the one-component system of this note.
* Given a continuous branch from a canonical seed with a finite first-loss point, 102 proves
  `τ_inst ≤ τ_f` (nonstrict), with the loss on the Fourier axis.
* Seed canonicity is proved for one component at every `η < 1` (109). The maximal branch exists
  for this note's family (118), and its finite end is a Fourier-axis instability (121). So for
  one species the Lean `β` is this note's `τ_inst`, up to the cluster-versus-limit wording, and
  `τ_inst ≤ τ_f` holds for a transverse fold on the branch (102).
* Strictness is open.

Record this status in §8c's open list at the merge-back.

## Tail-sign classification of whole-interval convergence (2026-10-31)

This section states what is known, by evidence level, about convergence of the coupling series
on the whole initial canonical interval, i.e. `R ≥ τ_inst` (`StableIntervalRadius`).

* **One attractive tail: proved** (Lean `SingleTailCanonicalRadius.maximal_whole_initial_interval_hasSum`).
* **Mixed-sign tails: can fail at a fully canonical state, certified.** M3 has
  `R ≤ 84 < 337/4 < τ_lo`. The implication from a checked chain to `R ≤ 84` is kernel-proved
  (`M3TaylorRadius.radius_of_chainL`); the chain and the canonicity on `[0, τ_lo]` are external
  interval certificates. The mixed-sign threshold `f*` above is float evidence.
* **All tails attractive (every `K_t ≥ 0`): conjectured to converge, float evidence.** For
  mixtures the condition must be `K_t ⪰ 0` as a matrix: entrywise `K_t > 0` is refuted, see
  *Coefficient signs: final status*.
  * `results/two_tail/two_tail_attractive_grid.log` covers 36 states: K = (1, w) with
    w ∈ {0.25, 1, 4}, six rate cells from z = (0.6, 0.84) to (7, 14), and η ∈ {0.3, 0.49}. In
    every state the nearest singularity is the real fold (R_c = τ_f to 1e-9), and
    τ_inst ≤ τ_f with a positive margin.
  * `results/two_tail/coupling_series_sign_probe.log` (the frozen foundation probe) gives no
    coefficient sign change through order 40 in any component. This holds for both two-attractive
    cases and for the binary mixtures, including a repulsive cross strength K₁₂ = −0.3. The
    Domb–Sykes estimate gives R/τ_f = 1.0000 with exponent 1/2. The competing-sign F5 state, by
    contrast, changes sign up to order 40.
  * `results/two_tail/two_tail_attractive_sign_wide.log` is a wider grid of 72 all-attractive states:
    * two-tail rates (0.3, 3), (0.3, 30), (1, 1.05), (1, 10), (3, 30), (10, 30), each with
      w ∈ {0.05, 1, 20};
    * three-tail rates (0.5, 2, 8) and (0.3, 3, 30), with mixed strength ratios;
    * η ∈ {0.05, 0.3, 0.49}.

    No component changes sign through order 30. Wherever the fold lies within τ ≤ 8, Domb–Sykes
    gives R/τ_f = 1 to 5e-4. No counterexample was found.
  * **Reduction.** If every component's positive-order coefficients have one sign, the proved
    `Paper.ActualAnalyticTaylor.actual_radius_eq_fold` gives `R = τ_f`. The proved
    `τ_inst ≤ τ_f` (§8c, transverse fold, Lean 102) then gives convergence on the whole initial
    interval. So the open step is exactly the sign-definiteness of the coefficients for
    `K_t ≥ 0`.
  * The one-tail proof uses a closed form. The multi-tail routes that were tried are listed in
    *Coefficient signs: final status*; nothing here is proved.

## All-attractive mixtures: the all-order sign premise is false (2026-10-31)

**Result: counterexample, multiprecision.** For all-attractive binary mixtures, the all-order sign
premise of `actual_radius_eq_fold` fails. Two all-attractive states (every K_t entry > 0) each
have components whose order-1 and order-2 Taylor coefficients have opposite signs:
* z = (0.5, 3), σ = (1, 1), x₂ = 0.5, η = 0.3: G_t=1 off-diagonal, c₁ = +2.5722e-3,
  c₂ = −1.2407e-3;
* z = (1.8, 12), σ = (1, 3), x₂ = 0.001, η = 0.3: D_t=1 entries (0,1) and (1,1),
  c₁ = +0.1697, c₂ = −0.0209.

In both, K_t = f_t·ε_ij·σ_ij with f = (1, 0.4) and ε = [[1, .7], [.7, .5]].

Evidence:
* `scripts/two_tail/mixture_sign_flip_mp.py` is an independent mpmath port of the residual.
  The order-1 and order-2 coefficients are exact formulas for the cubic residual.
* The coefficients agree to 20 digits at 40 and 80 digits of precision.
* They agree with the float probe to all printed digits.

Log: `results/two_tail/mixture_sign_flip_mp.log` (EXTERNAL, NOT a Lean proof).

What this does NOT refute:
* **Convergence of these two states.** The float series change sign only at orders ≤ 7, then keep
  one sign. Domb–Sykes gives R/τ_f = 1.0000. Other entrywise-attractive binaries do fail to
  converge: see *Coefficient signs: final status*.
* **Pure fluids.** `results/two_tail/attractive_sign_extreme.log` covers 72 states with 2–4 tails,
  rate ratios up to 1000, strength ratios up to 10⁵ and η from 0.01 to 0.49. The 71 that
  completed show no sign change through order 40; one state failed numerically. **Very
  short-range tails are not the issue:** the flips are a mixture effect.

**Lean correction.** `EventuallySignedTaylor.actual_radius_eq_fold_of_eventually_signed` proves
the fold equality under one sign only from some order m on. It uses standard axioms only. For
mixtures the open step is therefore *eventual* sign-definiteness. For pure fluids no flip was seen
at any order, so the strict form remains the conjecture there.

## Coefficient signs: final status (2026-10-31)

Every number below is external: float64 evidence, or multiprecision where marked EXTERNAL. None is
a Lean proof. Logs are in `results/two_tail/` and carry their command lines.

| Class | Sign of the coefficients | `R` against `τ_f`, `τ_inst` | Status |
|---|---|---|---|
| One tail, `K > 0` | one sign | `R = τ_f` | proved in Lean |
| Exchange-symmetric binary, all `K_t ⪰ 0` | modes positive at every order | `R = min(fold₊, fold₋)` | proved on paper, not in Lean |
| T = 1, `K` of rank one, any N | one scalar `ϱ(τ)` positive at every order | `R = τ_f` | on paper, matrix form checked at N ≤ 4, not in Lean |
| Pure, all `K_t > 0`, any T | positive at every order, in all mixed coefficients | `R = τ_f` | **proved on paper** (*Pure fluids: all-order positivity*); **in Lean**: `claude_pure_fluid_mixed_coefficients.md` for the signs, `claude_pure_fluid_taylor_radius_fold.md` for the radius, with `τ_f` read as where the analytic continuation ends |
| Binary, all `K_t ⪰ 0` | changes at low and sometimes late orders; on the state in *A binary with K_t PSD where R < τ_f*, no settling through order 480 | `R < τ_f` occurs, `R ≥ τ_inst` in every state read | **`R = τ_f` and eventual sign refuted** (EXTERNAL); convergence to `τ_inst` open |
| Ternary and quaternary, all `K_t ⪰ 0`, T = 1, 2 | changes at low and sometimes late orders in the samples, none after order 80 of 150 | `R/τ_f` near 1 in the samples | samples only; the binary counterexample was not sought at N = 3, 4 |
| Binary, all entries `> 0`, `K_t` indefinite | can alternate at every order | `R < τ_inst` occurs | **convergence refuted** (EXTERNAL) |
| Mixed-sign tails | changes | `R < τ_inst` occurs (M3) | refuted (certified) |

### Entrywise attraction does not give convergence

**Counterexample (EXTERNAL multiprecision).** η = 3/10, σ = (1, 1), x = (1/2, 1/2), z = 2,
`K = [[1/20, 1], [1, 1/20]]`. All entries are attractive; the eigenvalues are 21/20 and −19/20.

* All eight components alternate strictly in sign from order 1 through order 200.
* The ratio estimate of `R` from the coefficients alone reaches 0.54193 at order 200. The first
  fold on the negative axis, by arclength, is `τ_neg = −0.54190576`.
* Partial sums of `D₀₀`: at τ = 1/2 they converge to −0.23511; at τ = 1 they reach 1.3e49 at
  order 200; at τ = 2, 2.6e109.
* At τ = 1 the real root exists, with `det F(0) = 5.03018`, `min |det F(ik)| = 0.834` on
  0 ≤ k ≤ 200 (step 1/20) and winding 0. The float root agrees.
* `τ_inst = 2.783`, `τ_f = 2.79460`. So the series diverges on `0.5419 < τ < 2.783`, at canonical
  states with no instability anywhere near.

The coefficients agree to 3.7e-48 between 50 and 90 digits, and the mp port agrees with the float
probe at low order. The canonicity reading uses a finite `k` grid, so it is evidence and not an
interval certificate. Logs: `indefinite_binary_mp.log`, `indefinite_binary_check.log`.

**Mechanism, verified.** For this symmetric state `τ_f = 2.794595921` equals the fold of the pure
fluid at the same packing with `K = (K₀₀ + K₀₁)/2`. The null vector at the positive fold is purely
symmetric, and at the negative fold purely antisymmetric (`indefinite_mode_check.log`). The
antisymmetric channel has `K⁻ = (K₀₀ − K₀₁)/2 < 0`, so it is purely repulsive for τ > 0 and its
singularity lies at τ < 0. This is the matrix form of the known failure of a single repulsive tail.
Unlike attraction, it is not visible in the signs of the entries.

Nine indefinite states are compared in `indefinite_binary_check.log`, using `τ_neg` as the radius
(the printed root test `R` carries an amplitude bias of a few percent) and `τ_inst` to its grid step
`τ_f/240`:

| State | `τ_neg` | `τ_inst` | `τ_neg/τ_inst` | Verdict |
|---|---|---|---|---|
| sym (above) | 0.5419 | 2.783 | 0.195 | fails |
| e: η=.4008, σ₂=1.059, x₂=.0118, z=1.4258 | 1.218 | 2.747 | 0.44 | fails |
| f: η=.1833, σ₂=3.345, x₂=.256, z=.5153 | 0.3426 | 0.729 | 0.47 | fails |
| g: η=.4688, σ₂=2.845, x₂=.0544, z=5.3759 | 3.751 | 4.802 | 0.78 | fails |
| c: η=.4936, σ₂=2.765, x₂=.9073, z=2.0264 | 6.475 | 6.553 | 0.988 | fails, narrowly |
| h: T=2 | 2.0648 | 2.0705 | 0.997 | not resolved by the grid step |
| d: η=.02179, σ₂=2.244, x₂=.0119, z=.8477 | 3.865 | 3.824 | 1.011 | passes, narrowly |
| b: η=.1713, σ₂=2.006, x₂=.0351, z=10.1434 | 9.047 | 4.080 | 2.2 | passes |
| a: η=.2238, σ₂=3.645, x₂=.0837, z=10.1207 | 36.81 | 14.42 | 2.6 | passes |

So indefiniteness can cause failure but does not force it. Only `sym` has the multiprecision
certificate. The PSD controls have no fold at τ < 0.

**Consequence.** For mixtures the right analogue of `K_t ≥ 0` is `K_t ⪰ 0`. The earlier sign-flip
state z = (1.8, 12), σ = (1, 3) has an indefinite K; z = (0.5, 3), σ = (1, 1) has a PSD K, and its flip
stands as a PSD flip.

### Positive semidefinite binaries

`attractive_high_order_survey_seed1.log`, order 150, the fold by arclength. For 192 states (96 with
positive entries, 96 with mixed-sign entries; T = 1, 2):

* `R/τ_f` lies in [0.9998, 1.0002].
* T = 1: last sign change at order ≤ 4. T = 2: mostly ≤ 17, with three late cases.
* The latest is real. In the state with last change at order 129 in float, the same state with K
  rounded to four decimals has its change at order 100 (`psd_late_flip_mp.log`, EXTERNAL, one
  precision of 40 digits): one change per affected component, none afterwards through order 150.

In symmetric binaries the origin of the flips is visible: the mode series `X⁺`, `X⁻` have no sign
change through order 30, while the entry `X₀₁ = (X⁺ − X⁻)/2`, a difference of two series with different
radii, flips at orders 2–4 (`symmetric_binary_mode_signs.log`).

The order moved by 29 under a rounding of K, so no uniform bound on the last-change order should
be expected, even though each state's sequence appears to settle. Such a late change is what a
fold residue passing through zero in one component would produce; that explanation is not tested.

**Ternary mixtures** (`attractive_high_order_survey_ternary_seed1.log`, float64 evidence, NOT a Lean proof).
96 states, N = 3, T = 1, 2, order 150, diameter ratio to 4, each `K_t` a sum of two rank-one terms, with positive or
mixed-sign entries: no FLAG, `R/τ_f` in [0.9999, 1.0001]. Largest last-change order: 80 (positive entries, T = 1), 18 (positive,
T = 2), 7 (mixed, T = 1), 63 (mixed, T = 2). This is a survey of one sample and does not bound the last-change order.

**Quaternary mixtures** (`attractive_high_order_survey_quaternary_seed1.log`, float64 evidence, NOT a Lean proof). 96 states built the same way with N = 4: no FLAG,
`R/τ_f` in [1.0000, 1.0001]. Largest last-change order: 4 (positive entries, T = 1), 20 (positive, T = 2), 24 (mixed, T = 1), 17 (mixed, T = 2). N ≥ 5 was not run; this
is a sample, not a statement for all N.

### Pure fluids

* **No sign change in any test.** 96 states with T = 2, 3 through order 150 (rates 0.1–200, strength
  ratio to 1e5, η to 0.6): `R/τ_f` in [0.9997, 1.0043]. 71 extreme states through order 40. Three
  states through order 400 in multiprecision (`attractive_pair_series_mp_*.log`).
* **Adversarial margin search** (`pure_sign_adversarial.log`): the smallest normalised coefficient
  margin stays positive: T = 2 min +0.0648, local +0.05838 at z = (0.667, 200.2), K = (1, 0.001),
  η = 0.01; T = 3 min +0.0328, local +0.02901 at z = (0.1, 30, 200.4), K = (1, 0.001, 0.001), η = 0.01.
  The minima sit on the box boundary, so they are not interior infima.

A search of finitely many states is not a proof of the all-order claim, which stays open.

### Complex branch points exist, and the Stieltjes picture is false

The natural proof would make each component a Stieltjes function of τ. That picture is false.

* **Log-convexity and Hankel tests** (`stieltjes_logconvex_test.log`, 432 attractive states). T = 1:
  no violation. T = 2: 2 log-convexity violations (largest ratio 1.0043) and negative 3 × 3 Hankel
  determinants (D 5, G 3, E 3 states; min D −2.81e-3 at z = (0.53, 20.81), K = (0.023, 89.431),
  η = 0.103). T = 3: 1 violation and negative determinants (D 4, G 2). The mixed-sign control violates
  often.
* **Genuine complex pairs** (`attractive_branch_points.log`). At z = (3.1678, 23.8808),
  K = (0.03773, 62.316), η = 0.1903: `τ_f = 0.49602`, `τ* = 0.639123 ± 0.080379i` (`|τ*|/τ_f = 1.29866`).
  At z = (0.53, 20.81), K = (0.023, 89.431), η = 0.103: `τ_f = 0.218637`, `τ* = 0.3224 ± 0.057499i` (1.49786).
* **Monodromy** (`uhp_monodromy_test.log`, `uhp_monodromy_survey_*.log`). The closed-loop test has
  discrimination: M3 returns for r < 84 and fails above; rays do not (F5 and M3 pass them). A
  non-return occurs on part of the strong-short-range attractive sample, on 3°–177° loops, while
  ordinary-parameter attractive states return out to 60 `τ_f`.

**How close can the pair come?** To within about 1e-5 of the fold from above in this search, and never below it
(`attractive_pair_fast.log`, float64 evidence, NOT a Lean proof). T = 2, 3, rates 0.05–500, strength
ratios 1e-6 to 1e8, η < 0.8: 38854 evaluations (random states and Nelder–Mead descents, so not
independent samples) found no principal-sheet branch point with `|τ*| < τ_f`. The smallest
`|τ*|/τ_f` is 1.000013, at z = (0.62433, 0.57841, 10.5099), K = (1, 0.0013074, 4.1012e7), η = 0.79533. The
descents stop with `arg τ*` near 1e-5 or smaller, many at the strength cap 1e8 or at η ≈ 0.8. These are
where iteration-limited descents stopped, not converged minima, so 1.000013 is not an infimum; *The near tie, and where √3 comes from* shows why the infimum is 1, at `r → 0`. There `R = τ_f` is decided by these branch-point computations alone: a gap of
1e-5 cannot be read from coefficients at any order reached here, and a sign change from such a pair
would come only after order π/arg τ*. Earlier ratios below 1 were false, and every one was a sheet error
that a descent had found by sitting on the acceptance test:

* `attractive_pair_ratio.log` accepted `|u − u*|/|u*| < 0.1` at one radius, and reached 0.99634 and
  0.99978 at distances 0.09–0.098. At those parameters as printed, order-1000 coefficients have no sign change and
  `R/τ_f → 1`, and the states have no other principal-sheet branch point within 1.5 `τ_f`.
* The first version of `attractive_pair_fast` asked for a distance drop of 4 between two radii. It reached
  0.99935 (`attractive_pair_fast_two_radii.log`, 656 hits), mostly on real `τ*` with the drop at 0.25.
  A real `τ*` in (0, τ_f) cannot be on the principal sheet, since the real branch is analytic there.

The test now used reads the distance at `1 − |τ|/|τ*|` = 1e-2, 1e-4, 1e-6, 1e-8 and requires the square-root
law between the last two. A wrong root saturates at the gap between roots, so there is no tolerance to sit
under. Rerunning the 676 earlier states through it leaves none below 1
(`attractive_pair_fast_retest.log`), and the pairs at 1.29866 and 1.49786 pass it, with distances reaching about 1e-4.

**Tracker warning.** `msa_exact_mix.trace_coupling_mix` steps in τ and can jump over a fold onto a
separate real component on strong short-range tails. At z = (1.94, 76.34), K₂/K₁ = 1e5, η = 0.537 it
ended at 0.0023, while the coefficients and the arclength trace agree on a fold at 0.00067860. This
gave false ratios down to 0.31 in an earlier run of the pair search; the coefficients through order
400 (`attractive_pair_series_mp_*.log`, EXTERNAL) refuted them, with no sign change and a real
singularity. Where earlier logs use its end as `τ_f` on such states, that value is only a scale.
Its first-crossing reading is before the fold, so `τ_inst` is unaffected. Use
`attractive_real_branch.first_fold` to get a fold.

**No S-curve was seen.** On the five states traced past the first fold the curve then has τ
monotone decreasing, in three of them down to τ < 0 (`attractive_real_branch.log`). The two global runs
counted turning points on every state (79779 evaluations, no state with more than one; a trace stops at
τ < 0 or at a cap of 6000 steps, so a turning point beyond the cap would not be counted). So the
mechanism that could put a pair in front of the fold, two real folds merging, has no support here.

### Routes to a proof that were tried

| Route | Result | Evidence |
|---|---|---|
| Orthant cone: `S J₀⁻¹ Q(S·,S·) ≤ 0`, same for the cubic part | holds for one tail; fails for T ≥ 2 in one family (`G_fast` from `D₀G₀`, −0.005 to −0.59 normalised) | `sign_cone_test.log` |
| Linear positive form `S(I+E)` | best margin negative (−2.7e-7 to −0.13). The search closes it numerically only | `sign_cone_search.log` |
| Variables (D, P = G D), where F and S are affine | coefficients are not of one sign | `affine_factor_signs.log` |
| Global Pick / Herglotz | false, see above | above |

**True and possibly useful.** At a canonical point with N = 1, any tail signs:
`Im τ Σ K_t Im G_t = (2π)⁻³ ∫₀^∞ k² |S|² (Im ĉ)² dk`, with the defect scaling as 1/k_max
(`herglotz_identity.log`, `herglotz_gram_check.log`). It fails at non-canonical points, and the attractive
branch can lose canonicity in the upper half-plane. At real canonical τ, `M_st = ∂G_s/∂τ_t` is symmetric
and positive definite, entrywise positive on all states tested, including F5 and M3 (so it does not
separate attractive from mixed-sign tails). At τ = 0 there is a closed form:
`M_st = 1/[(z_s + z_t) F(z_s)² F(z_t)²]`, which makes order 1 explicit and positive (M/C = 1 to at worst 1e-5).

**Why a mixture eventual-sign proof is not an easier target.** For algebraic branches, eventual sign is
essentially equivalent to the fold being the unique dominant singularity: Pringsheim gives one direction and
Darboux transfer the other. So the premise of
`EventuallySignedTaylor.actual_radius_eq_fold_of_eventually_signed` is about as hard as its conclusion. It
does not reduce the problem; it states which single sign fact would suffice.

### The near tie, and where √3 comes from

All numbers here are float64 evidence or EXTERNAL multiprecision where marked, NOT a Lean proof, and the expansions are formal
asymptotics checked against exact branch points. They settle what the closest pairs look like. They do not prove the
all-order sign.

**Mechanism.** The closest pairs are not an accident of the search. A strong tail drives the curve, and a weak tail has `F_w` reaching
zero on it. In `(D, P = G D)` the factors are affine, so with `y = D_w`, `p = P_w`, `r = k_w/k_s`, `κ = τ k_s`, the strong tails define
`g = F_w(κ, y, p)` and `h = S_w(κ, y, p)` and the weak tail reads `g = r κ/y`, `p = h y²/(2π r κ)`. With `t = κ₁ − κ`, where `g(κ₁, 0, 0) = 0`:

    c t = r κ₁/y + (b̂/r) y² + next order,     c = −g_κ, γ = −g_p, h₁ = h(κ₁,0,0), b̂ = γ h₁/(2π κ₁),

so `y ~ r^(2/3)` and `t, p ~ r^(1/3)`. The three critical values form an equilateral triangle, whose leftmost vertex is the fold. Seen from it
the pair lies at ±30°, `|τ*|/τ_f − 1 ≈ (√3/2) gap`, and `gap → 0` as `r → 0`. This holds on an open set of `(z_w, z_s, η)`: 22074 of 60000 random
one-strong-tail states have such a tie (`attractive_tie_limit_signs.log`), always with `z_w < 0.42 z_s`.

**So the infimum of `|τ*|/τ_f` is 1, in the limit `r → 0`, not attained.** That is why the descents in *How close can the pair come?* kept going down
to the strength cap: 1.000013 is only where the cap stopped them.

**Local scaling function** (`normal_form_sign.py`, `normal_form_sign.log`). Keeping one coefficient, `τ_c − τ = y² + a y + β/y`. The coefficient is a residue
on a circle about `y = 0`, and with `B = βL^(3/2)`, `A = aL^(1/2)`, `L = n/τ_f` it is a double sum with positive terms for `A ≥ 0`. The Picard form
`y = β/(τ_c − τ − a y − y²)` has nonnegative Taylor coefficients in `(τ, y)` for `a ≥ 0`, so the local form has all-order positivity. For `a < 0` the strong-tail
scaling function changes sign already at A = −0.5, with first sign negative. At `a = 0` it has no free parameter, and it predicts the real coefficients:
weak components at `n·gap` = 0.3, 1, 3, 10, 30 read 0.134–0.145, 0.58–0.59, 1.07–1.08, 1.017–1.021, 1.005 against 0.136–0.144, 0.585–0.590, 1.078, 1.0177, 1.0051.
Strong components agree within 5–10 % at middle orders, with a regular background at low orders. Hence `Lam = ln ρ/θ < √3` is the target for a sign counterexample.
This fails to be a global statement twice over: the regular background is not in the local form, and the form is only local.

**Next order, closed form** (`attractive_tie_limit.py`). The terms of relative size `r^(1/3)` are `y`, `y⁴/r²`, `r²/y²`, all of one class at the critical points `y_c ω^j`,
`ω³ = 1`, so they act as one coefficient. In the variable `ln(κ₁/κ)`, which is what `Lam` reads:

    a  = −g_y + (γ h₁/4π) [ 3/(2cκ₁) − 9 g_κκ/(2c²) − 3 h_κ/(c h₁) + h_p/(γ h₁) + 3 g_κp/(cγ) − g_pp/(2γ²) ],
    Lam − √3 = Λ r^(1/3) + O(r^(2/3)),   Λ = 2√3 a / (3 b̂^(2/3) (κ₁/2)^(1/3)),
    gap = Γ r^(1/3),                     Γ = 3√3 b̂^(1/3) (κ₁/2)^(2/3) / (c κ₁).

So the sign of `Lam − √3` near a tie is the sign of one function of the strong curve at one point, with no free parameter. Also `Lam = cot(direction) + gap` at this order,
which is why states with direction above 30° still have `Lam > √3`: the search's `Lam` and the direction are different quantities.
Against exact branch points (`attractive_tie_limit_control.log`, `attractive_tie_limit_control3.log`):

| State | `r` or `K_w/K_s` | `Lam − √3`, exact / limit | gap, exact / limit |
|---|---|---|---|
| z = (1.0722, 56.33), η = 0.79 | `K_w/K_s` = 1e-9 | 3.157e-3 / 3.155e-3 | 7.921e-4 / 7.915e-4 |
| z = (2.6429, 56.529), η = 0.2641 | `K_w/K_s` = 1e-7 | 1.704e-2 / 1.696e-2 | 2.185e-2 / 2.160e-2 |
| z_w = 1, z_s = (20, 60), m = (1, 1), η = 0.4 | `r` = 1e-6 | 1.146e-2 / 1.142e-2 | 7.890e-3 / 7.850e-3 |
| z_w = 2, z_s = (30, 200), m = (1, 0.2), η = 0.15 | `r` = 1e-6 | 1.477e-2 / 1.471e-2 | 1.800e-2 / 1.782e-2 |

"no exact pair" at the smallest `r` in those logs is the float search of branch points giving up, not absence of a pair.

**The sign of `a`.**

| Search | Output | Ties | `a < 0` | Smallest `Λ/Γ` |
|---|---|---|---|---|
| direct, smallest `Lam` of real states, T = 2, 3, z in [0.2, 500], K to 1e10, η < 0.8 | `attractive_lam_bound.log` | 39136 states, 31094 with a pair | no `Lam < √3` | `Lam − √3` = 0.00145 at gap 3.4e-4, at the K and η caps |
| limit, one strong tail, descents | `attractive_tie_limit_search.log` | 2465579 evaluations | 0 | 0.557685, at the box corner η = 0.001, z_s = 5000, z_w = 6.77 |
| limit, two strong tails, descents | `attractive_tie_limit_strong2.log` | 88346 evaluations | 0 | 0.557685 |
| limit, three strong tails, descents | `attractive_tie_limit_strong3.log` | 84015 evaluations | 0 | 0.557685 |
| limit, two strong tails, random, half with a middle rate within 20 % of `z_w` | `attractive_tie_limit_strong2_random.log` | 9862 samples, 712 of them near `z_w` | 0 | 0.559 |

Descents repeat states, so their counts are not independent samples. Every run stays above the same 0.5577, so in the limit the data say `Lam − √3 ≥ 0.5577 gap`. That number
is where the box ended, not a computed infimum. The direct search and the limit agree: `Lam` approaches `√3` from above, and only as `gap → 0`.

**A false alarm.** The first tracer for several strong tails reported 1116 and 742 states with `a < 0` (those runs were overwritten by the reruns above). The three rechecked are false, and the fixed tracer finds no such state. The
tracer tested its step with a norm, blind to a middle tail with small `D`, and jumped branches. On the first candidate it reported `κ₁ = 1.768e-4`, where a fine direct trace finds `F_w = 0`
near 1.866e-4, together with `F_m = 0` (`attractive_tie_limit_control3.log`). The test is now component by component; the three candidates give no tie, and the runs above are after the fix.

**Sign conditions and terms** (`attractive_tie_limit_signs.log`). Of 60000 random states: 37790 no tie, 22074 ties with `c, γ, h₁ > 0`, 136 with `F_w = 0` only past the strong fold (a grid-end effect), none other.
`γ ≤ 0` or `h₁ ≤ 0` before the fold would turn the `y²` term around, and put a pair ahead of any nearby fold. That was the obvious place for a counterexample, and it did not occur.
Of the seven terms of `a`, `3/(2cκ₁)`, `−9g_κκ/(2c²)`, `−g_pp/(2γ²)` are positive and `3g_κp/(cγ)` negative in every state, while `−g_y`, `−3h_κ/(c h₁)`, `h_p/(γh₁)` take both signs and cancel strongly, with ratios near −2 : 3 : −1 at large `z_s`.
A guessed identity `g_y = −h_p/2π` that would have reduced them to a determinant is false. So `a > 0` has no term-by-term proof, and I have none.

### A stronger statement, and how close a Picard proof gets

**Mixed coefficients.** The all-order sign in one coupling needs `Σ_α c_α K^α` of one sign at each order, for every `K > 0`. The data support something stronger and more usable: `u(τ₁, …, τ_T) − u₀`
has every mixed Taylor coefficient nonnegative. Evidence, NOT a Lean proof:

| Run | Output | States | Order | Negative |
|---|---|---|---|---|
| cubic recursion, float, entries above 1e-9 of the largest at that order | `multivariate_sign_test_T2_o12.log`, `_T2_o24.log`, `_T3_o12.log` | 100, 200 (T = 2), 100 (T = 3) | 12, 24, 12 | none |
| Picard recursion, EXTERNAL mp, 50 and 90 digits, no cut, including near-tie and near-equal rates | `multivariate_sign_mp_T2.log` | 30 (T = 2) | 12 | none of 4680 (`D`), 5400 (`G̃`), 5400 (`1/F`), 5400 (`−ΔF`) |

This began as a conjecture, and is now the theorem of *Pure fluids: all-order positivity*. The induction that proves it runs in the variable `θ`, not in the variables below.

**The affine system after removing the hard-sphere value.** `affine_factor_signs` used `P = G D`, and its mixed signs do not say much. With `G̃ = G − G₀`, `P̃ = D G̃`:

    D_t = τ_t/F_t,   G̃_s = S̃_s/(2π F_s),   F_s = F₀_s + Σ_t (FD_st D_t + FP_st P̃_t),   S̃_s = Σ_t (SD_st D_t + SP_st P̃_t).

If `FD, FP ≤ 0` and `SD, SP ≥ 0` entrywise and `F₀ > 0`, a Picard induction proves every mixed coefficient nonnegative. Three of the four blocks have the right sign, one does not:

* `FD ≤ 0`, `FP ≤ 0`, `F₀ > 0`: no exception in 20000 states in float (`shifted_affine_signs.log`, rates 0.01–1000, η < 0.85) and 2000 at 60 digits (`shifted_affine_closed_form.log`).
* `SD_st = z_t / ((z_s + z_t) F₀_s F₀_t) > 0`, which is the known order-one form of `M_st`, in these variables. Largest relative difference 2.2e-41 at 60 digits. The 263 float states
  with a wrong sign, at rates near 0.01, are float artifacts: none appears at 60 digits.
* **`SP < 0` in every state.** This is the only obstruction in these variables, and it is structural, not marginal. The proof goes around it by changing variables.

These block signs are not proved either, though each block is an explicit function of `(z_s, z_t, η)`, unlike `a`. `S̃` is not the place to fix this: `S̃` has negative monomials from order 2 (1384 of 5400, in 15 of 30 states, first at `(1, 1)`,
`multivariate_sign_mp_T2.log`), while `G̃ = S̃/(2πF)` has none. Positivity of `G̃` therefore comes from `S̃` and `1/F` together, and a proof treating them separately cannot work.

**Invariant cones** (`invariant_cone.py`, `invariant_cone_T2.log`). The smallest cone containing the `J₀⁻¹ e_t`, closed under `−J₀⁻¹Q̃[x, y]` and `−J₀⁻¹C[x, y, w]`, would be a finite certificate at one state if it stayed in the orthant. It does not: 37 of 40 states
escape at step 2, and in the 12 escapes the log prints the negative entry is the fast `G`. The other 3, with nearly equal rates, are not closed after 10 steps. The closure is too coarse: real coefficients take these products only in tied combinations, which cancel. A certificate would
need a cone on the pair tensors `Σ c_β ⊗ c_γ`, and this has not been tried.

### What stays open

By decision of 2026-11-02 the first three items below that are mathematical, `R ≥ τ_inst`, frustrated T = 1 at N ≥ 3, and the opposite-sign class at equal diameters, are recorded as open problems and handed to Codex (handoff 343). They are not claimed solved.

* **Open problem, by decision of 2026-11-02: convergence on the whole canonical interval, `R ≥ τ_inst`, for mixtures with `K_t ⪰ 0`.** Neither proved nor refuted, and work on it has stopped here. No state with `R < τ_inst` was found; the route once proposed in *What the counterexample depends on* fails, as the root can be non-canonical inside the disk.
* **T = 1, N ≥ 3, and T ≥ 2 with one direction at unequal diameters.** `R = τ_f` is neither proved nor refuted, and no pair inside the fold was found. T = 1 of rank one is settled, on paper, in *One tail of rank one*, and T = 1, N = 2 and the sign-coherent classes in *Sign frustration*. Those proofs are on paper, the matrix form underneath is checked and not derived, and for T ≥ 2 the mixture word weights rest on a numerically checked integral.
* **Status of `R ≥ τ_inst` after this work.** Still open, and the route through canonicity on the whole disk is refuted (*What the counterexample depends on*). Two pieces of support, neither a proof for mixtures. In Lean, for one tail in a pure fluid, the first canonical loss lies strictly below both Taylor radii (Codex, 6ed949b, handoff 330). And by hand: at the near-tie mechanism the pole of `h_w` is a zero of `det Z` at real `x = z_w > 0`, already non-canonical, so pairs from that mechanism sit past `τ_inst`. Pairs away from the real axis are not covered.
* **A sharp condition.** At equal diameters, N = 2, same sign of `b_s` is sufficient for coefficient positivity and opposite sign is necessary for failure (certified example in *Sign frustration*), not sufficient. The boundary inside the opposite-sign class is not characterized; the simple orthogonality window was tested and fails as stated (Codex, handoffs 333, 334).
* **A Lean proof of the pure-fluid theorem.** Assigned to Codex by decision of 2026-11-02, handoff 226. Reached formal `H` Picard positivity (41326f9), left aside on reassignment to mixture amplitude escape (handoff 262), resumed by decision of 2026-11-02 (handoffs 288, 289). All-order `r`-coefficient positivity in `θ` is in Lean (02d64a8). Moved to the Claude session (handoff 347) and finished for signs and radius: see the two `claude_pure_fluid_*` notes, which also list what stays unproved. The matrix form, on paper with algebra checked at N ≤ 4, is not part of that assignment.
* **`a > 0`, the near-tie coefficient, for pure fluids.** Not derived directly. It is no longer needed for the pure-fluid sign, and it is false for mixtures.

## Pure fluids: all-order positivity, a proof on paper (2026-11-01)

**Status.** A complete proof on paper, for every T. It is not a Lean theorem. Its algebraic steps are exact computer algebra (`h_function_algebra.log`), its assembled statements were
checked at 60 digits for T = 1…5 (`h_function_representation.log`), and it supersedes the conjecture status of *A stronger statement* below. It covers one component only.

**Theorem.** Let `η ∈ (0,1)`, distinct `z_t > 0`, T arbitrary, and let `u = (D, G)` be the branch of `D_t F_t = τ_t`, `2π G_t F_t = S_t` through the hard-sphere point at `τ = 0`. Then every Taylor coefficient
of `D_s` and of `G_s − G0_s` in `(τ₁, …, τ_T)` is nonnegative. With `τ_t = τ · 2π K_t/z_t`, `K_t > 0`, the coefficients in `τ` are positive at every order. The series has radius `R = τ_f`, the first fold, and the branch
has no singularity on `[0, τ_f)`, with `F_s > 0` up to `τ_f`.

Notation: `ρ = 6η/π`, `A = 6η/(1−η)`, `F0(x)` the hard-sphere factor, `F0_s = F0(z_s)`.

**Step 1: exponentials separate.** With `Ŝ = ρS/x`, the factor is `F(x) = P(x) + e^(−x) Ŝ(x)`, `P` and `Ŝ` rational (`h_function_algebra.log`, A). Put `Λ_t = ρτ_t/F_t²`. Since `C_t F_t = D_t P_t` and `W_t F_t = (ρ/z_t) D_t S_t`:

    Ŝ(x) = a/x³ + q/x² + c/x − Σ_t Λ_t P_t/(x + z_t),
    P(x) = 1 − a/x³ + (a − q)/x² + (q − a/2 − c)/x − Σ_t Λ_t Ŝ_t/(x + z_t),

so `Res_{−z_t} Ŝ = −Λ_t P(z_t)`, `Res_{−z_t} P = −Λ_t Ŝ(z_t)`, with `c = Σ Λ_t P_t` and two linear relations for `a, q`. The BH system is thus linear for given `Λ`. Conversely, a solution of this linear system gives a solution of BH by
`D_t = Λ_t F_t/ρ`, `G_t = z_t Ŝ_t/(2πρF_t)`.

**Step 2: a dressing independent of η.** The hard-sphere matrix `Θ0(x) = [[P0(x), Ŝ0(x)], [Ŝ0(−x), P0(−x)]]` has `det Θ0 = 1` (B). For `w_t` small define

    U(x) = 1 − Σ_t w_t/(x + z_t),    U_s = U(z_s),    θ_s = w_s U_s,    Λ_s = w_s/U_s,
    r_s − Σ_t w_t (r_s − r_t)/(z_s + z_t) = Σ_t w_t z_t/(z_s + z_t),    g(x) = Σ_t w_t (z_t − r_t)/(x + z_t),

so that `g(z_s) = U_s r_s`. Then `P = (U − g/x) P0(x) + (g/x) Ŝ0(−x)`, `Ŝ = (U − g/x) Ŝ0(x) + (g/x) P0(−x)` have exactly the residues of Step 1, by the definitions of `r` and `g`. They tend to the right limits at infinity, and the polar parts at `x = 0` have the
required form. **The two relations for `a, q` hold identically for arbitrary `U, g` regular at 0** (C): they involve only Laurent coefficients at 0, so T does not enter. This is the solution of Step 1, and at `θ = 0` it is the hard-sphere point, so it is the branch.

**Step 3: closed form.** With `ω_s = e^(−z_s) F0(−z_s)/F0_s`, `κ_s = (1 − ω_s)/z_s`, and `F(x) = (U − g/x) F0(x) + (g/x) e^(−x) F0(−x)`, at the nodes, with `τ̂_s = ρτ_s/F0_s²`:

    F_s = F0_s U_s (1 − κ_s r_s),     ρ D_s = F0_s w_s (1 − κ_s r_s),
    2πρ F0_s² (G_s − G0_s) = r_s/(1 − κ_s r_s)   (E),
    τ̂_s = θ_s (1 − κ_s r_s)².

`η` enters only through `F0_s` and `κ_s`, and `U, r` depend only on `(z, θ)`. For T = 1: `r = w/2`, `U_s = 1 − w/(2z)`.

**Step 4: κ > 0 and F0 > 1.** `F0(x) = 1 + ∫₀¹ (1−r)[A + a0 r/2] e^(−xr) dr` with `a0 = ρ A_0 > 0`, so `F0(x) > 1` for every real `x`, with `F0` analytically extended at `x = 0`. The frozen Lean definition is rational and has `F0(ξ, 0) = 1` there (`actual_F0_at_zero`); the proof uses only positive rates, where Lean has `F0 > 1`, `ω < 1`, `κ > 0` (`PureFluidHardSphereNodePositivity`, commit 8cc8ec0). Also (D)
`F0(z) − e^(−z) F0(−z) = (1 − e^(−z)) + A [z(1 + e^(−z)) − 2(1 − e^(−z))]/z² > 0`, since `tanh(z/2) < z/2`. So `κ_s > 0`, with no condition on `η` or `z`.

**Step 5: H-function.** `H = 1/U` satisfies `1/H(x) = 1 − Σ_t θ_t H(z_t)/(x + z_t)`, Chandrasekhar's H-equation with a discrete characteristic. The function `U(x)U(−x)` is even, rational, tends to 1, with `Res_{−z_t} = −θ_t`, so

    U(x) U(−x) = 1 − Σ_t 2 z_t θ_t/(z_t² − x²),   and on x = ik:  |U(ik)|² = 1 − ϑ(k),  ϑ(k) = Σ_t 2 z_t θ_t/(z_t² + k²) > 0.

Similarly `g(x)U(−x) − g(−x)U(x) − x(U(x)U(−x) − 1)` is odd and rational, its residue at `−z_t` vanishes by the definition of `g`, and it tends to 0. So it vanishes, and `r(x) := g(x)/U(x)` satisfies `r(x) − r(−x) = x(1 − 1/(U(x)U(−x)))`.
For small `θ`, `U` has no zero in `Re x ≥ 0`, and `r`, `ln U` are analytic and `O(1/x)` there, so Cauchy's formula on the imaginary axis gives, for `x > 0`:

    r(x)  = (1/π) ∫₀^∞ [k²/(x² + k²)] Σ_{n≥1} ϑ(k)ⁿ dk,
    ln H(x) = (x/π) ∫₀^∞ [1/(x² + k²)] Σ_{n≥1} ϑ(k)ⁿ/n dk.

**Both have nonnegative Taylor coefficients in `θ`, term by term**, since `ϑ(k)ⁿ` is a sum of monomials in `θ` with positive functions of `k` as coefficients. Hence so has `H(x) = exp(ln H(x))`. Note `r` in `w` does not have them, which is why earlier variables failed.

*An algebraic form of the same fact* (`h_positivity_algebraic.log`, EXTERNAL; route unreviewed; handoff 260). For `H`, no integral is needed: `H_s = 1/(1 − Σ_t θ_t H_t/(z_s + z_t))` is itself a positive Picard equation. For `r`, the coefficient is a squared norm, `[θ^α] r(x) = (|α|!/α!) ‖s c_α(s)/(s + x)‖²`, `c_α = Π_t (√(2z_t)/(s + z_t))^α_t`, and at simple poles this is the Cauchy form `Σ_ij β_i β_j/(c_i + c_j) = ∫₀^∞ (Σ_j β_j e^(−c_j t))² dt`. The rational split `r(x) − r(−x) = x(1 − 1/(U(x)U(−x)))` determines it uniquely, so no complex contour or logarithm is required for the coefficient signs.

**Step 6: Picard.** `θ_s = τ̂_s (1 − κ_s r_s(θ))⁻²`, with `κ_s > 0` and `r_s(θ)` nonnegative, no constant term. So `θ(τ̂)` has nonnegative coefficients, by induction on the order. Composing: `r_s(θ(τ̂))`, `H_s(θ(τ̂))` are nonnegative. Then `G_s − G0_s = r_s/(1 − κ_s r_s)/(2πρF0_s²)`, `1/F_s = H_s/(F0_s(1 − κ_s r_s))`, and `D_s = τ_s/F_s` are nonnegative. Strictness for `K_t > 0`: the coefficient of `θ_t^n` in `r_s` and in `ln H_s` is strictly positive, and `θ_t ≥ τ̂_t` coefficientwise, which gives positivity at every order in `τ`.

**Step 7: R = τ_f.** Take all `K_t > 0`, so `τ̂_s > 0` along a ray. Rates that coincide are merged into one tail first.

*Domain.* Let `𝒟 = {θ ≥ 0, ε := 1 − ϑ(0) ≥ 0}`. For `θ ∈ 𝒟`, `ε > 0`, the dispersion function has positive roots `ν_j` and `U(x) = Π_j (x + ν_j)/(x + z_j)`, so `U` has no zero in `Re x ≥ 0`, and the formulas of Step 5, derived for small `θ`, extend to `𝒟` by the identity theorem. Also `H ≥ 1` gives `w > 0`, `U` is increasing, `U_s ≥ U(0) = √ε`. The integrals stay finite as `ε → 0`, since `1 − ϑ(k) ≈ ε + c k²` and `k²` compensates in `r`. Also `θ_s ≤ z_s/2` on `𝒟`.

*The first singularity.* With `f_s = 1 − κ_s r_s`, the Jacobian `J = ∂τ̂/∂θ` has entries `δ_st f_s² − 2 θ_s κ_s f_s ∂r_s/∂θ_t`. By Step 5 `∂r_s/∂θ_t > 0`, so `J` is an irreducible Z-matrix where `f > 0`, and it is the identity at 0, so it is a nonsingular M-matrix up to its first singularity along the ray. There `dθ/dτ̂ ≥ 0`, and `θ_s ≥ τ̂_s > 0`, while `f_s = √(τ̂_s/θ_s)` is positive and bounded below, using `θ_s ≤ z_s/2`. Since `τ̂_s ≤ θ_s ≤ z_s/2`, the ray cannot continue to arbitrary `τ`.
As `ε → 0`, `∂r_s/∂θ_s ~ ∫ k²/(ε + c k²)² dk → +∞`, so `J_ss → −∞`, while a nonsingular M-matrix has `J_ss > 0`. Hence the first singularity occurs at `ε > 0`, with `U_s > 0`, `f_s > 0`, so `F_s > 0` and `D, G` bounded: **no pole**.

*It is a nondegenerate fold.* At the first singularity `J` has a simple zero eigenvalue with positive right and left null vectors `v, l`, by irreducibility. `ln τ̂_s = ln θ_s + 2 ln f_s` is strictly concave along `v`: `r` is convex in `θ` by its integral, so `f` is concave. Since `Dτ̂_s[v] = 0`, `D²τ̂_s[v,v] = τ̂_s D²ln τ̂_s[v,v] < 0`, so `l · D²τ̂[v,v] < 0`. So `θ` has a square-root singularity in `τ`, and the curve `u(θ(τ))` turns there. Before it `τ` is strictly monotone along the curve, so it is the first turning point of the arclength curve, the first fold `τ_f`.

*Conclusion.* The sum of the series is the branch on `[0, τ_f)`, analytic there by the implicit function theorem in `θ`. Pringsheim's theorem says `R` is a singularity on the positive axis, so `R ≥ τ_f`, and the square-root singularity gives `R ≤ τ_f`.

*Independent review of this section* (a separate agent, by hand and numerically, 2026-11-01): no error and no counterexample found; it supplied the three arguments above that the first version lacked, namely extension to `𝒟`, the bound on `f_s`, and nondegeneracy. Its numbers are external evidence, not a Lean check: Newton on `Cubic.res` against Step 3 at 0.5, 0.9, 0.99 `τ_f` on 8 states, differences 1e-16 to 9e-12; 113434 mixed coefficients over 94 states at 90–130 digits with no nonpositive one, apart from the monomials of `D_s` lacking `τ_s`, which vanish exactly; rays to order 600 at 120 digits, long double to order 24000–40000.

*Tool caveat, from the same review.* At sharp folds (`ε ≲ 1e-3`), `attractive_real_branch.first_fold` can return `None`, and `P.arclength` can report the wrong value: z = (.10928, .29722), K = (1, 9.866e-4), η = .77419 has `τ_f ≈ 1.440128`, while `P.arclength` gives 1.43897. Searches using these tools may have skipped such states or read a wrong denominator near them. The closed form of Step 3 does not have this problem and is the better reference there.

**Why earlier attempts failed.** `SP < 0` in *(D, D(G−G0))* is real, and neither `r` nor `S̃` is positive in `w` or `D`. Positivity holds only in `θ = w U`, where the dispersion function `1 − ϑ` appears. The near-tie results are consequences in spirit: the formula `y² + a y + β/y`, `a ≥ 0`, is what this structure looks like locally. I have not derived `a ≥ 0` from the theorem in detail.

**Not covered.** Mixtures (`N ≥ 2`, see *What stays open*), and tails of mixed sign, where `τ̂_s < 0` breaks Step 6 at once, as it must (M3).

**Step 5 without complex analysis (2026-11-02).** The coefficient of `r` has an elementary positive form. By hand, then checked exactly (`r_weight_divided_difference.log`). For a multilinear `S` of size `n ≥ 1` at distinct rates, with `E_S = n! W_S` and handoff 260's rational form, put `y = (x, z_1, .., z_n)`, `w = y²`. Then

    W_S(x) = Σ_t (z_t/(x + z_t)) Π_{u≠t} 2z_u/(z_u² − z_t²) = 2^(n−1) (Π z) A(y),
    A(y) = − Σ_j y_j / Π_{a≠j} (y_a² − y_j²) = (−1)^(n−1) [w_0, .., w_n]√ = (2/π) ∫_0^∞ k² Π_a 1/(k² + y_a²) dk > 0.

The first equality is `1/(x + z_t) = (z_t − x)/(z_t² − x²)` plus the Lagrange identity for `1/Π(z_u² − x²)`. The last is real partial fractions in `k²`, `k²/Π(k² + w_a) = Σ_j (−w_j)/Π_{a≠j}(w_a − w_j) · 1/(k² + w_j)`, which for `n ≥ 1` has each term a convergent arctan integral `∫_0^∞ dk/(k² + y²) = π/2y`. So the weight is a divided difference of the square root, whose alternating derivatives explain the sign. Also `A = s_{δ_(n−2)}(y)/Π_{a<b}(y_a + y_b)` with `δ_m = (m, .., 1)`, from the bialternant with exponents `(2n−2, .., 4, 2, 1, 0)`, so its numerator has nonnegative coefficients: exact at rational points up to n = 8. Repeated rates follow by continuity, since the coefficients are rational in `z` with no pole at positive rates; the split limit agrees with the integral at one state. This replaces the Cauchy-form and Hardy steps of handoff 260 for a Lean proof. The word weights of the mixture section are these same numbers. In Lean, by Codex: `W_S(x) > 0` for pairwise distinct positive rates, `PureFluidRWeightPositivity.multilinear_W_pos` (3d0308b), and the full coefficient formula `[θ^S] r(x) = |S|! W_S(x)` with squarefree nonnegativity, `physicalFormalR_squarefree_eq_weight_all`, `RSeries_squarefree_coeff_nonneg` (2af981e). Repeated indices and coincident rates followed by splitting into labelled copies, coalescing and merging (handoff 313): every nonconstant coefficient of `r` is strictly positive in `θ`, at every `x > 0` and all positive rates, `physicalFormalR_coeff_pos_all`, `RSeries_coeff_pos_all` (02d64a8). So Step 5 is in Lean, as a formal `θ`-coordinate result. Not yet in Lean: Picard inversion to the physical strengths, and `R = τ_f` (handoff 321).

Also `r` is determined by `H` alone: with `E = Σ_t θ_t ∂/∂θ_t` and `m_0 = Σ_t θ_t H_t`, `r(x) = E m_0 − x E ln H(x)`, from `k²/(x² + k²) = 1 − x²/(x² + k²)` in the integrals, as `E` takes `ln(1/(1 − ϑ))` to `1/(1 − ϑ) − 1`. Exact as Taylor polynomials through order 6 at T = 1, 2, order 5 at T = 3, including coincident rates (`r_euler_identity.log`). With `ln H(x) + ln H(−x) = −ln(1 − v(x))` this gives the odd part of `r` at once. It gives no positivity on its own.

## Exchange-symmetric binaries: the proof carries over (2026-11-01)

**Status.** On paper, resting on the pure-fluid proof above, not Lean. Scope: equal diameters, equal densities `r`, each `K^t = [[a_t, b_t], [b_t, a_t]]`. Codex's Lean module `BinaryCanonicalChannels` has the row-mode equations for this class, and `BinaryExchangeSymmetry` excludes amplitude escape; neither states coefficient signs.

**Modes** `X± = X00 ± X01`. Mode `+` is a pure fluid at total density `2r` with `K = (a + b)/2`, `D+ = 2 D_pure`, `G+ = 2 G_pure`. In mode `−`, `Mv = Nc = 0` by antisymmetry, so the hard-sphere part is absent: `Θ0 = I`, `F0 = 1`, `G0 = 0`, with density `r`. Step 1 holds with `a = q = 0`, Step 2 with `D = (U − g/x, g/x)`, and Steps 3–6 read

    r τ_s = θ_s (1 − κ_s r_s)²,   F_s = U_s (1 − κ_s r_s),   r D_s = w_s (1 − κ_s r_s),   2π r G_s = r_s/(1 − κ_s r_s),   κ_s = (1 − e^(−z_s))/z_s > 0,

with `τ_s = τ 2π(a_s − b_s)/z_s`.

**Consequences.**
* If `K^t ⪰ 0` for all `t`, that is `a_t ± b_t ≥ 0`, both mode series have nonnegative coefficients, and `R = min(fold₊, fold₋)` by Step 7 in each mode (a mode with all strengths zero is absent).
* `X00 = (X+ + X−)/2` is then positive at every order. `X01 = (X+ − X−)/2` can change sign, and it has the eventual sign of the mode with the smaller fold whenever `fold₊ ≠ fold₋`. This explains the flips of `symmetric_binary_mode_signs.log`, and it is eventual sign in this class.
* If `a_t − b_t < 0` for all `t`, mode `−` has its fold at `τ < 0` and alternates at every order. That is the mechanism of the refuted indefinite example. For T = 1 its fold is `max_w w(1 − w/2z)(1 − κ w/2)²` in closed form.

**Checks** (`symmetric_binary_theorem_check.log`, float64 evidence, NOT a Lean proof). Against the mixture solver's own roots, 8 states with T = 1, 2, 3: `|G+/2 − G_pure|` below 1.2e-14 in 7 states and 2.2e-8 in one T = 3 state, which I attribute to the damped Picard solve in the script and did not confirm; `|G− − formula|` at most 5.1e-13. For `K = [[1/20, 1], [1, 1/20]]`, `z = 2`, `η = 3/10` the closed forms give `τ = −0.541906` against the reported `R = 0.5419`, and fold₊ `= 2.794596` against the reported `τ_f = 2.7946`, no parameter fitted.

**Not run.** The same decoupling should hold for N equal diameters when the `√ρ K_t √ρ` commute and have `√ρ` as an eigenvector. I did not derive or test this in detail.

## Mixtures with K_t PSD: matrix H-function form, and what positivity fails (2026-11-01)

Float64 evidence, EXTERNAL multiprecision where marked, NOT a Lean proof. No proof of `R = τ_f` for general mixtures follows from this section.

**The form carries over exactly** (`matrix_h_function_check.log`, 30 random states, N = 2–4, T = 1–3, unequal diameters, entries of either sign; largest error by relation 2.7e-7, from float conditioning). With `w = diag √ρ`, `X~ = w⁻¹ X w`, and the causal factor `Z = P + e Ŝ`, `e = diag e^(−sσ_i)`:

    Res_{−z_t} Ŝ = −P(z_t) L_t,   Res_{−z_t} P = −Ŝ(z_t) L_t,   L~_t = Z~_t⁻¹ (τ_t w K_t w) Z~_t⁻ᵀ  ⪰ 0,
    U(x) = I − Σ_t U_t L_t/(x + z_t),   Z_s = Z0_s (I − κ_s r_s) U_s,   κ_s = (I − Z0(z_s)⁻¹ e(z_s) Z0(−z_s))/z_s,
    Ũ(x) Ũ(−x)ᵀ = I − Σ_t 2 z_t θ~_t/(z_t² − x²),   θ~_s = f~_s⁻¹ K̂_s f~_s⁻ᵀ ⪰ 0,   K̂_s = Z~0_s⁻¹ τ_s w K_s w Z~0_s⁻ᵀ,
    2π w (G_s − G0_s) w = Z~0_s⁻ᵀ r~_s f~_s⁻¹ Z~0_s⁻¹.

These are checked identities here, not derived for every N and T. So `τ` enters only through the PSD `K̂_s`, the hard spheres only through `Z0(±z_s)`, and `U, r` depend only on `(z, θ~)`.

**Where the scalar proof stops.** An earlier version of this paragraph said that `r~` is not an integral of powers of `ϑ(k)`. That was wrong: it read the difference between `Ũ(−x)ᵀŨ(x)` and `Ũ(x)Ũ(−x)ᵀ` as an obstruction, whereas `r = gU⁻¹` pairs with the second. The scalar formula holds as it stands (`matrix_r_integral.log`, 40 states, T, N ≤ 3, largest relative difference 1.67e-11, and `r~` symmetric PSD):

    r~(x) = (1/π) ∫ k²/(x² + k²) [(I − ϑ(k))⁻¹ − I] dk,   ϑ(k) = Σ_t 2 z_t θ~_t/(z_t² + k²).

So `r~` and `H` are series in the words of the letters `θ~_t`, and each word carries the scalar weight of its multiset of tails, nonnegative by the pure-fluid Step 5; `matrix_r_positivity.log` found no negative entry on 1500 entrywise nonnegative PSD inputs, order 10. Through `θ~_s = f~_s⁻¹ K̂_s f~_s⁻ᵀ` and `f~_s = I − κ~_s r~_s`, the quantities `θ~`, `r~`, `f~⁻¹` are then free series with nonnegative coefficients in the letters `{K̂_s, κ~_s}`. What stops the proof is not the analysis but the signs of these letters. See *Sign frustration* below.

**Positivity that is false.** All with `K_t ⪰ 0`.

| Statement | Result | Evidence |
|---|---|---|
| Coefficient matrices of `G_t` are PSD | false, already N = 2, T = 1: `λ_min/λ_max` down to −1e-3 at order 7 | `mixture_loewner_test.log` |
| Coefficients of the excess energy `E = Σ_t Σ_ij ρ_i ρ_j K^t_ij ĝ_ij(z_t)` are positive | positive on 96 random and 33 constructed states, including 120° rank-one triples, but **false**: 6 of 6 states read at 50 and 100 digits have negative coefficients with the same signs at both precisions (EXTERNAL mp) | `mixture_loewner_test.log`, `mixture_energy_attack.log`, `mixture_energy_fast.log`, `mixture_energy_mp.log` |

Example: `σ = (1, 2.43779)`, `x = (.55584, .44416)`, `η = .49687`, `z = 8.48835`, `K = [[.1089339, .1698349], [.1698349, 1]]`, eigenvalues 0.078 and 1.03: `E_n` is negative at orders 6–13 and positive from 14 through 400 in float; mp confirms orders 6–12. `R/τ_f = 0.9999–1.0000` there, `τ_f = 71.0584`, one turning point, and the branch-point search finds no pair within `1.5 τ_f`. All six states read in mp behave this way (`energy_negative_state.log`, `energy_negative_unresolved.log`, order 400 or 200 in float): the window closes by order 19, and in four of them `R/τ_f` from all components lies in 0.9997–1.0011, with any pair found outside the fold, at ratio 1.018–1.038. In the other two the default arclength found no fold, a longer one did, and there the check is the single ratio estimate of `E` printed in that log. That is coefficient evidence at the states read. It does not follow from the real-axis no-escape theorem of Codex's handoff 206, which is compatible with a complex branch point inside the fold, and it is not a statement about all states. The search's `y` values of 1e100 are from its scale `E_{N−1}/E_N` in a window, not a measure of size, and most of the 9971 flagged states were not read in mp.

Energy would have served Pringsheim: `E = dW/dτ` for a potential `W`, so its square-root coefficient at a simple branch point on the sheet is the transversality of the ray, and `E` sees every such branch point. That argument remains, but it has no positive series to act on, so this route to `R = τ_f` is closed.

## A binary with K_t PSD where R < τ_f (2026-11-01)

**Statement.** All-attractive positive semidefinite tails do not give `R = τ_f` or eventual sign for mixtures. EXTERNAL multiprecision and float64 evidence, NOT a Lean proof.

    σ = (1, 234/100), x₂ = 453/10000, η = 531/1000, z = (139/100, 412/10),
    K₁ = c₁ (1, r₁)(1, r₁)ᵀ, K₂ = c₂ (1, r₂)(1, r₂)ᵀ, c = (785/10⁶, 734/10⁴), r = (683/1000, 369/100).

All entries are positive, each `K_t` is PSD of rank one, and the two do not commute.

| Quantity | Value | Source |
|---|---|---|
| first canonicity loss `τ_inst` (winding of `det Z` on the imaginary axis) | 196.068 | `psd_counterexample_float.log` |
| radius from coefficients, 16 components, exact rational input, no root tracking, orders to 480 | 314.71–314.84 | `psd_counterexample_mp.log`, 60 and 100 digits, relative difference at most 4.6e-51 |
| principal-sheet pair `τ*`, `|τ*|` | 314.567 + 8.515 i, 314.682, four-radius sheet test passed | `psd_counterexample_float.log` |
| first fold `τ_f`, then a second turning point | 327.402, then 286.040 (an S-curve) | fine real trace, same log |

So `R/τ_f = 0.961` and `R/τ_inst = 1.60`. Every component keeps changing sign: last changes at orders 378–415 of the 480 read, spacing 117 at high order against the half period `π/arg τ* = 116.1`, with the next change due beyond 480, and the sign changes are the same at both precisions. A fold-dominated series would settle to one sign. The coefficient radius, 4 % below the fold, is what excludes that. The state survives rounding its parameters to 3 digits, and the search state it came from has ratio 0.9615, so this is an open set. It was found with `mixture_pair_search.py --seeded`; `mixture_below_one_check.log` has the coefficient check on the unrounded state (slope `R/|τ*| = 0.99997`, spacing 110 against 109.8).

**How common.** `mixture_pair_search_seeded.log`, N = 2, T = 2, 3, near-tie sampling: 5819 `K`, 2720 with a pair, 25 lines with `Lam < √3`, spread over 5 of 12 workers, while all lines with ratio below 1 come from one `(σ, x, η, z)`, and 4 S-curves, against none in the pure-fluid searches. So the near-tie coefficient `a` can be negative for noncommuting tails, which is what the pure-fluid theorem excludes, and when it is large enough the pair passes inside the fold. The mechanism behind this is not derived.

**Physical convergence is not refuted.** Convergence on the initial interval needs `R ≥ τ_inst`, and it holds on this state. A direct search found no failure:

| Search | Output | States | Result |
|---|---|---|---|
| `K` at fixed `(σ, x, η, z)`, T = 1, 2, objective `|τ*|/τ_0`, `τ_0 ≥ τ_inst` the first zero of `det Z(0)` | `mixture_inst_search.log` | 6588 `K`, 1773 with a pair | none below 1, smallest 1.040; no pair at all for T = 1 |
| all parameters free, from the closest states | `mixture_inst_descent.log` | 1358 | none below 1, smallest 1.0201 |

`|τ*|/τ_0 ≥ 1` implies `R ≥ τ_inst` for that pair. 1.0201 is where the descents stopped, not an infimum, these are few states, and tails of general rank, N ≥ 3, and T ≥ 3 were barely covered. This is absence of a counterexample in a search, not a proof.

## One tail of rank one, any N: positivity of one scalar and R = τ_f (2026-11-01)

**Status.** On paper, on top of the matrix form. The matrix form's algebra is an exact-rational check at N ≤ 4, not a derivation for all N, so for N ≥ 5 this rests on that form being right. Not Lean.

**Algebra** (`matrix_h_function_algebra.log`, exact rationals, 4 random states at each of N = 1, 2, 3, 4, with generic `U, g`, T not entering): every polar term and both constraints for `A_j`, `qp_ij` vanish identically, with `Mv_j`, `Nc_j` read from the Laurent coefficients at 0, column by column. The hard-sphere matrix is symplectic in the columns, `P0(−s)ᵀρ⁻¹P0(s) − Ŝ0(−s)ᵀρ⁻¹Ŝ0(s) = ρ⁻¹`. Pairing rows instead fails for N ≥ 2, because the residues act on the right.

**κ̃ ⪰ 0, any N.** With `B(s) = I − √ρ Q̂(s) √ρ` the physical factor, `Ξ(s) := Z~0(s)⁻¹ ẽ(s) Z~0(−s) = ẽ^(1/2) B(s)⁻¹ B(−s) ẽ^(1/2)`, `ẽ = diag e^(−sσ_i)`.
* `K(s) = B(s) B(−s)ᵀ` is even, which says `B(s)⁻¹B(−s)` is symmetric, so `Ξ(s)` is symmetric at real `s`.
* `K(ik)` is real, so `B B† = B̄ Bᵀ`, which says `B⁻¹B̄` is unitary, and `ẽ^(1/2)(ik)` is a unitary diagonal, so `Ξ(ik)` is unitary.
* `Ξ` is analytic and bounded in `Re s > 0`: the hard-sphere factor is canonical, and `ẽ(s)` cancels the growth of `Z~0(−s)`. By the maximum principle `|Ξ| ≤ 1` there, a matrix inner function.
So `I − Ξ(z) ⪰ 0` and `κ~ = (I − Ξ(z))/z ⪰ 0`. In the scalar case this is `ω < 1` of Step 4. Check (`t1_rank_one_check.log`, float): 30 mixtures, N = 2–5, 4 rates each: asymmetry at most 2e-8, smallest eigenvalue of `I − Ξ` 0.0375, `|Ξ Ξ* − I|` at most 5.7e-9 on the axis, largest `|Ξ|` 0.962.

**Closure.** Take T = 1 and `K = v vᵀ`, so `K̂ = τ u uᵀ`. For T = 1, `U` and `r~` are scalar functions of `θ~` (with `θ = 2r(1 − r/z)`, `r = w/2`), and `θ~` has rank one: `θ~ = τ w wᵀ`, `r~ w = ϱ w`. Then `f~ w = u` becomes `(I − ϱ κ~) w = u`, so with `κ_i, u_i` in the eigenbasis of `κ~`:

    2 ϱ (1 − ϱ/z) = τ Φ(ϱ),     Φ(ϱ) = uᵀ(I − ϱκ~)⁻²u = Σ_i u_i²/(1 − ϱκ_i)²,
    w = (I − ϱκ~)⁻¹u,     r~ f~⁻¹ = ϱ w wᵀ/Ψ(ϱ),     Ψ(ϱ) = uᵀ(I − ϱκ~)⁻¹u = Σ_i u_i²/(1 − ϱκ_i).

`Φ` has positive coefficients since `κ_i ≥ 0`, so `ϱ = τ Φ(ϱ)/(2(1 − ϱ/z))` is a positive Picard equation: **`ϱ(τ)` has nonnegative coefficients**, and by Pringsheim its radius is the first turning point of `τ(ϱ) = 2ϱ(1 − ϱ/z)/Φ(ϱ)`. That radius is in fact `τ_f`: the maximum occurs before `ϱ = z/2`, and before the first pole `1/κ_max`, where `τ(ϱ) → 0`.
Everything else is analytic in `ϱ` on the disk `|ϱ| ≤ ϱ_f`: `(I − ϱκ~)⁻¹` has poles only at `ϱ = 1/κ_i > ϱ_f`; `Ψ` is Herglotz in `ϱ`, so its zeros are real, and it is positive on the real part of the disk; `1 − ϱ/z ≠ 0` there since `ϱ_f < z/2`. The rank-one projector on the range carries `1/Φ(ϱ)`, and `Φ` can vanish at complex `ϱ`, but not on the branch: `τΦ = 2ϱ(1 − ϱ/z)` makes `Φ = 0` possible only at `ϱ = 0` or `z`. So every `D, G` entry is analytic for `|τ| < τ_f`, and **`R = τ_f`, any N**. Since `ϱ(τ)` is aperiodic the fold is the only singularity on the circle, so each entry whose fold residue is nonzero has eventual sign.

**Checks.** Arclength fold against the scalar equation with no parameter, 10 states, N = 2, 3: relative difference at most 1e-11. On those states `R/τ_f = 1.0000`, no pair, and no sign change of any component, order 200 (`t1_rank_one_check.log`). No sign change at all is more than the argument gives, which I do not explain.

## What the counterexample depends on, and where R ≥ τ_inst stands (2026-11-01)

Float64 evidence, NOT a Lean proof.

| Class | Search | Result |
|---|---|---|
| T = 2, 3, `K_t` of different directions | `mixture_pair_search_seeded.log`, 5819 `K`, 2720 with a pair | `Lam` far below √3, ratio down to 0.9615, S-curves |
| T ≥ 2, one direction, `K_t = c_t v vᵀ` | `mixture_special_search.log`, 1850 `K`, 582 with a pair | no `Lam < √3`, smallest √3 + 0.0064, no S-curve: as for pure fluids |
| T = 1, rank 2, strengths far apart | same log, 4249 `K` | no pair at all |

Different directions are not by themselves the cause, and unequal diameters are not needed: a certified example at equal diameters is in *Sign frustration*, and flipping one coupling sign there removes the failure. These searches led to the statements of that section, which replace the earlier remark that nothing is proved here: T = 1, N = 2 is settled on paper. For one direction, `R = τ_f` holds at equal diameters and where the criterion holds at unequal ones (69 of 76 random states), on a connected block with every `K_t ≠ 0`.

**Canonicity in the complex disk: an earlier version here was wrong.** It reported no non-canonical point in the disk on 15 + 82 PSD states, and a route to `R ≥ τ_inst` through (a) the root stays canonical on `|τ| < τ_inst` and (b) canonical roots have no branch point. Those windings went through `msa_exact_mix._pieces`, which stores `float64`, so at complex `τ` they read a root with its imaginary part dropped: a complex step returns a derivative of 2e-8 where the true one is 0.19 to 0.47 (`complex_path_check.log`). `canonical_disk_test.log` and `mixture_disk_search.log` are therefore invalid at complex `τ`. Windings at real `τ`, hence `τ_inst`, and the coefficient certificates are unaffected.

Redone with amplitudes kept complex (`complex_pieces.py`, complex step agreeing to 1e-8; `disk_recheck.log`, `disk_winding_redo.log`). On 60 PSD states and 1920 disk points, one state has non-canonical points inside the disk. **So (a) is false.** It is `σ = (1, 2.4974)`, `x_1 = 0.2934`, `η = 0.5376`, `z = 41.0`, rank-one `K`: `τ_inst = 171.2` with one winding change in 120 real points, while on the ray at 60° the winding changes at `q ≈ 0.90`, with a zero of `det Z` near `k ≈ 2.57`, and at `q ≈ 0.97` and `1.0` on the rays at 30° and 15° (`disk_hit_check.log`). There `R = τ_f = 851.8`, as for any rank-one tail, so `R` is far above `τ_inst`: this refutes the route and not `R ≥ τ_inst`. The indefinite control separates (non-canonical points and a stopped ray).

Part (b) has support that survives: all 9 pairs read have winding −1 or −2 at the root next to `τ*`, none canonical, with smallest `|τ*|/τ_inst` 1.30 in this sample. Nine pairs is thin. The 1.02 of `mixture_inst_descent.log` rests on real windings and is unaffected by the `float64` issue, but it measures the wrong thing: that pair lies after the real fold, `|τ*|/τ_f = 1.00685`, so it is not the leading singularity (Codex, handoff 345). Among pairs before the fold, the smallest `|τ*|/τ_inst` read so far is about 1.57 (`results/codex_psd_binding/descent_120s.log`, from a short search, float64). A search seeded on such states, a fast strong tail with `τ_inst/τ_f` down to 0.063 (`inst_search_deep.log`, 926 `K`, 166 with a pair, short descents), finds nothing below 1, smallest `|τ*|/τ_inst` 1.196; that search did not require the pair to precede the fold. It is weak evidence, as the sample is small.

**Two other ideas tested for the same purpose.** A Jacobian zero needs `∫ tr(φ̂ S φ̂ S) = 0` with `φ` supported in the core, and if `|arg S(k)| < π/4` at every `k` then `S ⊗ S` has its numerical range in the open right half-plane, which excludes this. `disk_recheck.log` measures the angle: at `k → 0` it exceeds 45° already near `q = 0.5` to `0.8` at intermediate ray angles, and the Hermitian part of `S⁻¹` stops being positive. So the condition covers only part of the disk. Whether the core support of `φ` rescues it is not studied. A Hermitian-pencil argument, `S⁻¹ = M_0 − τM_1` with `M_1 ⪰ 0`, would forbid zeros at complex `τ` if `M_0` did not depend on `τ`; the state above shows such zeros exist, so `M_0`'s dependence is not a small correction. `disk_sector_measure.log` is invalid: same `float64` path, and a wrong normalisation of `M_1`, which should carry `e^(zσ_ij)`.

## Sign frustration: when K_t PSD mixtures do have R = τ_f (2026-11-01)

Hand reasoning plus float64 evidence, NOT a Lean proof. The counterexample shows that `R = τ_f` needs a condition. This section gives a sufficient one that holds on most random states. An independent referee read this section; the first version had a false sentence on the fold and a missing step, repaired below, and the pitchfork is the referee's finding.

**Criterion.** By *Where the scalar proof stops*, `θ~`, `r~`, `f~⁻¹` are free series with nonnegative coefficients in the letters `{K̂_s, κ~_s}`; `κ~_s` is symmetric. The recursion closes order by order in `τ`, since `θ~` at order `n` needs `f~⁻¹` only to order `n − 1`, as `K̂` carries one `τ`. Also `H_s = (I − Σ_t θ~_t H_tᵀ/(z_s + z_t))⁻¹` is a positive Picard equation, and `Z~_s⁻¹ = H_s f~_s⁻¹ Z~0_s⁻¹`, so the same holds for what `D` needs.

Suppose one orthogonal `O` makes every `O K̂_s Oᵀ` and every `O κ~_s Oᵀ` entrywise nonnegative. Then in that basis every entry of these series has nonnegative Taylor coefficients, and Pringsheim puts a singularity at `τ = R` on the positive axis. The word-weight formula rests on the matrix integral above, checked numerically and not derived for all T, N, and the whole setting rests on the matrix form, whose identities are checked at N ≤ 4 and not derived for all N. On 200 abstract states with nonnegative letters (T, N ≤ 3, order 8), no entry of `θ`, `r`, `h`, `Y`, `H` is negative; flipping one off-diagonal of `κ` gives negative entries on 51 of 200.

**The turn, T ≥ 2.** Hand reasoning, resting on the same checked identities, read twice by the referee, with its fixes included. Assume the letters are nonnegative in the basis `O`. They are symmetric, so if their common graph on coordinates is disconnected the system is a direct sum, treated block by block. Take a connected block, and assume **`K̂_s ≠ 0` on it for every `s`**. Since `K̂_s ⪰ 0`, it then has some positive diagonal entry.

The core system is `(θ~, r~, h)`, with `h_s = f~_s⁻¹`, and `r~` given by the word series. Columns `j` of `h_s` with `K̂_s,jj = 0` feed nothing back and are downstream, and so are `H` and `D`. Let `R_c` be the radius of the core. On `0 ≤ τ < R_c` all core series converge and all entries increase.

1. *`θ~`.* Convergence forces the Perron eigenvalue of `ϑ(k)` below 1 for `k > 0`, so `ϑ(0) ⪯ I`, and since each `θ~_t ⪰ 0`, `θ~_t ⪯ (z_t/2) I`. This does not use `H`.
2. *`r~`.* `ϑ(k) ⪯ g(k) ϑ(0) ⪯ g(k) I` with `g = z_max²/(z_max² + k²)`, so `(I − ϑ(k))⁻¹ − I ⪯ (z_max²/k²) I`, and the integral on `(0, ∞)` gives `r~(x) ⪯ (z_max²/2x) I`. At T = 1 and `x = z` this is the sharp `r~ ⪯ (z/2) I`. On 40 random states near the edge the largest ratio to this bound is 0.9947 (`referee_r3.log`).
3. *`h`.* All terms in `θ~_s,ii = Σ h_ik K̂_s,kl h_il` are nonnegative, so `θ~_s,ii ≥ h_ij² K̂_s,jj`, and step 1 bounds column `j` of `h_s` where `K̂_s,jj > 0`. On a connected block `r~_s > 0` makes `κ~_s r~_s` irreducible on its support, so if its Perron eigenvalue tended to 1 all entries of `h_s` would diverge together. One bounded column excludes that, so all of `h_s` is bounded.
4. *Strong connectivity of the core.* `κ~_s,ii > 0` since `κ~_s ≻ 0`, as `‖Ξ(z_s)‖ < 1`. For all `s, t, i, j`, `θ~_t,ij` feeds `r~_s,ij` with positive weight, `r~_s,ij` feeds `h_s,ij`, and `h_s,ij` feeds `θ~_s,ii` through `K̂_s,jj > 0`. Graph edges link entries through `K̂_s,kl > 0` and through `κ~_s,kl > 0`.
5. *The core has a square-root turn at `R_c`.* Write the core as `y = Φ(y, τ)`. `Φ` has nonnegative Taylor coefficients: the word series has positive weights and converges while the Perron eigenvalue of `ϑ(0)` is below 1, by Tonelli and `ϑ(k) ≤ g(k) ϑ(0)` entrywise. As `ϑ(0)` approaches `I`, with Perron vector `v > 0` by connectivity, `δr~ ≈ v vᵀ (vᵀ δϑ v) ε^(−1/2)`, so the Perron eigenvalue `ρ` of `D_yΦ` reaches 1 strictly before that edge (`dr~·√ε` stabilises to ε = 1e-6, `referee_r3.log`). If `ρ = 1` at `τ* < R_c` with left Perron vector `l > 0`, then for `τ > τ*`, `y − y* ≥ DΦ*(y − y*) +` a strictly positive term, and multiplying by `l` is a contradiction. So `ρ < 1` on `[0, R_c)`, and the finite limit at `R_c` has `ρ = 1`. There `l·∂_τΦ > 0` and `l·D²Φ[v, v] > 0`, which gives a square root, a true turn, and the first one since `y′` is finite before it.
6. *Everything else.* The edge is excluded at `R_c`, so `H` is analytic there and Pringsheim gives no earlier singularity. `‖H(ik)‖² = ‖(I − ϑ(k))⁻¹‖ ≤ 1 + z_max²/k²`, and `log‖H‖` is subharmonic in the right half-plane, where `H` is bounded because the zero count cannot change along the ray. So `‖H(x)‖ ≤ 1 + z_max/x` (largest ratio 0.9947). By `|y(τ)| ≤ y(|τ|)`, the series converge on the disk `|τ| < R_c`. Since `h_s = I + κ~_s Y_s` with `κ~_s` invertible, `G_s` is affine in `h_s`, and `v > 0` carries the square root to every `O`-basis entry of `Y_s`. So `R_c` is the radius of the collection `(D, G)`, though a single physical entry could in principle be larger.

Under these hypotheses `R = τ_f`, on paper. Not derived: the matrix form and the matrix integral. The weakened hypothesis was tested on 4 states with a zero diagonal entry of `K̂_1` (`referee_r5.log`, `referee_r6.log`): every `O`-basis entry of `Y` has the radius of the turn, with no earlier pole. Its coverage: rank-one tails with zero components are included, and all `K_t ≠ 0` on a connected block suffices.

**A wholly passive tail has a pole before the fold.** The condition `K̂_s ≠ 0` matters. Pure fluid, `K_1 = 0`, one active tail `z_2 = z`. In closed form `r(x) = 2z²p(1 − p)/(x + z − 2zp)`, and `G_1` is proportional to `r(z_1)/(1 − κ(z_1) r(z_1))`, with a simple pole at the `p` below the fold where `κ(z_1) r(z_1) = 1`, if there is one. Prediction written first; `fictitious_tail_pole.log`, `referee_r1.log`:

| `η, z_1, z_2` | Closed-form pole | Radius of `G_1` | Fold, closed form | `T = 1` radius | First turn at `K_1 = 1e-3, 1e-5, 1e-11` |
|---|---|---|---|---|---|
| .3, .5, 8 | 6.01877 | 6.01877 | 7.22424 | 7.22422 | 5.109, 5.845, 6.01709 |
| .45, .8, 12 | 10.87560 | 10.87560 | 12.97967 | 12.97964 | 9.730, 10.649, 10.87339 |
| .2, .3, 5 | 3.55118 | 3.55118 | 3.99923 | 3.99922 | 2.914, 3.439, 3.55013 |
| .45, 6, 8 | none | | 8.41448 | 8.41447 | 8.403, 8.414 |

In the second row the `T = 2` run reads 10.825 for `G_2`. That is noise in the numerically polarised tensors: entries of 2.2e-16 and 3.7e-17 couple `G_1` into `G_2` in that row only, and with them zeroed the radius is 12.97964 with positive coefficients (`referee_r4.log`). Rescaling could not show this.

This is the mechanism of *The near tie*: `F_w` reaching zero on the strong-tail curve is this pole. As `K_1 → 0⁺`, pole minus turn falls as `K_1^(1/3)`, local exponent 0.333–0.334 at `K_1 = 1e-11`, and the equilateral triangle gives the 30° and `√3` found there. The radius of the collection is continuous at `K_1 = 0` where a pole exists: 6.0188 is both `R(0)` and `lim R`. What jumps is the radius of the single entry `G_2` and the first turn, from 7.22 to about 6.02 in the first row. So the pure-fluid hypothesis `K_t > 0` is a real one for `R = τ_f`: at `K_t = 0` with a pole, `R` is below the active fold.

The pitchfork and the pole share a structure: a reducible positive system, with a block reaching `ρ = 1` before the active fold. A homogeneous block (`p_12 ≡ 0`) is invisible to the series, while an inhomogeneous one (`h_s = I + …`) is a simple pole in that block only. Coupling gives a turn tending to it, as `K^(1/3)` for the pole.

The entries in the physical basis are linear combinations with mixed signs, so they can have a window of negative coefficients while `R = τ_f`. That is what the negative energy states of *Positivity that is false* show (`R/τ_f = 0.9997–1.0011`).

**Tests, N = 2, T = 2** (`frustration_criterion_test.log`, `frustration_base_rate.log`; a rotation grid of 1441 angles, with one axis flip):

| Sample | States | Violate the criterion |
|---|---|---|
| Logged `Lam < √3`, from descents, sharing 7 values of `x` | 28 | 28 |
| Seeded distribution, `Lam < √3` | 4 | 4 |
| Seeded distribution, `Lam ≥ √3` | 184 | 18 |
| Seeded distribution, no pair | 79 | 9 |
| Random, margin below 0 | 100 | 18 |

The seeded rows count only margin below −1e-3; on the random sample that threshold gives 14 instead of 18, so the seeded base rate of about 10 % is somewhat understated. The 28 lines are not independent, and of their ratios below 1 only 0.9615 had its coefficients read. Direction of the evidence: every state with `Lam < √3` violates the criterion, as the argument requires, but this is weaker than 32 independent trials.

On the random states meeting it, at most 82, since states with no fold found are skipped after being counted, no coefficient of `Y_s = O Z~0_sᵀ 2π w (G_s − G0_s) w Z~0_s Oᵀ` falls below −1e-9 relative to its largest entry (order 240), and `R/τ_f` lies in 1.0000–1.0001. It is sufficient and not necessary: 27 violating states show no `Lam < √3` in the pair search, though their coefficients were not read. 13 of the 100 meet it with margin below 1e-3. The result does not depend on the grid: 40001 angles reproduce 18, 24 of 24, and 69 of 76. One direction, `K_t = c_t v vᵀ`: met on 24 of 24 at equal diameters and 69 of 76 at unequal ones.

**Equal diameters: the sign of the density-concentration coupling.** At equal diameters `Z~0(x) = I + (F0(x) − 1) e0 e0ᵀ`, `e0 = √ρ/|√ρ|` (error at most 1.7e-13 on 4 states), and `Ξ = e^(−z)(I − P) + e^(−z) (F0(−z)/F0(z)) P`, `P = e0 e0ᵀ` (error at most 6e-16). So every `Z~0(z_s)` and every `Ξ(z_s)` is diagonal in a fixed basis `(e0, e⊥)`, `κ~_s` is diagonal and nonnegative there, and for N = 2 the off-diagonal sign of `K̂_s` is that of `b_s = e0ᵀ w K_s w e⊥`, since `F0 > 0`. Hence for N = 2, any T, equal diameters: **if all `b_s` have the same sign or vanish, every entry in that basis has nonnegative coefficients and `R` lies on the positive axis.** If in addition the block is connected and every `K_s ≠ 0`, then `R = τ_f` by *The turn, T ≥ 2*. That covers one direction at equal diameters. Exchange-symmetric binaries, where all `b_s = 0`, are the separate decoupled case of *Exchange-symmetric binaries*.

The prediction was written first (`equal_diameter_cross_sign.py`), and both classes ran on the same `(x, η, z)` with the same descent:

| `b_1 b_2` | `K` | Pairs | `Lam < √3` | Smallest `Lam` | Ratio there |
|---|---|---|---|---|---|
| same sign | 761 | 458 | 0 | √3 + 0.009 | 1.0109 |
| opposite | 650 | 441 | 45 | 1.015 | 1.0024 |

For same sign, 24 random states (`equal_diameter_check.log`) have no negative coefficient to order 240 and `R/τ_f` in 0.9999–1.0000. For opposite sign, the fold behind `Lam < √3` is confirmed by coefficients with no tracking (`equal_diameter_fold_recheck.log`, order 2400, `R/τ_f` within 1e-4 of 1 at `Lam` = 1.015, 1.381, 1.631).

**Opposite signs can give `R < τ_f`, and a single sign flip removes it.** Descents on the ratio from the pair search stalled at 0.99989 (`equal_diameter_descent2.log`), a reading no coefficient check could resolve. Instead I followed the certified unequal-diameter counterexample from `σ_2 = 2.34` to 1, re-optimising `K` at each step (`counterexample_to_equal_diameter.log`). The prediction, written before running, was that the pair survives to equal diameters only if `b_1 b_2 < 0`. It survives, with `b = (−0.0015, +0.0371)`:

    σ = (1, 1),  x_2 = 0.0453,  η = 0.531,  z = (1.39, 41.2),
    K_1 = c_1 (1, r_1)^⊗2,  K_2 = c_2 (1, r_2)^⊗2,  c = (0.001852, 0.005404),  r = (0.3024, 5.672).

All entries of `K_t` are positive. With `K` scaled to largest entry 1: real turns at 211.809, 192.718 and 223.341, so `τ_f = 211.809`; `τ* = 196.225 + 1.878i`, `|τ*| = 196.234`; `R/τ_f = 0.9265`; `R/τ_inst` is about 1.3, since the winding of `det Z` first changes between 143.9 and 148.1. So `R ≥ τ_inst` is not contradicted.

| Check | Result | Log |
|---|---|---|
| Float, order 3000, every entry | 8 to 10 sign changes, spacing 328–330 to the end, against the pair's period 328.3; `R/|τ*| = 1.000001` | `equal_diameter_counterexample.log` |
| EXTERNAL mp, exact rational input, order 800, 50 and 80 digits, 16 components | radius 196.26–196.42, sign changes identical at both precisions, the late ones near 403 and 736, as in float; precision difference at most 6e-40 | `equal_diameter_counterexample_mp.log` |
| Flip both `b_s`, an exact symmetry | all numbers reproduced, ratio to 12 digits | `equal_diameter_control.log` |
| Flip `b_1` only, or `b_2` only, keeping `|b_s|` | one turn at 75.049, no pair found; no negative entry in the basis `(e0, e⊥)` to order 1200; `R/τ_f = 1.00000` | same |

That last row is the decisive one: two states whose only difference is the relative sign of `b_1, b_2`, and only the opposite-sign one fails. It is sensitive: 4 digits keep it, while `(c, r)` to 3 digits lose the pair (`equal_diameter_counterexample_rounded3.log`). Opposite signs do not always fail, as most opposite-sign states in the table above show no `Lam < √3`. So at equal diameters, N = 2: same sign is sufficient for coefficient positivity, and opposite sign is necessary for failure, not sufficient.

**Which opposite-sign states fail: tested by Codex, EXTERNAL, NOT Lean.** I proposed that failure sits in a window around the direction where the weak tail is orthogonal to the left Perron vector `u` of `κ~_w r~_w` at the pole of `h_w`, because then the forcing `u^T K̂_w u` vanishes, and that the window narrows as the weak strength grows. Handoffs 333, 334, `proof_notes/codex_equal_diameter_opposite_sign_test.md`, `results/codex_equal_diameter/`. On the certified strong tail, orthogonality is at `r_w = 0.16353`. Refuted or corrected:

| Claim | Result |
|---|---|
| Exact cancellation gives failure at finite strength | no: at `r_w = 0.16353` at original strength, no pair and settled signs |
| The window narrows as `c_w` grows | reversed on this slice: inside points span 0.074° at `c_w/4` (`r_w = .200–.202`) and 1.70° at full `c_w` (`.3024–.342`) |
| The window stays centred on orthogonality | no: it moves away as `c_w` grows, and the weak tail's own fold competes with the pole |

A second failing state, `c_w/4`, `r_w = .20`: `|τ*|/τ_f ≈ 0.996`, oscillation with half period about 83, signs agreeing at 40 and 70 digits to order 600. The far edge `r_w = .34` also has real continuations past `|τ*|`. Same-sign `r_w = 1.3` shows nothing. This is one slice, on a finite grid, with no phase boundary established. Orthogonality may still be a coordinate for `c_w → 0`, as `.3024, .20` move toward `.1635`, but two strengths do not show this. **So the opposite-sign class is not characterized.**

In the same log the smallest tool ratio on the path is 0.8926 at `σ_2 = 1.48`, with `Im τ*/Re τ*` of 4e-3. Those intermediate ratios had no coefficient check, so `0.9265` at equal diameters and the earlier 0.9615 are the only certified values.

**T = 1.** Now `U = I − p`, `r~ = zp`, `f~ = I − κ̂p` with `κ̂ = I − Ξ`, `θ~ = 2z p(I − p)`. Work in the eigenbasis of the symmetric `Ξ(z)`: `κ̂` is diagonal with entries in `(0, 2)`, since `‖Ξ(z)‖ < 1` at real `z > 0` by the maximum principle, as `Ξ → 0` at infinity. With `K0 = K̂|_{τ=1}/(2z)` and `h = f~⁻¹`,

    p = X + p²,   h = I + κ̂ p h,   X = τ h K0 hᵀ,   so   p = X + X² + 2X³ + 5X⁴ + …

If `K0` is entrywise nonnegative after a sign flip `D K0 D`, which conjugates the whole system since `κ̂` is diagonal, this is a polynomial positive system: by induction on the order in `τ`, all entries of `p`, `h`, `X` have nonnegative coefficients, and `R` lies on the positive axis.

*Bounds.* Along the ray, `X ⪰ 0` and is entrywise increasing, so its top eigenvalue increases. `p` commutes with `X` and has `spec p ⊂ [0, 1]`, so the eigenvalues of `X` are at most ¼. If the top eigenvalue of `p` exceeded ½ on an interval, the eigenvalue of `X` would have to stay at ¼, forcing an analytic eigenvalue branch of `p` to be constant at ½, which contradicts `p(0) = 0`. So `‖p‖ ≤ ½`, `‖κ̂p‖ ≤ (1 − ξ_min)/2 < 1`, and `‖h‖ ≤ 2/(1 + ξ_min)`, for any rank. By `|p_ij(τ)| ≤ p_ij(|τ|)`, these hold on the whole disk `|τ| < R`, so `U` and `f~` are invertible there, and `Y = zph`, tied linearly and invertibly to `G`, has the same radius as `p`.

*The singularity, when `K0` has a nonzero off-diagonal.* The nonzero unknowns are strongly connected. Let `ρ(τ)` be the Perron eigenvalue of the derivative of the positive map. If `ρ = 1` at some `τ*` with left Perron vector `l > 0`, then for `τ > τ*`, `y − y* = F(y, τ) − F(y*, τ*) ≥ DF*(y − y*) +` a strictly positive term, and multiplying by `l` gives a contradiction. So `ρ < 1` on `[0, R)`. The limit at `R` is finite, so the Jacobian is singular there. Finally `l·∂_τF > 0` from `h K0 hᵀ` and `l·D²F[v, v] > 0` from the `p²` term give a true square-root turn.

*When `K0` is diagonal in this basis.* The system is two scalar equations, as in *One tail of rank one* in structure, `p_12 ≡ 0`, and `R` is the smaller scalar fold. Here the Jacobian can be singular before `R`, in the `p_12` direction: at

    1 − p_1 − p_2 = κ̂_1 X_2/f_1 + κ̂_2 X_1/f_2.

This is a pitchfork, not a singularity of the series. **So `R` is discontinuous at zero coupling**: a small off-diagonal turns the pitchfork into a turn (`pitchfork_abstract.log`: `κ̂ = (1, 0)`, scalar folds 1.00109 and 1.00160, pitchfork 0.99378; at off-diagonal ratio 1e-4 the `p_12` coefficient ratio is already 0.99375). The analogue of this cusp is a plausible source of the narrow turns of the warning below; I have not checked that it accounts for all of them.

It occurs in physical states, by a small margin near a tie of modes (`pitchfork_physical.log`). It does not touch `R ≥ τ_inst`, since canonicity is already lost before it.

**So T = 1, N = 2 has `R = τ_f`, on paper**, for `K ⪰ 0`, `ρ_i > 0`, any rank, since a 2×2 symmetric matrix can always be sign flipped and its diagonal is nonnegative by PSD. The same proof covers T = 1 at any N where `K0` flips to nonnegative in the `Ξ` basis, block by block. This rests on the matrix form at T = 1, whose algebra is checked and not derived for all N, as in *One tail of rank one*. Evidence: 58975 abstract states (`t1_abstract_scan.log`, `R/τ_f ≥ 0.99999`, no sign change in the `Ξ` basis), with the abstract equation checked against physical folds (`t1_abstract_control.log`, 5e-8 and 6e-5; the larger is `real_fold`'s own error, as `first_fold` agrees to 8e-10). This does not by itself explain why the T = 1, rank 2 search found no pair at all, since `R = τ_f` allows pairs outside the disk.

**Lean status of this T = 1 result.** `claude_lean/T1PositiveSystem.lean` (e365933), outside the `MSAConvergence` library, standard three axioms: every solution of `p = X + p²`, `h = 1 + κ p h`, `X = τ h K hᵀ` with `p(0) = 0` has nonnegative coefficients for nonnegative `κ, K`; with `κ` diagonal and signs `d` making `K` nonnegative, `d_i d_j [τ^m] p_ij ≥ 0`; for N = 2, the same with one sign `s`, for every symmetric `K` with nonnegative diagonal; and the system implies the polynomial form. **This is the algebra only.** Not in Lean: that the physical MSA root solves this system, that `κ̂ = I − Ξ(z)` has nonnegative eigenvalues, which rests on `‖Ξ‖ ≤ 1` and needs a matrix maximum principle, and `R = τ_f`. The pure-fluid analogue of the first of these is a large part of Codex's 65 `PureFluid*` modules, about 16000 lines, and no matrix version exists.

**T = 1, N ≥ 3 with frustrated `K0` stays open.** Sign flips cannot remove `K0_12 K0_13 K0_23 < 0`, and `K0` is any PSD matrix there, since `K` is free. A general `O` could still meet the criterion in another basis only if it also keeps `κ̂` nonnegative, which I have not studied. Evidence:

| Search | States | Result |
|---|---|---|
| Random, N = 3, 4 (`t1_frustrated_scan.log`) | 19903 frustrated, 3552 unfrustrated | `R/τ_f ≥ 0.99997`; unfrustrated: no sign change; frustrated: latest change at order 467 |
| Near tie, physical `Ξ` (`t1_branch_points_physical.log`) | 775 frustrated, 392 unfrustrated | no `Lam < √3`, smallest 2.16 and 3.07 |
| Near tie, `ξ ∈ [−1, 1]` (`t1_branch_points_fixed.log`) | 855 frustrated, 345 unfrustrated | frustrated 5 hits with `Lam < √3`, resolved down to 1.47; unfrustrated none, smallest √3 + 0.010 |
| Descent, `ξ ∈ [0, 1]`, resolved pairs only (`t1_descent_gated.log`) | 1771 frustrated | 179 with `Lam < √3`, smallest 1.512 at ratio 1.00076; none inside |
| Descent, `ξ ∈ [−1, 1]`, resolved pairs only (same log) | 1768 frustrated | no `Lam < √3`, smallest 1.735; none inside |
| Descent over `K0` at `ξ` of actual hard-sphere states, from states with a pair, resolved pairs only (`t1_descent_physical.log`) | 361 sampled states, 15 descents, 12091 `K0`, 2251 pairs | no `Lam < √3`, smallest 1.918; none inside |

The state at 1.512 has `ξ = (.036, .402, .928)` with fold and coefficient radius agreeing, 0.994480 and 0.994489 (`t1_gated_recheck.log`). `ξ ∈ [0, 1]` covers the physical range up to a sliver (`−0.002` to `0.998` over `z`, N = 3, `t1_hits_recheck.log`), but these three values were not realized at one physical state. So frustrated T = 1 reaches `Lam < √3` in the abstract equation with some `ξ < −0.5`, and for `ξ ∈ [0, 1]` this is unconfirmed (see *A targeted attempt* below); no pair inside the fold was found. At physical `ξ` even `Lam < √3` was not reached, though only 15 descents had a start with a pair, so this is thin. `t1_scurve_search.log` tells nothing: its 2912 frustrated `K0` found no pair, since it started the solve only from the turn, and so its objective stayed on a plateau. I do not claim `R = τ_f` here, nor its failure.

**A targeted attempt on frustrated T = 1, N = 3 (2026-11-02).** It did not settle the question. The system is polynomial, `(I − κ̂p)p(I − p)(I − pκ̂) = τK0`, so its expansion is exact (`t1_cancellation_symbolic.log`). With `x, u, w = p_12, p_13, p_23` and eliminating `u, w`:

    C_eff x = β + Q x² + A x³,   β = τ b_12 − E τ² b_13 b_23/(C_13 C_23),   Q = −3 E E_13 E_23 τ² b_13 b_23/(C_13 C_23)²,

where `E, E_13, E_23` are the coefficients of `uw` in `F_12`, of `xw` in `F_13`, of `xu` in `F_23`; they tend to negative values as `p → 0`, and I did not check their sign over the whole range. If they are negative, `a < 0` needs `β b_13 b_23 < 0`, so a state at `C_eff = 0` with small `x` is frustrated. In the normal form, `f = u² − u + B/u`, `B = βA²/Q³`, a pair is inside the fold for `B < B_c ≈ 0.09441`, where both critical values have real part `−1/12`. This led me to predict `R < τ_f` near the cancellation `β = 0`. **The prediction was not confirmed:**

| Test | Result | Log |
|---|---|---|
| `b_12` scanned through the cancellation, coefficients only, order 2500, 30 states with about 28 values each | no late sign oscillation in any state; `R/first_fold ≥ 0.99974`; first turn moves by at most 0.0021 between neighbours, no jump to the mode folds | `t1_b12_coefficient_scan.log` |
| Inverse design, `K0 = F(p)`, seeded on null vectors along `p_12`, strict sheet test | 829 pitchforks, 109 on the branch, 19 pairs with no `Im` cut below 2e-5, none inside; smallest ratio 1.00009, `Lam ≈ √3` | `t1_inverse_design_pitchfork.log` |
| Same seeding, opposite sign of `x` | 2 of 827 on the branch, against 109 of 828 | same |
| Shallow hit, ratio 0.999976 from the older test | off the sheet: the ray passes it, distance fixed at 0.0343 to `1 − s = 1e-8`; the real turn scales at 0.314, and a real root at 0.9997 also fails, as controls | `t1_strict_sheet.log` |
| Continuation from that hit | leaves the sheet: at ratio 0.997 the coefficient radius is the turn, 1.000026 | `t1_descend_recheck.log` |

Three caveats. The inverse-design gate of 2e-5 cannot see the scale `Q²/A`, about 1e-7, at which the closed form places a pair for small `u, w`, and `t1_tiny_pair.log` did not resolve it, as that script did not check that its design points are on the branch. So a pair inside by less than about 1e-5 is not excluded. A coefficient scan on a grid of `b_12` would miss a window much narrower than its spacing, though a jump of the first turn across it would still show, and none did. `t1_b12_coefficient_scan.log` used `first_fold`, which can overstep a narrow turn. `t1_cancellation_scan.log` and `t1_scurve_search.log` found no pairs even in their controls and say nothing.

**Descent on `Lam`.** The normal form itself allows a pair inside: `normal_form_sheet.log`, the cubic at 50 digits with `a = −1`, keeps the pair on the principal sheet at every `B` from 3 down to 0.001, and `Lam` crosses 0 at `B_c`. So no sheet obstruction exists at the level of the normal form, and what stops the abstract system lies outside it. Objective matters: minimising the ratio only shrinks the scale at fixed `B` (`t1_descend_strict.log`). Minimising `Lam` under a strict sheet constraint gives 1.47 to 1.36 in 15 minutes, at some `ξ < −0.5` (`t1_descend_strict_lam.log`). As a per-step constraint the test then flips at step 1e-9 on an essentially unchanged state (`t1_gradient_lam.log`), so it is noisy at that margin. Recording it without enforcing it (`t1_gradient_lam2.log`), `Lam` crosses 0 with `Im τ*` collapsing to 1e-5, and every recorded state from `Lam ≈ 0.93` down fails the test. Taken together: on the sheet, I have nothing below about 1.36 in the abstract equation and nothing below 1.918 at physical `ξ`, the latter from only 15 descents.

A structural difference from T = 2, which I have not made into a proof: the certified failures at T = 2 sit near a pole of `h_w`, whereas at T = 1 `‖κ̂p‖ < 1` holds on the ray, so `h` has no pole. **Status: frustrated T = 1, N ≥ 3 is neither proved nor refuted. No resolved pair inside the fold has been found on the principal sheet. Conjecture, on this evidence: `R = τ_f` at T = 1 for every N.**

The older ray test is not reliable at a pair's own scale: its radii were 1e-2 to 1e-4. `t1_strict_recheck_lam.log` rechecks with radii scaled to `|Im τ*|`: the five `Lam < √3` hits of `t1_branch_points_fixed.log` are on the sheet, ratios 0.319 and 0.317 per decade against 0.316, all with some `ξ < −0.5`, outside the physical range, and the one reading −49 has a real turn before it, as in the warning below. The `ξ ∈ [0, 1]` reading 1.512 could not be decided, the march stopping at `1 − s = 8e-8`, so `t1_descent_gated.log` is unconfirmed for that class.

**Warning: real turns narrower than any step.** Near a tie between modes, the real branch can have a turn of width far below any continuation step, and arclength, stepping in `τ` with a bound on the change, or a test of the corrector against the tangent predictor all step over it onto another sheet. That overstates `τ_f` and understates `Lam`, and in the extreme reads a pair as inside the fold. All "inside" hits I checked at T = 1 were this: `R/|τ*| = 0.99936` from 16000 coefficients, with no sign change past order 2169 although the pair's period is 8557, and a real root solved directly at 0.93631 (`t1_candidate_check.log`, `t1_candidate_check2.log`), then 0.90906 and 0.93716 (`t1_inside_recheck.log`). Corrected, those pairs have `Lam` = 1.74, 1.72, 1.74. This came to light because an unfrustrated control, where a pair inside the fold is forbidden, showed one. So `t1_near_tie_scan.log`, `t1_near_tie_scan_fixed.log`, `t1_branch_points.log` and `t1_descent.log` overstate hits, and a tool-found ratio just below 1 with small `Im τ*` means nothing without a coefficient radius. The certified counterexample of *A binary with K_t PSD where R < τ_f* is unaffected: its radius comes from coefficients in exact-rational mp, with sign changes at the pair's period. A second-turn state from the arclength searches was never counted without coefficients.

## Mixture amplitude escape: numerical probe (2026-10-31)

**Superseded on the real axis (2026-11-02).** Codex's `TracerActiveGUniform.actual_full_mixture_amplitude_properness` and `no_finite_mixture_amplitude_escape` (commit a9f8fd3, standard-three axioms; for the paper use the `MixtureEndpointNoEscape` wrappers `..._from_data`, c726f7e, which need no auxiliary radius) bound the full original `(D, G)` over bounded symmetric `K` at every canonical reciprocal root, for finite positive rates and diameters and nonnegative densities, zero-density tracers included, with `vacMix ≠ 0`. So finite-coupling amplitude escape along a canonical real prefix is excluded in Lean, and the probe below is history. This says nothing about Taylor convergence or radius equality: the binary in *A binary with K_t PSD where R < τ_f* is untouched by it, and `R ≥ τ_inst` stays open. On top of it, `MixtureEndpointNoEscape.maximal_finite_mixture_endpoint_unique_physical_limit` (commit 84e0d56) gives, at every finite endpoint of a maximal physical branch, a unique full left limit along the selected path: an original MSA root in canonical closure, outside canonicity, with a real Fourier-factor zero. So `τ_inst` in this note is, when finite, a real Fourier zero of that limit. It does not assert uniqueness of all roots there, that the endpoint is finite, or continuation through it, and it gives no Taylor-radius lower bound.


`results/two_tail/mixture_escape_probe.log` traces the HS-seeded branch of 12 binary mixtures
up to λ = 30. They cover:
* equal and unequal diameters (1:3, 1:5);
* cross attraction and repulsion, K₁₂ ∈ [−3, 2];
* a repulsive self-tail;
* tracers (x₂ = 1e-4);
* rank-one strengths;
* a mixed-sign two-tail case.

In every case the first det F(0) zero (canonicity loss) comes before the trace end, and the
amplitude norm stays moderate (at most 34). No branch ends by amplitude divergence. This is float
evidence that the open escape alternative does not occur in these families; it is not a proof.
The scalar proof breaks for matrices only at a rank-deficient normalised limit, and these probes
do not reach that regime.

### Random counterexample search (2026-10-31)

`scripts/two_tail/mixture_escape_search.py` (seeds 2 and 3, 240 states each) samples random
binaries and ternaries. The sampled ranges:
* diameter ratios 1–5;
* Dirichlet compositions and tracers (x = 1e-3);
* η ∈ [0.05, 0.6], well below η → 1;
* 1–2 tails, z ∈ [0.5, 10];
* four sign patterns: random, all repulsive, attractive self with repulsive cross, and the
  reverse.

Each HS branch is traced to λ = 40. A counterexample would be a trace that stops at finite λ
before any det F(0) sign change.

Results:
* **No candidates in 480 states.** 282 reach λ = 40; 198 stop only after the spinodal.
* The largest amplitudes at λ = 40 grow sub-linearly, with log-log slope 0.55–0.94, decreasing
  in λ (`mixture_escape_growth.log`).

Float evidence, NOT a proof; logs `results/two_tail/mixture_escape_search_seed{2,3}.log`.

**Restricted class.** For equal diameters with mean-field-symmetric strengths (each Σ_j K_t,ij ρ_j
independent of i), the symmetrised Baxter factor is diagonal in the (ρ^{1/2}, ⊥) basis to 5e-16.
Its density entry equals the one-species factor to 1.3e-15; a non-symmetric control fails at 3e-2
(`mode_decoupling_check.log`). Per-mode normalisation then removes the rank-deficient obstruction.
That gives a provable restricted escape-exclusion target, not yet in Lean.

## Open

* **Re-entrance** (user, 2026-10-26: follow-up study). When does a canonical stable state reappear
  after a closed instability interval, and does the series reach it?
* The opposite sign order (short-range attraction, long-range repulsion), where `k ≠ 0`
  instabilities are expected; §8c's `k ≠ 0` route is untested.
* The `η → η_max` asymptotics of `f*`.
* Certification of boundary points beyond the control (candidates in *Boundary mechanisms*).
* A proof of the observed monotonicity in `η`, which would reduce the condition to `η_max` alone.
