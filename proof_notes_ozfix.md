# Proof Notes: Group OZFIX — `h_explicit`'s Closed-Form Assembly into `OzFixedPt`

Detailed proof records for Group OZFIX: assembling the residue-series construction `h_explicit`
(Group POLE's pole/residue machinery, summed over the pole family) into a genuine proof that it
satisfies `OzFixedPt` on the exterior domain `[σ,∞)`, so that `oz_fixed_pt_unique`'s uniqueness
clause identifies `oz_h = h_explicit` there. Split out of Group BAXTER (2026-07-15, by topic, when
that group grew to 15+ tasks spanning several unrelated areas) — task IDs `OZFIX.1`–`8` were
originally combined under `BAXTER.13`/`BAXTER.15` (`BAXTER.13` covered the done `B.0`–`B.4`
sub-steps, `BAXTER.15` the remaining `B.3`(outer)/`B.5`/`B.6`/`B.7`); both are retired, replaced by
the eight topic-scoped tasks below — see the mapping table at the top of `proof_notes_baxter.md`.
Depends on Group BAXTER (`BAXTER.1`–`3`) and Group POLE (`proof_notes_pole.md`, especially
`POLE.3`'s pole family and `POLE.4`'s `h_explicit`/`residue_term` definitions). See `todo_lean.md`
for task status summary.

Assembly-style, following `OzFixedPtDilute.lean`'s existing three-lemma pattern
(`isFixedPt`/`continuousOn`/`bounded`, `proof_notes_hard_sphere.md` Task OZ.10-dilute) as a
template. Scoped (2026-07-15 planning pass) to the **exterior fixed-point result** first
(`OzFixedPt` on the spliced `h_explicit`/`-1` function, `ContinuousOn`, bounded, then
`oz_fixed_pt_unique`); retiring the literal `oz_core_closure` axiom (its `r<σ` convolution
identity, needing a *second*, differently-shaped computation since `radial3d_conv` samples both
branches of `oz_h`) is a separate follow-on, **Phase C**, after this group lands.

Chosen strategy: **termwise**, directly via `oz_operator`'s own definition (`oz_forcing +
oz_linear_op`), *not* through `radial3d_conv`/Fourier inversion — this avoids needing any general
residue theorem or Jordan's-lemma-style contour-closing machinery (confirmed absent from this
Mathlib snapshot).

**✅ 2026-07-15 — upstream Group POLE blocker FIXED.** `G_baxter`'s zero condition
(`Qhat_pole_iff_G_baxter_zero`) previously used a double-counted `ρ`
(`1-ρ·Qhat_complex(k)=0`); found via three independent numerical checks and now corrected to the
physically-right `1-Qhat_complex(k)=0` (no extra `ρ`) throughout `BaxterPoles.lean`,
`BaxterResidue.lean`, and this file's own dependencies (`OzFixedPtHExplicit.lean`,
`HExplicitRegularity.lean`, `OzFixedPtHExplicitFinal.lean` — only needed the `hrho : rho ≠ 0 →
0 < rho` sign-strengthening propagated through, no other change). Full details, before/after pole
values, and the numerical re-confirmation are in `proof_notes_pole.md` `POLE.3`. Full project
`lake build` is green; `h_explicit(2.0)` rebuilt on the corrected pole family now converges to the
known ground-truth value `0.005663` (was previously built on the wrong pole family, so its values
were wrong even though every derivation *from* `G_baxter`'s definition was formally sound).

**✅ The fix ALSO resolves the aggregate collapse identity (re-scoped against the fixed code).**
`OZFIX.9`'s scoping was re-run against the now-corrected `G_baxter` and shows the aggregate identity
`oz_forcing+oz_linear_op[h_explicit]=h_explicit` **now holds** (anchor: `h_explicit(2.0)=0.005688` =
ground truth `0.005663`):
- **`r ≥ 2σ` (where `oz_forcing = 0`): holds EXACTLY, per-pole** — `diff = -0.000000` at every N (`r=2.0,
  3.0`). So `OZFIX.6`'s *original* per-pole/termwise route works in this region; the earlier
  "per-pole collapse is false (−2.72)" was a symptom of the wrong pole family, not an inherent obstruction.
- **`σ ≤ r < 2σ` (where `oz_forcing ≠ 0`): holds, but converges slowly** (`r=1.5`: diff
  `0.0385→0.0094` as poles `N: 10→45`, → 0 like `~1/N`, the `n^{-2}` tail). Here the collapse is genuinely
  *not* per-pole — `oz_forcing` supplies the difference — so a Route-A-style argument is needed for this
  sub-region. **Correction:** an earlier version of this note (and one in `proof_notes_pole.md`) claimed
  the aggregate "still fails ~50% even with the right poles"; that was a **truncation artifact** (`N=11`
  poles at the slow-converging `r=1.5`), now retracted.

**Consequence.** `OZFIX.9` is **unblocked** — `h_explicit` is now correct and the aggregate identity is
confirmed. What remains is a genuine *proof route* for `hcollapse` (still research-scale): the `r≥2σ`
per-pole part is now tractable; the `σ≤r<2σ` part needs the Route-A termwise argument (see `OZFIX.9`).

**✅ 2026-07-16 — the `r ≥ 2σ` half of `hcollapse` is PROVED (`OZFIX.11`, axiom-clean,
`OzCollapseTwoSigma.lean`):** the per-pole collapse factor is `ρ·Ĉ(k_n) = 1` at every `G_baxter`
zero (Wiener–Hopf factorization vanishing — `OZFIX.2`'s payoff), and `OZFIX.8`'s `hcollapse`
hypothesis is correspondingly weakened to `σ ≤ r < 2σ` only
(`oz_h_eq_spliced_h_explicit_of_inner_collapse`). Remaining: `OZFIX.12` (`σ ≤ r < 2σ`,
smoothed-kernel contour argument, scoped) + `OZFIX.13` (`σ`-endpoint via continuity + wiring).
The MA.2-pointwise inversion route was found to rest on a **false identity** and is retired —
see `OZFIX.10`'s 2026-07-16 update.

## Group OZFIX — `h_explicit` Satisfies `OzFixedPt`; Invoke `oz_fixed_pt_unique`

### Task OZFIX.1 — Strategy scoping (`B.0`) + zeroth-moment inner integral (`B.1`/`B.2`)

**`B.0` (pole-family completeness) — ✓ resolved: not needed, no new Lean.** Re-derived carefully
during implementation: the termwise real-space verification (`OZFIX.6`) only needs each `k_n` in
the *given* family to be a genuine `G_baxter` zero — it never needs the family to be the *entire*
zero set. `oz_linear_op` only ever samples `h_explicit` on `[σ,∞)`, so `OzFixedPt`'s exterior
clause reduces to a self-contained identity about the *specific* constructed `h_explicit`.
Completeness would only matter for a Fourier-inversion/residue-theorem argument, which this
project deliberately avoids. The originally-planned `hcomplete` hypothesis is dropped.

**`B.1` (numerical pre-check) — ✓ done.** `baxter13_moment_check.py` (scratch, not committed):
verified the closed-form moment integral against direct quadrature (max error ~1.66e-7, 20
random complex-`k` trials) and confirmed the "must bound using the closed form, not a naive
worst-case pre-integration bound" ordering subtlety is real (per-pole magnitude decays much
faster than a crude worst-case estimate — ratio ~7.7e-5 at n=5 down to ~1.9e-8 at n=80). A
slower, full nested-double-integral end-to-end check (`baxter13_b1_check.py`) timed out (60-pole
Newton refinement re-run inside adaptive quadrature); not needed once the targeted check landed,
since the underlying identity was already validated in a prior session at the approximate-pole
level.

**`B.2` (single-exponential inner moment integral) — ✓ done, genuinely simpler than planned.**
`moment0_formula` (`BaxterResidue.lean`): closed form for `∫ s in lo..hi, exp(I·k·s) ds` on any
interval, via `HasDerivAt`+FTC (mirrors `zeta0_formula`'s technique, `BaxterZeros.lean`, `+I`
sign convention). **Key realization this pass:** `oz_linear_op`'s inner integral is `∫ s·h(s)`,
but `s·h_explicit(s) = s·(1/(2πs))·Re[∑ h_explicit_term(n)(s)] = (1/(2π))·Re[∑
h_explicit_term(n)(s)]` — the `s` cancels against `h_explicit`'s own `1/(2πs)` prefactor, and
since `residue_term`'s only `s`-dependence is the single factor `exp(I·k_n·s)` (everything else
in `A(k_n) := k_n^7·Chat_complex(k_n)/(G_baxter(-k_n)·G_baxter_deriv(k_n))` is `s`-independent),
the needed integral is the **zeroth** moment, not the first moment originally assumed in the
plan (which would have needed a genuinely more involved antiderivative). A further, welcome
simplification: unlike `OZExteriorBridge.lean`'s `inner_integral_bridge`, **no case split on
`r-t ≷ σ` is needed at this step** — `moment0_formula`'s closed form is valid on `[max(r-t,σ),
r+t]` directly, for either value of the max. A case split only re-enters later (`OZFIX.6`),
matching `max(r-t,σ)` against `oz_forcing`'s own `if r < σ+t` structure.

**Status:** ✓ **DONE.** All in `BaxterResidue.lean`, no `sorry`/new axiom.

---

### Task OZFIX.2 — Complex-`k` Wiener–Hopf bridge (`OZFIX.6`'s key prerequisite)

**✓ DONE**, new file `LeanCode/HardSphere/BaxterWienerHopfComplex.lean` (no `sorry`/`axiom`,
`lake build` clean). Checked this pass: `residue_term`'s numerator uses `Chat_complex`
(`RadialFourierCHSComplex.lean`, built from `Chat_J`), while `G_baxter`'s zero condition
(`G_baxter(k)=0 ⟺ 1-ρ·Qhat_complex(k)=0` for `k≠0`, via `baxter_cube_mul_F_eq_G`,
`BaxterPoles.lean`) is stated via the *different* function `Qhat_complex` (`BaxterZeros.lean`,
built from `q0_poly`); the only existing bridge, `baxter_wiener_hopf_factorization`
(`BaxterWienerHopf.lean`), was **real-`k`-only**. Rather than re-deriving the real-axis proof's
algebra directly for complex `k` (which would essentially duplicate `BaxterWienerHopf.lean`'s
hard `field_simp`/Pythagorean-identity closing in a harder setting), this was closed via
**analytic continuation**: both sides of the target identity are holomorphic on the preconnected
set `ℂ\{0}` (`isConnected_compl_singleton_of_one_lt_rank`, new-to-this-codebase technique,
mirrored from Mathlib's `DirichletContinuation.lean`), and they agree on the reals — the
one-variable **identity theorem** (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) then
forces equality everywhere on `ℂ\{0}`. Concretely:

- `q0_poly_continuous`/`phi1_real_continuous`/`phi2_real_continuous` (`BaxterRealSpace.lean`,
  via `Continuous.if_le` — the two branches of each piecewise def agree at the junction `r=σ`).
- `Qhat_complex_eq_cos_sub_I_sin`: real/imaginary decomposition of `Qhat_complex` at real `k`
  (splits the `ℂ`-valued interval integral into `∫cos - I·∫sin` via
  `intervalIntegral.integral_sub`/`integral_ofReal`/`integral_const_mul` and `Complex.exp_mul_I`).
- `Qhat_complex_conj_eq_neg`: `conj(Qhat(k)) = Qhat(-k)` at real `k`, via commuting conjugation
  (`Complex.conjCLE`, an `ℝ`-linear `ContinuousLinearEquiv`) past the interval integral
  (`ContinuousLinearMap.intervalIntegral_comp_comm`) + `Complex.exp_conj` pointwise.
- `Chat_complex_eq_radial_fourier`: `Chat_complex(k) = radial_fourier(c_HS)(k)` at real `k` — a
  domain reduction (`Ioi 0 → [0,σ]`, mirroring `OZExteriorBridge.lean`'s
  `radial3d_conv_cHS_eq_Ioo`) plus the same `exp(±ikr)→sin(kr)` conversion technique.
- `baxter_wiener_hopf_complex_real`: combines the three above with
  `baxter_wiener_hopf_factorization` to get `(1-Qhat(k))(1-Qhat(-k)) = 1-ρ·Chat_complex(k)` at
  real `k≠0`, as a genuine `ℂ`-valued identity (the `(1-A)²+B²` sum-of-squares becomes a product
  via `conj`-symmetry, closed by `Complex.I_sq`+`ring`).
- **`baxter_wiener_hopf_complex`**: the complex-`k` extension — `Qhat_complex_entire` (already
  unconditionally entire) and `Chat_complex_differentiableAt` (`k≠0`) give `AnalyticOnNhd` via
  `DifferentiableOn.analyticOnNhd`; a real sequence `1+1/(n+1) → 1` (`≠1`, `≠0`) built via
  `tendsto_one_div_add_atTop_nhds_zero_nat` supplies the `∃ᶠ z in 𝓝[≠] 1, f z = g z` witness.
- **Result**: `∀ {eta sigma rho k}, 0<σ → η<1 → η=πρσ³/6 → k≠0 → (1-Qhat(k))(1-Qhat(-k)) =
  1-ρ·Chat_complex(k)` — fully unconditional (no new axiom, no numerical-only claim), the
  missing algebraic link that lets `OZFIX.6`'s termwise collapse actually use `G_baxter(k_n)=0` to
  control `Chat_complex(k_n)`.

**Status:** ✓ **DONE**, no `sorry`/new axiom.

---

### Task OZFIX.3 — Sum/integral interchange machinery (`B.3`–`B.4` core)

**`B.3`–`B.4` strategy switched (more efficient route found): antiderivative + `hasDerivAt_tsum`
instead of raw integral interchange.** Rather than swapping `∑'` and `∫` directly via
`MeasureTheory.hasSum_integral_of_dominated_convergence` (the original plan), Mathlib's
`hasDerivAt_tsum_of_isPreconnected` (`Analysis/Calculus/SmoothSeries.lean`, a Weierstrass-M-test
differentiation-under-the-sum theorem) lets `h_explicit`'s own derivative be obtained as a
termwise sum directly — then this project's usual `HasDerivAt`+FTC pattern
(`integral_eq_sub_of_hasDerivAt`) applies to the *whole series at once*, never needing a
separate integral-interchange lemma. `BaxterResidue.lean`:

- `residue_term_hasDerivAt {k≠0}(r) : HasDerivAt (fun r => residue_term(r)(k)/(I·k))
  (residue_term(r)(k)) r` — `residue_term(·)(k)/(I·k)` is its own antiderivative (dividing by
  `I·k` cancels the factor picked up differentiating `exp(I·k·r)`), mirroring `moment0_formula`'s
  internal antiderivative fact but built as a **standalone** reusable lemma this time.
- `h_explicit_term_hasDerivAt {k≠0}(r)`: pole+mirror pairing of the above, giving an explicit
  antiderivative of `h_explicit_term`.
- `residue_term_norm_le_of_le {Im(k)≥0}{r1≤r} : ‖residue_term(r)(k)‖ ≤ ‖residue_term(r1)(k)‖` —
  ✓ **done**. `‖exp(ikr)‖=exp(-r·Im(k))` is non-increasing in `r` for `Im(k)≥0`, so the value at
  any base point `r1` dominates for all `r≥r1`.
- `h_explicit_term_norm_bound_uniform` — ✓ **done**. Extends `h_explicit_term_norm_bound` (only
  stated at one `r`) to hold for *every* `y≥r1` with the *same* bound value (evaluated at `r1`),
  via the monotonicity lemma above plus the triangle inequality — the `y`-independent
  (only-`n`-dependent) summable bound `hasDerivAt_tsum_of_isPreconnected` needs on
  `Set.Ioi r1`.
- **`h_explicit_series_hasDerivAt` — ✓ DONE (the full `B.3`–`B.4` payoff).** `Hterm` (the
  pole+mirror antiderivative, packaged as a function of `(n,r)`) plus a single large theorem
  `h_explicit_series_hasDerivAt {r0<r}{concrete pole family} : HasDerivAt (fun z => ∑'n,
  Hterm(n)(z)) (∑'n, h_explicit_term(n)(r)) r`. Built entirely from pieces above: the uniform
  bound `u` (Summable, `n`-only-dependent, valid for **every** `n` — not just cofinitely many,
  via an explicit `summable_of_ne_finset_zero` finite correction on `n<N`, since
  `hasDerivAt_tsum_of_isPreconnected`'s hypothesis genuinely needs it for all `n`, unlike
  `h_explicit_summable_of_pole_family`'s `Summable.of_norm_bounded_eventually`-based proof which
  only needed it cofinitely); the antiderivative series' summability *at the actual target `r`*
  (not at the threshold `r0`, since `hasDerivAt_tsum_of_isPreconnected`'s base point must lie in
  the *open* set `t:=Set.Ioi r0`, forcing `r0<r` strictly) via one more monotonicity step
  bringing the bound at `r` down to the bound at `r0`; and `h_explicit_term_hasDerivAt`
  supplying the pointwise derivative. `set_option maxHeartbeats 4000000` (documented, matching
  `residue_term_norm_bound`'s precedent). No `sorry`/new axiom.

**`B.4` (sum/integral interchange) — ✓ DONE**, folded into the machinery above via the
`hasDerivAt_tsum_of_isPreconnected` route (never needed as a separate raw interchange step).

**`h_explicit_series_integral` — ✓ DONE.** Two-sided FTC (`integral_eq_sub_of_hasDerivAt`)
applied to `h_explicit_series_hasDerivAt`: `∫s in lo..hi,∑'h_explicit_term = ∑'Hterm(hi)-
∑'Hterm(lo)` for `lo>r0>σ` — the closed-form inner `s`-integral `oz_linear_op` needs, valid
whenever the lower endpoint is strictly past `σ`.

**`s_mul_h_explicit_integral` — ✓ DONE.** The actual closed-form value of `oz_linear_op`'s inner
integral: `∫s in lo..hi, s*h_explicit(s) = (1/(2π))*(∑'Hterm(hi)-∑'Hterm(lo)).re`, combining
`h_explicit_series_integral` with `intervalIntegral_re` (commuting `Re` past the interval
integral — needed a `show`/`change` bridge since `.re` notation and `RCLike.re` are defeq but not
syntactically identical for `rw`), for `lo>r0>σ`.

**Status:** ✓ **DONE.** All in `BaxterResidue.lean`, no `sorry`/new axiom (one
`set_option maxHeartbeats` bump, a performance not correctness issue).

---

### Task OZFIX.4 — The `σ`-boundary case

`oz_linear_op`'s inner integral has lower endpoint `max(r-t,σ)`, which equals `σ` exactly
whenever `r≤σ+t` — but `h_explicit_term`'s own series is only known summable for `r>σ` strictly
(the genuine PY hard-sphere contact discontinuity), so `OZFIX.3`'s `h_explicit_series_integral`
two-sided FTC (needing `HasDerivAt` at *every* point of `[lo,hi]`) cannot be applied when `lo=σ`.
Two genuine discoveries:

- **`residue_term_norm_bound`'s `hr:σ<r` hypothesis was unused** in its own proof (confirmed via
  grep) — weakened to `hr:0<r` (backward-compatible, 3 call sites updated). This matters because
  `Hterm` (the antiderivative) decays *one power of `‖k‖` better* than `h_explicit_term` (the
  extra `1/(I·k_n)` factor), so `Hterm`'s own series **is** summable already at `r=σ` (effective
  exponent `-2`, vs. `h_explicit_term`'s `-1`) — enabling `Hterm_uniform_summable_bound_of_pole_family`
  and continuity of `∑'Hterm` down to the *closed* endpoint `σ` (`continuousOn_tsum`). Went
  through three rewrite iterations to correctly track a consistent `corrOverK(n) :=
  (‖residue_term(σ)(k)‖+‖residue_term(σ)(-conj k)‖)/‖k‖` intermediate (an earlier attempt
  conflated `‖Hterm(σ)‖` with this quantity, which are related only by `≤`, not `=` — a genuine
  logic bug, fixed by threading `corrOverK` consistently through `hgN`/`hu_corr`/the final
  `hstep`).
- **The `hint : IntervalIntegrable` obligation for `h_explicit_term`'s own sum near `σ` is a
  genuine open analytic gap, not Lean bookkeeping.** Checked directly: even the worst-case
  (triangle-inequality) magnitude bound on the sum fails to be integrable near `σ` (its own
  integral diverges like `∑ 1/(n·ln n)`), so closing it needs real cancellation/oscillation
  structure in the residue sum. Investigated whether `g0_HS_contact_value`
  (`JumpAsymptotic.lean`, Group CONTACT) could supply this directly — its proof
  (`g0_HS_contact_value_of_oz_h_regularity`) turns out to route through a sophisticated
  Fourier–Tauberian "jump asymptotic" argument (`CONTACT.3`/`CONTACT.4`) specific to the *opaque,
  already-identified* `oz_h`, identified with a separately-known closed form via the Fourier-space
  OZ equation — adapting it to `h_explicit` directly would need an independent derivation of
  `h_explicit`'s own large-`k` Fourier asymptotic, a genuinely separate undertaking, not a quick
  reuse. **Resolution:** `h_explicit_series_integral_from_sigma` takes `hint` as an explicit
  hypothesis (matching `hstep`/`oz_h_exterior_regularity`'s established pattern for hard,
  currently-open analytic gaps), with the finding above recorded in its doc-comment.

**`h_explicit_series_integral_from_sigma` — ✓ DONE, conditionally.** One-sided FTC
(`integral_eq_sub_of_hasDerivAt_of_le`, only needs continuity on the closed interval and
differentiability on the open interior) handling `lo=σ` exactly, conditional on the explicit
`hint` hypothesis above. Both this and the (unconditional) `h_explicit_series_integral`
(`OZFIX.3`) are done, no `sorry`.

**Status:** ✓ **DONE** (conditional on `hint`). All in `BaxterResidue.lean`, no `sorry`/new axiom.

---

### Task OZFIX.5 — Outer `t`-integral assembly (`B.3` proper)

**✓ DONE**, new file `LeanCode/HardSphere/OzFixedPtHExplicit.lean` (no `sorry`/`axiom`, `lake
build` clean, `#print axioms` confirms only `[propext, Classical.choice, Quot.sound]`).

Wraps `OZFIX.3`'s `s_mul_h_explicit_integral` and a new `_from_sigma` counterpart of it
(`s_mul_h_explicit_integral_from_sigma`, landed in `BaxterResidue.lean` right after
`s_mul_h_explicit_integral` — the direct real-valued analogue of `OZFIX.4`'s
`h_explicit_series_integral_from_sigma`, same `Re`/integral-commutation technique) in
`oz_linear_op`'s outer `t`-integral, with the genuine case-split on `r-t ≷ σ` (i.e. whether
`max(r-t,σ)=σ` or `=r-t`) mirroring `OZExteriorBridge.lean`'s `inner_integral_bridge`/
`outer_integrand_bridge` pattern (`max_eq_right`/`max_eq_left`), applied to the closed-form sum
rather than a raw integral.

**Key correction found mid-implementation:** the naive first attempt tried to make `oz_forcing`'s
indicator term *cancel* against the closed-form inner integral (mirroring how the general
`inner_integral_bridge` folds the core's `h≡-1` contribution into a full `radial3d_conv`-style
shell integral over `[|r-t|,r+t]`). This is wrong for `h_explicit`: `h_explicit` is only ever
sampled on `s≥σ` (`oz_linear_op`'s own domain restriction), so there is nothing for the forcing
term to cancel against — it must stay as a genuinely separate additive piece throughout. Caught
by a failed `linarith`/leftover-goal check in the scratch test before landing, then fixed by
correcting the target statement (forcing term unchanged on both sides; only the *raw inner
integral* gets replaced by its `Hterm` closed form).

**Landed theorems** (all in `OzFixedPtHExplicit.lean`, plus the one addition to
`BaxterResidue.lean`):
- `s_mul_h_explicit_integral_from_sigma` (`BaxterResidue.lean`) — `∫s in σ..hi, s·h_explicit(s) =
  (1/2π)·Re[Hterm(hi)−Hterm(σ)]`, conditional on the `OZFIX.4` `hint` hypothesis.
- `inner_h_explicit_integral_bridge` — the case-split closed form for `oz_linear_op`'s raw inner
  integral `∫s in max(r-t,σ)..(r+t), s·h_explicit(s)`, uniform across both cases:
  `(1/2π)·Re[Hterm(r+t)−Hterm(max(r-t,σ))]`. The boundary sub-case (`max(r-t,σ)=σ`, i.e.
  `r≤σ+t`) needs `hint` for the *specific* interval `[σ,r+t]`; carried as an implication
  hypothesis (`r≤σ+t → IntervalIntegrable ...`) so the non-boundary case doesn't need to
  discharge it.
- `outer_h_explicit_integrand_bridge` — the `Set.EqOn (Icc 0 σ)` pointwise wrapper (peels `t=0`
  and `t=σ` via `simp`, the latter closing via the registered `@[simp]` lemma `c_HS_contact :
  c_HS eta sigma sigma = 0`), needed for `intervalIntegral.integral_congr`.
- **`oz_forcing_add_linear_op_h_explicit_eq_outer_integral`** — the main result:
  `oz_forcing(r) + oz_linear_op[h_explicit](r) = (2πρ/r)·∫t in 0..σ, [forcing-indicator-piece +
  t·c_HS(t)·(1/2π)·Re(Hterm(r+t)−Hterm(max(r-t,σ)))] dt`, i.e. the raw inner `∫s` integral is
  eliminated entirely — only the outer `t`-integral remains. Same `hcombine`/`hcongr` assembly
  technique as `OZExteriorBridge.lean`'s `oz_forcing_add_linear_op_eq_radial3d_conv` (two routine
  `IntervalIntegrable` side-conditions `hint1`/`hint2` carried explicitly, same spirit as that
  theorem's own `hint1`/`hint2`), but targets the `h_explicit`-specific closed form instead of
  `radial3d_conv` — matching Group OZFIX's chosen termwise strategy.

**What's left for `OZFIX.6`:** the outer `t`-integral above still needs to be *evaluated* — expand
`Hterm` as its own sum over the pole family, interchange the outer `t`-integral with that sum
(another `hasDerivAt_tsum`/dominated-convergence-style step), and show each pole's `t`-integral
contribution collapses (via `G_baxter(k_n)=0` and `baxter_wiener_hopf_complex`) to exactly
`h_explicit_term`'s own value. Not attempted yet — see `OZFIX.6` below.

---

### Task OZFIX.6 — Algebraic collapse (`B.5`, the mathematical payoff)

Combine `OZFIX.5`'s assembled `oz_forcing(r) + oz_linear_op(h_explicit)(r)` against
`h_explicit(r)`'s own defining sum, using: (a) `G_baxter(k_n)=0 ⟹ Npoly(k_n) =
Dpoly(k_n)·exp(-ik_nσ)` (already available in `BaxterPoles.lean`), and (b) `OZFIX.2`'s
`baxter_wiener_hopf_complex` linking `Chat_complex(k_n)` to `Qhat_complex(k_n)`/`G_baxter`'s own
structure. Likely the single hardest remaining piece; budget the most time here.

**2026-07-15 — numerical scoping pass, before any Lean attempt (this project's standard
discipline). Key finding: the collapse is *not* per-pole/termwise, contrary to this task's
original framing ("show the per-pole contribution collapses… termwise").** Checked directly
(`ozfix6_check.py`, scratch, not committed; η=0.3, σ=1, pole `k₅≈31.08+5.32i` found via
Newton refinement, `|G_baxter(k₅)|≈4×10⁻¹¹`, `r=1.5`):
- **Sanity check, confirmed exactly** (diff `~1e-19`, floating-point noise only): the trivial
  factoring `∫t·c_HS(t)·exp(ik(r+t))dt = exp(ikr)·Chat_F(-k)` (pulling the `r`-dependent phase
  out of the `t`-integral) — this is the elementary first step any collapse derivation needs, and
  it holds unconditionally (not dependent on `k` being a zero of `G_baxter`), so it's a safe,
  reusable building block regardless of how the rest of the collapse goes.
- **The actual per-pole isolation check, found FALSE.** Computed `oz_linear_op`'s pole-`n`
  contribution alone (`(2πρ/r)·∫t·c_HS(t)·(1/2π)·[Hterm_n(r+t)−Hterm_n(max(r-t,σ))] dt`, i.e. the
  `OZFIX.5`-closed-form piece for a *single* pole+mirror pair `n`, with **no** `oz_forcing`
  contribution added) against the natural per-pole target `(ρ/r)·h_explicit_term(n)(r)`: the
  ratio came out to **`-2.72`, not `1`** — not even close, not a sign error or missing constant.
  So `oz_forcing`'s contribution (which is a single closed-form real function with **no** pole
  index at all — it cannot itself decompose additively across the `n`-indexed sum in any obvious
  way) is *not* a separate, negligible correction to a working per-pole identity; it must be
  doing essential structural work in the collapse, meaning **the true identity only closes at the
  level of the full infinite sum over all poles, not term-by-term.** This matches the classical
  Wiener–Hopf picture (`(1-ρQ̂(k))(1-ρQ̂(-k))=1-ρĈ(k)` is a statement about the whole
  generating function, not about individual coefficients) far more than a naive "each residue
  matches its own target" framing — but means the Lean route needs rethinking, not just more
  algebra on the same per-pole approach.
- **Practical consequence for the Lean strategy:** the originally-planned route (interchange the
  outer `t`-integral with the pole sum, then close pole-by-pole via `G_baxter(k_n)=0` +
  `baxter_wiener_hopf_complex` alone) does **not** work as stated and should not be attempted
  as written. A working route most likely needs one of: (a) an independent residue/Fourier
  expansion of `oz_forcing` itself in the *same* pole family (not yet derived anywhere in this
  project — a genuinely new piece of mathematical content), so that its contribution can be
  folded pole-by-pole alongside `oz_linear_op`'s; or (b) abandoning the termwise route after all
  and going through `radial3d_conv` + a genuine Fourier-inversion/residue-theorem argument for the
  *whole* series at once (the route Group OZFIX's stated strategy deliberately avoided, precisely
  because Mathlib lacks the needed residue-theorem/argument-principle machinery — see `BAXTER.2`'s
  own Mathlib capability check, `proof_notes_baxter.md`). Neither is a quick fix.
- **The aggregate identity itself is not in doubt** — independent of this termwise-strategy
  setback, `oz_forcing(r)+oz_linear_op[h_explicit](r) = h_explicit(r)` (the actual target) has
  strong prior numerical confirmation: `oz_forcing_add_linear_op_eq_radial3d_conv`
  (`OZExteriorBridge.lean`, already proved, unconditional in `h`) shows this quantity equals
  `ρ·radial3d_conv(c_HS, spliced_h_explicit)(r)` (using that `oz_linear_op` only ever samples
  `h_explicit` on `s≥σ`, so splicing in `-1` below `σ` doesn't change the value), and `BAXTER.2`'s
  own "Independent real-space OZ-equation check" (`proof_notes_baxter.md`) already validated
  `radial3d_conv(c_HS, h_explicit)` against `h_explicit` directly to 0.05% at `r=1.2`, tightening
  to `~0.000%` by `r=2.5` — strong, independent evidence the *aggregate* fixed-point identity
  holds. What's missing is only a genuine **proof route**, not confidence in the target itself.

**Status:** ◑ **split → `OZFIX.11` (`r ≥ 2σ`, ✓ DONE 2026-07-16, axiom-clean) + `OZFIX.12`
(`σ ≤ r < 2σ`, scoped) + `OZFIX.13` (`σ`-endpoint + wiring, scoped)** — see those sections below.
The scoping finding above ("per-pole collapse is false, `−2.72`") is now fully understood: it is
specific to `σ ≤ r < 2σ` (where `oz_forcing ≠ 0`); for `r ≥ 2σ` the per-pole collapse is TRUE and
proved, with collapse factor `ρ·Ĉ(k_n) = 1` (Wiener–Hopf factorization vanishing at `G_baxter`
zeros — `OZFIX.11`).

---

### Task OZFIX.7 — Regularity (`B.6`): `ContinuousOn`+boundedness

**✓ DONE on `(σ,∞)`/`[r0,∞)` for `r0>σ`**, new file `LeanCode/HardSphere/HExplicitRegularity.lean`
(no `sorry`/`axiom`, `#print axioms` confirms only `[propext, Classical.choice, Quot.sound]`).
Confirmed the prediction: reused the existing uniform-bound infrastructure
(`h_explicit_term_uniform_summable_bound_of_pole_family` + `continuousOn_tsum`) near-directly for
both halves.

- **`h_explicit_continuousOn_Ioi`** — `ContinuousOn h_explicit (Set.Ioi σ)` (open ray),
  unconditional. Localizes at each point `x∈(σ,∞)` via the threshold `r0:=(σ+x)/2∈(σ,x)`:
  `continuousOn_tsum` gives `ContinuousOn (∑'h_explicit_term) (Ici r0)`, and since `Ici r0` is a
  neighborhood of `x` (`r0<x`, via `Ici_mem_nhds`), `ContinuousOn.continuousAt` upgrades this to
  `ContinuousAt … x` — the pointwise-in-`x` argument needed since the uniform bound `u` genuinely
  depends on the threshold `r0`, not a single global threshold covering all of `(σ,∞)` at once.
- **`h_explicit_bounded_on_Ici`** — `∃ C, ∀ r∈Ici r0, |h_explicit(r)|≤C` for any fixed `r0>σ`, via
  the same uniform bound `u` (`Summable`), `Summable.tsum_mono` for the termwise sum bound, and
  the `1/(2πr)≤1/(2πr0)` monotonicity of `h_explicit`'s own prefactor for `r≥r0>0`.

**What's left — the closed endpoint `r=σ` itself.** `oz_fixed_pt_unique`'s literal hypothesis
needs `ContinuousOn h (Set.Ici sigma)` (closed at `σ`) and a *global* bound `∃C,∀r,|h r|≤C` (not
just on some `[r0,∞)`). `h_explicit`'s own series is only known summable/continuous for `r>σ`
strictly — the same genuine `σ`-boundary gap already flagged in `OZFIX.4`'s `hint` and confirmed
structurally significant by `OZFIX.6`'s scoping finding. Not attempted here; not a quick corollary
of the two results above. `OZFIX.8`'s final assembly will need to either discharge this too
(likely requiring the same machinery as `OZFIX.4`'s `hint`) or take it as a further explicit
hypothesis, matching this project's established pattern.

**⛔ SKIP — do NOT re-attempt the closed endpoint `r=σ` (`hcont_sigma`). DECIDED 2026-08-25.**
A future gap-survey should treat this as *closed-by-decision*, not *open*. Three reasons:
1. **The easy route provably cannot reach σ.** `h_explicit_summable` (`BaxterResidue.lean`) needs
   the term exponent `1−2r/σ < −1`, i.e. `r > σ` *strictly*; at `r = σ` it is exactly `−1`
   (harmonic), so the `Summable` uniform bound that powers `continuousOn_tsum` does not exist there.
2. **Likely FALSE as literally stated.** Lean's `tsum` of a non-`Summable` family is `0`, so unless
   the paired residues decay strictly faster than `n⁻¹` (unknown — needs a sharper residue
   asymptotics at σ), `h_explicit σ` collapses to junk `0` and `ContinuousWithinAt h_explicit
   (Ici σ) σ` is false — the σ-endpoint junk-`tsum` trap this project has caught before
   (cf. `radial_inversion_antideriv` vacuity, MA.9 bug 4).
3. **Zero payoff even if proved.** `hcont_sigma` feeds ONLY `OZFIX.8`'s *conditional*
   `oz_h_eq_spliced_h_explicit`, already blocked on BOTH the `oz_fixed_pt_unique` axiom (OZ.10)
   AND the separate `hcollapse` gap (OZFIX.6). Discharging it makes nothing unconditional.

**If ever genuinely needed**, the only routes are hard and out of scope: (a) a sharper `r=σ`
residue-decay bound giving absolute summability at the endpoint, or (b) proving the *unbuilt*
pole-series = Baxter-renewal identity `h_explicit = baxterPsiOuter/·`, then transferring the known
`baxterPsiOuter_continuousOn_Ici` (closed at σ).

**Status:** ✓ DONE on `(σ,∞)`/`[r0,∞)` (std-3); closed endpoint `[σ,∞)` **SKIPPED by decision** (above).

---

### Task OZFIX.8 — Final assembly (`B.7`)

**✓ DONE, conditionally** — new file `LeanCode/HardSphere/OzFixedPtHExplicitFinal.lean`, theorem
`oz_h_eq_spliced_h_explicit`. No `sorry`; `#print axioms` →
`[propext, Classical.choice, Quot.sound, oz_fixed_pt_unique]` — i.e. the *only* dependency beyond
the standard three is the pre-existing `oz_fixed_pt_unique` axiom itself; `hcollapse`/`hcont_sigma`
are ordinary hypotheses on the theorem (not axioms), matching the established conditional-theorem
pattern (`hstep`, `hint`, `oz_h_exterior_regularity`).

Packages `OZFIX.5`–`7` into the `OzFixedPt ∧ ContinuousOn ∧ bounded` shape and invokes
`oz_fixed_pt_unique` to conclude `oz_h eta sigma rho` equals the spliced `h_explicit`/`(-1)`
function — **conditional on two explicit hypotheses**, corresponding exactly to the two genuine
gaps `OZFIX.6`/`OZFIX.7` found:
- `hcollapse` — the `OZFIX.6` algebraic-collapse identity itself (taken as a hypothesis since
  `OZFIX.6`'s scoping pass found the originally-planned per-pole proof route is false).
- `hcont_sigma` — continuity of `h_explicit` at `σ` from the right (`OZFIX.7`'s missing
  closed-endpoint piece).

**Everything else is unconditional, genuine Lean content, no shortcuts:**
- The core branch (`r<σ`): `oz_operator`'s own `if_pos` gives `-1=-1` trivially.
- **`oz_linear_op` splicing is invisible**: since `oz_linear_op`'s inner integral only ever
  samples `s∈[max(r-t,σ),r+t]⊆[σ,∞)`, the spliced function and raw `h_explicit` agree everywhere
  `oz_linear_op` looks — proved via nested `intervalIntegral.integral_congr` (outer over `t`,
  inner over `s`), not assumed.
- **Continuity on `Ici σ`**: glues `hcont_sigma` (at the single point `σ`, via
  `ContinuousWithinAt.congr`) with `OZFIX.7`'s open-ray `ContinuousOn (Ioi σ)` (elsewhere, via
  `ContinuousOn.continuousAt` + `Ioi_mem_nhds` since `Ioi σ` is a neighborhood of any `x>σ`).
- **Global boundedness**: `-1` on the core; on `[σ,∞)`, glues `OZFIX.7`'s `[r0,∞)` bound
  (`r0:=σ+1`) with a fresh compactness argument on `[σ,r0]` (`IsCompact.bddAbove_image`/
  `bddBelow_image`, powered by the `ContinuousOn (Ici σ)` fact just derived — genuinely needs
  `hcont_sigma`, since without it `[σ,r0]` boundedness has no source).
- **Final step**: unfolds `oz_h`'s `Classical.choose` definition, then closes via
  `ExistsUnique.unique` matching the spliced function's bundle against `oz_h`'s own (via
  `Classical.choose_spec`).

**Status:** ✓ **DONE, conditional on `hcollapse` and `hcont_sigma`.** This completes Group
OZFIX's logical shape end-to-end — the *only* things standing between this and an unconditional
`OzFixedPt` result are exactly the two named gaps, both honestly scoped (not vague). `POLE.3`'s
`hstep` gap is not threaded through here since this theorem is stated over an abstract `kfam`
(matching `OZFIX.3`–`7`'s own convention) — instantiating a concrete `kfam` witness would
additionally need `hstep`.

**2026-07-16 — hypothesis weakened by `OZFIX.11`:** the corollary
`oz_h_eq_spliced_h_explicit_of_inner_collapse` (`OzCollapseTwoSigma.lean`) replaces `hcollapse` by
`hcollapse_inner` (the identity on `σ ≤ r < 2σ` only) — the `r ≥ 2σ` half is now supplied by
`oz_collapse_of_two_sigma_le`. Costs two extra hypotheses (`heta_def`, `hkfam_ne`); same axiom
footprint (`oz_fixed_pt_unique` + standard three).

---

### Task OZFIX.9 — `hcollapse` via Route A (`oz_forcing` Mittag-Leffler expansion over the pole family)

**Goal.** Discharge `OZFIX.6`'s `hcollapse` (the algebraic-collapse identity, i.e. the `OZFIX.8`
gap) by **Route A** — the termwise route the `OZFIX.6` scoping left open — as an alternative to the
process-parallel **Route B** (whole-series `radial3d_conv` + a Mathlib-absent residue/Fourier-inversion
theorem, currently being axiomatized elsewhere). New task split off `OZFIX.6` so the two routes are
tracked independently.

**Starting identity (from `OZFIX.5`, proved, unconditional).**
`oz_forcing(r) + oz_linear_op[h_explicit](r) = (2πρ/r)·∫₀^σ [forcing-indicator-piece +
t·c_HS(t)·(1/2π)·Re(Hterm(r+t) − Hterm(max(r-t,σ)))] dt`
(`oz_forcing_add_linear_op_h_explicit_eq_outer_integral`). Route A must show this `= h_explicit(r)`.
Equivalently (via the already-proved `oz_forcing_add_linear_op_eq_radial3d_conv`, unconditional in
`h`): `ρ·radial3d_conv(c_HS, spliced h_explicit)(r) = h_explicit(r)` on `[σ,∞)`.

**Why the naive per-pole route is FALSE (`OZFIX.6` finding).** `oz_linear_op`'s single-pole-`n`
contribution vs its naive per-pole target has ratio `-2.72`, not `1`: `oz_forcing` is pole-index-free
and cannot be split across the `n`-sum, so it must do essential structural work — the identity closes
only at the full-series level.

**Route A key insight (2026-07-15, sharpening the `OZFIX.6` scoping).** `oz_forcing(r) =
-(πρ/r)·∫₀^σ t·c_HS(t)·(σ²-(r-t)²)·[r<σ+t] dt` is **compactly supported in `r`**: on `[σ,∞)` it
vanishes for `r > 2σ` (the indicator `r<σ+t`, `t≤σ`, forces `r<2σ`). Hence its Fourier transform
`ô_forcing(k)` is **entire (no poles)**. So Route A's "`oz_forcing` residue/Fourier expansion in the
same pole family" is **not** an expansion at `oz_forcing`'s own poles (it has none) but a
**Mittag-Leffler expansion using the resolvent's poles `{k_n}`** (zeros of `G_baxter`/`1-ρQ̂`), with
`ô_forcing(k_n)` as the (clean, finite, per-pole) coefficient. This makes Route A **well-defined and
arguably more tractable than the OZFIX.6 note suggested**: each pole `n` gets one number
`ô_forcing(k_n)`, and the collapse becomes "for each `n`: `oz_linear_op`'s pole-`n` piece +
`ô_forcing(k_n)`·(factor) = `h_explicit_term(n)`".

**Concrete plan.**
1. *(numerical scoping — project discipline, before any Lean)* At a test state point + a Newton-refined
   pole `k_n`: compute `ô_forcing(k_n)` (FT of the compact-support `oz_forcing`), the `oz_linear_op`
   pole-`n` contribution (the `OZFIX.5` closed `Hterm` piece), and `h_explicit_term(n)`; **validate**
   the per-pole fold `oz_linear_op_n + ô_forcing(k_n)·(residue factor) = h_explicit_term(n)` and pin
   the exact `(residue factor)`. This is the "genuinely new content" — derive it numerically first.
2. Interchange the outer `t`-integral with the pole sum (reuse `OZFIX.3`'s `hasDerivAt_tsum` /
   dominated-convergence machinery).
3. Per-pole algebraic collapse using `G_baxter(k_n)=0` (`BaxterPoles.lean`) + `baxter_wiener_hopf_complex`
   (`OZFIX.2`) + the derived `ô_forcing(k_n)` coefficient.
4. Sum back to `h_explicit(r)`; discharge `hcollapse` in `OZFIX.8`.

**Concurrency / files.** Route B (whole-series, Mathlib-axiom) is being developed elsewhere (edits
`BaxterResidue.lean` etc.). Route A should land in a **new file** (e.g. `OzForcingResidue.lean`) to
avoid conflict, importing the existing `OZFIX.1`–`5` results read-only. OZFIX/POLE files do not import
the (currently in-flux) `MixtureHSCounting.lean`, so a Route-A file builds independently.

**Depends on.** `OZFIX.1`–`5` (done), `baxter_wiener_hopf_complex` (`OZFIX.2`), `G_baxter` zero facts
(`BaxterPoles.lean`), `oz_forcing_add_linear_op_eq_radial3d_conv` (`OZExteriorBridge.lean`).
**Effort.** Research-scale (the `ô_forcing(k_n)` fold is new content; numerical scoping first, then a
substantial Lean proof) — but the compact-support insight makes it well-posed.
**Direction (2026-07-15, user-confirmed): Route B closes `hcollapse`.** Route A is ≈ Route-B
difficulty (finding 3 below: `R_n` is not a clean `ô_forcing(k_n)` coefficient — no shortcut), and
Route B (whole-series `radial3d_conv` + a Mathlib-missing residue axiom, in progress elsewhere) trades
the physics-specific `oz_core_closure` for a **standard, reusable** residue/argument-principle axiom —
a favorable *quality* trade (physics-axiom → math-axiom). Route A is kept here as the eventual
**unconditional (axiom-free)** path; if revisited, the `r≥2σ` per-pole part is now the easy, tractable
piece (exact per-pole), and only the `σ≤r<2σ` Mittag-Leffler part is hard.

**Status.** ☐ **UNBLOCKED — the fix resolved the aggregate identity; Route A is viable but still
research-scale.** Re-scoped against the now-fixed `G_baxter = (-ik)³·(1-Q̂)` (`ozfix9_retry.py`/
`ozfix9_conv.py`/`ozfix9_routeA.py`, scratch, η=0.3, σ=1; my reconstruction now matches the current
Lean `G_baxter`/`residue_term` exactly). **Hypothesis (b) from the previous status was correct — the
earlier "~50% fail" was truncation, not a residue-normalization bug.** Findings:

1. **Reconstruction validated:** `h_explicit(2.0) = 0.005688` (N=14) → ground truth `0.005663`; the
   corrected `n=0` pole `6.0580+1.4368i` = ground truth exactly (family denser, `≈2π` spacing).
2. **Aggregate `oz_forcing+oz_linear_op[h_explicit]=h_explicit` HOLDS.** Exactly, per-pole, to machine
   precision for `r ≥ 2σ` where `oz_forcing = 0` (`diff = -0.000000` at every N, `r=2.0, 3.0`); slowly
   convergent to 0 for `σ ≤ r < 2σ` where `oz_forcing ≠ 0` (`r=1.5`: diff `0.0385→0.0094` as `N:10→45`,
   `~1/N`, the `n^{-2}` tail). The prior `~0.036`-at-`N=11` residual was premature truncation.
   ⇒ `OZFIX.6`'s "per-pole collapse is false (−2.72)" is now understood: it is specific to the
   `σ≤r<2σ` sub-region (where `oz_forcing` must contribute); for `r≥2σ` the per-pole route works.
3. **Route A is viable but not the clean shape hypothesized.** `oz_forcing = Σ_n Re[H_n − L_n]` holds
   numerically (`0.674 → 0.684` as N grows), but the per-pole `R_n = H_n − L_n` is **not**
   `ô_forcing(k_n)·(clean factor)` — the ratio oscillates (`−15.8, −4.5, +4.9, …`), so the
   compact-support `ô_forcing(k_n)` idea does *not* yield a simple per-pole coefficient. Route A's
   identity `oz_forcing = Σ(H_n−L_n)` is just the aggregate **rearranged**; proving it termwise for
   `σ≤r<2σ` is a genuine Mittag-Leffler identity, **not obviously simpler than Route B**.

**Consequence.** `OZFIX.9` is unblocked (`h_explicit` correct, aggregate confirmed). Realistic Lean
path: the `r≥2σ` region is now a tractable per-pole collapse; the `σ≤r<2σ` region still needs a genuine
termwise argument (Route A) whose difficulty is comparable to Route B — so whether to invest in Route A
vs. let the Route-B (whole-series `radial3d_conv` + Mathlib-axiom) process close `hcollapse` is a real
choice, no longer a "Route A is clearly cheaper" situation.

---

### Task OZFIX.10 — `hcollapse` via Route B (growing-contour Fourier inversion)

*(Split off `OZFIX.6` as its own task 2026-07-15, mirroring `OZFIX.9` = Route A, so the two routes
are tracked independently. Formerly recorded in a standalone `proof_notes_route_b.md`, merged here
per the one-group-one-file convention; the general-purpose math-axiom documentation it contained
now lives centrally in `MATH_AXIOMS.md`.)*

**Goal.** Discharge `hcollapse` by **Route B**: establish `h_explicit(r)` as the rigorous real-line
Fourier inversion of `Ĥ(k) := Ĉ(k)/(1-ρĈ(k))` via a growing semicircular contour — real-line
integral `∫_{-R}^{R} k·Ĥ(k)·e^{ikr} dk` → `2πi·Σ residues` as `R→∞` through pole-avoiding radii —
then connect back to `radial3d_conv`'s real-space form. Continuation of the 2026-07-15
axiomatization effort (Phase 1: `circleIntegral_eq_sum_of_small_circles`,
`LeanCode/Analysis/ContourDeformation.lean`).

**Step 0 (numerical pre-check, scratch, not committed) — ✓ normalization pinned.** At η=0.3, σ=1,
r=1.5: `residue_term(r,k_n)` matches the true small-circle residue of `F(k)=k·Ĥ(k)·e^{ikr}` at
`k_n` to machine precision (0.0000% at poles 1, 4, 8), and
`(1/(2πr))·Re[∫_{-R}^{R}F dk / (2πi)]` tracks `h_explicit(r,N)` with `diff → 4·10⁻⁴` by `N=35` —
the standard residue-theorem constant `2πi` is exactly right, no normalization surprises.

**What's DONE — two genuine, general-purpose, reusable pieces (both `lake build` clean):**

1. **Jordan's lemma, `jordan_lemma_arc_bound` (`LeanCode/Analysis/JordanLemma.lean`) — proved
   outright, NO new axiom.** A dedicated research pass confirmed the classical quantitative bound
   `‖∫_arc g(z)e^{iaz}dz‖ ≤ πM/a` is fully provable from the pinned Mathlib: ML inequality
   (`intervalIntegral.norm_integral_le_of_norm_le`) + `Complex.norm_exp` + interval reflection
   (`Real.sin_pi_sub`) + Jordan's inequality itself (`Real.mul_le_sin` — literally docstringed
   "One half of Jordan's inequality" in Mathlib) + a `zeta0_formula`-style `HasDerivAt`+FTC
   antiderivative. `#print axioms` = standard three only.
2. **Half-disk boundary residue theorem (`LeanCode/Analysis/ContourDeformation.lean`)** — axiom
   `halfDiskBoundary_eq_sum_of_small_circles` + genuine theorem
   `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`. Needed because Jordan's lemma bounds an
   *arc* and the Phase-1 circular axiom deliberately covers circles only; the `[-R,R]`-diameter +
   upper-arc boundary is a genuinely different outer shape (same keyhole/slit content, equally
   absent from Mathlib). One new narrowly-scoped axiom, mirroring Phase 1's discipline;
   `#print axioms` on the derived theorem = that one axiom + standard three. Full axiom
   documentation: `MATH_AXIOMS.md`.

Both reusable by Group MZERO's Route B (`MZERO.9`–`MZERO.11`, `proof_notes_mixture_rdf.md`), which
independently hit the identical gap.

**What's BLOCKED — the arc genuinely does not vanish via crude magnitude bounds.** Applying the
two pieces to `h_explicit`'s actual `F(k)=k·Ĥ(k)·e^{ikr}` fails at the very first numerical check.
Sweeping `θ∈[0,π]` at fixed large `R` (η=0.3, σ=1):

```
R=30:   |k·Ĥ(k)|: 0.28 near θ=0,π — FLAT PLATEAU 52.36 for θ∈(≈10°,≈170°)
R=100:  same shape, plateau 174.53
R=300:  same shape, plateau 523.60        (52.36/30 ≈ 174.53/100 ≈ 523.60/300 ≈ 1.745)
```

**`|k·Ĥ(k)|` grows *linearly* in `R`** across most of the arc — it does not decay. In hindsight:
`Ĉ(k)` is the FT of a `[0,σ]`-supported function, so `|Ĉ|` blows up exponentially off the real
axis; `Ĥ=Ĉ/(1-ρĈ)` stays *bounded* (not small) only because the denominator blows up at matching
rate — the same individually-divergent-but-jointly-controlled behavior
`BaxterPoles.lean`'s pole-side machinery (`abs_exp_neg_ikn_sigma_*`) handles *at the poles*, but
nothing characterizes it on a generic growing arc. Feeding Jordan's lemma `M(R) ~ 1.745·R` yields
a bound `~π·1.745·R/r` — *growing*, the wrong conclusion entirely.

**Yet the arc integral itself genuinely decays** — re-confirmed carefully with pole-avoiding
midpoint radii (the `Rvals` construction) out to `N=55` (`R≈349`), `r=1.5`:

```
N= 6  R= 40.95  |arc|=0.1482  |arc|·R=6.07
N=15  R= 97.51  |arc|=0.0688  |arc|·R=6.71
N=25  R=160.33  |arc|=0.0377  |arc|·R=6.04
N=35  R=223.15  |arc|=0.0243  |arc|·R=5.43
N=45  R=285.97  |arc|=0.0173  |arc|·R=4.94
N=55  R=348.80  |arc|=0.0130  |arc|·R=4.54
```

Smooth `O(1/R)`-ish decay (with `|arc|·R` drifting slowly down — possibly a log correction). The
decay is **oscillatory cancellation**: the phase `Rr·cosθ` oscillates rapidly against a
comparatively slowly-varying amplitude. Sup-norm ML-inequality bounds — all Jordan's lemma's proof
technique can see — are structurally blind to this.

**Why this was NOT axiomatized (deliberate stop).** Every axiom admitted this session (the
circular and half-disk deformation facts) is a named, independently-recognized classical theorem.
Capturing *this* arc's decay rigorously needs a **non-stationary-phase / Van der Corput-type
oscillatory-integral estimate** (first-derivative test: `φ(θ)=r·cosθ` has `φ'` bounded away from 0
except near `θ=0,π`; integration by parts trades amplitude smoothness for a `1/R` gain) — whose
correct hypotheses (amplitude-derivative control vs. the amplitude's own `O(R)` growth) need real
derivation first. A rushed "this arc vanishes" axiom would silently assume the hardest part of
exactly the theorem being proved — a materially riskier kind of axiom than the two above, failing
the admissibility discipline (`MATH_AXIOMS.md`). Flagged as genuinely open
research-scale content, not attempted further.

**Status:** ◑ infrastructure DONE (Jordan's lemma, no axiom; half-disk residue theorem, one new
axiom), **arc-vanishing for the specific `Ĥ` OPEN** (needs a correctly-derived
non-stationary-phase estimate — or an altogether different contour/argument). `hcollapse` itself
remains open. **Per the user-confirmed direction recorded in `OZFIX.9` (2026-07-15), Route B — this
task — is the designated route to close `hcollapse`** (favorable axiom trade: retires the physics
axiom `oz_core_closure` in exchange for standard, reusable math axioms), with Route A kept as the
future unconditional path; so the open arc-vanishing estimate above is the critical path forward.

**✅ UPDATE (2026-07-15, Group MA): the blocked monolithic arc estimate is SUPERSEDED — a
decomposed path now exists.** Group MA (`MATH_AXIOMS.md`) landed `MA.2` + `MA.3`, which together
dissolve the arc-vanishing blocker without any inadmissible axiom:
- **`MA.2`** — `mittagLeffler_expansion_of_bounded_on_circles` (`Analysis/MittagLeffler.lean`,
  classical Mittag-Leffler expansion, new admissible axiom): `Ĥ` itself (not `k·Ĥ·e^{ikr}`) is
  numerically **uniformly bounded** on the expanding pole-avoiding circles (`sup‖Ĥ‖` constant at
  1.7453 for η=0.3 / 1.1636 for η=0.45, N=5→59) — exactly the theorem's hypothesis — and the
  expansion converges to `Ĥ` pointwise (verified, ~1e-7 by N=60 pole quadruples).
- **`MA.3`** — `fourier_kernel_one_pole` (same file, **genuine theorem**, `#print axioms` =
  half-disk axiom + standard three): `∫_{-R}^{R} e^{ixr}/(x-k₀)dx → 2πi·e^{ik₀r}` — here Jordan's
  lemma applies cleanly (amplitude `1/(z-k₀)` decays `1/R`; the `O(R)`-growth obstruction above
  was an artifact of bundling `k·Ĥ` into one amplitude).

**Revised Route B critical path:** expand `Ĥ` via MA.2 → Fourier-invert termwise via MA.3 →
control the sum/limit interchange (summability: reuse the `POLE.5` machinery + the `hkfam_re`
linear-growth input) → identify the resulting series with `h_explicit`'s `residue_term` sum
(the `k⁷Ĉ/(G(-k)G')` residue form — needs the `Ĥ`-residue ↔ `residue_term` bridge, cf.
`baxter_cube_mul_F_eq_G`). Remaining work is assembly + the interchange bookkeeping — no missing
classical machinery identified anymore.

**❌ 2026-07-16 — the MA.2-pointwise assembly above is BLOCKED by a FALSE identity (negative
result, recorded so it is not re-attempted).** Working out the termwise Fourier inversion of
`x·Ĥ(x)·e^{ixr}` against the MA.2 expansion: splitting `x·(1/(x−p)+1/p) = 1 + p/(x−p) + x/p`, the
`1`-moment `W₀ = ∫_{-R}^{R} e^{ixr}dx` cancels exactly within `±`-pairs (`res(−p) = −res(p)`,
`Ĥ` even) and the `p/(x−p)` pieces go to MA.3 — but the **`O(R)`-growing moment
`W₁ = ∫_{-R}^{R} x·e^{ixr}dx` enters with total coefficient `Ĥ(0) + Σ' res_n/p_n`, and that sum
is NOT zero**: the exact finite-`N` identity (residue theorem, kernel `Ĥ(w)/w`) makes the partial
sums equal the circle-mean of `Ĥ`, which tends to **`−1/ρ`** (off the real axis `|Ĉ|` blows up
exponentially, so `Ĥ = (1/ρ)·(S−1) → −1/ρ` with `S := 1/(1−ρĈ) → 0`; the near-axis transition
strip has vanishing angular measure). Smoking gun already in the recorded numerics: the
circle-bound plateaus `sup‖Ĥ‖ = 1.7453` (η=0.3) and `1.1636` (η=0.45) are exactly `1/ρ`;
re-confirmed directly (circle-mean `→ −1.73` at `R ≈ 763`, `−1/ρ = −1.7453`, slow `ln R/R`
approach). Consequences, all checked algebraically: (i) a degree-1 ML kernel (`f(w)/(w²(w−z))`)
leaves the `W₁` coefficient **unchanged** (`x·(1/(x−p)+1/p+x/p²) = 1 + p/(x−p) + x/p + x²/p²`;
the new `W₂` piece cancels within `±`-pairs, `W₁/p` does not); (ii) pairing `±p` *before*
splitting gives `2res·x³/(p(x²−p²)) = 2res·x/p + 2res·px/(x²−p²)` — same `W₁` term; so **no ML
degree or pairing order removes the obstruction** — it is the old arc-growth problem re-expressed,
and the divergent `(−1/ρ)·W₁` piece is compensated only non-locally (near-circle pole tail).
Pointwise inversion of `k·Ĥ·e^{ikr}` remains genuinely blocked.

**❌❌ 2026-07-16 (second pass) — the ORIGINAL "arc-vanishing OPEN" blocker at the top of this
task is ALSO FALSE. Retracted.** The recorded obstruction — "`‖k·Ĥ(k)‖` *grows* `≈1.745·R` on the
arc, so Jordan's crude sup-bound gives a growing estimate; the real `O(1/R)` decay is oscillatory
cancellation needing a non-stationary-phase/Van-der-Corput estimate" — is a **bookkeeping error,
not a real obstruction**. Jordan's lemma is applied to `F(z) = g(z)·e^{iaz}` and needs
`M(R) := sup_arc‖g‖ → 0`; it does **not** need `sup_arc‖k·Ĥ‖` to be small. Splitting the phase
`r = b + a` with `σ < b < r`, `a = r−b > 0`:
`k·Ĥ(k)·e^{ikr} = [z·Ĥ(z)·e^{izb}]·e^{iaz}`, and the bracket's sup **does** tend to `0`, because
the `1.745·R` plateau sits exactly where `e^{izb}` is exponentially small. Two regimes (both
provable from existing lemmas — no new machinery):
- **near the real axis** (`|Im z| ≤ δ·ln R`, `δ < 1/σ`): `‖Ĉ(z)‖ ≲ e^{Im z·σ}/‖z‖²` gives
  `‖Ĉ‖ ≲ R^{δσ−2} → 0` (`Chat_complex_norm_bound`, `RadialFourierCHSComplex.lean`), hence
  `‖1−ρĈ‖ ≥ 1/2` and `‖z·Ĥ·e^{izb}‖ ≲ R^{δσ−1}`;
- **interior** (`Im z > δ·ln R`): `‖Ĥ‖ ≤ M` on the pole-avoiding circles (`hHbound`, numerically
  `M = 1/ρ` *exactly*) and `‖e^{izb}‖ ≤ R^{−δb}`, so `‖z·Ĥ·e^{izb}‖ ≤ M·R^{1−δb}`.
Choosing `1/b < δ < 1/σ` (possible **iff `b > σ`, i.e. iff `r > σ`** — exactly the physical
domain) makes both `→ 0`, so `‖arc‖ ≤ π·M(R)/a → 0`.
**Numerically confirmed** (`ozfix12_arc_check.py`, scratch, η=0.3, σ=1, pole-avoiding radii to
`R ≈ 952`): `sup_arc‖z·Ĥ‖/R = 1.7453` *constant* (reproduces the recorded growth, and pins
`1.7453 = 1/ρ`); but `sup_arc‖z·Ĥ·e^{izb}‖` **decays with slope exactly `−1.00`** for every
`b ∈ {1.05, 1.2, 1.4}` (all three identical — the sup is attained at `θ = 0,π`, the real-axis
regime); and the method's boundary is confirmed to be `b > σ` (check D). **Consequences:** Van der
Corput (MA.4) is *not* needed here and has no consumer; MA.2/MA.3's "decomposition dissolves the
arc blocker" framing is unnecessary (the blocker was never there); and the pointwise inversion
`Λ(u) = −J(u)/(2π)` is available for every `u > 0` (no `k` factor ⟹ any `δ ∈ (0,1/σ)` works).
**But this does not close `hcollapse`** — see the next paragraph and `OZFIX.14`.

**✅ Supersession — `hcollapse` never needed pointwise inversion.** `oz_linear_op` integrates
`h_explicit` in `s` (kernels `(e^{ix·hi}−e^{ix·lo})/x`-type, phases `≥ σ`) and then in `t` against
`t·c_HS` (`Chat_F`-type factors): after BOTH integrations every kernel piece has decaying amplitude
with positive effective phase, where the already-proven `jordan_lemma_arc_bound` +
`halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles` suffice. Route B therefore decomposes as
**`OZFIX.11`** (`r ≥ 2σ`: per-pole, ✓ DONE — needs *no contour machinery at all*, the collapse
factor is `ρĈ(k_n) = 1`) + **`OZFIX.12`** (`σ ≤ r < 2σ`: smoothed-kernel windowed contour
argument, scoped) + **`OZFIX.13`** (`σ`-endpoint via continuity + discharge wiring). MA.2 itself
remains a valid, proved theorem (and its Ĥ-boundedness hypothesis data transfers to `OZFIX.12`'s
`hHbound`); only its *pointwise-inversion consumer role* for `hcollapse` is retired. MA.3's
private proof template (`fourier_kernel_halfdisk`/`fourier_kernel_arc_bound`) is the seed for
`OZFIX.12`'s kernel family.

---

### Task OZFIX.11 — `hcollapse` for `r ≥ 2σ`: the per-pole collapse (`ρĈ(k_n) = 1`)

**✓ DONE (2026-07-16), axiom-clean** — new file `LeanCode/HardSphere/OzCollapseTwoSigma.lean`,
main theorem `oz_collapse_of_two_sigma_le`; `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (no contour axiom — this half of `hcollapse` needs no complex analysis beyond the
already-unconditional `OZFIX.2` Wiener–Hopf bridge). Full `lake build` green.

**Statement.** For the standard pole-family pack (`hkfam_zero`/`hkfam_im`/`hkfam_re`/`hkfam_ne`,
`c,d>0`) plus the physical coupling `heta_def : eta = πρσ³/6`, and any `r` with `2σ ≤ r`:
`oz_forcing(r) + oz_linear_op[h_explicit](r) = h_explicit(r)` — literally `hcollapse`'s body.
No `hint`-family hypothesis: `OZFIX.5`'s `hint` is **vacuous** here (`r ≤ σ+t ∧ t < σ ⇒ r < 2σ`),
and its `hint1`/`hint2` side conditions are discharged outright (`hint1`: integrand ≡ 0 on
`uIoo`; `hint2`: `uIoo`-congruence to the manifestly-continuous `Hterm` closed form).

**The mathematical crux, found in this session's planning pass:** on `r ≥ 2σ` (where
`oz_forcing = 0` and `max(r−t,σ) = r−t`), `OZFIX.5`'s outer integral collapses **per pole**, and
the per-pole factor is exactly `ρ·Chat_complex(k_n) = 1`:

1. `∫₀^σ Chat_poly(t)·(e^{ik(r+t)} − e^{ik(r−t)}) dt = e^{ikr}·(Chat_F(−k) − Chat_F(k))`
   (`integral_Chat_poly_exp_pair` — the `r`-phase factors out; the `t`-exponentials are `Chat_F`'s
   own integrand at `∓k`), and `Chat_F(−k) − Chat_F(k) = ik·Ĉ(k)/(2π)` (`Chat_F_neg_sub_eq`,
   pure definition unfolding). Hence each pole's `Hterm`-difference `t`-integral is
   `residue_term(r,k)·Ĉ(k)/(2π)` (`integral_Chat_poly_mul_residue_pair` — the
   `residue_term = B·e^{ikx}` factorization is unconditional division-ring algebra).
2. **`rho_mul_Chat_complex_eq_one_of_G_zero`**: `G_baxter(k) = 0` (`k ≠ 0`) ⇒ `1 − Q̂(k) = 0`
   (`Qhat_pole_iff_G_baxter_zero`) ⇒ `1 − ρĈ(k) = (1−Q̂(k))(1−Q̂(−k)) = 0`
   (`baxter_wiener_hopf_complex`, the `OZFIX.2` payoff — this is what `heta_def` is for). The
   mirror `−conj(k_n)` is a zero too (`G_baxter_zero_mirror`), so the pole+mirror pair sums to
   exactly `h_explicit_term(n)(r)/(2πρ)` (`integral_Chat_poly_mul_Hterm_pair`, with
   `Ĉ = (ρ:ℂ)⁻¹` via `eq_inv_of_mul_eq_one_right`). **This identity is precisely why `OZFIX.9`'s
   numerics found the `r ≥ 2σ` collapse exact per-pole** — the mystery factor was `ρĈ(k_n)`.
3. Interchange `∫₀^σ dt ↔ Σ'_n` via `intervalIntegral.hasSum_integral_of_dominated_convergence`
   (the decisive Mathlib find — takes the `n`-indexed bound directly on `Ι 0 σ`, so the `t = σ`
   endpoint costs nothing), dominated by `P·(2·u n)` with `P` an explicit `Chat_poly` sup bound
   (`Chat_poly_abs_bound`) and `u` from `OZFIX.4`'s `y ≥ σ`-uniform
   `Hterm_uniform_summable_bound_of_pole_family` — valid since `r+t ≥ r ≥ 2σ ≥ σ` and
   `r−t ≥ r−σ ≥ σ` on all of `[0,σ]`, **including the closed endpoints** (`t = σ` at `r = 2σ`) —
   which is why the theorem is stated with closed `2σ ≤ r`.
4. Assembly: `OZFIX.5`'s theorem → one `integral_congr_uIoo` (kills the forcing indicator,
   `max_eq_left`, `Chat_poly_eq_mul_c_HS`, `Complex.re_ofReal_mul`) → `intervalIntegral_re`
   (the `RCLike.re` `change`/`rfl` idiom from `BaxterResidue.lean`) → `HasSum.tsum_eq` +
   `tsum_congr` + `tsum_div_const` + `Complex.div_ofReal_re` → `(2πρ/r)·(1/2π)·(X/(2πρ)) =
   (1/(2πr))·X` by `field_simp`.

**Numerical gate first (project discipline, `ozfix11_stage_check.py`, scratch, not committed;
η=0.3, σ=1, 160 Newton-refined poles):** `|ρĈ(k_n) − 1|` ~1e-15…5e-14 at poles AND mirrors
(n = 0…159); the per-pole `t`-integral identity to rel. ~1e-13 (r ∈ {2.0, 2.5, 3.0},
n ∈ {0, 3, 8}); end-to-end aggregate at `r ∈ {2.0, 2.5}` to quadrature tolerance (~1e-8);
`h_explicit(2.0) = 0.005663` = ground truth at N=160.

**Downstream unlock (proved same session):** `oz_h_eq_spliced_h_explicit_of_inner_collapse`
(same file) — `OZFIX.8`'s conclusion with `hcollapse` weakened to `hcollapse_inner`
(`σ ≤ r < 2σ` only), the `r ≥ 2σ` half supplied by this theorem; axiom footprint unchanged
(`oz_fixed_pt_unique` + standard three).

**Implementation notes (pitfalls hit & fixed):** `abs_add` is now `abs_add_le`;
`eq_inv_of_mul_eq_one_left` vs `_right` (left refers to the *result* factor position);
`intervalIntegrable_const` needs qualification under `open intervalIntegral`;
`Function.comp_def` (not `Function.comp`) for the `simpa`-normalization of
`ContinuousOn.comp`; `field_simp` closes several goals outright (trailing `ring` = "no goals");
`Chat_F_neg_sub_eq` needs a final `norm_num` (`2^2` vs `4`). No `maxHeartbeats` bump needed
(file builds in ~5s).

---

### Task OZFIX.12 — `σ < r < 2σ`: the exact defect algebra, and the reduction to (★)

**◑ Reduction target IDENTIFIED and numerically CONFIRMED; `Kterm` infrastructure ✓ DONE
(axiom-clean); the reduction's Lean assembly remains.** New file
`LeanCode/HardSphere/OzCollapseInner.lean`. The earlier "smoothed-kernel windowed contour"
architecture (previous version of this section) is **superseded**: the contour step turns out to
be circular (see `OZFIX.14`), and the region's real content is a single clean series identity.

**The exact defect algebra (derived this pass, all steps elementary).** Put `t₀ := r−σ ∈ [0,σ)`.
For `σ < r < 2σ`, `max(r−t,σ)` is `r−t` on `[0,t₀)` and `σ` on `[t₀,σ]`, so each pole's
`t`-integral splits. Writing `A(k) := k⁷Ĉ(k)/(G(−k)G′(k))` and using
`∫₀^σ Chat_poly(t)e^{ik(r−t)}dt = e^{ikr}Chat_F(k)` and `P(r) := ∫_{t₀}^σ Chat_poly(t)dt`:

`I_k := ∫₀^σ Chat_poly(t)·(Hterm-summand(r+t) − Hterm-summand(max(r−t,σ)))dt`
`    = (A(k)/(ik))·[e^{ikr}Chat_F(−k) − ∫₀^{t₀}Chat_poly(t)e^{ik(r−t)}dt − e^{ikσ}P(r)]`

and subtracting `OZFIX.11`'s (`r ≥ 2σ`) closed form `(A(k)/(ik))e^{ikr}(Chat_F(−k) − Chat_F(k))
= residue_term(r,k)/(2πρ)` (whose proof, `integral_Chat_poly_mul_Hterm_pair`, needs **no**
`r ≥ 2σ` — it is valid at every `r`) leaves the **defect**

`D_k = (A(k)/(ik))·∫_{t₀}^σ Chat_poly(t)·[e^{ik(r−t)} − e^{ikσ}]dt`,  `I_k = residue_term(r,k)/(2πρ) + D_k`.

Hence, after the (valid — both sample points are `≥ σ`) interchange,

**`oz_forcing(r) + oz_linear_op[h_explicit](r) = h_explicit(r) + (ρ/r)·Re ∑'ₙ Dₙ(r)`**,

so `hcollapse` on this region ⟺ **`Re ∑'ₙ Dₙ(r) = −2πΦ(r)`**, where
`Φ(r) := −(1/2)∫_{t₀}^σ Chat_poly(t)(σ²−(r−t)²)dt` and `(2πρ/r)Φ(r) = oz_forcing(r)`.

**Reduction to a pointwise series identity.** Substituting `u := r−t` in `Dₙ` gives
`Dₙ(r) = ∫_{r−σ}^σ Chat_poly(r−u)·[Hterm n u − Hterm n σ]du`, so it suffices to have, pointwise:

**(★)  `∑'ₙ [Hterm n u − Hterm n σ] = π(σ² − u²)` for `u ∈ (0,σ]`**

(then `∫_{r−σ}^σ Chat_poly(r−u)·π(σ²−u²)du = −2πΦ(r)` on the nose). **(★)'s content is exactly
the Wertheim–Thiele core closure for the concrete series**: differentiating gives
`∑' h_explicit_term(u) = −2πu ⟺ h_explicit(u) = −1` — *the exterior residue series, continued
into the core, reproduces `h = −1`*. Note `Hterm` is **exactly real** (mirror pairing:
`A(−conj k) = conj(A(k))` ⟹ `residue_term(x,−conj k) = conj(residue_term(x,k))`), so the `Re` is
redundant; verified numerically (`|Im/Re| = 0`).

**Numerically CONFIRMED** (`ozfix12_star_check.py`, scratch; η=0.3, σ=1, 400 Newton-refined poles):
(★) converges to `π(σ²−u²)` at every `u ∈ {0.55, 0.6, 0.7, 0.8, 0.9, 0.99}` — diff `≈ −1.9e−3` at
`N=400`, **halving per doubling of `N`** (the `~1/N` residue tail), e.g. `u=0.8`:
`1.129073` vs target `1.130973`. `∑'Dₙ(r) → −2πΦ(r)` likewise at `r ∈ {1.2, 1.5, 1.8, 1.95}`
(e.g. `r=1.5`: `−1.784173` vs `−1.791203` at N=150, `~1/N`).

**The summability subtlety, and why `Kterm` is needed (a genuine trap).** `‖Hterm n u‖ ≲
‖kₙ‖^{−2u/σ}`, so (★)'s series is absolutely summable **only for `u > σ/2`** — confirmed
numerically (check C: the term slope is `−2u/σ` to two digits at `u = 0.45, 0.3`, i.e.
`−0.90`/`−0.60`, and the partial sums still creep toward the target only conditionally). Stating
(★) as a `HasSum`/`tsum` hypothesis on all of `(0,σ]` would therefore be a **FALSE hypothesis**,
silently making any consuming theorem vacuous — the same class of bug as MA.5's literal-zero-set
and MA.2's ordered-partial-sums traps. Since `u = r−t` reaches down to `r−σ` (arbitrarily close to
`0` as `r ↓ σ`), the `Hterm` form cannot cover the region. **Fix: one more antiderivative.**
`Kterm` (`residue_term` over `(I·k)²`) obeys `‖Kterm n u‖ ≲ ‖kₙ‖^{−1−2u/σ}`, summable for **every**
`u > 0`; integrating (★) from `σ` to `u` gives the equivalent, always-summable

**(★K)  `∑'ₙ [Kterm n u − Kterm n σ − (u−σ)·Hterm n σ] = π(σ²(u−σ) − (u³−σ³)/3)`, `u ∈ (0,σ]`**

recorded in Lean as the predicate **`CoreSeriesClosure`**, with
`coreSeriesClosure_summand_summable` proving its series genuinely converges at every `u > 0`
(i.e. the predicate is non-vacuous — the check the `Hterm` form fails).

**✓ DONE this pass (axiom-clean, `#print axioms` = standard three, builds clean):** `Kterm`,
`Kterm_hasDerivAt` (`Kterm′ = Hterm`), **`Kterm_uniform_summable_bound_of_pole_family`** (the
`OZFIX.4` analogue with threshold `y0 > 0` instead of `y0 ≥ σ` — same `corrOverK`-threading
structure, `σ ↦ y0`, one more power of `‖k‖`), `Kterm_summable_of_pole_family`,
`CoreSeriesClosure`, `coreSeriesClosure_summand_summable`.

**Remaining Lean (mechanical, no new mathematics):** per-pole IBP
`Dₙ(r) = Chat_poly(r−σ)·Kterm n σ − Chat_poly(σ)·Kterm n (r−σ) + ∫_{r−σ}^σ Chat_poly′(t)·Kterm n (r−t)dt
− Hterm n σ·P(r)` (all four pieces absolutely summable for `r > σ`), the `Hterm`-bound interchange
(reuse `OZFIX.11`'s `hasSum_integral_Chat_poly_Hterm` with `max(r−t,σ)` in place of `r−t`), then
`CoreSeriesClosure` + polynomial algebra (the `Kterm σ` and `Hterm σ` terms cancel identically —
checked: `∫_{r−σ}^σ Chat_poly′(t)dt = Chat_poly(σ) − Chat_poly(r−σ)`). Carries `OZFIX.4`'s `hint`
(via the `OZFIX.5` route) — no new hypothesis class.

**Explicitly NOT needed** (all three retracted this pass): the defect-rate hypothesis (false —
`OZFIX.10`), `hcomplete`/`hHbound`/circle-counting data (only the *contour* route needed them, and
that route is circular — `OZFIX.14`), and any Van-der-Corput/arc axiom (the arc blocker is false —
`OZFIX.10`).

---

### Task OZFIX.14 — the circularity: (★) ⟺ core closure; **Group OZFIX cannot retire `oz_core_closure`**

**✗ NEGATIVE RESULT (2026-07-16), recorded so the route is not re-attempted.** The natural way to
prove `OZFIX.12`'s (★) is to close the UHP contour on the pole sum. Doing so **provably cannot
work**, for a structural reason — the contour merely transports the claim from the pole sum to the
*value of a real-line integral of `Ĥ`*, which **is** the core closure.

**The computation.** At a `G_baxter` zero, `ρĈ(k) = 1` (`OZFIX.11`), so `A(k) = k⁷/(ρG(−k)G′(k))`
and `Ĉ` drops out entirely: with `S(z) := 1/(1−ρĈ(z)) = z⁶/(G(z)G(−z))` (so `Res_k S =
k⁶/(G′(k)G(−k))`), each summand becomes `Res_k[S]·(…)/(iρ)` — (★) is a statement about `S` alone:

`(★) ⟺ ∑'_{k ∈ Z_UHP} Res_k[S(z)·Ξ(z)] = −ρ·p(u)`,  `Ξ(z) := (e^{izu}−e^{izσ})/z − i(u−σ)e^{izσ}` (entire).

Now `S = 1 + ρĤ`. On the half-disk contour of pole-avoiding radius `R`:
- the `ρĤ` part's arc → 0 (Jordan + the two-regime split of `OZFIX.10`'s correction), and its
  real-line integral converges absolutely (`Ĥ ~ 1/x²`);
- the `1` part contributes `∫_{−R}^{R}Ξ(x)dx` on the line and `∮Ξ − ∫_{−R}^R Ξ = −∫_{−R}^RΞ(x)dx`
  on the arc (since **`Ξ` is entire**, `∮Ξ = 0`) — they **cancel exactly, at every `R`**.

Hence `2πi·∑'_{k}Res_k[S]·Ξ(k) = ρ·∫_{−∞}^{∞} Ĥ(x)Ξ(x)dx`, i.e.

**(★) ⟺ `∫_ℝ Ĥ(x)·(e^{ixu} − e^{ixσ})dx = −2π²(σ²−u²)`  for `u ∈ (0,σ]`.**

That right-hand side is precisely "the inverse Fourier transform of `Ĥ` equals `−1` on the core" —
the Wertheim–Thiele theorem, i.e. the same mathematical content as the **existing physics axiom
`oz_core_closure`** (`PYOZ_GHS.lean`, stated for the abstract `oz_h`). The contour machinery is
*value-neutral*: it computes the pole sum **in terms of** the core value, never the other way.

**Consequences (structural, and they revise the group's stated goal).**
1. **`hcollapse` is TRUE but not provable inside Group OZFIX's current axiom budget.** It needs the
   core closure as an *input*. The long-standing plan — "OZFIX identifies `oz_h = h_explicit`,
   then a separate **Phase C** retires `oz_core_closure`" (this file's header, `OZFIX.8`) — is
   **impossible via this route**: `hcollapse ⟸ (★) ⟺ core closure`, so Phase C would be circular.
2. **The genuine axiom-free path is real-space Baxter (Wertheim–Thiele), not contours.** The
   Fourier side has been exhausted. `baxter_wiener_hopf_complex` (`OZFIX.2`, proved,
   unconditional) is the Fourier-space half of Baxter's equations — `c ↔ q₀`; the missing half is
   Baxter's second real-space equation `r·h(r) = −q₀′(r) + 2πρ∫₀^σ q₀(t)(r−t)h(|r−t|)dt`, from
   which the core closure for the *specific* PY `q0_poly` follows. The project already has the
   real-space infrastructure (`q0_poly`, `phi_real`, `BaxterRealSpace.lean`). Research-scale.
3. **Swapping the axiom is possible but NOT free — the naive form is FALSE.** (Corrected
   2026-07-16 on review; the first version of this note called it "same count, strictly better
   quality", which was too glib.) Taking (★K)/`CoreSeriesClosure` as the physics axiom *instead of*
   `oz_core_closure` does buy real checkability: it is a statement about the **concrete,
   computable** residue series (verified to `~1/N` with 400 poles) rather than about `oz_h`, which
   is `Classical.choose` of the `oz_fixed_pt_unique` axiom — i.e. the incumbent is *an axiom about
   an object defined by another axiom*, and is only indirectly checkable (one must first solve OZ
   numerically). **But** the obvious axiom
   `… (hkfam_zero) (hkfam_im) (hkfam_re) (hkfam_ne) : CoreSeriesClosure eta sigma rho kfam`
   is **FALSE ⇒ inconsistent**: that pack pins `kfam` only as *some* growth-separated sequence of
   `G_baxter` zeros, so **sub-families satisfy it too**. Verified (η=0.3, σ=1): `kfam' n := k_{2n}`
   satisfies all four (`hkfam_re` explicitly with `c = d = 6`) yet sums to `0.982` at `u = 0.7`
   against target `1.602` (odds: `0.618`; drop-first-5: `0.077`; full family: `1.600`). Third
   instance of this project's recurring false-axiom trap (cf. MA.5, MA.2) — caught *before*
   promotion, by asking what the axiom form would look like.
   **An honest axiom form must carry a completeness bundle**: `Function.Injective kfam`; UHP-zero
   exhaustion up to the mirror pairing (`∀ z, 0 < z.im → G_baxter … z = 0 → ∃ n, z = kfam n ∨
   z = -conj (kfam n)`); and pairing non-degeneracy (`(kfam n).re ≠ 0` — else `k = -conj k` and
   `Hterm`/`Kterm` double-count — and `kfam m ≠ -conj (kfam n)`). **None of these exists in the
   project**: `POLE.8`'s `Qhat_complex_zeros_infinite_unconditional` gives *infinitude*, **not**
   exhaustion. So the real cost of option (b) is: prove exhaustion (a new, non-trivial task — the
   argument-principle/zero-counting route, cf. `MixtureHSCounting.lean`'s analogue) *plus* accept a
   physics axiom whose statement is delicate enough to have been false on the first writing. That
   risk is one the incumbent `oz_core_closure` does not carry. Whether to take the trade is a user
   decision, not made here — but it should be priced with the exhaustion task included.
4. **Option (c) — `oz_core_closure` + radial-Fourier inversion. Now the RECOMMENDED route
   (2026-07-16, after the user asked whether the inversion is axiomatizable).** Chain:
   `oz_core_closure` + `oz_h_satisfies_conv_ext` ⟹ `oz_fourier_oz_eq_of_PY_core` gives
   `radial_fourier(oz_h) = Ĥ`; inversion (`MA.9`) gives `Ψ_oz(u) := ∫_u^∞ s·oz_h(s)ds` from `Ĥ`;
   `OzFixedPt(oz_h)` gives `oz_h = −1` below `σ`, so `Ψ_oz(u) − Ψ_oz(σ) = −(σ²−u²)/2` ⟹ exactly
   this task's `∫_ℝ Ĥ(e^{ixu}−e^{ixσ})dx = −2π²(σ²−u²)` ⟹ (★) (via the contour identity above,
   whose arc now provably vanishes — `OZFIX.10`'s retraction) ⟹ `hcollapse` (via `OZFIX.11` +
   `OZFIX.12`) ⟹ `OZFIX.8`. **Net: `hcollapse` becomes a theorem with NO new axiom** — strictly
   better than option (b). **The inversion should be PROVED, not axiomatized**: Mathlib has
   `MeasureTheory.Integrable.fourierInv_fourier_eq` (`Analysis/Fourier/Inversion.lean:165`), so
   axiomatizing would break Group MA's own discipline (MA.2/MA.4/MA.5 were all retired by
   proving). **⚠ It must be stated in antiderivative (`Ψ`) form** — `𝓕(s·h(s)) ~ k·Ĥ ~ 1/k ∉ L¹`
   (the PY contact jump), so the pointwise inversion's `Integrable (𝓕 f)` hypothesis FAILS; `Ψ`'s
   transform is `~ Ĥ ~ 1/k² ∈ L¹` ✓. Same lesson as `OZFIX.12`'s `Kterm`. Opened as **`MA.9`**;
   see `MATH_AXIOMS.md` ("Candidate REJECTED as an axiom").
5. **Both (b) and (c) additionally need pole-family EXHAUSTION** — opened as **`POLE.10`**. Option
   (c) needs it for the half-disk residue theorem (one must know there are no *other* UHP poles);
   option (b) needs it or its axiom is outright FALSE (see the counterexample in (3)). `POLE.8`'s
   `Qhat_complex_zeros_infinite_unconditional` gives *infinitude*, **not** exhaustion. This is the
   real shared cost of finishing `hcollapse`, and it is now the critical path.

**Status.** ✗ closed as a negative result; supersedes `OZFIX.9`/`OZFIX.10`'s "Route A vs Route B"
framing entirely (both routes are Fourier-side, hence both circular w.r.t. the core closure).
**Scope of the negative result (sharpened by `OZFIX.15`):** it says *Group OZFIX* cannot retire
`oz_core_closure` — i.e. no **Fourier/contour** route can. It does **not** apply to the real-space
Baxter route, which is structurally different (the core value is *definitional* there, not
something the series must reproduce) — see `OZFIX.15`, where Phase C turns out to be **reachable**.

---

### Task OZFIX.15 — real-space Baxter/Wertheim–Thiele: the axiom-free route, seed CONFIRMED

**◑ SEED PROVED IN LEAN, axiom-clean (`baxter_core_seed`, `HardSphere/BaxterRenewal.lean`,
`#print axioms` = standard three, `lake build` green); the route's remaining steps are scoped.**
User-directed 2026-07-16 after `MA.9` was assigned elsewhere. This is `OZFIX.14` option (a), and it
is better than expected: it targets `oz_core_closure` itself (Phase C), which `OZFIX.14` shows the
Fourier side can never reach.

**Why real space is structurally different from `OZFIX.14`'s circularity.** On the Fourier side the
obstruction was that the core value must be *reproduced by the residue series* — (★). In real
space the core value is **definitional**: `oz_operator`'s own `if r < sigma then -1` branch means
`OzFixedPt h ⟹ h ≡ -1` inside, so `ψ(v) := v·h(|v|)` satisfies `ψ(v) = -v` on `(-σ,σ)` for free.
That is what makes the key object explicit rather than unknown.

**Setup (project conventions, verified against the Lean code).** `q0_poly(r) = ρQ′(r-σ) +
(ρQ″/2)(r-σ)²` on `[0,σ]`, `0` outside (`BaxterRealSpace.lean:200`); `Q̂(k) = ∫₀^σ q0_poly(r)e^{-ikr}dr`
(`BaxterZeros.lean:339`). Put `ψ(v) := v·h(|v|)` (odd), `φ(v) := v·c_HS(|v|)` (odd, supported
`[-σ,σ]`), `Q₊ := δ - q0·1_{[0,σ]}` (so `F[Q₊](k) = 1 - Q̂(k)`), `Q₋(r) := Q₊(-r)`. Then the
**already-proved** `baxter_wiener_hopf_complex` (`OZFIX.2`) reads, in real space,

**`ψ ⋆ Q₊ ⋆ Q₋ = φ`**   (the `Q`-product is `k ↔ -k` symmetric, so no convention clash).

Define **`u := ψ ⋆ Q₊`**, i.e. `u(r) = ψ(r) - ∫₀^σ q0(t)·ψ(r-t)dt`.

**The four claims, all checked numerically** (`ozfix15_realspace_check.py`, scratch; η=0.3, σ=1,
300–400 Newton-refined poles; `q0_poly`/`c_HS` transcribed verbatim from the Lean):

| | claim | status |
|---|---|---|
| **D** | `Q̂(kₙ) = 1` at every `G_baxter` zero (and mirror) | ✓ `1e-16`…`1e-13` |
| **B** | `u(r) = r(M₀-1) - M₁` on `(0,σ)`, `M₀ := ∫₀^σ q0`, `M₁ := ∫₀^σ t·q0` | ✓ **`3e-16`** |
| **C** | `(u ⋆ Q₋)(r) = r·c_HS(r)` on `(0,σ)` | ✓ **`5e-15`** |
| **A** | `u(r) = 0` for `r > σ` (the renewal/Volterra equation) | ✓ exactly for `r ≥ 2σ` (`1e-17`…`1e-8` at **any** truncation — see below); inner region = pure truncation, **N-scan run**: at `r = 1.3` the residual is `-7.5e-3 → -3.7e-3 → -1.8e-3 → -9.1e-4` for `N = 50/100/200/400` — **halving per doubling of `N`**, i.e. the `~1/N` residue tail → 0 (same at `r = 1.7`) |

**Why each matters.**
- **D is the real-space collapse factor, and it is strictly more elementary than `OZFIX.11`'s.**
  `Q̂(kₙ) = 1` is *literally* `Qhat_pole_iff_G_baxter_zero` (`BaxterPoles.lean:140`) — no
  Wiener–Hopf, no `Chat_F`/`Chat_J` moment algebra, and **no `heta_def`**. It makes A exact
  per-pole for `r ≥ 2σ`: `∫₀^σ q0(t)·A(k)e^{ik(r-t)}dt = A(k)e^{ikr}·Q̂(k) = A(k)e^{ikr}` — a pure
  algebraic identity holding at *every* `r` and *every* truncation, which is exactly why A's
  `r ≥ 2σ` residual is `1e-17`-level rather than truncation-limited.
- **B is explicit** — it follows from the core value alone (`ψ = -v` on `(-σ,σ)` covers the whole
  sampling range `r-t ∈ (-σ,σ)` when `0 < r < σ`), giving `u(r) = -r + ∫₀^σ q0(t)(r-t)dt =
  r(M₀-1) - M₁`. Pure algebra, no series.
- **C is the Wertheim–Thiele seed and is a pure polynomial identity.** With A and B, `u` is fully
  explicit (linear on the core, `0` beyond), so `(u ⋆ Q₋)(r) = u(r) - ∫₀^{σ-r} q0(t)u(r+t)dt` is a
  polynomial in `r` whose equality with `r·c_HS(r)` involves only `q0`'s coefficients and
  `a0/a1/a3`. **Confirmed to `5e-15`.** This is provable in Lean by exactly the technique already
  used for `baxter_factorization_inner` (`BaxterRealSpace.lean:261`, PROVED: FTC + `field_simp`/
  `ring` after substituting `heta_def`) — that theorem is the *other* half (`c ↔ q`) of the same
  Baxter pair, so the project already owns both the technique and its precedent.

**The route, and its real payoff — Phase C (retire `oz_core_closure`), which `OZFIX.14` rules out
for the Fourier side.**
1. Define `ψ` := `-v` on `(-σ,σ)`, and on `(σ,∞)` as the unique solution of the **Volterra equation
   of the second kind** A (`ψ(r) = ∫₀^σ q0(t)ψ(r-t)dt`, which only ever samples `ψ` on `[r-σ, r]`).
   Existence/uniqueness is standard (Banach on compacts; cf. the project's own
   `Analysis/BanachPoleFamily.lean` machinery).
2. B holds by construction; A holds by construction; **C is the polynomial seed** ⟹ `ψ ⋆ Q₊ ⋆ Q₋ = φ`.
3. ⟹ (via the convolution theorem — the project has the *proved* 3D-radial one,
   `radial_fourier_conv`, `RadialFourier.lean:145` — plus the `3D-radial ↔ 1D-odd` reduction whose
   ingredient `sin_triangle_integral` is also already there) `Ĥ(1-ρĈ) = Ĉ`, i.e. **OZ for all `r>0`**.
4. ⟹ this `ψ/r` satisfies `OzFixedPt` (core branch trivial; exterior branch via the proved
   `oz_forcing_add_linear_op_eq_radial3d_conv`) + regularity ⟹ by `oz_fixed_pt_unique`,
   `oz_h = ψ/r` ⟹ **`oz_core_closure` becomes a THEOREM. Phase C done, axiom retired.**
5. `hcollapse` for `h_explicit` then needs one further step — `h_explicit = ψ/r` on `(σ,∞)`, i.e.
   "the Volterra solution is the residue series" — which is again Fourier/contour content
   (`OZFIX.14` + `MA.9` + `POLE.10`). **So the two routes are complementary, not competing**: real
   space retires the physics axiom; the Fourier side identifies the closed form.

**✓ Claim (A) NOW PROVED (2026-07-17, axiom-clean, *unconditional*): `baxter_psi_volterra_existsUnique`** (`BaxterRenewal.lean`). `MA.10` landed the same day (`Analysis/Volterra.lean`, proved not axiomatized, iterate-bound route), so (A) needed **no**
conditional hypothesis after all — it is a direct instantiation of `volterra_convolution_existsUnique`
at kernel `q := q0_poly` and forcing `g := baxterForcing`, both continuous (`q0_poly_continuous`,
the new `baxterForcing_continuous` via
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`).

*The mapping onto MA.10's shape (the one non-obvious step).* Substituting `s := r - t` turns
`ψ(r) = ∫₀^σ q0(t)ψ(r-t)dt` into `ψ(r) = ∫_{r-σ}^{r} q0(r-s)ψ(s)ds`. Because `q0` is supported in
`[0,σ]` (`q0_poly_outer`), `q0(r-s) = 0` whenever `s < r-σ`, so those samples contribute nothing and
the *core* part can be written **uniformly** as `baxterForcing r := ∫₀^σ q0(r-s)·(-s)ds` — no
`min`/`max`, no case split on `r ≶ 2σ`. The equation is then exactly MA.10's
`ψ(r) = g(r) + ∫_σ^r q0(r-s)ψ(s)ds` with `a = σ`. Free bonus: for `r ≥ 2σ` every sample has
`r - s ≥ σ` ⇒ `baxterForcing ≡ 0`, which *is* claim (A)'s exact `r ≥ 2σ` vanishing (previously only
observed numerically at `1e-17`).

⇒ **`u := ψ ⋆ Q₊ ≡ 0` on `(σ,∞)` holds by construction.** Note this uses **no compactness/Fredholm**:
a one-sided (Volterra) kernel is quasi-nilpotent — precisely why the Baxter factorisation sidesteps
the non-compact half-line Wiener–Hopf obstruction that stalled `OZ.10`.

**✓ Claim (B) PROVED (2026-07-17, axiom-clean): `baxter_u_core`** (`BaxterRenewal.lean`).
For **any** `ψ` carrying the definitional core value `ψ(v) = -v` on `(-σ,σ)`,
`u(r) := ψ(r) - ∫₀^σ q0(t)ψ(r-t)dt = r·(M₀-1) - M₁` on `(0,σ)`. No series, no Volterra solve: for
`0 < r < σ` and `t ∈ [0,σ]` the *entire* sampling range `r-t` lies in `(-σ,σ)`, so `ψ(r-t)` is known
outright; then `intervalIntegral.integral_congr` + linearity + `baxterM0_eq`/`baxterM1_eq` close it.

**Why this matters:** `baxter_core_seed` (C) **hard-codes** the affine `u(v) = v(M₀-1) - M₁` in its
*statement*. (B) is what licenses that hard-coding — it derives the affine form from the definitional
core value. **(B) + (C) together now give `(u ⋆ Q₋)(r) = r·c_HS(r)` for the actual `ψ`**, not merely
for an assumed functional form. Remaining for the `ψ ⋆ Q₊ ⋆ Q₋ = φ` identity: claim (A) — i.e. the
Volterra construction making `u ≡ 0` on `(σ,∞)` *by construction*.

**✓ DONE earlier (Lean, axiom-clean, `HardSphere/BaxterRenewal.lean`, build green).**
`baxterM0`/`baxterM1` (the two `q0_poly` moments, closed forms `-ρQ′σ²/2 + ρQ″σ³/6` and
`-ρQ′σ³/6 + ρQ″σ⁴/24`), their moment lemmas `baxterM0_eq`/`baxterM1_eq` (FTC), and **the seed
`baxter_core_seed`** — `(u ⋆ Q₋)(r) = r·c_HS(r)` on `(0,σ)`, i.e. claim (C), now a theorem.
Closed-form cross-check: at η=0.3, σ=1 the Lean forms give `M₀ = -111/49 = -2.265306` and
`M₁ = -45/49 = -0.918367`, matching the quadrature to all digits.

**Two Lean pitfalls worth recording** (both cost a compile cycle):
1. *Beta-reduction*: `intervalIntegral.integral_congr` leaves goals as `(fun x => …) t = (fun x => …) t`
   whenever the integrand is compound (`t * q0_poly …`), so `rw [q0_poly_inner …]` cannot fire —
   insert `dsimp only []` first (the idiom `baxter_factorization_inner` already uses).
2. *Substitution direction* (the real one): `baxter_factorization_inner` closes by eliminating
   **`eta`** (`simp only [heta_def]` → `field_simp`), but that **fails here**. The moments `M₀`,
   `M₁` are themselves degree-1 in `ρ`, so their products push the denominator up to
   `(6-πρσ³)⁴` — which `field_simp` cannot discharge and leaves as a bare `(1296 - 864x + 216x²
   - 24x³ + x⁴)⁻¹`. Eliminate **`rho`** instead (`hrho_eq : rho = 6·eta/(π·σ³)`): every
   denominator then stays `(1-eta)`-atomic (`M₀ = η(η-4)/(1-η)²` — dimensionless;
   `M₁ = -3ησ/(2(1-η)²)`), and `field_simp` + `ring` closes.

**✓ ALSO DONE this pass — the first bricks of step 3's bridge** (same file, all axiom-clean):
`oddExt g v := v·g|v|` (the odd extension in which Baxter's identity is stated: `ψ = oddExt h`,
`φ = oddExt c_HS`), `oddExt_neg`/`oddExt_of_nonneg`, `integral_oddExt_symm` (an odd function
integrates to `0` over any origin-symmetric interval), and the two payoff lemmas:

* **`integral_shell_eq_oddExt`** — `∫_{|r-t|}^{r+t} s·g(s)ds = ∫_{r-t}^{r+t} g̃(s)ds`. **The
  absolute value disappears.** For `r ≥ t` the integrands agree pointwise; for `r < t` the overhang
  `[r-t, t-r]` is symmetric about `0`, so the odd integrand contributes nothing. `0 ≤ r` is exactly
  what makes the overhang fit (`-(r-t) ≤ r+t ⟺ 0 ≤ r`) — it is not a convenience hypothesis.
* **`radial3d_conv_eq_oddExt`** — for `r > 0`,
  `radial3d_conv f g r = (2π/r)·∫ t in Ioi 0, t·f(t)·∫ s in (r-t)..(r+t), g̃(s) ds`.

This is worth having independently of `OZFIX.15`: the `|r-t|` in `radial3d_conv`'s definition is
precisely what forces the `max`/case-split machinery all through `OZFIX.5`/`OZFIX.11`/`OZFIX.12`,
and this form has none of it. It is also the shape in which the bridge closes: differentiating in
`r` turns the inner `∫_{r-t}^{r+t} g̃` into `g̃(r+t) - g̃(r-t)`, and folding the `t`-integral against
`f̃` gives exactly `-2π·(f̃ ⋆ g̃)(r)` — i.e. **`d/dr[r·(f ⊛₃ g)(r)] = -2π·(f̃ ⋆ g̃)(r)`**, the
1D-convolution identity (cross-checked in Fourier: `F[g̃](k) = -(ik/2π)·radial_fourier(g)(k)` since
`g̃` is odd, so `radial_fourier_conv` gives the multiplier `2πi/k` — an antiderivative, matching).

**The bridge is sound and non-circular** (worth stating, given `OZFIX.14`): `h̃ ⋆ Q₊ ⋆ Q₋ = c̃ ⟺
Ĥ(1-ρĈ) = Ĉ ⟺ OZ` is pure analysis — Wiener–Hopf factorization (proved, `OZFIX.2`) + the
convolution theorem + FT injectivity. No physics input, hence no value-neutrality trap.

**Superseded side-note — the Bielecki weight is NOT needed (recorded so it is not re-attempted).**
While scoping step 1 independently I proved the Bielecki contraction bound
(`∃ λ > 0, ∫₀^σ |q0_poly(t)|e^{-λt}dt < 1`, via `‖q0_poly‖_{∞,[0,σ]} ≤ |ρQ′|σ + |ρQ″|σ²/2` and
`∫₀^σ e^{-λt}dt ≤ 1/λ`). The motivating observation is still worth knowing: **the naive contraction
genuinely fails at physical densities** — the *unweighted* kernel norm is
`∫₀^σ |q0_poly| = |M₀| = 2.265 > 1` at η=0.3, σ=1 — so a direct sup-norm Banach argument on the
renewal operator does not apply, and one is tempted to reach for Bielecki's weight
(= a Laplace shift = the half-plane where the Wiener–Hopf Neumann series `Σ Q̂^m` converges; the
three are one device). **`MA.10`'s iterate-bound route makes all of that unnecessary** — the Volterra
solution is obtained without any weight — so the Lean lemmas were removed again rather than left as
dead code. Keep the observation, drop the machinery.

### Task OZFIX.16 — the `1D-odd ↔ 3D-radial` bridge

**Scope split off from `OZFIX.15` on 2026-07-17** (differently-scoped leftover work gets its own task
number, per the project's proof-notes convention). `OZFIX.15` now covers only the ψ construction
(claims A/B/C ⇒ `ψ ⋆ Q₊ ⋆ Q₋ = φ`); this task turns that real-space identity into OZ.

**Statement (target).** For radial `f, g` (with `f̃ := oddExt f`, `g̃ := oddExt g`):

  `d/dr [ r · (f ⊛₃ g)(r) ] = −2π · (f̃ ⋆ g̃)(r)`   for `r > 0`,

and hence `ψ ⋆ Q₊ ⋆ Q₋ = φ ⟺ Ĥ(1−ρĈ) = Ĉ ⟺ OZ for all r > 0`.

**Already proved (axiom-clean, `HardSphere/BaxterRenewal.lean`).**
- `oddExt g v := v·g|v|`, `oddExt_neg`, `oddExt_of_nonneg`, `integral_oddExt_symm` (an odd function
  integrates to `0` over any origin-symmetric interval).
- **`integral_shell_eq_oddExt`** — `∫_{\|r−t\|}^{r+t} s·g(s) ds = ∫_{r−t}^{r+t} g̃(s) ds`. *The absolute
  value disappears.* For `r ≥ t` the integrands agree pointwise; for `r < t` the overhang
  `[r−t, t−r]` is symmetric about `0`, so the odd integrand contributes nothing. `0 ≤ r` is exactly
  what makes the overhang fit (`−(r−t) ≤ r+t ⟺ 0 ≤ r`) — not a convenience hypothesis.
- **`radial3d_conv_eq_oddExt`** — for `r > 0`,
  `radial3d_conv f g r = (2π/r)·∫ t in Ioi 0, t·f(t)·∫ s in (r−t)..(r+t), g̃(s) ds`.

**Remaining.** Differentiate in `r`: the inner `∫_{r−t}^{r+t} g̃` becomes `g̃(r+t) − g̃(r−t)`; folding the
`t`-integral against `f̃` gives exactly `−2π·(f̃ ⋆ g̃)(r)`. Then either FT injectivity, or —
**preferred** — an injectivity-free real-space projection modelled on **Y1.3**'s re-route
(`proof_notes_yukawa_wh.md`: in real space `{·}^{[R,∞)}` is just `1_{[R,∞)}·`, so the FT-injectivity
difficulty *disappears* and the argument is elementary `Set.indicator`).

**Fourier cross-check.** `F[g̃](k) = −(ik/2π)·radial_fourier(g)(k)` (since `g̃` is odd), so
`radial_fourier_conv` (proved, `RadialFourier.lean:145`) gives multiplier `2πi/k` — an antiderivative,
matching the `d/dr` on the left.

**Non-circular** (worth stating given `OZFIX.14`): `h̃ ⋆ Q₊ ⋆ Q₋ = c̃ ⟺ Ĥ(1−ρĈ) = Ĉ ⟺ OZ` is pure
analysis — the *proved* Wiener–Hopf factorization (`OZFIX.2`) + the convolution theorem + injectivity.
No physics input, hence no value-neutrality trap.

**Independent of `MA.10`** ⇒ can proceed in parallel with the MA session.

**✓ The measure-theoretic half is PROVED (2026-07-17, axiom-clean): `oddExt_conv_fold`**
(`BaxterRenewal.lean`) —

  `∫_ℝ f̃(t)·g̃(r-t) dt = -∫_{Ioi 0} t·f(t)·(g̃(r+t) - g̃(r-t)) dt`.

Split `ℝ = Ioi 0 ⊎ Iic 0` (`MeasureTheory.integral_add_compl` + `Set.compl_Ioi`) and reflect the
negative half by `t ↦ -t` (`integral_comp_neg_Ioi`). On `Ioi 0`, `f̃(t) = t·f(t)`; the reflected half
contributes `f̃(-t)·g̃(r+t) = -t·f(t)·g̃(r+t)`. So the two halves differ **exactly** by the `g̃(r+t)`
vs `g̃(r-t)` sampling — which is the shape that differentiating `radial3d_conv_eq_oddExt`'s inner
shell integral `∫_{r-t}^{r+t} g̃` produces. **No differentiation is used in this half.**

**✓ The analytic half is PROVED (2026-07-17, axiom-clean) — the bridge is COMPLETE:
`hasDerivAt_radial3d_conv_bridge`** (`BaxterRenewal.lean`), stating exactly the target

  `HasDerivAt (fun x => x · radial3d_conv f g x) (−2π · ∫_ℝ f̃(t)·g̃(r−t) dt) r`   for `r > 0`,

assembled from `radial3d_conv_eq_oddExt` (kill the `\|r−t\|`) + brick 2 (move `d/dr` inside) +
`oddExt_conv_fold` (fold two half-lines into one 1D convolution). The two new bricks:

- **brick 1 `hasDerivAt_shell`** — `d/dx ∫_{x−t}^{x+t} φ = φ(r+t) − φ(r−t)` at `x = r`, requiring
  continuity of `φ` **only at the two endpoints** `r ± t`. Both halves are
  `intervalIntegral.integral_hasDerivAt_right` against a common base point `0`, composed with
  `x ↦ x ± t`; the shell is recovered by `integral_interval_sub_left`.
- **brick 2 `hasDerivAt_tIntegral_shell`** — differentiation under the `t`-integral.

**The key choice, and why the obvious lemma is the wrong one.** The physical `g` is `oz_h`, which
**jumps at contact** (`|v| = σ`), so `g̃` is not continuous and no smooth-integrand lemma applies. The
natural-looking `hasDerivAt_integral_of_dominated_loc_of_deriv_le` demands `HasDerivAt` for **all `x`
in a ball** — which is **false here**: for each `t` the shell fails to be differentiable at the
isolated `x` with `x ± t = ±σ`, and *every* ball around `r` catches a positive-measure set of such
`t`, so the hypothesis cannot be met. The right tool is
**`hasDerivAt_integral_of_dominated_loc_of_lip`**, whose `h_diff` is required **only at the base point
`r`, and only for a.e. `t`** — and at fixed `r` just the two values `t = |σ ∓ r|` are bad, a
measure-zero set. Regularity across the ball is carried instead by the **Lipschitz** hypothesis
`h_lip`, which a jump does **not** destroy. *A jump function is differentiable a.e. at a fixed base
point but nowhere-uniformly on a ball; picking the lemma whose hypothesis matches that fact is the
whole content of the analytic half.*

**Hypothesis style.** The domination data (`s`, `bound`, `h_lip`, `hF_meas`, `hF_int`, `hF'_meas`,
`hbound`, `hcont`, `hconv`) is carried as explicit hypotheses (the project's conditional-theorem
pattern, as in `OZFIX.15`(A) pre-`MA.10`). For the FMSA consumers these are dischargeable: `f` is
compactly supported (`q0_poly` on `[0,σ]`) and `g̃` is locally bounded, so `bound t := |t·f t|·2·(sup
|g̃| near r)` works. Helper `intervalIntegrable_of_locallyIntegrable` (`Ι a b ⊆ uIcc a b`, compact)
discharges `radial3d_conv_eq_oddExt`'s `hint` from `hg` alone.

**Lean pitfalls hit.** (i) `₊`/`₋` are **not legal in binder names** (`unexpected token '₊'`) — renamed
to `hcp`/`hcm`. (ii) `HasDerivAt.comp` for `ℝ → ℝ` produces a **different `AddCommGroup` instance
path** (`NormedField.toNormedCommRing.toAddCommGroup` vs `Real.instAddCommGroup`) and the `simpa`
fails on a type mismatch — use **`HasDerivAt.comp_add_const` / `.comp_sub_const`** from
`Analysis/Calculus/Deriv/Shift.lean` instead (same family of trap as the recorded
`HasDerivAt.inv` being `𝕜→𝕜`-only). (iii) `hasDerivAt_integral_of_dominated_loc_of_lip` **whnf-times
out at `isDefEq`** unless `μ`, `bound`, `s`, `x₀`, `F`, `F'` are all supplied **by name**, plus
`set_option maxHeartbeats 1000000` — the same pitfall recorded for `jordan_lemma_arc_bound`.
(iv) `set_option ... in` must precede the **docstring**, not sit between docstring and theorem.

**Remaining for the consumer (`OZFIX.17`), not for this task.** Going from the bridge to OZ needs no FT
injectivity: both sides' `r`-derivatives agree and the antiderivative is pinned, so it is an
**antiderivative argument** in real space (consistent with `MA.9`'s finding that the pointwise-inversion
hypothesis provably fails at a contact jump, and the antiderivative form is the usable one).

**Status:** ✓ **DONE — both halves proved, axiom-clean, `lake build` green.**

---

### Task OZFIX.17 — assembly: `oz_core_closure` becomes a THEOREM (Phase C)

**⚠ RE-SCOPED 2026-07-17, after `OZFIX.15`/`OZFIX.16` closed — this is NOT one task.** Investigating
the actual chain turned up a structural obstacle that the old one-line sketch ("⇒ `Ĥ(1−ρĈ)=Ĉ` ⇒ OZ")
hid, so the leftover work is split into `OZFIX.18`/`OZFIX.19`/`OZFIX.20` below (project convention:
differently-scoped leftover work gets its own task numbers), and `OZFIX.17` shrinks to the final
assembly.

**The obstacle: `Q̂` is a 1D transform, `Ĉ` is a 3D radial one.** The proved factorization
(`OZFIX.2`, `baxter_wiener_hopf_complex`) is `(1 − Q̂(k))(1 − Q̂(−k)) = 1 − ρĈ(k)` with `Q̂ =
Qhat_complex` a **1D** transform of `q0_poly` and `Ĉ = Chat_complex` the **3D radial**
`radial_fourier` of `c_HS`. So `1 − ρĈ(k)` is **not** the transform of `δ − ρ·c̃`, and
`ψ ⋆ Q₊ ⋆ Q₋ = φ` does not become OZ by naive real-space substitution. The two sides differ by the
multiplier `2πi/k` — an **antiderivative** — which is precisely the `d/dr` sitting on the left of
`OZFIX.16`'s bridge. *This is why the old plan's "then FT injectivity or a real-space projection"
was an underestimate.*

**The repair: Baxter's `K` function** (bricks landed 2026-07-17, axiom-clean, `BaxterRenewal.lean`):

  `K(v) := 2π ∫_{|v|}^σ s·c_HS(s) ds`,   `F[K](k) = radial_fourier(c_HS)(k) = Ĉ(k)`

(integrate by parts: the boundary term dies and `(4π/k)∫₀^∞ s·c(s)sin(ks)ds` reappears). Then the
factorization reads, **in real space**, `Q₊ ⋆ Q₋ = δ − ρ·K`, and `ψ ⋆ (δ − ρK) = φ` is
`ψ = φ + ρ·(ψ ⋆ K)` = `r·h(r) = r·c(r) + ρ·r·(c ⊛₃ h)(r)` = **OZ**.

- `baxterK`, `baxterK_neg` (even), **`baxterK_outer`** (`K ≡ 0` off the core — `c_HS` is compactly
  supported, so **no improper integral ever appears**).
- **`hasDerivAt_baxterK`**: `K' = −2π·c̃` on `(0,σ)` — i.e. **`OZFIX.16` is the *differentiated* form
  of what `OZFIX.17` needs**; the two identities differ by an antiderivative and `K` supplies it with
  the constant already pinned (both sides vanish off the core).
- **`v < σ` is not a convenience hypothesis:** `c_HS` **jumps at contact**, so `s ↦ s·c_HS(s)` is not
  continuous and the FTC's `ContinuousAt` genuinely fails at `v = σ`; integrability on `[v,σ]` must be
  routed through an a.e. congruence with the *polynomial* branch (bad set = the single endpoint `σ`).
  Same jump-driven shape as everywhere else on this route.

**Remaining chain (each now its own task).**
1. **`OZFIX.18`** — real-space factorization, **core form ✓ DONE 2026-07-17, axiom-clean**
   (`rho_baxterK_eq_q0_self_conv`): `ρ·K(v) = q0(v) − ∫_v^σ q0(t)·q0(t−v) dt` for `v∈(0,σ)`. This IS the
   `(0,σ)` slice of `Q₊ ⋆ Q₋ = δ − ρK` — the double integral is exactly the convolution
   `(q0·1_{[0,σ]} ⋆ q0(−·)·1_{[−σ,0]})(v)`. **Proof = two FTC evaluations + `field_simp`/`ring` under
   `heta_def`** (NO Fourier, NO injectivity, NO triangle-swap needed — the direct polynomial route beat
   the "integrate `baxter_factorization_inner`" plan): `K(v)=2π∫_v^σ s·c(s)ds` with degree-4
   antiderivative `Gpoly`; `∫_v^σ q0(t)q0(t−v)dt` with degree-5 antiderivative `Fpoly` (5 grouped
   `t`-power coefficients in `α,β,σ,v`); each `HasDerivAt` built by `hasDerivAt_pow` + `.const_mul` +
   `congr_of_eventuallyEq` (bridge the sum-of-lambdas vs single-lambda form, `Pi.add_apply`) +
   `congr_deriv`; `c_HS`'s contact jump handled by `integral_congr_ae` (single-point `∀ᵐ x, x≠σ`), the
   `q0` product is continuous so plain `integral_congr`. **Pre-verified** numerically (5 params to
   `1e-15`) and symbolically (sympy `LHS−RHS ≡ 0` under `heta_def`) before formalizing. **Sub-lemma
   `F[K]=Ĉ` also DONE** (`baxterK_cos_eq_radial_fourier`, above) — the two together give the full
   factorization content. **Remaining for the assembly: convolve this kernel identity with ψ (=OZFIX.20,
   a 2D diagonal-split reindex `∫₀^σ(∫_u^σ q0 q0)(ψ(r−u)+ψ(r+u)) = ∫₀^σ∫₀^σ q0 q0 ψ(r+t−s)`).**
2. **`OZFIX.19`** — the bridge `r·(c_HS ⊛₃ g)(r) = (K ⋆ g̃)(r)`. **✓ DONE 2026-07-17, axiom-clean**
   (`radial3d_conv_eq_baxterK_shell`): `r·(c_HS ⊛₃ g)(r) = ∫₀^σ K(u)·(g̃(r−u)+g̃(r+u)) du` for `r>0`,
   which is `(K ⋆ g̃)(r)` folded onto `[0,σ]` (K even). **MAJOR REALIZATION: this is NOT the
   differentiated identity integrated — it is a straight Fubini.** The earlier plan ("`OZFIX.16` gives
   the `d/dr`, `hasDerivAt_baxterK` gives `K'`, pin the constant") is *avoidable and worse*: a
   differentiate-in-`u` route breaks at the interior point `u = σ−r`, where `g̃ = ψ` **jumps** — but
   Fubini needs only integrability, so it is jump-proof. Proof: expand `K(u) = 2π∫_u^σ s·c(s) ds` on
   `[0,σ]` and swap the `(u,s)` order over the triangle `{0 ≤ u ≤ s ≤ σ}` via the reusable helper
   **`intervalIntegral_triangle_swap`** (`∫₀^a (∫_u^a p) q du = ∫₀^a p·(∫₀^s q) ds`, proved from
   `MeasureTheory.integral_integral_swap` + `Set.Ioi`/`Set.Iio` indicators — also axiom-clean); the
   inner `∫₀^s (g̃(r−u)+g̃(r+u)) du = ∫_{r−s}^{r+s} g̃` by two affine changes of variable
   (`integral_comp_sub_left`/`integral_comp_add_left`), with integrability via
   `IntervalIntegrable.comp_sub_left`/`comp_add_left`. LHS uses `radial3d_conv_eq_oddExt` + a
   `Ioi 0 → [0,σ]` support reduction (`c_HS` compactly supported). Conditional-theorem hypotheses: the
   shell interval-integrability and the triangle joint-integrability, both dischargeable for the
   concrete ψ (locally bounded, one jump). **No FT injectivity, no differentiation, no constant to
   pin.**
3. **`OZFIX.20`** — convolution associativity / the double-integral reindex. **✓ DONE 2026-07-17,
   axiom-clean** (`dbl_conv_reindex`): `∫₀^σ∫₀^σ q0(t)q0(s)ψ(r+t−s) = ∫₀^σ(∫_u^σ q0(t)q0(t−u)dt)·
   (ψ(r−u)+ψ(r+u))` for **any** `ψ` (numerically verified, 3 unrelated `ψ`, `1e-16`). **Both sides
   reduce to `∫ t in 0..σ, ∫ s in 0..t, q0(t)q0(s)(ψ(r+t−s)+ψ(r+s−t))`**: the RHS by the new 2-variable
   triangle Fubini `intervalIntegral_triangle_swap_gen` (generalises `intervalIntegral_triangle_swap` to
   a coupled integrand `f(u,t)`) + the inner change of variable `s=t−u`; the LHS by splitting the inner
   `∫ s in 0..σ` at the diagonal `s=t` and mapping the `{t<s}` half onto `{s<t}` via a **second** `_gen`
   swap (bound-variable relabel) followed by integrand symmetry (`ψ(r+s−t)` vs `ψ(r+t−s)`). Stated with
   6 integrability hypotheses (conditional-theorem pattern, all dischargeable for the concrete
   `baxterPsi`, which is bounded on compacts). **No shear Jacobian** — the relabel + symmetry replaces
   it. This is *the* place associativity is genuinely needed (NOT `OZFIX.15`, left-parenthesised).
4. **`OZFIX.17`** (final assembly) — **⚠ SCOPING RESULT 2026-07-17: the real-space route reaches a
   genuine (non-circular) analytic OBSTACLE at the *boundedness/decay* step; full axiom retirement is
   NOT achievable from the analytic core alone.** Details:

   **The reverse assembly (retires `oz_core_closure`, ~400 lines, decay-free but CONSUMES
   `oz_fixed_pt_unique`).** `oz_h` inherits `OzFixedPt ∧ ContinuousOn (Ici σ) ∧ (∃C, |oz_h|≤C)` from
   the `∃!` (via `Classical.choose_spec … .2.1/.2.2`). So: (i) `oz_h` satisfies OZ on `[σ,∞)`
   (`oz_operator` fixed-point + `oz_forcing_add_linear_op_eq_radial3d_conv`); (ii) push through
   `OZFIX.19`+KDEF+DBL — **with `oz_h`'s LOCAL integrability discharged from its `ContinuousOn`** (the
   renewal at `r` samples `oz_h` on the *bounded* `[r−σ,r]`) — to show `w := r·oz_h` solves the Volterra
   ψ-renewal `w(r)=baxterForcing(r)+∫_σ^r q0(r−t)w(t)dt`; (iii) `baxterPsi` solves the same renewal
   (`baxter_u_outer`), so by **`MA.10` Volterra uniqueness `w = baxterPsi` on `[σ,∞)`** ⇒ `oz_h =
   baxterPsi/·` on `(0,2σ)`; (iv) `OZFIX.15`+KDEF+DBL give `OZ★` for `baxterPsi` at core `r∈(0,σ)`, and
   since the core convolution only samples `(0,2σ)`, `oz_core_closure` follows. **This route needs NO
   global boundedness of `baxterPsi`** — it takes boundedness from `oz_h` (axiom) and gets
   `baxterPsi = r·oz_h` out. But it still *depends on* `oz_fixed_pt_unique`.

   **The two hard inputs blocking a CLEAN (axiom-table-clearing) retirement — both genuine analysis, not
   engineering:**
   - **`oz_h_exterior_regularity`'s decay clause `r·oz_h(r) → 0`** = `baxterPsi(r) → 0`. The crude
     Volterra iterate bound gives only `e^{M(r−σ)}` growth. For `r≥2σ` the forcing vanishes and
     `baxterPsi` solves the **homogeneous** renewal `ψ(r)=∫_{r−σ}^r q0(r−t)ψ(t)dt`, whose decay is
     governed by the roots of `1−Q̂(z)=0` (the Baxter poles). **A simple `L¹` contraction is REFUTED**:
     `∫_0^σ|q0| ≥ 1` for `η ≳ 0.13` (numerically `0.22, 0.48, 1.19, 2.27, 4.0, …` at `η=0.05…0.4`; `q0`
     is single-signed so `∫|q0|=|M₀|`). So decay needs **all poles in the open left half-plane** — the
     `POLE.4`/`h_explicit` spectral content, a substantial separate result (only *existence* of ∞-many
     zeros is proved, `Qhat_complex_zeros_infinite`; their LHP location is not).
   - **`oz_fixed_pt_unique`** needs the Volterra **operator** factorization `(I−K)=(I−K₊)(I−K₋)` (each
     one-sided factor invertible), i.e. the `h_explicit` construction — same spectral core.

   **⇒ CORRECTED SCOPING: the real-space Baxter route removes `OZFIX.14`'s *circularity* (the core value
   is definitional), but it still funnels through the *decay/pole* input at the boundedness step — a
   legitimate, non-circular, but hard analytic result. The "genuinely axiom-free path" claim needs this
   qualification.** Everything up to that input (`OZFIX.15–20`, the entire Baxter factorization
   machinery) IS done and axiom-clean. **All three physics axioms share the single remaining input:
   the LHP location of the Baxter poles (⇔ `baxterPsi` decay).**

**Original notes retained below** (axiom accounting, MA.10 non-blocking) — still accurate.


**Scope split off from `OZFIX.15` on 2026-07-17.**

**Chain.** `ψ ⋆ Q₊ ⋆ Q₋ = φ` (`OZFIX.15`) + the bridge (`OZFIX.16`) ⇒ `Ĥ(1−ρĈ) = Ĉ`, i.e. OZ for all
`r > 0` ⇒ `ψ/r` satisfies `OzFixedPt` (core branch trivial — `ψ = −v` is how ψ is *defined*; exterior
branch via the proved `oz_forcing_add_linear_op_eq_radial3d_conv`) ⇒ by `oz_fixed_pt_unique`,
`oz_h = ψ/r` ⇒ `oz_h ≡ −1` inside ⇒ **`oz_core_closure` retired.**

**Axiom accounting (important).** This *consumes* `oz_fixed_pt_unique` (OZ.10), so on its own it takes
the physics axioms 3 → 2. **But `MA.10` can retire OZ.10 too**: Baxter gives `(I−K) = (I−K₊)(I−K₋)`
with each one-sided factor **Volterra (spectral radius 0) ⇒ invertible with no compactness/Fredholm**
⇒ `(I−K)` invertible ⇒ uniqueness. So one general Volterra theorem serves **both** OZ.9a and OZ.10.
It further unblocks **OZ.3**: `oz_h` stops being an opaque `Classical.choose` object and becomes the
explicit Volterra solution, making `oz_h_exterior_regularity` ordinary real analysis (that axiom's own
docstring names the opacity as the obstruction). **All three physics axioms funnel through this route.**

**Not blocked on `MA.10`.** Like `OZFIX.15`(A), this is completed *conditionally*, carrying the
Volterra existence/uniqueness as an **explicit hypothesis** (`theorem … (hψ : ∃ ψ, core-value ∧
renewal-equation ∧ continuity) : …`) — the project's standard conditional-theorem pattern, distinct
from a bare axiom and cross-listed in `todo_lean.md`'s Conditional-hypotheses table. `MA.10` discharges
it afterwards at the kernel `K(r,t) = q0_poly(r−t)`.

**⚠ Vacuity check** (the project has been burned twice — GAP.8 and IB.4 were `∃`+`rfl` shells whose
content sat entirely in the hypothesis). This is **not** that: the hypothesised ψ is a *different
object* from `oz_h`; its core value is definitional-by-construction, not assumed about `oz_h`; and the
real work (B + C + the bridge + the uniqueness identification) happens between hypothesis and
conclusion. The conclusion `oz_h ≡ −1` is genuinely earned, not restated.

**Depends on:** `OZFIX.15` (A/B/C), `OZFIX.16` (bridge), `oz_fixed_pt_unique` (until `MA.10` retires it).

**Status:** ☐ scoped, not started.

---

### Task OZFIX.21 — axiom CONSOLIDATION (user design, 2026-07-17)

**Motivation.** All three physics axioms (`oz_core_closure`/OZ.9a, `oz_fixed_pt_unique`/OZ.10,
`oz_h_exterior_regularity`/OZ.3) funnel through ONE hard input: the LHP location of the Baxter poles
⇔ decay of the explicit Volterra solution `baxterPsi` (see `OZFIX.17` obstacle analysis; simple `L¹`
contraction REFUTED, `∫_0^σ|q0|≥1` for `η≳0.13`). Two consolidations turn this into progress.

**The linchpin lemma `OZ★` (conditional, decay-FREE — the entire analytic core assembles into it):**

  `baxterPsi(r) = r·c_HS(r) + ρ·r·radial3d_conv(c_HS, fun x => baxterPsi x/x)(r)`   for all `r>0`.

Proof chain (all pieces PROVED, only the integrability side-conditions are hypotheses, discharged
from `baxterPsi` bounded-on-compacts, which follows from `volterraGlobal_continuousOn` + the finitely
many jumps at `±σ` — NO global decay):
- `baxter_psi_conv_eq_phi` : `baxterUQm(r) = r·c_HS(r)`.
- expand `baxterUQm(r) = baxterPsi(r) − Aminus − Aplus + Adouble` (unfold `baxterU`/`baxterUQm` +
  `integral_sub`), where `Aminus=∫₀^σ q0(t)ψ(r−t)`, `Aplus=∫₀^σ q0(t)ψ(r+t)`,
  `Adouble=∫₀^σ∫₀^σ q0(t)q0(s)ψ(r+t−s)`.
- `radial3d_conv_eq_baxterK_shell` (`OZFIX.19`, g=baxterPsi/·, using
  **`oddExt (baxterPsi/·) = baxterPsi`** via `baxterPsi_odd`) : `r·radial3d_conv(c_HS,baxterPsi/·)(r)
  = ∫₀^σ K(u)(ψ(r−u)+ψ(r+u))du`.
- `rho_baxterK_eq_q0_self_conv` (`OZFIX.18`, per-`u` on `(0,σ)`) : `ρK(u)=q0(u)−∫_u^σ q0 q0` ⇒
  `ρ·∫₀^σ K(u)(…) = (Aminus+Aplus) − DoubleTerm`.
- `dbl_conv_reindex` (`OZFIX.20`) : `DoubleTerm = Adouble`.
- ⇒ `ρ·r·radial3d_conv = Aminus+Aplus−Adouble = baxterPsi(r) − r·c_HS(r)` ⇒ `OZ★`. ∎

**✅ OZ★ DONE 2026-07-17 — `baxterPsi_eq_phi_add_rho_conv` (`BaxterRenewal.lean`), axiom-clean
`[propext, Classical.choice, Quot.sound]`, 0 `sorry`, full build green.** Structure exactly as the
chain above, packaged as two `have`s sharing one RHS `E = Aminus+Aplus−Adouble`:
`claimA : baxterPsi r = r·c_HS r + E` (from `baxter_psi_conv_eq_phi` + `unfold baxterUQm baxterU` +
one `integral_sub` for the `Adouble` split + `linear_combination hkey`); `claimB : ρ·(r·radial3d_conv
(c_HS, baxterPsi/·) r) = E` (`radial3d_conv_eq_baxterK_shell` → `simp only [hg_eq]` folds `oddExt` →
`baxterPsi` → `← integral_const_mul` → KDEF `integral_congr_ae` → `integral_sub` split → `hFirst`
(`integral_add`) + `hSecond` (`dbl_conv_reindex.symm`)); close by `rw [claimA, claimB]`.
- **14 integrability hypotheses** (conditional, decay-FREE), = exactly the union of `OZFIX.19`'s
  `hshell`/`hjoint` (stated in `baxterPsi` form, converted to `oddExt` form in-proof via `hg_eq`),
  `OZFIX.20`'s 8, plus 4 for the `integral_sub`/`integral_add` splits (`hAminus`/`hAplus`/`hAdbl`/
  `hKdblH`; `hKq0H` DERIVED from `hAminus.add hAplus`). Dischargeable from `baxterPsi` bounded-on-
  compacts (`volterraGlobal_continuousOn` + finite jumps), NOT decay — a separable follow-up.
- **Lean pitfall:** `intervalIntegral.integral_congr_ae` gives the *implication* ae-form
  `∀ᵐ x, x∈uIoc a b → f x = g x`, NOT `f =ᵐ[volume.restrict (Ι a b)] g` — so the KDEF congr uses
  `rw [Set.uIoc_of_le]; filter_upwards [hne] with u hune hmem` (hmem = the `∈ Ioc` antecedent), NOT
  the `restrict_congr_set Ioo_ae_eq_Ioc` pattern (that is for genuine `=ᵐ[restrict]` goals like
  `baxter_psi_conv_eq_phi`'s `haeA`). The two ae-styles are NOT interchangeable.

**Consolidation B (RECOMMENDED, decay-FREE, net 3→2): merge `oz_core_closure` into
`oz_fixed_pt_unique`.** From `OZ★` + `MA.10`:
1. `oz_h` inherits `OzFixedPt ∧ ContinuousOn (Ici σ) ∧ bounded` from the `∃!`
   (`Classical.choose_spec … .2.1/.2.2`).
2. `oz_h` satisfies OZ on `[σ,∞)` (fixed-point + `oz_forcing_add_linear_op_eq_radial3d_conv`, hyps
   discharged from `oz_h` continuity — LOCAL).
3. **`w := r·oz_h` solves the Volterra renewal** `w(r)=baxterForcing(r)+∫_σ^r q0(r−t)w(t)dt`
   (`OZ★`-machinery applied to `oz_h`; local integrability from continuity).
4. `baxterPsi` solves the same renewal (`volterraGlobal_spec`).
5. `MA.10` uniqueness on each `[σ,b]` ⇒ `w = baxterPsi` ⇒ `oz_h = baxterPsi/·` on `(0,2σ)`.
6. `oz_core_closure` at `r∈(0,σ)`: substitute `oz_h = baxterPsi/·` (conv samples only `(0,2σ)`) +
   `OZ★` for `baxterPsi` at core (`ψ(r)=−r`) ⇒ `−1 = c_HS(r)+ρ·radial3d_conv(c_HS,oz_h)(r)`. ∎
   ⇒ `oz_core_closure` becomes a THEOREM depending only on `oz_fixed_pt_unique` + the core. **Net 3→2,
   no decay.** Cost: ~350 lines (`OZ★`-machinery applied to BOTH `oz_h` [step 3] and `baxterPsi`
   [step 6] + the renewal-match plumbing).

**Consolidation A (net 3→1): axiomatize ONLY the decay.** Introduce one explicit, numerically-checkable
axiom `baxter_exterior_decay` about **`baxterPsi`** (bounded on `[σ,∞)`, `→0`, differentiable,
`IntegrableOn (Ioi σ)`) — strictly better epistemically than the three opaque `Classical.choose`-`oz_h`
axioms it replaces. Then:
- `oz_fixed_pt_unique`: **existence** = `baxterPsi/·` is a bounded (from the axiom) continuous
  (`volterraGlobal_continuousOn`) `OzFixedPt` (from `OZ★`); **uniqueness** = decay-FREE (two bounded
  cont. fixed points ⇒ difference `d` has `d=0` inside + solves the *homogeneous* Volterra renewal on
  `[σ,∞)` ⇒ `d=0` by `MA.10`). ⇒ `oz_fixed_pt_unique` a THEOREM.
- `oz_h = baxterPsi/·`; `oz_core_closure` from `OZ★`; `oz_h_exterior_regularity` from the axiom's
  decay/integrability clauses (now about the explicit `baxterPsi`).
Cost: `OZ★` + uniqueness + 3 derivations, ~500 lines. **Deletes all 3 physics axioms, adds 1.**

**Recommendation:** do B first (unconditional, real 3→2), then A (adds the single decay axiom, reaching
3→1 with the residual being one *explicit* hypothesis). **Immediate next lemma = `OZ★`** (the shared
linchpin). First brick landed: `oddExt_div_self_eq_baxterPsi`.

**Status:** ✅ `OZ★` (`baxterPsi_eq_phi_add_rho_conv`) + brick `oddExt_div_self_eq_baxterPsi` DONE,
axiom-clean (2026-07-17). Next: Consolidation B (retire `oz_core_closure` via reverse assembly, ~350
lines, decay-free), then Consolidation A (single explicit `baxter_exterior_decay` axiom, 3→1).

### Task OZFIX.22 — axiom CONSOLIDATION executed: RETIRE `oz_core_closure` + `oz_h_exterior_regularity` (net 3→2)

**DONE 2026-07-17. Full build green (8653 jobs), no import cycles.** New file
`HardSphere/OzCoreClosure.lean` (+ edits to `PYOZ_GHS.lean`, `OZFourierBridge.lean`,
`JumpAsymptotic.lean`).

**Result — the three OZ physics axioms `{oz_fixed_pt_unique, oz_core_closure,
oz_h_exterior_regularity}` become `{oz_fixed_pt_unique, baxter_exterior_regularity}`:**
- **`oz_core_closure` RETIRED** → `theorem oz_core_closure` in `OzCoreClosure.lean` (axiom deleted from
  `PYOZ_GHS.lean`). `#print axioms` = `[propext, Classical.choice, Quot.sound,
  baxter_exterior_regularity, oz_fixed_pt_unique]`.
- **`oz_h_exterior_regularity` RETIRED** → `theorem` in `JumpAsymptotic.lean`, same footprint.
- **`oz_fixed_pt_unique` KEPT** — irreducibly Wiener–Hopf.
- **`baxter_exterior_regularity` NEW** — one explicit axiom about the *constructed* `baxterPsi`,
  epistemically superior to the two opaque-`oz_h`/physics axioms it replaces.

**The mechanism — everything routes through ONE bridge `oz_h = baxterPsi/·`:**
1. `radial3d_conv_cHS_congr` (decay-free brick): `radial3d_conv (c_HS) g r` depends on `g` only on
   `Ioo 0 (r+σ)` (`c_HS` supported `[0,σ]`, shell `⊆ [0,r+σ)`, `s=0` killed by the `s`-factor).
2. `oz_core_closure_of_bridge` (decay-free): closure `= OZ★ ⊘ r + bridge` (via (1)).
3. `ozBaxterFixedPt := fun r => if r<σ then -1 else baxterPsi r/r`; `ozBaxterFixedPt_eq_div`
   (`= baxterPsi/·` on `(0,∞)`, core `-1 = baxterPsi/·` by `baxterPsi_core`).
4. **The bridge `oz_h_eq_ozBaxterFixedPt : oz_h = ozBaxterFixedPt`** by `oz_fixed_pt_unique.unique`:
   `ozBaxterFixedPt` is a bounded (from decay axiom), exterior-continuous (`baxter_exterior_regularity`
   continuity clause) `OzFixedPt` — the exterior fixed-point equation is
   `oz_forcing_add_linear_op_eq_radial3d_conv` (bridge lemma) → `ρ·radial3d_conv(c_HS,ozBaxterFixedPt)`
   → (domain-congruence to `baxterPsi/·`) → OZ★⊘r → `baxterPsi r/r`. Since `oz_h` is *the* unique such
   fixed point, `oz_h = ozBaxterFixedPt`.
5. `oz_core_closure` = `oz_core_closure_of_bridge` fed the bridge + OZ★.
6. `oz_h_exterior_regularity` = **one `rw [oz_h_eq_ozBaxterFixedPt]`** (function equality rewrites the
   ENTIRE existential bundle `oz_h → ozBaxterFixedPt` at once) + the matching
   `baxter_exterior_regularity` clause. This is why the ~30-line regularity bundle transports in two
   tactic lines.

**Why NOT decay-free / why only 3→2 (definitive finding, corrects OZFIX.21's designs):**
- The bridge needs `oz_h` = *the* unique bounded fixed point (`oz_fixed_pt_unique`) matched to
  `baxterPsi/·`, which needs `baxterPsi` **bounded on `[σ,∞)`** = exterior **decay**. Not removable.
- **Bounded uniqueness of the OZ operator is irreducibly Wiener–Hopf**: `∫_0^σ|q0| ≥ 1` for `η≳0.13`
  ⇒ no `L¹`/sup contraction; the difference of two bounded fixed points solves a NON-causal
  homogeneous integral equation whose only-zero-solution property IS the pole-in-LHP spectral fact.
- **The OZFIX.21 "decay-free 3→2 merge" (Consolidation B) was WRONG:** converting the OZ convolution
  equation `h = ρ·radial3d_conv(c_HS,h)` to the *causal* Baxter renewal `w = ∫_0^σ q0 w(r-t)` for a
  **general** fixed point requires the Wiener–Hopf factorization (the two-sided/anti-causal `⋆Q₋`
  step), NOT just the general `OZFIX.18/19/20` machinery (which gives a two-sided form `g̃(r) =
  ∫q0(g̃(r-u)+g̃(r+u)) − double`, equivalent to the causal renewal only *given* the renewal —
  circular). So `w=r·oz_h` solving the renewal is not free; the decay axiom + `oz_fixed_pt_unique`
  route is the honest one.
- **The OZFIX.21 "3→1" (Consolidation A) was also over-optimistic:** its "uniqueness is decay-free"
  claim fails — two bounded fixed points' difference solves the non-causal `d = ρ·radial3d_conv(c_HS,d)`,
  not a homogeneous *causal* Volterra, so `MA.10` does not apply; uniqueness stays Wiener–Hopf.

**Lean notes:** (i) `radial3d_conv_cHS_congr` via nested `setIntegral_congr_fun` (Ioi then Icc),
`s=0` case by `s*g=0`. (ii) The bridge as a **function equality** makes `oz_h_exterior_regularity`'s
transport a single `rw` — key architectural win (had it been only a pointwise `∀s, oz_h s = …` the
existential bundle would have needed clause-by-clause `congr`/`Integrable.congr`). (iii) `oz_h` as
`Classical.choose (…).exists` + `(oz_fixed_pt_unique …).unique` for the identification.
(iv) `div_le_div_iff` renamed in the pinned Mathlib → used `one_div_le_one_div_of_le` + `mul_le_mul`.
(v) No cycle: `JumpAsymptotic` already transitively imports `OzCoreClosure` (via `OZFourierBridge`,
which now imports it for the relocated `oz_core_closure`).

### Task OZFIX.23 — Route 3 (operator-level from the concrete Baxter factorization): WHERE IT WALLS

**Investigated 2026-07-17 (numerics: `verify_wienerhopf_wall.py`).** Route 3 = derive
`oz_fixed_pt_unique` (bounded OZ fixed-point uniqueness, the sole surviving OZ physics axiom) from the
**already-proved** concrete Baxter factorization `baxter_wiener_hopf_complex`
(`1−ρĈ(k) = (1−Q̂(k))(1−Q̂(−k))`, i.e. `I−ρK = (I−K₊)(I−K₋)`, each factor one-sided/Volterra).

**The reduction (decay-free, elementary):** two bounded exterior-continuous fixed points, difference
`d` (=0 on core, `d = ρ·radial3d_conv(c_HS,d)` on the exterior); with `d̃ := oddExt d`, the
factorization gives `(d̃⋆Q₊)⋆Q₋ = 0`. Put `u := d̃⋆Q₊`; then `u⋆Q₋ = 0`, i.e. the **anti-causal**
homogeneous renewal `u(r) = ∫₀^σ q0(t)·u(r+t)dt`. Sup-norm: `|u(r)| ≤ (∫₀^σ|q0|)·sup|u| = M·sup|u|`.
If `M<1` and `u` bounded ⇒ `u≡0`; then `d̃⋆Q₊=0` is the **causal** renewal
`d̃(r)=∫₀^σ q0(t)d̃(r−t)dt`, same constant `M` ⇒ `d̃≡0` ⇒ `d≡0`.

**⇒ Route 3 proves bounded uniqueness IFF `M := ∫₀^σ|q0| < 1`.  THE WALL is exactly `M(η)=1`.**

**Closed form (this is the payoff):** with `q0` the PY Baxter polynomial (`BaxterRealSpace.lean`,
`q_prime_py`/`q_doubleprime_py`, `η=πρσ³/6`),
$$M(\eta)=\int_0^\sigma|q0| = \frac{\eta(4-\eta)}{(1-\eta)^2},$$
verified against numerics + the recorded `∫|q0|` values (0.22/0.48/1.19/2.27/4.0 at
η=0.05/0.1/0.2/0.3/0.4). `M(η)=1 ⟺ 2η²−6η+1=0 ⟺ η⋆ = (3−√7)/2 ≈ 0.17712`.

**So Route 3 walls at `η⋆=(3−√7)/2≈0.177`** — it does **reach further** than the naive OZ-operator sup-
norm (`oz_fixed_pt_unique_dilute`'s `T_ext_K=1` at η≈0.088), because the Volterra factors use the
tighter renewal-mass `∫|q0|`, but it **still caps well below `η=1`**. Above `η⋆`, `M>1` and the sup-
contraction fails at BOTH the causal and anti-causal step (anti-causal on the half-line has no initial
condition; causal solutions grow like `e^{(∫|q0|)r}` by Grönwall — boundedness is not preserved).

**The wall is a proof-TECHNIQUE wall, not a falsity:** the symbol `1−ρĈ(k)` stays strictly positive for
all `k` and all `η<1` (numerically: `min_k(1−ρĈ) = 0.80/0.66/0.49/0.40` at η=0.2/0.3/0.4/0.45;
`1−ρĈ(0)=(1+2η)²/(1−η)⁴` = PY inverse compressibility, large; no spinodal). Indeed the Lean lemma
`baxter_wiener_hopf_complex_real` already gives `1−ρĈ(k) = |1−Q̂(k)|² ≥ 0` structurally. So uniqueness
holds for every physical `η`; the missing step above `η⋆` is precisely the **Wiener–Hopf/Krein spectral
inversion** ("nonvanishing symbol with winding number 0 ⇒ `I−ρK` invertible"), NOT more elementary
algebra. That is a citable classical theorem (Krein 1958; Gohberg–Krein; Böttcher–Silbermann) absent
from Mathlib ⇒ candidate for a **Group MA** axiom (`MA.krein_wiener_hopf`, see `MATH_AXIOMS.md`); its
hardest hypothesis (symbol nonvanishing, index 0) is ≈free here via `|1−Q̂|²`, but the L^p↔bounded-space
bridge re-introduces the same exterior decay, so it upgrades `oz_fixed_pt_unique`'s pedigree (domain
claim → classical theorem) rather than removing the decay content. **Conclusion: `oz_fixed_pt_unique`
is irreducibly Wiener–Hopf; Route 3's elementary reach is exactly `η<(3−√7)/2`.**

### Task OZFIX.24 — RETIRE `ozExterior_triple_shell_sin_integrable` (6h): axiom → theorem

**✓ DONE 2026-07-19, full build green (8675 jobs), no new axiom, no `sorry`.**
`BaxterExteriorConvIntegrable.lean`; the `axiom` keyword is deleted, name and signature unchanged, so
no consumer edit was needed.

**Why it was the right target.** The axiom's own docstring called it "a pure absolute-convergence
(Tonelli) fact", gave the complete proof sketch, and justified the axiomatization as *"formalizing
the triple `lintegral` chain from Mathlib primitives is substantial."* That is an **effort argument,
not a gap argument** — in direct tension with Group MA admissibility rule (c) (anything derivable
from existing Mathlib is split off as a genuine theorem). Same category as MA.10/11/12, all retired
by proving. It had also just got easier: the third ingredient (exterior `L¹`) is now supplied by
MA.13's strengthened `IntegrableOn` (`baxterPsiOuter_integrableOn`). Abstracting a side condition
would have been the wrong move; proving it was the right one. **The sketch was correct** — unlike
MA.2/MA.5/MA.4, no statement bug surfaced.

**The proof, in four named steps.**

1. **`volume_ozShell_slice_le`** (axiom-clean, standard three only) — the shell-slice length estimate.
   `{a : |a−t| ≤ s ≤ a+t} ⊆ Icc |s−t| (s+t)`: unfolding `abs_le`, `s ≤ a+t` gives `s−t ≤ a` and
   `−s ≤ a−t` gives `t−s ≤ a`, i.e. `|s−t| ≤ a`; `a−t ≤ s` gives the upper end. `Real.volume_Icc`
   then gives length `s+t−|s−t| = 2·min(s,t) ≤ 2t`, the last step needing only `s−t ≤ |s−t|`
   (`le_abs_self`) — **no positivity hypothesis on `s`,`t` is required**.
2. **`lintegral_shell_weight_c_HS_lt_top`** — the `t`-side factor `∫_t 2t·‖t·c_HS t‖ₑ < ∞`. Dominate
   by `(Ioc 0 σ).indicator (const)`: for `t ≥ σ` the integrand is `0` (`c_HS_outer`), for `0 < t ≤ σ`
   it is `≤ 2σ·(σ·C)` (`c_HS_bddOn`). Then `lintegral_indicator` + `setLIntegral_const` +
   `measure_Ioc_lt_top`.
3. **`r_mul_ozBaxterFixedPt_integrableOn_Ioi_zero`** — the `s`-side factor, `IntegrableOn (s·ozBFP s)
   (Ioi 0)`. Core `(0,σ]`: `Measure.integrableOn_of_bounded` with `M := σ·C` from
   `ozBaxterFixedPt_bounded` on a finite-measure set. Exterior `(σ,∞)`:
   `r_mul_ozBaxterFixedPt_integrableOn` (= MA.13's strengthened `IntegrableOn`). Glue with
   `IntegrableOn.union` + `Set.Ioc_union_Ioi_eq_Ioi`.
4. **`lintegral_ozShellMajorant_lt_top`** — assembly. `lintegral_prod_symm` puts the `a`-integral
   **innermost**; there the majorant is `(Set.indicator (slice) (const C(t,s)))`, so
   `lintegral_indicator` + `setLIntegral_const` evaluate it to `C(t,s)·volume(slice) ≤ C(t,s)·2t`
   by step 1. Rearranged to `f(t)·g(s)` and split by `lintegral_prod_mul` into the product of
   steps 2 and 3; `ENNReal.mul_lt_top` finishes.

The main theorem then dominates the 6h integrand by `ozShellMajorant` — `sin` dropped via
`|sin(ka)| ≤ 1`, and the `Icc |a−t| (a+t)`-indicator in the `s`-variable re-read as the shell region
`ozShellRegion ⊆ ℝ×ℝ×ℝ` constraining `a` (the two membership conditions are *literally the same
conjunction*, so a single `by_cases` on `s ∈ Icc …` handles both indicators at once) — and applies
`lintegral_mono` through `hasFiniteIntegral_iff_enorm`.

**⚠ The `a`-innermost swap is the whole trick.** Taken in the measure's own nesting
(`μ_a.prod (μ_t.prod μ_s)`), Tonelli puts the **unbounded** `a`-axis *outermost* and the estimate
does not close — there is no finite `a`-factor to extract. `lintegral_prod_symm` (α := ℝ for `a`,
β := ℝ×ℝ for `(t,s)`) is what converts the shell constraint from an indicator into a *measure*, which
is where the finite `2t` comes from. Anyone re-deriving this in the matrix/mixture setting should
start here.

**Two small `def`s were introduced** (`ozShellRegion`, `ozShellMajorant`) rather than inlining the
set and the majorant three times; both are content-named, carrying no task number, per
`CONVENTIONS.md`.

**Ledger.** `#print axioms ozExterior_triple_shell_sin_integrable` → standard three +
`volterra_renewal_tendsto_zero` (MA.13) + `baxter_no_open_lhp_pole_core` (MA.14). Both are
**pre-existing upstream** axioms, reached only through step 3's exterior-`L¹` ingredient;
`ozExterior_conv_sin_integrable` (6j) has the identical list, so **no downstream footprint grew**.
Math axioms `10 → 9`; physics axioms stay at `0`. The exterior OZ integrability cluster (6g/6h/6j) is
now **entirely axiom-free**. Note the `todo_lean.md` header had been **stale at 9 while the table
listed 10 rows** (the earlier 7a/7b split was never added to the count) — it is now genuinely 9.

**Remaining in the OZFIX/exterior cluster:** only `ozExterior_smooth_repr` (7a) and
`ozExterior_deriv_integrable` (7b), both discharged by (★DIFF), the differentiated renewal.

### Task OZFIX.25 — (★DIFF): the differentiated renewal ⇒ retire BOTH split axioms 7a/7b

**Goal.** Prove the differentiated renewal equation, for `r > σ`:

  `ψ'(r) = baxterForcing'(r) + q0(0)·ψ(r) + ∫_σ^r q0'(r−t)·ψ(t) dt`        **(★DIFF)**

(`ψ := baxterPsiOuter`, from `baxterPsiOuter_spec`). **(★DIFF) retires BOTH halves of the OZFIX.22
split at once** — `ozExterior_smooth_repr` (7a) and `ozExterior_deriv_integrable` (7b),
`OzExteriorSmooth.lean` — so it is worth strictly more than relocating or abstracting either.

**Why both follow.**
* **7a** — RHS of (★DIFF) is continuous ⇒ `ψ` is `C¹` on `[σ,∞)` ⇒ `ψ/·` is `C¹` there (`r ≥ σ > 0`);
  take `g` := that, extended **linearly** below `σ` (tangent line at `σ`) ⇒ `g` is `C¹` *across* `σ`,
  which is exactly 7a's `∀ r ∈ Ici σ, HasDerivAt g (g' r) r`.
* **7b** — `g + r·g' = (r·g)' = ψ'` on `(σ,∞)`; each (★DIFF) summand is `L¹(Ioi σ)`:
  `baxterForcing'` is compactly supported (`baxterForcing = 0` for `r ≥ 2σ`,
  `baxterForcing_eq_zero_of_two_sigma_le`); `q0(0)·ψ` is `L¹` because **`IntegrableOn ψ (Ioi σ)` is
  ALREADY PROVEN** (`baxterPsiOuter_integrableOn`, from MA.13's strengthened conclusion); and
  `q0' ⋆ ψ` is `L¹` by Young (compactly-supported bounded `q0'`).

**Progress — step 1 of 6 DONE (2026-07-19, axiom-clean, `BaxterKernelDeriv.lean`).**
1. ✅ **Kernel derivative.** `hasDerivAt_phi2_real` (**`phi2_real` is differentiable EVERYWHERE with
   derivative exactly `phi1_real`** — including at `σ`, where both one-sided slopes vanish; so
   `phi2_real` is `C¹`, not `C²`), `hasDerivAt_phi1_real_of_ne` (`phi1_real` has a genuine **kink** at
   `σ`: left slope `1`, right slope `0`), `q0PolyDeriv` (def), `hasDerivAt_q0_poly_of_ne`,
   `q0PolyDeriv_eq_zero_of_gt`. ⇒ **`q0_poly` is differentiable exactly off the single point `σ`.**
   That point is `volume`-null (harmless inside (★DIFF)'s integral) **but it forces the Leibniz step
   to use the Lipschitz/dominated form, not a naive "differentiate under the integral".**
2. ◑ `baxterForcing'` — `baxterForcing r = ∫_0^σ q0(r−s)·(−s)ds` has **fixed** limits, so this is the
   pure parameter-differentiation case of MA.16. **The general lemma is now available**
   (`hasDerivAt_intervalIntegral_param`, stated with an *arbitrary* upper limit `b` precisely so it
   covers this fixed `[0,σ]` window as well as step 3); what remains here is instantiating it —
   `LipschitzOnWith` for `q0_poly` on a compact window + `Measurable q0PolyDeriv` — plus the compact
   support.
3. ✅ **The Leibniz lemma (MA.16) — DONE 2026-07-19, PROVED, axiom-clean**
   (`Analysis/ConvolutionLeibniz.lean`, `hasDerivAt_intervalIntegral_convolution`): variable upper
   limit **and** `r`-dependent integrand, for a kernel differentiable only **a.e.**.
   **Route taken, and why it differs from the plan.** The spec suggested `r ↦ (r,r)` + a 2-variable
   chain rule; that needs *joint* differentiability of `(x,y) ↦ ∫_a^y K(x−t)φ`, which does **not**
   follow from the two partials for free. Splitting at the base point instead —
   `∫_a^r = ∫_a^{r₀} + ∫_{r₀}^r` — reduces it to two independent single-variable facts, and is what
   made the proof routine. The moving-endpoint half then needs **no** ε-δ uniform-continuity
   argument: subtracting the constant `K 0` leaves a remainder bounded by `C·M·|x−r₀|²` using the
   **same** Lipschitz hypothesis the parametric half already requires, so the whole lemma runs on a
   single regularity assumption.
   **⚠ Statement trap found by smoke-testing before closing** (the discipline that caught bugs 1–4 in
   `MATH_AXIOMS.md`): the general lemma needs `Continuous φ`, but `baxterPsiOuter` **jumps at `σ`**
   (it is `0` below `σ`, while `ψ(σ) = baxterForcing(σ) ≠ 0`). The consumer must therefore pass the
   clamped representative `fun r => baxterPsiOuter (max r σ)` — the pattern already in
   `BaxterOzStar.lean` — and transfer back with `HasDerivAt.congr_of_eventuallyEq`, which is legitimate
   only for `r₀ > σ` **strictly**. This is not a defect: (★DIFF) is wanted on the open exterior
   `(σ,∞)` anyway. A verified smoke test (kernel `q0_poly`, derivative `q0PolyDeriv`, clamped `ψ`)
   confirms the interfaces compose, leaving exactly the two consumer-side side conditions named in
   step 2.
4. ☐ Assemble (★DIFF) from 2+3 via `baxterPsiOuter_spec`.
5. ☐ Derive 7a (construct `g`, linear extension below `σ`, `C¹` across).
6. ☐ Derive 7b (the three summands, as above).

**Lean pitfalls already hit and solved (step 1).** `HasDerivAt.const_mul` resolves to the
`RCLike.toInnerProductSpaceReal.toModule` instance path ⇒ **give the `have` an explicit type** to pin
the standard `ℝ` instance, else a `Type mismatch` on the module argument. `filter_upwards` yields
`x ∈ Iio σ` (a membership), not the inequality ⇒ `mem_Iio.mp` / `mem_Ioi.mp`. `hasDerivAt_id` produces
`id x` ⇒ `simp` needs `id_eq`. Gluing a two-sided derivative from one-sided ones:
`HasDerivWithinAt.union` + `Iic_union_Ici` + `hasDerivWithinAt_univ`.

**OZFIX.25 progress update (2026-07-19): steps 1–5 DONE; axiom 7a RETIRED.**
Full build green (8681 jobs), zero `sorry`.
1. ✅ kernel derivative (`BaxterKernelDeriv.lean`) + the `MA.16`-hypothesis feeders: closed forms
   `phi1_real = min r σ − σ` and **`phi2_real = phi1_real²/2`** (the reason `phi2_real` is `C¹` while
   `phi1_real` kinks), `lipschitzWith_phi1_real`, `q0_poly_lipschitzOnWith`, `q0PolyDeriv_measurable`,
   `hasDerivAt_q0_poly_ae`.
2. ✅ `hasDerivAt_baxterForcing` (`BaxterForcingDeriv.lean`) — fixed limits ⇒ `MA.16`'s
   `hasDerivAt_intervalIntegral_param`, first try.
3. ✅ `MA.16` (parallel session) — **verified**: 0 `sorry`, builds, all three results axiom-clean, and
   its `hK' : ∀ᵐ u, HasDerivAt K (K' u) u` is the a.e. form `q0_poly`'s kink needs.
4. ✅ **(★DIFF)** `hasDerivAt_baxterPsiSmooth` (`BaxterRenewalDiff.lean`).
5. ✅ **7a `ozExterior_smooth_repr` RETIRED → theorem** (`ozExterior_smooth_repr_proved`).
6. ☐ **7b `ozExterior_deriv_integrable` — REMAINS.** Reduces to `IntegrableOn baxterPsiSmoothDeriv
   (Ioi σ)`, i.e. the three (★DIFF) summands: `baxterForcing'` (vanishes for `r > 2σ` by
   `q0PolyDeriv_eq_zero_of_gt` ⇒ compact support), `q0(0)·ψ` (**`baxterPsiOuter_integrableOn` already
   proven**), and `q0' ⋆ ψ` (Young). ⚠ **Blocked by an import-layering tangle, not just the estimate**:
   `baxterPsiOuter_integrableOn` lives in `BaxterExteriorRegularityGeneral`, which is *downstream* of
   `OzExteriorSmooth` (via `BaxterRenewalDecay → BaxterDiluteDecay → OzCoreClosure`), while 7b is
   *declared* in `OzExteriorSmooth`. Retiring it needs either moving the 7b statement downstream or
   lifting `ozBaxterFixedPt`/ψ-integrability upstream. **Do the layering first, then the Young step.**

**Key design win (worth reusing).** `ψ̃ := ψ ∘ (max · σ)` gives `MA.16`'s *globally* continuous `φ`
(`ψ` itself jumps at `σ`), and `Ψ := baxterForcing + Φ` is differentiable **including at `σ`
two-sidedly** precisely because it is stated for `Ψ`, not `ψ`. That is the clean repair of the false
clause 6a. Lean pitfalls (recurring): `HasDerivAt.div`/`.const_mul` pick a non-standard module
instance ⇒ pin with an explicit `have` type; `abs_add` is `abs_add_le`; `le_or_lt` is `le_or_gt`;
`LipschitzWith.sub_const` absent ⇒ compose; beta-redexes after `refine ⟨…⟩` ⇒ `show`.

### Task OZFIX.26 — OZ/Baxter layering: lift the OZ veneer out of the Baxter analysis files

**Problem (measured 2026-07-19).** The layering is *inverted*: pure Baxter real-analysis files import
the OZ-flavoured `OzBaxterFixedPt` and state their results in OZ terms, although the mathematics is
entirely about `baxterPsi`/`baxterPsiOuter`. Files importing `OzBaxterFixedPt`: `BaxterDiluteDecay`,
`BaxterExteriorDecayReduction`, `BaxterExteriorDerivBundle`, `BaxterExteriorIntegrability`,
`BaxterExteriorConvIntegrable` (+ legitimately `OzCoreClosure`).

**Why it is cheap to fix.** The Baxter-named counterparts **already exist**, so the OZ-named results
are thin wrappers over them, generated by the single translation `r · ozBaxterFixedPt r = baxterPsi r`
(`r > 0`, from `ozBaxterFixedPt_eq_div`):

| already-existing Baxter form | OZ wrapper to lift |
|---|---|
| `baxterPsiOuter_tendsto_zero` | `r_mul_ozBaxterFixedPt_tendsto_zero` |
| `baxterPsiOuter_integrableOn` | `r_mul_ozBaxterFixedPt_integrableOn` |
| `baxterPsi_bounded_Ici` | `ozBaxterFixedPt_bounded` |
| `baxterPsi_bounded_Ici_of_dilute` | `r_mul_ozBaxterFixedPt_tendsto_zero_of_dilute` (+ `_of_eta_dilute`) |
| `baxterPsi_bounded_Ici_of_tendsto_zero` | `r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero` |

Only **5 signatures each** in `BaxterExteriorIntegrability` / `BaxterExteriorConvIntegrable` are
OZ-stated (the 35/53 raw mentions are overwhelmingly inside proof bodies); those need a Baxter-term
restatement, everything else is a move.

**Target layering.**
```
Layer B — pure Baxter analysis, NO `oz*` anywhere:
  BaxterRenewal
  BaxterKernelDeriv / BaxterForcingDeriv / BaxterRenewalDiff      ← already OZ-free (OZFIX.25)
  BaxterDiluteDecay, BaxterRenewalDecay, BaxterExteriorDecayReduction,
  BaxterExteriorRegularityGeneral, BaxterExteriorIntegrability, BaxterExteriorConvIntegrable
Layer OZ — thin translation on top:
  OzBaxterFixedPt        (def + `ozBaxterFixedPt_eq_div`)
  OzExteriorFromBaxter   (NEW: all `r_mul_ozBaxterFixedPt_*` / `ozBaxterFixedPt_*` wrappers)
  OzExteriorSmooth, OzCoreClosure, …
```
The `OZFIX.25` files are the model for Layer B — they were written OZ-free from the start.

**Staging (do in this order, each independently build-green).**
1. Thin files first: `BaxterDiluteDecay`, `BaxterExteriorDecayReduction`,
   `BaxterExteriorRegularityGeneral` — 5 wrappers total, drop the `OzBaxterFixedPt` import.
2. `BaxterExteriorDerivBundle` (import only).
3. Entangled: `BaxterExteriorIntegrability`, `BaxterExteriorConvIntegrable` — restate the 5+5
   signatures in Baxter terms, keep OZ versions as wrappers in `OzExteriorFromBaxter`. **Note the
   axiom `ozExterior_triple_shell_sin_integrable` (6h) lives here** — restating it in Baxter terms is
   itself an improvement (it is a Baxter-analysis fact, not an OZ one).

**Payoff beyond tidiness.** It removes the layering hazard that made `OZFIX.25` step 6 (7b) *look*
blocked: with Layer B free of OZ, ψ-integrability is unambiguously upstream of every OZ statement.
⚠ **Coordinate before executing** — these files are being actively edited by parallel sessions
(`BaxterPoles`, `BaxterHermiteBiehler`, …); a 6-file cross-cutting move will conflict if run blind.

**OZFIX.26 EXECUTED (2026-07-19) — OZ/Baxter layering done in one pass, full build green (8682 jobs).**
Two moves, not one:
1. **Lifted the thin veneer.** The 5 OZ wrappers were moved out of the pure-analysis files into the new
   **`OzExteriorFromBaxter.lean`** (Layer OZ): `r_mul_ozBaxterFixedPt_tendsto_zero_of_dilute`,
   `…_of_eta_dilute` (from `BaxterDiluteDecay`), `…_of_tendsto_zero` (from
   `BaxterExteriorDecayReduction`), `r_mul_ozBaxterFixedPt_tendsto_zero`, `…_integrableOn` (from
   `BaxterExteriorRegularityGeneral`). Those three files swapped `import OzBaxterFixedPt` →
   `import BaxterRenewal` and are now **oz-import-free**.
2. **Reclassified by renaming, not by moving content.** Three files were *inherently* Layer OZ (their
   theorems are all `ozBaxterFixedPt_*`: the jump at σ, continuity/boundedness, the OZ shell/conv
   integrability incl. the 6h axiom) and only carried Baxter-ish names:
   `BaxterExteriorDerivBundle → OzExteriorDerivBundle`,
   `BaxterExteriorIntegrability → OzExteriorIntegrability`,
   `BaxterExteriorConvIntegrable → OzExteriorConvIntegrable`.

**Result — the layering now reads off the filenames.** `Baxter*` = Layer B (pure analysis, provably
0 oz-imports across `BaxterRenewal`, `BaxterKernelDeriv`, `BaxterForcingDeriv`, `BaxterRenewalDiff`,
`BaxterDiluteDecay`, `BaxterRenewalDecay`, `BaxterExteriorDecayReduction`,
`BaxterExteriorRegularityGeneral`); `Oz*` = Layer OZ (interface). Axiom ledger unchanged (pure
refactor), no `sorry`.

⚠ **Gotcha for future renames:** the root module list `LeanCode.lean` sits *beside* `LeanCode/`, so a
`grep -rl … LeanCode/` sweep misses it — the build fails with `bad import`. Update `LeanCode.lean` too.

**Payoff:** `OZFIX.25` step 6 (7b `ozExterior_deriv_integrable`) is now unambiguously unblocked —
ψ-integrability (`baxterPsiOuter_integrableOn`, Layer B) is upstream of every OZ statement by
construction. The only remaining work for 7b is the Tonelli/Young estimate for `q0' ⋆ ψ`.

**OZFIX.25 step 6 (7b) — statement bug found & fixed 2026-07-19; proof route now fully scoped.**

⚠ **`ozExterior_deriv_integrable` was stated over-generally and is FALSE as it stood.** It carried
only `hsigma`, i.e. it asserted the `L¹` bound for *arbitrary* `eta, rho`. But without the physical
relation `heta_def`, the renewal kernel mass `∫₀^σ|q0_poly|` scales linearly in `ρ` and can be made
arbitrarily large, so `baxterPsiOuter` grows exponentially — neither `L¹` nor with an `L¹` derivative.
**Fixed** by adding `heta0/heta1/hrho/heta_def`, which are exactly what `baxterPsiOuter_integrableOn`
consumes and which the sole consumer (`ozBaxterFixedPt_smooth_deriv_bundle`) *already carries*, so the
change is free. **This is the third statement bug in this cluster caught by working the proof**
(after clause 6a being false, and the mis-diagnosed 7b "import cycle"); the pattern — *an axiom stated
with fewer hypotheses than its only consumer supplies* — is a reliable smell worth grepping for.

**Remaining work for 7b (well-scoped, no new axiom).** On `Ioi σ`, `g + r·g' = (r·g)' = ψ'`
(derivative uniqueness: `y·g y = baxterPsiSmooth y` on the open `Ioi σ` by `hg_eq` +
`baxterPsiSmooth_eq_of_ge`, and both sides are differentiable there), so the goal reduces to
`IntegrableOn (baxterPsiSmoothDeriv …) (Ioi σ)`, i.e. the three (★DIFF) summands:
* `baxterForcing'(r) = ∫₀^σ q0PolyDeriv(r−s)(−s)ds` — **vanishes for `r > 2σ`** (there `r−s ≥ r−σ > σ`
  so `q0PolyDeriv_eq_zero_of_gt` applies), and is bounded on the remaining `(σ,2σ]`; integrable on a
  bounded set.
* `q0_poly 0 · ψ̃` — constant times the **already-proven** `baxterPsiOuter_integrableOn`.
* `∫_σ^r q0PolyDeriv(r−t)·ψ̃(t)dt` — **use Mathlib's Young inequality**
  `MeasureTheory.Integrable.integrable_convolution` (`Analysis/Convolution.lean:520`,
  `Integrable f μ → Integrable g μ → Integrable (f ⋆[L,μ] g) μ`) rather than a hand-rolled Tonelli:
  the integrand is `(q0PolyDeriv·1_{[0,σ]}) ⋆ (ψ·1_{[σ,∞)})`, both factors `L¹`. The only real work is
  matching the codebase's `intervalIntegral` form to Mathlib's `convolution` definition (measure/group
  instances, and the support truncations `q0PolyDeriv(u)=0` for `u>σ`, giving the effective window
  `t ∈ [max(σ,r−σ), r]` of length `≤ σ`).
Estimated ~150–250 lines, dominated by the convolution-form matching.

**OZFIX.25 step 6 (7b) — substantial progress 2026-07-19; `BaxterExteriorDerivIntegrable.lean` (new,
Layer B), build green, 0 `sorry`.  Two of the three (★DIFF) summands DONE, including the hard one.**

* ✅ **Convolution term (the hard one) — DONE.** `renewalConv_eq_convolution`: for `r ≥ σ`,
  `∫_σ^r q0'(r−t)ψ̃(t)dt = (psiTrunc ⋆[lsmul, volume] q0DerivTrunc) r` with
  `psiTrunc := 1_{Ici σ}·baxterPsiOuter`, `q0DerivTrunc := 1_{Icc 0 σ}·q0PolyDeriv` (axiom-clean).
  Then `renewalConv_integrableOn` via **Mathlib's Young**
  `Integrable.integrable_convolution` — *no hand-rolled Tonelli needed*, which was the main worry.
  Supporting `L¹` factors: `psiTrunc_integrable` (from the proven `baxterPsiOuter_integrableOn`) and
  `q0DerivTrunc_integrable` (bounded+measurable on a compact — **not** `ContinuousOn`: `q0PolyDeriv`
  jumps at `σ`, so `Measure.integrableOn_of_bounded` is the right tool).
  ⚠ **Both truncations are load-bearing, and I initially got this wrong**: for `t ∈ [σ,r]` the value
  `r−t` may *exceed* `σ`, so `r−t ∈ Icc 0 σ` is FALSE in general — the identification needs a
  sub-case where both sides vanish via `q0PolyDeriv_eq_zero_of_gt`. Dually the `Icc 0 σ` indicator is
  what kills `t > r` (there `q0PolyDeriv (r−t)` has a *negative* argument and is **not** zero).
* ✅ **`q0(0)·ψ̃` term — DONE** (`q0_mul_psiExt_integrableOn`).
* ✅ `forcingDeriv_eq_zero_of_gt` — the forcing summand vanishes past `2σ`.
* ☐ **Remaining: the forcing summand's bound on the bounded piece `Ioc σ (2σ)`** — routine:
  measurability is free because the function **is** `deriv (baxterForcing …)`
  (`hasDerivAt_baxterForcing` + `measurable_deriv`), and the bound is `(|ρq'|+|ρq''|σ)·σ` from the new
  general `abs_q0PolyDeriv_le` (`|q0PolyDeriv u| ≤ |ρq'| + |ρq''|·|u−σ|`) plus
  `intervalIntegral.norm_integral_le_of_norm_le_const`; finish with
  `Measure.integrableOn_of_bounded` and `integrableOn_union` on `Ioi σ = Ioc σ (2σ) ∪ Ioi (2σ)`.
  Then assemble the three summands and apply the derivative-uniqueness step
  (`g + r·g' = (r·g)' = Ψ'` on the open `Ioi σ`, since `y·g y = baxterPsiSmooth y` there) to retire 7b.

**OZFIX.25 COMPLETE (2026-07-19) — axiom 7b `ozExterior_deriv_integrable` RETIRED → theorem.
Full build green (8683 jobs), 0 `sorry`. The OZ exterior-regularity cluster is now axiom-free.**

Step 6 finished in `BaxterExteriorDerivIntegrable.lean` (Layer B, axiom-clean modulo the two upstream
axioms `volterra_renewal_tendsto_zero`/`baxter_no_open_lhp_pole_core` that `ψ ∈ L¹` already carries):
* `forcingDeriv_integrableOn` — vanishes past `2σ`; on `Ioc σ (2σ)` measurability is **free** because
  the function *is* `deriv (baxterForcing …)` (`hasDerivAt_baxterForcing` + `measurable_deriv`),
  sidestepping the integrand's own jump; bound `(|ρq'|+|ρq''|σ)·σ²` via the new general
  `abs_q0PolyDeriv_le` + `intervalIntegral.norm_integral_le_of_norm_le_const`.
* `baxterPsiSmoothDeriv_integrableOn` — the three summands added.
* `ozExterior_deriv_integrable_proved` — representative-independence via **derivative uniqueness**:
  on the *open* `Ioi σ`, `y·g y = baxterPsiSmooth y`, so `HasDerivAt.unique` forces
  `g r + r·g' r = baxterPsiSmoothDeriv r` for *any* valid `g`.

**Ledger: 9 → 8 axioms** (7 math + 1 physics). `MA.14 baxter_no_open_lhp_pole_core` is now the
**sole domain-referencing axiom**; `MA.15 radialShell_bounded_injective` is the only other residue of
the physics-axiom retirements, and it is abstract (`Analysis/`).

⚠ **`baxter_no_open_lhp_pole_core` (MA.14) is NOT in reach the way 7a/7b were.** 7a/7b were
*regularity/integrability* facts about an explicitly constructed solution — the (★DIFF) route made
them mechanical. MA.14 is **Hermite–Biehler root location** for the Baxter symbol on the bounded core
`{Im k < 0, ‖Npoly‖ ≤ ‖Dpoly‖}`: a spectral statement of the same family as general-`η` `POLE.11`,
which the triage heuristic classifies as a **gap** argument (Mathlib has no winding number / Rouché /
argument-principle-with-contour-construction for this), not an **effort** argument. It should be
attacked as its own research task (see `proof_notes_pole.md` `POLE.11`), not as a follow-on here.
