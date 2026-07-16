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

**Status:** ☐ not started — scoped, with a concrete finding that rules out the originally-planned
termwise approach. Left open for a future session with more room to develop either the
`oz_forcing`-residue-expansion route or a from-scratch Mathlib residue-theorem build-out.

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

**Status:** ✓ **DONE** on `(σ,∞)`/`[r0,∞)`; the closed-endpoint extension to `[σ,∞)` remains open,
tied to the same `σ`-boundary difficulty as `OZFIX.4`/`OZFIX.6`.

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

Both reusable by Group MZERO's Route B (`MZERO.9`–`MZERO.11`, `proof_notes_yukawa_wh.md`), which
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
