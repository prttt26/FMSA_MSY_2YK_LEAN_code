# Proof Notes: Group CONTACT — `g0_HS_contact_value` via the Jump-Asymptotic Route

Detailed proof records for Group CONTACT: deriving the PY hard-sphere contact value
`g0_HS(σ)=(1+η/2)/(1-η)²` from a real-analysis jump-asymptotic argument on `radial_fourier`'s
large-`k` behavior — sidestepping the full residue-series/Wiener–Hopf inversion Group BAXTER/POLE
pursue. Split out of Group BAXTER (2026-07-15, by topic, when that group grew to 15+ tasks
spanning several unrelated areas) — task IDs `CONTACT.1`–`5` were `BAXTER.4`, `5`, `6`, `7`, `8`
respectively; see the mapping table at the top of `proof_notes_baxter.md`. Depends on Group
BAXTER (`BAXTER.1`–`3`) and Group OZ (`proof_notes_hard_sphere.md`, `oz_h`, `radial_fourier`,
OZ.8/OZ.9b). See `todo_lean.md` for task status summary.

## Group CONTACT — Contact-Value Derivation via Jump Asymptotics

### Task CONTACT.1 — `g0_HS_contact_value` via OZ.8's Fourier-domain closed form (full residue calculus) *(formerly Task OZ.13)*

**Statement:** OZ.8 (`radial_fourier_c_HS_formula` + `radial_fourier_c_HS_eq_C_HS_laplace_expr`,
both proved, no sorry/axiom, `proof_notes_hard_sphere.md`) gives the Fourier-domain OZ solution
in closed form as a function of `k`. Inverting this back to real space (residue calculus on the
closed-form-in-`k` structure factor, essentially reconstructing the classical PY closed-form
solution for `g0_HS(r)` for *every* `r`, not just the contact point) would give
`g0_HS_contact_value` directly.

**Depends on:** Task OZ.8 (done; this is OZ.8's originally-scoped "Part C", deliberately split
off — see OZ.8's writeup, `proof_notes_hard_sphere.md`) and effectively Task `CONTACT.2`'s
groundwork.

**2026 — not actually independent of Task `BAXTER.2`/`CONTACT.2`, and superseded in priority by
`CONTACT.2`.** The original framing ("a route independent of Task `BAXTER.2`/`BAXTER.3`'s
Baxter-`Q` machinery") was wrong: `BAXTER.3`'s identity `1-ρĈ_sine(k) = (1-ρQ̂(k))(1-ρQ̂(-k))`
holds for all complex `k`, so `Ĥ(k)=Ĉ(k)/(1-ρĈ(k))`'s pole structure is governed by the *same*
factor `BAXTER.2`/`CONTACT.2` analyze — this task shares their analyticity question, not a
separate one. Since this task additionally needs the full inversion (not just the contact-point
boundary data), `CONTACT.2` is strictly smaller and is the one to attempt first.

**2026 — fully subsumed by `BAXTER.2` now, no independent content.** `CONTACT.2` succeeded (split
into `CONTACT.3`/`CONTACT.4`/`CONTACT.5`, `g0_HS_contact_value` now a proved theorem) via a route
that needed *none* of this task's residue-calculus machinery — so the "revisit once `CONTACT.2`
clarifies the analyticity blocker" condition above has resolved in the direction that removes
this task's reason to exist: its narrower payoff (the contact value) is already done elsewhere,
and its only remaining content (full inversion of `Ĥ(k)` back to `g0_HS(r)` for every `r`) is
exactly `BAXTER.2`'s own full scope, not a distinct task. See `BAXTER.2`'s 2026 scoping-pass note
for the Mathlib capability check and staged sub-task split (`POLE.1`–`5`, plus `OZFIX.1`–`8` for
the `h_explicit`/`OzFixedPt` assembly).

**Status:** ☐ deliberately parked — no independent content left; fully absorbed into `BAXTER.2`'s
scope. Do not treat as a separate task going forward.

---

### Task CONTACT.2 — `g0_HS_contact_value` from the Wiener–Hopf splitting's boundary data (narrower target) *(formerly Task OZ.14)*

**Statement:** rather than constructing the full `h(r)` for every `r` (Task `BAXTER.2`) or the
full residue-calculus inversion (Task `CONTACT.1` below), extract *just*
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
full closed-form expansion) — full derivation and numbers in Tasks `CONTACT.3`/`CONTACT.4` below,
where the work is now split into separate, pure-numeric task IDs (this task bundled several
logically distinct pieces of different difficulty, same splitting pattern as
`OZ.9-RouteB`→`OZ.11`–`OZ.14` earlier this session).

**Status:** ✓ **DONE** as a whole — **split into `CONTACT.3`/`CONTACT.4`/`CONTACT.5`** below, all
three now ✓ **DONE** (no sorry/axiom). `CONTACT.5`'s final theorem is conditional on `oz_h`'s
exterior regularity/decay (see `CONTACT.5`'s writeup for the exact, honestly-scoped remaining gap)
— it does not unconditionally retire the `g0_HS_contact_value` axiom, but reduces its truth to
that strictly smaller, physically well-motivated open question.

---

### Task CONTACT.3 — General jump-asymptotic lemma for `radial_fourier` *(formerly Task OZ.15)*

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
  (`c_HS(0)=-α0`); not needed for `CONTACT.2`'s own target (only the leading term matters), flagged
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
`CONTACT.5`'s actual argument doesn't need matching *rates* on both sides of the leading-coefficient
comparison — it needs `(k²·radial_fourier[f](k)) - 4πσJ·cos(kσ) → 0` as a genuine limit, then
evaluates that limit along the explicit subsequence `k_n=2πn/σ` (where `cos(k_nσ)=1` identically)
to conclude `J` is pinned down exactly — no density/equidistribution argument, no rate comparison,
needed. See `CONTACT.5` below.

**Status:** ✓ **DONE** — `radial_fourier_jump_asymptotic`, genuine theorem, no sorry/axiom, in
`HardSphere/JumpAsymptotic.lean`.

---

### Task CONTACT.4 — Concrete closed-form asymptotic of `Ĥ(k)` *(formerly Task OZ.16)*

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
   `RadialFourierCHS.lean`) — this session's full symbolic expansion (see `CONTACT.3`) already has
   it in closed form.
3. Apply `py_f1_eq` (already proved) to simplify `α0+α1+α3` to `(1+η/2)/(1-η)²`.

**Depends on:** `radial_fourier_c_HS_formula` (Task OZ.8, done), `py_f1_eq` (`PYDCF.lean`, done).
Independent of `CONTACT.3` — can proceed immediately.

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
existentials — directly usable by `CONTACT.5`.

---

### Task CONTACT.5 — Assembly: `g0_HS_contact_value` from `CONTACT.3`+`CONTACT.4` *(formerly Task OZ.17)*

**Statement:** apply `CONTACT.3` to `f=oz_h` — jump `J=oz_h(σ)+1=g0_HS(σ)` at `σ` (using
`oz_h_core`, already proved, for the `-1` core value) — giving
`radial_fourier[oz_h](k) ~ 4πσJ·cos(kσ)/k²` (as a genuine `Tendsto`/`o(1/k²)` statement).
Separately identify `radial_fourier[oz_h](k)` with `Ĥ(k)=Hhat_closed` via
`oz_fourier_oz_eq_of_PY_core` (Task OZ.9b: `H·(1-ρC)=C`, so `H=C/(1-ρC)` whenever `1-ρC≠0`), then
transfer `CONTACT.4`'s asymptotic across that identification. Match the two resulting asymptotic
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
   `CONTACT.4`'s own proof uses (`one_sub_rho_mul_radial_fourier_c_HS_ne_zero`, extracted from
   `Hhat_closed_asymptotic`'s proof as its own reusable fact, `RadialFourierCHS.lean`),
   transferred across `CONTACT.4`'s `Hhat_closed_asymptotic_tendsto` (the explicit-bound
   `Hhat_closed_asymptotic` repackaged as a `Tendsto`, pure squeeze argument).
2. `hFactB`: `CONTACT.3`'s `radial_fourier_jump_asymptotic` applied directly to `f:=oz_h`, `c:=-1`.
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

**Depends on:** `CONTACT.3` and `CONTACT.4` (both done), `OZ.9b` (`oz_fourier_oz_eq_of_PY_core`,
done, `proof_notes_hard_sphere.md`).

**Status:** ✓ **DONE** — conditional theorem `g0_HS_contact_value_of_oz_h_regularity` **plus** the
unconditional `theorem g0_HS_contact_value` (via the `oz_h_exterior_regularity` axiom), both genuine
theorems, no sorry, in `HardSphere/JumpAsymptotic.lean`. The old physical-number axiom is retired.
