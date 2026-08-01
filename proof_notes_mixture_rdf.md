# Proof Notes: N=2 Mixture Inner-Core RDF — Mittag-Leffler HS-Pole Series (Groups MML / MZERO)

Proof records for the **N=2 mixture inner-core RDF `h₁`** line: **Group MML** (Mittag-Leffler
inner-core: 2×2 inverse → residue → assembly) and **Group MZERO** (`det(Q̂₀)` zero / HS-pole family).
Split out of `proof_notes_yukawa_wh.md` on 2026-07-17 — the RDF counterpart to the DCF real-space
groups in [proof_notes_mixture_dcf.md](proof_notes_mixture_dcf.md).

**Why RDF, not DCF — the (★) dividing line (2026-07-16).** The RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` carries
**two** `Q̂₀⁻¹` factors ⇒ genuine HS poles (zeros of `det Q̂₀`) ⇒ a genuine **Mittag-Leffler HS-pole
series**, which is exactly what MML/MZERO formalize. By contrast the inner **DCF**
`Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` (MRS.3 (★)) has **no** inverse ⇒ no HS poles ⇒ a finite closed form — so
MML.8's DCF reading is refuted and superseded by Group MRS (`proof_notes_mixture_dcf.md`). **The
`Q̂₀⁻¹`-factor count is the dividing line: none ⇒ DCF; two ⇒ RDF `h₁` (this file).**

**Foundation.** These groups build on **Group Y1** (the first-order Wiener–Hopf RDF derivation:
spectral amplitude `b_{ij}(s)`, `Ĥ₁`) in [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md), and on
Group POLE (the N=1 HS-pole existence analog, `proof_notes_pole.md`).

**History.** Split from the former flat "Group Y2" on 2026-07-15 (into MML / MZERO / MPOLY); MPOLY
went with the DCF groups to `proof_notes_mixture_dcf.md`, and MML / MZERO moved here on 2026-07-17.

## Group MML — N=2 Mixture Mittag-Leffler Inner-Core (2×2 inverse → residue → assembly)

**Motivation (2026-07-15).** For N=2, Q̂₀(z) is a 2×2 matrix with fully algebraic entries
(Y1.1 DONE). Its inverse is Q̂₀(z)⁻¹ = adj(Q̂₀)/det(Q̂₀), also proved (Y1.1:
`inv_apply_eq_adj_div_det`). For the (0,1) off-diagonal entry:

    [Q̂₀(z)⁻¹]₀₁  =  adj(Q̂₀)₀₁ / det(Q̂₀)  =  −Q̂₀₀₁(z) / det(Q̂₀(z))     (2×2 identity)

The zeros s_k of det(Q̂₀(z)) (the "HS poles") then give residues:

    Res_{z=s_k} [Q̂₀⁻¹]₀₁  =  −Q̂₀₀₁(s_k) / det′(Q̂₀)(s_k)     (residue_of_simple_pole)

This is the B_k coefficient used in `fmsa_hs_pole_residue.py`. **MML.1 + MML.2 DONE (2026-07-15)**,
axiom-clean (`HSMixture/MixtureHSPoles.lean`) — the 2×2 adj/det/inverse algebra and the `B_k`
residue via `residue_of_simple_pole`. MZERO.1 (infinitely many HS poles for det(Q̂₀)) is a harder
structural result; MML.8 (full assembly) uses Y1.3 (now done). Together they prove the exact inner
DCF for N=2 unlike pairs IS a convergent Mittag-Leffler series — resolving the "no closed
form" claim.

---

### Task MML.1 — Explicit 2×2 adjugate/det for Q̂₀

**Statement.** For N=2 (`Fin 2` indexing):

    adj(Q̂₀)₀₁  =  −Q̂₀₀₁
    det(Q̂₀)     =  Q̂₀₀₀·Q̂₀₁₁ − Q̂₀₀₁·Q̂₀₁₀
    [Q̂₀(z)⁻¹]₀₁ = −Q̂₀₀₁(z) / det(Q̂₀(z))      (combining adj/det with Y1.1)

**Proof strategy.** Direct `simp` using Mathlib:
- `Matrix.det_fin_two`: `det M = M 0 0 * M 1 1 − M 0 1 * M 1 0`
- `Matrix.adjugate_fin_two`: explicit 2×2 formula
- `Matrix.inv_def` (Y1.1's `inv_apply_eq_adj_div_det`): connects to the above

**Depends on.** Y1.1 (`inv_apply_eq_adj_div_det`), Mathlib `Matrix.det_fin_two`,
`Matrix.adjugate_fin_two`.
**Lean (`HSMixture/MixtureHSPoles.lean`, namespace `FMSA.MixtureHSPoles`).** `adjugate_fin_two_zero_one`
(`adj(M)₀₁ = −M₀₁`), `inv_zero_one_eq` (`M⁻¹₀₁ = −M₀₁/det M`, unconditional via
`inv_apply_eq_adj_div_det`), `Q0_det_fin_two` (`det(Q̂₀) = Q̂₀₀₀Q̂₀₁₁ − Q̂₀₀₁Q̂₀₁₀`), `Q0inv_zero_one`
(`[Q̂₀(s)⁻¹]₀₁ = −Q̂₀₀₁(s)/det(Q̂₀(s))`).
**Status.** ✓ DONE (2026-07-15), axiom-clean.

---

### Task MML.2 — B_k residue formula for N=2

**Statement.** Let s_k ∈ ℂ be a simple zero of `z ↦ det(Q0_mat_c z)` (an HS pole),
i.e., `det(Q̂₀(s_k)) = 0` and `(d/dz det(Q̂₀(z)))|_{z=s_k} ≠ 0`. Then:

    Res_{z=s_k} ([Q̂₀(z)⁻¹]₀₁)  =  −Q̂₀₀₁(s_k) / det′(Q̂₀)(s_k)

(This is the Q̂₀-residue part of the B_k amplitude in `fmsa_hs_pole_residue.py`.
The Yukawa-propagator factor `K/(z_t²−s_k²)` requires Y1.3 and is not part of this task.)

**Proof chain.**
1. MML.1: `[Q̂₀(z)⁻¹]₀₁ = N(z)/D(z)` where `N(z) = −Q̂₀₀₁(z)`, `D(z) = det(Q̂₀(z))`.
2. `N` and `D` are meromorphic / holomorphic near s_k (Y1.1 — entries are entire).
3. `residue_of_simple_pole` (BaxterResidue.lean DONE): gives `Res = N(s_k)/D′(s_k)`.
4. Conclude `= −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)`.

**Depends on.** MML.1, `residue_of_simple_pole` (DONE), M.3/M.4 (for det′ ≠ 0 hypothesis,
currently conditional).
**Lean (`HSMixture/MixtureHSPoles.lean`).** `b_k_residue` — given a simple zero `s_k` of
`s ↦ det(Q̂₀(s))` (`HasDerivAt` det with `Dprime`, `det(s_k)=0`, `Dprime ≠ 0`, `Q̂₀₀₁` continuous at
`s_k` — all as hypotheses, matching `residue_of_simple_pole`), concludes
`Res_{z=s_k}[Q̂₀(z)⁻¹]₀₁ = −Q̂₀₀₁(s_k)/Dprime`.  Proof: rewrite via `Q0inv_zero_one` (holds for all
`z`), then `residue_of_simple_pole` with `N = −Q̂₀₀₁`, `D = det(Q̂₀)`.  Discharging the analytic
hypotheses concretely (entry/det holomorphy at `s_k ≠ 0`) is left to a later pass / MZERO.1.
**Status.** ✓ DONE (2026-07-15), axiom-clean (residue wiring; analytic hyps taken as inputs).

---

### Task MML.3 — RETIRED (2026-07-16), superseded by MML.4–MML.8

The single "full inner-DCF Mittag-Leffler assembly" task bundled ~5 independent sub-results, and its
genuine difficulty — proving the residue *series equals the true inner DCF* (the "collapse") — is the
N=2 matrix analog of the scalar `hcollapse` (OZFIX.6/9/10), **still open even in the scalar HS case**.
As one atomic task it could not be tracked or landed incrementally. Split (per the proof-notes
convention of promoting differently-scoped leftover work to new task numbers) into the five
topic-scoped tasks below. The target identity (N=2 unlike pair (0,1), r ∈ (0, R₀₁]) is unchanged:

    r · c^{inner}_{01}(r) = Σ_t [Q̂₀(z_t)⁻¹·K_t·Q̂₀(z_t)⁻ᵀ]₀₁ · exp(z_t(R₀₁−r))     (I)  MML.6
                           + Σ_k 2·Re[B_k · exp(−s_k·r)]                          (II) MML.4/MML.5
                           + p₀                                                   (III) MML.7
                           [ (I)+(II)+(III) = true inner DCF                            MML.8 ]

MML.4–MML.7 are **DONE (axiom-clean)**; MML.8 (the collapse) is scoped-only. Lean home:
`YukawaDCF/MixtureMLSeries.lean` (MML.4/MML.5), `YukawaDCF/MixtureInnerDCF.lean` (MML.6/MML.7, and
the eventual MML.8).

---

### Task MML.4 — HS-pole Mittag-Leffler term (II) + Yukawa-coupled residue *(**RDF-only**)*

> **⚠ Scope (2026-07-16).** Term (II) (an HS-pole sum) exists **only for the RDF `h₁`** — by (★) the DCF
> carries no `Q̂₀⁻¹`, hence no `det Q̂₀` zeros and no term (II) (finite closed form — Group MRS). The
> definitions/lemmas below stay valid, RDF-scoped. See the MML.8 box.

**Statement.** Define the per-pole term `mixHSterm B_k s_k r n = B_k(n)·exp(−s_k(n)·r)` and the series
`mixHS_series = 2·Re[∑' n, mixHSterm n]` (term (II)). The `B_k` amplitude of `fmsa_hs_pole_residue.py`
is `Res_{s_k}[Q̂₀⁻¹]₀₁ · Σ_t K_t/(z_t²−s_k²)`; MML.4 ties a given `B_k` to the proven MML.2 residue by
showing that multiplying MML.2's `−Q̂₀₀₁(s_k)/det′` by any factor `coupling` continuous at `s_k`
yields the coupled residue `coupling(s_k)·(−Q̂₀₀₁(s_k)/det′)`.

**Design (key).** The term is kept **generic in the coefficient** `Bcoef : ℕ → ℂ` and pole family
`sfam : ℕ → ℂ` (mirroring how the scalar `h_explicit_term` takes an abstract `kfam`). This defers the
singly-vs-doubly-propagation modeling choice to MML.8 (see there), keeping MML.4 grounded in the
already-proven MML.2 residue.

**Depends on.** MML.2 (`b_k_residue`), Y1.1 (`Q0_mat_c`).
**Lean (`YukawaDCF/MixtureMLSeries.lean`, namespace `FMSA.MixtureHSPoles`).**
`mixHSterm`, `mixHS_series`; `yukawaCoupling K z nt s = Σ_{t<nt} K_t/(z_t²−s²)` with
`yukawaCoupling_continuousAt` (continuous where `z_t²≠s_k²`, via `tendsto_finsetSum` + `ContinuousAt.div`);
`b_k_residue_coupled` (`b_k_residue` × the continuous coupling via `Tendsto.mul` + a `ring` regrouping).
**Status.** ✓ DONE (2026-07-16), axiom-clean.

---

### Task MML.5 — Convergence of the HS-pole series (abstract; concrete deferred) *(**RDF-only**)*

> **⚠ Scope (2026-07-16).** HS-pole series exist **only for the RDF `h₁`**. By (★)
> `Ĉ₁ = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` the **DCF** has no `Q̂₀⁻¹`, hence no `det Q̂₀` zeros and no HS-pole
> sum at all (finite closed form — Group MRS). So MML.5 (and its deferred `MML.5-concrete`
> magnitude gate, and MZERO) are **not on the DCF path**; they are load-bearing for `h₁` only.
> Everything below is RDF-scoped. See the MML.8 box.

**Statement (abstract).** If `‖mixHSterm n‖ ≤ C·(n+1)^p` with `p < −1`, then
`Summable (mixHSterm B_k s_k r)`.

**Proof.** Near-copy of the scalar `h_explicit_summable` (`HardSphere/BaxterResidue.lean`): reduce to
`Summable (n ↦ (n+1)^p)` via `Real.summable_nat_rpow` (holds iff `p < −1`) + `summable_nat_add_iff`
index shift, then `Summable.of_norm_bounded`.

**Reduction (DONE 2026-07-16, axiom-clean).** `mixHS_summable_of_growth` (`MixtureMLSeries.lean`):
given (i) a linear pole-growth `c·n+d ≤ ‖sfam n‖` (`c,d>0`) and (ii) the per-pole power bound
`‖mixHSterm n‖ ≤ C·‖sfam n‖^p` (`p<−1`), the series is `Summable`. Converts the `‖s_k‖`-power bound
to `mixHS_summable`'s `(n+1)^p` form via the negative-exponent `rpow` antitone step
(`Real.rpow_le_rpow_iff_of_neg`) — mirrors `h_explicit_summable_of_pole_family`. This **isolates**
the concrete gate to exactly one obligation (see below).

**Growth witness (DONE 2026-07-16, axiom-clean).** The claim (in an earlier draft of this note) that
"no mixture pole-family growth witness exists" is now **retired** — it does:
- `exists_zero_family_growth_of_chordPoleFamily` (**generic**, `Analysis/BanachPoleFamily.lean`):
  from any `ChordPoleFamily F` whose centres grow linearly (`c·n+d ≤ ‖s1 n‖`), the constructed zero
  family `g` inherits `c·n + (c·N + d − r) ≤ ‖g n‖` (reverse triangle, `norm_sub_norm_le`). Reusable
  by **both** POLE.5 and MML.5.
- `Q0_det_c_pole_family_growth` (**mixture instance**, `MixtureHSZeros.lean`): the same
  `ChordPoleFamily detC` as `Q0_det_c_zeros_infinite`, exposing `π·n + (π·N − r) ≤ ‖g n‖` (centres
  `‖s1 n‖ ≥ |Im| = π·n` via `Complex.abs_im_le_norm`; with `N≥1`, `r<π/2` the offset `>π/2>0`).
  Conditional on the MZERO.5 bounds, like `Q0_det_c_zeros_infinite`.

**The remaining MML.5-concrete gate — ✅ CLOSED 2026-07-17 (superseding the "deferred" text
that follows).** The per-pole **magnitude bound** `‖B_k‖·e^{−r·Re s_k} ≤ C·‖s_k‖^p` (`p<−1`) was
the last piece; it is now proved (`detF_family_magnitude_bound`) and fed into
`mixHS_summable_of_growth` (`detF_mixHS_summable`, `YukawaDCF/MixtureMLBound.lean`), both
axiom-clean — see the "GATE PROVED" and "`Summable` WIRED end-to-end" notes at the top of the
MZERO.5 section. *Original scoping text (kept for the technique record):* a POLE.5-analog —
POLE.5's `Npoly/Dpoly` cubic-over-linear chain re-derived for the **two-frequency** exp-polynomial
`detC` (`detC_lam_free`); in the event this was NOT a `‖B_k‖·e^{−r·Re s_k}` bound at the raw
zeros (those have `Re s_k < 0`) but at the **reflected** family `−g n`, and the exponent's
threshold turned out to be `max(σ₀/2, (σ₁−σ₀)/2)`, not `σ₀/2`.

**Depends on.** All discharged: abstract/reduction/growth + MZERO.1 pole family (CLOSED 2026-07-17)
+ the `detC` magnitude lemma (proved 2026-07-17).
**Lean.** `mixHS_summable`, `mixHS_summable_of_growth` (`MixtureMLSeries.lean`);
`exists_zero_family_growth_of_chordPoleFamily` (`Analysis/BanachPoleFamily.lean`);
`Q0_det_c_pole_family_growth` (`MixtureHSZeros.lean`); `detF_family_magnitude_bound`,
`detF_zero_family_growth`, `detF_mixHS_summable` (`MixtureChordFamily.lean`/`MixtureMLBound.lean`).
**Status.** ✅ **FULLY CLOSED (2026-07-24), axiom-clean, no remainder** — abstract + reduction +
growth-witness (2026-07-16) + concrete magnitude gate + end-to-end `Summable` (2026-07-17) + the
`Bcoef = b_k_residue` identification (2026-07-24, below).

**✅ 2026-07-24 — the last bookkeeping item CLOSED: the summed coefficient *is* the residue.**
Until now `Bcoef n = −q01(g n)/det′(g n)` was a *formula* that resembled MML.2's `B_k` but was never
proved equal to it, so "the series converges" and "the series is the HS-pole Mittag-Leffler series"
were separate claims. Both new pieces are axiom-clean, full build green:

- `detF_family_magnitude_bound` (`MixtureChordFamily.lean`) **strengthened** with a non-vanishing
  clause `∀ n, g n ≠ 0 ∧ det′(g n) ≠ 0`. No new analysis: both are strict consequences of the
  `disk_facts` the magnitude chain already consumed (`1 ≤ ‖g n‖`, and
  `‖det′(g n)‖ ≥ σ₁μ/(24(μ+K₁)) > 0`). The proof only needed those three facts *hoisted* out of the
  per-`n` bullet into a shared `hfacts`, so both conclusions can read them.
- `detF_Bcoef_eq_b_k_residue` + `detF_eq_det_Q0` (`MixtureMLBound.lean`, which now also imports
  `MixtureHSPoles`): at any `s_k ≠ 0` with `detF s_k = 0`, `det′(s_k) ≠ 0`, the coefficient
  `−q01(s_k)/det′(s_k)` **is** `Res_{s_k}[Q̂₀(z)⁻¹]₀₁`. The three `b_k_residue` inputs come from the
  `MixParams` layer: `detF_hasDerivAt` (needs `s_k ≠ 0`), `hzero`, and
  `q0_entry_c_differentiableAt` for the entry's continuity. `detF_eq_det_Q0` is `rfl` — the
  parameter pack's `detF` *is* `det Q̂₀` of the cast matrix — and `q01_eq` was already there.
- `detF_mixHS_summable` correspondingly gains a third clause certifying the identification for the
  constructed family, so a single theorem now delivers: injective zero family + each coefficient is
  a genuine HS-pole residue + the series is `Summable`.

⚠ Note the shape of the fix: the non-vanishing was *already inside* the old proof and was simply
being discarded. Whenever a "cosmetic remainder" is logged, check first whether the missing fact is
already established and merely unexported — here that turned a projected analysis task into a
five-line restructure.

**✅ 2026-07-17 — MML.5-concrete GATE PROVED (reflected form), axiom-clean.**
`detF_family_magnitude_bound` (`HSMixture/MixtureChordFamily.lean`, module green, no `sorry`,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

```
detF_family_magnitude_bound (P : MixParams) (hP : P.Phys) {rdist : ℝ}
    (hrd : max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2) < rdist) :
    ∃ g C p, p < -1 ∧ 0 < C ∧ Function.Injective g ∧ (∀ n, P.detF (g n) = 0) ∧
      (∃ c d, 0 < c ∧ 0 < d ∧ ∀ n, c*n + d ≤ ‖g n‖) ∧
      ∀ n, ‖q01 P (g n)‖ * Real.exp (rdist * (g n).re) / ‖derivF P (g n)‖ ≤ C * ‖g n‖ ^ p
```
with `p = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁)`. Plus `detF_zero_family_growth` (linear growth
`c·n+d ≤ ‖g n‖`, from a local re-run of the Banach construction — the generic
`exists_zero_family_growth_of_chordPoleFamily` forgets disk membership, which the magnitude
chain needs), and the supporting `q01`/`q01_norm_le`, `derivF_at_sGuess_lower`, `disk_facts`,
`sGuess_re_dev`, `magnitude_bound_at`.

**⚠ CORRECTION to this session's own earlier scoping formula (below): the threshold is
`max(σ₀/2, (σ₁−σ₀)/2)`, NOT `σ₀/2`.** The extra branch is a genuine effect, not proof slack —
it is the `−σ₀/s` term of `q01` (from `(1 − sσ₀ − e^{−sσ₀})/s²`), decaying like `‖s‖^{2λ/σ₁−1}`,
which dominates the `e^{σ₀x}/‖s‖²` term exactly when `2σ₀ < σ₁`. **Numerically re-confirmed
2026-07-17** at σ=[0.8,2.3] (`2σ₀=1.6 < 2.3`, n=2000): measured `p(0.45) = −0.867 > −1`
(**NOT summable**) where the naive one-branch formula predicted `−1.043` — so the `σ₀/2`
threshold would have been WRONG there; true threshold ≈ 0.603, the proved `max(…) = 0.75` is
sufficient (conservative). The earlier scoping missed this because both tested σ-pairs were
degenerate for it (σ=[1,2]: `2σ₀ = σ₁`, branches coincide; σ=[1,1.5]: `2σ₀ > σ₁`, first branch
binds) — a reminder to sweep the *qualitative regimes*, not just several parameter values.

**`Summable` corollary NOW WIRED (2026-07-17) — MML.5-concrete CLOSED end-to-end.**
`detF_mixHS_summable` (`YukawaDCF/MixtureMLBound.lean`, new file importing both
`MixtureChordFamily` and `MixtureMLSeries`; axiom-clean, no `sorry`, full build green): for
`rdist > max(σ₀/2, (σ₁−σ₀)/2)`, `∃ g` injective `detC`-zero family with
`Summable (mixHSterm (fun n => −q01(g n)/derivF(g n)) (fun n => −g n) rdist)`. The wiring is
pure reflection + a norm computation: `mixHS_summable_of_growth` takes `Bcoef`/`sfam` as FREE
functions (no `b_k_residue` analytic hypotheses), and `‖mixHSterm‖ = ‖q01(g n)‖·e^{rdist·Re(g n)}
/‖det′(g n)‖` is *exactly* the gate's LHS (via `norm_div`/`norm_neg`/`Complex.norm_exp`), while
`‖sfam n‖ = ‖−g n‖ = ‖g n‖` transfers the linear growth. **Only cosmetic bookkeeping remains**:
identifying `Bcoef n = −q01(g n)/det′(g n)` with `b_k_residue`'s abstract `B_k` (same value,
different packaging) inside the DCF assembly — not an analytic gap.

**2026-07-16 (POLE session) — the concrete magnitude bound is REFUTED as literally stated for
the raw zero family, and CONFIRMED for the reflected family.** Scoping (`mzero5_scoping.py`):
the detC zeros have `Re z_k ≈ −(2/σ₁)ln|z_k| < 0`, so enumerating `s_k := z_k` makes
`e^{−r·Re s_k}` GROW: measured `‖B_k‖e^{−r·Re s_k} ~ |s_k|^{p_eff}` with
`p_eff(r) ≈ −0.5 + r·(2/σ₁)` — never `< −1` for `r ≥ 0` (σ=[1,2]: `p_eff(1) = +0.45`).
With the **reflected family `s_k := −z_k`** (`Re s_k > 0` — the correct enumeration for
`mixHSterm`'s decaying kernel under the inverse-Laplace convention `Σ Res·e^{z_k r} =
Σ B_k e^{−s_k r}`, `s_k = −z_k`), the bound HOLDS: measured `p_eff(r) ≈ −0.5 − r·(2/σ₁) < −1`
for `r ≳ 0.5` at both σ sets tested; analytic account: `‖q01(z)‖ ~ e^{λ|Re z|}·C/|z| =
|z|^{2λ/σ₁−1}`, `‖det′(z_k)‖ → σ₁·|Mc| = Θ(1)`. The Lean deliverable (in
`HSMixture/MixtureChordFamily.lean`) states the bound at the constructed zero family in the
reflected form; **reconciling `mixHSterm`'s family argument (feed `−z_k`, not `z_k`) is flagged
for the mixture session** — cf. the `G_baxter` ρ-bug lesson: sign conventions matter and the
numerics have now pinned this one.

---

### Task MML.6 — Yukawa doubly-propagated base term (I)

**Statement.** Define the base amplitude `yukawaBaseAmp = [Ĝ·K·Ĝᵀ]₀₁` (`Ĝ = Q̂₀(z)⁻¹`) and the
real-space base `yukawaBaseTerm = Σ_t amp_t·exp(z_t(R−r))` (term (I)). Certify that `yukawaBaseAmp` is
exactly the residue at the Yukawa pole `s = −z` of the Y1.5 spectral amplitude — i.e. the exact
**doubly-propagated** leading residue ([LN] Eq. 73), *not* the singly-propagated `K·Ĝ₀₁` leading-order
approximation shipped by the Python.

**Proof.** Direct reuse of `spectralAmp_residue` (Y1.5, `SpectralAmplitude.lean`): its limit value is
literally `(Ĝ·K·Ĝᵀ)₀₁ = yukawaBaseAmp` (defeq after `unfold`).

**Note (envelope = MML.8).** The real-space `exp(z_t(R−r))` envelope — the inverse-Laplace step
relating this residue to `yukawaBaseTerm` — is the assembly, deferred to MML.8. `outerDCF_transform`
(Y1.2, `OuterDCF.lean`) supplies one direction of that transform pair.

**Note (RDF vs DCF — CORRECTED 2026-07-16 by (★)).** `yukawaBaseAmp` is the **RDF** (`h₁`)
amplitude: at an HS pole it produces a *double* pole (`doubly_prop_entry_eq`), hence `r·e^{−s_k r}`
terms. MML.6 proves that RDF amplitude — a valid, exact object (Y1.5/Y1.6).

⚠ An earlier version of this note added: *"the DCF `c^{inner}` base is instead the **singly**-propagated
`K·[Q̂₀⁻¹]₀₁`; the DCF assembly (MML.8, reading (S)) uses it."* **That is refuted.** (★)
`Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` contains **no `Q̂₀⁻¹` at all** ⇒ the DCF has *no* HS poles and *no*
term (II); its base is not a singly-propagated inverse amplitude either. The DCF route is **Group
MRS** (finite closed form). The `Q̂₀⁻¹`-count is the dividing line: **none ⇒ DCF (MRS); two ⇒ RDF
`h₁`** — the "singly" reading corresponds to no object. See the MML.8 box.

**Depends on.** Y1.5 (`spectralAmp`/`spectralAmp_residue`), Y1.1 (`Q0_mat_c`).
**Lean (`YukawaDCF/MixtureInnerDCF.lean`).** `yukawaBaseAmp`, `yukawaBaseTerm`,
`yukawaBaseAmp_eq_spectralAmp_residue`.
**Status.** ✓ DONE (2026-07-16), axiom-clean.

---

### Task MML.7 — Origin (singularity-cancellation) constant `p₀`

**Statement.** The constant `p₀ = −(Yukawa base + HS-pole sum)|_{r→0}` keeping `c(r)=rc₁(r)/(…·r)`
finite as `r→0` (`_precompute_p0`). Abstractly: for `base`, `hsum`, inner-polynomial `P` continuous
at 0 with the `1/r` limit existing, `P 0 = −(base 0 + hsum 0)`.

**Proof.** Instantiates P.2's fully-generic `origin_necessity` (`FMSAPoly/OriginConstraint.lean`) with
the bundled `E := base + hsum`. The Yukawa specialization fixes `base := eij` (its continuity via
`fun_prop`, as in Y1.7) and rewrites `eij(0)` via `eij_at_origin`, giving
`P 0 = −(Σ_k A_k·exp(−z_k R) + hsum 0)` — exactly `_precompute_p0`'s `−(E_ij(0) + Σ_k 2·Re[B_k])`
form. Extends Y1.7's `origin_constraint_eq76` (Yukawa-only) by folding the HS-pole sum into `E`.

**Depends on.** P.2 (`origin_necessity`), P.1 (`eij`/`eij_at_origin`), Y1.7 (pattern).
**Lean (`YukawaDCF/MixtureInnerDCF.lean`).** `origin_constant_mix`, `origin_constant_eij_mix`.
The one deferred ingredient is `ContinuousAt (mixHS_series …) 0` (the HS-sum's continuity at 0, a
tsum-continuity fact needing the same dominated-summability machinery as MML.5-concrete); MML.7 takes
it as the hypothesis `hcSum`.
**Status.** ✓ DONE (2026-07-16), axiom-clean.

---

### Task MML.8 — Full assembly / collapse *(ex-MML.3, scoped only)*

> **⚠ PREMISE REFUTED (2026-07-16) — for the DCF, term (II) does not exist.**
>
> The numerical session's **(★)** result (`todo/to_Lean.md` §1; `fmsa_double_prop.py`,
> `probe_true_first_order.py`; verified to 4.4×10⁻¹³) removes the inverses from the DCF. Equating
> [LN] eq:OZ1_Baxter (a) with `Hhat1_spec` (b) and solving for `Ĉ₁`:
>
>     Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)                                  (★)
>
> **(★) contains no `Q̂₀⁻¹`.** `Q̂₀` is entire (the `φ₁`,`φ₂` singularities at `s=0` are removable)
> and `B₁_ij(k) = e^{−ikR_ij}·b_ij(ik)` carries only the Yukawa poles `k = i·z_q`. Hence `Ĉ₁` is
> meromorphic with **only Yukawa poles**, and the zeros of `det Q̂₀` — the whole subject of Group
> MZERO — **never enter the DCF**. Consequences:
>
> - The **stated** target above — (II) as an infinite HS-pole sum `Σ_k 2Re[B_k e^{−s_k r}]` — is
>   **false-as-premised for the DCF**. The correct target is a **finite closed form** (polynomial +
>   finitely many exponentials), **piecewise** in `r`, with knots at the support-overlap
>   breakpoints (`λ_ij` first — exactly Group IB's set).
> - The listed blockers **dissolve for the DCF**: `MZERO.1`, `MML.5`-concrete, `MZERO.5`,
>   MA.2/MA.3 termwise inversion, and — decisively — the **`OZFIX.14` circularity**. The
>   "VERY HARD, matrix analog of `hcollapse`" difficulty was an artifact of the wrong premise.
> - **Crux #1's doubly-vs-singly analysis presupposes HS poles**, so it is about the **RDF**, not
>   the DCF. It stays valid for `h₁`.
> - It vindicates the hint recorded at the end of this entry — "the only genuinely axiom-free path
>   is the **matrix real-space Baxter/Wertheim–Thiele derivation**" — and shows that path is
>   *elementary* once (★) removes the inverses.
>
> **Superseded for the DCF by → Group MRS** (below): MRS.1 (matrix WH factorization — the only
> analytic input), MRS.2 (eq:OZ1_Baxter), MRS.3 ((★) + "no HS poles"), MRS.4 (real-space `q` + the
> `λ_ij` delta), MRS.5 (convolution ⇒ finite closed form).
>
> **What survives here.** MML.8 remains meaningful **only as the RDF (`h₁`) assembly**, whose
> `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` *does* carry the inverses ⇒ genuine HS poles ⇒ a genuine Mittag-Leffler
> series. **The inverses are the DCF/RDF dividing line.** MZERO and MML.5-concrete stay
> load-bearing for that object only. Everything below this box was written under the DCF premise —
> read it as RDF-scoped or historical.

**Statement.** The full identity `(I) MML.6 + (II) MML.4/MML.5 + (III) MML.7 = r·c^{inner}_{01}(r)` —
the N=2 matrix analog of the scalar Mittag-Leffler series in POLE.4/Group OZFIX. **Effort: VERY HARD**
(same scale as Y1.3 + Group OZFIX combined; the matrix Blum–Wertheim Laplace inversion).

**Depends on.** Y1.3 (Wiener–Hopf, ✓), MML.4–MML.7 (✓), MZERO.1 (infinitely many poles),
MML.5-concrete (the `detC` magnitude/growth bound), POLE.4/OZFIX (scalar collapse precedent).

**Crux #1 — settle singly-vs-doubly propagation. RESOLVED (pole-order argument, 2026-07-16, Lean).**
The stated identity mixes a **doubly**-propagated base (I) `[Q̂₀⁻¹KQ̂₀⁻ᵀ]₀₁` (Y1.5/Y1.6 = MML.6) with a
**singly**-propagated `B_k = adj/det′` (MML.2); `to_python.md` logs three options and the naive mix
blows up numerically (`ĉ₁₂ ≈ +4.5×10⁵`). The resolution is a **pole-order** fact, now proved:

- `doubly_prop_entry_eq` (`MixtureInnerDCF.lean`, axiom-clean): since `Q̂₀⁻¹ = adj/det`
  (`Matrix.inv_def`), the doubly-propagated entry is `[Q̂₀⁻¹KQ̂₀⁻ᵀ]₀₁ = (adj·K·adjᵀ)₀₁/det²` — an
  `N/det²` object.
- `double_pole_leading_coeff` / `_ne_zero` (axiom-clean): any `N/D²` with `D` a simple zero at `s_k`
  has an **order-2** pole, leading coefficient `N(s_k)/det′(s_k)²` (= `to_python.md` option (a)'s
  `B_k^{new}`), nonzero when `N(s_k)≠0`. **A double pole inverse-Laplace-transforms to `r·e^{−s_k r}`
  (an `r`-prefactor), absent from the stated simple-exponential term (II).**

**Conclusion.** The stated term-(II) form `Σ_k 2·Re[B_k·e^{−s_k r}]` (clean exponentials) is consistent
**only** with **singly**-propagated (simple-pole) HS terms. The two readings considered were:
- ~~**(S) fully-singly** — the DCF `c^{inner}`: base `K·[Q̂₀⁻¹]₀₁`, `B_k = adj/det′` (simple poles,
  clean `e^{−s_k r}`). Matches the stated form **and** the shipped Python `get_c1_inner` **and** the
  MSA outer-DCF continuation (direct-correlation `−βu`, single-propagated).~~
  **⚠ REFUTED (★): the DCF carries *no* `Q̂₀⁻¹`, so reading (S) corresponds to no object** — the
  agreement with `get_c1_inner` was agreement with the shipped *leading-order approximation*, not with
  the exact DCF. (The exact DCF is finite/piecewise — Group MRS.)
- **(D) fully-doubly** — the RDF `h₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (Y1.6 `Hhat1`): base `[Q̂₀⁻¹KQ̂₀⁻ᵀ]₀₁` +
  **double**-pole HS terms `(α_k + β_k r)·e^{−s_k r}`. ✅ **This is the surviving reading** — MML.4–MML.8
  are RDF-scoped, and the pole-order lemmas are load-bearing exactly here.

~~**Recommendation (CORRECTED — was "fully-doubly").** For the DCF `c^{inner}` that MML.8 targets,
pursue **(S) fully-singly**: it is the coherent reading matching the stated series, the Python, and
the DCF's physical nature. MML.4's generic-`Bcoef` design already carries the singly instance
(`b_k_residue_coupled`). The doubly-propagated MML.6 amplitude is then correctly understood as the
**RDF** base (a valid, proven object — Y1.5/Y1.6 — but not term (I) of the DCF); MML.6's docstring
labels it accordingly.~~

**⚠ The (S) recommendation above is REFUTED too (2026-07-16, by (★)) — struck.** It assumed the DCF
carries *one* `Q̂₀⁻¹`. (★) `Ĉ₁ = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` shows it carries **none**, so the DCF has no HS
poles and no term (II) at all — **reading (S) corresponds to no object**. The correct statement of the
Crux #1 content is the `Q̂₀⁻¹`-**count** as the DCF/RDF dividing line:

| `Q̂₀⁻¹` factors | object | HS poles | inner form |
|---|---|---|---|
| **none** | **DCF `Ĉ₁`** (★) | none | **finite closed form**, piecewise at `λ_ij` — **Group MRS** |
| one | *(no object)* | simple | ~~`Σ B_k e^{−s_k r}`~~ — the shape that motivated (S) |
| **two** | **RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹`** | **double** | `Σ (α_k+β_k r)·e^{−s_k r}` |

So the pole-order lemmas (`doubly_prop_entry_eq`, `double_pole_leading_coeff`) are **correct and
load-bearing for the RDF row**; only the DCF attribution was wrong. What the analysis got right — that
the inverse factors dictate the pole structure — is exactly the dividing line (★) confirms.

**Crux #2 — the collapse route.** Two candidates from the scalar `hcollapse` precedent
(`proof_notes_ozfix.md`):
- **Route A** (OZFIX.9): termwise `oz_forcing` Mittag-Leffler expansion at the resolvent poles.
  Unblocked, axiom-free *target*, but the per-pole coefficients do **not** factor cleanly (the
  `R_n = H_n − L_n` ratio oscillates), so the `σ≤r<2σ` region is a genuine ML identity of
  comparable difficulty; `r≥2σ` is per-pole exact.
- **Route B** (OZFIX.10, now powered by MA.2 `mittagLeffler_expansion_of_bounded_on_circles` +
  MA.3 `fourier_kernel_one_pole`): growing-contour Fourier inversion. **Favored** (user-confirmed
  for the scalar case): trades the physics-specific axiom for standard reusable math axioms, and
  MA.2/MA.3 already dissolved its arc-vanishing blocker.
  ~~**Recommendation:** pursue the **matrix Route B** — expand each entry of `Ĥ₁(s)` (or `c^{inner}`'s
  transform) via MA.2, Fourier-invert termwise via MA.3, control the sum/limit interchange (MML.5),
  and identify the result with `mixHS_series` (II) + base (I) + `p₀` (III).~~

**Crux #2 recommendation CORRECTED (2026-07-16, from the scalar `OZFIX.11`/`OZFIX.12` findings).**
The struck-through MA.2-pointwise plan above inherits the scalar route's **false-identity
obstruction** (`proof_notes_ozfix.md` `OZFIX.10`, 2026-07-16 update): termwise inversion of the
pointwise kernel makes the `O(R)` moment `W₁` enter with coefficient = the circle-mean of `Ĥ`,
which tends to `−1/ρ` (NOT 0) — no ML degree or pairing order fixes it. The corrected scalar
route decomposes instead into (i) a **per-pole-exact region** where the forcing vanishes and the
collapse factor is the WH factorization at zeros (`ρĈ(k_n)=1`, `OZFIX.11`, proved axiom-clean
with *no* contour machinery), plus (ii) a windowed contour argument on **doubly-smoothed kernels
only** (`OZFIX.12`). For MML.8 this transfers as:
1. **First concrete sub-piece — matrix WH factorization** (mixture analog of `OZFIX.2`):
   `Q̂₀(s)·Q̂₀ᵀ(−s) = I − Ĉ_mix(s)`, currently ABSENT from Lean (`YukawaWienerHopf.lean` has only
   residue-through-conjugation). Its det corollary `det(I−Ĉ_mix)(s_k) = 0` at `det(Q̂₀)` zeros is
   the mixture collapse factor; entry-wise collapse will need the adjugate-level version
   (cf. MML.1's `[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁/det`).
2. Scope numerically whether the inner-DCF assembly has a per-pole-exact sub-region (the analog
   of `r ≥ 2σ` — geometry differs for the inner core, needs its own scoping pass) before any
   whole-series work.
3. Any contour step must use doubly-smoothed kernels; run the mixture analog of the circle-mean
   check (`Ĥ₁` entries' means → a `−1/ρ`-type matrix constant) FIRST to pin the obstruction shape.

**Prerequisite ordering — UPDATED 2026-07-17: all prerequisites now DONE.** MML.8 was gated behind
MML.5-concrete (the interchange / `Summable`) and, for an *unconditional* statement, MZERO.1's full
zero-family (then conditional on MZERO.5). **Both are now closed axiom-clean (2026-07-17):**
MML.5-concrete = `detF_mixHS_summable` (`YukawaDCF/MixtureMLBound.lean`, `Summable` wired end-to-end
from `detF_family_magnitude_bound`); MZERO.1 = `detC_zeros_infinite_unconditional`
(`HSMixture/MixtureChordFamily.lean`, parameter-only hypotheses), with MZERO.5's `hbound`/`hstep`
retired. So the "conditional MML.8 first, unconditional later" ordering is moot — an *unconditional*
statement is no longer blocked by any prerequisite, and **the only remaining content is Crux #2, the
collapse itself.**

**Lean.** `YukawaDCF/MixtureInnerDCF.lean` — Crux #1 pole-order lemmas `doubly_prop_entry_eq`,
`double_pole_leading_coeff`, `double_pole_leading_coeff_ne_zero` (all axiom-clean).
**Term (II) + collapse reduction target now landed (2026-07-17, axiom-clean, build green):**
- **Both Laurent coefficients of the double pole certified.** `double_pole_leading_coeff` (earlier)
  gives the order-2 `β_k = N(s_k)/D′(s_k)²` (the `r`-prefactor). **`double_pole_reg_hasDerivAt` /
  `double_pole_reg_eventuallyEq` / `double_pole_second_coeff` (2026-07-18, axiom-clean)** give the
  order-1 `α_k = N′/E(s_k)² − 2·N(s_k)·E′/E(s_k)³` via the simple-zero factorization `D = (·−s_k)·E`
  (`E(s_k)=D′(s_k)`): the regularization `reg := N/E²` equals `(·−s_k)²·(N/D²)` on `𝓝[≠]s_k`, is
  genuinely differentiable at `s_k`, and `α_k = reg′(s_k)` (read through `hasDerivAt_iff_tendsto_slope`
  as the simple-pole residue `(z−s_k)f − A/(z−s_k) → α_k`). **This avoids the (Mathlib-absent-over-ℂ)
  L'Hôpital / 2nd-order-Taylor route** — the factorization `E` is exactly what
  `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` supplies for the analytic `det Q̂₀`. So the
  real-space term (II) `(α_k + β_k·r)e^{−s_k r}` is now fully pinned by the pole data.
- `mixHSterm2` / `mixHS_series2` — term (II) in the **doubly-propagated** RDF form
  `(α_k + β_k·r)·e^{−s_k r}` (the surviving reading). `mixHSterm2_eq` / `mixHS_series2_eq` identify
  them *definitionally* with the singly `mixHSterm`/`mixHS_series` at the `r`-absorbed coefficient
  `α_k + β_k·r`, so all of MML.4/5's summability API transfers for free.
- `mixHS_series2_summable` — convergence from the (DONE) MML.5-concrete growth bounds
  (`mixHS_summable_of_growth`), i.e. the collapse target is non-vacuous.
- `mixRDFInnerAssembly` (`(I) base + (II) doubly series + (III) p₀`) + `MixRDFInnerCollapse` (the
  `Prop` `assembly = r·h₁` on `(0,Rij)`) — the reduction target, the matrix analog of the scalar
  `CoreSeriesClosure` (OZFIX.12). **Deliberately not an axiom** (sub-family trap; needs pole
  exhaustion, which MZERO.1's infinitude does not give).

The collapse identity itself (discharging `MixRDFInnerCollapse` for the genuine pole family) is the
remaining (future) content — the bridge `assembly = r·h₁`, which per the OZFIX.22 template awaits a
matrix `oz_fixed_pt_unique` + matrix OZ★ (Group MRS).

**⟳ RE-EVALUATION 2026-07-29 (after matrix OZ★ + all-`N` pole-freeness landed).**  Two findings:
1. **The blocker "awaits matrix OZ★" is STALE** — matrix OZ★ is now built (`matOzStar_of_shellClaims`,
   `MixtureOzStar.lean`).  `MixtureRDFAntideriv.lean`'s "neither built yet (i)+(ii)" is stale for (ii).
2. **The non-circular OZFIX.22-template route is now assembled up to ONE scoped gap**
   (`MixtureRDFUniqueness.lean`, axiom-clean, ledger unchanged 7):
   * `MatOZHom` + `matOzStar_sub_hom` — difference of two `MatOZStar` solutions solves the homogeneous
     matrix radial OZ★ equation (matrix analog of `oz_linear_op_sub`).
   * `matOzStar_unique_of_injective` — **conditional matrix `oz_fixed_pt_unique`**: two solutions
     coincide given the matrix WH injectivity `hinj`.
   * `matStructureFactor_isUnit_of_det_ne_zero` — `det Q̂₀ ≠ 0` ⇒ `T₀ = Q̂₀(k)Q̂₀(−k)ᵀ` a unit
     (`det_eq_of_wienerHopf_factorization`), i.e. the **coercivity input** `hinj` needs is exactly what
     `mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal` supply.
   The gap `hinj` = matrix analog of the scalar KEPT axiom `radialShell_bounded_injective`
   (bounded/`L∞` WH injectivity; the `L∞`-Wiener-algebra gap, same class as `MA.13`, that `MA.12`'s
   `L²` Plancherel does not reach).  **✅ COMMITTED 2026-07-30** as `matRadialShell_bounded_injective`
   (`MixtureRDFUniqueness.lean`, one new **math** axiom, ledger `7 → 8` = 7 math + 1 physics).
   `matOzStar_unique` now discharges `hinj` via it — the **value route is UNCONDITIONAL** (no abstract
   injectivity hypothesis), resting on: the axiom + the coercive matrix symbol `MatSymbolCoercive`
   (`vᵀ(I − ρĈ(k))v ≥ ε‖v‖²`, the multicomponent no-spinodal — a hypothesis exactly as in the scalar
   axiom, whose invertibility `det Q̂₀ ≠ 0` is `matStructureFactor_isUnit_of_det_ne_zero` from
   `mixtureDet_pole_free_N`) + the solutions' regularity.  `matRadialSymbol` = the matrix radial sine
   symbol.  **✅ ABSTRACTED to `Analysis/MatrixRadialWienerHopf.lean` 2026-07-30**: the axiom is now
   the project-independent, raw-integral `FMSA.matRadialShell_bounded_injective` (arbitrary matrix
   kernel, no project defs — mirrors the scalar `radialShell_bounded_injective`);
   `MixtureRDFUniqueness.lean` re-exposes it as a theorem via the definitional bridges `matOZHom_raw`
   (operator = raw `∑ₖ(2π/r)∫∫`) and `matRadialSymbol` (symbol).  Bucket now **`Analysis` 7 +
   `HSMixture` 1** (the 1 = physics `pyhs_mixture_no_spinodal`).
3. **The literal pole-series collapse `MixRDFInnerCollapse` stays open/circular** (Fourier route,
   inherited from scalar `CoreSeriesClosure`); the OZ★+uniqueness route above targets the RDF *value*,
   not the pole-series representation.
**Crux #2 — CIRCULARITY WARNING inherited from the scalar case (2026-07-16, 2nd pass).** The scalar
`hcollapse` was pushed to completion this session and closed as a **negative result** (`OZFIX.14`,
`proof_notes_ozfix.md`): closing the contour on the pole sum is *value-neutral* — with `ρĈ(kₙ)=1` the
summands become `Res_k[S]·Ξ(k)` (`S := 1/(1−ρĈ)`, `Ξ` entire), the `1` of `S = 1+ρĤ` cancels **exactly at
every `R`** between the real line and the arc, and one is left with
`2πi·∑'Res = ρ∫_ℝ Ĥ(x)Ξ(x)dx` — the pole sum expressed **in terms of** the core value, which is the core
closure itself. So the scalar Route B does *not* prove the collapse; it restates it.
**Expect the same for MML.8**, whose (I)+(II)+(III) identity is the matrix analogue. Practical guidance:
1. Do **not** invest in the "expand `Ĥ₁` via MA.2 → invert via MA.3 → identify with `mixHS_series`" plan
   before checking whether the mixture *inner-core value* is an independent input (it almost certainly is).
2. The genuinely axiom-free path is the **matrix real-space Baxter/Wertheim–Thiele** derivation. Y1.3 +
   the matrix WH factorization are its Fourier half; the missing half is the real-space equation fixing
   the inner-core value for the concrete `q0_poly`-analogue.
3. Cheap legitimate alternative: axiomatize the **concrete, numerically-checkable series identity** (the
   mixture analogue of the scalar `CoreSeriesClosure`, `OzCollapseInner.lean`) instead of an abstract
   closure — same axiom count, strictly better checkability.
4. **Inherit the `Kterm` trap**: the natural `tsum` form of such an identity may be absolutely **divergent**
   (the scalar one is, for `u ≤ σ/2`), which would make it a FALSE and hence vacuous hypothesis. Check the
   decay exponent and add antiderivatives until it is `< −1` (scalar fix: `Kterm`, `‖·‖ ≲ ‖k‖^{−1−2u/σ}`).
5. The scalar **arc blocker was also refuted** (`OZFIX.10`, 2nd pass): a phase-split `e^{izb}` + two-regime
   bound suffices, no Van der Corput. If a matrix arc estimate is ever needed, use that technique.

**Status.** ◑ **Crux #1 (pole order / singly-vs-doubly) RESOLVED** (2026-07-16, axiom-clean);
**all prerequisites DONE** (2026-07-17: MML.5-concrete `detF_mixHS_summable`; MZERO.1
`detC_zeros_infinite_unconditional`; MZERO.5 retired). The collapse (Crux #2, VERY HARD) remains.
**Route status (2026-07-17):** the contour route is circular (scalar precedent `OZFIX.14`), so the
realistic path is the matrix real-space Baxter/Wertheim–Thiele derivation. The scalar precedent for
that path is now much sharper — `OZFIX.15–20` completed the *entire* scalar analytic core
(`ψ⋆Q₊⋆Q₋=φ`, the bridge, `F[K]=Ĉ`, `ρK=q0(v)−∫q0q0`, the 2D reindex), all axiom-clean — **but
`OZFIX.17` then exposed a genuine analytic OBSTACLE**: the assembly still needs the Baxter poles in
the open LHP ⇔ `baxterPsi` decay (simple `L¹` contraction REFUTED, `∫₀^σ|q0|≥1` for `η≳0.13`), which
is separate hard spectral content (`POLE.4`/`h_explicit`) not supplied by the analytic core. **The
matrix RDF collapse would inherit the matrix analog of exactly this decay input.** An axiom swap on
the concrete, numerically-checkable series identity (items 3–4 above) stays the cheap legitimate
alternative.

**OZFIX.22 template (2026-07-17) — the scalar reverse-assembly is now executed, and it is exactly
MML.8's recipe.** The scalar `oz_h`/`baxterPsi` *is* the RDF analog (the total-correlation `h`), and
`OZFIX.22` (`HardSphere/OzCoreClosure.lean`, full build green) retired `oz_core_closure` +
`oz_h_exterior_regularity` to **theorems** — consolidating the 3 OZ physics axioms to 2 — via the
single bridge `oz_h = baxterPsi/·` (proved by feeding the *constructed* `baxterPsi`, a bounded
exterior-continuous `OzFixedPt`, into `oz_fixed_pt_unique`), with the collapse then falling out of the
real-space OZ★ identity. Three ways this transfers to MML.8:
1. **Proven recipe.** MML.8's RDF collapse is the matrix version step-for-step: construct the explicit
   matrix real-space solution → show it is a bounded exterior-continuous matrix OZ fixed point →
   matrix-uniqueness bridge → collapse from the matrix OZ★. Not "VERY HARD/circular" anymore — a
   transcription task once the matrix ingredients exist.
2. **Axiom-swap is now a blessed pattern, not a fallback.** The hard decay input didn't get *proved* —
   it got cleanly isolated into the new axiom `baxter_exterior_regularity`, one explicit
   boundedness/decay statement about the *constructed* `baxterPsi` (`|baxterPsi r| ≤ C` on `[σ,∞)`),
   epistemically superior to the opaque physics axioms it replaced. MML.8's collapse can land as a
   theorem modulo the **matrix analog** of exactly this axiom.
3. **No decay-free route exists (definitive).** OZFIX.22's writeup refutes the earlier "decay-free
   3→2" designs: bounded OZ-uniqueness is *irreducibly* Wiener–Hopf (`∫₀^σ|q0| ≥ 1` for `η≳0.13`), so
   the difference of two bounded fixed points solves a non-causal homogeneous equation whose
   only-zero property **is** the pole-in-LHP fact. ⇒ MML.8 must **not** hunt a decay-free matrix
   route; the matrix decay axiom is unavoidable.

**Still needed before MML.8 can run the recipe** (what OZFIX.22 got for free in the scalar case):
a **matrix `oz_fixed_pt_unique`** (matrix OZ fixed-point uniqueness, irreducibly Wiener–Hopf, not yet
built for the mixture) and a **matrix OZ★** / matrix real-space Baxter identity for the
inverse-carrying RDF `h₁` — Group MRS is building the mixture real-space infra (MRS.3 (★) done,
MRS.4/5 in progress) but on the *DCF* side. Once both exist, MML.8's collapse is a mechanical
transcription of OZFIX.22 modulo the matrix decay axiom. **Priority is unchanged: RDF-only, off the
DCF path** — the template lowers MML.8's difficulty ceiling, not its priority.

**⇒ SHARPENED 2026-07-24 by MML.9 (below): the "matrix OZ★" MML.8 still needs is a
*hard-sphere* statement, not a Yukawa one.** `Ĥ₁ = S₀·Ĉ₁·S₀` with `Ĉ₁` HS-pole-free (MRS.3) and
finite (MRS.5) ⇒ every HS pole of the first-order RDF is contributed by the two `S₀ = (I−Ĉ₀)⁻¹`
factors, which contain **no Yukawa data at all**. The Yukawa half of MML.8 is therefore already
closed by Group MRS; the residual collapse content is the mixture **hard-sphere** RDF.

---

### Task MML.9 — the structure-factor form `Ĥ₁ = S₀·Ĉ₁·S₀`, and where the RDF's HS poles come from

**Statement.** Solve the same first-order OZ equation MRS.2 solves for the DCF, but for the RDF:
from `Ĥ₁·T₀ = S₀·Ĉ₁` (`hoz`) and `T₀·S₀ = I` (`hTS`, the zeroth-order OZ `S₀ = (I−Ĉ₀)⁻¹`),

    Ĥ₁ = Ĥ₁·(T₀·S₀) = (Ĥ₁·T₀)·S₀ = (S₀·Ĉ₁)·S₀ = S₀·Ĉ₁·S₀ .

Physically: **the first-order RDF is the first-order DCF dressed on both sides by the hard-sphere
structure factor** `S₀ = I + Ĥ₀`. Pure matrix algebra, and with *strictly weaker* hypotheses than
MRS.2's `star_of_first_order_oz` (no MRS.1 factorization, no MRS.7 symmetry).

**Why it matters for MML.8.** Combined with the two established facts

* **(★)** `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` carries no `Q̂₀⁻¹` ⇒ the first-order **DCF has no HS poles**
  (MRS.3 `star_entry_differentiableAt`) and is a finite closed form (MRS.5), and
* `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (MRS.6) ⇒ `det T₀ = det Q̂₀(k)·det Q̂₀(−k)`,

this **localizes the RDF's entire HS-pole content in the two `S₀` factors** — objects built from the
hard-sphere DCF `Ĉ₀` alone, with no Yukawa data in them. So MML.8's remaining collapse content is a
*hard-sphere* mixture statement; the Yukawa factor sandwiched between the two `S₀`s is finite and
pole-free, already delivered by Group MRS. This is a genuine narrowing of the "still needed" list
above, not a new route.

**Consequence — the pole set is reflection-symmetric, matching MML.5-concrete's convention.**
`det T₀ = det Q̂₀(k)·det Q̂₀(−k)` is invariant under `k ↦ −k`, so the RDF's HS poles are Group MZERO's
`det Q̂₀` zeros **together with their reflections**. That is exactly the "mirror pairing" the MML.8
completeness caveat refers to, and it is the same reflection `detF_mixHS_summable`
(`MixtureMLBound.lean`) already builds in (`s_k := −(g n)`, `Re s_k > 0`).

**Second, independent proof of Crux #1.** `rdf_entry_eq_num_div_det_sq` derives the `N/det²` shape —
hence the order-2 pole, hence term (II)'s `r`-prefactor — **from the OZ equation**, never mentioning
`B₁`. The original Crux #1 argument (`doubly_prop_entry_eq`) runs through Y1.6's
`Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`. Two independent routes to the same double-pole conclusion.

**The DCF/RDF dividing line as a single hypothesis.** `rdf_entry_differentiableAt` is the exact
counterpart of MRS.3's `star_entry_differentiableAt`, with one added hypothesis: `det T₀(k) ≠ 0`.
The DCF statement pointedly has no such hypothesis. That one hypothesis *is* the dividing line.

**The four-term dressing — the HS poles' exact residence (added 2026-07-24).** Writing the structure
factor as `S₀ = I + Ĥ₀` and expanding `Ĥ₁ = S₀·Ĉ₁·S₀` (`structureFactorDressing`,
`rdf_four_term_dressing`) gives

    Ĥ₁ = Ĉ₁ + Ĥ₀·Ĉ₁ + Ĉ₁·Ĥ₀ + Ĥ₀·Ĉ₁·Ĥ₀ ,

i.e. in real space `h₁ = c₁ + h₀⋆c₁ + c₁⋆h₀ + h₀⋆c₁⋆h₀`. Since `Ĉ₁` is finite and HS-pole-free
(MRS.3/MRS.5), the undressed term carries **no** HS pole, so `rdf_sub_dcf_is_dressed`
(`Ĥ₁ − Ĉ₁ = Ĥ₀·Ĉ₁ + Ĉ₁·Ĥ₀ + Ĥ₀·Ĉ₁·Ĥ₀`) locates **every** HS pole of the first-order RDF in the three
`Ĥ₀`-dressed terms. This is the sharpest form of MML.9's "the residual collapse content is
hard-sphere": MML.8's target `assembly = r·h₁` is term-by-term over exactly these three `h₀`-dressed
convolutions, and the mixture HS RDF `h₀` (= `S₀`'s pole content) is the only object whose ML
collapse is still owed. The Fourier identity is mechanical (`noncomm_ring`); the real-space
convolution reading of `⋆` is the still-missing transform step — the same transform gap that Group
MRS's finite-form assembly (MRS.5) is working through on the DCF side.

**Cofactor-free Laurent coefficients.** `double_pole_second_coeff` states `α_k` through the analytic
cofactor `E` of the simple-zero factorization `D = (·−s_k)·E`. `E` is auxiliary — a consumer (the
concrete `detF` family, or numerics) holds `D = det Q̂₀` and its derivatives, not `E`. Eliminating it
via `D′(s_k) = E(s_k)` and `D″(s_k) = 2·E′(s_k)` gives both coefficients in terms of `D` alone:

    β_k = N(s_k)/D′(s_k)²                                  (`double_pole_leading_coeff`)
    α_k = N′(s_k)/D′(s_k)² − N(s_k)·D″(s_k)/D′(s_k)³        (`double_pole_second_coeff_deriv_form`)

⚠ **The `D″` step needs only `ContinuousAt E′`, not a second derivative of `E`.** `D′ = E + (·−s_k)·E′`,
and the extra linear factor supplies the missing differentiability all by itself: `(·−s_k)·g` has
derivative `g(s_k)` at `s_k` for merely *continuous* `g` (`hasDerivAt_sub_mul_of_continuousAt`, one
line from the slope characterization). Attempting this with a `ContDiff`/2nd-order-Taylor hypothesis
on `E` is unnecessary work — the same "the linear factor does the analysis for you" observation that
made `double_pole_second_coeff` avoid the (ℂ-absent) L'Hôpital route.

**Depends on.** MRS.2 `oz1_C1_eq` (the dual it mirrors), MRS.3 (★), MRS.6 factorization,
MML.8 `double_pole_leading_coeff` / `double_pole_second_coeff`. Nothing new is assumed.

**Lean.** New file `YukawaDCF/MixtureRDFStructureFactor.lean` (ns `FMSA.MixtureRDF`), all
axiom-clean, full build green:
`oz1_H1_eq`, `structureFactor_eq_inv` (`T₀⁻¹ = S₀` — no invertibility hypothesis needed,
`Matrix.inv_eq_right_inv`), `rdf_eq_inv_conj`, `inv_conj_entry_eq` (the transpose-free sibling of
`doubly_prop_entry_eq`), `rdf_entry_eq_num_div_det_sq`, `det_eq_of_wienerHopf_factorization`,
`rdf_entry_star_eq` (capstone), `triple_entry_eq`, `adjugate_entry_differentiableAt` (`Fin 2`),
`rdf_entry_differentiableAt`, `rdf_entry_double_pole`; then
`hasDerivAt_sub_mul_of_continuousAt`, `factor_hasDerivAt`, `factor_hasDerivAt_at_zero`,
`factor_second_hasDerivAt`, `double_pole_second_coeff_deriv_form`; and the dressing
`structureFactorDressing`, `rdf_four_term_dressing`, `rdf_sub_dcf_is_dressed`.

**Lean pitfalls hit.** (1) `fin_cases p <;> fin_cases q` leaves indices as `⟨1, ⋯⟩`, which does **not**
match the numeral `1` for `rw` — use `Fin.forall_fin_two.2 ⟨…⟩` on a `∀ p q` conclusion instead.
(2) `field_simp` on the slope goal leaves a `s_k * (1 − 1) * g s_k` residue; close with `ring`.

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** Does **not** discharge `MixRDFInnerCollapse` — it
shows which poles are being summed (`S₀`'s, at `det Q̂₀`'s zeros and their reflections) and that
their order is 2, and it narrows MML.8's residual input to the hard-sphere side.

---

### Task MML.10 — term (II)'s coefficient factors as `HS residue × (finite Yukawa DCF) × HS residue`, and the mixture collapse factor

**Statement.** MML.9 says the RDF's HS poles all come from the two `S₀` factors. This task turns
that into an identity between *numbers*, and then extracts the mixture analog of the scalar
collapse factor.

**(a) The residue-matrix sandwich.** Define the hard-sphere structure factor's residue matrix at a
simple zero `s_k` of `det T₀`,

    R_k := det′T₀(s_k)⁻¹ • adj T₀(s_k) .

`structureFactor_entry_residue` certifies that this **is** the residue of `S₀ = T₀⁻¹` entrywise
(`inv_apply_eq_adj_div_det` + `residue_of_simple_pole`): **one `S₀` factor ⇒ one simple pole**, so
the RDF's two factors give the order-2 pole of MML.9's `rdf_entry_double_pole`. Then
`num_div_det_sq_eq_sandwich` (pure `smul` algebra) rewrites the order-2 Laurent coefficient as

    β_k = (R_k · Ĉ₁(s_k) · R_k) i j ,

and with (★) substituted (`rdf_double_pole_coeff_star`)

    β_k = (R_k · Q̂₀(−s_k) · B₁(s_k) · Q̂₀ᵀ(−s_k) · R_k) i j .

`R_k` is built from `T₀ = I − Ĉ₀` alone — **no Yukawa data whatsoever** — while `Ĉ₁(s_k)` is a plain
evaluation of the finite, HS-pole-free (★) closed form (MRS.3/MRS.5). So the MML.9 narrowing is no
longer only a structural reading: term (II)'s coefficients are *literally* factored into hard-sphere
spectral data × closed-form Yukawa data.

**(b) The mixture collapse factor — MML.8 Crux #2's "first concrete sub-piece", now trivial.**
The scalar `hcollapse` (`OZFIX.11`) turns on `ρĈ(kₙ) = 1`, i.e. `1 − ρĈ` vanishes at the pole, which
kills the forcing term per pole. MML.8's own scoping named the mixture counterpart as its first
concrete sub-piece — "`det(I−Ĉ_mix)(s_k) = 0` … entry-wise collapse will need the **adjugate-level**
version". Both now land in two lines:

* the determinant statement is `det_eq_of_wienerHopf_factorization` (MML.9) — MRS.6's
  `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` with `T₀ = I − Ĉ₀` its `Cmix0` definition;
* the adjugate-level statement is `hsResidue_annihilates`: `R_k·T₀(s_k) = T₀(s_k)·R_k = 0`,
  straight from Mathlib's `adjugate_mul` / `mul_adjugate` (`adj A·A = det A • I`) at `det A = 0`.

Rewriting with `T₀ = I − Ĉ₀` gives `hsResidue_eq_mul_cmix`:

    R_k = R_k · Ĉ₀(s_k) = Ĉ₀(s_k) · R_k ,

**the literal matrix transcription of `ρĈ(kₙ) = 1`** — the residue matrix is a fixed point of
multiplication by the hard-sphere DCF at the pole. (Scalar check: at `N = 1`, `R_k` is a nonzero
number and cancels, leaving `Ĉ₀(s_k) = 1`.)

⚠ **Why this was cheap and the 2026-07-17 scoping expected it to be expensive.** That scoping listed
the sub-piece as needing a matrix Wiener–Hopf factorization "currently ABSENT from Lean". MRS.6/MRS.7
supplied the factorization in the meantime, and once `hsResidueMatrix` is *defined through the
adjugate*, the collapse factor is a Mathlib one-liner rather than an analytic construction. The
lesson is the same as MML.5's: re-check a stale blocker against what has landed since.

**Depends on.** MML.9 (`rdf_entry_double_pole`, `det_eq_of_wienerHopf_factorization`), MML.2's
`residue_of_simple_pole` route, Y1.1's `inv_apply_eq_adj_div_det`, MRS.3 (★), MRS.6.

**Lean.** `YukawaDCF/MixtureRDFStructureFactor.lean`, axiom-clean, full build green:
`hsResidueMatrix`, `num_div_det_sq_eq_sandwich`, `structureFactor_entry_residue`,
`rdf_double_pole_coeff_sandwich`, `rdf_double_pole_coeff_star`, `hsResidue_annihilates`,
`hsResidue_eq_mul_cmix`.

**Lean pitfall.** In `hsResidue_eq_mul_cmix`, `rw [hT] at hL hR` also rewrites the `T0` *inside*
`hsResidueMatrix T0 Dprime`, desynchronising the hypothesis from the goal; and
`linear_combination (norm := module)` then reports the useless `⊢ 2 = 0`. Fix: never rewrite the
hypotheses — build `R*T₀ = R − R*C₀` as its own `have` (there `rw [hT]` rewrites *both* sides
uniformly, which is harmless), substitute `hL`, and finish with `sub_eq_zero.mp`.

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** Still does not discharge `MixRDFInnerCollapse`.
What MML.8 now has: the pole set (MZERO zeros + reflections), the pole order (2), both Laurent
coefficients in closed form (MML.9), the coefficients factored HS × Yukawa (a), and the per-pole
collapse factor (b). What it lacks is unchanged and is the hard part: the **real-space** step
identifying the summed series with the inner-core value — the matrix analog of `OZFIX.12`/`OZFIX.22`,
now visibly a hard-sphere-only obligation.

---

### Task MML.11 — the *concrete* term-(II) data: one pole family carrying poles, coefficients and summability

**Statement.** MML.9/MML.10 pinned the RDF's pole structure for free matrices. MML.11 produces the
concrete instance for the actual `N=2` mixture: a single explicit pole family on which the pole
locations, the order-2 Laurent coefficient, and MML.5's summability all live simultaneously.

**⚠ Which of the two `Ĥ₁` forms to instantiate — a real choice, not bookkeeping.** MML.9's
`Ĥ₁ = S₀·Ĉ₁·S₀` has denominator `det T₀ = det Q̂₀(k)·det Q̂₀(−k)`. Making *that* concrete would
require a zero of `det Q̂₀` to remain a **simple** zero of the product, i.e. `det Q̂₀(−s_k) ≠ 0` — a
reflection-asymmetry fact nobody has proved, and one that MZERO does not supply (MZERO gives
infinitude, not asymmetry). Y1.6's `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` has denominator `det Q̂₀(k)²`, so its
poles are the `det Q̂₀` zeros **directly** and simplicity there is exactly `det′ ≠ 0` — which the
strengthened MML.5 family now exports. The two forms agree (`oz1_H1_eq` vs `Hhat1_spec`); only the
Y1.6 one has an available concrete instance. **This is why MML.5's non-vanishing clause was worth
adding: it is the enabling hypothesis for MML.11, not a cosmetic tidy-up.**

**The chain.**
- `hhat1_entry_eq_num_div_det_sq` — `Ĥ₁ i j = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀) i j / (det Q̂₀)²`, from
  `(Mᵀ)⁻¹ = (det M)⁻¹ • (adj M)ᵀ` (`Matrix.adjugate_transpose` + `Matrix.det_transpose`). The
  transposed sibling of MML.9's `inv_conj_entry_eq` and of `doubly_prop_entry_eq`.
- `num_div_det_sq_eq_transpose_sandwich` + `hhat1_double_pole` — the order-2 coefficient is the
  residue-matrix sandwich `β_k = (R̃ᵀ·B₁(s_k)·R̃) i j`, `R̃ = det′(s_k)⁻¹ • adj Q̂₀(s_k)`
  (MML.10's `hsResidueMatrix`, now at `Q̂₀` instead of `T₀`).
- **`q0Residue_zero_one` — the loop closes on MML.5/MML.2**: `R̃ 0 1 = −q01(s_k)/det′(s_k)`. The
  `(0,1)` entry of MML.10's *matrix* residue is literally the `Bcoef` that `detF_mixHS_summable`
  sums and that `detF_Bcoef_eq_b_k_residue` certified to be MML.2's `B_k`. Matrix-level and
  scalar-level residues are **one object**, not two parallel constructions. (Proof: MML.1's
  `adjugate_fin_two_zero_one` `adj M 0 1 = −M 0 1`, plus `q01_eq`.)
- `detF_rdf_pole_family` — the capstone: for physical data and `rdist > max(σ₀/2,(σ₁−σ₀)/2)` there
  is **one** injective `g` with (i) `detF (g n) = 0 ∧ g n ≠ 0 ∧ det′(g n) ≠ 0`, (ii) the order-2
  pole of `Ĥ₁` at each `g n` with coefficient `rdfBeta P B1f (g n) i j`, (iii) `Summable` for the
  reflected series with coefficient `q0Residue P (g n) 0 1`.

**Non-vacuity.** The only hypothesis on the Yukawa side is entrywise continuity of `B₁`, satisfied
by any continuous matrix (and supplied in the physical case by the finite (★) closed form,
MRS.3/MRS.5); the parameter hypotheses are `P.Phys` + the `rdist` threshold, both satisfiable. The
coefficient clause states the *value* of the limit, not that it is nonzero — order-2-ness for a
particular `B₁` is `double_pole_leading_coeff_ne_zero` at `Num(s_k) ≠ 0`, separately.

**Depends on.** MML.5 (strengthened family), MML.10 (`hsResidueMatrix`), MML.2/MML.1, Y1.6
(`Hhat1`), MML.8's `double_pole_leading_coeff`.

**Lean.** New file `YukawaDCF/MixtureRDFPoleData.lean` (ns `FMSA.MixtureRDF`), axiom-clean, full
build green: `hhat1_entry_eq_num_div_det_sq`, `num_div_det_sq_eq_transpose_sandwich`,
`triple_entry_transpose_eq`, `adjugate_entry_continuousAt`, `hhat1_double_pole`, `q0Mat`,
`q0Mat_det` (`rfl`), `q0Residue`, `q0Residue_zero_one`, `rdfBeta`, `q0Mat_entry_continuousAt`,
`detF_rdf_pole_family`. `detF_mixHS_summable` (`MixtureMLBound.lean`) correspondingly upgraded to
export the simple-zero triple.

**Lean pitfalls.** (1) Mathlib has no `continuousAt_finset_sum`/`ContinuousAt.fun_sum` — use
`tendsto_finsetSum` (the `_finset_sum` spelling is deprecated), which applies directly because
`ContinuousAt f x` is definitionally the right `Tendsto`. (2) After `Summable.congr` the goal
carries unreduced beta redexes `(fun n ↦ …) n`, so `rw [q0Residue_zero_one]` fails to find its
pattern; `simp only [mixHSterm, q0Residue_zero_one]` beta-reduces and closes it.

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** Term (II) is now fully concrete. MML.8's residual
content is exactly the real-space identification (below), unchanged.

---

### Task MML.12 — the collapse *region*: a scoping correction, and what the ML series can never reach

**Trigger.** `MixRDFInnerCollapse` quantifies `∀ r, 0 < r → r < R_ij`, but term (II)'s convergence is
established only for `r > max(σ₀/2, (σ₁−σ₀)/2)` (MML.5's gate exponent
`p(r) = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁)` is `< −1` exactly there). The two ranges were never
reconciled.

**(1) Scoping correction — state the collapse on the annulus.** Below the threshold there is no
summability result, and the evidence points the wrong way: the scalar precedent (`Kterm`, `OZFIX.12`)
is genuinely **divergent** for `u ≤ σ/2`, and MML.5's own numerics measured `p(0.45) = −0.867 > −1`
at `σ = [0.8, 2.3]`. Lean's `tsum` of a non-summable family is the junk value `0`, so
`mixHS_series2` becomes `0` there and the predicate silently degenerates into `base r + p0 = r·h₁(r)`
— a *different* claim, with no reason to hold. **This is the `Kterm` vacuity trap the MML.8 notes
warned about (Crux #2, item 4), reaching MML.8 through the quantifier range rather than through the
summand** — which is why the earlier check ("add antiderivatives until the decay exponent is `< −1`")
did not catch it: the summand is fine, the *interval* is not.

⚠ **Honest disposition: this does not prove the `(0, R_ij)` form false.** It shows its content below
the threshold is unsupported and junk-valued. The fix is to state the identity where term (II)
converges — `MixRDFInnerCollapseAnnulus` — and `threshold_lt_contact` shows that region is **never
empty** (`max(σ₀/2, (σ₁−σ₀)/2) < (σ₀+σ₁)/2` for every physical pair, both branches strict from
`0 < σ₁` and `0 < σ₀`), so the restriction costs no generality.

**(2) Structural — the ML series only ever reaches the OUTER inner-core piece.** The threshold's
second branch is *exactly* the inner-core knot:

    (σ₁ − σ₀)/2  =  Mix.lam 0 1  =  λ₀₁ .

Hence `λ₀₁ ≤ max(σ₀/2, λ₀₁) = threshold` (`lam01_le_threshold`), and the entire collapse region lies
inside `(λ₀₁, R₀₁)` — the **outer** of the two pieces into which the unlike-pair inner core splits
(IB.4 / MPOLY.5: `(0,λ)` degree 1, `(λ,R)` degree 4). ⇒ **the HS-pole Mittag-Leffler series can never
certify the inner piece `(0, λ₀₁)`, whatever happens to MML.8's real-space step**; that piece must
come from Group MRS's finite closed form. The coincidence is not accidental in the other direction
either: MML.5 recorded that the `(σ₁−σ₀)/2` branch "binds only when `2σ₀ < σ₁`", and
`σ₀/2 ≥ λ₀₁ ⟺ 2σ₀ ≥ σ₁` — the same condition, now with a geometric reading.

This also sharpens the DCF/RDF division of labour: Group MRS covers the whole inner core with a
finite closed form; the RDF's ML series covers only its outer piece. They are not two routes to the
same interval.

**Depends on.** MML.5 (the threshold and its numerics), MML.11 (the concrete family), IB.4/MPOLY.5
(the `λ₀₁` split), `Mix.lam`/`Mix.R` (`InnerDecomp.lean`).

**Lean.** `YukawaDCF/MixtureRDFPoleData.lean`, axiom-clean, full build green: `rdfCollapseThreshold`,
`contactR01`, `lam01`, `lam01_le_threshold`, `lam01_lt_of_threshold_lt`, `threshold_lt_contact`,
`threshold_pos`, `exists_mem_collapse_region`, `MixRDFInnerCollapseAnnulus`,
`mixRDFInnerCollapseAnnulus_of_collapse` (the `(0,R)` form implies the annulus form; the converse
fails, and the difference is precisely the junk-valued region).

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** MML.8's target is now stated on the interval where
its own term (II) converges, and its reach is bounded below by `λ₀₁` for good.

---

### Task MML.13 — the `n = 1` soundness bridge for MML.9–MML.12

**Why.** MML.8's collapse is unproved and MML.9–MML.12 are matrix statements with **no consumer
yet**. The one mechanical test such a body of statements admits is the degenerate case: instantiate
at a single component and check it reproduces the *known* scalar theory rather than something new.
Same test MRS.0b ran on the consumer-less physics axiom `pyhs_mixture_no_spinodal`
(`MixtureNoSpinodalN1.lean`), and the project's record says it earns its keep — the statement bugs in
MA.5 (junk-valued zero set), MA.2 (partial-sum grouping) and `baxter_exterior_regularity` clause 6a
(a jump at `σ`) were all caught by confronting a case whose answer was independently known.

**Check 1 — the collapse factor.** MML.10's `R_k = R_k·Ĉ₀(s_k)` at `Fin 1` yields `Ĉ₀(s_k) = 1`, the
scalar `ρĈ(kₙ) = 1` behind `OZFIX.11` (`cmix_eq_one_fin_one`, routed through the matrix identity,
cancelling the nonzero `det′` via `hsResidueMatrix_fin_one`: `adj = 1` so `R = det′⁻¹ • I`).

⚠ **Read this correctly — it is a consistency check, not independent confirmation.** At `Fin 1` the
conclusion is already forced by `det T₀(s_k) = 0` alone (`cmix_eq_one_fin_one_of_det`, via
`Matrix.det_fin_one`, no residue matrix in sight). So the two routes are not independent evidence.
What the test rules out is a **sign slip, a transposition error, or a wrong `det′` power** in
`hsResidue_eq_mul_cmix` — any of those would land the first route somewhere else and contradict the
second. That is what a degenerate-case test can check, and all it can check; overstating it as
"two independent confirmations" would be wrong.

**Check 2 — the pole order.** `hhat1_fin_one_entry`: Y1.6's `Ĥ₁` at one component is the scalar
`B₁/(det Q̂₀)²`, a genuine **double** pole at a simple zero — matching the `Q̂₀⁻¹`-count reading (two
inverse factors ⇒ order 2) that MML.8's Crux #1 rests on.

**Check 3 — the term-(II) coefficient.** `hhat1_double_pole_fin_one`: MML.11's residue-matrix
sandwich `β_k = (R̃ᵀ·B₁(s_k)·R̃) i j` degenerates to the elementary scalar double-pole coefficient
`β_k = B₁(s_k)/det′(s_k)²`. **No matrix artifact survives** — the outcome the general formula had to
produce and did not have to.

**Non-vacuity certificate.** A degenerate-case test proves nothing if its own case is empty, and this
repo has produced true-but-vacuous statements before (`b4_origin_bc_abstract`,
`b9_d_ij_nonzero_example`). So the witness is recorded as a Lean `example`: `Q̂₀(z) = !![z − 1]` has a
simple determinant zero at `s_k = 1` with `det′ = 1 ≠ 0`, and a constant `B₁` is continuous — all
four hypotheses of `hhat1_double_pole_fin_one` (hence of `hhat1_double_pole`) simultaneously
satisfied.

**Lean.** `YukawaDCF/MixtureRDFPoleData.lean`, axiom-clean, full build green:
`hsResidueMatrix_fin_one`, `cmix_eq_one_fin_one`, `cmix_eq_one_fin_one_of_det`,
`hhat1_fin_one_entry`, `hhat1_double_pole_fin_one`, + the non-vacuity `example`.
Mathlib inputs: `Matrix.adjugate_fin_one` (`adj A = 1`), `Matrix.det_fin_one`, `Matrix.one_apply_eq`.

**Status.** ✓ **DONE (2026-07-24), axiom-clean. All three checks pass, no statement bug found.**
Unlike MA.5/MA.2/clause-6a, this bridge did **not** turn up a defect — a clean pass, recorded so that
a future session does not re-run it. It does not advance the collapse itself.

---

### Task MML.14 — matrix real-space infrastructure I: the antiderivative tower of term (II)

**The step past scaffolding.** MML.9–MML.13 characterised MML.8's remaining obligation; MML.14 begins
**building** the infrastructure that obligation needs. The scalar `hcollapse` (`OZFIX.11`/`OZFIX.12`)
runs on an **antiderivative tower** over the per-pole Fourier residue —
`residue_term → Hterm → Kterm` (`OzCollapseInner.lean`) — each rung one integration in `r` and one
power of `1/‖k‖` better in summability, so that `Kterm` (two rungs) is summable at **every** `u > 0`
and the inner region (sampled down toward `r = 0`) can be reached. MML.14 is the mixture counterpart.

**The key structural fact (proved).** The mixture per-pole term is already in hand as
`mixHSterm2 α β s r = (α + β·r)·e^{−s·r}` (the double pole's envelope, MML.8/MML.9/MML.11). Its tower
needs **no new function shapes**:

> the family `{(a + b·r)·e^{−s·r} : a, b ∈ ℂ}` (`expLinTerm`) is **closed under antidifferentiation
> in `r`**, with coefficient map `antiCoeff s (a,b) = (−a/s − b/s², −b/s)`.

`expLinTerm_antideriv_hasDerivAt` (`s ≠ 0`) proves `expLinTerm (antiCoeff s a b) s` is an
antiderivative of `expLinTerm a b s` — the mixture analog of `Kterm_hasDerivAt`. Iterating gives the
two concrete rungs `mixHSAntideriv1` (matrix `Hterm`) and `mixHSAntideriv2` (matrix `Kterm`), with the
`HasDerivAt` chain `mixHSAntideriv2 → mixHSAntideriv1 → mixHSterm2`.

**Why the tower buys summability, made precise.** `expLinTerm_norm`:
`‖(a+b·r)·e^{−s·r}‖ = ‖a+b·r‖·e^{−r·Re s}`, so on the reflected family (`Re s_n > 0`) the exponential
is `≤ 1` for `r ≥ 0` (`expLinTerm_norm_le_of_re_nonneg`) and the size is set by the coefficient. Each
`antiCoeff` divides by `s`: `antiCoeff_snd_norm` (`‖B‖ = ‖b‖/‖s‖`) and `antiCoeff_fst_norm_le`
(`‖A‖ ≤ ‖a‖/‖s‖ + ‖b‖/‖s‖²`). **Two rungs ⇒ two spare powers of `1/‖s_n‖`**, which should push the
summability exponent below `−1` *without* the `rdist > max(σ₀/2, λ₀₁)` threshold the untowered series
(MML.5) needs — the mixture form of `Kterm`'s all-`u>0` summability, and the mechanism that reaches
the inner core.

**Summability, reduced to one coefficient bound.** `mixHSAntideriv2_eq_mixHSterm` writes the `Kterm`
rung as a plain `mixHSterm` at its `r`-absorbed coefficient, and `mixHSAntideriv2_summable_of_growth`
then gives `Summable` from linear pole growth + a `‖s_n‖^p` bound (`p < −1`) on that coefficient
(reusing `mixHS_summable_of_growth`). **The one remaining analysis obligation is isolated as the
hypothesis `hbound`**: magnitude bounds on the double-pole coefficients `α_n`, `β_n` in `‖s_n‖` — the
mixture analog of the scalar `residue_term_norm_bound`, which MML.5's `detF_family_magnitude_bound`
did for the *simple*-pole residue `B_k = −q01/det′` but not yet for the double-pole `α, β`.

**Roadmap — the remaining rungs of the infrastructure.**
1. ✅ **Rung 1 DONE (2026-07-24) — the coefficient step is discharged.** See the Rung 1 note below.
   What remains of it is only the concrete `α, β` bounds (the mixture `residue_term_norm_bound`).
2. **The collapse predicate** — a matrix `CoreSeriesClosure`: an explicit, always-summable series
   identity (over the `Kterm` rung) equal to a polynomial in `r`, carried as a hypothesis exactly as
   the scalar `CoreSeriesClosure` is (⚠ the `Kterm`-form, not `Hterm`, to dodge the vacuity trap —
   this is the MML.12 lesson at the series level).
3. **The reduction** — a matrix `oz_collapse_inner_of_star`: per-pole integration by parts
   (`mixHSAntideriv2′ = mixHSAntideriv1`, `mixHSAntideriv1′ = mixHSterm2`, both proved here) converts
   the convolution over the annulus into `Kterm`-values at endpoints + one interval integral, which
   the collapse identity then closes by polynomial algebra.

**Depends on.** `mixHSterm2` (MML.8), `mixHS_summable_of_growth` (MML.5 infra). Mathlib:
`HasDerivAt.cexp`, `Complex.ofRealCLM.hasDerivAt`, `Complex.norm_exp`.

**Lean.** New file `YukawaDCF/MixtureRDFAntideriv.lean` (ns `FMSA.MixtureRDF`), axiom-clean, full
build green: `expLinTerm`, `mixHSterm2_eq_expLinTerm`, `expLinTerm_hasDerivAt`, `expLinTerm_deriv_eq`,
`antiCoeff`, `expLinTerm_antideriv_hasDerivAt`, `mixHSAntideriv1`/`2` + their `hasDerivAt` chain,
`expLinTerm_norm`, `expLinTerm_norm_le_of_re_nonneg`, `antiCoeff_snd_norm`, `antiCoeff_fst_norm_le`,
`mixHSAntideriv2Coeff`, `mixHSAntideriv2_eq_mixHSterm`, `mixHSAntideriv2_summable_of_growth`.

**Lean pitfall.** `once-/twice` in prose closes a `/-! -/` docstring early (the `-/`); write
`once- or twice-`. The `expLinTerm` derivative is cleanest via `rw [show <deriv-value> = <product-rule
form> from by ring]; exact hlin.mul hexp` rather than `convert … ; ring` (which leaves a non-ring
`HasDerivAt` goal fragment).

**Status.** ◑ **Tower + decay mechanism DONE (2026-07-24), axiom-clean.** Summability reduced to one
explicit coefficient bound, then Rung 1 (below) discharges that bound down to the concrete `α, β`
estimate. Roadmap rungs 2–3 remain.

---

### Task MML.14 Rung 1 — threshold-free summability of the `Kterm` tower

**What it delivers.** The `hbound` hypothesis left open by `mixHSAntideriv2_summable_of_growth` is now
proved from the inputs a concrete pole family actually supplies. Given a **common `‖s_n‖^q` bound**
(`q < 1`) on the two double-pole coefficients `α_n`, `β_n`, plus reflected positivity `Re s_n ≥ 0`,
`‖s_n‖ ≥ 1`, and linear pole growth, the `Kterm`-rung series `Σ_n mixHSAntideriv2` is `Summable` at
**every** `r ≥ 0` (`mixHSAntideriv2_summable_of_coeff_bounds`). The two `antiCoeff` divisions turn `q`
into the summability exponent `p = q − 2 < −1`, **with no `rdist > max(σ₀/2, λ₀₁)` threshold** — this
is exactly the mixture form of the scalar `Kterm`'s all-`u>0` summability (`Kterm_summable_of_pole_family`),
and it is what lets the tower reach arbitrarily close to `r = 0` (the inner-core sampling).

**The arithmetic, done once.**
- `mixHSAntideriv2Coeff_eq` — the `Kterm`-rung coefficient in closed form: `α/s² + 2β/s³ + (β/s²)·r`
  (`field_simp; ring` at `s ≠ 0`), exhibiting the two spare `1/s` powers concretely.
- `mixHSAntideriv2Coeff_norm_le` — `‖coeff‖ ≤ (‖α_n‖ + (2+r)·‖β_n‖) / ‖s_n‖²`, folding the `1/‖s‖³`
  term into `1/‖s‖²` via `‖s‖ ≥ 1`.
- `mixHSAntideriv2_summable_of_coeff_bounds` — assembles: on the reflected family
  `‖mixHSterm coeff‖ = ‖coeff‖·e^{−r·Re s} ≤ ‖coeff‖` (the exp is a genuine decay), then the coeff
  bound + the `‖s_n‖^q` inputs land `‖·‖ ≤ Cc(3+r)·‖s_n‖^{q−2}`, and `mixHS_summable_of_growth`
  closes it. The `‖s‖^q/‖s‖² = ‖s‖^{q−2}` step is `Real.rpow_sub` + `Real.rpow_two`.

**The remaining concrete input — reduced twice, then validated.** The `α, β` bounds are the mixture
analog of the scalar `residue_term_norm_bound`. From MML.11, `β_n = N(s_n)/det′(s_n)²` and
`α_n = N′(s_n)/det′(s_n)² − N(s_n)·det″(s_n)/det′(s_n)³`, with `N = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀)ᵢⱼ`. Rung 1
(below) discharges this down to **component** magnitudes and then confirms `q < 1` genuinely holds.
Isolated as `hα`, `hβ`.

**Reduction to component magnitudes (`mixHSAntideriv2_summable_of_component_bounds`).** The `α, β`
bounds reduce, by pure algebra, to component magnitudes on the RDF numerator: `coeff_div_sq_norm_le`
gives `‖β‖ = ‖N/det′²‖ ≤ ‖N‖/c₀²` and `coeff_alpha_norm_le` gives
`‖α‖ ≤ ‖N′‖/c₀² + ‖N‖·‖det″‖/c₀³`, from a constant `det′` lower bound `c₀` (MML.5's `disk_facts` f3).
So the tower is summable given common `‖s_n‖^q` (`q < 1`) bounds on `‖N‖`, `‖N′‖`, and the *product*
`‖N‖·‖det″‖`.

**⚠ A live scoping question — resolved in the tower's favour (`bMulti_norm_le`).** Whether `q < 1`
actually holds turns on the growth of the Yukawa numerator `B₁` along the pole family. Earlier worry:
if `B₁` carried the outer DCF's `e^{−ikR}` it could grow like `‖s_n‖^{2R/σ₁}` at the raw zeros
(`Re s_n < 0`), forcing `q ≥ 1` and reinstating the MML.5 `rdist` threshold (the tower buying nothing
past MML.12's annulus). **It does not.** The WH-projected `B₁` is the spectral amplitude
`bMulti = Σ_{m,p} c_{mp}/(s + z_{mp})` — a **pure sum of simple poles, no exponential** (the `e^{−ikR}`
lives in the *outer* transform `U₁` and is absorbed into the residues by the causal projection,
`outer_residue_eq_spectralAmp_residue`). `bMulti_norm_le` (`SpectralAmplitude.lean`, axiom-clean)
proves `‖B₁(s)‖ ≤ C·N²/‖s‖` past the pole radius: **`B₁` decays like `1/‖s‖`.** With the adjugate
entries bounded (`q0_entry_c → δ`) and `det Q̂₀ → 1` (`Q0_det_c_tendsto_one`, so `det′, det″` bounded),
all three component bounds hold with `q < 1` (in fact strongly negative). The tower is genuinely
threshold-free.

**The numerator assembly (`triple_transpose_entry_norm_le`, `tower_summable_of_matrix_bounds`).**
The RDF numerator `N = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀)ᵢⱼ` bound is now **assembled from entry-level primitives**:
`triple_transpose_entry_norm_le` gives `‖(Aᵀ·B·A)ᵢⱼ‖ ≤ NN²·Ca²·Cb` from `‖A_pq‖ ≤ Ca`, `‖B_pq‖ ≤ Cb`
(via the proved `triple_entry_transpose_eq` + finite triangle inequality). Feeding the adjugate entry
bound `Ca` and the Yukawa entry bound `Cb·‖s_n‖^q` (which `bMulti_norm_le` supplies at `q = −1`) gives
`‖N(s_n)‖ ≤ K·‖s_n‖^q`, and `‖N·det″‖ ≤ K·CDpp·‖s_n‖^q` (`det″` bounded). `tower_summable_of_matrix_bounds`
then closes tower summability from these plus the `det′` lower bound `c₀` and the `N′` bound — the
`N`- and `N·det″`-sides are assembled internally; only `N′` is an input.

**What is left of Rung 1.** Two mechanical pieces, no open obstacle:
1. **The `N′` assembly** — the same triple-product pattern applied to `N′ = (adj′ᵀ·B₁·adj + adjᵀ·B₁′·adj
   + adjᵀ·B₁·adj′)ᵢⱼ`, needing the adjugate/`B₁` *derivative* entry bounds (a `bMulti′` decay `~1/‖s‖²`
   and `q0_entry_c′` bounds). Taken as the input `hNd` for now.
2. **The raw per-entry primitives** — `‖adj Q̂₀(s_n)‖ ≤ Ca`, `‖B₁‖ ≤ Cb/‖s_n‖` (`bMulti_norm_le`, done),
   `‖det″‖ ≤ CDpp`, `c₀ ≤ ‖det′‖` (`disk_facts` f3) — standard magnitude estimates on the *explicit*
   Baxter matrix and its determinant, i.e. the mixture `residue_term_norm_bound`; the `adj` bound is a
   `q01_norm_le`-style estimate on the pole disks, `det″` bounded from `det Q̂₀ → 1`. Cofinite-to-`∀n`
   bookkeeping (`bMulti_norm_le` needs `‖s‖` past the pole radius) is the only wiring subtlety.
The crux (`B₁` growth) is settled and the numerator assembly is complete; what remains is the
per-entry magnitude grind, not new structure.

**Depends on.** MML.14 tower; `bMulti` (Y1.5, `SpectralAmplitude.lean`); MML.11 coefficient formulas;
`Q0_det_c_tendsto_one`, `disk_facts` f3. Mathlib: `Real.rpow_sub`, `Real.rpow_two`, `div_le_div₀`,
`pow_le_pow_left₀`, `Complex.norm_real` (⚠ → real `‖r‖`, then `Real.norm_eq_abs`).

**Lean.** `YukawaDCF/MixtureRDFAntideriv.lean` (`mixHSAntideriv2Coeff_eq`,
`mixHSAntideriv2Coeff_norm_le`, `mixHSAntideriv2_summable_of_coeff_bounds`, `coeff_div_sq_norm_le`,
`coeff_alpha_norm_le`, `mixHSAntideriv2_summable_of_component_bounds`);
`YukawaDCF/SpectralAmplitude.lean` (`bMulti_norm_le`); `YukawaDCF/MixtureRDFPoleData.lean`
(`triple_transpose_entry_norm_le`, `tower_summable_of_matrix_bounds`) — all axiom-clean, full build green.

**Lean pitfalls.** A binder `∀ n, … (n:ℝ) … sfam n …` makes Lean infer `n : ℝ` from the cast —
annotate `∀ n : ℕ`. `Complex.norm_real` rewrites `‖(r:ℂ)‖` to the *real* norm `‖r‖`, not `|r|` (follow
with `Real.norm_eq_abs`). `div_le_div` is renamed `div_le_div₀`.

**Status.** ✅ **DONE (2026-07-24), axiom-clean.** The tower is summable threshold-free; the full
reduction chain is built (tower ← coefficient ← component ← matrix-primitive bounds); the RDF
numerator `N` and `N·det″` are **assembled** from entry bounds (`tower_summable_of_matrix_bounds`); and
the crux (`B₁` decays like `1/‖s‖`, `bMulti_norm_le`) is proved, so `q < 1` genuinely holds and the
tower approach is validated. What remains is purely the per-entry magnitude grind — the `N′` assembly
(same triple-product pattern) and the standard `adj`/`det″` bounds on the explicit Baxter matrix (the
mixture `residue_term_norm_bound`), no new structure. Roadmap rung 2 (matrix `CoreSeriesClosure`)
remains; rung 3 (the integration-by-parts toolkit) is done — see below.

---

### Task MML.14 Rung 3 — the per-pole integration-by-parts toolkit

**What it delivers.** The scalar `hcollapse` reduction (`OZFIX.12`, `oz_collapse_of_two_sigma_le`) runs
on **per-pole integration by parts** — the antiderivative tower `Kterm′ = Hterm`,
`Hterm′ = h_explicit_term` turns the collapse's outer `t`-integral into endpoint antiderivative values
plus a lower-order integral, which the core series identity then closes. Rung 3 is the mixture analog,
built directly on MML.14's proved `HasDerivAt` chain `mixHSAntideriv2 → mixHSAntideriv1 → mixHSterm2`,
all axiom-clean:

* `expLinTerm_continuous` — the `(a+b·r)e^{−s·r}` shape is continuous in `r` (⇒ interval-integrable).
* `mixHSterm2_integral` / `mixHSAntideriv1_integral` — **per-pole FTC** on the two rungs:
  `∫_a^b mixHSterm2 = [mixHSAntideriv1]_a^b`, `∫_a^b mixHSAntideriv1 = [mixHSAntideriv2]_a^b`
  (`integral_eq_sub_of_hasDerivAt` + the chain).
* `mixHSterm2_weighted_ibp` — **integration by parts against a weight** `w`:
  `∫_a^b w·mixHSterm2 = [w·mixHSAntideriv1]_a^b − ∫_a^b w′·mixHSAntideriv1`
  (`integral_mul_deriv_eq_deriv_mul`). This is the step that moves the derivative off the per-pole
  term onto the weight, lowering the integrand's `r`-order — the mechanism the collapse's outer
  integral needs.
* `mixHSterm2_integral_tsum` — **termwise integration of the series**:
  `∫_a^b (∑ₙ mixHSterm2 · n) = ∑ₙ [mixHSAntideriv1 n]_a^b`, from `MeasureTheory.integral_tsum`
  (each summand continuous ⇒ `AEStronglyMeasurable`) + the per-pole FTC. The `L¹` hypothesis
  `∑ₙ ∫⁻ ‖·‖ₑ ≠ ∞` holds on the annulus, where the term series is summable (MML.5). This carries the
  collapse from `r·h₁ = r·(∑ …)` to a per-pole endpoint sum.

**What the full reduction still needs (not this task).** Rung 3 is the *plumbing*; the full matrix
`oz_collapse_of_two_sigma_le` additionally requires (i) Rung 2's matrix `CoreSeriesClosure` — the
series identity that closes the endpoint terms — and (ii) the **matrix OZ★** real-space convolution
that exhibits the collapse as such an integral identity in the first place (the mixture
`baxterPsi_eq_phi_add_rho_conv`, still unbuilt). Rung 3 gives the calculus that consumes those two;
it does not supply them.

**Depends on.** MML.14 tower `HasDerivAt` chain (`mixHSAntideriv1_hasDerivAt`,
`mixHSAntideriv2_hasDerivAt`). Mathlib: `integral_eq_sub_of_hasDerivAt`,
`integral_mul_deriv_eq_deriv_mul`, `MeasureTheory.integral_tsum`.

**Lean.** `YukawaDCF/MixtureRDFAntideriv.lean` (§ Rung 3): `expLinTerm_continuous`,
`mixHSterm2_integral`, `mixHSAntideriv1_integral`, `mixHSterm2_weighted_ibp`,
`mixHSterm2_integral_tsum` — all axiom-clean, full build green.

**Lean pitfall.** The enorm notation `‖·‖ₑ` (needed for `integral_tsum`'s hypothesis) requires
`open ENNReal` (or `open scoped ENNReal`) — without it, `‖x‖ₑ` fails to parse ("expected token"),
even under `open MeasureTheory`. `Continuous.intervalIntegrable`/`.aestronglyMeasurable.restrict` take
the endpoints/measure explicitly.

**Status.** ✅ **DONE (2026-07-24), axiom-clean.** The per-pole IBP/FTC toolkit is complete. The full
collapse reduction is gated on Rung 2 (`CoreSeriesClosure`) and the matrix OZ★ — neither of which is
Rung 3.

---

### Task MML.14 Rung 2 — the matrix `CoreSeriesClosure` predicate and its non-vacuity

**What it delivers.** The scalar collapse reduces to a single series identity `CoreSeriesClosure`
(`OzCollapseInner.lean`): the twice-antidifferentiated (`Kterm`-form), always-summable residue
series, corrected by its first-order Taylor data at the anchor `σ`, equals an explicit polynomial in
`u` (content: *the exterior residue series, continued into the core, reproduces the inner value*).
Rung 2 is the matrix analog — the predicate plus its non-vacuity.

* `MixCoreSeriesClosure alpha beta sfam anchor poly` — the predicate: on `(0, anchor]`,
  `∑ₙ [mixHSAntideriv2(r) − mixHSAntideriv2(anchor) − (r−anchor)·mixHSAntideriv1(anchor)] = poly r`.
  The bracket is the **first-order Taylor remainder** of `mixHSAntideriv2` at `anchor` (since
  `mixHSAntideriv2′ = mixHSAntideriv1`, MML.14 chain). `poly : ℝ → ℂ` is general (the matrix analog
  of the scalar's `π(σ²(u−σ) − (u³−σ³)/3)`; its concrete value comes from the inner core via the
  unbuilt matrix OZ★).
* `mixCoreSeriesClosure_summand_summable` — **non-vacuity**: the summand is `Summable` from the three
  Rung-1 summabilities (`mixHSAntideriv2` at `r`, at `anchor`; `mixHSAntideriv1` at `anchor`), so the
  predicate is about a *convergent* `tsum` — exactly the scalar `coreSeriesClosure_summand_summable`.
* `mixHSAntideriv1_summable_of_coeff_bounds` — the `Hterm`-rung summability that discharges the
  `mixHSAntideriv1` hypothesis: one `antiCoeff` gain ⇒ exponent `q − 1`, so it needs `q < 0` (vs the
  `Kterm` rung's `q < 1`); the RDF's `q ≈ −1` clears it. Plumbing: `mixHSAntideriv1Coeff`,
  `_eq_mixHSterm`, `mixHSAntideriv1Coeff_norm_le` (one `1/‖s‖` gain).

⚠ **The `Kterm`-form is essential — MML.12's vacuity lesson at the series level.** The `Hterm`-form
(`mixHSAntideriv1`) series is summable only for `q < 0` at a fixed point and (raw) only above the
MML.5 threshold, so a predicate stated on it would be false/vacuous near `r = 0`. The `Kterm`-form
(`mixHSAntideriv2`) is summable at every `r ≥ 0` (Rung 1), and the *remainder* combination is
genuinely summable — this is why the predicate uses `mixHSAntideriv2` with the first-order correction,
not a bare series.

**Held as a `Prop`, not an axiom** — identical discipline to the scalar `CoreSeriesClosure`: a naive
series-value axiom is satisfiable by sub-families summing to the wrong value (`MZERO.1`-infinitude ≠
pole-exhaustion). It is discharged only by a genuine pole-enumerating family, and the concrete `poly`
needs the matrix OZ★ real-space identity — the one input Rung 2 does not (and should not) supply.

**Depends on.** MML.14 tower (`mixHSAntideriv1`/`2`, `mixHS_summable_of_growth`); Rung 1 summabilities.

**Lean.** `YukawaDCF/MixtureRDFAntideriv.lean` (§ Rung 2): `mixHSAntideriv1Coeff`,
`mixHSAntideriv1_eq_mixHSterm`, `mixHSAntideriv1Coeff_eq`, `mixHSAntideriv1Coeff_norm_le`,
`mixHSAntideriv1_summable_of_coeff_bounds`, `MixCoreSeriesClosure`,
`mixCoreSeriesClosure_summand_summable` — all axiom-clean, full build green.

**Status.** ✅ **DONE (2026-07-24), axiom-clean.** The predicate is defined and proved non-vacuous.
What remains for the full collapse is discharging `MixCoreSeriesClosure` for the genuine pole family —
which needs the **matrix OZ★** (the concrete `poly` from the inner value) — plus the matrix
`oz_fixed_pt_unique` bridge, i.e. the mixture real-space Baxter core (`OZFIX.15–20` analog), started
below (MML.15).

---

### Task MML.15 — matrix OZ★: the mixture real-space OZ identity (foundation / START)

**The last unbuilt piece of MML.8's infrastructure, launched.** The three calculus rungs (Rung 1
summability, Rung 2 `CoreSeriesClosure`, Rung 3 IBP) are complete; they all **consume** the matrix
OZ★ — the real-space matrix Ornstein–Zernike identity that (i) exhibits the collapse as an integral
identity and (ii) supplies `MixCoreSeriesClosure`'s concrete `poly` from the inner value. The scalar
OZ★ `baxterPsi_ozstar` (`BaxterOzStar.lean`, unconditional) is
`baxterPsi(r) = r·c_HS(r) + ρ·r·radial3d_conv(c_HS, baxterPsi/·)(r)`; the general-`N` matrix analog is
the mixture version of the *entire* `BaxterRenewal.lean` + `BaxterOzStar.lean` apparatus
(`OZFIX.15–20`) — large. MML.15 lays the **structural foundation** and validates the target shape.

* `matRadialConv` — the entrywise matrix radial convolution `(A ⋆ B)ᵢⱼ = ∑ₖ radial3d_conv(Aᵢₖ, Bₖⱼ)`,
  reducing the matrix OZ convolution to the *scalar* `radial3d_conv` machinery per entry, with a
  **species-coupling sum** over the intermediate `k`.
* `MatOZStar Ψ Φ ρ` — the matrix OZ★ predicate: `Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·r·(matRadialConv Φ (Ψ/·))ᵢⱼ(r)`
  for `r > 0`. Held as a `Prop` — the concrete `Ψ, Φ` and the proof are the matrix-Baxter construction
  (the research-scale remainder); this fixes the *target shape*.
* `matOZStar_entry` — the explicit coupled entry equation, exhibiting the `∑ₖ radial3d_conv(Φᵢₖ, Ψₖⱼ/·)`
  species coupling that makes the matrix OZ★ genuinely more than `N` independent scalar problems.
* `matOZStar_fin_one_of_scalar` — **the `n = 1` soundness bridge**: at one component `MatOZStar`
  (`Ψ = baxterPsi`, `Φ = c_HS`) is *exactly* the proved scalar `baxterPsi_ozstar`. The framework
  specializes correctly to the known scalar theory (MML.13 / MRS.0b discipline) and this doubles as a
  non-vacuity witness — `MatOZStar` is instantiable, not a vacuous `Prop`.

**The real-space factorization foundation (started 2026-07-24).** The scalar OZ★ is *built on* the
real-space Baxter factorization (`OZFIX.18` KDEF, `rho_baxterK_eq_q0_self_conv`):
`ρ·K(v) = q0(v) − ∫_v^σ q0(t)·q0(t−v)dt`, the real-space content of `1 − ρĈ = Q̂(k)·Q̂(−k)`. The
mixture factorization `I − Ĉ₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (MRS.6 `Cmix0_factorization`, Fourier) inverse-
transforms with the same second foundational layer, now built:
* `matSelfConv` — the matrix self-convolution `(Q ⋆ Qᵀ)ᵢⱼ(v) = ∑ₖ ∫_v^σ Qᵢₖ(t)·Qⱼₖ(t−v) dt`, the
  real-space image of `Q̂₀(k)·Q̂₀ᵀ(−k)` (the `ᵀ` gives the species-summed `∑ₖ`; the `−k` makes it a
  correlation), reducing to the scalar self-convolution per entry-pair.
* `MatBaxterFactorization` — the matrix real-space KDEF `ρ·Kᵢⱼ(v) = qᵢⱼ(v) − (matSelfConv q)ᵢⱼ(v)` on
  `(0, σ)`, held as a `Prop`.
* `matBaxterFactorization_fin_one_of_scalar` — the **`n = 1` bridge**: at one component
  (`K = baxterK`, `q = q0_poly`) it is *exactly* the scalar `rho_baxterK_eq_q0_self_conv`.

**The shell-conv = K-conv bridge — third layer (`OZFIX.19` analog, 2026-07-24).** The scalar
`radial3d_conv_eq_baxterK_shell` ties the 3D radial convolution (the OZ★ shape) to a 1D convolution
with the Baxter shell kernel `K` (the factorization): `r·radial3d_conv(c_HS, g)(r) = ∫₀^σ baxterK(u)·
(oddExt g(r−u) + oddExt g(r+u)) du`. **The matrix analog is that scalar identity summed over the
intermediate species `k`** — no new analysis, since `matRadialConv` is a sum of scalar
`radial3d_conv`s and `r` pulls inside the sum:
* `matShellConv` — the 1D Baxter-kernel form `∑ₖ ∫₀^σ Kᵢₖ(u)·(oddExt Gₖⱼ(r−u) + oddExt Gₖⱼ(r+u)) du`.
* `matRadialConv_eq_matShellConv` — the bridge `r·(matRadialConv C G)ᵢⱼ = (matShellConv K G)ᵢⱼ` from
  the per-`(i,k)` scalar shell identity (`hentry`); pure assembly (`Finset.mul_sum` + `sum_congr`).
* `matShellBridge_fin_one_of_scalar` — the **`n = 1` bridge**: the per-entry `hentry` is exactly the
  proved scalar `radial3d_conv_eq_baxterK_shell` (carrying its two integrability hypotheses,
  discharged unconditionally in `BaxterOzStar.lean` for `g = baxterPsi/·`). This layer connects the
  OZ★ shape (layer 1, `matRadialConv`) to the factorization (layer 2, `matSelfConv`/`K`).

**The general-`c` shell identity — the per-entry analytic input, now proved (2026-07-24).** The
mixture entries `C₀ᵢₖ` are each a different `c`-shape at their own `σ_ik`, not the single `c_HS`, so
the shell bridge's `hentry` needed the shell identity for an *arbitrary* kernel. `ShellKernel.lean`
supplies it: `shellKernel c σ v = 2π ∫_|v|^σ s·c(s) ds` (the general Baxter shell kernel), and
`radial3d_conv_eq_shellKernel` proves `r·radial3d_conv(c, g)(r) = ∫₀^σ shellKernel(c)(u)·(oddExt
g(r−u)+oddExt g(r+u)) du` for **any** `c` supported in `[0,σ]`. The proof is a transcription of the
scalar `radial3d_conv_eq_baxterK_shell` with `c_HS → c`, `baxterK → shellKernel c`, `c_HS_outer →
hc_outer` — `c_HS` was used only through its support and `baxterK`'s definition; everything else
(`radial3d_conv_eq_oddExt`, `intervalIntegral_triangle_swap`, the inner shell reassembly) is generic.
`shellKernel_c_HS` confirms it reduces to `baxterK`. **Consumed by**
`matRadialConv_eq_matShellConv_of_shellKernel` (`MixtureOzStar.lean`): the matrix shell bridge with
the kernel *built from the entries* `Kᵢₖ = shellKernel(C₀ᵢₖ)`, discharging `hentry` per entry — the
general-`N` form the assembly consumes, with only per-entry support + integrability as hypotheses.

**The matrix `baxterPsi` construction — shape + renewal equation (2026-07-24).** The scalar
`baxterPsi` is the three-branch glued solution (outer Volterra `baxterPsiOuter` on `[σ,∞)`, odd
reflection, definitional core `−v`), satisfying `baxterPsiOuter_spec`. The matrix analog now has the
same shape:
* `matBaxterPsi Ψouter Ψcore σ` — the glued matrix solution; `matBaxterPsi_core` / `_outer` /
  `_reflect` the branch equations.
* `MatRenewalEq Ψouter F Q σ` — the matrix renewal equation `Ψouterᵢⱼ(r) = Fᵢⱼ(r) + ∑ₖ ∫_σ^r
  Qᵢₖ(r−t)·Ψouterₖⱼ(t) dt` (`r ≥ σ`), the **coupled** Volterra system across species `k` (the
  coupling that distinguishes it from `N` scalar renewals).
* `matBaxterPsi_fin_one_of_scalar` / `matRenewalEq_fin_one_of_scalar` — the **`n = 1` bridges**: the
  matrix `baxterPsi` core is the scalar `baxterPsi`, and `MatRenewalEq` is the proved scalar
  `baxterPsiOuter_spec`.
**`Ψouter` is now constructed (2026-07-24) — the coupled matrix Volterra is solvable.** The mixture
renewal `Ψ(r) = F(r) + ∫_σ^r Q(r−t)·Ψ(t) dt` is a **matrix product** — the species-coupling sum
`∑ₖ Qᵢₖ·Ψₖⱼ` *is* `(Q·Ψ)ᵢⱼ` — so it is a Volterra equation on the complete normed ring
`E = Matrix (Fin N) (Fin N) ℝ`. Two pieces:
* **`Analysis/VolterraBanach.lean` — the Banach generalization of `MA.10`.** For any complete normed
  ring `E` (`NormedRing`, `NormedAlgebra ℝ`, `CompleteSpace`) and continuous convolution kernel
  `q : ℝ → E`, `volterra_convolution_existsUniqueE` gives a unique continuous `E`-valued solution of
  `u(r) = g(r) + ∫_a^r q(r−t)·u(t) dt`. The proof is the *identical* iterate-contraction argument as
  the scalar `MA.10`; the only change is `|K·u| ≤ M·|u|` becoming `‖q·u‖ ≤ ‖q‖·‖u‖` via `norm_mul_le`
  (submultiplicativity). Axiom-clean — a mechanical generalization, not new mathematics.
* **`matVolterra_convolution_existsUnique`** (`MixtureOzStar.lean`) — the instantiation at
  `E = Matrix (Fin N) (Fin N) ℝ` under the submultiplicative `Matrix.linftyOp` norm: the matrix
  renewal has a unique continuous matrix solution `Ψouter`. The entrywise `MatRenewalEq` form follows
  by matrix-entry evaluation commuting with the integral (`Matrix.mul_apply` +
  `ContinuousLinearMap.intervalIntegral_comp_comm`), a mechanical step.

**Entry-extraction is complete — the matrix-norm plumbing is solved (2026-07-24).** The entrywise
`MatRenewalEq` (`∑ₖ ∫ Qᵢₖ·Ψₖⱼ`) from the matrix-product solution needs `(∫ f)ᵢⱼ = ∫ fᵢⱼ` (entry
evaluation commuting with the matrix Bochner integral), through
`ContinuousLinearMap.intervalIntegral_comp_comm` at the entry CLM, hence through
`IntervalIntegrable (f : ℝ → Matrix ℝ)`.

⚠ **The instance-diamond fix.** That predicate does not elaborate on its own under the `letI`'d
`Matrix.linftyOp` norm — `ENormedAddMonoid (Matrix ℝ)` is not synthesized, because the default
`Matrix` product topology competes with the norm's and
`NormedAddCommGroup.toENormedAddCommMonoid`'s topology does not unify (it *is* synthesized for an
abstract `[NormedAddCommGroup E]`, so a Matrix-topology-diamond, not a gap). **The one-line fix:
`letI : ENormedAddCommMonoid (Matrix ℝ) := NormedAddCommGroup.toENormedAddCommMonoid`**, which pins
the norm-induced topology. Three lemmas then close the extraction:
* `matrix_intervalIntegral_apply` — `(∫ f)ᵢⱼ = ∫ fᵢⱼ` (via the entry CLM + the fix).
* `matrix_mul_intervalIntegral_entry` — `(∫ Q·U)ᵢⱼ = ∑ₖ ∫ Qᵢₖ·Uₖⱼ` (`matrix_intervalIntegral_apply`
  + `Matrix.mul_apply` + `intervalIntegral.integral_finsetSum`).
* `matRenewalEq_of_matrixProduct` — **end-to-end**: a matrix-product renewal `Ψ(r) = F(r) + ∫ Q(r−t)·
  Ψ(t) dt` (the `matVolterra_convolution_existsUnique` form) *is* `MatRenewalEq` for the entry
  families. So `Ψouter` is now constructed in the exact `∑ₖ` form the matrix `baxterPsi` consumes.

**Matrix `F[K]=Ĉ` DONE (2026-07-24, `OZFIX.18` F-part).** The scalar `baxterK_cos_eq_radial_fourier`
matches the Fourier transform of the Baxter shell kernel with the DCF `radial_fourier`. Its
matrix form is that identity per entry, so the genuine content is the **general-`c` version**, now
proved in `HardSphere/ShellKernel.lean` (like the shell identity, `c_HS`-independent):
* `shellKernel_hasDerivAt` — `shellKernel(c)′(v) = −2π·v·c(v)` on `(0,σ)` (FTC-1, the general-`c`
  `hasDerivAt_baxterK`); `shellKernel_apply_sigma` (`K(σ)=0`), `shellKernel_continuousOn` (primitive).
* `radial_fourier_eq_intervalIntegral_of_support` — `radial_fourier(c) = (4π/k)∫₀^σ r·c(r)·sin`
  for `c` supported in `[0,σ]`.
* `shellKernel_cos_eq_radial_fourier` — `2∫₀^σ shellKernel(c)·cos(kv) = radial_fourier(c)(k)`, one
  integration by parts (boundary killed by `K(σ)=0`), for `c` supported in `[0,σ]`, continuous on the
  open core, `s·c(s)` interval-integrable.
`MixtureOzStar.lean`: `matShellKernel_cos_eq_radial_fourier` (per entry `C₀ᵢⱼ`) +
`matShellKernel_cos_eq_radial_fourier_fin_one_of_scalar` (the `n = 1` bridge to
`baxterK_cos_eq_radial_fourier`).

**Matrix 2D reindex DONE (2026-07-27, `OZFIX.20`).** The scalar `dbl_conv_reindex` uses the *same*
`q0` for both Baxter factors; the matrix self-convolution `matSelfConv i j = ∑ₖ Qᵢₖ⋆Qⱼₖ` couples
*different* factors `Qᵢₖ, Qⱼₖ` (off-diagonal), so the genuine content is a **two-function** reindex:
* `dbl_conv_reindex_two` (`BaxterRenewal.lean`) — for two distinct factors `q0a, q0b`,
  `∫ q0a(t)∫ q0b(s)ψ(r+t−s) = ∫_u [(∫_u^σ q0a·q0b(·−u))·ψ(r+u) + (∫_u^σ q0b·q0a(·−u))·ψ(r−u)]`.
  Both sides route through the *asymmetric* triangle-split double integral
  `∫ t ∫_{s<t} [q0a(t)q0b(s)ψ(r+t−s) + q0a(s)q0b(t)ψ(r+s−t)]` (the scalar's symmetrized `ψ(r±u)`
  splits because the two factors no longer commute across the diagonal). Same
  `intervalIntegral_triangle_swap_gen` + `integral_comp_sub_left` change of variable as the scalar;
  9 fine-grained integrability hypotheses. For `q0a = q0b` it collapses to `dbl_conv_reindex`.
* `matDblConv_reindex` (`MixtureOzStar.lean`) — sums the two-function reindex over the intermediate
  species `k` (`intervalIntegral.integral_finsetSum` + `Finset.sum_mul` regroup), giving
  `∑ₖ (Qᵢₖ⋆Qⱼₖ)⋆ψ = ∫_u [matSelfConv Q σ u i j · ψ(r+u) + matSelfConv Q σ u j i · ψ(r−u)]`
  (the second kernel is the `i↔j` transpose). `matDblConv_reindex_fin_one` = the `n = 1` bridge.

**Integrability side-conditions DONE (2026-07-27, `OZFIX.20` discharge).** The matrix reindex is
stated with nine per-species integrability hypotheses; `MixtureOzStarIntegrable.lean` discharges all
nine from the **natural regularity** of the Baxter data (factors `Q i j` continuous, `psi` measurable
+ `|psi|` `uIcc`-bounded), exactly the regularity the scalar `ozstar_h…` (`BaxterOzStar.lean`) exploit
for `q0_poly`/`baxterPsi`. Generic engine:
* `bddOn_uIcc_of_continuous`, `psiComp_bddOn` — compact-interval bounds from continuity (via
  `isCompact_uIcc.exists_isMaxOn`);
* `swap_indicator_integrable` — the shared Fubini `(Ioi ·).indicator` engine, factoring the three
  product-measure side-conditions (`integrable_prod_restrict_of_measurable_bddOn` + indicator
  boundedness); `swapPM_integrable` / `swapA_integrable` specialise it to the `ga(t)·gb(t−u)·ψ(w u)`
  and `ga(t)·gb(s)·ψ(r+t−s)` shapes;
* `constMul_psi_intervalIntegrable` — the slice side-conditions;
* `paramLo_/paramHi_/paramKernel_mul_intervalIntegrable` — the parametric inner-integral
  side-conditions (`measurable_intervalIntegral_param` + `norm_integral_le_of_norm_le_const`).
`matDblConv_reindex_of_regular` assembles them: the matrix reindex conditional only on
`(∀ a b, Continuous (Q a b))`, `Measurable psi`, and `psi`'s `uIcc`-boundedness — the matrix analog of
the way `baxterPsi_ozstar` is unconditional.

**Matrix OZ★ ASSEMBLED (2026-07-28, `OZFIX.15/19/20` combined) — axiom-clean, no decay axiom.**
`matOzStar_of_shellClaims` (`MixtureOzStar.lean`) derives the matrix real-space OZ identity
`MatOZStar Ψ Φ ρ` from four inputs, exactly mirroring the scalar `baxterPsi_eq_phi_add_rho_conv`:
* `hfact` — `MatBaxterFactorization` (matrix KDEF `ρKᵢₖ = Qᵢₖ − matSelfConv(i,k)`);
* `hbridge` — `matRadialConv_eq_matShellConv` (matrix `OZFIX.19` shell-conv bridge);
* `hQint`/`hSint` — shell integrability (dischargeable via `MixtureOzStarIntegrable.lean`);
* `hclaimA` — the **matrix renewal identity in shell form** (`OZFIX.15` analog of
  `baxter_psi_conv_eq_phi`): `Ψᵢⱼ(r) = r·Φᵢⱼ(r) + (shell-Q − self-conv-shell)`.
The load-bearing algebra is `matShellConv_kdef_split` (KDEF substituted a.e. on the open core splits
`ρ·matShellConv` into shell-`Q` minus self-conv-shell). `claimA` supplies `Ψ − r·Φ`, and
`ρ·matShellConv` (bridge + KDEF split) supplies the *same* shell expression ⇒ `MatOZStar`.
Validated at `N = 1` by the pre-existing `matOZStar_fin_one_of_scalar` (= unconditional scalar
`baxterPsi_ozstar`). **The assembly needed NO matrix decay axiom** — the hard content lives entirely
in the three `constructed-solution` Prop inputs (`hfact`/`hbridge`/`hclaimA`).

**Assembly integrability plumbing FINISHED (2026-07-30, `MixtureOzStarIntegrable.lean`, axiom-clean).**
`matOzStar_of_shellClaims` still carried its two shell-integrability side-conditions (`hQint`, the
linear `Q`-shell; `hSint`, the self-conv shell) as *bare* hypotheses — the last un-plumbed integral in
the matrix assembly, the analog of the reindex's nine that `matDblConv_reindex_of_regular` already
discharged. Now closed by the capstone **`matOzStar_of_regular`**, which discharges both from the same
natural regularity (`Q` continuous, `oddExt (Psi·/·)` measurable + `uIcc`-bounded per entry) and keeps
only the genuine constructed-solution inputs `hfact`/`hbridge`/`hclaimA` — so the matrix assembly now
needs *no* integrability hypotheses, exactly mirroring the unconditional scalar
`baxterPsi_eq_phi_add_rho_conv`. Two reused engine lemmas: `shellQ_intervalIntegrable`
(`g·(psi(r−u)+psi(r+u))` = two `mulCont_psi_intervalIntegrable`, the `c=1` slice of
`constMul_psi_intervalIntegrable`) and `shellS_intervalIntegrable` (expand `matSelfConv` into the
species sum of `paramKernel_mul_intervalIntegrable` shapes, close by `IntervalIntegrable.sum` +
`Finset.sum_mul`). `#print axioms` on all four = standard three only, **no new axiom, ledger unchanged**.

**`Ψouter` CONSTRUCTED — no longer a parameter (2026-07-31, axiom-clean).**  The renewal scaffolding
took `Ψouter` (the coupled matrix Volterra outer solution) as a *parameter*; the note "constructing it
is the remaining analytic core" is now discharged.  Built by lifting the proved scalar global-gluing
chain (`volterraSol`→`volterraGlobal`→`volterraGlobal_spec`, `BaxterRenewal.lean`) to **any complete
normed ring** in `Analysis/VolterraBanach.lean` — `volterraSolE`/`volterraSolE_spec`/`_unique`,
`volterraSolE_compat` (overlap agreement from uniqueness), `volterraGlobalE` (`if a≤r then sol(b:=r) at
r else 0`), `volterraGlobalE_eq_sol`/`_spec`/`_continuousOn`/`_continuousOn_Ici` (half-line continuity by
`mono_of_mem_nhdsWithin` gluing).  Instantiated at `E = Matrix (Fin N) (Fin N) ℝ` (`linftyOp` ring) in
`MixtureOzStar.lean`: `matBaxterPsiOuterFun` = `volterraGlobalE` precomposed with `max σ ·` (globally
continuous, agrees with the solution on `[σ,∞)`; `matBaxterPsiOuterFun_continuous` via
`ContinuousOn.comp_continuous`, `_renewal` via `volterraGlobalE_spec` + `integral_congr`).  Capstone
**`matBaxterPsiOuter_matRenewalEq`**: for *any* continuous matrix Baxter data `Q, F`, the entries of
`matBaxterPsiOuterFun` satisfy the entrywise `∑ₖ` `MatRenewalEq` (via `matRenewalEq_of_matrixProduct`).
`#print axioms` = standard three, **no new axiom, ledger unchanged**.  **Still open for the full
`hclaimA`:** (i) instantiate `Q, F` with the concrete real-space matrix Baxter kernel + forcing (the
momentum→real-space `Q0_mat_c` data), and (ii) the **matrix seed identity** — the analog of
`baxter_psi_conv_eq_phi` converting `MatRenewalEq` (the `∫_σ^r` renewal) to the OZ★ shell form (the
`oddExt`/`∫_0^σ` shell).  The existence/renewal half of the construction is now done; the seed identity
is the remaining research-scale piece.

**Matrix seed — claim (A) + outer half BUILT (2026-07-31, `MixtureBaxterSeed.lean`, axiom-clean).**
The scalar seed `baxter_psi_conv_eq_phi` (`Ψ⋆Q₊⋆Q₋ = r·c_HS`) rests on `baxter_u_outer` (claim (A):
`u := Ψ⋆Q₊ ≡ 0` on `[σ,∞)`) + `baxter_core_seed` (the Wertheim–Thiele affine algebra on the core).
Built for the matrix:
* `intervalConv_sub_open` — the reusable analytic heart: `∫_0^σ q(t)ψ(r−t) = ∫_0^r q(r−s)ψ(s)` for any
  continuous `q` supported in `[0,σ]` (substitute `s=r−t`, then the `[0,r−σ]` tail vanishes since
  `q(r−s)=0` there).  Carries NO core/forcing content — the general form of the scalar reduction.
* `matBaxterU` (`uᵢⱼ = Ψᵢⱼ − ∑ₖ ∫_0^σ Qᵢₖ·Ψₖⱼ(r−·)`) + **`matBaxterU_outer`** — matrix claim (A):
  the coupled `MatRenewalEq` (with forcing `Fᵢⱼ(r)=∑ₖ∫_0^σ Qᵢₖ(r−s)·Ψcoreₖⱼ(s)`) is equivalent on
  `[σ,∞)` to `Ψᵢⱼ(r)=∑ₖ∫_0^σ Qᵢₖ(t)·Ψₖⱼ(r−t)`.  Proof = `intervalConv_sub_open` **summed over species
  `k`** (`Finset.sum_congr`), `[0,r]` split at `σ` (`integral_add_adjacent_intervals`), the `[0,σ]`
  piece matched to the forcing via core values a.e. (jump at `σ` null).  Integrability per `k` from
  core-continuous on `[0,σ]` (a.e.) + outer-`ContinuousOn` on `[σ,r]` — the glued-solution regularity.
* `matBaxterUQm` (second convolution `⋆Q₋`) + **`matBaxterUQm_zero_of_uOuter`** — the **outer half of
  the seed**: `Ψ⋆Q₊⋆Q₋ ≡ 0` on `[σ,∞)` (both `uᵢⱼ(r)` and `uₖⱼ(r+t)` vanish; matches `r·c_HS(r)=0`
  since `c_HS` supported in `[0,σ]`), reduced abstractly to the claim-(A) conclusion `hUouter`.
`#print axioms` all three = std 3.  **Still open (the CORE half, `0<r<σ`):** `matBaxterU_core` (affine
`u = r·(M₀−1)−M₁`) + matrix `baxter_core_seed` (the WT/PY moment algebra tying it to `c_HS`) — both
need the concrete real-space matrix moments/DCF, i.e. piece (i).  Claim (A) is the renewal-side half
and is now unconditional (given the glued-solution regularity); the core half is the concrete-data half.

**⚠️ RETRACTED (2026-07-31) — the "piece (i)" real-space kernel below was a DUPLICATE, file removed.**
The real-space matrix Baxter factor **already exists**: `WHSupports.q0MixEntry` ("[LN] Eq. 56/10") =
`X.Q0·(r−Rᵢⱼ) + X.Qpp·(r−Rᵢⱼ)²/2` windowed on `Icc λᵢⱼ Rᵢⱼ` (`Rᵢⱼ = σ̄ᵢⱼ`), from the `Mix` struct —
**with the causal lower-cut** that my `q0MatReal` lacked (mine was continuous / no cut / `ρ_geo`-bundled ⇒
wrong for unlike pairs: misses the `λᵢⱼ` jump and the separate `λᵢⱼ`-delta).  The momentum factorization
is also long-standing (`Cmix0 = I − Q̂₀(k)Q̂₀ᵀ(−k)`, MRS.6 `Cmix0_factorization`; `Q0_mat_c`).
`MixtureBaxterRealSpace.lean` (q0MatReal + moments + transform) deleted; **`matBaxterU_core` kept** (it is
abstract / Q-agnostic).  The paragraphs below are the retracted account; see the gap map after them.

**Claim (B) `matBaxterU_core` BUILT (2026-07-31, `MixtureBaxterSeed.lean`, axiom-clean).**  Matrix analog of
scalar `baxter_u_core`: for `Ψ` with core value `Ψₖⱼ(v)=−v` on `(−σ,σ)`, on `0<r<σ` the whole sample range
`r−t` stays in the core, so `matBaxterU Psi Q σ i j r = r·(∑ₖ M₀ᵢₖ − 1) − ∑ₖ M₁ᵢₖ` with `M₀ᵢₖ=∫_0^σ Qᵢₖ`,
`M₁ᵢₖ=∫_0^σ t·Qᵢₖ` (the scalar computation summed over `k`).  **Stated with integrability (`hQ0`/`hQ1`),
not continuity**, so it accepts the discontinuous physical `q0MixEntry`.  The `−1` is the single
`Ψᵢⱼ(r)=−r` term (Baxter identity part), not summed.

**GAP MAP toward concrete `hclaimA` (2026-07-31).**  (1) **Matrix Wertheim core seed** `matBaxterUQm_ij(r)
= r·c_HS_ij(r)` on the core — needs a real-space matrix PY DCF `c_HS_ij(r)` and the WT/PY algebra (matrix
analog of `baxter_core_seed`).  **The crux.**  **⚠ Verified 2026-07-31: the real-space matrix PY DCF closed
form exists NOWHERE in the project** (not a forgotten formula).  The matrix PY DCF is present only in
**momentum** space (`Cmix0 = I − Q̂₀Q̂₀ᵀ`, MRS.6); the **real-space** HS DCF the project uses is the **FMT**
form (`cHS_FMT`/`CHSKink`; Python `get_HS_FMT` in every route).  A real-space PY closed form = the inverse
transform of `Cmix0` = the **Lebowitz/Wertheim** result, which `MixtureRealSpace.lean` explicitly **defers as
MRS.8** ("`Ĉ₀` equals the physical HS DCF transform").  So gap #1's two halves collapse: defining `c_HS_ij`
real-space **is** the Wertheim derivation, not a transcription — the project deliberately sidesteps it (FMT
real-space + `Cmix0` momentum).  **✅ ADDRESSED 2026-07-31 (`YukawaDCF/MixtureHSDCF.lean`, axiom-clean):
zeroth-order HS DCF built REUSING the existing `q0MixEntry`/`pMixEntry`/`⋆` machinery.**  Key structural
fact: `Cmix0 = I − Q̂₀(k)Q̂₀ᵀ(−k)` is **forward × reflected**, so `qpConv = qFwd ⋆ pMixEntry` (`qFwd` = the
forward `2π√ρ·q0MixEntry`), support `[−Rᵢⱼ,Rᵢⱼ]` with `σₙ` cancelling (`λᵢₙ−Rⱼₙ=−Rᵢⱼ`, exactly like
`bConvP`; both-reflected `P⋆P` would keep `σₙ`).  `cHSmixRaw_ij = qFwd_ij + pMixEntry_ji − ∑ₗ qpConv_ilj`
= the real-space non-delta part of `[Cmix0]_ij` (verified by the `Cmix0` expansion), supported on
`[−Rᵢⱼ,Rᵢⱼ]`.  Remaining: the inverse-transform theorem `cHSmixRaw = [Cmix0]_ij` (parallel to `(★)`), the
`2π√ρ·t` normalization + odd part, then `matBaxterUQm = r·c_HS`.
**✅ `cHSodd` done + MML.8 trace (2026-07-31).**  The normalization/odd-part (#2) was **not a theorem but a
def-pattern**: the first-order DCF is *defined* as the odd part `dcfOdd = fun x => Wmix x − Wmix (−x)`
(`= 2π√ρ·r·c^(1)`); mirrored as `cHSodd = fun x => cHSmixRaw x − cHSmixRaw (−x)` (`= 2π√ρ·r·c^HS`, since
`r·c` is odd), with `cHSodd_odd` + `cHSodd_support_subset [−Rᵢⱼ,Rᵢⱼ]`.  **Trace conclusion — the c_HS/seed
line is on the critical path, not redundant:** `Ĥ₁ = S₀Ĉ₁S₀`, `S₀ = I+Ĥ₀`, dressing (done) ⇒
`h₁ = c₁ + h₀⋆c₁ + c₁⋆h₀ + h₀⋆c₁⋆h₀`, and since `Ĉ₁` is HS-pole-free **every HS pole of `h₁` is in the
three `h₀`-dressed terms** ⇒ MML.8's residual is `h₀` (the zeroth-order HS RDF) = the OZ★ solution
`matBaxterPsi`.  The momentum route to `h₀` (`(I−Cmix0)⁻¹−I`) is the *circular* ML-collapse; the chosen
non-circular route is `matOzStar_unique` (uniqueness, done, **abstract `Phi`**) + a **concrete
`matBaxterPsi` existence** (= `hclaimA`, needs concrete `Phi = c_HS`).  So the single missing MML.8 input
is `h₀ = matBaxterPsi` as a concrete `MatOZStar` solution — `c₁`/dressing/uniqueness are all done.
(2) **Matrix KDEF `hfact`** `ρK=Q−matSelfConv(Q)` for the concrete `q0MixEntry` — only N=1
(`matBaxterFactorization_fin_one_of_scalar`); needs the matrix real-space self-convolution factorization.
(3) **The `λᵢⱼ` jump/delta** — the physical factor is `q0MixEntry`(quadratic) + a `λᵢⱼ`-delta + `δᵢⱼ·δ(r)`;
the seed treats `Q` as the quadratic function only, so the whole chain is rigorous **only for equal
diameters** (like pairs, `λ=0`: continuous, delta-free, common-`σ` core holds).  Unequal diameters need the
delta incorporated ("drop it ⇒ wrong identity").  (4) **Wiring** `Q:=q0MixEntry`, `F:=core convolution`,
discharge (A)/(B) hyps, combine (A)+(B)+core-seed into the full seed, feed `matOzStar_of_regular`.  Deep
gaps = (1) + (3).

<details><summary>Retracted account (q0MatReal — do not build on this)</summary>

**Piece (i) — real-space matrix Baxter kernel BUILT (2026-07-31, `MixtureBaxterRealSpace.lean`,
axiom-clean).**  The momentum entry `q0_entry_c(s) = δᵢⱼ − ρ_geo·e^{−λᵢⱼs}·(Q'·φ̂₁(s,σᵢ) + Q''·φ̂₂(s,σᵢ))`
(`λᵢⱼ=(σⱼ−σᵢ)/2`; `φ̂₁,φ̂₂` = Laplace transforms of `phi1_real`/`phi2_real`) inverse-transforms to a
δ-at-origin (the `δᵢⱼ` identity part) plus the **function part**
`q0MatReal(r) = ρ_geo·(Q'·phi1_real(σᵢ,r−λᵢⱼ) + Q''·phi2_real(σᵢ,r−λᵢⱼ))` — the single-component
polynomial shifted by `λᵢⱼ` with the multicomponent PY coefficients `Q0phys`/`Qppphys`/`rhoGeoPhys`
(`MatrixQ0.lean`).  Built + proved:
* `q0MatReal` (def) + `q0MatReal_continuous` (`hQcont`) + `q0MatReal_support` (vanishes for
  `r ≥ σ̄ᵢⱼ=(σᵢ+σⱼ)/2`; `hQsupp` for the seed, with a common bound `σ_max ≥ σ̄ᵢⱼ` at the use site).
* `shift_laplace` (reusable: substituting `u=r−λ` factors `e^{−sλ}`, no continuity needed) +
  **`q0MatReal_laplace`** — the **inverse-transform certificate**: `∫_{λ}^{σ̄} q0MatReal·e^{−sr} =
  ρ_geo·e^{−sλ}·(Q'·φ̂₁ + Q''·φ̂₂)` (via `shift_laplace` + scalar `phi1_real_laplace`/`phi2_real_laplace`
  + interval-integral linearity), so `q̂₀ᵢⱼ = δᵢⱼ − (this)`.  This is exactly the `q0_entry_c` bracket ⇒
  `q0MatReal` IS the regular part of `Q0_mat_c`'s inverse transform.
`#print axioms` all three = std 3.  **Still open in piece (i):** the moments `M₀ᵢⱼ`/`M₁ᵢⱼ` + the matrix
`baxter_core_seed` (core WT/PY algebra), the forcing `Fmat`, and wiring `q0MatReal` into `matBaxterU_outer`
(feed `Q := q0MatReal`, discharge `hQcont`/`hQsupp`).  The λᵢⱼ<0 (σⱼ<σᵢ) causality subtlety is invisible
to the seed's `∫_0^σ` convolutions (only `r ≥ 0` sampled) but would matter for a full two-sided transform.

**Matrix moments `M₀ᵢⱼ`/`M₁ᵢⱼ` BUILT (2026-07-31, `MixtureBaxterRealSpace.lean`, axiom-clean).**  Checked
first: **NOT in the library** — the matrix HS DCF exists only in *White-Bear FMT* form (`CHSKink`/
`CHSFlatInner`), the MRS `star_*` lemmas are the *first-order Yukawa* momentum-space `(★)`, and the
zeroth-order matrix Baxter–Wertheim real-space factorization is proved only at N=1
(`matBaxterFactorization_fin_one_of_scalar`).  Built the moments: the four convention-independent
`phi`-basis atoms (`phi1_real_int`=`∫_0^σ phi1=−σ²/2`, `phi2_real_int`=σ³/6, `phi1_real_mom1`=`∫u·phi1=
−σ³/6`, `phi2_real_mom1`=σ⁴/24; each one FTC via `integral_eq_sub_of_hasDerivAt` + explicit
antiderivative) and the matrix moments **`matBaxterM0`/`matBaxterM1`** (defs + `_eq` proofs) — the
zeroth/first moments of `q0MatReal` over its physical support `[λᵢⱼ,σ̄ᵢⱼ]`: `M₀=ρ_geo(Q'(−σᵢ²/2)+Q''σᵢ³/6)`
(shift-invariant), `M₁=ρ_geo[(Q'(−σᵢ³/6)+Q''σᵢ⁴/24)+λᵢⱼ·(Q'(−σᵢ²/2)+Q''σᵢ³/6)]` (the `λᵢⱼ·M₀` weight
correction).  Proved by direct polynomial FTC on `[λ,σ̄]` (`integral_congr` to the shifted polynomial +
one antiderivative each; the `integral_add`/`const_mul` linearity route was too fragile — it elaborates
the integrand as a Pi-product `f·g` that the `rw` pattern misses).  `#print axioms` all = std 3.
**Still open in the core-seed:** the matrix `baxter_core_seed` (the WT/PY identity tying the matrix DCF
`c_HS` to the `q0MatReal` self-convolution), then `matBaxterU_core` (affine `u=r(M₀−1)−M₁` on the core,
consuming `M₀`/`M₁`), and the matrix KDEF `hfact` — plus the causal-kernel convention decision for λᵢⱼ<0.

</details>

**Structural finding (general-`N`).** The self-convolution is *not* symmetric:
`matSelfConv(i,k) ≠ matSelfConv(k,i)`, and `matDblConv_reindex` outputs the asymmetric pairing
`matSelfConv(i,k)·ψ(r+u) + matSelfConv(k,i)·ψ(r−u)`, whereas the symmetric `matShellConv` weights
both shells by `Kᵢₖ`. The two align only at `N=1` / symmetric `Q`. The assembly sidesteps this by
taking `claimA` **directly in shell form** (which the renewal construction provides), so the reindex
is not needed to close `MatOZStar`; the asymmetry is absorbed into the renewal identity `claimA`.

**Matrix pole-freeness needs NO new axiom (2026-07-28, `OZFIX.17` matrix).** The scalar
`baxter_no_open_lhp_pole_core` retirement feeds the *general* argument-principle axiom
`zeroFree_lowerHalfPlane_of_homotopy` (`ZeroCountHomotopy.lean`), which is stated for an **arbitrary**
continuous family of entire functions `H : ℝ → ℂ → ℂ`. So the matrix `det Q̂ ≠ 0` on the open LHP is
that **same** axiom at `H t z = (M t z).det`. `MatrixDetPoleFree.lean`:
* `differentiable_matrix_det` / `continuousOn_matrix_det` — entrywise regularity ⇒ `det` regularity
  (Leibniz expansion `det_apply'` is a finite sum of products of entries; stated entrywise so **no**
  matrix normed-space instance is needed);
* `matDet_zeroFree_lowerHalfPlane_of_homotopy` — the matrix pole-freeness reduction, depending only on
  `zeroFree_lowerHalfPlane_of_homotopy` (verified via `#print axioms`) — **no new axiom**.

**`hbound` escape mechanism DONE (2026-07-28, `MixtureDetEscape.lean`) — no new axiom.**  Under the
Baxter convention the open lower half `k`-plane is the **right** half `s`-plane, so `hbound` is
`det Q̂₀(s) ≠ 0` for `Re s ≥ 0`, `‖s‖ ≥ R`.  The **escape mechanism** is proved via the MML monomial
bridge `s⁶·detF = Mc + M₀e^{−sσ₀} + M₁e^{−sσ₁} + M₀₁e^{−s(σ₀+σ₁)}` (`detC_monomial_eq`):
* `exp_neg_mul_norm_le_one` — `Re s ≥ 0 ⇒ ‖e^{−sσ}‖ ≤ 1` (the exponentials are contractions in the
  right half-plane, hence subdominant);
* `Wfun_ne_zero_of_dominant` / `detF_ne_zero_of_dominant` — if the degree-6 leading `Mc` outweighs
  `M₀+M₁+M₀₁`, then `W ≠ 0`, hence `detF ≠ 0`.  Matrix analog of the scalar `exists_uniform_escape_radius`.
**`hbound` FULLY CLOSED (2026-07-28, `exists_escape_radius`) — axiom-clean, no new axiom.**  The
large-`‖s‖` polynomial asymptotics are discharged by evaluating the existing `MixtureChordFamily.lean`
bounds at `M := ‖s‖` (all `‖·‖ ≤ … · M^k` become `… · ‖s‖^k`): `McNum_sub_norm_le` gives
`‖Mc‖ ≥ ‖s‖⁶ − K_Mc‖s‖⁵` (reverse triangle), and `M0Num_norm_le`/`M1Num_norm_le`/`M01Num_norm_le`
give `‖M₀‖+‖M₁‖+‖M₀₁‖ ≤ (K₀+μ+K₁+K₀₁)‖s‖⁴`.  So for `‖s‖ ≥ R := max(1, K_Mc+K₀+μ+K₁+K₀₁+1)` the
dominance `‖M₀‖+‖M₁‖+‖M₀₁‖ < ‖Mc‖` holds (`nlinarith`) and `detF_ne_zero_of_dominant` gives
`detF(s) ≠ 0`.  `exists_escape_radius : ∃ R > 0, ∀ s, Re s ≥ 0 → R ≤ ‖s‖ → detF s ≠ 0` — the exact
`hbound` input, `#print axioms` = standard three.  (Nonnegativity of the `K`-constants and `μ` from
the existing `KMc_nonneg`/`K0_nonneg`/`K1_nonneg`/`K01_nonneg` + new `mu_nonneg`.)

**Density-homotopy scaffold BUILT (2026-07-28, `MixtureDetHomotopy.lean`) — axiom-clean.**  The
`s=0` pole is handled by running the homotopy on the **entire** monomial form `W(s) = s⁶·detF(s)`
(`detC_monomial_eq`; `W = 0 ⇔ detF = 0` for `s ≠ 0`) rather than the meromorphic `detF`, and applying
the **scalar** `zeroFree_lowerHalfPlane_of_homotopy` at `H t z = W(Pscale t P, I·z)` (`detF` is
scalar-valued, so no matrix-`det` machinery is needed).  Convention `s = I·z` gives `Re s = −Im z`, so
`Im z < 0` (open lower half `z`-plane) is `Re s > 0`.  Ingredients (all axiom-clean):
* `Pscale t P` = coupling homotopy `rr ↦ t·rr` (`Pscale 1 P = P`, `Pscale 0 P` = zero coupling);
  `Pscale_Phys` (positivity for `t > 0`).
* `Wfun_Pscale_zero` — dilute base `W(P₀, s) = s⁶`; `Wfun_dilute_ne_zero` = **`hbase`**
  (`W(P₀, I·z) = −z⁶ ≠ 0` for `Im z < 0`).
* `Wfun_ne_zero_of_norm_ge` — **`hbound`** in `z`-form, from `exists_escape_radius` through `s = I·z`.
* `Wfun_comp_I_differentiable` — **`hholo`** (via `Wfun_hasDerivAt`); `Wfun_Pscale_comp_I_continuous`
  — **`hcont`** (via `fun_prop`).

**Homotopy ASSEMBLED (2026-07-28, conditional) — no new axiom.**  `Wfun_zeroFree_of_hreal` /
`detF_zeroFree_of_hreal` wire the four geometric bricks (`hcont`/`hholo`/`hbound`/`hbase`) into the
scalar `zeroFree_lowerHalfPlane_of_homotopy` at `H t z = W(Pscale t P, I·z)`, concluding
`detF(I·z) ≠ 0` for `Im z < 0` — **conditional on** a uniform-in-`t` escape radius (`hRunif`) and
`hreal`.  `#print axioms` = standard three + the existing `zeroFree_lowerHalfPlane_of_homotopy`.

**Structural finding — the `Pscale` (linear-`rr`) family is the wrong homotopy for `hreal`.**  `hreal`
(`detF(Pscale t P, I·k) ≠ 0` for real `k`, all `t`) is the no-spinodal condition *along the path*.
`pyhs_mixture_no_spinodal` holds for any physical density (`etaMix < 1`), so it discharges `hreal`
along the **physical density path** (`ρ ↦ t·ρ`, `etaMix(t·ρ) = t·etaMix(ρ) < 1`) — but the `Pscale`
family scales only the coupling `rr` *linearly*, which does **not** correspond to a physical
`(σ, ρ')` point (the PY closure ties `rr = √(ρᵢρⱼ)`, `Qp`, `Qpp` together non-linearly), so
no-spinodal does not cover `Pscale t P` for `t ∈ (0,1)`.  Completing `hreal` therefore needs the
homotopy re-based on the physical density scaling `Pdens t` (deriving `rr/Qp/Qpp` from `(σ, t·ρ)` via
`rhoGeoPhys`/`Q0phys`/`Qppphys`); the four bricks' *structure* transfers (they are family-generic:
dilute base, escape radius, entire, continuous), only the concrete family changes.

**Physical density path BUILT (2026-07-28, `MixtureDetHomotopyPhys.lean`) — `hreal` (`k ≠ 0`) done, no
new axiom.**  `Pdens σ ρ t` = the `MixParams` at density `t·ρ` (`rhoGeoPhys(t·ρ)` scales linearly in
`t`, but `Q0phys`/`Qppphys` vary via the vacancy `1−η`, so unlike `Pscale` every point is a genuine
physical state).
* `detF_Pdens_eq` — the bridge `detF(Pdens σ ρ t) = det Q̂₀-phys(σ, t·ρ)` (both `det Q0_mat_c` with the
  same substituted PY coefficients; the only mismatch `![σ₀,σ₁]` vs `σ` closed by `fin_cases`).
  **Axiom-clean.**
* `etaMix_smul` — `η(t·ρ) = t·η(ρ)`, so `t ≤ 1 ⇒ η(t·ρ) = t·η(ρ) ≤ η(ρ) < 1`.
* `detF_Pdens_ne_zero` — **`hreal` for `k ≠ 0`**: `detF(Pdens σ ρ t, I·k) ≠ 0` for real `k ≠ 0`,
  `t ∈ (0,1]`, directly from the existing `pyhs_mixture_no_spinodal` at density `t·ρ`.  (HS has no
  spinodal at any density ⇒ the physical path is singularity-free.)  Depends only on the existing
  physics axiom — no new axiom.

**Remaining subtlety found — run the homotopy on the ENTIRE `detF`, not `W`.**  `W(P₀, 0) = 0` (the
dilute base `W = z⁶` has a zero at the origin), which breaks `hreal` at `z = 0`; the scalar track
avoided this by using `1−Q̂` (entire, nonzero at origin).  The matrix analog is `detF` itself, which is
**entire** — each `q0_entry_c` has a *removable* singularity at `s = 0` (`q0_entry_c_differentiableAt`
only records `s ≠ 0`).  So completing the assembly needs: (i) `detF` entire; (ii) the `z = 0` value
`detF(Pdens t, 0) = det Q̂₀(0) ≠ 0`; (iii) a uniform-in-`t` escape radius.  All three are transcription,
**not** new axioms.

**`detF` entire DONE (2026-07-28, `MixtureDetEntire.lean`) — axiom-clean.**  The Lean `detF` is
`0/0`-junk at `s = 0` but analytic away from `0` (`Q0_det_c_differentiableAt`) with a finite removable
limit (`detC_tendsto`, from the already-proved `q0_entry_c_tendsto`: `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6`).
* `detF_update_differentiable` — `Function.update detF 0 c` is **entire** for the limit `c`, by
  Riemann's removable-singularity theorem `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  (differentiable on the punctured `𝓝` since `update = detF` off `0`; `ContinuousAt 0` via
  `nhdsNE_sup_pure` + the limit).
* `detF_tendsto` / `detF_ext_differentiable` — package the limit with the entire extension.
This is the entire object the homotopy runs on (`hholo`), the matrix analog of the scalar `1−Q̂`.
**Dilute base of the extension DONE (2026-07-28) — `hbase` for `detF_ext`.**  `Pdens_zero_rr`
(`rr(Pdens σ ρ 0) = 0`, since `rhoGeoPhys(0·ρ) = √0 = 0`) + `Q0_mat_c_rho_geo_zero`
(`Q0_mat_c` at zero coupling `= I`) ⇒ `detF_Pdens_zero` (`detF(Pdens σ ρ 0) ≡ 1`, no `0/0` issue) and
`detF_ext_Pdens_zero` (`update (detF(Pdens 0)) 0 1 ≡ 1`, nonzero everywhere incl. `z = 0`).
Axiom-clean.

**Precise remaining accounting for the concrete pole-freeness theorem** (all no-new-axiom):
* **`hholo`** = `detF_ext_differentiable` ✓; **`hbase`** = `detF_ext_Pdens_zero` ✓;
  **`hreal` (`k ≠ 0`)** = `detF_Pdens_ne_zero` ✓ (existing no-spinodal); **`hbound`** = lift
  `exists_escape_radius` to `detF_ext` in `z`-form ✓ (mechanical).
* **`hreal` at `z = 0` — the origin value `detF_ext(Pdens t, 0) = c_t ≠ 0`** — is the genuine remaining
  physical sub-fact, characterised precisely (2026-07-28):
  - `c_t` = `det` of the removable **moment matrix** `Mᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ(Qpᵢⱼ(−σᵢ²/2) + Qppᵢⱼ(σᵢ³/6))`
    (the `q0_entry_c_tendsto` values) — **not** the Lean `0/0`-junk value `1`; physically it is the
    `k = 0` structure factor = **compressibility**.
  - **`pyhs_mixture_no_spinodal` does not cover it** (it is stated with `k ≠ 0`, precisely to dodge the
    `s = 0` removable value); `Q0_moment_det_pos` gives `det > 0` for real `z > 0`, hence only
    `c_t = lim_{z→0⁺} ≥ 0`, **not** strict.
  - **`c_t ≠ 0` is NOT derivable from the axis non-vanishing** (`detF ≠ 0` on the real-positive axis
    via `Q0_mat_phys_isUnit_det`, and on the imaginary axis via no-spinodal): if `c_t = 0` then the
    entire `detF_ext ~ a·zⁿ` near `0`, which is consistent with non-vanishing on **both** axes
    (`a·zⁿ > 0` for `z > 0`; `a·iⁿyⁿ ≠ 0`) — no contradiction.  So `c_t > 0` is genuine `k = 0`
    compressibility content.
  - **✅ CLOSED (2026-07-28, `Q0MomentGeOne.lean` + `MixtureDetOrigin.lean`) — AXIOM-CLEAN, no physics
    axiom.**  Route 1 (explicit moment determinant): `moment_key` gives not just `det > 0` but
    `ad − bc ≥ a + d`, hence `det = 1 − (a+d) + (ad−bc) ≥ 1` (`Q0_moment_det_ge_one`,
    `Q0_mat_phys_det_ge_one`) — a **strict-with-margin** bound.  It survives the `z → 0` limit: at real
    `z > 0`, `detF(Pdens σ ρ t, z) = det Q0_mat_phys(z, σ, t·ρ) ≥ 1` (`detF_Pdens_ofReal` +
    `Q0_mat_phys_det_ge_one`), so `Re(c) = lim_{z→0⁺} det ≥ 1 > 0` (`ge_of_tendsto`), hence `c ≠ 0`
    (`detF_Pdens_origin_ne_zero`; `hreal` at `z=0` = `detF_ext_Pdens_origin_ne_zero`).  `#print axioms`
    = standard three — the `k = 0` compressibility positivity is **proved**, not a companion axiom
    (`moment_key` is proved algebra; `pyhs_mixture_no_spinodal` is not even used).  Bonus: real
    removable values `p1 → −σ²/2`, `p2 → σ³/6` (`p1_tendsto_zero_nhds`, `p2_tendsto_zero_nhds`).
* **`hcont`** (joint continuity of the family extension) and **uniform-`t` escape radius**
  (`K`-constants `rr`-monotone) — mechanical.

**Concrete pole-freeness theorem ASSEMBLED (2026-07-28, `MixtureDetOrigin.lean`) — no new axiom.**
`mixtureDet_pole_free_of_regular` : for the physical mixture `(σ, ρ)`, `detF(Pdens σ ρ 1, I·z) ≠ 0`
throughout the open lower half `z`-plane — the LHP pole-freeness of `det Q̂₀`.  It runs the density
homotopy on the entire removable extension via `zeroFree_lowerHalfPlane_of_homotopy`, discharging
**every** pointwise input from the proved lemmas: `hholo` (`detF_update_differentiable`), `hbase`
(dilute `detF ≡ 1`), `hreal` for `k ≠ 0` (`Pdens_detF_imag_ne_zero`, no-spinodal) and `k = 0`
(`cf_ne_zero`, the axiom-clean compressibility), `hbound` (uniform escape).  `#print axioms` = the two
**existing** axioms only (`zeroFree_lowerHalfPlane_of_homotopy` + `pyhs_mixture_no_spinodal`) — no new
axiom.  Conditional only on the two **family-regularity** hypotheses `hcont` (joint continuity of the
`(t,z) ↦ detF_ext(Pdens t)(I·z)` family) and `hRunif` (uniform-in-`t` escape radius) — both purely
mechanical (continuity of a parametrised analytic family; `K`-bound over the compact `[0,1]`), the
last remainder.

**Progress on the remainder (2026-07-28).**  `detF_ne_zero_of_Kbound` (`MixtureDetEscape.lean`) — the
**uniform escape mechanism** for `hRunif`: from a common bound `K_Mc,K₀,μ,K₁,K₀₁ ≤ B`, `detF(P,s) ≠ 0`
for `Re s ≥ 0`, `‖s‖ ≥ max(1,5B+1)` (axiom-clean).  Building blocks for the uniform `B`:
`vacMix`/`xi2` continuous in `t` on `[0,1]` (`fun_prop`), `vac > 0` there (`etaMix(t·ρ)=t·etaMix(ρ)<1`).
**`hRunif` DONE (2026-07-29, `MixtureDetUniform.lean`) — axiom-clean.**  `hRunif_Pdens` : a single
`R = max(1, 5B+1)` works for all `t ∈ [0,1]`.  The five `K`-constants of `Pdens t` are continuous in
`t` (`Ksum_cont` — `vacMix`/`xi2` continuous via `fun_prop`, `vac(t)=1−t·η(ρ)>0`, so `Q0phys`/`Qppphys`
= `…/vac` continuous by `ContinuousOn.div`, then `cB`/`K`s are polynomials in the fields), hence their
sum is bounded on the compact `[0,1]` (`isCompact_Icc.exists_bound_of_continuousOn`); `Pdens_Phys`
(physicality for `t > 0`, from `Q0phys_pos`/`Qppphys_pos`/`rhoGeoPhys_pos`) + `detF_ne_zero_of_Kbound`
close it (`t = 0` is dilute `detF ≡ 1`).

**`hcont` DONE ⇒ UNCONDITIONAL theorem (2026-07-29, `MixtureDetHcont.lean`).**  The `0/0`-junk of
`detF` at `s = 0` comes only from `φ₁,φ₂ = num/sⁿ`, which depend on `s`/`σ` **not** on `t`.  Replacing
them with continuous removable extensions `psi1`,`psi2` (`psi{1,2}_continuous` via `phi{1,2}_tendsto` +
`nhdsNE_sup_pure`) gives the `ψ`-form det `detFpsi` — **manifestly jointly continuous**
(`detFpsi_continuous`; fields of `Pdens t` continuous in `t`, `ψ` continuous in `s`) and `= detF` away
from `0` (`detFpsi_eq_detF`).  Since `cf t = detFpsi(Pdens t) 0` (`cf_eq_detFpsi_zero`), the
update-based `detF_ext = detFpsi`, so `hcont` follows by `ContinuousOn.congr` (`hcont_Pdens`).  No
parametrised removable-singularity theorem was needed — the `t`-independence of `φ` sidesteps it.

**`mixtureDet_pole_free`** : `detF(Pdens σ ρ 1, I·z) ≠ 0` on the open lower half `z`-plane for every
physical `N=2` hard-sphere mixture — **fully unconditional**.  `hcont`/`hRunif`/`cf` all discharged;
`#print axioms` = the two **existing** axioms only (`zeroFree_lowerHalfPlane_of_homotopy` +
`pyhs_mixture_no_spinodal`).  The matrix `pole-in-LHP ⇔ decay` obstacle (`OZFIX.17`) is fully resolved
for `N=2` — no new axiom, everything else proved (including the axiom-clean `k=0` compressibility).

**Answer to "does the matrix track need a NEW math axiom?" — NO.**  Pole-freeness reuses the existing
`zeroFree_lowerHalfPlane_of_homotopy` (`matDet_zeroFree_lowerHalfPlane_of_homotopy`); `hreal` is the
existing `pyhs_mixture_no_spinodal`; `hbase` = `det Q̂₀(0)=1` (MML `Q0_mat_c_at_zero`); `hbound`'s
mechanism is now proved (this file). The matrix Baxter factorization is **explicit**
(`Q0_mat_phys_eq_one_sub_mul`, proved) — no abstract Wiener–Hopf existence gap. What remains
(`hfact`/`hbridge`/`hclaimA` for the concrete mixture, the poly asymptotics, the homotopy scaffold,
`s=0` pole) is **transcription work, not new axioms** — the matrix track can reach the scalar track's
standard modulo only the *existing* kept math axioms.

**Depends on.** Scalar `baxterPsi_ozstar`, `rho_baxterK_eq_q0_self_conv`, `baxterK`, `q0_poly`
(`BaxterOzStar.lean`/`BaxterRenewal.lean`); `radial3d_conv` (`RadialLaplace.lean`).

**Lean.** `HSMixture/MixtureOzStar.lean` (ns `FMSA.MixtureOzStar`): `matRadialConv`,
`matRadialConv_apply`, `matRadialConv_fin_one`, `MatOZStar`, `matOZStar_entry`,
`matOZStar_fin_one_of_scalar`; `matSelfConv`, `matSelfConv_apply`, `matSelfConv_fin_one`,
`MatBaxterFactorization`, `matBaxterFactorization_fin_one_of_scalar`; `matShellConv`,
`matShellConv_apply`, `matRadialConv_eq_matShellConv`, `matShellBridge_fin_one_of_scalar`,
`matRadialConv_eq_matShellConv_of_shellKernel`; `matBaxterPsi`, `matBaxterPsi_core`/`_outer`/`_reflect`,
`MatRenewalEq`, `matBaxterPsi_fin_one_of_scalar`, `matRenewalEq_fin_one_of_scalar`;
`matShellConv_kdef_split`, `matOzStar_of_shellClaims` — all axiom-clean.  `HSMixture/MixtureOzStarIntegrable.lean`
discharges every integral side-condition of the assembly: the reindex's nine
(`matDblConv_reindex_of_regular`) and the assembly's two shell conditions
(`mulCont_psi_intervalIntegrable`, `shellQ_intervalIntegrable`, `shellS_intervalIntegrable`,
capstone `matOzStar_of_regular`) — all axiom-clean.
`matVolterra_convolution_existsUnique`. Plus `HardSphere/ShellKernel.lean` (`shellKernel`,
`radial3d_conv_eq_shellKernel`, `shellKernel_c_HS`) and `Analysis/VolterraBanach.lean` (the Banach
`MA.10`: `volterraTE`, `volterra_iterate_boundE`, `volterra_existsUniqueE`,
`volterra_convolution_existsUniqueE`). Full build green.

**Status.** ◑ **STARTED (2026-07-24), axiom-clean foundation — four layers, `Ψouter` constructed.** (1) The OZ★ target
shape (`MatOZStar`, entrywise reduction to scalar `radial3d_conv`); (2) its real-space factorization
foundation (`MatBaxterFactorization`, `matSelfConv`); (3) the shell-conv = K-conv bridge
(`matRadialConv_eq_matShellConv`, general-`c` via `ShellKernel.lean`) connecting (1) to (2); (4) the
matrix `baxterPsi` construction shape + renewal equation (`matBaxterPsi`, `MatRenewalEq`). Each has an
`n = 1` bridge to a proved scalar theorem (`baxterPsi_ozstar`, `rho_baxterK_eq_q0_self_conv`,
`radial3d_conv_eq_baxterK_shell`, `baxterPsi_core`/`baxterPsiOuter_spec`). The
general-`N` analytic construction (matrix `baxterPsi`, `OZFIX.18` F-part + `OZFIX.20` reindex,
renewal + integrability, modulo the matrix decay axiom) is the remaining research-scale work — the
last unbuilt piece of MML.8. **The general-`c` shell identity (`radial3d_conv_eq_shellKernel`,
`ShellKernel.lean`) is now proved**, so the shell-bridge layer is complete for arbitrary mixture
entries, not just `c_HS`.  **UPDATE 2026-07-31 — the assembly integrability and the `Ψouter`
existence/renewal are now BUILT** (`matOzStar_of_regular`; `matBaxterPsiOuter_matRenewalEq` via the
Banach global Volterra chain `VolterraBanach.volterraGlobalE`), so what remains of MML.8's construction
narrows to: (a) the concrete real-space matrix Baxter data `Q, F` (momentum→real-space `Q0_mat_c`),
and (b) the **matrix seed identity** (analog of `baxter_psi_conv_eq_phi`, `MatRenewalEq` → OZ★ shell
form).  See the "`Ψouter` CONSTRUCTED" note above.

---

## Group MZERO — Mixture `det(Q̂₀)` Zero Family (HS-pole existence)

**Scope.** `det(Q̂₀(s))` has **infinitely many** complex zeros `s_k` (the "HS poles" whose
residues feed MML.4/MML.8's Mittag-Leffler series). **MZERO.1** is the foundational statement;
**MZERO.2–MZERO.11** decompose it across two independent routes (Banach contraction / Jensen
zero-counting), either of which alone closes MZERO.1. The route overview precedes the numbered
tasks below.

**✅ GROUP CLOSED — audited 2026-07-24, no open item.** The audit was mechanical rather than a
re-read of recorded statuses: every named deliverable of MZERO.1–MZERO.11 was `#print axioms`-checked
and returns the standard three only (`detC_zeros_infinite_unconditional`, `chordPoleFamily_detC_exists`,
`chord_zero_exists_of_bounds`, `chordPhi_fixedPt_iff`, `chordPhi_lipschitzOnWith`,
`mapsTo_closedBall_of_lipschitzOnWith_of_dist_le`, `Q0_det_c_zeros_infinite`,
`Q0_det_c_pole_family_growth`, `det_meromorphicOn`, `det_divisor_nonneg`, `detC_jensen_log_bound`,
`detBoundaryGrowth_of_linear`, `detC_boundaryGrowth_iff_infinite_zeros`,
`detC_zeros_infinite_of_boundaryGrowth`). ⚠ **Namespace note for future audits:** the MZERO.3/4/6
Banach machinery lives in `FMSA.BanachPoleFamily` and MZERO.10's growth predicate in
`FMSA.BoundaryGrowth` — **not** in `FMSA.MixtureHSPoles`, because the generic layer was migrated to
`Analysis/` (MRS.9b). Looking them up under the mixture namespace reports "unknown constant" and
looks like a missing proof.

#### Re-audit 2026-07-31 — the 07-24 audit still holds, plus three findings

**Re-measured, not re-read.** All 20 MZERO constants (the 14 above plus `Q0_det_c_tendsto_one`,
`Q0_det_c_not_identically_zero`, `Q0_det_c_differentiableAt`, `detC_boundaryGrowth_of_infinite_zeros`,
`infinite_zeros_of_growth`, `detC_zeros_infinite_of_growth`) `#print axioms` = **standard three**.
Nothing moved under MZERO's feet in the `be70ac4` "General N" rewrite or the MRS.9d file shuffle.

**1. Split the group's status honestly: the machinery is load-bearing, the headline is
consumer-less.** These are different facts and the group note ran them together.

| MZERO artifact | Lean consumers outside its own file |
|---|---|
| **`detF_family_magnitude_bound`** (the MZERO.5 magnitude/growth work) | **`MixtureMLBound.lean` (MML.5), `MixtureInnerDCF.lean` (MML.8), `MixtureRDFPoleData.lean` (MML.11)** — genuinely load-bearing |
| **`ChordPoleFamily` / `zeros_infinite_of_chordPoleFamily`** (MZERO.3/4/6/7's abstraction) | **`HardSphere/BaxterChordFamily.lean`, `HardSphere/BaxterPoles.lean`** — the **scalar** track reuses it, so the `Analysis/` migration paid off outside the mixture |
| **`detC_zeros_infinite_unconditional`, `detF_zeros_infinite`, `Q0_det_c_zeros_infinite`** (MZERO.1, Route A) | **none** — every hit is a docstring |
| **`detC_zeros_infinite_of_boundaryGrowth`, `detC_zeros_infinite_of_growth`** (MZERO.11, Route B) | **none** — every hit is a docstring |

So "infinitely many HS poles" is currently **proved and unconsumed**. That is *expected*, not a
defect: **MRS.3** removed the DCF consumer outright (the `det Q̂₀` zeros never enter `Ĉ₁`), and the
only remaining consumer is **MML.8**, which is open. Worth stating because this project treats
consumer-less statements as a hazard class (cf. MRS.0b, written precisely to test a consumer-less
axiom; four axioms here were false *as stated* and every one was caught by a proof attempt, never by
`#print axioms`). MZERO's headline has had no such test — but unlike an axiom it is *proved*, so the
exposure is only to a mis-*statement*, and finding 3 below is the check that closes that.

**2. ⚠ Naming trap: `MixParams.Phys` does NOT mean "the physical Lebowitz coefficients".** Its own
docstring is accurate — "ordered positive diameters and entrywise positive matrices" — but
`chordPoleFamily_detF_exists P hP` with `hP : P.Phys` reads, at a glance, as though MZERO had been
instantiated at the actual PY mixture. It has not: `rr`, `Qp`, `Qpp` are **free** matrices
constrained only by positivity. `Q0phys` / `Qppphys` / `rhoGeoPhys` **appear nowhere** in
`MixtureChordFamily.lean`, `MixtureHSZeros.lean`, or `MixtureHSCounting.lean`.

**3. The physical bridge is available, favourable, and unwritten — this is the one actionable item.**
Reading the definitions in `MatrixQ0.lean`, the Lebowitz coefficients are *manifestly* entrywise
positive whenever `vac = 1−η > 0`, `σ > 0`, `ρ ≥ 0`:

```
Q0phys  = (2π/vac)·( (σᵢ+σⱼ)/2 + π·ξ₂·σᵢσⱼ/(4·vac) )     every summand > 0
Qppphys = (2π/vac)·( 1 + π·ξ₂·σⱼ/(2·vac) )                every summand > 0
rhoGeo  = √(ρᵢρⱼ) > 0,      ξ₂ = Σ ρᵢσᵢ² ≥ 0
```

Confirmed numerically at the reference mixture (σ=[1,2], x=[0.25,0.75], ρ*=0.139 ⇒ η=0.4549,
vac=0.5451): `min Q0phys = 19.03`, `min Qppphys = 26.53`, `min rhoGeo = 0.0348`, `0<σ₀<σ₁` — so
**`MixParams.Phys` holds for the physical mixture** and `detC_zeros_infinite_unconditional` applies
to it. End-to-end non-vacuity re-checked by locating the zeros themselves at those *physical*
coefficients (Newton from MZERO.5's anchor `i·2πn/σ₁`): 8 distinct zeros,
`s = −0.417+3.389i, −0.946+6.291i, …, −2.362+25.075i`, `|detC| ≤ 3.4e-15`, mean `Im` spacing
**3.098** against the predicted `2π/σ₁ = 3.1416` — reproducing MZERO.2's recorded "Δ Im ≈ π" GO gate.

### ✅ MZERO.12 — the physical instantiation, WRITTEN (2026-07-31)

**`LeanCode/HSMixture/MixtureZerosPhys.lean`** (ns `FMSA.MixtureHSPoles`), axiom-clean, full build
green (8716 jobs). A **new file**, so `MixtureChordFamily.lean` and its neighbours — the MML.8
working set — are untouched.

| theorem | statement |
|---|---|
| `Pdens_one` | `Pdens sigma rho 1` **is** the physical pack (`1 • rho = rho`) — the bridge between the homotopy packaging and the plain coefficients |
| **`detC_zeros_infinite_phys`** | `0 < σᵢ`, `σ₀ < σ₁`, `0 < ρᵢ`, `η < 1` ⇒ `{s : ℂ \| detC ![σ₀,σ₁] (↑rhoGeoPhys) (↑Q0phys) (↑Qppphys) s = 0}.Infinite` |
| **`Q0_mat_c_phys_det_zeros_infinite`** | the same on the matrix itself — `(Q0_mat_c s σ ↑rhoGeoPhys ↑Q0phys ↑Qppphys).det`, i.e. **definitionally MRS.7's `Qphys`**. The form a consumer wants |
| `example` (non-vacuity) | the four hypotheses hold simultaneously at the project's reference mixture `σ=[1,2]`, `ρ=[0.03475,0.10425]` (`η ≈ 0.4549`); the `η < 1` step needs only `π < 4` |

⚠ **It proves nothing new — and the reason is the finding.** The three `MixParams.Phys` positivity
obligations were **already theorems**: `Q0phys_pos`, `Qppphys_pos`, `rhoGeoPhys_pos`, and even the
packaged **`Pdens_Phys`**, all in `MixtureDetUniform.lean`. They were built for the **density
homotopy** of the physics-axiom-retirement track (`MatrixDetPoleFree` / `MixtureDetHomotopyPhys`),
whose consumer is `hRunif_Pdens` — and **nobody ever pointed them at `detF_zeros_infinite`**. So the
whole corollary is `Pdens_Phys … 1` plus `1 • rho = rho`. My first draft re-proved all three from
scratch and the build caught it as a name clash (`environment already contains
'FMSA.MixtureHSPoles.Qppphys_pos'`) — `feedback_stale_blockers` again, in its purest form: the
missing fact was already in the tree, merely never exported to the group that needed it. **Two
tracks had each done half of this and neither knew.**

Layering respected (`HSMixture/` may not import `YukawaDCF/`), so the statement stops at the
`Q0_mat_c` level; an `FMSA.MRS`-side restatement in terms of the literal `Qphys` alias is a one-liner
whenever someone wants it.

---

### ⚠ Layering violation in `MixtureRDFUniqueness.lean` — found and repaired 2026-07-31

Checking that layering claim turned up a real back-edge, present since `c8efdc4`:
**`HSMixture/MixtureRDFUniqueness.lean` imported `YukawaDCF/MixtureRDFStructureFactor.lean`**, so
`CONVENTIONS.md`'s first self-check grep had been non-empty. All three greps print nothing again.

**The dependency was one declaration out of 26** — `det_eq_of_wienerHopf_factorization`, i.e.
`T₀ = Qp·Qmᵀ ⇒ det T₀ = det Qp · det Qm`, whose proof is `Matrix.det_mul` then
`Matrix.det_transpose`. No Baxter, Yukawa or mixture content whatsoever; it was in `YukawaDCF/`
only because MML.9 happened to be where it was first needed.

**Repair (not a file move).** The generic core is now
**`Analysis/MatrixIdentity.det_mul_transpose`** — `(A * Bᵀ).det = A.det * B.det`, stated without the
factorization hypothesis so it is a plain rewrite rule, generic in ring and index type. Both sides
cite it: `MixtureRDFUniqueness.matStructureFactor_isUnit_of_det_ne_zero` now does
`rw [Matrix.isUnit_iff_isUnit_det, hfact, det_mul_transpose]` and dropped the `YukawaDCF` import;
`MixtureRDF.det_eq_of_wienerHopf_factorization` keeps its name, its physics-facing docstring and all
four of its in-file uses, and became a one-line consequence.

**Moving the file up would have been wrong.** `MixtureRDFUniqueness` is matrix OZ★ uniqueness — a
**hard-sphere** statement (MML.9 itself established that the residual collapse content is `Ĥ₀`, the
Yukawa factor `Ĉ₁` between the two `S₀`'s being pole-free). Relocating it to `YukawaDCF/` would have
encoded the false claim that it needs a Yukawa tail. Push the generic lemma **down**; do not move the
specific file **up**.

**Ledger unchanged** — verified, not assumed: `#print axioms` after the repair gives
`det_mul_transpose`, `det_eq_of_wienerHopf_factorization`,
`matStructureFactor_isUnit_of_det_ne_zero`, `rdf_entry_star_eq`, `rdf_entry_double_pole` = standard
three, and **`matOzStar_unique` still carries exactly `FMSA.matRadialShell_bounded_injective`** and
nothing new. Full build green (8716 jobs).

---

### Task MZERO.1 — Infinitely many HS poles for N=2

**Statement.** `det(Q0_mat_c s) = 0` has infinitely many distinct complex solutions.

**Strategy.** The 2×2 determinant det(Q̂₀(s)) is an entire function of s (each entry of
Q̂₀ is entire by Y1.1, determinant of entire matrix is entire). It is not identically
zero (det → 1 as s → ∞ by Y1.1's entry formulas). For a non-constant entire function,
the zeros are either finite in number or form a discrete infinite sequence.

The non-constancy + "not eventually large" argument:
- As Re(s) → +∞: the off-diagonal entries Q̂₀₀₁, Q̂₀₁₀ → 0 (GA.2 mechanism), so
  det(Q̂₀) → Q̂₀₀₀·Q̂₀₁₁ → 1 (bounded away from 0 for large real s).
- On the imaginary axis: behavior like N=1 `Qhat_complex` (periodic structure from
  e^{−is·σ} terms); Rouché applied on large circles shows zeros accumulate.

Alternatively, extend POLE.3's Banach-contraction strategy to det(Q̂₀):
- Parameterize zeros of det(Q̂₀(s)) by solving `s = F_n(s)` for a family of maps F_n
  derived from the quasi-polynomial structure of det(Q̂₀).
- Show the contraction bound holds for each n (numerically: run the analog of POLE.2
  for the N=2 det).

**Depends on.** MML.1 (det formula), Y1.1 (entries entire), M.4 (det ≠ 0 on real axis),
POLE.3 proof strategy.
**File.** `HSMixture/MixtureHSZeros.lean` (foundation) / `MixtureHSPoles.lean`.

**Foundation — DONE (2026-07-15), axiom-clean, `HSMixture/MixtureHSZeros.lean`** (namespace
`FMSA.MixtureHSPoles`).  The non-constancy every infinitely-many-zeros argument starts from:
- `Q0_det_c_tendsto_one` — `det(Q0_mat_c (t:ℂ) …) → 1` as real `t → +∞` (via `Matrix.det_fin_two`):
  diagonal Baxter entries → 1 (`q0_diag_c_tendsto_one`) and the off-diagonal *product* → 0
  (`q0_offdiag_prod_tendsto_zero` — the two `λ`-shifts are opposite, `λ_{01}+λ_{10}=0`, so the
  exponentials cancel and each Baxter bracket `φ₁,φ₂ → 0`).
- `Q0_mat_c_at_zero` (`Q0_mat_c 0 = I`, Lean `0/0=0` value) + `Q0_det_c_not_identically_zero`
  (`∃ s, det ≠ 0`).
- `q0_entry_c_differentiableAt` / `Q0_det_c_differentiableAt` — **holomorphy away from `s=0`**: each
  Baxter entry, and (for `N=2`, via `Matrix.det_fin_two`) `det(Q̂₀)`, is `DifferentiableAt ℂ` at every
  `s₀ ≠ 0` (`fun_prop (disch := assumption)` on the `s^{2,3} ≠ 0` div side-goals).  With the
  non-constancy above, this is the holomorphic-and-non-constant setup a zero-counting argument needs.
- Helpers: `cofReal_inv_tendsto_zero`, `cexp_neg_mul_tendsto_zero`, `phi1c_tendsto`/`phi2c_tendsto`,
  `bracket_tendsto_zero`, `offdiag_prod_eq`.
- *Note:* this file imports only `Q0Complex` (uses `Matrix.det_fin_two` directly, not MML.1's
  `Q0_det_fin_two`), so it builds independently of the currently-in-progress `BaxterResidue` import
  that `MixtureHSPoles` (MML.1/MML.2) transitively pulls.

**Status.** ◑ **foundation DONE** (non-constancy / `det → 1`); the full *infinitely many zeros*
(zero family) is decomposed into **MZERO.2–MZERO.11** below.

---

### MZERO.2–MZERO.11 — MZERO.1 zero-family decomposition (routes overview)

The "`det(Q̂₀(s))` has infinitely many complex zeros" core (= MZERO.1), split into numbered tasks
MZERO.2–MZERO.11 across **two independent routes** (either alone closes MZERO.1). Foundation done
(`Q0_det_c_tendsto_one` non-constancy + `Q0_det_c_differentiableAt` holomorphy off `s=0`,
`MixtureHSZeros.lean`).

- **Route A — Banach contraction (MZERO.2–MZERO.7)**, POLE.3-style, mirrors `BaxterPoles.lean`. ✓ DONE
  (2026-07-15), axiom-clean & `sorry`-free, **conditional on the MZERO.5 magnitude bounds**. **Unified with
  POLE.3:** the generic chord engine + shared **`ChordPoleFamily F`** predicate +
  `zeros_infinite_of_chordPoleFamily` live in `Analysis/BanachPoleFamily.lean`; `Q0_det_c_zeros_infinite`
  (mixture) and `G_baxter_zeros_infinite_of_chordPoleFamily` (Baxter) both consume it ⇒ **MZERO.5 ≡ POLE.3's
  open `hstep`** (one asymptotic-family lemma closes both). `#print axioms` on all three →
  `[propext, Classical.choice, Quot.sound]`.
- **Route B — Rouché / zero-counting (MZERO.8–MZERO.11)**. *Mathlib has no ready Rouché or argument principle,
  but zero-counting routes through Jensen's formula + the divisor:* `MeromorphicOn.circleAverage_log_norm`
  (`Analysis/Complex/JensenFormula.lean`) gives `circleAverage (log‖f·‖) c R = ∑ᶠ u, divisor f
  (closedBall c |R|) u · log(R‖c−u‖⁻¹) + … + log‖trailingCoeff‖`, and `divisor f (closedBall c R)` counts
  zeros for analytic `f` (no poles). *Contradiction route:* finitely many zeros ⇒ `divisor det
  (closedBall 0 R)` stabilizes ⇒ RHS ~ `(const)·log R`; but the boundary average grows `≥ c·R` (the
  `e^{−sσ}` growth) ⇒ `R ≫ log R` ⇒ contradiction ⇒ ∞ many zeros. MZERO.8 done, MZERO.10/MZERO.11 structural
  capstones done, MZERO.9 `divisor ≥ 0` unconditional, **`hJensen` NOW PROVED** (2026-07-16,
  `detC_jensen_log_bound`) — so **Route B is fully closed modulo only MZERO.10** (`DetBoundaryGrowth`),
  the `e^{−sσ}` boundary-growth input (`detC_zeros_infinite_of_boundaryGrowth`).

---

### Task MZERO.2 — feasibility gate (Python, POLE.2 analog: GO/NO-GO)

*(Route A.)* Feasibility check. ✓ **DONE — GO** (`verify_mixture_hs_poles.py`, σ=[1,2], ρ=[0.2,0.05],
η=0.314). Found a **quasi-periodic zero family** (Δ Im ≈ π, 22 zeros up to Im≈239, `Re(s_n)` growing
~`log(Im)`), and a **chord-Newton** map `g(s)=s−F(s)/F′(s1)` on a disk `r=0.15` satisfies **both** Banach
conditions for **all** of them with margin: Lipschitz `K ≈ 0.30–0.35` — critically **uniform** across the
whole family (does *not* drift to 1 as `n→∞`, unlike BAXTER's plain-Newton concern), self-map gap
~`1e-40 ≪ r(1−K)≈0.10`. ⇒ the Banach path (MZERO.3–MZERO.7) is viable with **chord-Newton**; each zero is
simple (`F′≠0`). Also confirms the quasi-periodic structure Route B's boundary-growth estimate (MZERO.10)
relies on.

---

### Task MZERO.3 — generic chord-Newton Banach existence wrapper

*(Route A, Lean.)* `chord_zero_exists_of_bounds (F : ℂ → ℂ) …` (Lipschitz self-map `chordPhi F Fp1` of a
`Metric.closedBall` ⇒ `∃ s ∈ ball, F s = 0`), from `ContractingWith.exists_fixedPoint'`. Map-independent.
✓ **DONE (axiom-clean)**, shared `Analysis/BanachPoleFamily.lean`. Cleaner than
`G_baxter_pole_exists_of_bounds`: the `fp ⟹ zero` direction folds in (no `hFixedImpliesRoot` hyp),
because chord-Newton's `fp ⟺ F = 0` is unconditional.

---

### Task MZERO.4 — chord-Newton map + fixed-point ⟺ zero

*(Route A, Lean.)* `chordPhi F Fp1 s := s − F s / Fp1` + `chordPhi_fixedPt_iff` (`IsFixedPt ⟺ F s = 0`,
given `Fp1 ≠ 0`). ✓ **DONE (axiom-clean).** One-line (`sub_eq_self` + `div_eq_zero_iff`); **simpler than
the log-map** `baxterPhi_fixedPt_implies_zero` (no `Complex.log`, `Complex.exp_log`, `2π`-periodicity, or
branch-safety) — the payoff of the MZERO.2 chord-Newton choice.

---

### Task MZERO.5 — magnitude bounds (`ChordPoleFamily det_c`) — the residual gap

*(Route A, the one remaining piece — now UNIFIED with POLE.3.)* Construct a `ChordPoleFamily det_c`: the
chord-Lipschitz bound `∀ s ∈ ball, ‖1 − det′(s)/Fp1‖ ≤ K` (`K<1`) + the good-guess
`hstep : ‖det(s₁)/Fp1‖ ≤ r(1−K)` + the asymptotic pole locations. ◑ Two things pin it down:
- **Shared predicate** `ChordPoleFamily F` (`Analysis/BanachPoleFamily.lean`) — the *same* obligation
  `G_baxter` (POLE.3) carries; `Q0_det_c_zeros_infinite` and `G_baxter_zeros_infinite_of_chordPoleFamily`
  both consume it. So MZERO.5 ≡ POLE.3-`hstep`, and one asymptotic-family lemma closes **both**. (**POLE.5 is
  DONE** — the `n^{1−2r/σ}` summability bound; its magnitude machinery
  `abs_exp_neg_ikn_sigma_*`/`G_baxter_deriv_lower_bound_of_zero` is the reusable *technique* for the
  mixture bounds, transposed to 2 frequencies.)
- **MZERO.5a bridge** `detC_lam_free` (`MixtureHSZeros.lean`, ✓ DONE axiom-clean) — `det_c` has **no
  `e^{±λs}` blow-up** (off-diag shifts cancel), so `det_c = (diag₀)(diag₁) − ρ₀₁ρ₁₀(bracket₀)(bracket₁)`
  is a **2-frequency exp-polynomial in the same Baxter brackets as `G_baxter`** — the structural reason
  the two share the class.

What remains: the *quantitative* `‖det″‖`-upper/`‖det′‖`-lower bounds + the asymptotic Im-quantized zero
locations (the 2-freq analog of POLE.5's `Im(k_n)=Θ(ln n)`). `det` differentiability on the disk **is**
proved (`Q0_det_c_differentiableAt`); no branch-safety (unlike BaxterPoles' `R_mem_slitPlane`).


**✅ 2026-07-17 — MZERO.5 CLOSED (⇒ MZERO.1 CLOSED).** `HSMixture/MixtureChordFamily.lean`
(3497 lines, axiom-clean, no `sorry`, full `lake build` green 8646 jobs). Headline:

```
detC_zeros_infinite_unconditional {sig0 sig1 : ℝ} (h0 : 0 < sig0) (h01 : sig0 < sig1)
    {rr Qp Qpp : Fin 2 → Fin 2 → ℝ} (hrr : ∀ i j, 0 < rr i j) (hQp : ∀ i j, 0 < Qp i j)
    (hQpp : ∀ i j, 0 < Qpp i j) :
    {s : ℂ | detC ![sig0, sig1] (fun i j => (rr i j : ℂ)) (fun i j => (Qp i j : ℂ))
      (fun i j => (Qpp i j : ℂ)) s = 0}.Infinite
```

— **hypotheses are parameter positivity/ordering ONLY**; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. Also `chordPoleFamily_detC_exists` (the
`ChordPoleFamily detC` value the shared engine consumes), plus the `MixParams`-form siblings
`chordPoleFamily_detF_exists` / `detF_zeros_infinite` / `chord_conditions_eventually`
(`MixParams.detF P = detC ![P.sig0,P.sig1] … ` is `rfl`). This **retires the `hbound`/`hstep`
hypotheses of `Q0_det_c_zeros_infinite`** — that conditional theorem is superseded for the
existence question (kept as the ∀-parameterised layer). **Route A is now the completed genuine
route** (Route B remains a reformulation of MZERO.1, per `detC_boundaryGrowth_iff_infinite_zeros`).

Construction (2-freq transposition of `POLE.9`'s template): parameters packed as `MixParams` +
`Phys`; the **monomial polynomialisation** `Wfun P s = s⁶·detC s = McNum + M0Num·e^{−sσ₀} +
M1Num·e^{−sσ₁} + M01Num·e^{−s(σ₀+σ₁)}` (from `detC_lam_free`, clearing `s⁶`; all four `*Num`
explicit polynomials); anchor `aₙ = i·2πn/σ₁` with **exact phase kill** of the σ₁-frequency;
the **derived guess** `sGuess P n = −(1/σ₁)·log t + i·2πn/σ₁`, `t = ‖McNum(aₙ)‖/‖M1Num(aₙ)‖`
(note `Re < 0` — the log-lift is NEGATIVE here, opposite to Baxter); anchor envelopes
(`McNum_two_point_le`, `M1Num_two_point_le`, `tRat_upper/lower`), derivative `derivF` +
`detF_hasDerivAt` (quotient rule off `Wfun`), `WD_at_sGuess_lower`, `Wfun_on_disk_le`,
`WD_var_on_disk_le`, `Ag_lower_and_step`, `chord_bound_at`, and `chord_conditions_eventually`
(threshold bundle + push along `n ↦ 2πn/σ₁`). Constants: radius `rc = 1/(20σ₁)`, `K = 3/4`;
separation from the **exact** `Im(sGuess P n) = 2πn/σ₁` (gap `2π/σ₁ > 2rc`, `Real.pi_gt_three`).
Reused verbatim: `FMSA.HardSphere.norm_sub_ratio_mul_le` (generic phase-difference bound),
`eventually_log_cap`. Lean lessons: `field_simp`+`ring` on the chord split fails in a fat
context — extract the pure-algebra lemma `chord_algebra_split`
(`1 − (B/x⁶)/(A/y⁶) = (A−B)/A + (B/A)(1 − y⁶/x⁶)`) and `exact` it; inserting a lemma between
`set_option maxHeartbeats … in` and its theorem silently detaches the option (spurious `whnf`
timeout); `rpow` avoided throughout in favour of `Real.exp (δ·log t)` + `Real.add_one_le_exp`.

**2026-07-16 — POLE-session takeover + numerical scoping (GO).** With `POLE.9`'s 1-freq chord
template complete (`HardSphere/BaxterChordFamily.lean`), this session is closing MZERO.5 in a
new file `HSMixture/MixtureChordFamily.lean` (MixtureHSZeros/Counting/MLSeries untouched).
Scoping (`mzero5_scoping.py`, σ∈{[1,2],[1,1.5],[0.8,2.3]}, n→5000, mpmath): **(i) dominant
balance identified** — at every zero, `|Mc| ≈ |M₁E₁| ≈ 1` while `|M₀E₀|, |M₀₁E₀E₁| → 0`
(monomial split `detC = Mc + M₀e^{−sσ₀} + M₁e^{−sσ₁} + M₀₁e^{−s(σ₀+σ₁)}` from `detC_lam_free`);
the zero family balances the constant term against the **larger-diameter** frequency `σ₁`,
spacing `Δ Im = 2π/σ₁` (the recorded `π` was `2π/σ₁` at `σ₁=2`); **(ii) `Re s_k` is NEGATIVE**,
`≈ −(2/σ₁)·ln|s_k|` (MZERO.2's scan window `re∈[−6,1]` already said so); (iii) the **derived
guess** `s_guess(n) = −(1/σ₁)ln|Mc(aₙ)/M₁(aₙ)| + i·(2πn − arg(−Mc/M₁)(aₙ))/σ₁`, anchor
`aₙ = i·2πn/σ₁`, converges to the true zeros (`|g−s*|: 0.33 → 0.0014` over `n=2→2000`), chord
step → 0, `K(r=0.15) ≈ 0.29–0.41` uniform, `|det′(s_k)|/(σ₁|Mc|) → 1.000`; chord-OK from
`n ≈ 10–20` at all three σ sets. Same construction shape as `POLE.9` (phase kill at the anchor
is exact for the σ₁-frequency since `σ₁·Im aₙ = 2πn`).
---

### Task MZERO.6 — chord-map Lipschitz + MapsTo (disk into itself)

*(Route A, Lean.)* `chordPhi_lipschitzOnWith` (from `HasDerivAt F F′` + the MZERO.5 bound, via
`Convex.lipschitzOnWith_of_nnnorm_deriv_le`) + generic `mapsTo_closedBall_of_lipschitzOnWith_of_dist_le`.
✓ **DONE (axiom-clean)** — now in the shared `Analysis/BanachPoleFamily.lean`.

---

### Task MZERO.7 — infinitude engine + `det` instantiation

*(Route A, Lean.)* The generic **`zeros_infinite_of_chordPoleFamily`** (`BanachPoleFamily.lean`, per-`n`
chord existence → `choose` → injective via `hsep` → `Set.infinite_of_injective_forall_mem`) is the shared
infinitude engine; **`Q0_det_c_zeros_infinite`** (`MixtureHSZeros.lean`) is a thin instantiation packaging
the det-family data (Im-spacing ⇒ `hsep`, differentiability off `0`) into a `ChordPoleFamily det_c`. ✓
**DONE (axiom-clean), conditional on MZERO.5** — exact parity with, and now sharing the predicate of,
`G_baxter_zeros_infinite_of_chordPoleFamily`.

---

### Task MZERO.8 — `det(Q̂₀)` meromorphic (for Jensen)

*(Route B, Lean.)* ✓ **DONE**, axiom-clean (`det_meromorphicAt`, `det_meromorphicOn`,
`MixtureHSZeros.lean`). **Much easier than planned — no analytic continuation needed:** each
`φ₁,φ₂ = (entire)/s^{2,3}` is `MeromorphicAt` everywhere as a *ratio of entire functions*, meromorphic is
closed under `+,−,×,÷`, and `fun_prop` (MeromorphicAt closure lemmas are `@[fun_prop]`) discharges the
whole `det_fin_two` combination. The Lean `0/0` value at `s=0` is irrelevant (`MeromorphicAt` only sees a
punctured nbhd) ⇒ **Route B's `s=0` "hard part" dissolves**; only the MZERO.10 boundary-growth estimate
remains hard.

---

### Task MZERO.9 — `divisor det ≥ 0` + `hJensen` Jensen-counting bound

*(Route B, Lean, `MixtureHSCounting.lean`.)* The bound: `MeromorphicOn.circleAverage_log_norm` (Jensen) +
`divisor det ≥ 0` (`det` poleless — each `φ=num/sⁿ` has `meromorphicOrderAt φ 0 = 0`, `num` vanishing to
order `n`) + finite support ⇒ finite zeros give the `O(log R)` bound. ✓ **DONE (2026-07-16, axiom-clean).**
- **`divisor det ≥ 0` is now UNCONDITIONAL** (`det_divisor_nonneg`, axiom-clean, 2026-07-15). The "det has
  a limit at `0`" hyp of `det_divisor_nonneg_of_tendsto` (reduced via
  `tendsto_nhds_iff_meromorphicOrderAt_nonneg`) is discharged by the **Baxter removable values at `s=0`**:
  `φ₁(0)=−σ²/2` (`phi1_tendsto`), `φ₂(0)=σ³/6` (`phi2_tendsto`).
- Mechanism: exp-Taylor limits `(eʷ−1−w)/w²→½` (`expTaylor2`), `(eʷ−1−w−w²/2)/w³→⅙` (`expTaylor3`), proved
  via `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` (order of the Taylor remainder from vanishing
  derivatives) + the reusable `remainder_div_tendsto_zero` (`f w/wⁿ→0` when `analyticOrderAt f 0 ≥ n+1`).
  Substitution `w=−sσ` (`neg_mul_tendsto_punctured`) gives the `φ` limits; **the `s³` odd power flips the
  sign** so the `φ₂` multiplier is `+σ³` (not `−σ³`).
- Chain: `q0_entry_c_tendsto` (entry limit `δ − ρ·(Qp·(−σ²/2)+Qpp·(σ³/6))`, `e^{−λs}→1`) → `detC_tendsto`
  (`det_fin_two` combination) → `det_divisor_nonneg`. **The `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6` are the `s=0`
  Taylor coefficients of the Baxter entries — reusable for the inner-core polynomial / numerical
  construction (cf. MPOLY, GAP.9).**
- **`hJensen` NOW PROVED** ✓ (2026-07-16, axiom-clean): `detC_jensen_log_bound` (`MixtureHSCounting.lean`)
  discharges it by citing the abstract MA.5 `circleAverage_log_norm_le_of_finite_zeros`
  (`Analysis/JensenCounting.lean`) + a `detC`-specific **bridge** (finite *literal* zeros ⇒ finite
  *divisor* support): every point of nonzero order is either `s=0` (the removable point, whose Lean junk
  value need not vanish) or — being analytic there (`Q0_det_c_differentiableAt`, `u≠0`) with positive
  order — a genuine zero (`AnalyticAt.analyticOrderAt_ne_zero`), so the support sits in `{0} ∪ zeros`,
  finite. **⇒ Route B now closes `Set.Infinite {detC=0}` modulo ONLY MZERO.10** (`DetBoundaryGrowth`),
  via `detC_zeros_infinite_of_boundaryGrowth` — the `hJensen` hypothesis is gone.

---

### Task MZERO.10 — boundary growth hypothesis

*(Route B, Lean; the `detC` half in `HSMixture/MixtureHSCounting.lean`, the generic predicate and
`detBoundaryGrowth_of_linear` in **`Analysis/BoundaryGrowth.lean`** ns `FMSA.BoundaryGrowth` — migrated
by MRS.9b, checked 2026-07-31.)* ✓ **DONE** as the input hypothesis `DetBoundaryGrowth f`
(`circleAverage (Real.log‖f·‖) 0 R` beats every `M·log R + C`) + `detBoundaryGrowth_of_linear` (a
`≥ c·R − C₀` estimate implies it, via `Real.isLittleO_log_id_atTop`). Axiom-clean.

**⚠ MZERO.10 for `detC` is EQUIVALENT to MZERO.1 — not an independent analytic input (2026-07-16,
PROVED).** By the integrated Jensen identity `circleAverage(log‖detC·‖) 0 R = ∫₀ᴿ n(t)/t dt + const`
(no poles ⇒ `divisor ≥ 0`), super-log growth of the boundary average ⟺ `n(t)→∞` ⟺ **infinitely many
zeros = MZERO.1**. The theorem **`detC_boundaryGrowth_iff_infinite_zeros`** (axiom-clean,
`MixtureHSCounting.lean`, `0<σᵢ`) proves this equivalence: `⟸` is `detC_zeros_infinite_of_boundaryGrowth`
(= `hJensen`'s contrapositive), `⟹` is `detC_boundaryGrowth_of_infinite_zeros` (Jensen LOWER bound —
`K` zeros in the ball give `circleAverage ≥ K·log R − const`; rules out `detC` locally-zero via the
identity theorem on `ℂ∖{0}` + the non-vanishing witness `Q0_det_c_tendsto_one`). **Correction to the
earlier note:** the growth is NOT "from `e^{−sσ}` magnitude" — a zero-*free* exponential `e^{−sτ}` has
circle-average `0` (`∫cos θ = 0`); the linear log-average growth comes **entirely from the (linearly
dense) zeros**. So Route B is a Jensen *reformulation* of MZERO.1, not an independent closure of it —
proving MZERO.10 from analytic structure alone is exactly as hard as the whole result. The genuine
independent route is **Route A (MZERO.5/hstep)**.

---

### Task MZERO.11 — Jensen capstone ⇒ ∞ many zeros

*(Route B, Lean; `infinite_zeros_of_growth` now in **`Analysis/BoundaryGrowth.lean`**, the `detC`
capstones in `HSMixture/MixtureHSCounting.lean` — checked 2026-07-31.)* ✓ **structural capstone DONE** (`infinite_zeros_of_growth`: a
Jensen log-bound for the finite-zeros case + `DetBoundaryGrowth` ⇒ `Set.Infinite {f=0}`; pure
contradiction) and `detC_zeros_infinite_of_growth` (**independent Route-B proof** of
`Set.Infinite {detC=0}`, matching Route A's `Q0_det_c_zeros_infinite`). Axiom-clean. Reuses
`det_meromorphicOn` (MZERO.8) for Jensen's hypothesis. **With MZERO.9's `hJensen` now proved (2026-07-16),
the hJensen hypothesis is discharged**: `detC_zeros_infinite_of_boundaryGrowth` gives the Route-B
infinitude conditional on **only** `DetBoundaryGrowth` (MZERO.10) — full parity with Route A (which rests
on the MZERO.5 magnitude bounds).


### Task MRS.0b — the `n = 1` bridge: `pyhs_mixture_no_spinodal` at one component is a THEOREM

**✓ DONE 2026-07-19, full build green (8678 jobs), no `sorry`, `#print axioms` = STANDARD THREE
ONLY.** New file `HSMixture/MixtureNoSpinodalN1.lean`; the axiom's own file is untouched except for
a docstring correction.

**Why this was worth doing before any consumer exists.** `pyhs_mixture_no_spinodal` (MRS.0) is
pre-placed with **no consumer**. That is a specific hazard, not a neutral state: a consumer-less
axiom has no downstream use that could ever expose a mis-statement, and this project has had **four**
axioms that were false *as stated* (MA.5 literal-zero-set, MA.2 ordered-vs-circle-grouped, MA.4,
clause 6a's jump at σ) — every one caught **only** by a proof attempt, never by `#print axioms`, the
build, or review. The `n = 1` slice is the one mechanically checkable soundness test such an axiom
admits, because there the mixture claim *must* reduce to the already-proven scalar `pyhs_no_spinodal`.

**Result — stronger than "consistent".** `pyhs_mixture_no_spinodal_n1` has the **same statement as
the axiom specialised to `Fin 1`** and is proved **without** the axiom, depending on nothing but
`[propext, Classical.choice, Quot.sound]`. Not even MA.13/MA.14 appear, because the scalar
`pyhs_no_spinodal` is itself axiom-clean via the `k⁶` route. **So at `n = 1` the axiom is redundant,
and its entire content lives in `n ≥ 2`** — consistent with the numerics, where every certificate
that succeeds at `N = 1` (term-wise dominance) fails from `N = 2` onward.

**The chain (four steps).**

1. **Moments.** `xi2_n1 : ξ₂ = ρ₀σ₀²`, `etaMix_n1 : η = πρ₀σ₀³/6` — the latter is *literally* the
   `heta_def` hypothesis `pyhs_no_spinodal` requires, so the coupling conventions agree exactly.
2. **Coefficients.** `Q0phys_n1 : Q0phys ρ σ 0 0 = q_prime_py η σ₀` and
   `Qppphys_n1 : Qppphys ρ σ 0 0 = q_doubleprime_py η`. Proof: substitute `ρ₀ = 6η/(πσ₀³)` and
   `field_simp`/`ring`. **This closes a loop** — `q_doubleprime_py`'s docstring *derives* it from the
   multicomponent formula `(2π/Δ)(1+πR_jξ₂/(2Δ))`, so the scalar and mixture coefficients were two
   hand-transcriptions of one paper; they are now a machine-checked identity.
   Also `rhoGeoPhys_n1 : √(ρ₀ρ₀) = ρ₀`.
3. **Kernels.** `qhat_complex_eq_mixture_kernel` — the mixture's two Laplace kernels reassemble the
   scalar transform. The observation that makes it easy: with `s = ik`,
   `(1−sσ−e^{−sσ})/s² = −∫₀^σ(σ−r)e^{−sr}dr` and `(1−sσ+(sσ)²/2−e^{−sσ})/s³ = ∫₀^σ(σ−r)²/2·e^{−sr}dr`,
   which is **exactly** the shape of `q0_poly r = ρ(Q'(r−σ) + Q''(r−σ)²/2)`. So no integration is
   needed: `Qhat_complex_formula` (POLE.1) already supplies the closed form, and both sides are
   rational in `s` and `e^{−sσ}` ⇒ `field_simp; ring`. ⚠ **`Complex.I` never needs `I² = −1`** — the
   identity holds treating `I` as a formal atom, which is why `ring` closes it.
4. **Determinant.** `Q0_mat_c_phys_n1_det` via `Matrix.det_fin_one`; the off-diagonal shift
   `λ₀₀ = (σ₀−σ₀)/2` vanishes and `δ₀₀ = 1`.

Assembly: `det Q̂₀(ik) = 1 − Q̂(k)`, then `qhat_complex_ne_one_of_real`.

**Prior art check:** the bridge did not exist in any form. The only `Fin 1` lemma touching `Q0_mat`
was `Q0_mat_n1_entry` (`MatrixQ0.lean:254`), which terminates in an unfolded `q0_entry`, never a
named scalar object; `MatrixN1.lean` proves the `Fin 1` collapse only for *abstract constant* 1×1
matrices, so it does not compose with `Q0_mat_phys`. None of `etaMix`/`Q0phys`/`Qppphys` had an
`n = 1` reduction, and `Matrix.det_fin_one` appeared nowhere in `LeanCode/`.

**What this does NOT do.** It does not make the general axiom any more provable. The `k⁶` route is
still dead for `N ≥ 2` (term-wise dominance fails 300/300, even at diameter ratio ≈ 1.00 — a phase
artifact, not a weakness of the claim), so MRS.0 remains MA.14-class, needing a winding argument.
The bridge is a *validation*, not a step toward the proof.


### Task MRS.9 — `HSMixture/` library reorganization

**✓ Overall COMPLETE: 9a–9c DONE 2026-07-19, 9d DONE 2026-07-27.**  The library reorganization is **one** task —
create the `HSMixture/` layer, re-home misfiled files, split straddlers into `Analysis/`, normalize
the species binder — so it is recorded here as `MRS.9` with four sub-parts, **not** as four letter
suffixes of the physics axiom `MRS.0`.  Consolidated from the ex-`MRS.0c/0d/0e/0f` records
2026-07-19 (`MRS.0`/`MRS.0b` remain the physics-axiom cluster above).  The layering invariant it
establishes — `Analysis/ ← HardSphere/ ← HSMixture/ ← YukawaDCF/`, imports leftward only — is in
`CONVENTIONS.md`.

#### MRS.9a — `LeanCode/HSMixture/` — the N-component hard-sphere layer

**✓ DONE 2026-07-19, build green (8683 jobs, identical to the pre-move baseline ⇒ pure move,
no declaration added or removed), all four invariants re-verified.**

**Motivation.** `pyhs_mixture_no_spinodal` sat in `YukawaDCF/` although it is a pure hard-sphere
statement. Chasing that revealed a structural problem: `HardSphere/` (66 files) was *already* the
home of the mixture Baxter matrix `MatrixQ0`, `Q0DetRankTwo`, and the whole FMT cluster, so
"HardSphere = single-component" was simply not true. The scalar/mixture line is the same one
`MRS.0b`'s `n = 1` bridge just made precise (scalar proven, mixture axiomatized), so it is worth
making visible in the directory structure.

**Layering invariant** (now recorded in `CONVENTIONS.md` with copy-pasteable greps):
`Analysis/ ← HardSphere/ ← HSMixture/ ← YukawaDCF/`, imports pointing leftward only.

**Moved — 14 files into `HSMixture/`.**
* Baxter mixture core, from `HardSphere/` (6): `MatrixQ0` (with `etaMix`/`xi2`/`Q0phys`/`Qppphys`/
  `rhoGeoPhys`), `Q0Complex`, `Q0DetRankTwo`, `Q0DetLimit`, `MixtureNoSpinodal`,
  `MixtureNoSpinodalN1`.
* FMT mixture cluster, from `HardSphere/` (4): `WhiteBearFMT`, `CHSKink`, `CHSKinkWB`,
  `CHSFlatInner` — species-indexed and predicated on unlike radii `Ri ≠ Rj`. The cluster is fully
  self-contained (imports only each other; `CHSKinkWB`/`CHSFlatInner` have no external consumer), so
  it moves as a unit with zero back-edges.
* From `YukawaDCF/` (4): `MixtureHSZeros`, `MixtureHSPoles`, `MixtureChordFamily` (`MixParams`),
  `MixtureHSCounting` — none has any Yukawa content outside its copyright line.

**Also re-homed:** `SingleCompReduction` `YukawaDCF/ → HardSphere/` (entirely scalar signatures
`(S M z : ℝ)` despite the directory); `MatrixIdentity` `HardSphere/ → Analysis/` (abstract identity
over arbitrary `Matrix (Fin n) (Fin n) ℝ`, imports no LeanCode module).

**Namespaces needed no change** — `FMSA.MatrixQ0`, `FMSA.Q0Complex`, … encode content, not
directory (the content-descriptive naming convention), so a directory move is free.

⚠ **Classification-method lesson — the narrow grep lies.** The species-index binder is *not*
uniform across the library: `Fin n` (Baxter), `Fin N` (`WhiteBearFMT`), `Fin M` (`CHSKinkWB`).
Screening on `Fin n` alone reported "0 hits" for `CHSKinkWB` and **misfiled the entire FMT cluster as
scalar**; it surfaced only after re-sweeping with `Fin [A-Za-z]+ → (ℝ|ℂ)` plus the mixture-only
concept `Ri ≠ Rj`. Two further traps: `Mixture*` prefixes are unreliable in *both* directions
(`MixtureHSCounting` is abstract complex analysis; `SingleCompReduction` is scalar), and the
`Mix N M` structure is **not** pure HS — its `zp`/`cb` fields are Yukawa pole residues, which is why
`WHSupports`/`MixtureClosedForm`/`MixtureConvolution`/`MixtureDCFSmooth`/`InnerDecomp` all stayed
put. All recorded in `CONVENTIONS.md`.

**Deliberately NOT moved (blocked by a genuine back-edge, → the split task below):**
`MixtureLaurent` and `MixtureMLBound` import `MixturePolyCoeffs` / `MixtureMLSeries`, which do carry
real Yukawa content; moving them would create `HSMixture → YukawaDCF`. Likewise `MatrixN1` cannot go
to `Analysis/` while it imports `HardSphere/SingleCompIdentity`+`BaxterFactor`.

**Verified:** (1) `lake build` green at 8683 jobs, equal to baseline; (2) all three layering greps
empty; (3) the axiom ledger is **byte-identical** before/after — 8 axioms (7 math + 1 physics), the
physics one now under the `HSMixture` bucket; (4) `#print axioms pyhs_mixture_no_spinodal_n1` still
`[propext, Classical.choice, Quot.sound]`.

**Continued as `MRS.9b` (below):** split the three straddling files, general half leftward —
`MatrixN1` (4 abstract lemmas → `Analysis/`, `m2_identity_baxter` stays), `MixtureHSCounting`
(`DetBoundaryGrowth`/`infinite_zeros_of_growth`/`expTaylor2,3`/… → `Analysis/`), `MixtureLaurent`
(`taylor4_*` generic calculus → `Analysis/`). That also unblocks the two moves above.


#### MRS.9b — splitting the straddling files: general math moved into `Analysis/`

**✓ DONE 2026-07-19, build green (8688 jobs), no `sorry`, all four invariants re-verified.**
Directory counts `Analysis 18→23`, `HardSphere 56`, `HSMixture 14→15`, `YukawaDCF 23→22`.

Stage 2 of the `HSMixture/` reorganisation (`MRS.9a`): a file that straddles the layering boundary
is **split**, not filed by majority vote — the general half moves left, per Group MA admissibility
rule (c) and the `BanachPoleFamily` / `radialShell_bounded_injective` precedents.

**Five new `Analysis/` files, all imports = Mathlib only (except `BoundaryGrowth`).**

| new file | extracted from | contents |
|---|---|---|
| `MatrixFin1.lean` | `HardSphere/MatrixN1` | `1×1` matrix mul/inv = scalar mul/div; unconditional (`D = 0` ⇒ both sides `0`) |
| `ExpTaylorLimits.lean` | `HSMixture/MixtureHSCounting` | `remainder_div_tendsto_zero`, `expTaylor2/3`, `phi1/phi2_tendsto` — removable singularities at `s = 0` for arbitrary `σ ≠ 0` |
| `BoundaryGrowth.lean` | same | `DetBoundaryGrowth`, `detBoundaryGrowth_of_linear`, `infinite_zeros_of_growth`, `finset_sum_le_finsum_of_nonneg` — abstract `f : ℂ → ℂ` |
| `Taylor4Calculus.lean` | `YukawaDCF/MixtureLaurent` | the order-4 Taylor germ algebra: `taylor4_mul/sub/neg/recip`, `poly4_eq_zero_of_littleO`, `taylor4_coeff_unique` — arbitrary `f g : ℝ → ℝ` |
| `PoleSeriesSummable.lean` | `YukawaDCF/MixtureMLSeries` | `mixHSterm`, `mixHS_summable`, `mixHS_summable_of_growth` — arbitrary `Bcoef sfam : ℕ → ℂ` |

**A 4th split was needed and was not in the plan.** `MixtureMLBound` was blocked by
`MixtureMLSeries`, which I had classified as "genuinely Yukawa" from keyword counts. That was
right about the *file* (it defines `yukawaCoupling`, the Laplace-space propagator factor) but wrong
about the *dependency*: `MixtureMLBound` uses only `mixHSterm` / `mixHS_summable_of_growth`, both
fully abstract. Splitting those out unblocked it, and **`MixtureMLBound` is now in `HSMixture/`**.

**⚠ `MixtureLaurent` is still blocked — the plan's claim that stage 2 would unblock it was wrong.**
Its residual three theorems need `q0_entry_taylor3`, `p1_limit`, `p2_limit`, `p1/p2_cubic_coeff`,
`exp_neg_cubic_rem` from `MixturePolyCoeffs`, which imports `InnerOriginBC` + `ContactMatching`
(real Yukawa). Those six lemmas do **not** themselves touch the Yukawa imports, so a 5th split is
*feasible* — but `MixturePolyCoeffs` is 1300+ lines and currently carries ~390 lines of uncommitted
edits from another session, so it was left alone. Recorded as `MRS.9d`.

**Extraction-method notes** (all three hazards actually bit):
* Blocks were located by script (declaration + its preceding `/--` docstring) rather than by hand,
  and re-inserted verbatim — no proof was retyped.
* ⚠ The extractor matched `/--` but not `/-!`, so **section headers were orphaned**: `MixtureLaurent`
  kept a `/-! ### Well-definedness …` header whose theorem had moved. Check `^/-! ###` after any
  extraction.
* ⚠ The last block of a file swallows its `end Namespace` line. `MixtureLaurent` lost its `end` and
  **still built** — Lean auto-closes at EOF and only emits a `linter.style.missingEnd` warning.
  Green build ⇏ balanced namespaces; grep `^namespace` vs `^end ` counts.
* `open` does not propagate through `import`: every downstream consumer of a moved declaration needs
  its own `open` (`MixtureInnerDCF`, `MixtureMLBound` both did).

**Deliberate non-goal.** `PoleSeriesSummable`'s `mixHS*` names are historical and now live in
`Analysis/` despite the domain-flavoured prefix. Renaming them to content-descriptive names is a
follow-up (`MRS.9d`), deferred to keep this split's blast radius small while other sessions have
uncommitted work in the same files.


#### MRS.9c — species binder normalised to `N`

**✓ DONE 2026-07-19, build green (8683 jobs, unchanged), convention recorded in `CONVENTIONS.md`.**

Species count is now uniformly `N` (`sigma rho : Fin N → ℝ`). Renamed in 9 files — `n → N` in
`MatrixQ0`, `Q0Complex`, `Q0DetRankTwo`, `Q0DetLimit`, `MixtureNoSpinodal`, `MixtureHSZeros`,
`MixtureRealSpace`, `SpectralAmplitude`; `M → N` in `CHSKinkWB`. `WhiteBearFMT`, `BijReduction` and
the `Mix N M` structure already conformed. **Reserved:** `M` = Yukawa poles per residue expansion
(`Mix`'s `zp`/`cb` third index), bare `n` = anything unindexed (pole/branch number, iteration count,
chord index, Taylor order).

**The scope was 9 files, not the ~24 an initial `Fin _ → ℝ` sweep suggested.** ⚠ **`Fin _ → ℝ` does
NOT mean "species"** — it is equally the *Yukawa tail* index: `FMSAPoly/*`, `FreeEnergy/*`,
`ContactMatching`, `YukawaInnerCore`, `MixtureInnerDCF` all bind `(A z : Fin n → ℝ)` = tail
amplitudes and decay rates. Renaming those would have been actively wrong. The correct discriminator
is **what is indexed**: `sigma`/`rho`/`d` ⇒ species; `A`/`z`/`K`/`Amp` ⇒ tails. Caught by inspecting
`variable {n : ℕ} (A z : Fin n → ℝ)` lines before editing.

`CHSKinkWB`'s `M` was the one genuine defect: `M` means *pole count* in `Mix N M`, so the same letter
carried two meanings. Binder names are implicit, so this could never surface as an error — only a
reader would ever notice.

⚠ **Method lesson — `lake build` cannot validate a binder rename.** Renaming a bound variable is
alpha-equivalent: a *local* `n` (a `∀ n`, an `intro n`) wrongly swept into `N` compiles perfectly and
is silently wrong. Green build ⇏ correct rename. The actual verification was (i) per-declaration
scoping in the rewrite (only blocks matching `Fin n → (ℝ|ℂ)` or `Matrix (Fin n)`), (ii) a guard
skipping any block that already bound `N` (relevant: `MixtureHSZeros` uses `N` for a summation count
in *other* declarations), and (iii) a post-hoc grep of all 9 files for `∀ N`/`intro N`/`fun N`/
`induction N` — all empty, so no local was captured.


#### MRS.9d — split `MixturePolyCoeffs`, move `MixtureLaurent`, rename `mixHS*` (ex-`0f`)

**✓ DONE 2026-07-27, build green (8699 jobs), layering invariant re-verified, axiom ledger
byte-identical (pure reorg).**  The deferral blocker is gone — the other session's `MixturePolyCoeffs`
edits landed in commits `93f10f6`/`b3896eb`, so the tree is clean.

**⚠ The 2026-07-19 dependency list above was STALE — re-derived before acting** (per
`feedback_stale_blockers`).  The recorded back-edge was six lemmas; the *current* `MixtureLaurent`
needed **only `p1_limit` + `p2_limit`** from `MixturePolyCoeffs`.  The other four (`q0_entry_taylor3`,
`p1_cubic_coeff`, `p2_cubic_coeff`, `exp_neg_cubic_rem`) had dropped out of `MixtureLaurent`'s
dependency set — `q0_entry_taylor4` now uses the already-extracted `p1_quartic_coeff` /
`exp_neg_quartic_rem` (`Taylor4Calculus`), so only the two order-0 limits remained.  A `grep` of the
actual references, not the note, is what caught this.

**What was done.**
1. **Extracted to `Analysis/Taylor4Calculus.lean`** (namespace `FMSA.Taylor4`, its established home for
   the p1/p2 block-coefficient lemmas — `p1_quartic_coeff`/`exp_neg_quartic_rem` were already there):
   `p2_limit`, `p1_limit` (from `MixturePolyCoeffs`; `p1_limit` uses `p2_limit`, kept in that order)
   and `p2_quartic_coeff` (from `MixtureLaurent` itself — pure real-analysis, its only consumer was
   `q0_entry_taylor4` in the same file, so it left with the general lemmas rather than riding along to
   `HSMixture/`).  All three are `#print axioms = {std three}`.  Names kept (`p1`/`p2` is the
   file's existing convention, not a domain leak).  `MixturePolyCoeffs` now `import`s
   `Analysis/Taylor4Calculus` + `open FMSA.Taylor4` for its three internal `p1_limit`/`p2_limit`
   call sites; nothing else references them externally.
2. **Moved `MixtureLaurent` `YukawaDCF/ → HSMixture/`** (`git mv`, namespace `FMSA.MixtureLaurent`
   unchanged — content-descriptive).  Imports are now `Mathlib` + `Analysis.Taylor4Calculus` +
   `HSMixture.MatrixQ0` (the `q0_entry` it uses, previously pulled in transitively via
   `MixturePolyCoeffs`, now imported directly).  `p1_limit`/`p2_limit`/`p2_quartic_coeff` resolve via
   its existing `open FMSA.Taylor4`.  Its theorems (`q0_entry_taylor4`, `taylor4_inv_entry`) have no
   code consumers, so the move is a leaf relocation.  `LeanCode.lean` import path updated.
3. **Renamed the four generic `mixHS*` in `Analysis/PoleSeriesSummable`** to content-descriptive
   names (word-boundary `sed`, 70 occurrences across 7 files):
   `mixHSterm → poleExpTerm`, `mixHS_series → poleExpSeriesRe`,
   `mixHS_summable → poleExpTerm_summable_of_decay`,
   `mixHS_summable_of_growth → poleExpTerm_summable_of_growth`.
   **Scope = only the generics in `Analysis/`.**  The domain-layer *derived* objects
   (`mixHSterm2`, `mixHS_series2`, `mixHSAntideriv*`, `detF_mixHS_summable`) keep their `mixHS*`
   names — they are genuinely mixture-HS specific and live in `YukawaDCF/`/`HSMixture/`, where a
   domain prefix is correct.  ⚠ The rename must be `\b`-anchored: `mixHSterm` is a substring of the
   preserved `mixHSterm2` (digit-suffixed) and `detF_mixHS_summable` / `…_eq_mixHSterm` (`_`-prefixed);
   the word boundary protects all of them, verified by before/after counts
   (`mixHSterm2` 34→34, `detF_mixHS_summable` 8→8).
4. **Re-verified the layering invariant** (`MRS.9a`'s three greps): `Analysis/ ⊬ higher`,
   `HardSphere/ ⊬ {HSMixture,YukawaDCF}`, **`HSMixture/ ⊬ YukawaDCF`** — all empty.  Directory counts
   now `Analysis 27, HardSphere 59, HSMixture 17, YukawaDCF 24`.

**MRS.9 (`9a`–`9d`) is now COMPLETE.**  Follow-up (2026-07-27): the order-3 p1/p2 lemmas
(`p1_cubic_coeff`, `p2_cubic_coeff`, `exp_neg_cubic_rem`) — verified genuinely physics-independent
(they take only `(σ : ℝ)`/`(λ : ℝ)` and prove via `Real.exp_bound`; NO `q0_entry`/`MatrixQ0`/Yukawa
in the *code*, only in motivating prose) — were **also moved to `Analysis/Taylor4Calculus.lean`**,
completing the p1/p2/exp Baxter-block Taylor family there (orders 0, 3, 4 now all in `Analysis/`).
Their sole consumers were `MixturePolyCoeffs`-internal (`q0_entry_taylor3`), which resolve via the
`open FMSA.Taylor4` already added in `MRS.9d`; verbose GAP.9/`D_ij` docstrings trimmed to the
domain-neutral house style.  Build green 8699, all three `#print axioms = {std three}`.  ⚠ A crude
"references a domain object?" grep suggests a few remaining `p1_num*`/`p2_num*` numerator-derivative
helpers *may* also be general, but the classifier split sibling lemmas inconsistently, so migrating
those needs per-lemma reading and is left as a genuinely-optional future pass — not started.


**GENERAL-`N` — UNCONDITIONAL (2026-07-29, `MixtureDetGeneralN.lean`).**  The `N=2`
`mixtureDet_pole_free` generalises to arbitrary `N`, `mixtureDet_pole_free_N` : `det Q̂₀(I·z) ≠ 0`
on the open lower half `z`-plane for every physical `N`-component mixture, **fully unconditional**,
`#print axioms` = the same two existing axioms (`zeroFree_lowerHalfPlane_of_homotopy`,
`pyhs_mixture_no_spinodal`) — no new axiom.  Route: the already-`N`-general framework
`matDet_zeroFree_lowerHalfPlane_of_homotopy` applied to the entire `ψ`-matrix `Mdens` (physical `Q̂₀`
with each `φ = num/sⁿ` replaced by its entire removable extension `ψ`, so every entry is entire
(`hholo`, `Mdens_hholo`) and jointly continuous (`hcont`, `Mdens_hcont`)).  `hbase` = dilute `Mdens 0
= I`.  `hreal` = `k≠0` no-spinodal (`{N}`) + `k=0` compressibility `detMdens_origin_ne_zero`
(axiom-clean, `det ≥ 1` via `Q0_mat_phys_det_ge_one_N` = rank-2 reduction + `moment_key`, which is
`{N}`).

**The escape `hbound` (the crux `N`-general obstacle) — SOLVED cleanly via a diagonal similarity.**
Individual `Q̂₀` entries blow up as `Re s → ∞` (`e^{−λ_{ij}s}`, `λ_{ij}<0`), but the phase
`e^{−λ_{ij}s} = e^{σᵢs/2}·e^{−σⱼs/2}` **is** a diagonal similarity `D(·)D⁻¹`, so
`det Q̂₀ = det Mgauge` (`det_Q0_eq_det_gauge`, via `det_mul` + `det_diagonal`, `∏e^{σᵢs/2}·∏e^{−σⱼs/2}
= e^0 = 1`) where `Mgauge` has the phase stripped (`lam=0`, entries bounded).  Then `Mgauge = 1 − A`,
`‖A‖_{L∞ op} ≤ Abnd/‖s‖ → 0` (kernel bounds `‖φ₁‖ ≤ (2+σ)/‖s‖`, `‖φ₂‖ ≤ (2+σ+σ²/2)/‖s‖` from
`‖e^{−sσ}‖ = e^{−σ Re s} ≤ 1`; `linfty_opNorm_le_row`), uniformly in `t` (`Abnd_cont` + compact
`[0,1]`), so `1 − A = Mgauge` is a unit (`isUnit_one_sub_of_norm_lt_one`) and `det ≠ 0` for `‖s‖ ≥ R`
(`exists_uniform_escape`, axiom-clean).  This is **cleaner than the `N=2` monomial bridge** and needed
no complex VU factorisation.  **`OZFIX.17` matrix pole↔decay is now RESOLVED for ALL `N`.**
