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
**Status.** ✅ CLOSED (2026-07-17), axiom-clean — abstract + reduction + growth-witness
(2026-07-16) + concrete magnitude gate + end-to-end `Summable` (2026-07-17). Only cosmetic
bookkeeping (`Bcoef = b_k_residue` identification in the DCF assembly) remains.

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

---

## Group MZERO — Mixture `det(Q̂₀)` Zero Family (HS-pole existence)

**Scope.** `det(Q̂₀(s))` has **infinitely many** complex zeros `s_k` (the "HS poles" whose
residues feed MML.4/MML.8's Mittag-Leffler series). **MZERO.1** is the foundational statement;
**MZERO.2–MZERO.11** decompose it across two independent routes (Banach contraction / Jensen
zero-counting), either of which alone closes MZERO.1. The route overview precedes the numbered
tasks below.

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

*(Route B, Lean, `MixtureHSCounting.lean`.)* ✓ **DONE** as the input hypothesis `DetBoundaryGrowth f`
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

*(Route B, Lean, `MixtureHSCounting.lean`.)* ✓ **structural capstone DONE** (`infinite_zeros_of_growth`: a
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

### Task MRS.0c — `LeanCode/HSMixture/` — the N-component hard-sphere layer

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

**Follow-up (`MRS.0d`, not done):** split the three straddling files, general half leftward —
`MatrixN1` (4 abstract lemmas → `Analysis/`, `m2_identity_baxter` stays), `MixtureHSCounting`
(`DetBoundaryGrowth`/`infinite_zeros_of_growth`/`expTaylor2,3`/… → `Analysis/`), `MixtureLaurent`
(`taylor4_*` generic calculus → `Analysis/`). That also unblocks the two moves above.

### Task MRS.0e — species binder normalised to `N`

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

### Task MRS.0d — splitting the straddling files: general math moved into `Analysis/`

**✓ DONE 2026-07-19, build green (8688 jobs), no `sorry`, all four invariants re-verified.**
Directory counts `Analysis 18→23`, `HardSphere 56`, `HSMixture 14→15`, `YukawaDCF 23→22`.

Stage 2 of the `HSMixture/` reorganisation (`MRS.0c`): a file that straddles the layering boundary
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
edits from another session, so it was left alone. Recorded as `MRS.0f`.

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
follow-up (`MRS.0f`), deferred to keep this split's blast radius small while other sessions have
uncommitted work in the same files.
