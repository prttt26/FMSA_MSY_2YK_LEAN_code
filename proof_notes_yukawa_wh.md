# Proof Notes: First-Order Yukawa RDF via Wiener–Hopf (Group Y1)

Proof records for **Group Y1** — the analytical first-order (order-ε¹) Yukawa RDF/DCF derivation of
Tang & Lu (1995), formalized from the **[LN]** lecture notes
(`pdf/lecture_notes_OZ_Yukawa_poly.pdf`, §5–§6, §8–§9).

**Scope — the Wiener–Hopf RDF foundation.** This file hosts **Group Y1** only: the first-order
Wiener–Hopf derivation producing the spectral amplitude `b_{ij}(s)` (Eq. 73) and the first-order RDF
`Ĥ₁ = [Q̂₀ᵀ]⁻¹ B₁ [Q̂₀]⁻¹` (Eq. 68). It is the general (mono- and multi-component) foundation reused
by both mixture inner-core lines.

**The N=2 mixture inner-core groups moved out.** The `Q̂₀⁻¹`-factor count is the dividing line:
**none ⇒ DCF; two ⇒ RDF `h₁`.**
- **RDF `h₁`** (two inverses): Groups **MML** (Mittag-Leffler HS-pole series) and **MZERO**
  (`det(Q̂₀)` zero / HS-pole family) are in
  [proof_notes_mixture_rdf.md](proof_notes_mixture_rdf.md) (split out 2026-07-17).
- **DCF** (no inverse, finite closed form): Groups **MRS** (real-space Baxter route) and **MPOLY**
  (inner-core polynomial coefficients) are in
  [proof_notes_mixture_dcf.md](proof_notes_mixture_dcf.md) (split out 2026-07-17).
The convergence-radius corollary (former Y2.16) is Group **GA.4** in `proof_notes_failures.md`.

**Relation to Group BAXTER.** Group BAXTER handled the *zeroth-order* hard-sphere route
(Baxter/Wiener–Hopf factorization → PY closed form). Group Y1 is the **first-order Yukawa analog**:
the same **algebraic** Wiener–Hopf machinery (causal/anti-causal split + support statements +
residues — *not* the Hilbert transform of [LN] §6.3, which Mathlib lacks; see Y1.3) applied to the
first-order OZ equation `H̃₁(I − C̃₀) = (I + H̃₀)C̃₁` ([LN] Eq. 7), producing the spectral amplitude
`b_{ij}(s)` (Eq. 73) and the first-order RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹ B₁ [Q̂₀]⁻¹` (Eq. 68). Split off from
`proof_notes_yukawa_dcf.md` (2026-07-15) since it is a Group-BAXTER-scale body of work, not a
Group-C "consistency check".

**Status (2026-07-15).** The task chain Y1.1–Y1.7 is **fully proved** (all axiom-clean), including the
Y1.5 general distinct-`z` multi-tail residue. Y1.3 was re-routed off [LN]'s Hilbert-transform
presentation to the codebase's algebraic real-space method (support + residues). **Group Y1 is
complete.**

## Already-proved pieces (reused across Y1)

- `FMSA.YukawaPoleResidue.g_entry_eq_adj_div_det` (`YukawaDCF/YukawaPoleResidue.lean`) —
  `[Q̂₀⁻¹]_{ij} = adj(Q̂₀)_{ij}/det Q̂₀` (Mathlib `Matrix.inv_def`); the `G_{ij} = adj/det` core of Y1.1.
- `FMSA.YukawaPoleResidue.c5_residue_eq_K_mul_Ginv` — residue assembly conditional on the Blum
  simple-pole shape (the C.5 conditional core; feeds Y1.6).
- `FMSA.SpectralAmplitude.spectralAmp_residue` / `spectralAmp_residue_n1`
  (`YukawaDCF/SpectralAmplitude.lean`) — the **single-tail** exact residue
  `Res_{s=−z} b_{ij}(s) = [Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` (Y1.5, single-tail case) and the `N=1` `K·G²` form
  (the correction to the numerical `K·G` shorthand).
- `FMSA.HardSphere.residue_of_simple_pole` (`HardSphere/BaxterResidue.lean`) — general
  `(z−z₀)·N/D → N(z₀)/D'(z₀)` simple-pole residue (reused in Y1.4).

## Task chain

Task IDs are group-local `Y1.*`. Statuses: ☐ not started · ◑ partial · ✓ done.

---

### Task Y1.1 — Complex Baxter matrix `Q̂₀(s)` and its inverse

**Statement.** Define the Laplace-space Baxter factor matrix `Q̂₀(s) : ℂ → Matrix (Fin n) (Fin n) ℂ`
([LN] Eq. 10, `s = −ik`):
```
{Q̂₀(s)}_{ij} = δ_{ij} − (ρ_iρ_j)^{1/2} · e^{−sλ_{ij}} · [ φ₁(R_i) Q'_{ij} + φ₂(R_i) Q''_j ],
```
with `φ₁, φ₂` (Eq. 13), `Q'_{ij}, Q''_j` (Eq. 11), `ξ_n, Δ` (Eq. 12), `λ_{ij} = (R_j − R_i)/2`;
and prove the inverse-entry identity ([LN] Eq. 14/17/70)
```
{Q̂₀(s)⁻¹}_{ij} = δ_{ij} + A_{ij}(s) · e^{−sλ_{ij}},   A_{ij}(t) = 2π(ρ_iρ_j)^{1/2} W_{ij}(t)/(Δ det(t)),
```
with `W_{ij}` (Eq. 15), `det` (Eq. 16). Complex extension of the real `Q0_mat` (`MatrixQ0.lean`).

**Lean (`HSMixture/Q0Complex.lean`).** `q0_entry_c` / `Q0_mat_c` — complexification of the real
`FMSA.MatrixQ0.q0_entry` / `Q0_mat`; `q0_entry_c_real` — consistency at real `s` (`push_cast`);
`inv_apply_eq_adj_div_det` — `[Q̂₀(s)⁻¹]_{ij} = adj/det` (local restatement of `Matrix.inv_def`, kept
self-contained to avoid the transitively-broken `BaxterResidue` import).
**Depends on.** M.10 (real `Q0_mat` structure), M.3/M.4 (`det ≠ 0`).
**Status.** ✓ DONE (2026-07-15), axiom-clean. *Deferred:* the closed-form inverse [LN] Eq. 14
(`W/det`); `adj/det` is the usable form for the residue chain.

---

### Task Y1.2 — Outer MSA DCF Laplace transform + Yukawa pole

**Statement ([LN] Eq. 34/46).** For the single-tail MSA closure `c^{(1)}_{ij}(r) = βR_{ij}ε_{ij}
e^{−z_{ij}(r−R_{ij})}/r` (`r > R_{ij}`), the outside-core Fourier/Laplace transform is
```
{U₁(k)}_{ij} = 2π(ρ_iρ_j)^{1/2} ∫_{R_{ij}}^∞ r · c^{(1)}_{ij}(r) · e^{−ikr} dr
            = K_{ij} · e^{−ikR_{ij}} / (ik + z_{ij}),   K_{ij} = 2π(ρ_iρ_j)^{1/2} R_{ij} β ε_{ij}  (Eq. 36),
```
a simple pole at `k = i z_{ij}` (upper half-plane), i.e. `s = z_{ij}`.

**Lean (`YukawaDCF/OuterDCF.lean`).** `integral_Ioi_cexp` — `∫_{Ioi R} e^{c·r} = −e^{c·R}/c` for
`Re c < 0` (FTC via `integral_Ioi_of_hasDerivAt_of_tendsto`; integrability via `integrableOn_exp_mul_Ioi`
+ `Integrable.mono'`, decay via `Real.tendsto_exp_atBot`); `outerDCF_transform` — Eq. 46
`∫_{Ioi R} A e^{−z(r−R)} e^{−ikr} = A e^{−ikR}/(ik+z)` (`z>0`), the `U₁` form with pole at `ik=−z`.
**Depends on.** Group 1 flavour (integral lemmas); the `K`/`√(ρρ)` prefactor is external data.
**Status.** ✓ DONE (2026-07-15), axiom-clean.

---

### Task Y1.3 — Wiener–Hopf one-sided projection isolating `B₁ = {T_U}^{[R,∞)}`

**Goal.** Isolate the causal part `B₁ = Q̂₀ᵀ Ĥ₁ Q̂₀ = {T_U}^{[R,∞)}` (Eq. 62) of
`T_U(k) = [Q̂₀(−k)]⁻¹ U₁(k) [Q̂₀ᵀ(−k)]⁻¹` — the step that *derives* `b_{ij}` (Eq. 73) from the
first-order OZ equation.

**Re-routed off the Hilbert transform.** [LN] §6.3 states the split via the Hilbert transform /
Cauchy P.V. / Sokhotski–Plemelj (Eq. 47–51). **Do not follow that literally**: Mathlib has no
Hilbert-transform / P.V.-integral / distributional-FT support, and the codebase deliberately avoids
it — Group 3 `HardSphere/Splitting.lean` already does the WH split algebraically
(`yukawa_kernel_split`, `1/(ik+z)+1/(−ik+z)=2z/(z²+k²)` via `Complex.I_sq`) + indicator→FT-support
lemmas, and Group BAXTER did the zeroth-order split via Baxter factorization + residue series. The
two routes give the same `B₁`; only the tooling differs. So Y1.3 = **algebraic split + support
statements + residues**, mirroring `Splitting.lean` / Group BAXTER.

**Decomposition.** all three sub-tasks now done (real-space route).
- **Y1.3a — support statements** (§6.3.2, [LN] Eq. 55–57): the atomic real-space supports (Baxter
  factor on `[λ_{ij}, R_{ij}]`; `h^{(1)}` on `[R,∞)`; `S₁` on `[0,R]`) + the half-line ⇄ full-line
  transform bridges. ✓ DONE — see below.
- **Y1.3b — support-orthogonality projection** (Eq. 61–62): matching the `[R,∞)` parts ⇒
  `L = {T_U}^{[R,∞)}`. **Key reframing:** done in *real space*, where the `{·}^{[R,∞)}` projection is
  just multiplication by `1_{[R,∞)}` — so the support-orthogonality is *elementary* (`Set.indicator`),
  and the "FT injectivity" difficulty (an artifact of [LN]'s k-space Hilbert-transform presentation)
  **disappears**: no FT-inversion of the distributional Baxter factors is needed. ✓ DONE — see below.
- **Y1.3c — causal projection = residue extraction** (Eq. 63–66): the Yukawa-pole residue of
  `T_U = [Q̂₀(−k)]⁻¹ U₁ [Q̂₀ᵀ(−k)]⁻¹` is the conjugated `U₁`-residue `[G·K·Gᵀ]` = `Res b_{ij}` (Y1.5).
  Via the `s`-dependent-factor `matrix_conj_residue_analytic`. ✓ DONE — see below.

**Depends on.** Y1.1, Y1.2 (both done); reuses `FMSA.WienerHopf.{yukawa_kernel_split,
innerCoreFun, innerCore_support_subset_Iic, T_S_eq_fourier_of_innerCore}` (`Splitting.lean`),
`FMSA.HardSphere.{q0_poly, q0_poly_outer, phi1_real, phi2_real}` (`BaxterRealSpace.lean`), the
`FMSA.InnerDecomp.Mix` real-space data (`R`, `lam`, `mediated`, `terms_II_III_zero`), and
`residue_of_simple_pole` + this session's `matrix_conj_residue`.

**Y1.3a — DONE (axiom-clean), `LeanCode/YukawaDCF/WHSupports.lean` (namespace `FMSA.WHSupports`).**
- `q0_poly_support_subset` — repackages `q0_poly_outer` as `Function.support (q0_poly …) ⊆ Set.Iic σ`
  (the monodisperse Baxter-factor support anchor).
- `q0MixEntry` / `q0MixEntry_support_subset` — the mixture real-space Baxter entry `{Q̂₀(r)}_{ij}`
  ([LN] Eq. 10), the Baxter polynomial windowed on the core (from `Mix` data `R`/`lam`/`Q0`/`Qpp`),
  with `Function.support ⊆ Set.Icc (X.lam i j) (X.R i j)` ([LN] Eq. 56, via `indicator_of_notMem`).
- `integral_Iic_eq_of_support` / `integral_Ici_eq_of_support` — reusable core: a half-line-supported
  function integrates the same over that half-line as over `ℝ` (via `integral_indicator` +
  `Set.indicator_eq_self`).
- `fourier_Iic_eq_full` (anti-causal, inner `S₁`) / `fourier_Ici_eq_full` (causal, outer `h^{(1)}`) —
  the `Set.Iic`/`Set.Ici` Fourier analogues of `Splitting.lean`'s `[0,R]` `T_S_eq_fourier_of_innerCore`.

**Y1.3c — DONE (axiom-clean), `LeanCode/YukawaDCF/YukawaCausalResidue.lean` (namespace `FMSA.YukawaWH`).**
Support lemma `matrix_conj_residue_analytic` (in `YukawaWienerHopf.lean`) generalizes
`matrix_conj_residue` to `s`-dependent conjugating factors analytic at the pole (`Lf → Lval`,
`Rf → Rval`), so the inverse-Baxter factors of `T_U` enter only via their pole-values.
- `U1mat` / `U1mat_residue` — the single-tail outer matrix `U₁(s)_{ij} = K_{ij}/(s+z)` has entrywise
  Yukawa-pole residue `K` (reuses `SpectralAmplitude.simplePole_residue`).
- `outer_residue` — `Res_{s=−z}[Lf·U₁·Rf]_{ij} = [Lval·K·Rval]_{ij}`.
- `outer_residue_eq_spectralAmp_residue` — with `Lf → G = Q̂₀(z)⁻¹`, `Rf → Gᵀ`, the residue is the
  doubly-propagated `[G·K·Gᵀ]_{ij}`, **identical to** `spectralAmp_residue`: `Res T_U = Res b_{ij}`.

**Y1.3b — DONE (axiom-clean), `LeanCode/YukawaDCF/YukawaCausalProjection.lean` (namespace `FMSA.YukawaWH`).**
The support-orthogonality projection, done in **real space** (where `{·}^{[R,∞)}` = `1_{[R,∞)}·`), so
the [LN] Hilbert-transform / FT-injectivity machinery is unnecessary.
- `causal_projection_real` — from the OZ split `L = T_U + T_S` with `support L ⊆ [R,∞)`,
  `support T_S ⊆ (−∞,R)`, conclude `L = 1_{[R,∞)}·T_U` (`= {T_U}^{[R,∞)}`). Elementary `Set.indicator`
  case split. `hOZ` (OZ equation) + the two supports are the physical / Y1.3a inputs.
- `causal_projection_fourier` — its Fourier form `L̂(k) = ∫_{[R,∞)} T_U(r) e^{−ikr} dr = {T̂_U}^{[R,∞)}`,
  i.e. the `B₁ = {T_U}^{[R,∞)}` statement. Combined with Y1.3c's residue this closes the WH derivation.

**Status.** ✓ Y1.3a + Y1.3b + Y1.3c all DONE (axiom-clean, real-space route). Remaining physics inputs
(that the concrete `L`/`T_S` meet the support hypotheses; the OZ equation) are Y1.3a + standard, not
gaps in the derivation logic.

---

### Task Y1.4 — Residue evaluation of the WH projection → `B₁(k)`

**Statement ([LN] §6.4.1, Eq. 63–67).** Closing the contour in the upper half-plane, the only poles
are the Yukawa denominators `1/(iy + z_{mn})` at `y = i z_{mn}`; the residue theorem gives
```
B₁(k) = −E(k) [ Res_{y=iz_{mn}} {E(−y)[Q̂₀(−y)]⁻¹U₁(y)[Q̂₀ᵀ(−y)]⁻¹E(−y)}_{ij} / (y−k) ] E(k)   (Eq. 67),
```
with `{B₁(k)}_{ij} = b_{ij}(ik) e^{−ikR_{ij}}` (Eq. 66).

**Lean (`YukawaDCF/YukawaWienerHopf.lean`).** `triple_apply` — `(L·X·R)_{ij}` as a double sum;
`matrix_conj_residue` — **the residue-theorem step in matrix form**: if every entry of `bfun` has
residue `Bres` at `s₀`, then `L·bfun·R` has residue `L·Bres·R` (entrywise `Tendsto` pushed through
the two constant matrix factors). Self-contained (local, not importing the broken `BaxterResidue`).
**Depends on.** Y1.2 (`U₁` poles), Y1.1 (`[Q̂₀⁻¹]`). Y1.3 (the WH projection producing the Eq. 63
integrand) is **deferred** — `matrix_conj_residue` takes the projected form as its input.
**Status.** ◑ residue-theorem step DONE (2026-07-15), axiom-clean (`matrix_conj_residue`); the full
Y1.3-dependent derivation of the Eq. 63 integrand from the OZ equation remains open.

---

### Task Y1.5 — Spectral amplitude `b_{ij}(s)` (four-term / multi-tail)

**Statement ([LN] Eq. 73).** In Laplace variable `s = −ik`,
```
b_{ij}(s) = K_{ij}/(s+z_{ij}) + Σ_n K_{in}A_{jn}(z_{in})/(s+z_{in}) + Σ_m K_{mj}A_{im}(z_{mj})/(s+z_{mj})
            + Σ_{m,n} K_{mn}A_{im}(z_{mn})A_{jn}(z_{mn})/(s+z_{mn}),
```
with `A` evaluated at the fixed pole positions (Eq. 70). Its Yukawa-pole residues carry the
hard-sphere propagators; for a **single common tail** `b_{ij}(s) = [(I+A)K(I+A)ᵀ]_{ij}/(s+z) =
[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}/(s+z)`.

**Lean (`YukawaDCF/SpectralAmplitude.lean`).** `spectralAmp_residue` / `_n1` (single-tail exact
residue `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}`, the "`K·G` is a leading-order approximation" correction); `bMulti` —
the multi-tail `Σ_{m,n}(I+A)_{im}K_{mn}(I+A)_{jn}/(s+z_{mn})` form (= Eq. 73's four terms);
`simplePole_residue` — `Res_{s=−z}[c/(s+z)] = c`; `bMulti_single_eq` — common-`z` collapse to
`spectralAmp` (`(I+A)K(I+A)ᵀ`); `bMulti_single_residue` — its exact residue.
**General distinct-`z` residue — DONE (2026-07-15), axiom-clean.**
- `simplePole_offResidue` — an off-pole summand `c/(s+w)` (`w ≠ z₀`) has residue `0` at `s = −z₀`
  (the `(s+z₀)` factor kills the finite `c/(w−z₀)`).
- `bMulti_residue` — `Res_{s=−z₀} bMulti = Σ_{m,p} [z_{mp}=z₀] (1+A)_{im}K_{mp}(1+A)_{jp}` (per-pole
  term matching: on-pole terms via `simplePole_residue`, off-pole via `simplePole_offResidue`).
- `one_add_sub_one` + `bMulti_residue_Qinv` — tie `A` to `Q̂₀⁻¹` ([LN] Eq. 70, `I+A = Q̂₀⁻¹` via
  Y1.1): the residue is `Σ_{(m,p): z_{mp}=z₀} [Q̂₀⁻¹]_{im} K_{mp} [Q̂₀⁻¹]_{jp}` (multi-tail form of the
  single-tail `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]`).
**Status.** ✓ DONE (2026-07-15), axiom-clean — single-tail, single-tail collapse, and general
distinct-`z` residue all proved.

---

### Task Y1.6 — First-order RDF `Ĥ₁` and the C.5 residue corollary

**Statement ([LN] Eq. 68).** `Ĥ₁(k) = [Q̂₀ᵀ(k)]⁻¹ B₁(k) [Q̂₀(k)]⁻¹`, from `Q̂₀ᵀĤ₁Q̂₀ = B₁`
(Eq. 62/69). Corollary: the Yukawa-pole residue of the first-order amplitude, expressed through
`Q̂₀⁻¹` — the exact form of the C.5 claim (`Q̂₀⁻¹·K·Q̂₀⁻ᵀ`, not `K·G`).

**Lean (`YukawaDCF/YukawaWienerHopf.lean`).** `Hhat1` — the def `[Q̂₀ᵀ]⁻¹·B·[Q̂₀]⁻¹`; `Hhat1_spec` —
Eq. 68 ⟺ 69 (`Q̂₀ᵀ·Ĥ₁·Q̂₀ = B` for invertible `Q̂₀`, via `Matrix.mul_nonsing_inv`/`nonsing_inv_mul`
+ `det_transpose`); `Hhat1_residue` — `Res Ĥ₁ = [Q̂₀ᵀ]⁻¹·(Res B₁)·[Q̂₀]⁻¹` (via `matrix_conj_residue`).
Combined with Y1.5's `bMulti_single_residue` (`Res B₁ = [Q̂₀⁻¹·K·Q̂₀⁻ᵀ]`) this is the **exact** [LN]
first-order-RDF residue — no `K·G` simplification.
**Depends on.** Y1.4 (`matrix_conj_residue`), Y1.5 (`B₁` residue), Y1.1 (`Q̂₀⁻¹`).
**Status.** ✓ DONE (2026-07-15), axiom-clean (`Hhat1`, `Hhat1_spec`, `Hhat1_residue`).

---

### Task Y1.7 — inner-core `S₁(k)`, origin constraint, contact matching (Group Y1 capstone)

**Statement ([LN] §9, §7).** `b₁ = U₁ + S₁` (Eq. 43); the inside-core contribution
`{S₁(k)}_{ij} = 2π√(ρρ) ∫₀^{R} r c_{ij}(r) e^{−ikr} dr` (Eq. 45), which §9 (*"…Inside the Hard Core:
r < R_{ij}"*) shows is anti-causal (Proof 2: supported on `(−∞,R_{ij}]`); the origin constraint
`A_{ij} = −Σ_n 𝓔_n(0)` (Eq. 76); and contact matching at `r = R_{ij}` (§7).

**Key realization.** This is a **capstone that reuses existing infrastructure**, not new analysis: the
anti-causal drop-out *is* Y1.3b (`causal_projection_fourier`) for the concrete inner core; Eq. 76 *is*
the P.2 origin-regularity condition + `eij_at_origin`; §7 matching *is* Group 5.1.

**Lean (`YukawaDCF/YukawaInnerCore.lean`, namespace `FMSA.YukawaWH`).** ✓ DONE, axiom-clean.
- `innerS1` / `innerS1_support_subset_Iio` — the inside-core amplitude `r c_{ij}(r)` on the strict
  core `[0,R)` (Eq. 45) and Proof 2 (`support ⊆ Set.Iio R`, anti-causal).
- `b1_causal_eq_U1_fourier` — [LN] §9.3: from `b₁ = U₁ + S₁` (Eq. 43) with `b₁` causal
  (`support ⊆ [R,∞)`), `∫ b₁ e^{−ikr} = ∫_{[R,∞)} U₁ e^{−ikr}` (`= {U₁}^{[R,∞)} = B₁`, Eq. 62). One
  line: instantiates Y1.3b's `causal_projection_fourier` with `T_S = innerS1`.
- `origin_constraint_eq76` — [LN] Eq. 76: origin regularity forces
  `P_{ij}(0) = −Σ_k A_k e^{−z_k R} = −𝓔_{ij}(0)` (reuses `FMSA.OriginConstraint.origin_necessity` +
  `FMSA.EijStructure.eij_at_origin`).
- `innerS1_contact_value` — §7 contact: inner-core `𝓔_{ij}(R) = Σ_k A_k` (via
  `FMSA.EijStructure.eij_at_contact`); full inner/outer continuity is Group 5.1
  (`FMSA.Contact.soft_core_contact_limit`), modulo the external MSA closure `K ↔ A`.

**Depends on.** Y1.3b (`causal_projection_fourier`); Groups 5.1 (`eij_at_contact`,
`soft_core_contact_limit`), P.2 (`origin_necessity`/`origin_finiteness`), P.1 (`eij`,
`eij_at_origin`).
**Status.** ✓ DONE (2026-07-15), axiom-clean. **Group Y1 complete** (Y1.1–Y1.7 all proved, including
the Y1.5 distinct-`z` multi-tail residue; the N=2 mixture groups MML/MZERO/MPOLY remain, below).
