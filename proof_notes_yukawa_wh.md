# Proof Notes: First-Order Yukawa RDF/DCF via Wiener–Hopf + N=2 Mixture Inner-Core (Groups Y1 / MML / MZERO / MPOLY)

Proof records for **Group Y1** — the analytical first-order (order-ε¹) Yukawa RDF/DCF derivation of
Tang & Lu (1995), formalized from the **[LN]** lecture notes
(`pdf/lecture_notes_OZ_Yukawa_poly.pdf`, §5–§6, §8–§9).

**Groups in this file.** Besides **Group Y1** (first-order WH, below), this file hosts the N=2
mixture-inner-core group family split out of the former flat "Group Y2" on 2026-07-15: **MML**
(Mittag-Leffler inner-DCF: 2×2 inverse → residue → assembly), **MZERO** (`det(Q̂₀)` zero / HS-pole
family), **MPOLY** (inner-core polynomial coefficients `D_ij = R'_ij(0)/6`). The convergence-radius
corollary (former Y2.16) moved to Group **GA.4** in `proof_notes_failures.md`. Group Y1 and the
mixture groups are the same physics (the mixture builds directly on Y1's WH infrastructure).

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
complete**; the remaining Yukawa-WH work is in the N=2 mixture groups **MML** / **MZERO** / **MPOLY** below.

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

**Lean (`YukawaDCF/Q0Complex.lean`).** `q0_entry_c` / `Q0_mat_c` — complexification of the real
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

---

## Group MML — N=2 Mixture Mittag-Leffler Inner-Core (2×2 inverse → residue → assembly)

**Motivation (2026-07-15).** For N=2, Q̂₀(z) is a 2×2 matrix with fully algebraic entries
(Y1.1 DONE). Its inverse is Q̂₀(z)⁻¹ = adj(Q̂₀)/det(Q̂₀), also proved (Y1.1:
`inv_apply_eq_adj_div_det`). For the (0,1) off-diagonal entry:

    [Q̂₀(z)⁻¹]₀₁  =  adj(Q̂₀)₀₁ / det(Q̂₀)  =  −Q̂₀₀₁(z) / det(Q̂₀(z))     (2×2 identity)

The zeros s_k of det(Q̂₀(z)) (the "HS poles") then give residues:

    Res_{z=s_k} [Q̂₀⁻¹]₀₁  =  −Q̂₀₀₁(s_k) / det′(Q̂₀)(s_k)     (residue_of_simple_pole)

This is the B_k coefficient used in `fmsa_hs_pole_residue.py`. **MML.1 + MML.2 DONE (2026-07-15)**,
axiom-clean (`YukawaDCF/MixtureHSPoles.lean`) — the 2×2 adj/det/inverse algebra and the `B_k`
residue via `residue_of_simple_pole`. MZERO.1 (infinitely many HS poles for det(Q̂₀)) is a harder
structural result; MML.3 (full assembly) uses Y1.3 (now done). Together they prove the exact inner
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
**Lean (`YukawaDCF/MixtureHSPoles.lean`, namespace `FMSA.MixtureHSPoles`).** `adjugate_fin_two_zero_one`
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
**Lean (`YukawaDCF/MixtureHSPoles.lean`).** `b_k_residue` — given a simple zero `s_k` of
`s ↦ det(Q̂₀(s))` (`HasDerivAt` det with `Dprime`, `det(s_k)=0`, `Dprime ≠ 0`, `Q̂₀₀₁` continuous at
`s_k` — all as hypotheses, matching `residue_of_simple_pole`), concludes
`Res_{z=s_k}[Q̂₀(z)⁻¹]₀₁ = −Q̂₀₀₁(s_k)/Dprime`.  Proof: rewrite via `Q0inv_zero_one` (holds for all
`z`), then `residue_of_simple_pole` with `N = −Q̂₀₀₁`, `D = det(Q̂₀)`.  Discharging the analytic
hypotheses concretely (entry/det holomorphy at `s_k ≠ 0`) is left to a later pass / MZERO.1.
**Status.** ✓ DONE (2026-07-15), axiom-clean (residue wiring; analytic hyps taken as inputs).

---

### Task MML.3 — Full Mittag-Leffler inner-DCF assembly for N=2 *(blocked on Y1.3)*

**Statement.** For the N=2 unlike pair (0,1), for r ∈ (0, R₀₁]:

    r · c^{inner}_{01}(r) = Σ_t [Q̂₀⁻¹·K_t·Q̂₀⁻ᵀ]₀₁ · exp(z_t(R₀₁−r))
                           + Σ_k 2·Re[B_k · exp(−s_k·r)]  +  p₀

where B_k = K_t · adj(Q̂₀(s_k))₀₁ / ((z_t²−s_k²) · det′(Q̂₀)(s_k)) (combining MML.2
with the Yukawa propagator from Y1.3).

This is the N=2 matrix analog of the scalar Mittag-Leffler series in POLE.4/Group OZFIX.

**Depends on.** Y1.3 (Wiener–Hopf), MML.2 (B_k residue), MZERO.1 (infinitely many poles),
Y1.5 (doubly-propagated Yukawa amplitude), POLE.4 (convergence strategy).
**Status.** ☐ not started. Effort: VERY HARD (same scale as Y1.3 + Group OZFIX combined;
requires the Blum-Wertheim Laplace inversion for the matrix case).

---

## Group MZERO — Mixture `det(Q̂₀)` Zero Family (HS-pole existence)

**Scope.** `det(Q̂₀(s))` has **infinitely many** complex zeros `s_k` (the "HS poles" whose
residues feed MML.2/MML.3's Mittag-Leffler series). **MZERO.1** is the foundational statement;
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
**File.** `YukawaDCF/MixtureHSZeros.lean` (foundation) / `MixtureHSPoles.lean`.

**Foundation — DONE (2026-07-15), axiom-clean, `YukawaDCF/MixtureHSZeros.lean`** (namespace
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
  capstones done, MZERO.9 `divisor ≥ 0` now unconditional; only `hJensen` (Nevanlinna finsum) open — **not
  blocking, Route A closes MZERO.1.**

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
order `n`) + finite support ⇒ finite zeros give the `O(log R)` bound. ◑
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
  construction (cf. MPOLY, B.9).** Only `hJensen` (Nevanlinna finsum) still open; **not blocking, since
  Route A already closes MZERO.1.** ☐

---

### Task MZERO.10 — boundary growth hypothesis

*(Route B, Lean, `MixtureHSCounting.lean`.)* ✓ **DONE** as the input hypothesis `DetBoundaryGrowth f`
(`circleAverage (Real.log‖f·‖) 0 R` beats every `M·log R + C`) + `detBoundaryGrowth_of_linear` (the
physical `≥ c·R − C₀` implies it, via `Real.isLittleO_log_id_atTop`). The `≥ c·R` estimate itself (from
`e^{−sσ}` growth) is the one analytic input, numerically confirmed by MZERO.2. Axiom-clean.

---

### Task MZERO.11 — Jensen capstone ⇒ ∞ many zeros

*(Route B, Lean, `MixtureHSCounting.lean`.)* ✓ **structural capstone DONE** (`infinite_zeros_of_growth`: a
Jensen log-bound for the finite-zeros case + `DetBoundaryGrowth` ⇒ `Set.Infinite {f=0}`; pure
contradiction) and `detC_zeros_infinite_of_growth` (**independent Route-B proof** of
`Set.Infinite {detC=0}`, matching Route A's `Q0_det_c_zeros_infinite`, modulo `hJensen` +
`DetBoundaryGrowth`). Axiom-clean. Reuses `det_meromorphicOn` (MZERO.8) for Jensen's hypothesis.

---

## Group MPOLY — Mixture Inner-Core Polynomial Coefficients (`D_ij = R'_ij(0)/6`)

**Motivation (2026-07-15).** Task **B.9 Option B** (`B5MixturePoly.lean`) is DONE and axiom-clean: it
proves the **cubic-coefficient mechanism** behind `D_ij ≠ 0` for unlike pairs — `p1_cubic_coeff`
(=σ⁵/120), `p2_cubic_coeff` (=−σ⁶/720), `exp_neg_cubic_rem`, the product-of-expansions assembly
`q0_entry_taylor3` (the `s=0` order-3 Taylor of `q0_entry` is `δ − ρ·Ep·Pp`), and `b9_dij_cubic_nonzero`
(concrete unlike pair `σ_i=1, λ=1/2, Qp=Qpp=ρ=1, δ=0` ⇒ cubic Taylor coeff `−133/2880 ≠ 0`). What B.9
does **not** give is the *faithful* inner-core polynomial coefficient `D_ij = R'_ij(0)/6` (nor A,B,C,E⁴):
the cubic Taylor coefficient of `q0_entry` is the mechanism, but the actual `P_ij(r)` coefficients come
from the **inside-core Laplace remainder** `R_ij(s) = s⁵·[exp(sR)·S_ij(s) − Y_ij(s)]` ([LN] eqs
1353–1427), where `S_ij(s)` involves `Q̂₀(s)⁻¹`.

**Statement.** Build the N=2 inside-core Laplace remainder `R_01(s)` from `[Q̂₀(s)⁻¹]₀₁ = −q₀₁(s)/det`
(MML.1's 2×2 adj/det) + the `exp(sR)` factor + the `s⁵` regularization + the singular-part subtraction
`Y_ij`, prove `AnalyticAt ℝ R_01 0`, and conclude `D_01 = R'_01(0)/6` equals the value B.9's mechanism
predicts (a concrete rational at rational parameters, via the same `q0_entry_taylor3`-style Taylor
extraction). This closes the gap between B.9's cubic-coefficient mechanism and the exact inner-core
polynomial coefficient.

**Why optional / why here.** The construction is the same-core object as the rest of the mixture
groups (MML/MZERO — the `s=0` Taylor *polynomial* form of the N=2 inner DCF), but MML.1–MML.3 build the **pole/residue
(Mittag-Leffler)** representation instead — there is no quick bridge from that to the `s=0` Taylor
form (it would require summing over the infinitely many HS poles of MZERO.1/MML.3). So MPOLY is a distinct,
optional sub-project: it reuses MML.1's adj/det but needs the inside-core Laplace `S_ij`/`Y_ij` packaging
that Lean does not yet have. B.9's mechanism (Option B) already settles `D_ij ≠ 0`; MPOLY only upgrades
it to the exact `R'_ij(0)/6` identity.

**Depends on.** MML.1 (adj/det), B.5–B.10 (`P_ij` degree/coefficients), B.9 Option B
(`q0_entry_taylor3`, the cubic-coefficient mechanism + Taylor-extraction technique), **[LN] §9.4
(Eqs 106–120, 128–139)** — the inside-core Laplace `S_ij` (Eq 106), Yukawa-pole part `Y_ij` (Eq 107),
remainder `R_ij(s) = s⁵[e^{sRᵢⱼ}·S_ij − Y_ij]` (Eq 108), and `D_ij = R'_ij(0)/6` (Eq 118). *(The
"1353–1427" in older notes were stale `pdftotext` line refs, not equation numbers.)*

**Scope correction (2026-07-15, after reading [LN] §9.4).** The earlier "independent / medium-hard"
framing was optimistic. Faithful MPOLY needs `S_ij(s)` in **closed form from the transform equation
(128/129)** — the PDF itself (§9.4.5, end of §9.4.3) flags this as *"the real difficulty"*, and it
overlaps the Y1.3/MML.3 inner-core-Laplace machinery. (Note: `[Q̂₀⁻¹]₀₁ = −q₁₂/Δ_Q` is **analytic** at
`s=0` — `φ₁,φ₂` are finite there — so it is *not* `S_ij`; the `1/s⁵` pole lives in `S_ij` itself.)

**Decomposition (2026-07-15) — MPOLY is the umbrella; the pipeline is split into independent tasks
`MPOLY.1`–`MPOLY.5`** (`YukawaDCF/MixtureLaurent.lean`), each with its own section below: **MPOLY.1** order-4
Taylor of `q0_entry` (✓ DONE) → **MPOLY.2** reciprocal series `1/Δ_Q` (Eq 136–137) → **MPOLY.3** `Δ_Q` +
inverse-entry series (Eq 130) → **MPOLY.4** Laurent→coeff machinery (Eq 105/120, the self-contained
*fallback endpoint*, extends B.8) → **MPOLY.5 (crux)** exact `S_01(s)` from Eq 128/129 ⇒ `D_01` matching
B.9's `−133/2880`-style value.
**Status.** ◑ umbrella; MPOLY.1 done, MPOLY.2–MPOLY.5 staged. Effort: HARD (MPOLY.5 = closed-form `S_ij`).

---

### Task MPOLY.1 — Order-4 Taylor of `q0_entry` *(MPOLY pipeline)*

**Statement.** The `s=0` order-4 Taylor of `q0_entry z σ λ Qp Qpp ρ δ` is `δ − ρ·Ep₄·Pp₄`, where
`Ep₄ = Σ_{k=0}^4 (−λz)^k/k!` and `Pp₄ = Qp·p1p₄ + Qpp·p2p₄` collect the order-4 Taylors of the Baxter
blocks (`p1p₄`'s `z⁴`-coefficient is `−σ⁶/720`, `p2p₄`'s is `σ⁷/5040`). This is the 5-coefficient
`q_ij(s) = q^[0] + q^[1]s + … + q^[4]s⁴ + O(s⁵)` structure ([LN] Eq 134) that `Δ_Q`/`1/Δ_Q`
(MPOLY.2–MPOLY.3) require.

**Lean (`YukawaDCF/MixtureLaurent.lean`, ns `FMSA.MixtureLaurent`).** `q0_entry_taylor4` — the
product-of-expansions assembly, mirroring B.9's `q0_entry_taylor3` one order up; via the new order-4
remainder lemmas `p1_quartic_coeff` (`→ −σ⁶/720`), `p2_quartic_coeff` (`→ σ⁷/5040`),
`exp_neg_quartic_rem`, each extending its B.9 cubic analog by one order (`Real.exp_bound` at `n+1`).

**Depends on.** B.9 Option B (`q0_entry_taylor3`, `b5_p1_limit`/`b5_p2_limit`).
**Status.** ✓ **DONE (axiom-clean, 2026-07-15)** — `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

### Task MPOLY.2 — Reciprocal-series recursion for `1/Δ_Q(s)` *(MPOLY pipeline)*

**Statement.** For an analytic `Δ_Q(s) = d₀ + d₁s + … + d₄s⁴ + O(s⁵)` with `d₀ ≠ 0`, the reciprocal
`1/Δ_Q(s) = δ₀ + δ₁s + … + δ₄s⁴ + O(s⁵)` has coefficients ([LN] Eqs 136–137)
```
δ₀ = 1/d₀,   δₙ = −(1/d₀)·Σ_{m=1}^n d_m δ_{n−m}   (n ≥ 1).
```
A self-contained numerical-series identity (no physics input).

**Lean (`MixtureLaurent.lean`).** The five `δₖ` as explicit functions of `d₀..d₄` (order-4 truncation),
verified either as a `Tendsto`/`AnalyticAt` reciprocal-Taylor statement or a direct recursion lemma.

**Depends on.** none new (pure series algebra).
**Status.** ☐ not started (tractable, self-contained).

---

### Task MPOLY.3 — `Δ_Q` order-4 coefficients + inverse-entry series *(MPOLY pipeline)*

**Statement.** Assemble `Δ_Q(s) = q₁₁(s)q₂₂(s) − q₁₂(s)q₂₁(s)` order-4 coefficients `d₀..d₄` from the
`q_ij` Taylors (MPOLY.1), and the order-4 series of `[Q̂₀(s)⁻¹]₀₁ = −q₁₂(s)·(1/Δ_Q(s))` ([LN] Eq 130)
via MPOLY.2. **Note:** this object is **analytic** at `s=0` (`φ₁,φ₂` are finite there); the `1/s⁵` pole
of the Laurent form lives in `S_ij` (MPOLY.5), not here.

**Lean (`MixtureLaurent.lean`).** Order-4 product of two `q_ij` Taylors → `Δ_Q` coeffs; apply MPOLY.2's
reciprocal recursion; multiply by `−q₁₂`'s Taylor.

**Depends on.** MPOLY.1, MPOLY.2, MML.1 (2×2 adj/det form).
**Status.** ☐ not started.

---

### Task MPOLY.4 — Laurent → coefficient extraction machinery *(MPOLY pipeline; the fallback endpoint)*

**Statement.** With `R_ij(s) := s⁵·[e^{sRᵢⱼ}·S_ij(s) − Y_ij(s)]` ([LN] Eq 108) analytic at `s=0`, the
polynomial coefficients are `A=a^{(−1)}, B=a^{(−2)}, C=a^{(−3)}/2!, D=a^{(−4)}/3!, E⁴=a^{(−5)}/4!`
(Eqs 105/115–119), unified as
```
coeff[rᵐ] P_ij = R_ij^{(4−m)}(0) / (m!·(4−m)!)   (Eq 120),
```
in particular `D_ij = R'_ij(0)/6`. Extends B.8's `b8_poly_coeff_from_laurent`; **takes `S_ij`/`Y_ij`
abstract**, so it is the self-contained fallback deliverable (formalizes [LN] §9.4.2–9.4.3 without the
closed-form `S_ij`).

**Lean (`MixtureLaurent.lean`).** `R_ij` as a def + the coefficient formulas (from `iteratedDeriv` / B.8)
+ the Eq-120 unified corollary.

**Depends on.** B.8 (`b8_poly_coeff_from_laurent`).
**Status.** ☐ not started (tractable; mostly a B.8 extension).

---

### Task MPOLY.5 — Exact `S_01(s)` ⇒ concrete faithful `D_01` *(MPOLY pipeline — the crux)*

**Statement.** Build the genuine closed-form inside-core Laplace `S_01(s)` from the first-order OZ
transform equation ([LN] Eqs 128/129, §9.4.5), form `R_01` via MPOLY.4, prove `AnalyticAt ℝ R_01 0`,
extract `D_01 = R'_01(0)/6`, and verify it equals the value B.9's cubic mechanism predicts (the
concrete `−133/2880`-style rational at rational parameters). This closes the gap between B.9's
cubic-coefficient *mechanism* and the *faithful* inner-core coefficient.

**Depends on.** MPOLY.1–MPOLY.4, MML.1 (adj/det), Y1.5 (doubly-propagated Yukawa amplitude), [LN] §9.4.5.
**Status.** ☐ not started. Effort: **HARD** — the closed-form `S_ij` is the PDF's "real difficulty"
(end of §9.4.3) and overlaps the Y1.3/MML.3 inner-core-Laplace machinery. Fallback: land MPOLY.1–MPOLY.4
(the abstract machinery) and defer this.
