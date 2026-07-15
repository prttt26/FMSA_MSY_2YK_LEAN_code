# Proof Notes: First-Order Yukawa RDF/DCF via Wiener–Hopf (Group Y1)

Proof records for **Group Y1** — the analytical first-order (order-ε¹) Yukawa RDF/DCF derivation of
Tang & Lu (1995), formalized from the **[LN]** lecture notes
(`pdf/lecture_notes_OZ_Yukawa_poly.pdf`, §5–§6, §8–§9).

**Relation to Group BAXTER.** Group BAXTER handled the *zeroth-order* hard-sphere route
(Baxter/Wiener–Hopf factorization → PY closed form). Group Y1 is the **first-order Yukawa analog**:
the same **algebraic** Wiener–Hopf machinery (causal/anti-causal split + support statements +
residues — *not* the Hilbert transform of [LN] §6.3, which Mathlib lacks; see Y1.3) applied to the
first-order OZ equation `H̃₁(I − C̃₀) = (I + H̃₀)C̃₁` ([LN] Eq. 7), producing the spectral amplitude
`b_{ij}(s)` (Eq. 73) and the first-order RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹ B₁ [Q̂₀]⁻¹` (Eq. 68). Split off from
`proof_notes_yukawa_dcf.md` (2026-07-15) since it is a Group-BAXTER-scale body of work, not a
Group-C "consistency check".

**Scaffold only (2026-07-15).** This file currently holds the task *chain* (Y1.1–Y1.7) with [LN]
equation references, dependencies, and the already-proved pieces cross-linked. Proofs are added
task-by-task in later sessions.

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
**Depends on.** B.2 (real `Q0_mat` structure), M.3/M.4 (`det ≠ 0`).
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

**Decomposition.** a/c are light; the hard, independent piece is Y1.3b.
- **Y1.3a — support statements** (§6.3.2, [LN] Eq. 55–57): the atomic real-space supports (Baxter
  factor on `[λ_{ij}, R_{ij}]`; `h^{(1)}` on `[R,∞)`; `S₁` on `[0,R]`) + the half-line ⇄ full-line
  transform bridges. ✓ DONE — see below.
- **Y1.3b — support-orthogonality / FT injectivity** (Eq. 61–62): matching the `[R,∞)` parts via FT
  uniqueness on disjoint half-line supports (incl. the convolution-support fact that
  `L = Q̂₀ᵀĤ₁Q̂₀` is `[R,∞)`-supported) ⇒ `L = {T_U}^{[R,∞)}`. **The logical crux, hardest new
  analysis.** ☐ not started.
- **Y1.3c — causal projection = residue extraction** (Eq. 63–66): `{T_U}^{[R,∞)}` = sum of the
  upper-half-plane Yukawa-pole residues. Largely *is* `matrix_conj_residue` (Y1.4); increment = the
  "causal part = that residue term" identification, closing to `B₁ = b_{ij}` (Y1.5).

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

**Status.** ◑ Y1.3a DONE; Y1.3b (FT injectivity, the crux) + Y1.3c (residue identification) ☐ open.

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
**Remaining (☐).** the general distinct-`z_{αβ}` residue (per-pole term matching) and tying
`A_{ij}(z)` to `[Q̂₀(z)⁻¹]_{ij} − δ` via Y1.1.
**Status.** ✓ single-tail + multi-tail collapse DONE (2026-07-15), axiom-clean; general distinct-`z`
residue not started.

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

### Task Y1.7 — *(optional)* inner-core `S₁(k)` and contact matching

**Statement ([LN] §9, §7).** The inside-core contribution `S₁(k)` (Eq. 45) and the core matching
condition at `r = R_{ij}` (§7). Links to the polynomial `P_ij` of Groups B/IB (the inner DCF
polynomial) and the origin constraint `A_{ij} = −Σ_n 𝓔_n(0)` (Eq. 76).

**Depends on.** Y1.3–Y1.6; Groups B.5–B.10 (`P_ij`), IB (breakpoints), 5.1 (matching).
**Status.** ☐ not started (optional; lowest priority).

---

## Group Y2 — N=2 Mixture Inner-Core Closed Form (Mittag-Leffler)

**Motivation (2026-07-15).** For N=2, Q̂₀(z) is a 2×2 matrix with fully algebraic entries
(Y1.1 DONE). Its inverse is Q̂₀(z)⁻¹ = adj(Q̂₀)/det(Q̂₀), also proved (Y1.1:
`inv_apply_eq_adj_div_det`). For the (0,1) off-diagonal entry:

    [Q̂₀(z)⁻¹]₀₁  =  adj(Q̂₀)₀₁ / det(Q̂₀)  =  −Q̂₀₀₁(z) / det(Q̂₀(z))     (2×2 identity)

The zeros s_k of det(Q̂₀(z)) (the "HS poles") then give residues:

    Res_{z=s_k} [Q̂₀⁻¹]₀₁  =  −Q̂₀₀₁(s_k) / det′(Q̂₀)(s_k)     (residue_of_simple_pole)

This is the B_k coefficient used in `fmsa_hs_pole_residue.py`. Y2.1–Y2.2 are provable from
existing tools without Y1.3; Y2.3 (infinitely many HS poles for det(Q̂₀)) is a harder
structural result; Y2.4 (full assembly) requires Y1.3. Together they prove the exact inner
DCF for N=2 unlike pairs IS a convergent Mittag-Leffler series — resolving the "no closed
form" claim.

---

### Task Y2.1 — Explicit 2×2 adjugate/det for Q̂₀

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
**File.** Extend `YukawaDCF/Q0Complex.lean` (or `MatrixQ0.lean`).
**Status.** ☐ not started. Effort: LOW (single `simp` / `ring` step).

---

### Task Y2.2 — B_k residue formula for N=2

**Statement.** Let s_k ∈ ℂ be a simple zero of `z ↦ det(Q0_mat_c z)` (an HS pole),
i.e., `det(Q̂₀(s_k)) = 0` and `(d/dz det(Q̂₀(z)))|_{z=s_k} ≠ 0`. Then:

    Res_{z=s_k} ([Q̂₀(z)⁻¹]₀₁)  =  −Q̂₀₀₁(s_k) / det′(Q̂₀)(s_k)

(This is the Q̂₀-residue part of the B_k amplitude in `fmsa_hs_pole_residue.py`.
The Yukawa-propagator factor `K/(z_t²−s_k²)` requires Y1.3 and is not part of this task.)

**Proof chain.**
1. Y2.1: `[Q̂₀(z)⁻¹]₀₁ = N(z)/D(z)` where `N(z) = −Q̂₀₀₁(z)`, `D(z) = det(Q̂₀(z))`.
2. `N` and `D` are meromorphic / holomorphic near s_k (Y1.1 — entries are entire).
3. `residue_of_simple_pole` (BaxterResidue.lean DONE): gives `Res = N(s_k)/D′(s_k)`.
4. Conclude `= −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)`.

**Depends on.** Y2.1, `residue_of_simple_pole` (DONE), M.3/M.4 (for det′ ≠ 0 hypothesis,
currently conditional).
**File.** New `YukawaDCF/MixtureHSPoles.lean`.
**Status.** ☐ not started. Effort: MEDIUM (wiring simple-zero hypothesis; no new analysis).

---

### Task Y2.3 — Infinitely many HS poles for N=2

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

Alternatively, extend BAXTER.11's Banach-contraction strategy to det(Q̂₀):
- Parameterize zeros of det(Q̂₀(s)) by solving `s = F_n(s)` for a family of maps F_n
  derived from the quasi-polynomial structure of det(Q̂₀).
- Show the contraction bound holds for each n (numerically: run the analog of BAXTER.10
  for the N=2 det).

**Depends on.** Y2.1 (det formula), Y1.1 (entries entire), M.4 (det ≠ 0 on real axis),
BAXTER.11 proof strategy.
**File.** `YukawaDCF/MixtureHSPoles.lean`.
**Status.** ☐ not started. Effort: HARD (quasi-polynomial root analysis; may need
preliminary numerical check analogous to BAXTER.10).

---

### Task Y2.4 — Full Mittag-Leffler inner-DCF assembly for N=2 *(blocked on Y1.3)*

**Statement.** For the N=2 unlike pair (0,1), for r ∈ (0, R₀₁]:

    r · c^{inner}_{01}(r) = Σ_t [Q̂₀⁻¹·K_t·Q̂₀⁻ᵀ]₀₁ · exp(z_t(R₀₁−r))
                           + Σ_k 2·Re[B_k · exp(−s_k·r)]  +  p₀

where B_k = K_t · adj(Q̂₀(s_k))₀₁ / ((z_t²−s_k²) · det′(Q̂₀)(s_k)) (combining Y2.2
with the Yukawa propagator from Y1.3).

This is the N=2 matrix analog of the scalar Mittag-Leffler series in BAXTER.12/13.

**Depends on.** Y1.3 (Wiener–Hopf), Y2.2 (B_k residue), Y2.3 (infinitely many poles),
Y1.5 (doubly-propagated Yukawa amplitude), BAXTER.12 (convergence strategy).
**Status.** ☐ not started. Effort: VERY HARD (same scale as Y1.3 + BAXTER.13 combined;
requires the Blum-Wertheim Laplace inversion for the matrix case).
