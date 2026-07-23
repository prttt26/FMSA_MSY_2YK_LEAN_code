# Proof Notes: N=2 Mixture Inner-Core DCF — Real-Space Baxter Route + Polynomial Coefficients (Groups MRS / MPOLY)

Proof records for the **N=2 mixture inner-core DCF as a finite closed form** — the route that
replaces the refuted Mittag-Leffler premise of MML.8 (see `proof_notes_mixture_rdf.md` Group MML).
Split out of `proof_notes_yukawa_wh.md` (2026-07-17) once the DCF real-space line (**MRS**) and the
inner-core polynomial-coefficient line (**MPOLY**) outgrew the shared Wiener–Hopf file.

**Groups in this file.**
- **Group MRS** — Mixture Real-Space Baxter route. Pivot: **(★)** `Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)`
  (no `Q̂₀⁻¹` ⇒ the DCF has **only Yukawa poles**, `det Q̂₀`'s zeros never enter ⇒ a **finite closed
  form**, piecewise at the `λ_ij` knots). The matrix WH factorization (old MRS.1, now decomposed into
  **MRS.6–MRS.8**) is the only analytic input.
- **Group MPOLY** — inner-core polynomial coefficients `D_ij = R'_ij(0)/6` (the `s=0` Taylor form of
  the same finite inner-core DCF).

**The RDF counterpart** — the Mittag-Leffler / HS-pole route (Groups Y1, MML, MZERO) — stays in
`proof_notes_yukawa_wh.md`. The `Q̂₀⁻¹`-factor count is the dividing line: **none ⇒ DCF (this file);
two ⇒ RDF (`h₁`, that file)**.

---
## Group MRS — Mixture Real-Space Baxter Route to the Inner DCF (finite closed form)

**Scope.** The DCF route that replaces MML.8's refuted Mittag-Leffler premise. Its pivot is
**(★)** `Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)`, an algebraic consequence of [LN] eq:OZ1_Baxter (a) and
`Hhat1_spec` (b) that **contains no `Q̂₀⁻¹`**. Because `Q̂₀` is entire, `Ĉ₁` has **only Yukawa
poles**: the `det Q̂₀` zeros (Group MZERO) never enter the DCF, and the inner-core DCF is a
**finite closed form** (polynomial + finitely many exponentials), **piecewise** at the
support-overlap knots (`λ_ij` first — Group IB's set). Equivalently, in real space (★) is a triple
convolution of elementary kernels:

```
    𝒞 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ
    𝒬_ij(t) = δ_ij·δ(t) − 2π√(ρᵢρⱼ)·q_ij(t),   𝒬⁻_ij(t) = 𝒬_ij(−t)
    q_ij(t) = (1/2π)[Q₀_ij·(t−R_ij) + Qpp_j·(t−R_ij)²/2]   on [λ_ij, R_ij]   (quadratic)
    ℬ_ij(t) = Σ_q c_q·e^{−z_q(t−R_ij)}·θ(t−R_ij)                            (exponentials)
    𝒞_ij(t) = 2π√(ρᵢρⱼ)·t·c^{(1)}_ij(t)·θ(t)
```

Convolutions of (piecewise polynomial) with (exponential × step) are closed-form; the knots are
the support intersections.

**Source.** `todo/to_Lean.md` §1–§2 (2026-07-16 numerical session): `fmsa_double_prop.py`,
`probe_dp_assembly.py`, `probe_true_first_order.py`; results in
`numerical_notes/results/fmsa_dp_comparison.md`.

**Numerical status (from the handoff).** (★) at N=2 over a k-sweep: **max abs err 4.4×10⁻¹³**; at
N=1 exact. Finite-basis fit `{rⁿ} ∪ {e^{±z_q r}}` to `r·c^{(1)}_{01}`: **unsplit** core resid
1.9×10⁻³ (fails, and does *not* improve with polynomial degree) vs **split at `λ_01`=0.465** resid
**1.3×10⁻⁶** (a ~1000× jump, then sitting at the QAWF quadrature noise floor); pair (2,2) (no
interior `λ` knot) 6×10⁻⁶ = the same noise floor. That is the decisive signal that the object is
finite-but-piecewise, not an infinite pole sum.

## ✅ Group MRS — completion status (2026-07-17)

**The group's goal is achieved: the inner DCF is a FINITE closed form** (refuting MML.8's
infinite-HS-pole-sum premise), and every structural step is **proved in Lean, axiom-clean modulo the
one already-accepted MA.3 half-disk axiom** (`halfDiskBoundary_eq_sum_of_small_circles`). Lean home:
`YukawaDCF/MixtureRealSpace.lean` (ns `FMSA.MRS`).

| Task | Title | Status |
|------|-------|--------|
| ~~MRS.1~~ | ~~Matrix WH factorization `Q̂₀(k)Q̂₀ᵀ(−k)=I−Ĉ₀`~~ — **decomposed → MRS.6/7/8** | ✗ retired |
| MRS.2 | [LN] eq:OZ1_Baxter (a) — **physical route to (★)** | ✓ `oz1_C1_eq`, `star_of_first_order_oz` |
| MRS.3 | **(★)** `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)`; only-Yukawa-poles corollary | ✓ `star_of_oz1_baxter_hhat1`, `star_entry_differentiableAt`, **`starMix_entry_differentiableAt`** (concrete for `Q0_mat_c`) |
| MRS.4 | real-space `q_ij` + `λ_ij` jump amplitude + symmetry | ✓ **jump-value core** (`q0Mix_jump_amplitude` `=−σᵢσⱼ/(2Δ)`, `_symm`, `_quad_at_R`, `lam_sub_R_eq`); δ-distribution reframing avoided (not needed) |
| MRS.5 | inversion ⇒ **finite closed form** | ✅ **COMPLETE + machine-verified end-to-end** (`MixtureClosedForm.lean`, 29 thm/def, all axiom-clean). **Engine:** 3 bridges (`indicator_ici/icc_conv_indicator_icc/ici` + single-window `indicator_icc_conv_general`), 5 atoms (`integral_quadratic_exp{neg,pos}_conv`, `integral_quartic_exppos_conv`, `integral_quartic`, product-integrals `integral_quad_quadReflected(_exppos)`), capstones, connectors. **All 4 𝒲 terms in closed form:** T2 `bConvP_closed_form`(+`_outer`), T3 `pConvB_closed_form` (validated vs `scipy.quad` 1.8e-15); **T4 `pbpConv_eq_intervalIntegral` = `∫P·bConvP`, and THAT integral is now CLOSED**: `expQuadClosed_decomp` (the `bracket_u`-constant cancellation ⇒ bConvP = pure-exp + quadratic) + `intervalIntegral_P_expQuadClosed` (`∫P·expQuadClosed = expQuadClosedPos + A·quartic-integral`, no residual integral, validated 1.1e-12). **Odd-part capstone** `innerDCF_N1_oddPart`: `r·c₁ = −bConvP(r)−pConvB(r)+pbpConv(r)−pbpConv(−r)`, **reproduces `get_c1_inner` to 1.2e-15**. Every integral of the DCF chain is a proven axiom-clean closed form. arbitrary-N realized+certified in `fmsa_double_prop.py` |
| MRS.6 | WH-factorization frame; `hfact` + reduce `hT0symm` to a scalar | ✓ `Cmix0`, `Cmix0_factorization`, `Cmix0_isSymm_iff`, `fin2_transpose_eq_iff_offdiag` |
| MRS.7 | swap identity ⇒ **`hT0symm`** for the physical matrix | ✓ `Qphys_T0_isSymm` (via `swap_offdiag_of_keys` + KEY 1/2) |
| MRS.8 | `Ĉ₀ = physical HS DCF` (behind MRS.2's OZ hyps) | ✗ **deprioritized** — off the critical path (payoff needs only (★)+`Q̂₀` entire); a mixture PY `Ĉ₀` does not exist in Lean and is not needed |

**What "complete" means here.** Everything provable at the structural level is proved: the DCF route
`(★) → no HS poles → finite exponential + polynomial pieces` is established, with the WH-factorization
gate (`hfact`/`hT0symm`) discharged for the physical matrix. **The single remaining item is the
explicit N=2 coefficient extraction** (MRS.5's `hpp`).

*Route for that extraction (corrected).* It is **not** a distribution/contour problem — the
**real-space** route (which MRS is built around, and which `integral_poly_exp_conv` targets) reaches
it with definite integrals only. Expand `𝒬⁻ = δ − q⁻` algebraically first: `𝒞 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ`
becomes four terms — `ℬ` (pure exp tail), `q⁻ ⋆ ℬ` and `ℬ ⋆ (q⁻)ᵀ` (poly ⋆ exp), and
`q⁻ ⋆ ℬ ⋆ (q⁻)ᵀ` (poly ⋆ exp ⋆ poly) — with **no literal `δ`-convolutions surviving** (the `δ`s just
select which factors appear). Each term is a convolution of *compactly-supported* functions =
a **piecewise definite integral**, computed by `integral_poly_exp_conv` per overlap region (the
`min/max` limits are the knots). So the extraction is **elementary but voluminous** — many definite
integrals + a case-split on `r`'s region + the 2×2 matrix bookkeeping — reachable with the building
block already proved. It is **not** faked here (it is a large multi-lemma derivation), but it is
neither a machinery gap nor genuinely hard analysis; the structural finite-form result stands without
it, and the one hard sub-question (contour vs. real-space) is settled in favour of the tractable
real-space route.

---

### Task MRS.1 — Matrix Wiener–Hopf factorization `Q̂₀(k)·Q̂₀ᵀ(−k) = I − Ĉ₀(k)` *(DECOMPOSED → MRS.6/7/8)*

**Statement.** For the N=2 mixture, `Q̂₀(k)·Q̂₀ᵀ(−k) = I − Ĉ₀(k)`, with `Ĉ₀` the zeroth-order (HS)
DCF transform matrix. The mixture analog of `OZFIX.2`, and — per (★) — the **only** genuinely
analytic input the DCF route needs (it makes eq:OZ1_Baxter, MRS.2, available).

**Decomposed (2026-07-17) into pure-numeric MRS.6/MRS.7/MRS.8** once scoping showed it is not a
single identity but a frame + one hard theorem + a deferred validation. The decisive scoping finding
that forced the split: MRS.2's `hT0symm` (`Ĉ₀` symmetric, equivalently the swap identity
`Q̂₀(k)Q̂₀ᵀ(−k) = Q̂₀(−k)Q̂₀ᵀ(k)`) is **NOT free structural algebra** —
- numerically it holds to `~10⁻¹⁴` (N=2), but **only** with the concrete Lebowitz PY coefficients;
- symbolically with **generic** Baxter coefficients it **fails**: the off-diagonal defect is a sum of
  **5 distinct exponentials** that cancels only under the PY relations. (Diagonal is automatic —
  `Σ_m Q_{im}Q'_{im}` commutes.)

So `hfact` and `hT0symm` both belong to the one physical identity; neither is a `ring`-style
throwaway. See MRS.6/7/8.

---

### Task MRS.6 — WH factorization *frame* (ex-MRS.1a)

**Done (2026-07-17), axiom-clean** — `YukawaDCF/MixtureRealSpace.lean` (ns `FMSA.MRS`). Take the
factorization as the *definition* of the zeroth-order DCF matrix and reduce the remaining symmetry
obligation to a clean swap identity:
- `Cmix0 Qfun k := 1 − Qfun k · (Qfun (−k))ᵀ` — the zeroth-order DCF matrix `Ĉ₀`.
- `Cmix0_factorization` — `Q̂₀(k)·Q̂₀ᵀ(−k) = I − Ĉ₀(k)`, discharging MRS.2's **`hfact`** for free.
- `Cmix0_transpose` — `Ĉ₀(k)ᵀ = I − Q̂₀(−k)·Q̂₀ᵀ(k)`.
- `Cmix0_isSymm_iff` — **`Ĉ₀` symmetric ⟺ the swap identity** `Q̂₀(−k)Q̂₀ᵀ(k) = Q̂₀(k)Q̂₀ᵀ(−k)`
  (so `hT0symm` reduces exactly to MRS.7).
- `T0_isSymm_of_swap` — the swap identity ⇒ `T₀ᵀ = T₀`, i.e. MRS.2's **`hT0symm`** hypothesis.
- `fin2_transpose_eq_iff_offdiag` / `T0_isSymm_iff_offdiag` — for **N=2**, `T₀ᵀ = T₀ ⟺ (T₀) 0 1 =
  (T₀) 1 0` (the diagonal is automatic, `Σ_m Q_{im}Q'_{im}` commutes). So `hT0symm` reduces all the
  way to a **single scalar identity** — exactly MRS.7.

**Status.** ✓ DONE. Discharges `hfact` outright; reduces `hT0symm` to the single off-diagonal scalar
identity of MRS.7.

---

### Task MRS.7 — the swap identity for the physical `Q̂₀` (ex-MRS.1b) — *the genuine gate*

**Statement.** `Q̂₀(−k)·Q̂₀ᵀ(k) = Q̂₀(k)·Q̂₀ᵀ(−k)` for `Q̂₀ = Q0_mat_c` with the **physical** Lebowitz PY
coefficients (`Q0phys`/`Qppphys`, `MatrixQ0.lean`). Discharges MRS.2's `hT0symm` (via MRS.6).

**Why it is the gate.** As the MRS.1 finding shows, this *fails* for generic Baxter coefficients — it
is genuine physical content of the WH factorization.

**Breakthrough (2026-07-17) — MRS.7 factors into two clean relations + a coefficient-free identity.**
The physical PY coefficients satisfy two structural relations (`c := π/vac`):
- **KEY 1** `Q0phys_ij = (σᵢ/2)·Qppphys_j + c·σⱼ` — DONE, axiom-clean (`Q0phys_key_relation`,
  `unfold; field_simp; ring`). The `ξ₂`-coupling of `Q0phys` is `(σᵢ/2)` × that of `Qppphys`.
- **KEY 2** `Qppphys_j = 2c + c²·ξ₂·σⱼ` — DONE, axiom-clean (`Qppphys_key_relation`; `Qppphys` is
  affine in `σⱼ`, slope `c²ξ₂`).

Then — **verified symbolically (sympy)** — the swap identity holds for **any** coefficients obeying
KEY 1 ∧ KEY 2 (with `ρ,σ > 0`), with the specific values `Q0phys`/`Qppphys` **eliminated** (defect
`= 0` exactly, and the only residual `√(ρᵢ²)−ρᵢ` terms vanish by positivity). So MRS.7 is no longer a
"5-exponential cancellation needing the PY values" — it is:
1. KEY 1 + KEY 2 (✓ both DONE), plus
2. **the structural swap** `Q̂₀(k)Q̂₀ᵀ(−k) 0 1 = Q̂₀(k)Q̂₀ᵀ(−k) 1 0` for `q0_entry_c` with `Q0_ij`,
   `Qpp_j` *symbols* constrained only by KEY 1 ∧ KEY 2 — a coefficient-free exp-polynomial identity.

**The structural swap — DONE (2026-07-17), axiom-clean** (`swap_offdiag_of_keys`,
`MixtureRealSpace.lean`). The minimal hypotheses were pinned down (sympy): KEY 1, KEY 2,
**`rg₀₀·rg₁₁ = rg₀₁²`**, and **`ξ₂ = rg₀₀σ₀² + rg₁₁σ₁²`** (ξ₂ in terms of the diagonal `rg`s). Under
these four, `(Q̂₀(k)Q̂₀ᵀ(−k)) 0 1 = (Q̂₀(k)Q̂₀ᵀ(−k)) 1 0` — the off-diagonal identity — holds for the
`q0_entry_c` entries with the coefficients as **free symbols** (no PY values). Proof (closed on the
first attempt): `set E₀ := exp(σ₀k/2)`, `E₁ := exp(σ₁k/2)`; eight `have`s rewriting each exponential
(`e^{±σᵢk}`, `e^{±(σ₀−σ₁)k/2}`) into `E₀,E₁` monomials via `exp_neg`/`exp_add` + `ring_nf` on the
argument; then `simp only [those]`, `field_simp` (clears `s²,s³`, `E₀,E₁ ≠ 0`), `ring`. The
half-frequency atoms make every exponential an *integer* power of `E₀,E₁`, so `ring` closes with no
extra relation.

**The physical-matrix assembly — DONE (2026-07-17), axiom-clean** (`Qphys_T0_isSymm`).  Instantiates
`swap_offdiag_of_keys` for the concrete `Qphys = Q0_mat_c` with `Q0phys`/`Qppphys`, via
`fin2_transpose_eq_iff_offdiag` (MRS.6), discharging the four hypotheses: KEY 1/2 (`Q0phys_key_relation`/
`Qppphys_key_relation`, cast to `ℂ` by `exact_mod_cast congrArg Complex.ofReal`), and
`rg₀₀rg₁₁ = rg₀₁²` / `ξ₂ = rg₀₀σ₀²+rg₁₁σ₁²` from `rhoGeoPhys i i = √(ρᵢρᵢ) = ρᵢ` (`Real.sqrt_mul_self`,
`Real.sq_sqrt`; needs `ρ ≥ 0`) + `xi2`'s `Fin.sum_univ_two`. The entry-matching (`Qppphys` ignores its
row index → `rfl`; `rhoGeoPhys` symmetry → `mul_comm`; `λ_ii = 0` → `sub_self`; the `δ` `if`s →
`Fin.reduceEq`/`reduceIte`) is handled inside the `simp only`.

**Status.** ✓ **DONE (2026-07-17), axiom-clean.**  `Qphys_T0_isSymm` proves `T₀ = Q̂₀(k)Q̂₀ᵀ(−k)` is
symmetric for the physical matrix — MRS.2's **`hT0symm`** is fully discharged. (With MRS.6's `hfact`,
two of the three MRS.1-derived inputs to MRS.2 are now proven; only MRS.8 — the `Ĉ₀ = physical DCF`
identification behind the OZ hypotheses `hoz`/`hTS` — remains.)

---

### Task MRS.8 — `Ĉ₀` is the physical HS DCF transform (ex-MRS.1c) — *deferred*

**Statement.** The `Ĉ₀ := I − Q̂₀(k)Q̂₀ᵀ(−k)` of MRS.6 equals the physical zeroth-order HS mixture DCF
transform. This is what makes MRS.2's OZ hypotheses (`hoz`/`hTS`) hold with real physical content
rather than as bare conditional inputs (it identifies `Ĉ₀` as the DCF the OZ equation is about).

**Route.** Needs the mixture real-space PY DCF `c₀_ij(r)` (cubic on the core) + its radial Fourier
transform matrix — the matrix analog of the scalar `baxter_wiener_hopf_factorization` (a cos/sin
integral computation, Group BAXTER / `OZ.12`). A BAXTER-group-scale build, not a transposition.

**Codebase search (2026-07-17) — a mixture PY DCF `Ĉ₀` does NOT exist in Lean.** Thorough sweep
verdict: only the **scalar** `c_HS` (`PYDCF.lean`) + its transforms (`C_HS_laplace`,
`RadialFourierCHS`) exist; `cHS_core`/`cHS_FMT` (`CHSKink.lean`) is the White-Bear **FMT** DCF (a
different object). There is **no species-pair-indexed real-space `c₀_ij(r)`** and no `Ĉ₀` transform.
Closest building blocks if this is ever built: the **rank-2 factorization**
`Q0_mat_phys = I − Umat·Vmat` (`Q0DetRankTwo.lean`, `Q0_mat_phys_eq_one_sub_mul`; note: a
factorization of `Q̂₀` *itself*, real argument, not the WH product), and the **scalar WH** template
`baxter_wiener_hopf_factorization`/`baxter_wiener_hopf_complex` whose `1 − ρ·radial_fourier(c_HS)`
RHS is the `n=1` case a matrix `I − Ĉ₀` must reduce to.

**⚠ MRS.8 is NOT on the critical path (2026-07-17).** The route's *payoff* — the finite closed-form
DCF — follows from **(★) + `Q̂₀` entire**; `Ĉ₀` appears nowhere in it. `Ĉ₀` enters *only* in MRS.2's
derivation of (★), and (★) is *also* obtainable directly from `(a) = eq:OZ1_Baxter` (MRS.3, done).
Moreover MRS.2's remaining inputs can be handled without MRS.8: `hTS` (`T₀S₀ = I`) is **definitional**
(`S₀ := (Q̂₀Q̂₀ᵀ(−k))⁻¹`), and `hoz` (the first-order OZ equation) is the **theory's physical axiom**
([LN]'s starting point), not something to derive. So MRS.8 is a *physical-interpretation/consistency*
item (it makes MRS.2 "fully physical" rather than conditional on the OZ law), **not a prerequisite for
the finite-form result.**

**Status.** ☐ deferred — **and deprioritized**: the route (★)→(no HS poles)→(finite form) stands
without it. Higher-value next work is MRS.4/MRS.5 (the finite closed form) and `Q̂₀` entire (removable
at `k=0`, sharpening `starMix_entry_differentiableAt`). Build the physical `Ĉ₀` only if an
unconditional (axiom-free-of-the-OZ-law) statement is wanted.

---

### Task MRS.2 — [LN] eq:OZ1_Baxter (a)

**Statement.** `Q̂₀ᵀ(k)·Ĥ₁(k)·Q̂₀(k) = [Q̂₀(−k)]⁻¹·Ĉ₁(k)·[Q̂₀ᵀ(−k)]⁻¹`  ([LN] eq:OZ1_Baxter).

**Why it matters.** One of the two inputs to (★). Its partner (b) `Q̂₀ᵀ(k)·Ĥ₁(k)·Q̂₀(k) = B₁(k)` is
**already in Lean** as `Hhat1_spec` (Y1.6). Equating (a) with (b) and solving for `Ĉ₁` is the whole
of MRS.3.

**Route.** Follows from the first-order OZ equation plus MRS.1's factorization. Check whether a
usable form already falls out of Y1's chain before re-deriving from scratch.

**Lean (`YukawaDCF/MixtureRealSpace.lean`, ns `FMSA.MRS`) — ◑ physical route to (★) DONE 2026-07-17, axiom-clean.**  Rather than assume (a), (★) is derived from the physical inputs:
- `oz1_C1_eq` — the first-order OZ step (pure algebra): `Ĥ₁·T₀ = S₀·Ĉ₁` + `T₀·S₀ = I` ⇒ `Ĉ₁ = T₀·Ĥ₁·T₀`
  (`T₀ := I−Ĉ₀`, `S₀ := I+Ĥ₀ = T₀⁻¹`; left-multiply by `T₀`, one line).
- **`star_of_first_order_oz`** — the full (★) from five clean matrix-identity hypotheses: `hoz`
  (first-order OZ `Ĥ₁T₀ = S₀Ĉ₁`), `hTS` (`T₀S₀ = I`, zeroth-order OZ), **`hfact`** (MRS.1
  `T₀ = Q̂₀(k)Q̂₀ᵀ(−k)`), **`hT0symm`** (`T₀ᵀ = T₀`, i.e. `Ĉ₀` species-symmetric), and **`hB1`**
  (`B₁ = Q̂₀ᵀ(k)Ĥ₁Q̂₀(k)` = Y1.6 `Hhat1_spec`). The symmetry step derives `Q̂₀(k)Q̂₀ᵀ(−k) =
  Q̂₀(−k)Q̂₀ᵀ(k)` from `hT0symm`+`hfact` via `transpose_mul`.

**What this pins down.** The algebra *closes exactly* only with this arrangement — first-order OZ in
the form `Ĥ₁T₀ = S₀Ĉ₁` (matches the notes' `H̃₁(I−C̃₀)=(I+H̃₀)C̃₁`), factorization order
`T₀ = Q̂₀(k)Q̂₀ᵀ(−k)` (as MRS.1 states), and `Ĉ₀` **symmetric**. So MRS.2's remaining content is exactly
these three concrete facts (all physical/MRS.1), now isolated as named hypotheses instead of an
opaque `(a)`.

**Depends on.** MRS.1 (`hfact`), Y1.6 (`hB1` = `Hhat1_spec`), the zeroth/first-order OZ (`hTS`/`hoz`),
`Ĉ₀` symmetry (`hT0symm`).

**Status.** ◑ **algebraic backbone DONE (2026-07-17), axiom-clean** — conditional on the five named
matrix identities (MRS.1 + OZ + symmetry + Hhat1_spec); the concrete factorization is MRS.1.

---

### Task MRS.3 — (★) `Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)`, and the "no HS poles" corollary

**Statement.**

```
    Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)                                   (★)
```

obtained by equating MRS.2 (a) with `Hhat1_spec` (b) and solving for `Ĉ₁` — **pure algebra**: no
contour integration, no Mittag-Leffler machinery.

**Corollary (the load-bearing one).** `Q̂₀` is entire (the `φ₁ ~ 1/k²`, `φ₂ ~ 1/k³` singularities at
`k=0` are removable — the removable values `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6` are already proved in
`MZERO.9`'s chain via `phi1_tendsto`/`phi2_tendsto`), and `B₁_ij(k) = e^{−ikR_ij}·b_ij(ik)` carries
only the Yukawa poles `k = i·z_q`. Therefore **`Ĉ₁` is meromorphic with only Yukawa poles**: the
zeros of `det Q̂₀` — the whole subject of Group MZERO — **never enter the DCF**. This refutes
MML.8's premise (see the box there) and dissolves its blockers for the DCF.

**Why it matters.** The pivot of the group: it converts the inner DCF from an
(unprovable-without-circularity) infinite pole sum into a finite closed form.

**Lean (`YukawaDCF/MixtureRealSpace.lean`, ns `FMSA.MRS`) — ✓ DONE 2026-07-17, axiom-clean.**
- `star_of_oz1_baxter` — the algebra: `Qm⁻¹·C₁·(Qmᵀ)⁻¹ = B₁` with `IsUnit Qm.det` ⇒
  `C₁ = Qm·B₁·Qmᵀ`. (Instantiate `Qm := Q̂₀(−k)`.) Proof mirrors `Hhat1_spec`'s style:
  `Matrix.mul_nonsing_inv` / `nonsing_inv_mul` + one `mul_assoc` reassociation. `IsUnit (Qmᵀ).det`
  comes free from `Matrix.det_transpose`.
- `star_of_oz1_baxter_hhat1` — the same, with **(b) supplied by Y1.6's proved `Hhat1_spec`**
  (`Ĥ₁ := Hhat1 Q0k B₁`), i.e. literally "equate (a) with (b) and solve". So the only *assumed*
  input is (a) = MRS.2.
- `star_entry_eq` — `(A·B·Aᵀ) i j = ∑_q ∑_p A i p · B p q · A j q`.
- **`star_entry_differentiableAt`** — the load-bearing corollary in Lean-checkable form: every entry
  of `Ĉ₁(z) = Q̂₀(−z)·B₁(z)·Q̂₀ᵀ(−z)` is `DifferentiableAt` wherever the entries of `Q̂₀(−·)` and `B₁`
  are — **the statement carries no hypothesis on `det Q̂₀` whatsoever**, and *that absence is the
  content*: a `det Q̂₀` zero imposes no singularity on the DCF. (Pitfall: use
  `DifferentiableAt.fun_sum`, not `DifferentiableAt.sum` — the latter is the Pi-form sum and
  produces `DifferentiableAt (∑ i ∈ s, f i)`, not `DifferentiableAt (fun z => ∑ …)`.)

- **`starMix_entry_differentiableAt`** (2026-07-17) — the corollary made **concrete for the actual
  mixture matrix** `Ĉ₁(z) = Q̂₀(−z)·B₁(z)·Q̂₀ᵀ(−z)`, `Q̂₀ = Q0_mat_c` (Y1.1): every entry is
  `DifferentiableAt` at any `k ≠ 0` where `B₁` is, **with no `det Q̂₀` hypothesis** — the `Q̂₀(−·)`
  differentiability discharged from `q0_entry_c_differentiableAt` (holomorphy off `s=0`) composed
  with negation. So the DCF's only singularities are `k=0` (removable) and `B₁`'s Yukawa poles; the
  `det Q̂₀` zeros never appear — now proved for the real object, not an abstract `Qfun`.

**Not yet formalized here:** that `Q̂₀` *is* entire and `B₁`'s only poles are Yukawa. Those are the
concrete inputs to `star_entry_differentiableAt`'s two hypotheses; the removable values
`φ₁(0) = −σ²/2`, `φ₂(0) = σ³/6` already exist (`phi1_tendsto`/`phi2_tendsto`, MZERO.9's chain), so
this is wiring, not new analysis.

**Status.** ✓ **DONE (2026-07-17), axiom-clean** — conditional only on (a) = MRS.2 (hypothesis).

**Numerical certification.** (★) verified at N=2 over a k-sweep to **max abs err 4.4×10⁻¹³**
against the independently validated assembly; exact at N=1 (the `Q`-inverse cancellation
`C̃₁ = [Q²B₁(−k) − Q̄²B₁(k)]/(ik)`).

**Depends on.** MRS.2 (a), Y1.6 (b), `Q̂₀` entirety (Group M / MZERO.9's removable values).

**Status.** ☐ not started — algebraically immediate once MRS.2 is in place.

---

### Task MRS.4 — Real-space `q_ij` (quadratic) and the `λ_ij` delta in `q'_ij`

**Statement.** Inverting the `Q̂₀` Laplace form used throughout the codebase (`_build_Qhat`), with
`φ₁(σ_i,s) = ∫₀^{σ_i} e^{−su}(u−σ_i) du` and `φ₂(σ_i,s) = ∫₀^{σ_i} e^{−su}(u−σ_i)²/2 du`:

```
    q_ij(t) = (1/2π)·[Q₀_ij·(t − R_ij) + Qpp_j·(t − R_ij)²/2],   λ_ij ≤ t ≤ R_ij
    Q̂₀_ij(s) = δ_ij − 2π√(ρᵢρⱼ)·∫_{λ_ij}^{R_ij} e^{−st} q_ij(t) dt
```

`q` is **not symmetric** (`supp q_ij = [λ_ij, R_ij]` has width `σ_i`).

**The delta (easy to miss, load-bearing).** `q_ij` is discontinuous at its inner edge, so

```
    q'_ij(t) = (poly)·1_{[λ_ij,R_ij]} + q_ij(λ_ij)·δ(t − λ_ij),
    q_ij(λ_ij) = (1/2π)[−Q₀_ij·σ_i + Qpp_j·σ_i²/2] = −σ_i·σ_j/(2Δ)      (ξ₂ cancels exactly)
```

**Delta-cancellation lemma.** The amplitude `−σᵢσⱼ/(2Δ)` is **symmetric** in `(i,j)` — and that is
exactly what makes the deltas of the `−q'_ij(r)` and `+q'_ji(−r)` terms of Baxter's relation
cancel, so `c(r)` carries no delta. The delta *inside* the convolution term, however, **survives
and must be kept**:

```
    r·c^{HS-PY}_ij(r) = −q'_ij(r) + q'_ji(−r) − 2π Σ_m ρ_m ∫ q_im(t)·q'_jm(t−r) dt
```

**⚠ Formalization warning.** Dropping the delta was a **real bug** on the Python side (broke
`c_ij = c_ji` by O(20) and made `c` diverge as `r→0`). **A Lean model that treats `q'` as a plain
function on the open support will silently prove the wrong identity.** Model `q'` as a
measure/distribution, or carry the boundary term explicitly.

**Numerical status.** `q_ij` and the `Q̂₀` form verified against `_build_Qhat` to machine
precision; `q_ij(λ_ij) = −σᵢσⱼ/(2Δ)` likewise. With the delta kept: `c_ij = c_ji` to 10⁻¹⁴ and
`c ≡ 0` for `r > R_ij` — the classic Lebowitz piecewise structure, with `q'_ji(−r)` supplying
precisely the `r < λ_ij` piece.

**Home.** The existing real-space infra — `q0_poly`/`phi_real`, `Mix` `R`/`lam`/`mediated` (cf.
`project_group_y1`, Group IB) — is the natural place.

**Depends on.** Group M (Q̂₀ entries), Group IB (`R`/`lam` infra).

**Status.** ☐ not started.

---

**Lean (`YukawaDCF/MixtureRealSpace.lean`, ns `FMSA.MRS`) — ◑ first piece DONE 2026-07-17, axiom-clean.**
The **delta amplitude is now proved**, with the concrete Lebowitz/Baxter PY coefficients
(`Q0phys`/`Qppphys`, `HSMixture/MatrixQ0.lean` — they are concrete, not abstract `Mix` fields):
- `lam_sub_R_eq` — `λᵢⱼ − Rᵢⱼ = −σᵢ` (the left endpoint offset; trivial but load-bearing).
- `q0Mix_quad_at_R` — the quadratic **vanishes** at the right endpoint `Rᵢⱼ` ⇒ **no delta there**;
  the `λᵢⱼ` end is the only jumping one. (Confirms the delta is one-sided.)
- **`q0Mix_jump_amplitude`** — `Q₀ᵢⱼ·(−σᵢ) + Q''ⱼ·(−σᵢ)²/2 = −π·σᵢ·σⱼ/vac`, i.e. **`−σᵢσⱼ/(2Δ)`
  in the `q = (1/2π)[…]` normalization** — exactly the handoff's claimed amplitude. **`ξ₂` cancels
  exactly**: `Q₀ᵢⱼ` gives `−π ξ₂ σᵢ²σⱼ/(4 vac)` and `Q''ⱼ` gives `+π ξ₂ σⱼ σᵢ²/(4 vac)`. Proof is
  `unfold; field_simp; ring` (needs `vac ≠ 0`). Verified symbolically (sympy) first.
- `q0Mix_jump_amplitude_symm` — the amplitude is **`i↔j`-symmetric**, the algebraic input to the
  delta-cancellation that MRS.5's convolution needs.

**Remaining for MRS.4:** the *distributional* statement — that `q'_ij` genuinely contains
`(−πσᵢσⱼ/vac)·δ(t−λᵢⱼ)` — and the cancellation itself. The amplitude/symmetry above are its
arithmetic core; the trap (modelling `q'` as a plain function on the open support drops the delta)
is why the jump must be carried explicitly. `q0MixEntry` (Y1.3a, `WHSupports.lean`) is the windowed
`q_ij` these attach to.

---

### Task MRS.5 — Convolution bookkeeping ⇒ finite closed form, piecewise at the knots

**Statement.** Inverting (★) term by term — equivalently, evaluating the real-space triple
convolution `𝒞 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ` of the group header — gives, inside the core, a **finite** sum of
Yukawa-pole residues (`e^{±z_q r}`) plus the `k=0` contributions (a polynomial in `r`): a finite
closed form for `r·c^{inner}_{ij}(r)`, **piecewise**, with knots exactly at the support-overlap
breakpoints (`λ_ij` first among them).

**Why it matters.** The constructive endpoint that replaces MML.8 for the DCF. It would also make
Python's `get_c1_inner` table-free (it currently uses one DST table or per-point QAWF — an
optimization, not a correctness gap).

**Route (elementary but tedious).** Convolutions of (piecewise polynomial) with
(exponential × step) are closed-form; the knots are the support intersections. Must consume MRS.4's
delta correctly (see the warning there).

**Consistency checks already available.** (i) N=1 (Tang / `SingleCompReduction.lean`): `c(r)` has a
finite closed form (poly₄ + two exponentials) while `g(r)` needs a pole expansion — (★) explains
*why*, and shows it is not special to N=1. (ii) The predicted piecewise structure coincides with
**Group IB**'s independently derived breakpoint set (`λ_ij` C⁰ knot + mediated knots).

**Depends on.** MRS.3 ((★)), MRS.4 (`q` + delta); Group IB (knot set).

**The atomic core — DONE (2026-07-17), axiom-clean** (`MixtureRealSpace.lean`). The claim "finite
closed form" rests on one fact: **a polynomial ⋆ (exp × step) is a polynomial + one exponential** —
proved:
- `integral_poly_exp_conv` — for `z ≠ 0` and any polynomial `q` with integrating-factor
  antiderivative `G` (`G′ + zG = q`), `∫_a^u q(τ)·e^{−z(u−τ)} dτ = G(u) − G(a)·e^{−z(u−a)}`. Proof:
  FTC-2 with antiderivative `F(τ) = e^{−z(u−τ)}·G(τ)`, whose derivative is exactly `q(τ)·e^{−z(u−τ)}`
  (the `zG` terms cancel). This is the per-piece "finite closed form, no new poles" content: **each
  convolution `q ⋆ ℬ` closes in a polynomial + a single exponential**, with the `e^{−z(u−a)}`
  frequency the pre-existing Yukawa pole (no HS poles introduced).
- `integral_linear_exp_conv` — the explicit linear instance (`q = c₀+c₁τ`, `G = c₁/z·τ + (c₀/z−c₁/z²)`).
- `integral_quadratic_exp_conv` (**NEW 2026-07-18, axiom-clean**) — **the degree the mixture actually
  needs**: the Baxter inversion `_q_coeffs` shows `q_ij(t) = c₀+c₁t+c₂t²` is a *quadratic*, with
  `G = c₂/z·τ² + (c₁/z−2c₂/z²)·τ + (c₀/z−c₁/z²+2c₂/z³)`. This **completes the `integral_*_exp_conv`
  family up to the DCF's degree** — every per-piece convolution the real-space assembly needs now has
  its atomic closed form in Lean. **Numerically tied to the Python oracle** `fmsa_double_prop.py`
  (`_build_closed_form`/`_px_antideriv_u`): with the *real* mixture `_q_coeffs` and *real* Yukawa poles,
  the Lean closed form `G(u)−G(a)·e^{−z(u−a)}` equals `scipy.quad` of the integrand to **1e-15**, and
  the Lean `G′+zG=q` hypothesis is literally the oracle's `γB−B_u=A` antiderivative check.

**~~What remains (needs machinery Mathlib lacks)~~ — SUPERSEDED (2026-07-18) by the real-space route
below.** *(Original escalation: a literal `𝒞 = 𝒬⁻⋆ℬ⋆(𝒬⁻)ᵀ` assembly with `MeasureTheory.convolution`
of the `δ_ij·δ(t)` unit terms would need distribution theory. This was wrong to frame as the only
route.)* Expanding `𝒬⁻ = δ − q⁻` **first** kills every literal `δ`-convolution (only the four terms
`ℬ`, `q⁻⋆ℬ`, `ℬ⋆(q⁻)ᵀ`, `q⁻⋆ℬ⋆(q⁻)ᵀ` survive, all compactly-supported ordinary integrals), so **no
distribution API is needed** — the per-piece atoms `integral_poly_exp_conv`/`integral_quadratic_exp_conv`
suffice. What genuinely remains is *bookkeeping volume*, not a machinery gap (see the two-routes note
below and the Python oracle, which does exactly this assembly for arbitrary N).

**The finite-pole Fourier inversion — DONE (2026-07-17), via MA.3 (no new axiom, no distributions).**
The earlier "needs distribution/convolution machinery" was the *real-space* route; the **finite-pole
k-space route dissolves it** — the mixture analog of the OZFIX.10 dissolution. By (★)/MRS.3, `Ĉ₁` has
**only finitely many** poles (the Yukawa poles), so:
- **Exponential part** — `fourier_kernel_finite_poles` (`MixtureRealSpace.lean`): for a *finite* set of
  upper-half-plane poles `k_q` with residue weights `A_q`, the truncated inverse-Fourier integral of
  the principal part `Σ_q A_q/(x−k_q)` → `Σ_q A_q·2πi·e^{i k_q r}`, a **finite exponential sum** (no
  convergence issue, unlike the RDF's infinite HS-pole series). Direct linear combination of MA.3
  `fourier_kernel_one_pole` over the finite pole set. `#print axioms` =
  `[halfDiskBoundary_eq_sum_of_small_circles, propext, Classical.choice, Quot.sound]` — i.e. **only
  MA.3's already-accepted half-disk deformation axiom**, no new assumption.
- **Polynomial×exponential part** — `integral_poly_exp_conv` (above): the core-Baxter `q ⋆ ℬ`
  convolution pieces, `= poly + one exp`. (This is the directly-applicable analog of
  `radial_inversion_antideriv` for the real-space convolution structure.)

Both inversion mechanisms are proved, plus a capstone:
- `innerDCF_finite_closed_form` — **if** `Ĉ₁` agrees on the real axis with its finite principal-part
  sum `Σ_q A_q/(k−k_q)`, its inverse FT is the finite exp sum `Σ_q A_q·2πi·e^{ik_q r}`. Wraps
  `fourier_kernel_finite_poles`; axiom dependency = only MA.3's half-disk.

**Two routes to the concrete N=2 coefficients — the real-space one is the tractable one.**
- *k-space* (harder): the concrete `Ĉ₁` is **not** a global finite principal-part sum on ℝ (`Q̂₀(−k)`,
  `B₁` carry entire exponential factors `e^{±λk}`, `e^{−ikR}`), so `innerDCF_finite_closed_form`'s
  global `hpp` fails as-is; a region-by-region contour argument would be needed. Avoid this.
- *real-space* (the MRS route, tractable): expand `𝒬⁻ = δ − q⁻` **first**, so
  `𝒞 = 𝒬⁻⋆ℬ⋆(𝒬⁻)ᵀ` becomes four terms — `ℬ`, `q⁻⋆ℬ`, `ℬ⋆(q⁻)ᵀ`, `q⁻⋆ℬ⋆(q⁻)ᵀ` — with **no literal
  `δ`-convolution surviving**. Each is a convolution of *compactly-supported* functions = a piecewise
  definite integral, and each region reduces (via `u = t−R`) to exactly `integral_poly_exp_conv`
  (`∫_a^u q(τ)·A·e^{−z(u−τ)}dτ = A(G(u)−G(a)e^{−z(u−a)})`). So the extraction is **elementary but
  voluminous** (four terms × the region case-split × the 2×2 matrix), reachable with the building
  block already proved — **not distributions, not contours, not genuinely hard**, just a large
  derivation. (An earlier note here wrongly escalated it to "needs a contour argument"; that route
  exists but the real-space route sidesteps it.)

**Status.** ◑ **finite-form structure + all per-piece atoms + the convolution-VALUE engine (both
directions) + the mixture-kernel connectors DONE, axiom-clean modulo MA.3.**
k-space mechanism: `fourier_kernel_finite_poles` + `innerDCF_finite_closed_form`.  Real-space atoms
(`MixtureRealSpace.lean`): `integral_poly_exp_conv` / `integral_linear_exp_conv` /
`integral_quadratic_exp_conv`.  **NEW `MixtureClosedForm.lean` (2026-07-18) — the convolution-value
engine the transcription was blocked on** (`MixtureConvolution.lean` had only the *support* geometry,
no values; it flagged "the Mathlib-convolution ⇄ interval-integral bridge" as the missing piece):
- **The bridge, both directions** — `indicator_ici_conv_indicator_icc` (`ℬ⋆P`) and
  `indicator_icc_conv_indicator_ici` (`P⋆ℬ`): the Mathlib `mul`-convolution of an `[a,∞)`-window with
  an `[b,c]`-window equals the *interval integral* of the smooth product over the support overlap
  (`[max a (x−c), x−b]` resp. `[b, min c (x−a)]`) — the `px_convolve` limit rule, proved from
  `convolution_def` (no numerics).  **This is the keystone the file had flagged as missing.**
- **The sign-paired atoms** — `integral_quadratic_expneg_conv` (decaying `e^{−zτ}`, for `ℬ⋆P`) and
  `integral_quadratic_exppos_conv` (growing `e^{zτ}`, for `P⋆ℬ`): the two integrating-factor
  antiderivatives the two convolution directions need.
- **End-to-end per-term closed forms** — `expWindow_conv_quadWindow` (`ℬ⋆P`) and
  `quadWindow_conv_expWindow` (`P⋆ℬ`): a single Yukawa-exp window convolved with a quadratic window
  = explicit poly×exp, in closed form, chaining bridge + atom.  **No new poles — only the pre-existing
  Yukawa rate.**  Each is validated to **machine precision** against a *direct numerical convolution*
  (`∫ℬ(t)P(x−t)dt` by `scipy.quad`): `ℬ⋆P` 1.8e-15, `P⋆ℬ` 1.2e-15.
- **Mixture-kernel connectors** — `pMixEntry_eq_indicator_quad` (rewrites the real `pMixEntry` into
  the engine's `(Icc)-quadratic-indicator` shape) and `bMixEntry_eq_sum` (`bMixEntry` = finite `Σ_q`
  of single-exp windows).  So the engine applies **verbatim** to the actual mixture kernels — the
  "last mile" is a definitional rewrite, not new analysis.

All 8 lemmas axiom-clean (only `propext`/`Classical.choice`/`Quot.sound`; the bridge needs *no* MA.3).
The Python oracle `fmsa_double_prop.py` `_build_closed_form` remains the independently-certified
arbitrary-N assembly (outer=MSA tail 1e-14, N=1 inner=Tang 1e-9) and an exact per-piece checker.

**What remains — the multi-term assembly (mechanical chaining of the proved pieces above).** (i) the
double convolution `P⋆ℬ⋆P` (convolve `pMixEntry` against the already-closed-form `bConvP` — same atoms,
more regions); (ii) the "other" `max`/`min` region of each convolution (the capstones cover the aligned
region); (iii) convolution-linearity over the finite `Σ_q` (`bMixEntry_eq_sum`) and the `Σ_{m,n}`
species sum; (iv) the 4-term `𝒲 = ℬ − Σℬ⋆P − ΣP⋆ℬ + ΣP⋆ℬ⋆P` and the odd part
`[𝒲(r)−𝒲(−r)]/(2π√ρᵢρⱼ·r)`.  **Not** a machinery gap — every atom, bridge, and connector it needs is
now proved and validated; it is bookkeeping over proved lemmas, with the Python oracle as per-piece
checker.  Deliberately not ground out in full here; the arbitrary-N closed form is realized and
certified in Python.

---

## Group MPOLY — Mixture Inner-Core Polynomial Coefficients (`D_ij = R'_ij(0)/6`)

**Motivation (2026-07-15).** Task **GAP.9 Option B** (`MixturePolyCoeffs.lean`) is DONE and axiom-clean: it
proves the **cubic-coefficient mechanism** behind `D_ij ≠ 0` for unlike pairs — `p1_cubic_coeff`
(=σ⁵/120), `p2_cubic_coeff` (=−σ⁶/720), `exp_neg_cubic_rem`, the product-of-expansions assembly
`q0_entry_taylor3` (the `s=0` order-3 Taylor of `q0_entry` is `δ − ρ·Ep·Pp`), and `dij_cubic_nonzero`
(concrete unlike pair `σ_i=1, λ=1/2, Qp=Qpp=ρ=1, δ=0` ⇒ cubic Taylor coeff `−133/2880 ≠ 0`). What GAP.9
does **not** give is the *faithful* inner-core polynomial coefficient `D_ij = R'_ij(0)/6` (nor A,B,C,E⁴):
the cubic Taylor coefficient of `q0_entry` is the mechanism, but the actual `P_ij(r)` coefficients come
from the **inside-core Laplace remainder** `R_ij(s) = s⁵·[exp(sR)·S_ij(s) − Y_ij(s)]` ([LN] eqs
1353–1427), where `S_ij(s)` involves `Q̂₀(s)⁻¹`.

**Statement.** Build the N=2 inside-core Laplace remainder `R_01(s)` from `[Q̂₀(s)⁻¹]₀₁ = −q₀₁(s)/det`
(MML.1's 2×2 adj/det) + the `exp(sR)` factor + the `s⁵` regularization + the singular-part subtraction
`Y_ij`, prove `AnalyticAt ℝ R_01 0`, and conclude `D_01 = R'_01(0)/6` equals the value GAP.9's mechanism
predicts (a concrete rational at rational parameters, via the same `q0_entry_taylor3`-style Taylor
extraction). This closes the gap between GAP.9's cubic-coefficient mechanism and the exact inner-core
polynomial coefficient.

**Why optional / why here.** The construction is the same-core object as the rest of the mixture
groups (MML/MZERO — the `s=0` Taylor *polynomial* form of the N=2 inner DCF), but MML.1/2/4–8 build the **pole/residue
(Mittag-Leffler)** representation instead — there is no quick bridge from that to the `s=0` Taylor
form (it would require summing over the infinitely many HS poles of MZERO.1/MML.8). So MPOLY is a distinct,
optional sub-project: it reuses MML.1's adj/det but needs the inside-core Laplace `S_ij`/`Y_ij` packaging
that Lean does not yet have. GAP.9's mechanism (Option B) already settles `D_ij ≠ 0`; MPOLY only upgrades
it to the exact `R'_ij(0)/6` identity.

**Depends on.** MML.1 (adj/det), GAP.5–GAP.10 (`P_ij` degree/coefficients), GAP.9 Option B
(`q0_entry_taylor3`, the cubic-coefficient mechanism + Taylor-extraction technique), **[LN] §9.4
(Eqs 106–120, 128–139)** — the inside-core Laplace `S_ij` (Eq 106), Yukawa-pole part `Y_ij` (Eq 107),
remainder `R_ij(s) = s⁵[e^{sRᵢⱼ}·S_ij − Y_ij]` (Eq 108), and `D_ij = R'_ij(0)/6` (Eq 118). *(The
"1353–1427" in older notes were stale `pdftotext` line refs, not equation numbers.)*

**Scope correction (2026-07-15, after reading [LN] §9.4).** The earlier "independent / medium-hard"
framing was optimistic. Faithful MPOLY needs `S_ij(s)` in **closed form from the transform equation
(128/129)** — the PDF itself (§9.4.5, end of §9.4.3) flags this as *"the real difficulty"*, and it
overlaps the Y1.3/MML.8 inner-core-Laplace machinery. (Note: `[Q̂₀⁻¹]₀₁ = −q₁₂/Δ_Q` is **analytic** at
`s=0` — `φ₁,φ₂` are finite there — so it is *not* `S_ij`; the `1/s⁵` pole lives in `S_ij` itself.)

**Decomposition (2026-07-15) — MPOLY is the umbrella; the pipeline is split into independent tasks
`MPOLY.1`–`MPOLY.5`** (`YukawaDCF/MixtureLaurent.lean`), each with its own section below: **MPOLY.1** order-4
Taylor of `q0_entry` (✓ DONE) → **MPOLY.2** reciprocal series `1/Δ_Q` (Eq 136–137) → **MPOLY.3** `Δ_Q` +
inverse-entry series (Eq 130) → **MPOLY.4** Laurent→coeff machinery (Eq 105/120, the self-contained
*fallback endpoint*, extends GAP.8) → **MPOLY.5 (crux)** exact `S_01(s)` from Eq 128/129 ⇒ `D_01` matching
GAP.9's `−133/2880`-style value.
**Status.** ◑ umbrella; MPOLY.1 done, MPOLY.2–MPOLY.5 staged. Effort: HARD (MPOLY.5 = closed-form `S_ij`).

---

### Task MPOLY.1 — Order-4 Taylor of `q0_entry` *(MPOLY pipeline)*

**Statement.** The `s=0` order-4 Taylor of `q0_entry z σ λ Qp Qpp ρ δ` is `δ − ρ·Ep₄·Pp₄`, where
`Ep₄ = Σ_{k=0}^4 (−λz)^k/k!` and `Pp₄ = Qp·p1p₄ + Qpp·p2p₄` collect the order-4 Taylors of the Baxter
blocks (`p1p₄`'s `z⁴`-coefficient is `−σ⁶/720`, `p2p₄`'s is `σ⁷/5040`). This is the 5-coefficient
`q_ij(s) = q^[0] + q^[1]s + … + q^[4]s⁴ + O(s⁵)` structure ([LN] Eq 134) that `Δ_Q`/`1/Δ_Q`
(MPOLY.2–MPOLY.3) require.

**Lean (`YukawaDCF/MixtureLaurent.lean`, ns `FMSA.MixtureLaurent`).** `q0_entry_taylor4` — the
product-of-expansions assembly, mirroring GAP.9's `q0_entry_taylor3` one order up; via the new order-4
remainder lemmas `p1_quartic_coeff` (`→ −σ⁶/720`), `p2_quartic_coeff` (`→ σ⁷/5040`),
`exp_neg_quartic_rem`, each extending its GAP.9 cubic analog by one order (`Real.exp_bound` at `n+1`).

**Depends on.** GAP.9 Option B (`q0_entry_taylor3`, `p1_limit`/`p2_limit`).
**Status.** ✓ **DONE (axiom-clean, 2026-07-15)** — `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

### Task MPOLY.2 — Reciprocal-series recursion for `1/Δ_Q(s)` *(MPOLY pipeline)*

**Statement.** For an analytic `Δ_Q(s) = d₀ + d₁s + … + d₄s⁴ + O(s⁵)` with `d₀ ≠ 0`, the reciprocal
`1/Δ_Q(s) = δ₀ + δ₁s + … + δ₄s⁴ + O(s⁵)` has coefficients ([LN] Eqs 136–137)
```
δ₀ = 1/d₀,   δₙ = −(1/d₀)·Σ_{m=1}^n d_m δ_{n−m}   (n ≥ 1).
```
A self-contained numerical-series identity (no physics input).

**Lean (`MixtureLaurent.lean`).** `taylor4_recip` — the `Tendsto` reciprocal-Taylor statement, in the
file's convention: from `Δ = d₀+…+d₄z⁴ + o(z⁴)` at `0⁺` and `d₀ ≠ 0`, conclude
`1/Δ = r₀+…+r₄z⁴ + o(z⁴)`, with the `rₖ` supplied as the Eq-(137) hypotheses `hr0`–`hr4` (`n = 0..4`).

**Route chosen — `Tendsto`, NOT `PowerSeries`.** Mathlib's `PowerSeries.inv`
(`RingTheory/PowerSeries/Inverse.lean:131`, `coeff_inv`) *is* Eq (137), but it sits on the wrong side of
a bridge Mathlib does not have: there is **no** `FormalMultilinearSeries.inv` / `HasFPowerSeriesAt.inv`,
and `AnalyticAt.inv` is coefficient-free. Nothing in `LeanCode/` uses `PowerSeries` (0 grep hits).
Building that bridge would exceed proving the recursion directly, and would not compose with
`q0_entry_taylor4`.

**Proof.** (1) *Cleared convolution* `e0 : d₀r₀ = 1`, `eₖ : d₀rₖ + Σ_{m=1}^k d_m r_{k−m} = 0` — Eq (137)
with `1/d₀` cleared (`field_simp; ring`). (2) *Tail identity*
`1 − P₄(z)Q₄(z) = z⁵(c₅ + c₆z + c₇z² + c₈z³)`, `c₅ = −(d₁r₄+d₂r₃+d₃r₂+d₄r₁)`, …, `c₈ = −d₄r₄` —
discharged by `linear_combination (-1)*e0 + (-z)*e1 + (-z²)*e2 + (-z³)*e3 + (-z⁴)*e4` (the `eₖ` *are* the
vanishing of the `z⁰..z⁴` coefficients). (3) `Δ → d₀` ⇒ `Δ ≠ 0` eventually and `1/Δ → 1/d₀`.
(4) `(1/Δ − Q₄)/z⁴ = [(1 − ΔQ₄)/z⁴]·(1/Δ)` and `(1 − ΔQ₄)/z⁴ = z·(c₅+…) − ((Δ−P₄)/z⁴)·Q₄ → 0`;
the `congr'` step closes by `field_simp; linear_combination -hk`.

**Numerically pre-checked** (verify-before-formalize): exact-rational check that `P₄·Q₄` has coefficients
`(1,0,0,0,0)` for `z⁰..z⁴`, and 60-dp check that `(1/Δ − Q₄)/z⁵ → δ₅` (predicted by the same recursion) to
9 digits.

**Depends on.** none new (pure series algebra).
**Status.** ✓ **DONE (2026-07-16), axiom-clean** — `taylor4_recip`; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.

---

### Task MPOLY.3 — `Δ_Q` order-4 coefficients + inverse-entry series *(MPOLY pipeline)*

**Statement.** Assemble `Δ_Q(s) = q₁₁(s)q₂₂(s) − q₁₂(s)q₂₁(s)` order-4 coefficients `d₀..d₄` from the
`q_ij` Taylors (MPOLY.1), and the order-4 series of `[Q̂₀(s)⁻¹]₀₁ = −q₁₂(s)·(1/Δ_Q(s))` ([LN] Eq 130)
via MPOLY.2. **Note:** this object is **analytic** at `s=0` (`φ₁,φ₂` are finite there); the `1/s⁵` pole
of the Laurent form lives in `S_ij` (MPOLY.5), not here.

**Lean (`MixtureLaurent.lean`).** A small **order-4 Taylor calculus** in the file's `Tendsto`
convention, then the two capstones:
- `taylor4_tendsto_const` — order-4 Taylor data ⇒ the `0⁺` limit is the constant term (reused by
  `taylor4_mul`, and the same block MPOLY.2's proof needs).
- `taylor4_mul` — the **order-4 Cauchy product** ([LN]'s "ordinary series multiplication and
  collection"): `cₖ = Σ_{i+j=k} aᵢbⱼ`. Proof = the `q0_entry_taylor4` product-of-expansions skeleton:
  `f·g − P_f P_g = (f−P_f)·g + P_f·(g−P_g)`, plus the `z⁵..z⁸` tail of `P_f P_g` (pure `ring`).
- `taylor4_sub`, `taylor4_neg` — coefficientwise, one-liners off `Tendsto.sub`/`.neg` + `congr'`.
- **`taylor4_deltaQ`** — Eq (131)/(135): `Δ_Q = q₀₀q₁₁ − q₀₁q₁₀` order-4 coefficients as the
  Cauchy combinations `(a⋆e)ₖ − (b⋆c)ₖ`; a pure composition `taylor4_sub (taylor4_mul …) (taylor4_mul …)`.
- **`taylor4_inv_entry`** — Eq (130): the order-4 series of `[Q̂₀⁻¹]₀₁ = −q₀₁·(1/Δ_Q)`, composing
  MPOLY.2's `taylor4_recip` with `taylor4_neg` + `taylor4_mul`.

**Design note — no MML.1 dependency.** MML.1's `Q0_det_fin_two`/`Q0inv_zero_one` are over **ℂ**
(`Q0_mat_c`), while the whole MPOLY Taylor line is over **ℝ** (`FMSA.MatrixQ0.q0_entry`, `z → 0⁺`).
Rather than bridge that seam, `taylor4_deltaQ` takes the four `q_ij` **abstractly** and states Eq (131)
algebraically — which is exactly what Eq (131) is. The concrete `q0_entry` instantiation (via
`q0_entry_taylor4`) is then a plug-in, and `d₀ ≠ 0` (physically `det Q̂₀(0) ≠ 0`) stays a hypothesis,
discharged per-parameters by `norm_num` as in `dij_cubic_nonzero`.

**Depends on.** MPOLY.1, MPOLY.2. *(Not MML.1 — see the design note.)*
**Status.** ✓ **DONE (2026-07-16), axiom-clean** — `taylor4_tendsto_const`, `taylor4_mul`,
`taylor4_sub`, `taylor4_neg`, `taylor4_deltaQ`, `taylor4_inv_entry`; all `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.

---

### Task MPOLY.4 — Laurent → coefficient extraction machinery *(MPOLY pipeline; the fallback endpoint)*

**Statement.** With `R_ij(s) := s⁵·[e^{sRᵢⱼ}·S_ij(s) − Y_ij(s)]` ([LN] Eq 108) analytic at `s=0`, the
polynomial coefficients are `A=a^{(−1)}, B=a^{(−2)}, C=a^{(−3)}/2!, D=a^{(−4)}/3!, E⁴=a^{(−5)}/4!`
(Eqs 105/115–119), unified as
```
coeff[rᵐ] P_ij = R_ij^{(4−m)}(0) / (m!·(4−m)!)   (Eq 120),
```
in particular `D_ij = R'_ij(0)/6`. Extends GAP.8's `poly_coeff_from_laurent`; **takes `S_ij`/`Y_ij`
abstract**, so it is the self-contained fallback deliverable (formalizes [LN] §9.4.2–9.4.3 without the
closed-form `S_ij`).

**Lean (`MixtureLaurent.lean`).** `R_ij` as a def + the coefficient formulas (from `iteratedDeriv` / GAP.8)
+ the Eq-120 unified corollary.

**Depends on.** ~~GAP.8~~ — **GAP.8 is vacuous** (`∃` closed by 5 `rfl`s; its `AnalyticAt` hypothesis is
never used) ⇒ nothing to inherit.
**Status.** ❌ **NOT COMPLETABLE** — see below. Beyond GAP.8's vacuity, the target `P_ij` itself does not
exist for unlike pairs.

**❌ NOT COMPLETABLE — premise falsified (2026-07-17).** Decisive evidence: read the **data structure**
of the shipped, validated `fmsa_double_prop` closed form (`closed_form_pieces`, 2YK) — structural, not a fit:

| pair | λ | pieces on `r>0` | rate-0 polynomial |
|---|---|---|---|
| like (0,0) | 0 | **1** piece `[0,0.967]` | deg 5 |
| like (1,1) | 0 | **1** piece `[0,1.897]` | deg 5 |
| **unlike (0,1)** | ≠0 | **2** pieces | `[0,0.465]`: deg 2 ／ `[0.465,1.432]`: deg 5 |

The polynomial part of `f = 𝒲(r) − 𝒲(−r)` ([LN]'s `E+P`): on `(0,λ)`, `f_poly = 1.111·r` (degree 1, zero
constant — exactly Eq (102) origin regularity); on `(λ,R)`, `f_poly = −1.281 + 1.189r + 0.203r² + 0.0447r⁴`
(degree 4, nonzero constant; the `r³` and `r⁵` terms cancel exactly). **Two different polynomials** ⇒
[LN] Eq (101)'s "**single** deg-≤4 `P_ij` on all of `0<r<R_ij`" is **false for unlike pairs**.

Mechanism: `c⁽¹⁾ = [𝒲(r) − 𝒲(−r)]/(2π√(ρᵢρⱼ)r)`; for `r<λ` both `±r` land in the same piece (even terms
cancel ⇒ only `1.111r` survives), for `r>λ` they land in **different** pieces. At λ=0 (like) the interior
breakpoint disappears ⇒ **Eq (101) is correct for like pairs** — which is why N=1 Tang/FMSA_pure works.
The breakpoint originates in the support `[λ_ij, R_ij]` of the Baxter `q_ij(t)` (shipped docstring:
"piece edges = support-overlap breakpoints, **λ_ij first**"), consistent with Group IB /
`project_mediated_breakpoints`' stepwise-poly conclusion. The rigidity that turns "different pieces" into
"no single `P`" is **IB.4**'s `not_single_poly_of_pieces_ne` (`InnerDecomp.lean`, axiom-clean).

**A second, independent contradiction:** the shipped structural identity
`Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` — **no Q̂₀⁻¹, and the DCF has no HS poles at all** ("the zeros of
det Q̂₀ never enter"; the Mittag-Leffler HS-pole sum belongs **only to the RDF `ĥ₁`**). This directly
conflicts with the MPOLY umbrella's "`S_ij(s)` involves `Q̂₀(s)⁻¹`" and with MPOLY.3's
`[Q̂₀⁻¹]₀₁ = −q₁₂/Δ_Q` route.

**Survives:** the **generic order-4 Taylor calculus** proved in MPOLY.2/MPOLY.3 (`taylor4_recip`,
`taylor4_mul`, `taylor4_sub`, `taylor4_neg`, `taylor4_tendsto_const`, `taylor4_deltaQ`,
`taylor4_inv_entry`) together with `taylor4_coeff_unique` / `poly4_eq_zero_of_littleO` does **not**
depend on Eq (101) and applies equally to the piecewise form.


---

### Task MPOLY.5 — Exact `S_01(s)` ⇒ concrete faithful `D_01` *(MPOLY pipeline — the crux)*

**Statement.** Build the genuine closed-form inside-core Laplace `S_01(s)` from the first-order OZ
transform equation ([LN] Eqs 128/129, §9.4.5), form `R_01` via MPOLY.4, prove `AnalyticAt ℝ R_01 0`,
extract `D_01 = R'_01(0)/6`, and verify it equals the value GAP.9's cubic mechanism predicts (the
concrete `−133/2880`-style rational at rational parameters). This closes the gap between GAP.9's
cubic-coefficient *mechanism* and the *faithful* inner-core coefficient.

**Depends on.** ~~MPOLY.1–MPOLY.4, MML.1, Y1.5, [LN] §9.4.5~~
**Status.** ❌ **NOT COMPLETABLE (2026-07-17)** — the target `D_01 = R'_01(0)/6` rests on [LN] Eq (101)'s
single polynomial `P_01`, and `P_01` **does not exist for unlike pairs** (the inner core splits at λ_ij).
Same evidence as MPOLY.4 above; the rigidity is IB.4's `not_single_poly_of_pieces_ne`.
**This also settles GAP.8**: GAP.8 is "half a theorem" whose other half (the `P_ij` side) is exactly MPOLY.5 —
that side's object is now known to be falsified, so **GAP.8 cannot be completed as stated**.
