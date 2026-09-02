# Other closures (其他闭包) — task status

The closures that are **neither** the FMSA-DP construction itself **nor** the exact MSA: PYE (the
`pullback_passes=0` construction ≡ first-order PY) and HNCB (first-order HNCB bridge). **Scope + axiom
gate: [`LeanCode/ClosuresProject.lean`](LeanCode/ClosuresProject.lean)** (the PYE/HNCB-specific
capstones; the shared first-order-outer results stay in `FMSAProject.lean`).

↩ **Index:** [`todo_lean.md`](todo_lean.md) — layer map, project-wide axiom/sorry ledger, category index.

**Detailed records:**
- [proof_notes_closures.md](proof_notes_closures.md) — the **PYE** and **HNCB** parts

---

## Task Status

### Group PYE — No-Pull-Back Construction ≡ First-Order PY *(closures)*

The `pullback_passes=0` YK-tail FMSA-DP construction **is** first-order PY; the only error vs true
first-order PY is the finite-Yukawa-tail re-approximation of the outer closure `g_HS·(−βu)`. Sits on
Groups Y1 (DP linearity) + MRS (finite closed form). Source: `hncb_first_order.md`, `HNCB_FMSA_dp.py`.
See [proof_notes_closures.md](proof_notes_closures.md) Group PYE.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| PYE.1 | PY closure to O(coupling): outer `c₁ = g_HS·(−βu)` (`y₀=g_HS`) | ✓ DONE (2026-07-31, axiom-clean): `py_first_order_outer`, `cavity_zero_coupling`, `py_first_order_outer_cavity`, `msa_first_order_outer`; **+ the γ₁-collapse** `pass_zero_eq_py_first_order` (with `hncbClosure`, `hncb_first_order_outer`, `hncb_outer_zeroth_order_eq_zero`) | `Closures/ClosureExpansions.lean` |
| PYE.2 | DP first-order solution map **linear** in the outer closure (corollary of Y1 `bMulti`/`Ĉ₁` linearity) | ✓ DONE (2026-07-31, axiom-clean): `b1OfCouplingLinear` (Y1.5 `bMulti` linear in `K`) ∘ `starConjLinear` ((★), MRS.3) = `dpDCFLinear`, fixed-rate family `dpTailsLinear`; stage 1 `outerTransform_add/_smul`. ⚠ needs the rates **frozen** — free rates sit in `s + z_mp` and the map is not linear | `Closures/ClosureExpansions.lean` |
| PYE.3 ⭐ | **DCF error = DP-map[finite-tail fit residual]** ⇒ "only error = the YK re-approximation"; needs `wh_solution_operator_bounded` *(recommended first target)* | ✓ DONE (2026-07-31, axiom-clean): `dp_error_eq_dp_of_residual` (= `map_sub`), physical form `dp_sub_py_first_order_eq_conj_residual` (via MRS.2 `star_of_first_order_oz`), headline `dp_error_entry_norm_le`. **`wh_solution_operator_bounded` is a THEOREM, not a new axiom** — explicit `whOperatorBound = T·N⁴·Qb²·Ab²/δ` | `Closures/ClosureExpansions.lean` |
| PYE.4 | Abstract equivalence `DP-map[g_HS·(−βu)] = OZ+PY first order` (needs WH map lifted to an L¹/L² function-space closure) | ⭐ **conditional-complete (2026-09-01)** — capstone `dp_converges_to_py_first_order_of_whProjectionL1` (std-3, gated §PYE) assembles the whole equivalence into ONE theorem (`exists_tailFit_whConvergent` → `dp_tendsto_py_first_order`); **sole hypothesis = `WHProjectionL1`** (matrix Wiener-`1/f` `L¹` bound, deliberately a `Prop`/hypothesis, MA.13/MA.15-class boundary, non-vacuity certified). Nothing left but that analysis boundary; assembly adds no axiom | `Closures/DPClosureMap.lean` |
| PYE.5 | **`k → r` bridge** — k-space `Ĉ₁` identity ⇒ real-space `c₁(r)` on the core `(0,R)` | ✓ DONE (2026-08-03, axiom-clean): `radial_fourier_injective` (on the project's own `radial_inversion`, a theorem not an axiom), dictionary `IsRadialEntry`, `inner_core_dcf_eq_of_khat_eq`, capstone `inner_core_dcf_eq_of_exact_fit` + structural non-vacuity `example`. ⚠ open core only (contact jump), and **no real-space error bound** (`k·Ĉ₁(k) ∉ L¹` under a k-uniform bound) | `Closures/ClosureExpansions.lean` |
| PYE.6 | the zeroth-order factor **is** the PY hard-sphere Baxter factor | ✓ DONE at `N = 1` (2026-08-03, axiom-clean) — **the library already had it**: BAXTER.3 `baxter_wiener_hopf_complex` (= MRS.8 at `N=1`) + `pyhs_no_spinodal` + the MRS.0b chain `Q0phys_n1`/`Qppphys_n1`/`qhat_complex_eq_mixture_kernel`. Wired in as `pyBaxterMat`/`pyT0Mat`/`pyT0Mat_entry`/`pyT0Mat_isUnit_det`/`dp_zeroth_order_is_py_n1`/`dp_eq_py_first_order_n1` ⇒ `hfact`+`hT0symm`+`hTS` discharged with the physical PY objects, … | `Closures/{ClosureExpansions,DPClosureMap}.lean` |
| PYE.7 | density of finite Yukawa-tail fits ⇒ PYE.3's residual → 0 on the outer window | ✓ DONE (2026-08-03, axiom-clean): `exists_yukawa_tail_fit` (+ `_pyOuter` for the actual target `r·g_HS·(−βu)`). **Route: Weierstrass after `t = e^{−r}`, NOT Stone-Weierstrass** — polynomials in `e^{−r}` *are* exponential sums, so no adjoin/span extraction; one `δ`-shift makes the `k=0` constant a legal tail. Rates come out **unit-spaced** (third independent argument for fixed separated rates). … | `Closures/ClosureExpansions.lean` |

### Group HNCB — First-Order HNCB Bridge Pull-Back Construction *(closures)*

The whole **fixed-rate** first-order HNCB (`'solve'`) = closure expansion + finite `(I−L)⁻¹` + DP map
+ linear OZ apply — finite linear algebra, the finite-tail truncation the only approximation. Exact
self-consistent HNCB-1 is the **RDF** ⇒ HS poles ⇒ not finite-closed-form (HNCB.4, boundary). See
[proof_notes_closures.md](proof_notes_closures.md) Group HNCB.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| HNCB.1 | HNCB closure to O(coupling): outer `c₁ = −βu + B·h₁`, `B=h_HS/g_HS=1−1/g_HS` | ✓ **DONE (2026-08-03, axiom-clean)**. `exp`-form half (PYE.1 by-products): `hncbClosure`, `hncb_outer_zeroth_order_eq_zero`, **`hncb_first_order_outer`**, `pass_zero_eq_py_first_order`. Audit additions: `hncb_base_point_gamma_eq` (the two hypotheses **force `γ₀ = g_HS−1 = h_HS`**) + non-vacuity `example`. … | `Closures/ClosureExpansions.lean` |
| HNCB.2 | Fixed-rate pull-back map **affine** `K̃'=a+L·K̃` (reuses Y1 `Ĥ₁`) | ✅ **DONE 2026-09-01** — `pullbackRung`/`pullbackLinearPart`/`pullbackRung_affine` (std-3, gated §HNCB): rung = `refit(−βu) + L·K̃`, `L = B·refit ∘ starConj(F⁻¹) ∘ dpDCFLinear ∘ embed`; frozen rates make it affine | `Closures/DPClosureMap.lean` |
| HNCB.3 | Fixed point `K̃*=(I−L)⁻¹a`; `(I−L)` invertible (finite matrix) | ✅ **DONE 2026-09-01** — `affine_fixed_point_unique` + `pullbackRung_fixed_point` (`∃!`) + `pullbackRung_fixed_point_eq` (`K̃*=(I−L)⁻¹·refit(−βu)`), std-3, gated §HNCB; `I−L` invertibility = caller `LinearEquiv` hyp. HNCB.1–.3 complete | `Closures/DPClosureMap.lean` |
| HNCB.4 | *(record only)* Exact HNCB-1 carries the RDF `h₁` ⇒ HS poles ⇒ not finite-closed-form (MZERO/MML.5 wall) | ☐ **boundary marker, NOT a to-do** — nothing to prove; the `☐` reads like unstarted work and is not | — |

### Group PYE PYE.1–PYE.3 CLOSED (2026-07-31) — no-pull-back construction ≡ first-order PY, **no new axiom**
`Closures/ClosureExpansions.lean` (ns `FMSA.FirstOrderClosure`): PYE.1–3 axiom-clean (std-3, all decls). PYE.1 `c₁=g_HS·(−βu)`; PYE.2 DP map **linear** (frozen rates); PYE.3 error = DP-map[fit residual] (`map_sub`), `wh_solution_operator_bounded` = THEOREM (`whOperatorBound=T·N⁴·Qb²·Ab²/δ`). Non-vacuity certified by a non-degenerate `example`. See the Group PYE table.

### PYE.5 + PYE.6 (2026-08-03) — the k→r bridge, and the zeroth-order factor IS PY's (N=1)
PYE.5 k→r bridge (`radial_fourier_injective` + `IsRadialEntry` ⇒ `inner_core_dcf_eq_of_exact_fit`, pointwise on `(0,R)`; ⚠ open core only, no real-space error bound). PYE.6 zeroth-order factor = PY Baxter: `N=1` already in the library (BAXTER.3 = MRS.8@N=1); **general `N` DONE 2026-08-19** (`dp_zeroth_order_is_py_N`, `#print axioms` = std-3 + `pyhs_mixture_no_spinodal`). See the Group PYE table.

### PYE.7 CLOSED (2026-08-03) — Yukawa-tail fits are dense; PYE.4 still open
`exists_yukawa_tail_fit`(+`_pyOuter`), axiom-clean: Yukawa-tail fits are dense (Weierstrass after `t=e^{−r}`, NOT Stone–Weierstrass; rates unit-spaced). ⚠ does NOT close PYE.4 (compact window ≠ half-line; function residual ≠ WH-datum distance).

### PYE.4 REDUCED to one classical input (2026-08-03) — the function-space lift, built
PYE.4's function-space lift is built except ONE classical input `WHProjectionL1` (hypothesis, MA.13/15-class Wiener 1/f — kept, not axiomatized). Proved: half-line + **L¹** tail-fit density, `‖Û₁(k)‖≤‖Ψ‖_{L¹}` uniform in k, `TailFitWHConvergent` **derived**. ⚠ amplitude route is a DEAD END (unbounded); the norm must be real-space L¹ (Riesz, not sup-k). See the Open-tasks PYE.4 row.
