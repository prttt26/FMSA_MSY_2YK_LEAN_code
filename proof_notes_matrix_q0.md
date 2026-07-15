# Proof Notes — Group M: Multi-Component Baxter Q̂₀ Matrix Identity & det-positivity

Status index: [todo_lean.md](todo_lean.md). Lean files: `LeanCode/YukawaDCF/MatrixIdentity.lean`
(M.1), `MatrixN1.lean` (M.2), `MatrixQ0.lean` (M.3), `Q0DetRankTwo.lean` (M.4–M.8). Split from
`proof_notes_yukawa_dcf.md` on 2026-07-15 (Group M outgrew it). Numerical analysis:
`numerical_notes/{theory,results}/q0_det_positivity.md`, `q0_det_analysis.py`,
`verify_q0_det_positivity.py`.

---

## Group M — Multi-Component Baxter Identity

Derives the matrix analog of the N=1 identity `g + a·e^{-z} = 1` (Task 4.2).
The mathematical derivation is in `problem_answers/multicomp_g_a_derivation.md`.

### Task M.1 — Abstract matrix identity: Ĝ + Â·c = I

**Statement:** For `n×n` real matrices `P`, `E`, `D` with `D = P + c • E` (c a scalar)
and `D` invertible:
```
P * D⁻¹ + c • (E * D⁻¹) = 1
```
This is the matrix analog of `g + a·e^{-z} = 1` (Task 4.2), where:
- `P` = polynomial-part matrix (analog of `S`)
- `E` = exponential-coefficient matrix (analog of `12η·L`)
- `c = exp(−z·σ_min)` = the exponential factor from the smallest diameter
- `D = Q̂₀` = full Baxter Q-matrix (analog of `D = S + 12ηL·e^{-z}`)
- `Ĝ = P·D⁻¹`, `Â = E·D⁻¹` = multi-component analogs of scalar g, a

**Why it matters:** Guarantees that the corrected inner-core formula
`c_ij(r) = K(1−Ĝ²_{ij})·e^{-z(r-R)} − K·Â²_{ij}·e^{+z(r-R)} + Poly`
uses the correct coefficients (Ĝ + Â·c = I mirrors g + a·e^{-z} = 1 for N=1).

**Proof sketch:**
```
P·D⁻¹ + c•(E·D⁻¹) = (P + c•E)·D⁻¹ = D·D⁻¹ = I
```
Left-distributes `D⁻¹`, substitutes `D = P + c•E`, then applies `IsUnit.mul_val_inv`.

**Lean:**
```lean
-- LeanCode/YukawaDCF/MatrixIdentity.lean
theorem g_mat_add_a_mat_exp_eq_one {n : ℕ}
    (P E D : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hD_def : D = P + c • E)
    (hD : IsUnit D) :
    P * D⁻¹ + c • (E * D⁻¹) = 1 := by
  rw [← add_mul, smul_mul, ← hD_def]
  exact hD.mul_val_inv
```

**Depends on:** Nothing new — pure matrix algebra (Mathlib `Matrix` API).

**Status:** ✓ DONE — `g_mat_add_a_mat_exp_eq_one` in `LeanCode/YukawaDCF/MatrixIdentity.lean` (complete):
  `rw [← Algebra.smul_mul_assoc, ← add_mul, ← hD_def]` + `Matrix.mul_nonsing_inv D hD`.
  Note: hypothesis is `IsUnit D.det` (not `D.det ≠ 0`); Mathlib's `Matrix.mul_nonsing_inv`
  requires `IsUnit`. Also includes `g_mat_n1_eq_scalar` (N=1 scalar limit sanity check):
  `rw [← mul_div_assoc, ← add_div, hnum, div_self hD]` — same structure as Task 4.2.

---

### Task M.2 — N=1 limit: Ĝ₀₀ = g(z) and Â₀₀ = a(z)

**Statement:** For n=1, the matrix definitions `Ĝ = P̂·D̂⁻¹` and `Â = Ê·D̂⁻¹` reduce to
the scalar single-component propagators:
```
Ĝ_{00} = P̂_{00} / D̂_{00} = S(z) / D(z) = g(z)
Â_{00} = Ê_{00} / D̂_{00} = 12η·L(z) / D(z) = a(z)
```
where `S`, `L`, `D`, `g`, `a` are as in `SingleCompIdentity.lean` (Task 4.2).

**Why it matters:** Confirms that the multi-component FMSA_GA_matrix_mix formula reduces exactly to
FMSA_pure for N=1. The corrected inner-core `K(1−Ĝ²)·e^{-z(r-R)} − K·Â²·e^{+z(r-R)}`
then matches [chsY] Eq. 43 term-by-term.

**Proof strategy:** For n=1, `P̂`, `Ê`, `D̂` are 1×1 matrices = scalars. Matrix multiplication
`P̂ · D̂⁻¹` becomes scalar division `P̂_{00} / D̂_{00}`. Lean:
```lean
theorem g_mat_n1_eq_g_scalar (S L η z : ℝ) (hD : D ≠ 0) :
    let D := S + 12 * η * L * Real.exp (-z)
    (fun _ _ => S : Matrix (Fin 1) (Fin 1) ℝ) *
    (fun _ _ => D : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = fun _ _ => S / D := by
  ext i j; fin_cases i; fin_cases j
  simp [Matrix.inv_fin_one, div_eq_mul_inv]
```

**Depends on:** M.1, Task 4.2 (`g_add_a_mul_exp_eq_one`), `Matrix.inv_fin_one`.

**Status:** ✓ DONE — `LeanCode/YukawaDCF/MatrixN1.lean`

Key results proved (all in `namespace FMSA.MatrixN1`):
- `fin1_const_mul` (proved): 1×1 matrix multiplication is scalar multiplication
- `fin1_const_inv` (proved via left-inverse uniqueness): 1×1 matrix inverse is scalar inverse;  needed — D=0 case uses `nonsing_inv_apply_not_isUnit`; D≠0 case uses `mul_assoc` + `Matrix.mul_nonsing_inv` uniqueness argument
- `mat_fin1_mul_inv` (proved): `(fun _ _ => S) * (fun _ _ => D)⁻¹ = fun _ _ => S/D` unconditionally
- `g00_eq_g_scalar`, `a00_eq_a_scalar` (proved): entry-wise reduction
- `m2_identity` (proved): chains into `FMSA.SingleComp.g_add_a_mul_exp_eq_one`
- `m2_identity_baxter` (proved): concrete form using `Q0_ne_zero_at_yukawa` axiom from Task 2.2

---

### Task M.3 — det(Q̂₀) ≠ 0 for valid multi-component parameters

**Statement:** For a physically valid n-component mixture (total packing fraction η < 1,
all ρᵢ ≥ 0, all σᵢ > 0), the Baxter Q-matrix `Q̂₀(z)` is invertible for all z > 0:
```
det(Q̂₀(z)) ≠ 0
```
This is the multi-component analog of Task 2.2 (`Q0_ne_zero_of_eta_lt_one` for N=1).

**Why it matters:** Required to define Ĝ = P̂·Q̂₀⁻¹ and Â = Ê·Q̂₀⁻¹ (M.1, FMSA_GA_matrix_mix).
Without invertibility, the matrix decomposition is ill-defined.

**2026 update — the original axiom was FALSE, now replaced:** Since Task 2.2 was proved (not
just axiomatized), it was tempting to axiomatize M.3 the same way. But the old axiom left `Qp`
(`Q'ᵢⱼ`) and `Qpp` (`Q''ᵢⱼ`) as free real parameters, unconstrained by `sigma`/`rho`. Since
`hz`/`hsigma`/`hrho`/`heta` say nothing about `Qp`/`Qpp`, they can be chosen adversarially to
force `det = 0` even when every hypothesis holds — concrete counterexample: `n=2`, equal
diameters, `z=1`, `rho_geo ≡ 0.1` (`η≈0.0105∈(0,1)`), `Qpp≡0`, `Qp≈−13.59` gives
`Q0_mat = !![0.5,-0.5;-0.5,0.5]`, `det=0`. So the axiom was disproved, not just hard.

**Fix:** substitute the actual multicomponent PY (Lebowitz/Baxter) closed-form coefficients
for `Qp`/`Qpp`/`rho_geo` (matching `fmsa_ga_matrix_mix.py`'s `_build_Q0_Qpp`/`_build_Qhat`
exactly) instead of leaving them free. This makes the claim genuinely meaningful. The
*unconditional* (`∀ z>0`) version is Task M.4 (see below): numerically, individual
off-diagonal entries of the raw matrix blow up exponentially for large `z` whenever species
diameters differ (`exp(-z·λᵢⱼ)` with `λᵢⱼ<0`) — the same obstruction as the FMSA_chsY/
GA_matrix_mix 2YK failure. What's proved here (Task M.3) is a *conditional* result via
Mathlib's Gershgorin circle theorem (`det_ne_zero_of_sum_row_lt_diag`): strict row diagonal
dominance of the concrete physical matrix (an explicit, numerically-checkable inequality)
implies invertibility. That's real progress — no axiom, and the hypothesis is checkable at any
given state point — even though the fully general `∀ z>0` claim remains open (Task M.4).

**Depends on:** Task 2.2 (proved; motivated attempting the same axiomatic shortcut for M.3,
which failed); Mathlib's `det_ne_zero_of_sum_row_lt_diag` (Gershgorin) for the conditional
proof.

**Status:** ◑ conditional — `LeanCode/YukawaDCF/MatrixQ0.lean`. Unconditional case: Task M.4.

Key results in `namespace FMSA.MatrixQ0`:
- `q0_entry`: concrete scalar (i,j) entry formula (B.2 form), still parameterized by free
  `Qp`/`Qpp` (used only for the pure B.2 algebraic identity, which holds for any `Qp`/`Qpp`)
- `Q0_mat`: n×n matrix assembled from `q0_entry`
- `Q0_mat_entry_decomp` (proved): each entry satisfies the B.2 decomposition
  `Q̂₀ᵢⱼ = P̂ᵢⱼ + Êᵢⱼ · exp(-z·σ_min)` via `b2_qhat_entry_decomp`
- `Q0_mat_isUnit_det` (old axiom): **removed — disproved**, see above
- `xi2`, `etaMix`, `vacMix`, `Q0phys`, `Qppphys`, `rhoGeoPhys` (defined): concrete
  Lebowitz/Baxter multicomponent PY coefficients, matching the Python implementation
- `Q0_mat_phys` (defined): `Q0_mat` with `Qp`/`Qpp`/`rho_geo` substituted by the above
- `Q0_mat_phys_isUnit_det_of_diag_dom` (proved): `IsUnit (Q0_mat_phys ...).det` conditional
  on strict row diagonal dominance, via Gershgorin
- `Q0_mat_n1_entry` (proved): for n=1, the (0,0) entry simplifies to the scalar Q₀ form
  (N=1 consistency check; `λ₀₀ = 0` gives `exp(0) = 1` automatically)

---

### Task M.4 — Unconditional invertibility of `Q0_mat_phys` for all `z > 0`

**Statement:** For a physically valid n-component mixture (same hypotheses as Task M.3:
`z≠0`, `vacMix≠0`, all `ρᵢ≥0`), `Q0_mat_phys(z)` is invertible **unconditionally** — no
diagonal-dominance side hypothesis needed, unlike M.3's conditional result. Individual
off-diagonal entries of `Q0_mat_phys` blow up exponentially as `z→∞` whenever species
diameters differ, so M.3's Gershgorin approach cannot reach this; M.4 instead exploits that the
determinant itself stays bounded even though entries don't.

**Rank-2 reduction** (`LeanCode/YukawaDCF/Q0DetRankTwo.lean`, no `sorry`/`axiom`):
`Q0_mat_phys(z)` is exactly `1 - U·V` for `U : n×2`, `V : 2×n` built from
`u1ᵢ=√ρᵢ·exp(zσᵢ/2)·f(σᵢ,z)`, `u2ᵢ=√ρᵢ·exp(zσᵢ/2)·g(σᵢ,z)`,
`v1ⱼ=√ρⱼ·exp(-zσⱼ/2)`, `v2ⱼ=√ρⱼ·exp(-zσⱼ/2)·σⱼ` — proved as `Q0_mat_phys_eq_one_sub_mul`
(the `√ρᵢ·√ρⱼ`/`exp(zσᵢ/2)·exp(-zσⱼ/2)` merges are isolated into a separate lemma, `UV_apply`,
before the `Q0phys`/`Qppphys`/`p1`/`p2` algebra, which is then a clean `field_simp;ring`).
Mathlib's `det_one_sub_mul_comm` (Weinstein–Aronszajn/Sylvester identity,
`Mathlib.LinearAlgebra.Matrix.SchurComplement`) then gives, as `Q0_mat_phys_det_eq_two_by_two`,
`det(Q0_mat_phys) = det(1 - V·U)`, a **fixed 2×2 determinant independent of n** — this is why
individual entries diverge as `z→∞` while `det` stays bounded: inside `V·U`'s sums,
`exp(zσᵢ/2)·exp(-zσᵢ/2)=1` cancels the blowup exactly (`VU_apply_00`).

**Sign facts:** proved (same `p(0)=0,p'(0)=0,p''>0` derivative-chain technique as
`bigD0/bigD1/bigD2` in `BaxterFactor.lean` for Task 2.2, as `p1_neg`/`mAux_neg`/`nAux_neg`):
`p₁(σ,z)<0`, `p₂(σ,z)>0`, and hence `fFun<0`, `gFun<0` for all `σ,z>0` (`fFun_neg`, `gFun_neg`).
This pins every entry of the reduced 2×2 matrix `M=V·U` as `≤0`.

**The one remaining gap:** the sign facts reduce the whole claim to one explicit, n-independent
scalar inequality `(1+a)(1+d) > bc` for nonneg moment sums `a,b,c,d` (the negated 2×2 entries).
**Not yet closed**, and — sharpened by the 2026-07-15 de-risk pass
(`numerical_notes/{theory,results}/q0_det_positivity.md`) — it is *not* Cauchy–Schwarz-closable in
either direction: with `F=−f>0, G=−g>0`, `det = 1 + a + d + (ad−bc)` and (Cauchy–Binet)
`ad−bc = Σ_{j<k} ρⱼρₖ(σₖ−σⱼ)(FⱼGₖ−FₖGⱼ)`, which is **identically 0 at N=1** and, because `g/f` is
monotone **decreasing** in σ, is **≤ 0 always**, i.e. **`bc ≥ ad` for all N** (Task **M.8**; so the
`ad ≥ bc` direction is never available). Positivity therefore rests entirely on the `1+a+d` slack.
Numerically **`det ≥ 1`** always (20 000 trials, `η` up to 0.999, min `det = 1.0000020`, sharp only
in the dilute limit), so the sharp target is **`det ≥ 1 ⟺ a + d ≥ bc − ad`**; the residual content
is an `O(ρ²) bc−ad ≤ O(ρ) a+d` bound that must use the packing constraint `η<1` (`vac=1−η` in the
denominators of f,g) — it does **not** factor (`sympy.factor`). Eigenvalue restatement:
`det > 0 ⟺ λ₋([[a,b],[c,d]]) > −1`. The monotonicity route (`bc ≥ ad`) is the elementary Tasks
**M.5–M.8** below, **all now proved** (axiom-clean). Stated as an explicit hypothesis (`hdet`) on
the final theorem `Q0_mat_phys_isUnit_det_of_two_by_two` rather than a `sorry` — the smallest
possible remaining gap for M.4.

**Recommended closure routes (2026-07-15), neither yet formalized:**
(a) **monotone-in-z** — numerically `det(z)` is *strictly decreasing in z* with `det(∞)=1`
(`verify_q0_det_positivity.py monotone_in_z_scan`: 0 genuine violations over 28 000 trials), so
`det(z) > det(∞) = 1 > 0`; splits into `lim_{z→∞} det = 1` (a limit computation, `f,g→0`) and
`d(det)/dz < 0` (a derivative-sign lemma, the harder half). (b) the sharp
`det ≥ 1 ⟺ a+d ≥ bc−ad` bound (the `O(ρ²) ≤ O(ρ)` estimate under `η<1`). `bc ≥ ad` (M.8) is the
key available tool. Full derivation in `Q0DetRankTwo.lean` and
`numerical_notes/{theory,results}/q0_det_positivity.md`.

Key results in `LeanCode/YukawaDCF/Q0DetRankTwo.lean` (`namespace FMSA.MatrixQ0`):
- `p1_neg`, `mAux_neg`, `nAux_neg` (proved): one-variable sign facts underlying `fFun`/`gFun`
- `fFun_neg`, `gFun_neg` (proved): `fFun,gFun < 0` for all physical `σ,z>0`
- `Umat`, `Vmat` (defined): the rank-2 factors
- `Q0_mat_phys_eq_one_sub_mul` (proved): `Q0_mat_phys = 1 - U·V`, entrywise algebra
- `Q0_mat_phys_det_eq_two_by_two` (proved): reduces to `det(1 - V·U)` via `det_one_sub_mul_comm`
- `VU_apply_00` (proved): `(V·U) 0 0 = Σⱼ ρⱼ·fFun(...)` — the exact-cancellation identity
- `Q0_mat_phys_isUnit_det_of_two_by_two` (proved, conditional on `hdet`): the final theorem —
  `IsUnit (Q0_mat_phys z sigma rho).det` given the one scalar inequality `hdet` above

**Depends on:** Task M.3 (motivates the unconditional question); Task 2.2's
`p(0)=0,p'(0)=0,p''>0` derivative-chain technique, reused for `p1_neg`/`mAux_neg`/`nAux_neg`.

**Status:** ◑ conditional — `LeanCode/YukawaDCF/Q0DetRankTwo.lean`, no axiom/sorry, but the
final theorem carries the one open scalar inequality as an explicit hypothesis rather than a
proved fact. See `todo_lean.md`'s "Numerically verified — not proved in Lean" section.

---

### Task M.5 — `nAux = mAux/2` and the g/f decomposition

**Statement:** For all `u`, `nAux u = mAux u / 2`, where (as in `Q0DetRankTwo.lean`)
`mAux(u) = (2−u) − e^{−u}(u+2)` and `nAux(u) = (1−u/2) − e^{−u}(1+u/2)`.

**Why it matters:** it collapses the σ-dependence of the ratio `g/f`. Using the proved
`f_identity`/`g_identity` (`σp₁+2p₂ = mAux(zσ)/z³`, `σp₁/2+p₂ = nAux(zσ)/z³`), M.5 gives the clean
form (with `u=zσ`, mixture constant `β=πξ₂/vac`):
```
g/f = πξ₂/(2·vac) + z · P1(zσ)/mAux(zσ)          [P1(u)=1−u−e^{−u}]
```
so the only species-varying part of `g/f` is the single ratio `P1/mAux` (Task M.7).

**Proof sketch:** pure ring identity — `nAux u − mAux u/2 = 0` by expanding both (verified in
`q0_det_analysis.py`, `sympy.simplify == 0`). In Lean: `unfold nAux mAux; ring`. The `g/f`
decomposition then follows from `f_identity`, `g_identity`, and `field_simp; ring`.

**Depends on:** the existing `mAux`, `nAux`, `p1`, `p2`, `f_identity`, `g_identity` defs/lemmas in
`Q0DetRankTwo.lean`.

**Status:** ✓ DONE — `theorem nAux_eq_mAux_div_two` (`Q0DetRankTwo.lean`), axiom-clean
(`unfold nAux mAux; ring`). The g/f decomposition is realized by `gFun_ratio_eq` (private, used in M.8).

---

### Task M.6 — `cosh u > 1 + u²/2` for `u > 0`

**Statement:** `Real.cosh u > 1 + u^2/2` for all `u > 0` (equivalently `u² − 2·cosh u + 2 < 0`).

**Why it matters:** this is exactly the sign of the Wronskian numerator behind M.7
(`eᵘ·W = u² − 2cosh u + 2`), hence the engine of the `g/f` monotonicity and ultimately `bc ≥ ad`
(M.8).

**Proof sketch:** `cosh u = Σ_{k≥0} u^{2k}/(2k)! = 1 + u²/2 + u⁴/24 + …`, so
`cosh u − (1 + u²/2) = Σ_{k≥2} u^{2k}/(2k)! > 0` for `u>0`. In Mathlib, either from the series,
or via the `p(0)=0, p'(0)=0, p''(u)=cosh u − 1 > 0` derivative-chain technique already used for
`mAux_neg`/`nAux_neg`/`p1_neg` (apply it to `p(u) = cosh u − 1 − u²/2`, with
`p'(u)=sinh u − u`, `p''(u)=cosh u − 1 > 0` for `u>0`).

**Depends on:** Mathlib `Real.cosh` lemmas (`Real.add_one_le_exp`, `Real.cosh_pos`, or series), or
the Task 2.2 derivative-chain infrastructure.

**Status:** ✓ DONE — `theorem one_add_half_sq_lt_cosh` (`Q0DetRankTwo.lean`), axiom-clean. Proved via
the derivative chain (not the series): `coshGap = cosh − 1 − u²/2`, `coshGap1 = sinh − id`,
`coshGap2 = cosh − 1 > 0` (`Real.one_lt_cosh`), two applications of
`strictMonoOn_of_hasDerivWithinAt_pos` (mirrors `mAuxNeg`).

---

### Task M.7 — `P1/mAux` strictly decreasing on `(0,∞)`

**Statement:** the map `u ↦ P1(u)/mAux(u)` is strictly decreasing on `(0,∞)`
(`P1(u)=1−u−e^{−u} < 0`, `mAux(u) < 0`, so the ratio is positive).

**Why it matters:** with M.5, `g/f = β/2 + z·P1/mAux`, so `P1/mAux` decreasing ⟹ `g/f` strictly
decreasing in σ — the input to M.8.

**Proof sketch:** the sign of `(P1/mAux)'` equals the sign of the Wronskian
`W = P1'·mAux − P1·mAux'` (since `mAux² > 0`). A `ring`-level computation gives
`eᵘ·W(u) = u² − 2·cosh u + 2`, which is `< 0` for `u>0` by **M.6**; hence `W < 0` and the ratio is
strictly decreasing. (`eᵘ·W = u² − 2cosh u + 2` verified in `q0_det_analysis.py`.)

**Depends on:** M.6; `mAux`, `P1` defs; a monotonicity-from-derivative lemma
(`StrictAntiOn` via `deriv < 0`).

**Status:** ✓ DONE — `theorem ratioPM_strictAntiOn` (`Q0DetRankTwo.lean`, the ratio is named
`ratioPM = pAux/mAux`, `pAux u = 1−u−e^{−u}`), axiom-clean. `hasDerivAt_pAux`/`hasDerivAt_mAux` +
`HasDerivAt.div`; `wronskian_neg` proves `eᵘ·W = u²−2cosh u+2 < 0` via
`linear_combination (2−e^{−u}+u²)·(eᵘe^{−u}=1)` and M.6; `strictAntiOn_of_hasDerivWithinAt_neg`.

---

### Task M.8 — `g/f` decreasing ⟹ `bc ≥ ad` (all N)

**Statement:** for a physical mixture, the negated 2×2 moment entries `a=−Σρf, b=−Σρg, c=−Σρσf,
d=−Σρσg` satisfy `ad − bc ≤ 0`, i.e. **`bc ≥ ad`**, for every N (equality only at N=1 or coincident
diameters).

**Why it matters:** this turns M.4's informal "not simple Cauchy–Schwarz (`bc` can exceed `ad`)"
into a theorem: `bc ≥ ad` **always**, so det-positivity can never come from the `ad ≥ bc`
direction — it must use the `1+a+d` slack. It is the clean structural core of the M.4 gap.

**Proof sketch:** by Cauchy–Binet on `M̃ = V·U` (2×N times N×2),
```
ad − bc = det M̃ = Σ_{j<k} ρⱼρₖ (σₖ − σⱼ)(FⱼGₖ − FₖGⱼ),   F=−f>0, G=−g>0.
```
`FⱼGₖ − FₖGⱼ = FⱼFₖ·((G/F)ₖ − (G/F)ⱼ)`, and `G/F = g/f` is strictly decreasing (M.5+M.7), so for
`σⱼ < σₖ` the factor `(σₖ−σⱼ)` and `((G/F)ₖ−(G/F)ⱼ)` have opposite signs ⟹ every summand `≤ 0` ⟹
`ad − bc ≤ 0`. (The N=2 Cauchy–Binet identity and the `≤0` sign are verified symbolically and over
20 000 trials in `q0_det_analysis.py` / `verify_q0_det_positivity.py`.)

**Depends on:** M.5, M.7 (`g/f` decreasing); the Cauchy–Binet / `Matrix.det` expansion of `V·U`
(`Finset.sum` rearrangement, or Chebyshev's sum inequality for the 2×2 case).

**Status:** ✓ DONE — `theorem moment_ad_le_bc` (`Q0DetRankTwo.lean`), axiom-clean. Realized via
`gFun_ratio_eq` (`gFun = fFun·(πξ₂/(2vac)+z·ratioPM(zσ))`), `cross_nonpos` (each Cauchy–Binet
summand `≤0`, using `ratioPM_strictAntiOn` through `antiOn_mul_diff_nonpos`), then the double-sum
rearrangement `2·(ad−bc) = ∑ⱼₖ ρⱼρₖ(σₖ−σⱼ)(fⱼgₖ−fₖgⱼ)` (`Finset.sum_mul_sum`/`sum_comm`) with
`Finset.sum_nonpos`. Holds for any `ξ₂` (needs only `ρ≥0, σ>0, z>0, vac>0`). Does **not** close M.4
— the main `det>0` still needs the `1+a+d` slack bound; but it closes the "is it Cauchy–Schwarz?"
question negatively (`bc ≥ ad` always) and is a reusable structural lemma.

---

