## Route C (FMSA_HS_pole_residue) — Lean foundations

### GA.1 (formerly C.3): Unlike-pair two-exp base unbounded → Group GA / `proof_notes_failures.md` (not started)

**Lean result**: ∀ M, ∃ z R K, K·exp(z·R) ≥ M; additive correction sum Σ|Bₖ|·exp(−sₖ·r)
with |Bₖ| ≤ K/z² cannot cancel K·(1−G²)·exp(z·R) when z·R ≫ log(n).

**Python implication**: Confirms that adding HS-pole exponentials ON TOP OF K·(1−G²)·exp
cannot fix the 2YK divergence for any finite set of poles. The K·G·exp base
(Route C as implemented in `fmsa_hs_pole_residue.py`) is the only viable approach
within the perturbative MSA framework. Closes the dead-end of additive corrections.

### GA.2 (formerly C.4): G_{01}→0 exponential decay → Group GA / `proof_notes_failures.md` (optional, not started)

**Lean result**: [Q̂₀(z)⁻¹]_{01} → 0 as exp(−z·(σ₁−σ₀)/2) for large z·(σ₁−σ₀).

**Python implication**: Guarantees K·G₀₁·exp(−z(r−R)) ≤ K·C·exp(−z·(σ₁−σ₀)/2 + z·R₀₁)
stays bounded for all σ-ratios. For σ-ratio=2 (σ₁−σ₀=1): bound ∝ exp(−z/2) ≪ K·exp(z·R₀₁).
Validates that Route C's inner formula is well-conditioned for all σ-ratios ≥ 1.

### C.5 (MIGRATED 2026-07-15 → Group C): K·G·exp = exact MSA Yukawa-pole residue

**Lean statement**: In multicomponent Yukawa MSA (Blum 1975), the leading residue of
c^(1)_{ij}(r) at Yukawa pole s=z_t (from the Baxter–Wertheim Laplace inversion) is exactly

    c^(1)_{ij}(r)  ∋  K_t · [Q̂₀(z_t)⁻¹]_{ij} · exp(−z_t(r − R_{ij}))   for r < R_{ij}, i≠j

where [Q̂₀(z_t)⁻¹]_{ij} = G_{ij}(z_t) from the GA-matrix.

**Python implication**: Validates `get_c1_inner` in `fmsa_hs_pole_residue.py` at leading order.

Explains why ĉ₁₂ ≈ 0 for Route C at σ-ratio=2 (NOT a bug):
- G₀₁ ≈ 0 → inner K·G·exp contribution → 0 by construction
- Outer Yukawa: ĉ₁₂_outer = 2Σ_t K_t^(01)·(R₀₁/z_t + 1/z_t²); GA-matrix K₀₁ values are
  inaccurate for 2YK (same root cause as ĉ₂₂ = +8174 for like pair (2,2))
- Route C is NOT wrong — the GA-matrix K₀₁ values are wrong. Fix ĉ₁₂ requires better K₀₁
  (from poly-term, GCMC fit, or OZ self-consistency), not a different inner formula.

If C.5 is proved: inner formula confirmed exact at leading order; remaining error is entirely
from K₀₁ (outer region). If disproved: an additional inner-core term beyond K·G·exp is needed.

**Proof strategy**: Partial-fraction expansion of the Laplace-domain ĉ^(1)_{ij}(s) around
s=z_t; residue picks up [adj Q̂₀(z_t)]_{ij}/det Q̂₀(z_t) = G_{ij}(z_t). N=1 check: reduces
to K·(1−g²)·exp(−z(r−d)) + ... (the FMSA_pure formula). Dependencies: M.10, M.3/M.4.
Effort: medium-high (requires Blum 1975 Laplace-space formula or independent derivation).

#### ⚠ CORRECTION (2026-07-15) — the exact residue is `Q̂₀⁻¹·K·Q̂₀⁻ᵀ`, not `K·G`

Reading the **[LN] lecture notes** (Tang & Lu 1995, `pdf/lecture_notes_OZ_Yukawa_poly.pdf`) §6.4 to
the end (Eq. 73) and formalizing it (`LeanCode/YukawaDCF/SpectralAmplitude.lean`,
`spectralAmp_residue` + `spectralAmp_residue_n1`, axiom-clean) shows the spectral amplitude — the
residue-carrying object in `Ĥ₁ = [Q̂₀ᵀ]⁻¹ B₁ [Q̂₀]⁻¹` (Eq. 68) — is, for a single tail:

    b_{ij}(s) = [ Q̂₀(z)⁻¹ · K · Q̂₀(z)⁻ᵀ ]_{ij} / (s + z),

so the **exact** Yukawa-pole residue is `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` — `K` sandwiched by **two**
inverse-Baxter factors (doubly propagated). At N=1 this is `K·G²`, not `K·G`.

**Python implication (revised):** `get_c1_inner`'s `K·G·exp` is a **leading-order approximation** of
the exact `Q̂₀⁻¹·K·Q̂₀⁻ᵀ`, *not* the exact leading residue. The qualitative conclusions above still
hold (`G₀₁≈0` ⇒ inner contribution → 0; residual 2YK error in outer `K₀₁`), but if a higher-accuracy
inner formula is ever needed, use the doubly-propagated `Q̂₀⁻¹·K·Q̂₀⁻ᵀ` form (both `i` and `j`
propagated through `Q̂₀⁻¹`), not the singly-propagated `K·G`.

**Status (2026-07-15):** **Group Y1 COMPLETE (Y1.1–Y1.7, axiom-clean).** The concrete derivation
of `b_{ij}` is fully done: complex `Q̂₀(s)` (Y1.1), multi-tail `b_{ij}` residue tied to Q̂₀⁻¹
(Y1.5 `bMulti_residue_Qinv`), assembly `Ĥ₁` (Y1.6 `Hhat1_residue`), Wiener–Hopf projection
re-routed to real-space `1_{[R,∞)}·` (Y1.3a/b/c, axiom-clean), and inner-core `S₁` + origin
constraint + contact matching (Y1.7). See [proof_notes_yukawa_wh.md] (Group Y1).

---

### Y1.5 / Y1.6 (DONE, 2026-07-15): Lean-proved doubly-propagated amplitude

**Lean results**:
- `bMulti_residue_Qinv` (Y1.5, `YukawaDCF/SpectralAmplitude.lean`): for each Yukawa tail t and
  pair (i,j), ties the spectral amplitude to Q̂₀⁻¹: b_{ij}(z_t) = [Q̂₀(z_t)⁻¹·K_t·Q̂₀(z_t)⁻ᵀ]_{ij}
  (general multi-tail, distinct-z case, axiom-clean).
- `Hhat1_residue` (Y1.6, `YukawaDCF/YukawaWienerHopf.lean`): the first-order RDF
  Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹ (Eq. 68) has (i,j) residue at pole z_t equal to
  [Q̂₀(z_t)⁻¹·K_t·Q̂₀(z_t)⁻ᵀ]_{ij}.

**Python implication (new method)**: The inner-DCF Yukawa-pole base for unlike pairs must use
the doubly-propagated amplitude. In Python (already tested in `test_ml_convergence.py` Part B):

```python
Q0inv = ga._Qinv_mat[t, 0, 1]           # shape (N,N) — Q̂₀(z_t)⁻¹
amp_dp = (Q0inv @ ga.K[t] @ Q0inv.T)[0, 1]   # doubly-propagated [Q̂₀⁻¹·K·Q̂₀⁻ᵀ]₀₁
```

Numerical values at 2YK state point (σ=[1,2], ρ*=0.139, T*=1.0):
- tail 0: singly-propagated K·G₀₁ = −0.0165; doubly-propagated = +0.245 (×14.8, sign flip)
- tail 1: singly-propagated K·G₀₁ ≈ 0; doubly-propagated = +1.840 (×47M)

**Open question for Python**: Replacing the Yukawa base in `get_c1_inner` from `K·G₀₁·exp` to
`amp_dp·exp` WITHOUT updating B_k gives ĉ₁₂ ≈ +4.5×10⁵ (catastrophic, see
`test_ml_convergence.py` Part B). The correct B_k^{new} must be determined from MML.3 before
the doubly-propagated base can be used in `fmsa_hs_pole_residue.py`. ML-OZ fit (archived,
`old/fmsa_ml_oz_fit.py`) showed B_k^{new} from OZ are ×22–52 larger than current B_k (but the
OZ fit is circular and gives all-orders B_k, not first-order FMSA B_k).

---

### Y1.7 (DONE, 2026-07-15): Origin constraint validates `_precompute_p0`

**Lean result**: `origin_constraint_eq76` (Y1.7, `YukawaDCF/YukawaInnerCore.lean`): the [LN]
Eq. 76 origin constraint `p₀ = −E_{ij}(0)` is proved, where E_{ij}(0) is the Yukawa-base + HS-pole-sum
evaluated at r=0 (reuses Group 5.1 `ContactMatching.lean` + `P.2` `OriginConstraint.lean`).

**Python implication**: `FMSA_HS_pole_residue._precompute_p0` (`fmsa_hs_pole_residue.py:120–153`)
implements exactly `p₀ = −(Yukawa base at r=0 + Σ_k 2·Re[B_k])`. Lean confirms this is the
**exact** origin constraint (not an approximation). When B_k is updated to B_k^{new} (after MML.3),
`_precompute_p0` automatically gives the correct p₀^{new} with no code change.

For the **shifted basis** `(exp(-z_t r) - 1)` (the new doubly-propagated method), p₀ is automatic
(each basis function vanishes at r=0), so `_precompute_p0` becomes unnecessary. Lean Y1.7 confirms
this: the shifted basis satisfies Eq. 76 trivially.

---

### M.8 (DONE, 2026-07-15): bc ≥ ad confirms det(Q̂₀) > 0

**Lean result**: `moment_ad_le_bc` (M.8, `HardSphere/Q0DetRankTwo.lean`): for all N components
and all z > 0, bc ≥ ad (Cauchy–Binet identity + Wronskian argument, no axiom/sorry). Together with
M.4 (axiom `Q0_moment_det_pos`): det(Q̂₀(z)) > 0 for all physical z > 0.

**Python implication**: The `_Qinv_mat[t]` matrix inversion in `fmsa_ga_matrix_mix.py`
(`np.linalg.inv(Q0)`) is always numerically stable — Q̂₀ is never singular on the positive real
axis. No need for a fallback or regularization in `_G_mat`/`_A_mat`/`_Qinv_mat` computation.
Also: for N=2, [Q̂₀⁻¹]₀₁ = -Q̂₀₀₁/det where det ≥ 1 > 0 (from M.4+M.8).

---

### MML.1 / MML.2 (not yet started): Adjugate formula and B_k residue

**Lean results** (planned, `todo_lean.md` Groups MML/MZERO/MPOLY):
- MML.1 (trivial): `adj(Q̂₀)₀₁ = −Q̂₀₀₁` and `[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁/det(Q̂₀)` for 2×2,
  via `Matrix.det_fin_two`/`adjugate_fin_two`.
- MML.2 (medium): `Res_{s=s_k}[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` from `residue_of_simple_pole`
  (already in `BaxterResidue.lean`) + MML.1.

**Python implication (MML.1)**: Validates `_Qinv_mat[t, 0, 1]` analytically for N=2:
`ga._Qinv_mat[t, 0, 1][0, 1] == -Q0[0, 1] / np.linalg.det(Q0)` (can add an assertion).

**Python implication (MML.2)**: The singly-propagated B_k formula in `_precompute_residues`:
```python
B[k, i, j] += K_t * adj_k[i, j] / ((z_t**2 - sk**2) * dp_k)
```
is exactly `K_t × [−Q̂₀₀₁(s_k)/det′] / (z_t²−s_k²)` = MML.2 residue × Yukawa coupling denominator.
Lean MML.2 would formally prove this formula is the correct HS-pole residue.

**Open question (for MML.3)**: Whether this singly-propagated B_k pairs correctly with the
doubly-propagated Yukawa base to give the correct inner DCF. From `test_ml_convergence.py`:
naive pairing gives ĉ₁₂ ≈ +4.5×10⁵ (wrong). Possible resolutions:
(a) MML.3 uses a doubly-propagated B_k^{new} = adj·K·adj^T / (det')² (derivable from MML.2 × MML.1)
(b) The singly-propagated B_k is correct for MML.3 but requires an exact cancellation proven by MZERO.1
(c) MML.3 does not use doubly-propagated Yukawa base — the "Yukawa poles" in MML.3 are different
    from what Y1.5/Y1.6 establish (separate derivation path via Y1.3's inner-core Laplace)
Resolution requires MML.3 proof; until then, Python B_k^{new} must come from OZ (circular) or
from proving MML.3 first.
