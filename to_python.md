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
to K·(1−g²)·exp(−z(r−d)) + ... (the FMSA_pure formula). Dependencies: B.2, M.3/M.4.
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

**Status (2026-07-15):** the concrete derivation of `b_{ij}` now lives in **Group Y1** (the ε¹ analog
of Group BAXTER). Done: complex `Q̂₀(s)` (Y1.1), single/multi-tail `b_{ij}` residue (Y1.5),
assembly `Ĥ₁` (Y1.6), and the Wiener–Hopf support lemmas (Y1.3a, `WHSupports.lean`). The remaining
open piece is the Wiener–Hopf projection derivation (Y1.3b, FT injectivity), re-routed off the
Hilbert transform. See [proof_notes_yukawa_wh.md] (Group Y1).
