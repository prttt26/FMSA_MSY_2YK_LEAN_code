# Phase 0 spec — the Blum–Høye exact-MSA derivation, mapped to the repo (GO)

**Sources.** Exact MSA: **Blum & Høye 1978**, *J. Stat. Phys.* 19, 317 (pp. 320–322 rendered,
`pdf/sources_paywall/Solution of the Ornstein-Zernike equation with Yukawa closure for a mixture.pdf`).
First-order structure (Tang & Lu 1995): `lecture_notes_OZ_Yukawa_poly.pdf` (§5–7). The repo's `bhF`
is the **exact** (quadratic-in-(Dt,G)) system = BH, NOT the first-order lecture-notes theory.

## GO decision: **GO.**

The derivation is Laplace-transform-of-convolution + coefficient-matching + 2×2 linear algebra — the
same class of work as the completed M3/M4. Every BH object maps to an existing repo `def`, and the
two target equations (29)/(33) are exactly `h29`/`h33`. No OZ/Fourier rebuild is needed; the missing
lemmas are the *derivations* connecting the OZ integral equations (8),(9) to the closed forms.

## The exact real-space Baxter function (BH Eqs 10–12)

```
r < σ :  Q(r) = ½(r−σ)² q''  +  (r−σ) q'  +  C(e^{−zr} − e^{−zσ})  +  D e^{−zr}
r > σ :  Q(r) = D e^{−zr}
```
(scalar N=1, σ=1). Continuity `Q(σ⁻)=Q(σ⁺)=D e^{−zσ}` is built in (the `−e^{−zσ}` kills the C-exp at
σ; the poly vanishes at σ). Support from `λ = 0` (N=1). **The exp part is `C(e^{−zr}−e^{−zσ}) + D
e^{−zr}`, not `D e^{−zr}` alone** — this resolves the "G-entangled tail": `C` is RDF-coupled (Eq 27),
so the `C(e^{−zr}−e^{−zσ})` Laplace moment IS the repo's `tailtil`.

## Equation ↔ repo map (all verified against the defs)

| BH eq | statement | repo object |
|---|---|---|
| (22) | `φ₁(x)=(1−x−e^{−x})/x²`, `φ₂(x)=(1−x+½x²−e^{−x})/x³` | `phi1 z`, `phi2 z` (x=z) ✓ |
| (25) | PY coeffs `q⁰′, A⁰, B⁰` | `qp0`, `bA0`, `bB0` ✓ |
| (23) | `A = A⁰(1+M) − 4σ⁻²B⁰N`, `B = B⁰(1+M)+[A⁰+4σ⁻¹B⁰]N` | `msaA` ✓ (σ=1) |
| (24) | `q' = q⁰′(1+M) + A⁰N` | `msaQp` ✓ |
| (20) | `M = Σρe^{−λz}[zσ²e^{−zσ}φ₁(−zσ)C − D/z]` | `Mtil·Dt` (after C via (27)) |
| (21) | `N = Σρe^{−λz}{ze^{−zσ}σ²[σφ₂(−zσ)−λφ₁(−zσ)]C + (1+zλ)z⁻²D}` | `Ntil·Dt` |
| (27) | `−C = Σ[δ − 2πρĝ(z)/z]D` | ties C to RDF moment ĝ(z) ⇒ G |
| (35) | `γ = δ − 2πρ ĝ(z) z` | `gam` (identification, RDF moment) |
| (28)/(16) | `ĝ(s)=∫₀^∞ e^{−sr}r g(r)`, `Q̂(s)=∫_λ^∞ e^{−st}Q(t)` | RDF / Baxter Laplace moments |
| **(29)** | `2πK/z = Σ_l D_il[δ_lj − ρ_l Q̂_jl(z)]` | **h29**: `2πK/z = Dt·bhF`, bhF=1−ρQ̂(z) |
| **(33)/(34)** | `Σ 2πĝ_il(z)[δ−ρQ̂] = e^{−zσ}·{dressed}` | **h33**: `2πG·bhF = bhP` |

## Derivation chains (the missing lemmas)

**h29 (Eq 29) — from Eq (8) at r>σ.** Eq (8) is the Baxter `2πr c(r) = −Q'(r)+2πρ∫Q'Q(·+r)`.
For r>σ, matching the `e^{−zr}` coefficient gives `2πK/z = Dt(1−ρQ̂(z)) = Dt·bhF`. My **M3**
(`baxter_exterior_moment_form`, exterior RHS `= z Dt e^{−zr}(1−M_full)`) + **M4**
(`bhF_eq_one_sub_dressed_moment`, bhF=1−ρQ̂(z)) already supply both sides — provided the tail moment
in M_full is upgraded to the exact `C(e^{−zr}−e^{−zσ})+D e^{−zr}` (Phase 3). **⇒ Phase 4 is short.**

**h33 (Eq 33/34) — from Eq (9)/(32), Laplace at s=z.** Eq (32) is the OZ convolution integral
equation for g at r>σ; Laplace-transform (Eq 33), set s=z (Eq 34) ⇒ `2π ĝ(z)(1−ρQ̂(z)) = e^{−zσ}·{
dressed A/q'/γ}` = h33. Needs: the OZ convolution (32) as a Lean statement (check `oz_*` machinery)
+ the dressed RHS (Phase 2).

**Coefficients (Eqs 13,14,17,18,20,21) — from Eq (9) at r<σ.** Matching constant + r + e^{−zr}
coefficients of Eq (9) gives the linear system (17)/(18) for A,B and (20)/(21) for M,N in terms of
C,D. Solve 2×2 (Eq 23) ⇒ `msaA`/`msaQp`. **Pure linear algebra + field_simp;ring.**

## Refined phase notes

- **Phase 1 (γ):** Eq (35) is a *definition* (γ ≡ the RDF moment δ−2πρĝ(z)z), not a derivation. The
  repo `gam` uses G = a scaled ĝ(z); Phase 1 = pin the `gam` ↔ ĝ(z) identification. LOW.
- **Phase 2 (M,N → msaQp/msaA):** Eqs (20)/(21) [M,N from C,D] + (27) [C from ĝ] + solve (17)/(18).
  The 2×2 solve (23)/(24) is `ring`; the inputs (20),(21),(27) come from the r<σ coefficient match of
  Eq (9). MEDIUM-HIGH (the coefficient match is the real content).
- **Phase 3 (tailtil):** the `C(e^{−zr}−e^{−zσ})+D e^{−zr}` Laplace moment, C via (27). Its moment IS
  `Dt·ρ·tailtil` (M4 residual) — now with a *physical* real-space origin (the C-exp), not vacuous.
- **Phase 4 (h29):** M3+M4+Phase 3, e^{−zr} coeff of Eq (8). SHORT.
- **Phase 5 (h33):** OZ conv (32) Laplace at s=z. Check `oz_*` for (32). MEDIUM-HIGH.
- **Phase 6:** wire into `exactMSA_factorization`.

**Net transcription after the program:** h29/h33 ⟸ the OZ integral equations (8),(9) + MSA closure
(2),(34) + Baxter factorization — standard SM primitives (the repo has much of the OZ/Baxter side).

**Print-error caution** (memory `reference_ln_deviates_from_tanglu1995`, `fmsa_is_first_order_msa`):
the lecture notes are first-order and have a known `H̃₁=Ĥ₁` error; BH 1978 itself has 3 print errors
(z-power in (36), z-inversion in (35), e^{zσ} in (29) per `waisman_msa_closed_form.md`). Cross-check
every transcribed coefficient numerically before proving (the repo `def`s already encode the
corrections — trust `MSABlumHoyeSystem`/`MSABaxterKSpace`, verify against BH by value).
