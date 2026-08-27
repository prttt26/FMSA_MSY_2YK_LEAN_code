# leg-3 g-side (Blum–Høye Eq. 9) — the spec for `h33` and the coefficient equations

**Purpose.** Phase 4 closed `h29` (`h29_of_baxter_exterior`, commit `564b4f2`) from Baxter's
**DCF** relation Eq. (8) at `r > σ` + the MSA exterior closure. `h33` and the interior coefficient
equations come instead from Baxter's **g-side** relation **Eq. (9)** — the actual Yukawa OZ integral
equation. This note pins the exact equations (transcribed from
`pdf/sources_paywall/Solution of the Ornstein-Zernike equation with Yukawa closure for a mixture.pdf`,
Blum & Høye 1978, JSP 19 317, pp. 320–322, rendered at 190 dpi) and the roadmap, and records the
**measured normalization caveat** that blocks a literal transcription.

## The exact Baxter function (Eqs 10–12, `N=1`, drop index `n`)

    Q_ij(r) = Q⁰_ij(r) + D_ij e^{−zr}                                             (10)
    Q⁰_ij(r) = ½(r−σ_ij)² q''_ij + (r−σ_ij) q'_ij + C_ij(e^{−zr} − e^{−zσ_ij})    (11)   for λ_ji < r < σ_ji
    λ_ji = ½(σ_j − σ_i)  (= 0 at N=1)                                             (12)

`Q⁰` is COMPACT (support `[λ, σ]`); the `D e^{−zr}` tail is over the full half-line (generates the
`s=−z` pole). Continuity of `Q⁰` at `r=σ` (⟸ Eq. 8) is built in: poly(σ)=0 and `C(e^{−zσ}−e^{−zσ})=0`.
This is exactly `bhCoreFn` (= `Q⁰`, ρ/eᶻ-normalized) + `bhBaxterFn` (= `Q`) from Phase 4.

## The two master relations (Eqs 8, 9)

* **Eq. (8)** = the DCF Baxter relation. At `r > σ`: `2πK_ij/z = Σ_l D_il[δ_lj − ρ_l Q̂_jl(z)]` = **Eq.
  (29) = `h29`** (Phase 4, DONE). Also forces `Q⁰` continuity at σ.
* **Eq. (9)** = the g-side OZ integral equation. Real-space forms:

      r < σ:  0 = 2πr − Q'_ij(r) − 2π Σ_l ρ_l ∫_{λ_jl}^∞ dt (r−t) Q_il(t)
                    + 2π Σ_l ρ_l ∫_r^∞ dt (r−t) g_il(|r−t|) Q_lj(t)              (30)
      r > σ:  2πr g_ij(r) = 2πr + z D_ij e^{−zr} − 2π Σ_l ρ_l ∫_{λ}^∞ (r−t)Q_il(t)
                    + 2π Σ_l ρ_l ∫_λ^∞ (r−t) g_il(|r−t|) Q_lj(t)                 (31)
      subtract analytic-cont. of (30) from (31):
      2πr g_ij(r) = (r−σ)q''_ij + q'_ij − z C_ij e^{−zr}
                    + 2π Σ_l ρ_l ∫_λ^r dt (r−t) g_il(|r−t|) Q_lj(t)              (32)

  **`g(r)` appears on BOTH sides** — the OZ nonlinearity. There is **no exterior closure for `g`**
  (unlike `c(r>σ)=cMSAtail` for `h29`), so `h33` cannot shortcut through a known LHS; the convolution
  `∫(r−t) g Q` must be engaged. That is why `h33` is a genuinely larger build than `h29`.

## Where each equation comes from (page 320, verbatim structure)

Matching coefficients of Eq. (9) at `r < σ` using the ansatz (10)/(11) + core condition `g(r<σ)=0`:
* **constant term** → Eq. (13) `A_j = q''_ij = 2π[1 − Σρ T₀]`
* **`r` term** → Eq. (14) `B_j = −σq''_ij + q'_ij = 2π Σρ T₁`  (⇒ `q' = B + σA`; at σ=1, `q'=B+A`)
* **`e^{−zr}` term** → Eq. (27) `−C_ij = Σ_l[δ_il − 2πρ_l ĝ_il(z)/z] D_lj`   (= `C = −gam·D` at N=1)

with moments `T_n = ∫_λ^∞ tⁿ Q(t) dt = (−∂/∂s)ⁿ Q̂(s)|₀` (15), `Q̂(s)=∫_λ^∞ e^{−st}Q(t)dt` (16),
`ĝ(s)=∫₀^∞ e^{−sr} r g(r) dr` (28). Solving (17)/(18) gives the dressed `A_j`/`q'_ij` = Eqs (23)/(24)
= `msaA`/`msaQp` (already `msaCoeff_continuity_17`/`_18`, Phase-2 linear half).

**`h33` = Eq. (34)** = the Laplace transform of Eq. (9)/(32), at `s = z`:

    Σ_l 2π ĝ_il(z)[δ_lj − ρ_l Q̂_lj(z)]
      = e^{−zσ}{ (A⁰+z q⁰')(1+M) + (−4σ⁻²B⁰ + zA⁰)N + (z²/2)e^{−zσ} Σ_l γ_il D_lj }        (34)
    γ_ij = δ_ij − 2πρ_j ĝ_ij(z) z    (35, DIFFERENT from the Eq-27 bracket `gam`)

At `N=1`: LHS `= 2π ĝ(z)·bhF` (with `bhF = 1−ρQ̂(z)`), and `(A⁰+zq⁰')(1+M)+(−4B⁰+zA⁰)N = msaA + z·msaQp`.

## ⚠ MEASURED CAVEAT — do NOT transcribe (33)/(34) literally

The repo's `bhF`/`bhP`/`gam` are the **numerically-corrected** forms (memory:
`fmsa_is_first_order_msa`, "BH 1978 has 3 print errors, trust repo defs, verify by value"). The repo
target is `h33 : 2π G·bhF = bhP`, `bhP = (msaA + z·msaQp + (z²/2)·gam·Dt)/z²`, with `ĝ(z)=G e^{−z}`
(so repo `G = ĝ(z) eᶻ`) and `gam` the **Eq-27 bracket** `1−2πρG e^{−z}/z` (not the Eq-35 `γ`).

A hand-transcription of Eq. (34) — `2πĝ(z)bhF = (e^{−z}/z²)[msaA + z msaQp + (z²/2)e^{−z}gam·Dt]`,
i.e. LHS `2πG e^{−z} bhF`, and the C-term carrying an extra `e^{−z}` — was checked against the repo
residual `2πG·bhF − bhP` at 6 random OFF-manifold points (`h33_pin.py`): the two residuals are
**NOT proportional** (ratios 43/10358/13125/6/384/12 ≈ eᶻ but drifting 0.86–1.03×eᶻ), so the literal
transcription is wrong by an `(xi,z,Dt,G)`-dependent factor. **Conclusion:** derive `h33` through the
repo's consistent normalization via the real-space route (like `h29`), NOT by matching BH's printed
(33)/(34). Both residuals vanish on the solution manifold (both are the same constraint there), but
only the repo `bhP` is trustworthy off it.

## ⭐ The poly/C split — worked out (2026-08-27): the poly part is CLEAN, the C-term is the obstruction

Eq. (33) at `s = z`, `N=1`, `σ=1` reads `2πĝ(z)·bhF = L_z[((r−σ)q'' + q' − zC e^{−zr})·Θ(r>σ)]`, the
Laplace transform of the exterior g-source (the OZ convolution having folded into the LHS via the
convolution theorem `L[(rg)∗Q] = ĝ·Q̂`). Working out each piece with `ĝ(z)=G e^{−z}`, `q''=msaA`,
`q'=msaQp`, `C=−gam·Dt` (Eq 27):

* **LHS** `= 2πĝ(z)·bhF = 2π G e^{−z}·bhF`.
* **poly part** `L_z[((r−1)msaA + msaQp)Θ(r>1)] = msaA·e^{−z}/z² + msaQp·e^{−z}/z`
  (exterior transforms: `∫_1^∞(r−1)e^{−zr}=e^{−z}/z²`, `∫_1^∞ e^{−zr}=e^{−z}/z`).
* **C-term** `L_z[−zC e^{−zr}·Θ(r>1)] = −zC·e^{−2z}/(2z) = (gam·Dt)·e^{−2z}/2`.

Dividing the whole relation by `e^{−z}`:

    2πG·bhF  =  msaA/z² + msaQp/z + (gam·Dt/2)·e^{−z}          (derived from Eq 33)

versus the **repo target**

    bhP      =  msaA/z² + msaQp/z +  gam·Dt/2                  (h33 : 2πG·bhF = bhP)

**⇒ the polynomial part (`msaA/z² + msaQp/z`) matches EXACTLY and is cleanly derivable** — it is
`e^z ·` the exterior Laplace of `(r−σ)q'' + q'`, an FTC computation (Mathlib
`integral_Ioi_of_hasDerivAt_of_tendsto`, modulo an `Ioi` poly×exp integrability lemma). **Only the
C-term differs, by a factor `e^{−z}`** (`(gam Dt/2)e^{−z}` derived vs `gam Dt/2` in the repo). This is
exactly BH's known print-error zone (memory `fmsa_is_first_order_msa`: "z-power in (36), z-inversion
in (35), e^{zσ} in (29)") — the `γ`/`C`/`e^{±zσ}` normalization of the tail term. So:

> **h33 is derivable EXCEPT for the C/γ tail term, whose correct normalization the printed BH
> equations do not reliably give.** Resolving it needs the g-side derivation carried through in the
> repo's consistent normalization (re-deriving Eq 32→33's tail contribution), NOT transcription.

This mirrors Phase 4 exactly: there the poly moment was a genuine integral and the tail (`Dt·ρ·tailtil`)
was the residual closed form; here the poly Laplace is clean and the `gam·Dt/2` tail is the residual —
but for `h29` the residual was pinned by the exterior closure, while for `h33` no g-closure pins it.

## Roadmap for `h33` (the real build)

1. Define the RDF moment `ĝ(z)` (Eq 28) as a Lean object, and `Q̂(s)` (Eq 16) at general `s` (extend
   the Phase-4 core-moment lemmas from `s=z` to symbolic `s`; pure FTC).
2. State Eq. (9)/(32) as the physical hypothesis `hbax_g` (the g-side OZ relation), analogous to `h29`'s
   `hbax`. Its Laplace transform at `s=z` is the input.
3. Compute the Laplace transform of (32)'s RHS from `bhBaxterFn` in the repo normalization — this is
   where the OZ convolution `∫(r−t)gQ` enters; the `g` appears via `ĝ(z)`, closing the loop.
4. Match to get `2πG·bhF − bhP = 0`, all in repo-consistent normalization (so the caveat above is moot).

**Shared prerequisite** with the interior coefficient equations (Phase-2 OZ-half, #56): both need
Eq. (9)'s convolution machinery. Est: substantially larger than `h29` (which had the exterior closure
handed to it). Tracker: #59 (h33), #56 (coeff eqs), #61 (discharge the Eq-8/9 identities pointwise).

**Also available for free (Eq 38, contact value):** `g_ij(σ⁺) = [q'_ij − z C_ij e^{−zσ}]/(2πσ)` — an
algebraic route to `ĝ(z)`'s boundary data, and the Tang & Lu contact gate.
