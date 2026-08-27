# leg-3 → exact h29/h33: the Blum–Høye real-space derivation (phased plan)

**Why this exists.** leg-3 (`MSABlumHoyeDerivation.lean`) has taken the exterior-convolution /
faithfulness-bridge route as far as *algebra* allows:

| done | result |
|---|---|
| M1–M2b | K-side + overlap integrals + hard-sphere bridge `qhat0_eq_laplace_q0poly` |
| M3 | general moment form `baxter_exterior_moment_form` — exterior RHS `= z Dt e^{−zr}(1−M_full)`; reduces (29) to the definitional `bhF = 1 − M_full` |
| M4 | **exact** `bhF_eq_one_sub_dressed_moment`: `bhF = 1 − (∫₀¹ dressed-poly e^{−zt} + Dt·ρ·tailtil)` (polynomial half a genuine integral theorem) |
| Phase 2 (lin.) | `msaCoeff_continuity_17`/`_18`: the dressed `(A,q')` satisfy the BH (17)/(18) continuity system (linear-algebra half; OZ-derivation half still open) |
| Phase 3 | `tailtil_eq_integral_form` + `bhF_eq_one_sub_full_integral`: `bhF = 1 − (both halves as genuine Laplace integrals)`, tail via the C-exp `(e^{−zr}−e^{−zσ})`, `γ = gam` = Eq-27 bracket |
| **Phase 4 ✅** | **`h29` DERIVED** (`h29_of_baxter_exterior`, axiom-clean): built the concrete exact Baxter fn `bhBaxterFn = bhCoreFn + D e^{−z·}` (`D=ρDt eᶻ`, `C=−ργDt eᶻ`); its exterior Baxter relation `bh_exterior_baxter_relation` = Eq (8) RHS `= z D e^{−zr}·bhF`; matching `cMSAtail` gives `Dt·bhF = 2πK/z`. **`h29` is now a theorem given Eq (8).** |

**Measured hard fact.** `h29`/`h33` are **constraints, not identities**: `2πG·bhF − bhP` is nonzero at
generic `(Dt,G)` (−7.6/−7.9/+5.3/+10.6), zero only on the solution manifold. So they **cannot** be
proved by `ring`/`field_simp`. The only route is the real-space OZ+MSA+Baxter derivation — which
reduces the trusted transcription from "`h29`/`h33` (BH's algebraic equations)" down to
"OZ equation + MSA closure + Baxter factorization" (standard SM primitives the repo *largely already
has* as theorems).

**De-risking fact.** The repo already carries `baxter_wiener_hopf_factorization`,
`exactMSA_factorization`, `factorization_of_core`, ~30 `oz_*` lemmas (`oz_core_closure`, `oz_h_core`,
`oz_fourier_oz_eq_of_core_closure`, …), RDF/contact lemmas, and `lecture_notes_OZ_Yukawa_poly.pdf`.
So this is **connect existing machinery to the Yukawa dressing**, not rebuild OZ.

## Phase DAG (tracker #54–#60)

```
 #54 Phase 0  map machinery + pin real-space forms  (GO/NO-GO gate)
      ├── #55 Phase 1  core closure g(r<σ)=0 → γ  (RDF moment)
      │        ├── #57 Phase 3  tail real-space form → tailtil moment  (closes M4 residual)
      │        └── #59 Phase 5  RDF moment → h33  (2πG·bhF = bhP)
      └── #56 Phase 2  σ-continuity → dressed coeffs msaQp/msaA (M,N)
               └── #57 Phase 3 …
 #57 → #58 Phase 4  exterior match → h29  (Dt·bhF = 2πK/z)
 {#58,#59} → #60 Phase 6  wire into exactMSA_factorization, retire h29/h33
```

| # | phase | target lemma(s) | est | risk |
|---|---|---|---|---|
| 54 | 0 map+pin (gate) | spec doc: existing↔needed | ~1 sess | low code, high value |
| 55 | 1 γ from core | `gam_eq_of_core_closure` | 1–2 | γ may be irreducible RDF spec |
| 56 | 2 continuity→M,N | `dressed_coeffs_of_continuity` | 2–3 | the continuity system (crux) |
| 57 | 3 tail moment | `tail_moment_eq_tailtil`, `bhF_eq_one_sub_full_moment` | 1–2 | amplitude must be physical, not vacuous |
| 58 | 4 h29 | ✅ `h29_of_baxter_exterior` DONE, axiom-clean | — | rests on `hbax` = Eq (8) exterior identity |
| 59 | 5 h33 | `h33` (thm) | 2 | constraint ⇒ needs RDF machinery |
| 60 | 6 wire-in | unconditional `exactMSA_factorization` (N=1) | 0.5 | axiom-clean check |

**Phase 4 status (`h29` DONE).** `h29_of_baxter_exterior` derives `Dt·bhF − 2πK/z = 0` from a single
hypothesis `hbax`: Baxter's exterior real-space factorization identity (Eq. 8),
`2πρ r c(r) = −Q'(r) + ∫₀^∞ Q(t)·Q'(t+r) dt` at `r > σ`, with `c = cMSAtail` (the MSA closure) and
`Q = bhBaxterFn` (the concrete exact Baxter function). This **relocates** `h29`'s trust from "BH's
posited algebraic equation" to "the OZ/Baxter Eq. (8) + the MSA exterior closure" — exactly the
recognised SM primitive the repo proves for hard spheres as `baxter_factorization_inner`. The
`Q'(t+r)` in `hbax` is written in exterior closed form `−z D e^{−z(t+r)}` (valid since `t+r > σ`),
matching the repo convention (`baxter_factorization_inner` likewise uses the explicit polynomial
derivative in its integrand, not `deriv q0_poly`). The `ρ`/`e^z` normalizations cancel: with
`D = ρ Dt e^z` the closure coupling `K` in `cMSAtail` **is** the BH `K` with no residual factor.
**Not yet done:** discharging `hbax` itself as a theorem (the Yukawa analog of
`baxter_factorization_inner`, i.e. proving Eq. 8 for `bhBaxterFn` pointwise — the interior half is the
harder poly·exp / exp·exp FTC); and Phases 5 (`h33`) / 6 (wire-in).

**Total ≈ 8–12 sessions.** Phase 0 is a genuine GO/NO-GO gate: it decides whether the existing
machinery + a few gap lemmas suffice, and whether γ/M/N are *derivable* from the continuity
conditions or are themselves irreducible transcriptions (relocating vs eliminating the spec
boundary). Either outcome is worth knowing before committing to Phases 1–6.

**Key references:** `MSABlumHoyeDerivation.lean` (M1–M4), `MSABlumHoyeSystem.lean` (`gam`/`Mtil`/
`Ntil`/`tailtil`/`bhF`/`bhP`/`bh_base_eq`), `MSABaxterKSpace.lean` (`msaA`/`msaQp`), `MSAFullFactorization.lean`
(`exactMSA_factorization`, the wire-in target), `HardSphere/BaxterRealSpace.lean`
(`baxter_factorization_inner` template), `lecture_notes_OZ_Yukawa_poly.pdf`, BH-mixture PDF in
`pdf/sources_paywall/`, `numerical_notes/theory/waisman_msa_closed_form.md` §5–7.
