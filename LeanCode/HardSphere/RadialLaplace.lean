/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.PYOZ

/-!
# Radial Laplace convolution theorem — foundation for OZ.2b

## ⚠ 2026 update: `radial_laplace_conv` is mathematically false, not just unproved

The clean-product claim below (`ℒ_r[c ⊛₃D h](s) = ℒ_r[c](s) · ℒ_r[h](s)`) does **not** hold —
confirmed by exact symbolic re-derivation and independent numerical checks. See the axiom's
own doc comment for the corrected identity and why even a fixed statement wouldn't rescue
`oz_laplace_oz_eq`/`g0_HS_laplace_spec` below. The rest of this module docstring describes the
*originally intended* (but incorrect) strategy; kept for context, not as a claim of validity.

## Summary

The 3D Ornstein–Zernike equation for radially symmetric functions is a convolution:
    `h(r) = c(r) + ρ · (c ⊛₃D h)(r)`

where `(c ⊛₃D h)(r) = (2π/r) ∫_0^∞ t·c(t) · [∫_{|r-t|}^{r+t} s·h(s) ds] dt`.

Under the *r-weighted Laplace transform* `ℒ_r[f](s) = ∫_0^∞ r·f(r)·e^{-sr} dr`, this
convolution *factors*:

    `ℒ_r[c ⊛₃D h](s) = ℒ_r[c](s) · ℒ_r[h](s)`

This is the **radial Laplace convolution theorem** (axiomized below).  Combined with the
algebraic OZ identity `oz_laplace_identity` from `PYOZ.lean`, it gives:

    `H̃(s) · (1 - ρC̃(s)) = C̃(s)`   →   `H̃(s) = C̃(s) · S₀(s)`

which is `g0_HS_laplace_spec` (Task OZ.2b).

## Axiom hierarchy

This file contains only the pure-math half.  The physics and the proved theorem live in
`PYOZ_GHS.lean` (which imports this file):

```
radial_laplace_conv   (axiom, this file: Fubini + substitution on radial 3D convolution)
        ↓
oz_laplace_oz_eq      (axiom, PYOZ_GHS.lean: oz_h satisfies the full OZ integral equation)
        ↓
g0_HS_laplace_spec    (proved theorem, PYOZ_GHS.lean: via oz_laplace_identity)
```

## References

- Baxter, R.J. (1970) J. Chem. Phys. 52, 4559 — radial Laplace factorization for 3D OZ
- Wertheim, M.S. (1963) Phys. Rev. Lett. 10, 321 — PY hard-sphere analytical solution
-/

open MeasureTheory Set Real

namespace FMSA.HardSphere

/-! ### Radial 3D convolution and Laplace transform -/

/-- **3D radial convolution of radially symmetric functions.**

For two radial functions `f, g : ℝ → ℝ`, the 3D convolution
`(f * g)(r) = ∫ f(|r−r'|) g(|r'|) d³r'`
reduces (after angular integration) to:

    `(f ⊛₃D g)(r) = (2π/r) · ∫_0^∞ t · f(t) · [∫_{|r−t|}^{r+t} s · g(s) ds] dt`

The factor `2π/r` arises from integrating over the azimuthal angle and the cosine of the
polar angle.  The inner integral `∫_{|r-t|}^{r+t} s·g(s) ds` sweeps over the shell of
radii accessible from distance `t` at angle `θ` from `r`. -/
noncomputable def radial3d_conv (f g : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0
  else (2 * Real.pi / r) *
       ∫ t in Set.Ioi (0 : ℝ), t * f t *
         ∫ s in Set.Icc (|r - t|) (r + t), s * g s

/-- **Modified (r-weighted) one-sided Laplace transform.**

    `ℒ_r[f](s) = ∫_0^∞ r · f(r) · e^{-sr} dr`

This differs from the ordinary Laplace transform by the factor `r`, which enters naturally
when computing the Laplace transform of `h(r) = g(r) - 1` for radially symmetric functions
in 3D: the Fourier transform `ĥ(k) = 4π ∫_0^∞ r² h(r) sinc(kr) dr` reduces to
`(4π/k) · ∫_0^∞ r sin(kr) h(r) dr` and in the Laplace limit gives this form. -/
noncomputable def radial_laplace (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), r * f r * Real.exp (-s * r)

/-! ### Axiom 1: radial Laplace convolution theorem -/

/-- **Axiom (radial Laplace convolution theorem) — ⚠ MATHEMATICALLY FALSE AS STATED.**

**2026 update:** this axiom's claimed clean-product factorization is **false**, not merely
unproved — verified both by exact symbolic re-derivation and by independent numerical checks
(ratio of the two sides varies from ~12 to ~37 across different `(f,g,s)` test triples,
including when `g` has compact support like `c_HS`; this rules out a missing-normalization-
constant explanation, and confirms the mismatch is structural, not a scaling bug).

Doing the swap of integration order correctly (over the triangle-inequality region
`{(r,t,s'): |r-t|≤s'≤r+t}`, symmetric in `r,t,s'`, integrating over `r` first) gives the
TRUE identity instead:
```
ℒ_r[f ⊛₃D g](s) = (2π/s) · [A(s) − ℒ_r[f](s) · ℒ_r[g](s)]
```
where `A(s) = ∫∫ t·f(t)·s'·g(s')·e^{-s|t-s'|} dt ds'` — a genuinely different (bilateral
Green's-function-kernel) object that does **not** vanish or factor further in general
(confirmed to match the true LHS to 6 decimal places numerically). The `∫_{|s-t|}^{s+t}
e^{-sr} dr` step below correctly integrates to `(1/s)[e^{-s|s-t|} - e^{-s(s+t)}]`, not to a
clean product — the *first* term of that difference is exactly the missing `A(s)` piece the
original proof sketch silently dropped.

**Consequence:** even a corrected, TRUE `radial_laplace_conv` (the `A(s)`-including form
above) would **not** rescue `oz_laplace_oz_eq`, since that theorem needs precisely the clean
product form to combine with `oz_laplace_identity`. The real OZ multiplicative structure
lives in Fourier space (`ĥ(k)=ĉ(k)+ρĉ(k)ĥ(k)`, real `k`) or Baxter's Wiener–Hopf
factorization (`1-ρĉ(k)=A(k)·Ā(k)`, requiring half-plane analyticity) — neither reduces to a
one-sided real Laplace transform of `r·f(r)` the way this file assumes. Fixing this requires
rearchitecting the OZ.2/OZ.2b/OZ.3 chain around one of those correct transforms, not patching
this axiom's statement; not attempted here (out of scope, needs its own scoping pass).
`g0_HS_laplace_spec` (`PYOZ_GHS.lean`) is proved *conditional on* this axiom and therefore
currently rests on a false foundation despite building successfully.

---

The `r`-weighted Laplace transform of the 3D radial convolution factors as a product:

    `ℒ_r[f ⊛₃D g](s) = ℒ_r[f](s) · ℒ_r[g](s)`

**Mathematical proof (outline) — ⚠ this argument is WRONG, see update above.** Expanding and
applying Fubini's theorem:
```
∫_0^∞ r · (f ⊛₃D g)(r) · e^{-sr} dr
= 2π ∫_0^∞ ∫_0^∞ t·f(t) · ∫_{|r-t|}^{r+t} s·g(s) ds · e^{-sr} dt dr
```
Change the order of integration (Fubini), then for fixed `t` and `s`, the range of `r`
where `|r-t| ≤ s ≤ r+t` is `|s-t| ≤ r ≤ s+t`.  After integrating over `r`, the
exponential `∫_{|s-t|}^{s+t} e^{-sr} dr` factors into separate Laplace transforms,
yielding `ℒ_r[f](s) · ℒ_r[g](s)`.

**Integrability conditions:** The axiom assumes that `f` and `g` are integrable with the
`r · e^{-sr}` weight (ensuring Fubini applies) — satisfied for OZ solutions with
exponential decay at infinity, which is physically expected for `h` and the PY `c_HS`.

**Used in:** `oz_laplace_oz_eq` below (to convert the OZ integral equation for `oz_h`
into the Laplace-domain OZ equation). -/
axiom radial_laplace_conv {f g : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hf : Integrable (fun r => r * f r * Real.exp (-s * r))
            (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hg : Integrable (fun r => r * g r * Real.exp (-s * r))
            (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    radial_laplace (radial3d_conv f g) s = radial_laplace f s * radial_laplace g s

end FMSA.HardSphere
