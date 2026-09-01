/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSAGSideOZ
import LeanCode.YukawaOZ.MSAFullFactorization

/-!
# The MSA Baxter factorization from the OZ primitives (leg-3, `N = 1`) — Phase 6 wire-in

`MSAFullFactorization.exactMSA_factorization` derives the exact-MSA Baxter factorization
`|1 − ρQ̂(ik)|² = 1 − ρĉ_MSA(k)` from the two **posited** Blum–Høye constraints `h29`
(`Dt·bhF = 2πK/z`) and `h33` (`2πG·bhF = bhP`).  This file **retires those posited constraints**,
feeding in the versions now *derived* from the recognised OZ/Baxter primitives:

* `h29` ⟵ `MSABlumHoyeDerivation.h29_of_baxter_exterior` (from Baxter's exterior real-space relation
  `hbax`, Eq. 8, plus the MSA closure `cMSAtail`);
* `h33` ⟵ `MSAGSideOZ.h33_of_gside_baxter` (from the g-side OZ equation Laplace-transformed at `s = z`,
  `hgside`, Eq. 32, with the OZ-convolution term folded by the proved convolution theorem, and the
  concrete supported Baxter kernel `bhBaxterSupp` discharging the `Q̂`/integrability side).

So `exactMSA_factorization_of_oz` produces the MSA factorization from exactly the recognised inputs
`hbax` (the `c`-side Baxter Eq. 8) and `hgside` (the `g`-side OZ Eq. 32), plus the RDF-side data
(`g`'s core support, the RDF moment integrability, and the moment identification `ĝ(z) = G`) — no
free-floating `h29`/`h33`.  Its axiom footprint is the standard three **plus** the single
physics-computation axiom `exactMSA_hcore` inherited from `exactMSA_factorization` (the sympy-certified
`Dt¹/Dt²` `hcore` residual — `ring`-infeasible, not a mathematical assumption); the leg-3 derivations
`h29_of_baxter_exterior` and `h33_of_gside_baxter` add **no** new axiom.
-/

open Real MeasureTheory

namespace FMSA.ExactMSA.GSide

open FMSA.HardSphere

/-- **The exact-MSA Baxter factorization, derived from the OZ primitives** (Phase-6 wire-in).
`|1 − ρQ̂(ik)|² = 1 − ρĉ_MSA(k)` at the Blum–Høye root, with the two constraints supplied by the
leg-3 derivations rather than posited: `h29` from Baxter's exterior relation `hbax` (Eq. 8) and `h33`
from the g-side OZ equation `hgside` (Eq. 32) via the convolution theorem.  `(1 − xi) ≠ 0` is
supplied from `xi < 1`. -/
theorem exactMSA_factorization_of_oz (xi z Dt G K : ℝ) {k : ℝ} (hk : k ≠ 0)
    (hxipos : 0 < xi) (hxi1 : xi < 1) (hz : 0 < z)
    (hbax : ∀ r, 1 < r →
      2 * Real.pi * rhoOf xi * r * cMSAtail K z 1 r
        = -deriv (fun s => bhBaxterFn xi z Dt G s) r
          + ∫ t in Set.Ioi (0:ℝ), bhBaxterFn xi z Dt G t
              * (-z * (rhoOf xi * Dt * Real.exp z) * Real.exp (-z * (r + t))))
    (g : ℝ → ℝ)
    (hgsupp : ∀ u, u < 0 → g u = 0)
    (hF1 : Integrable (fun u => Real.exp (-z * u) * (u * g u)))
    (hgmoment : rdfLaplaceMoment g z = G)
    (hgside : 2 * Real.pi * rdfLaplaceMoment g z
      = (∫ u in Set.Ioi (0:ℝ),
            (u * msaA xi z Dt G + msaQp xi z Dt G + z * gam xi z G * Dt * Real.exp (-z * u))
              * Real.exp (-z * u))
        + 2 * Real.pi * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
            * ∫ t in Set.Ioi (0:ℝ), (r - t) * g (r - t) * bhBaxterSupp xi z Dt G t)) :
    (1 - msaQre xi z Dt G k) ^ 2 + msaQim xi z Dt G k ^ 2
      = 1 - rhoOf xi * (radial_fourier (c_HS xi 1) k
          + radial_fourier (msaCoreCorr xi z Dt G K) k
          + radial_fourier (cMSAtail K z 1) k) :=
  exactMSA_factorization xi z Dt G K hk hxi1
    (h29_of_baxter_exterior xi z Dt G K hz
      (show (1 - xi) ≠ 0 from (show (0:ℝ) < 1 - xi by linarith).ne') hxipos hbax)
    (h33_of_gside_baxter xi z Dt G hz
      (show (1 - xi) ≠ 0 from (show (0:ℝ) < 1 - xi by linarith).ne') g hgsupp hF1 hgmoment hgside)

end FMSA.ExactMSA.GSide
