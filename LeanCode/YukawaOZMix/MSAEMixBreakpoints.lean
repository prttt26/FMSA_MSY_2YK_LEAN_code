/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# MSAEMIX.5 — the unequal-σ core breakpoint structure has NO mediated (3-body) breakpoints

Group **MSAEMIX** (`proof_notes_msa_exact.md`).  Numerical partner: `msaemix_uneq_n3.py`.

The exact-MSA mixture core `c_ij(r)` on `(0, σ_ij)` comes from the Baxter convolution
`2πr c_ij(r) = −Q'_ij(r) + Σ_l ρ_l ∫₀^∞ Q'_il(t+r) Q_jl(t) dt`.  Each real-space `Q_ab` is
supported on `[edgeLo σ a b, ∞)` with the Baxter poly on `[edgeLo σ a b, edgeHi σ a b]`, where
`edgeLo σ a b = (σ_b − σ_a)/2` and `edgeHi σ a b = (σ_a + σ_b)/2`.  The `r`-breakpoints of the
`l`-term occur where the four `t`-kinks — `edgeLo σ j l`, `edgeHi σ j l` (from `Q_jl(t)`) and
`edgeLo σ i l − r`, `edgeHi σ i l − r` (from `Q'_il(t+r)`) — cross, i.e. at the four `r`-values

    edgeLo σ i l − edgeLo σ j l,  edgeHi σ i l − edgeHi σ j l,
    edgeHi σ i l − edgeLo σ j l,  edgeLo σ i l − edgeHi σ j l.

⭐ **Key MSAEMIX.5 fact (this file, fully proved, no axioms):** every one of these four crossings is
**independent of the intermediate species `l`** — `σ_l` enters `edgeLo σ i l = (σ_l−σ_i)/2` and
`edgeLo σ j l = (σ_l−σ_j)/2` symmetrically and cancels in the difference.  They equal, resp.,
`(σ_j−σ_i)/2` (`edgeLo σ i j`), `(σ_i−σ_j)/2` (`edgeLo σ j i`), `(σ_i+σ_j)/2` (`edgeHi σ i j`),
`−(σ_i+σ_j)/2`.  Hence the breakpoint set is `{ ±(σ_i−σ_j)/2, ±(σ_i+σ_j)/2 }` at **every `N`**: the
intermediate species contributes **no new (mediated / 3-body) breakpoint** — unlike the FMSA
first-order mediated terms (`_compute_mediated`, whose breakpoints are genuinely `σ`-dependent).

## What is / isn't in Lean
* **In Lean (no axioms):** the `σ_l`-cancellation (`bp_*`, `bp_*_indep`, `breakpoints_sigma_l_free`)
  and the interior-location claim (`interior_breakpoint_eq_absLam`: the unique crossing in the OPEN
  core interval `(0, σ_ij)` is `|λ_ij| = |σ_i−σ_j|/2`, `edgeHi = σ_ij` is the endpoint).
* **Not in Lean (analytic / Stage 3):** that `edgeLo`/`edgeHi` are the real-space `Q_ab` support
  edges, and that the convolution's kinks *are* exactly these crossings (a piecewise-convolution
  analysis lemma).  These are verified numerically (`msaemix_uneq_*.py`).  The full piecewise core
  basis is MSAEMIX.4 Stage 3.
-/

namespace MSAEMix

variable {N : ℕ}

/-- Low support edge of the real-space Baxter factor `Q_ab`: `λ_ab = (σ_b − σ_a)/2` (where its poly
support and Yukawa tail begin). -/
noncomputable def edgeLo (σ : Fin N → ℝ) (a b : Fin N) : ℝ := (σ b - σ a) / 2

/-- Poly/tail junction of `Q_ab`: `σ_ab = (σ_a + σ_b)/2` (where the Baxter poly ends and the tail
begins). -/
noncomputable def edgeHi (σ : Fin N → ℝ) (a b : Fin N) : ℝ := (σ a + σ b) / 2

/-! ### The four breakpoint crossings are `σ_l`-independent -/

/-- `edgeLo·edgeLo` crossing `= (σ_j−σ_i)/2 = edgeLo σ i j` — no `σ_l`. -/
theorem bp_loLo (σ : Fin N → ℝ) (i j l : Fin N) :
    edgeLo σ i l - edgeLo σ j l = edgeLo σ i j := by unfold edgeLo; ring

/-- `edgeHi·edgeHi` crossing `= (σ_i−σ_j)/2 = edgeLo σ j i` — no `σ_l`. -/
theorem bp_hiHi (σ : Fin N → ℝ) (i j l : Fin N) :
    edgeHi σ i l - edgeHi σ j l = edgeLo σ j i := by unfold edgeHi edgeLo; ring

/-- `edgeHi·edgeLo` crossing `= (σ_i+σ_j)/2 = edgeHi σ i j` (core endpoint `σ_ij`) — no `σ_l`. -/
theorem bp_hiLo (σ : Fin N → ℝ) (i j l : Fin N) :
    edgeHi σ i l - edgeLo σ j l = edgeHi σ i j := by unfold edgeHi edgeLo; ring

/-- `edgeLo·edgeHi` crossing `= −(σ_i+σ_j)/2 = −edgeHi σ i j` — no `σ_l`. -/
theorem bp_loHi (σ : Fin N → ℝ) (i j l : Fin N) :
    edgeLo σ i l - edgeHi σ j l = -edgeHi σ i j := by unfold edgeLo edgeHi; ring

/-! ### "No mediated breakpoints": the crossings do not depend on which intermediate species -/

/-- ⭐ **No mediated breakpoint (loLo).** For any two intermediate species `l`, `l'`, the crossing is
the same — the exact-MSA core breakpoint from `Q'_il ⋆ Q_jl` does not depend on `l`. -/
theorem bp_loLo_indep (σ : Fin N → ℝ) (i j l l' : Fin N) :
    edgeLo σ i l - edgeLo σ j l = edgeLo σ i l' - edgeLo σ j l' := by
  rw [bp_loLo, bp_loLo]

/-- No mediated breakpoint (hiHi). -/
theorem bp_hiHi_indep (σ : Fin N → ℝ) (i j l l' : Fin N) :
    edgeHi σ i l - edgeHi σ j l = edgeHi σ i l' - edgeHi σ j l' := by
  rw [bp_hiHi, bp_hiHi]

/-- No mediated breakpoint (hiLo). -/
theorem bp_hiLo_indep (σ : Fin N → ℝ) (i j l l' : Fin N) :
    edgeHi σ i l - edgeLo σ j l = edgeHi σ i l' - edgeLo σ j l' := by
  rw [bp_hiLo, bp_hiLo]

/-- No mediated breakpoint (loHi). -/
theorem bp_loHi_indep (σ : Fin N → ℝ) (i j l l' : Fin N) :
    edgeLo σ i l - edgeHi σ j l = edgeLo σ i l' - edgeHi σ j l' := by
  rw [bp_loHi, bp_loHi]

/-- ⭐⭐ **MSAEMIX.5 — the breakpoint set is `{±(σ_i−σ_j)/2, ±(σ_i+σ_j)/2}`, `σ_l`-free.**  For every
intermediate species `l`, the four `Q'_il ⋆ Q_jl` crossings equal exactly the four `i,j`-only values
`(σ_j−σ_i)/2`, `(σ_i−σ_j)/2`, `(σ_i+σ_j)/2`, `−(σ_i+σ_j)/2` — so no `l` introduces a new breakpoint.
(The interior one in `(0, σ_ij)` is `|(σ_i−σ_j)/2| = |λ_ij|`; `σ_ij` is the endpoint.) -/
theorem breakpoints_sigma_l_free (σ : Fin N → ℝ) (i j l : Fin N) :
    edgeLo σ i l - edgeLo σ j l = (σ j - σ i) / 2
    ∧ edgeHi σ i l - edgeHi σ j l = (σ i - σ j) / 2
    ∧ edgeHi σ i l - edgeLo σ j l = (σ i + σ j) / 2
    ∧ edgeLo σ i l - edgeHi σ j l = -((σ i + σ j) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [edgeLo, edgeHi]; ring)

/-! ### The unique interior breakpoint on the core interval `(0, σ_ij)` is `|λ_ij|` -/

/-- ⭐⭐ **The unique interior breakpoint is `|λ_ij|`, and it is `σ_l`-free.**  Of the four `σ_l`-free
crossing values `{edgeLo σ i j, edgeLo σ j i, edgeHi σ i j, −edgeHi σ i j}` (`= {±(σ_i−σ_j)/2,
±(σ_i+σ_j)/2}`), for positive diameters with `σ_i ≠ σ_j` exactly one lies in the open core interval
`(0, σ_ij)` — namely `|λ_ij| = |σ_i−σ_j|/2 = |edgeLo σ i j|`.  (`edgeHi σ i j = σ_ij` is the right
endpoint, excluded; `−edgeHi σ i j` and the negative of `±(σ_i−σ_j)/2` are `≤ 0`.)  So the exact-MSA
core `c_ij` on `(0, σ_ij)` has its single interior breakpoint pinned to `|λ_ij|`, at every `N` and
independent of the intermediate species — the `σ_l`-free location claim of MSAEMIX.5, algebraically
complete (the semantic link "these crossings *are* the convolution's kinks" is analytic). -/
theorem interior_breakpoint_eq_absLam (σ : Fin N → ℝ) (i j : Fin N)
    (hi : 0 < σ i) (hj : 0 < σ j) (hne : σ i ≠ σ j) :
    |edgeLo σ i j| ∈ Set.Ioo (0 : ℝ) (edgeHi σ i j) ∧
      ∀ c ∈ ({edgeLo σ i j, edgeLo σ j i, edgeHi σ i j, -edgeHi σ i j} : Set ℝ),
        c ∈ Set.Ioo (0 : ℝ) (edgeHi σ i j) → c = |edgeLo σ i j| := by
  have habs : |edgeLo σ i j| = |σ j - σ i| / 2 := by
    simp only [edgeLo, abs_div]; rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hpos : (0 : ℝ) < |edgeLo σ i j| := by
    rw [habs]; have := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne)); linarith
  have hlt : |edgeLo σ i j| < edgeHi σ i j := by
    have h : |σ j - σ i| < σ i + σ j := abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [habs]; simp only [edgeHi]; linarith
  refine ⟨Set.mem_Ioo.mpr ⟨hpos, hlt⟩, ?_⟩
  intro c hc hmem
  rw [Set.mem_Ioo] at hmem
  obtain ⟨h1, h2⟩ := hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with h | h | h | h <;> subst h
  · -- c = edgeLo σ i j > 0 ⇒ |edgeLo σ i j| = edgeLo σ i j
    rw [abs_of_pos h1]
  · -- c = edgeLo σ j i > 0 ⇒ edgeLo σ i j = -edgeLo σ j i < 0
    rw [show edgeLo σ i j = -(edgeLo σ j i) from by simp only [edgeLo]; ring, abs_neg,
      abs_of_pos h1]
  · exact absurd h2 (lt_irrefl _)
  · exact absurd h1 (by have : (0:ℝ) < edgeHi σ i j := by simp only [edgeHi]; linarith
                        linarith)

end MSAEMix
