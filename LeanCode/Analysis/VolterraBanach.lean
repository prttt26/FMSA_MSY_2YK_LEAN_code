/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Volterra integral equation of the second kind in a Banach normed ring

The Banach-space generalization of `MA.10` (`Analysis/Volterra.lean`, the `ℝ`-valued Volterra
existence/uniqueness). For a **complete normed ring** `E` (`NormedRing E`, `NormedAlgebra ℝ E`,
`CompleteSpace E`) and the **convolution** kernel `q(r−t)` with `q : ℝ → E`, the equation

  `u(r) = g(r) + ∫_a^r q(r−t) · u(t) dt`   (`·` the ring multiplication of `E`)

has a unique continuous `E`-valued solution on `[a,b]`. The proof is the identical
iterate-contraction argument as the scalar case: the only change is `|K·u| ≤ M·|u|` becoming
`‖q · u‖ ≤ ‖q‖ · ‖u‖ ≤ M·‖u‖` via `norm_mul_le` (submultiplicativity of the normed ring).

**Motivation.** The mixture Baxter renewal equation
`Ψ(r) = F(r) + ∫_σ^r Q(r−t)·Ψ(t) dt` (matrix product) *is* this equation at
`E = Matrix (Fin N) (Fin N) ℝ` — the species-coupling sum `∑ₖ Qᵢₖ·Ψₖⱼ` is exactly the matrix
product `(Q·Ψ)ᵢⱼ`. So this file constructs the matrix `baxterPsi`'s outer solution `Ψouter`
(`HSMixture/MixtureOzStar.lean`, `MatRenewalEq`).

Status: ✓ axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only), a mechanical
generalization of the proved `MA.10`.
-/

open Metric Set Filter Topology MeasureTheory Nat

noncomputable section

namespace FMSA.VolterraBanach

set_option linter.unusedSectionVars false

variable {a b : ℝ} {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- The `E`-valued affine Volterra operator with convolution kernel `q(r−t)`. -/
def volterraTE (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (u : C(Icc a b, E)) : C(Icc a b, E) where
  toFun := fun r => g r + ∫ t in a..(r : ℝ), q ((r : ℝ) - t) * Set.IccExtend hab u t
  continuous_toFun := by
    have hext : Continuous (Set.IccExtend hab u) := u.continuous.Icc_extend'
    have huc : Continuous (Function.uncurry fun r t => q (r - t) * Set.IccExtend hab u t) := by
      simp only [Function.uncurry_def]
      exact (hq.comp (continuous_fst.sub continuous_snd)).mul (hext.comp continuous_snd)
    have hcore : Continuous fun r : ℝ => g r + ∫ t in a..r, q (r - t) * Set.IccExtend hab u t :=
      hg.add (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous huc
        continuous_id)
    exact hcore.comp continuous_subtype_val

@[simp] lemma volterraTE_apply (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (u : C(Icc a b, E)) (r : Icc a b) :
    volterraTE hab q g hq hg u r
      = g r + ∫ t in a..(r : ℝ), q ((r : ℝ) - t) * Set.IccExtend hab u t := rfl

/-- `∫_a^r (t−a)^n dt = (r−a)^(n+1)/(n+1)`. -/
lemma volterra_integral_sub_pow (a r : ℝ) (n : ℕ) :
    (∫ t in a..r, (t - a) ^ n) = (r - a) ^ (n + 1) / (n + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun t => t ^ n) a, sub_self, integral_pow]; simp

variable {M : ℝ}

/-- **The iterate bound** (`E`-valued): `‖Tⁿu(r) − Tⁿw(r)‖ ≤ Mⁿ(r−a)ⁿ/n! · dist u w`.  The heart of
the argument; the `(r−a)ⁿ` local factor is what the induction closes on. -/
lemma volterra_iterate_boundE (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (hM : 0 ≤ M) (hqb : ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, ‖q (r - t)‖ ≤ M)
    (u w : C(Icc a b, E)) (n : ℕ) (r : Icc a b) :
    ‖(volterraTE hab q g hq hg)^[n] u r - (volterraTE hab q g hq hg)^[n] w r‖
      ≤ M ^ n * ((r : ℝ) - a) ^ n / n ! * dist u w := by
  set T := volterraTE hab q g hq hg with hT
  set D := dist u w with hD
  have hD0 : 0 ≤ D := dist_nonneg
  induction n generalizing r with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, Nat.factorial_zero,
        Nat.cast_one, div_one, mul_one]
      calc ‖u r - w r‖ = dist (u r) (w r) := (dist_eq_norm _ _).symm
        _ ≤ dist u w := ContinuousMap.dist_apply_le_dist r
        _ = D := hD.symm
  | succ n ih =>
      have hra : (r : ℝ) ∈ Icc a b := r.2
      have har : a ≤ (r : ℝ) := hra.1
      have hext : ∀ t ∈ Icc a b,
          ‖Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t‖
            ≤ M ^ n * (t - a) ^ n / n ! * D := by
        intro t ht
        have : Set.projIcc a b hab t = ⟨t, ht⟩ := by simp [Set.projIcc, ht.1, ht.2]
        simpa [Set.IccExtend, this] using ih ⟨t, ht⟩
      have hdiff : T^[n+1] u r - T^[n+1] w r
          = ∫ t in a..(r : ℝ), q ((r : ℝ) - t) *
              (Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hT]
        simp only [volterraTE_apply]
        rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub]
        · congr 1; funext t; rw [mul_sub]
        · apply Continuous.intervalIntegrable
          exact ((hq.comp (continuous_const.sub continuous_id)).mul
            ((T^[n] u).continuous.Icc_extend' (h := hab)))
        · apply Continuous.intervalIntegrable
          exact ((hq.comp (continuous_const.sub continuous_id)).mul
            ((T^[n] w).continuous.Icc_extend' (h := hab)))
      rw [hdiff]
      have hfac : ((n ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hbound : ‖∫ t in a..(r : ℝ), q ((r : ℝ) - t) *
            (Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t)‖
          ≤ ∫ t in a..(r : ℝ), M ^ (n + 1) * (t - a) ^ n / n ! * D := by
        apply intervalIntegral.norm_integral_le_of_norm_le har
        · filter_upwards with t ht
          have htab : t ∈ Icc a b := ⟨le_of_lt ht.1, le_trans ht.2 hra.2⟩
          calc ‖q ((r : ℝ) - t) *
                (Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t)‖
              ≤ ‖q ((r : ℝ) - t)‖ *
                ‖Set.IccExtend hab (T^[n] u) t - Set.IccExtend hab (T^[n] w) t‖ := norm_mul_le _ _
            _ ≤ M * (M ^ n * (t - a) ^ n / n ! * D) :=
                mul_le_mul (hqb _ hra _ htab) (hext t htab) (norm_nonneg _) hM
            _ = M ^ (n + 1) * (t - a) ^ n / n ! * D := by ring
        · apply Continuous.intervalIntegrable; fun_prop
      have heval : (∫ t in a..(r : ℝ), M ^ (n + 1) * (t - a) ^ n / n ! * D)
          = (M ^ (n + 1) * D / n !) * (((r : ℝ) - a) ^ (n + 1) / (n + 1)) := by
        have hre : (fun t : ℝ => M ^ (n + 1) * (t - a) ^ n / n ! * D)
            = fun t => (M ^ (n + 1) * D / n !) * (t - a) ^ n := by funext t; ring
        rw [hre, intervalIntegral.integral_const_mul, volterra_integral_sub_pow]
      rw [heval] at hbound
      refine hbound.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]; push_cast; field_simp

/-- Sup-distance form of the iterate bound. -/
lemma volterra_iterate_distE (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (hM : 0 ≤ M) (hqb : ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, ‖q (r - t)‖ ≤ M)
    (u w : C(Icc a b, E)) (n : ℕ) :
    dist ((volterraTE hab q g hq hg)^[n] u) ((volterraTE hab q g hq hg)^[n] w)
      ≤ (M * (b - a)) ^ n / n ! * dist u w := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hnn : 0 ≤ (M * (b - a)) ^ n / n ! * dist u w := by positivity
  rw [ContinuousMap.dist_le hnn]
  intro r
  rw [dist_eq_norm]
  refine (volterra_iterate_boundE hab q g hq hg hM hqb u w n r).trans ?_
  rw [mul_pow]
  gcongr
  · exact sub_nonneg.mpr r.2.1
  · exact r.2.2

/-- **Volterra existence & uniqueness, `E`-valued, given a kernel bound** — the Banach fixed point
of `volterraTE`, from the eventual-contraction of its iterates. -/
theorem volterra_existsUniqueE (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (hM : 0 ≤ M) (hqb : ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, ‖q (r - t)‖ ≤ M) :
    ∃! u : C(Icc a b, E), volterraTE hab q g hq hg u = u := by
  set T := volterraTE hab q g hq hg with hT
  haveI : Nonempty C(Icc a b, E) := ⟨0⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (M * (b - a)) ^ n / n ! < 1 / 2 := by
    have htend := FloorSemiring.tendsto_pow_div_factorial_atTop (M * (b - a))
    exact (htend.eventually_lt_const (by norm_num)).exists
  have hcontract : ContractingWith (1 / 2 : NNReal) T^[n] := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
    refine (volterra_iterate_distE hab q g hq hg hM hqb u w n).trans ?_
    have hhalf : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
    rw [hhalf]
    exact mul_le_mul_of_nonneg_right hn.le dist_nonneg
  refine ⟨hcontract.fixedPoint _, hcontract.isFixedPt_fixedPoint_iterate, fun w hw => ?_⟩
  exact hcontract.fixedPoint_unique (Function.IsFixedPt.iterate (f := T) hw n)

/-- **The Banach generalization of `MA.10` — hypothesis-free.**  For a complete normed ring `E`, a
continuous convolution kernel `q : ℝ → E` and continuous data `g : ℝ → E`, the Volterra equation
`u(r) = g(r) + ∫_a^r q(r−t)·u(t) dt` has a **unique** continuous `E`-valued solution on `[a,b]`.
The kernel bound is supplied by compactness of `[a,b]²`. -/
theorem volterra_convolution_existsUniqueE (hab : a ≤ b) (q g : ℝ → E)
    (hq : Continuous q) (hg : Continuous g) :
    ∃! u : C(Icc a b, E), ∀ r : Icc a b,
      u r = g r + ∫ t in a..(r : ℝ), q ((r : ℝ) - t) * Set.IccExtend hab u t := by
  obtain ⟨M, hM, hqb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Icc a b, ∀ t ∈ Icc a b, ‖q (r - t)‖ ≤ M := by
    have hcpt : IsCompact ((Icc a b) ×ˢ (Icc a b) : Set (ℝ × ℝ)) :=
      isCompact_Icc.prod isCompact_Icc
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn
      ((hq.comp (continuous_fst.sub continuous_snd)).continuousOn)
    refine ⟨max C 0, le_max_right _ _, fun r hr t ht => ?_⟩
    exact le_trans (hC (r, t) ⟨hr, ht⟩) (le_max_left _ _)
  obtain ⟨u, hu, huniq⟩ := volterra_existsUniqueE hab q g hq hg hM hqb
  refine ⟨u, fun r => (ContinuousMap.ext_iff.mp hu r).symm,
    fun w hw => huniq w (ContinuousMap.ext fun r => (hw r).symm)⟩

/-! ## The global `E`-valued Volterra solution on `[a,∞)`

`volterra_convolution_existsUniqueE` produces a solution on each **compact** `[a,b]` separately, as an
element of the dependent type `C(Icc a b, E)`.  The mixture Baxter outer solution `Ψouter` needs
**one** function on `[a,∞)`.  As in the scalar `volterraGlobal` (`BaxterRenewal.lean`), uniqueness is
the glue: a solution on the longer interval, restricted, still solves the shorter equation (the
integration range `[a,r]` never leaves `[a,b]`), hence **is** the shorter solution.  Evaluating the
`b := r` solution at its own right endpoint therefore defines a single global solution satisfying the
renewal equation at every `r ≥ a`.  This is the exact Banach-ring transcription of the proved scalar
chain, so the matrix `Ψouter` is a direct instantiation at `E = Matrix (Fin N) (Fin N) ℝ`. -/

/-- The local `E`-valued Volterra solution on `[a,b]` (`volterra_convolution_existsUniqueE`, named). -/
def volterraSolE (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g) :
    C(Icc a b, E) :=
  (volterra_convolution_existsUniqueE hab q g hq hg).choose

theorem volterraSolE_spec (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (r : Icc a b) :
    volterraSolE hab q g hq hg r = g r + ∫ t in a..(r : ℝ),
      q ((r : ℝ) - t) * Set.IccExtend hab (volterraSolE hab q g hq hg) t :=
  (volterra_convolution_existsUniqueE hab q g hq hg).choose_spec.1 r

theorem volterraSolE_unique (hab : a ≤ b) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (v : C(Icc a b, E))
    (hv : ∀ r : Icc a b, v r = g r + ∫ t in a..(r : ℝ),
      q ((r : ℝ) - t) * Set.IccExtend hab v t) :
    v = volterraSolE hab q g hq hg :=
  (volterra_convolution_existsUniqueE hab q g hq hg).choose_spec.2 v hv

/-- **Compatibility: the local solutions agree on overlaps.**  Restricting the `[a,b']` solution to
`[a,b]` (`b ≤ b'`) still solves the `[a,b]` equation, so uniqueness on `[a,b]` forces the equality. -/
theorem volterraSolE_compat (hab : a ≤ b) {b' : ℝ} (hab' : a ≤ b') (hbb' : b ≤ b')
    (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g) (r : ℝ) (hr : r ∈ Set.Icc a b) :
    volterraSolE hab' q g hq hg ⟨r, ⟨hr.1, le_trans hr.2 hbb'⟩⟩
      = volterraSolE hab q g hq hg ⟨r, hr⟩ := by
  have hsub : Set.Icc a b ⊆ Set.Icc a b' := Set.Icc_subset_Icc_right hbb'
  set v : C(Set.Icc a b, E) :=
    (volterraSolE hab' q g hq hg).comp ⟨Set.inclusion hsub, continuous_inclusion hsub⟩ with hvdef
  have hvapp : ∀ x : Set.Icc a b, v x = volterraSolE hab' q g hq hg (Set.inclusion hsub x) :=
    fun _ => rfl
  have hext : ∀ t ∈ Set.Icc a b,
      Set.IccExtend hab' (volterraSolE hab' q g hq hg) t = Set.IccExtend hab v t := by
    intro t ht
    rw [Set.IccExtend_of_mem hab' _ (hsub ht), Set.IccExtend_of_mem hab _ ht, hvapp ⟨t, ht⟩]
  have hv : ∀ x : Set.Icc a b, v x = g x + ∫ t in a..(x : ℝ),
      q ((x : ℝ) - t) * Set.IccExtend hab v t := by
    intro x
    have hx := volterraSolE_spec hab' q g hq hg (Set.inclusion hsub x)
    have hxv : ((Set.inclusion hsub x : Set.Icc a b') : ℝ) = (x : ℝ) := rfl
    rw [hxv] at hx
    rw [hvapp x, hx]
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro t ht
    dsimp only []
    rw [Set.uIcc_of_le x.2.1] at ht
    have htmem : t ∈ Set.Icc a b := ⟨ht.1, le_trans ht.2 x.2.2⟩
    rw [hext t htmem]
  have hvu := volterraSolE_unique hab q g hq hg v hv
  calc volterraSolE hab' q g hq hg ⟨r, ⟨hr.1, le_trans hr.2 hbb'⟩⟩
      = v ⟨r, hr⟩ := rfl
    _ = volterraSolE hab q g hq hg ⟨r, hr⟩ := by rw [hvu]

/-- **The global `E`-valued Volterra solution on `[a,∞)`** — evaluate the `b := r` local solution at
its own right endpoint.  Off `[a,∞)` it is `0`. -/
def volterraGlobalE (a : ℝ) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g) (r : ℝ) : E :=
  if h : a ≤ r then volterraSolE h q g hq hg ⟨r, ⟨h, le_refl r⟩⟩ else 0

/-- `volterraGlobalE` agrees with every local solution on that solution's own interval. -/
theorem volterraGlobalE_eq_sol (hab : a ≤ b) (q g : ℝ → E)
    (hq : Continuous q) (hg : Continuous g) (r : ℝ) (hr : r ∈ Set.Icc a b) :
    volterraGlobalE a q g hq hg r = volterraSolE hab q g hq hg ⟨r, hr⟩ := by
  rw [volterraGlobalE, dif_pos hr.1]
  exact (volterraSolE_compat (b := r) (b' := b) hr.1 hab hr.2 q g hq hg r
    ⟨hr.1, le_refl r⟩).symm

/-- `volterraGlobalE` satisfies the renewal equation at **every** `r ≥ a`, with the *same* function
under the integral sign. -/
theorem volterraGlobalE_spec (a : ℝ) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    {r : ℝ} (hr : a ≤ r) :
    volterraGlobalE a q g hq hg r
      = g r + ∫ t in a..r, q (r - t) * volterraGlobalE a q g hq hg t := by
  have hmem : r ∈ Set.Icc a r := ⟨hr, le_refl r⟩
  rw [volterraGlobalE_eq_sol hr q g hq hg r hmem, volterraSolE_spec hr q g hq hg ⟨r, hmem⟩]
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro t ht
  dsimp only []
  rw [Set.uIcc_of_le hr] at ht
  rw [volterraGlobalE_eq_sol hr q g hq hg t ht, Set.IccExtend_of_mem hr _ ht]

/-- The global solution is continuous on every compact `[a,b]` (it *is* the bundled local solution
there). -/
theorem volterraGlobalE_continuousOn (hab : a ≤ b) (q g : ℝ → E)
    (hq : Continuous q) (hg : Continuous g) :
    ContinuousOn (volterraGlobalE a q g hq hg) (Set.Icc a b) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : Set.restrict (Set.Icc a b) (volterraGlobalE a q g hq hg)
      = fun x => volterraSolE hab q g hq hg x := by
    funext x
    exact volterraGlobalE_eq_sol hab q g hq hg (x : ℝ) x.2
  rw [heq]
  exact (volterraSolE hab q g hq hg).continuous

/-- The global solution is continuous on the whole half-line `[a,∞)` (glue the compact-interval
continuity: each point of `Ici a` sits in the interior of some `Icc a (x+1)` relative to `Ici a`). -/
theorem volterraGlobalE_continuousOn_Ici (a : ℝ) (q g : ℝ → E)
    (hq : Continuous q) (hg : Continuous g) :
    ContinuousOn (volterraGlobalE a q g hq hg) (Set.Ici a) := by
  intro x hx
  have hax : a ≤ x := hx
  have hb : a ≤ x + 1 := by linarith
  have hcont := (volterraGlobalE_continuousOn (b := x + 1) hb q g hq hg) x ⟨hax, by linarith⟩
  refine hcont.mono_of_mem_nhdsWithin ?_
  exact Filter.mem_of_superset
    (inter_mem_nhdsWithin (Set.Ici a) (IsOpen.mem_nhds isOpen_Iio (show x < x + 1 by linarith)))
    (fun y hy => ⟨hy.1, le_of_lt hy.2⟩)

end FMSA.VolterraBanach
