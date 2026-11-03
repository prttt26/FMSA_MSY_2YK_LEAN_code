import MSAConvergence.M3MonodromyPath
import MSAConvergence.ActualComplexBH

/-! From a checked M3 slab chain to the Taylor-radius bound `R ≤ 84` of the original HS germ.

The chain starts at the HS seed (`τ = 0`), runs along edge 0 to `V₀` (`u = 1`), and then around
the loop back to `V₀` (`u = 5`). The two endpoint boxes at `u = 1` and `u = 5` are disjoint, so
the continuous regular lift changes value around the loop. The whole path lies in `|τ| < 84`.
`ActualComplexBH.exists_hs_real_series_radius_bound_of_changed_complex_lift` then bounds the
radius of the real coupling series of the original HS germ. All numerical content is the
hypothesis `chainRest … = true` and a few cheap executable checks. -/
noncomputable section
namespace FMSA.Convergence.M3TaylorRadius
open Set Filter Topology
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.ComplexPolynomialSystem
open FMSA.Convergence.ActualComplexBH FMSA.Convergence.CanonicalNeighborhood
open ScaledIntegerIntervals ComplexTaylorModels ComplexTaylorSpecs ComplexTaylorCells
open ComplexTaylorPaths M3TaylorSpec M3MonodromyPath M3ResidualModel

/-! ### The HS seed -/

/-- The original HS seed in the ordered coordinates `Dt₁, Dt₂, G₁, G₂`. -/
def seedX : Fin 4 → ℝ := fun i => amplitudeValues ((0 : TailMatrix (Fin 2) 1), baseSeed z rho sigma) (index i)

theorem point_seedX : point seedX = ((0 : TailMatrix (Fin 2) 1), baseSeed z rho sigma) :=
  point_coordinates_inverse _

theorem seedX_formula : formula 0 seedX = 0 := by
  obtain ⟨hz, hsigma, hrho, -⟩ := physical_data
  have hv : 0 < vacMix rho sigma := by rw [vacancy_eq]; norm_num
  have h := baseSeed_isRoot z rho sigma hz hv hrho hsigma
  rw [← actual_root_iff_formula_zero, point_seedX, zero_smul]
  exact h

theorem seedX_zero : seedX 0 = 0 ∧ seedX 1 = 0 := ⟨rfl, rfl⟩

/-- Rational bounds on the seed `G` values. -/
theorem seedX_bounds :
    (2064 / 5000 : ℝ) ≤ seedX 2 ∧ seedX 2 ≤ 2065 / 5000 ∧
      (1286 / 5000 : ℝ) ≤ seedX 3 ∧ seedX 3 ≤ 1287 / 5000 := by
  have hf := seedX_formula
  have h2 := congrFun hf 2
  have h3 := congrFun hf 3
  obtain ⟨h0, h1⟩ := seedX_zero
  simp only [formula, h0, h1] at h2 h3
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h2 h3
  have e7 := Real.exp_pos (-7)
  have e14 := Real.exp_pos (-14)
  have e7u : Real.exp (-7) ≤ 1 / 1000 := by
    have := M3PhysicalBounds.exp_seed_multiple 14
    norm_num at this ⊢; linarith [this.2]
  have e14u : Real.exp (-14) ≤ 1 / 100000 := by
    have := M3PhysicalBounds.exp_seed_multiple 28
    norm_num at this ⊢; linarith [this.2]
  have hpi := Real.pi_pos
  have k2 : seedX 2 * (8222 + 2852 * Real.exp (-7)) = 71300 / 21 := by
    have : Real.pi * (seedX 2 * (8222 + 2852 * Real.exp (-7)) - 71300 / 21) = 0 := by linear_combination 2023 * h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hpi.ne'
    · linarith
  have k3 : seedX 3 * (5989 + 647 * Real.exp (-14)) = 32350 / 21 := by
    have : Real.pi * (seedX 3 * (5989 + 647 * Real.exp (-14)) - 32350 / 21) = 0 := by linear_combination 2023 * h3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hpi.ne'
    · linarith
  have p2 : 0 < seedX 2 := by nlinarith
  have p3 : 0 < seedX 3 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The executable seed-box check: the first slab box contains the rational seed bounds. -/
def seedOK (d : Cell) : Bool :=
  let X := fun i => getB d.X i
  encQ (X 0).re 0 1 && encQ (X 0).im 0 1 && encQ (X 1).re 0 1 && encQ (X 1).im 0 1 &&
    encQ (X 2).re 2064 5000 && encQ (X 2).re 2065 5000 && encQ (X 2).im 0 1 &&
    encQ (X 3).re 1286 5000 && encQ (X 3).re 1287 5000 && encQ (X 3).im 0 1

theorem seed_inBox {d : Cell} (h : seedOK d = true) : InBox S 4 d (fun i => (seedX i : ℂ)) := by
  simp only [seedOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0r, h0i⟩, h1r⟩, h1i⟩, h2a⟩, h2b⟩, h2i⟩, h3a⟩, h3b⟩, h3i⟩ := h
  obtain ⟨b2l, b2u, b3l, b3u⟩ := seedX_bounds
  obtain ⟨z0, z1⟩ := seedX_zero
  have one : (0 : ℤ) < 1 := one_pos
  have q : (0 : ℤ) < 5000 := by norm_num
  have zero_of {A : Interval} (hA : encQ A 0 1 = true) : Encloses S A 0 := by
    simpa using encQ_sound one hA
  have mid {A : Interval} {x : ℝ} {l u : ℤ} (hl : encQ A l 5000 = true) (hu : encQ A u 5000 = true)
      (hxl : (l : ℝ) / 5000 ≤ x) (hxu : x ≤ (u : ℝ) / 5000) : Encloses S A x :=
    ⟨(encQ_sound q hl).1.trans (by exact_mod_cast hxl), hxu.trans (by exact_mod_cast (encQ_sound q hu).2)⟩
  intro i
  fin_cases i
  · exact ⟨by simpa [z0] using zero_of h0r, by simpa using zero_of h0i⟩
  · exact ⟨by simpa [z1] using zero_of h1r, by simpa using zero_of h1i⟩
  · exact ⟨by simpa using mid h2a h2b (by norm_num; linarith) (by norm_num; linarith), by simpa using zero_of h2i⟩
  · exact ⟨by simpa using mid h3a h3b (by norm_num; linarith) (by norm_num; linarith), by simpa using zero_of h3i⟩

theorem seed_root : complexResidual polynomial (gam (upos 0 0), fun i => (seedX i : ℂ)) = 0 := by
  have hg : gam (upos 0 0) = ((0 : ℝ) : ℂ) := by
    rw [gam_upos (by norm_num) (by unfold G; positivity)]; apply Complex.ext <;> simp [M3MonodromyPath.W]
  rw [hg, complexResidual_ofReal]
  funext i
  rw [polynomial_eval, seedX_formula]
  simp

/-! ### The loop and the disc -/

def disjI (A B : Interval) : Bool := decide (A.hi < B.lo) || decide (B.hi < A.lo)

/-- Executable disjointness of two root boxes: some component interval separates them. -/
def boxDisjoint (n : ℕ) (A B : Cell) : Bool :=
  (List.range n).any fun i => disjI (getB A.X i).re (getB B.X i).re || disjI (getB A.X i).im (getB B.X i).im

theorem disjI_sound {A B : Interval} {x y : ℝ} (h : disjI A B = true) (hx : Encloses S A x)
    (hy : Encloses S B y) : x ≠ y := by
  have hS : (0 : ℝ) < S := by exact_mod_cast S_pos
  simp only [disjI, Bool.or_eq_true, decide_eq_true_eq] at h
  intro hxy
  subst hxy
  rcases h with h | h
  · have : (A.hi : ℝ) / S < B.lo / S := div_lt_div_of_pos_right (by exact_mod_cast h) hS
    linarith [hx.2, hy.1]
  · have : (B.hi : ℝ) / S < A.lo / S := div_lt_div_of_pos_right (by exact_mod_cast h) hS
    linarith [hx.1, hy.2]

theorem ne_of_boxDisjoint {n : ℕ} {A B : Cell} (h : boxDisjoint n A B = true) {z w : Fin n → ℂ}
    (hz : InBox S n A z) (hw : InBox S n B w) : z ≠ w := by
  obtain ⟨i, hi, hd⟩ := List.any_eq_true.mp h
  have hi' := List.mem_range.mp hi
  simp only [Bool.or_eq_true] at hd
  intro hzw
  subst hzw
  rcases hd with hd | hd
  · exact disjI_sound hd (hz ⟨i, hi'⟩).1 (hw ⟨i, hi'⟩).1 rfl
  · exact disjI_sound hd (hz ⟨i, hi'⟩).2 (hw ⟨i, hi'⟩).2 rfl

theorem wC_norm_lt (k : ℕ) (hk : k ≤ 5) : ‖wC k‖ < 84 := by
  have h : ‖wC k‖ ^ 2 < 84 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    interval_cases k <;> simp [wC, M3MonodromyPath.W] <;> norm_num
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h

theorem gam_norm_lt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) : ‖gam t‖ < 84 := by
  have key : ∀ k : ℕ, k < 5 → (k : ℝ) ≤ t → t ≤ k + 1 → ‖gam t‖ < 84 := by
    intro k hk h0 h1
    have ht' : t = k + (t - k) := by ring
    rw [ht', gam_edge hk (by linarith) (by linarith)]
    set l : ℝ := t - k
    have hl0 : 0 ≤ l := by simp only [l]; linarith
    have hl1 : l ≤ 1 := by simp only [l]; linarith
    have hcomb : wC k + (l : ℂ) * (wC (k + 1) - wC k) = ((1 - l : ℝ) : ℂ) * wC k + (l : ℂ) * wC (k + 1) := by
      push_cast; ring
    rw [hcomb]
    calc ‖((1 - l : ℝ) : ℂ) * wC k + (l : ℂ) * wC (k + 1)‖
        ≤ (1 - l) * ‖wC k‖ + l * ‖wC (k + 1)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg hl0]
      _ < (1 - l) * 84 + l * 84 := by
          rcases eq_or_lt_of_le hl1 with h | h
          · rw [h]; simp; exact wC_norm_lt (k + 1) (by omega)
          · have := wC_norm_lt k (by omega)
            have := wC_norm_lt (k + 1) (by omega)
            nlinarith
      _ = 84 := by ring
  obtain ⟨h0, h5⟩ := ht
  by_cases a1 : t ≤ 1
  · exact key 0 (by norm_num) (by simpa using h0) (by simpa using a1)
  by_cases a2 : t ≤ 2
  · exact key 1 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
  by_cases a3 : t ≤ 3
  · exact key 2 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
  by_cases a4 : t ≤ 4
  · exact key 3 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
  · exact key 4 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem gam_loop : gam (upos 0 G) = gam (upos 4 G) := by
  rw [gam_upos (by norm_num) le_rfl, gam_upos (by norm_num) le_rfl]
  apply Complex.ext <;> simp [M3MonodromyPath.W] <;> ring

theorem upos_zero : upos 0 0 = 0 := by simp [upos]
theorem upos_one : upos 0 G = 1 := by simp [upos, G_pos.ne']
theorem upos_five : upos 4 G = 5 := by simp [upos, G_pos.ne']; norm_num

/-! ### The radius bound from a checked chain -/

theorem complexAmplitudes_injective : Function.Injective complexAmplitudes := by
  intro a b h
  funext i
  have := congrFun h (index i)
  simpa [complexAmplitudes] using this

/-- **M3 Taylor radius from a checked chain.** -/
theorem radius_of_chain (x₀ : Slab) (xs₀ rest : List Slab)
    (h₀ : chainRest (x₀ :: xs₀) = true)
    (hrest : chainFrom (lastPos (x₀.seg, x₀.s1) xs₀) (lastCell x₀.ends xs₀) rest = true)
    (hpos : x₀.seg = 0 ∧ x₀.s0 = 0)
    (hA : lastPos (x₀.seg, x₀.s1) xs₀ = (0, G))
    (hB : lastPos (lastPos (x₀.seg, x₀.s1) xs₀) rest = (4, G))
    (hdisj : boxDisjoint 4 (lastCell x₀.ends xs₀) (lastCell (lastCell x₀.ends xs₀) rest) = true)
    (hseed : seedOK x₀.cell = true) :
    ∃ (p : ℝ → TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)
      (a : FormalMultilinearSeries ℝ ℝ (TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)),
      p 0 = (0, baseSeed z rho sigma) ∧ HasFPowerSeriesAt p a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • strengths) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) ∧
      a.radius ≤ ENNReal.ofReal 84 ∧ ∀ tau : ℝ, 84 < |tau| → ¬Summable (fun n => tau ^ n • a.coeff n) := by
  have hs := S_pos
  have hrel := spec_rel
  have hF := polynomial_eq_spec
  have hγ := gam_continuous
  simp only [chainRest, Bool.and_eq_true] at h₀
  obtain ⟨hx₀, hxs₀⟩ := h₀
  have hf₀ := slabFacts_of_ok hx₀
  rw [hpos.1, hpos.2, upos_zero] at hf₀
  have hA' : lastPos (0, x₀.s1) xs₀ = (0, G) := by simpa [hpos.1] using hA
  rw [hpos.1, hA'] at hrest hB
  rw [hpos.1] at hxs₀
  -- the first slab, from the seed
  have hseedroot : complexResidual polynomial (gam 0, fun i => (seedX i : ℂ)) = 0 := by
    rw [← upos_zero]; exact seed_root
  obtain ⟨p, hp, hp0⟩ := start_chain hs hrel hF hγ hf₀ (seed_inBox hseed) hseedroot
  -- the rest of edge 0
  obtain ⟨hc₀, he₀⟩ := chainFacts_of_chainFrom xs₀ hxs₀
  obtain ⟨p₁, hp₁, -, heq₁⟩ := extend_chain hs hrel hF hγ (toList xs₀) hf₀.le hp hc₀
  rw [he₀, hA', upos_one] at hp₁
  -- the loop
  obtain ⟨hc₁, he₁⟩ := chainFacts_of_chainFrom rest hrest
  have h1 : upos (0, G).1 (0, G).2 = 1 := upos_one
  rw [h1] at hc₁ he₁
  obtain ⟨p₂, hp₂, -, heq₂⟩ := extend_chain hs hrel hF hγ (toList rest) zero_le_one hp₁ hc₁
  rw [he₁, hB, upos_five] at hp₂
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hseed₂ : p₂ 0 = fun i => (seedX i : ℂ) := by
    rw [heq₂ 0 h01, heq₁ 0 ⟨le_rfl, hf₀.le⟩, hp0]
  have hA₂ : InBox S 4 (lastCell x₀.ends xs₀) (p₂ 1) := by
    rw [heq₂ 1 ⟨zero_le_one, le_rfl⟩]; exact hp₁.2.2
  have hne : p₂ 1 ≠ p₂ 5 := ne_of_boxDisjoint hdisj hA₂ hp₂.2.2
  -- apply the generic changed-lift radius bound
  haveI : PreconnectedSpace (Icc (0 : ℝ) 5) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  obtain ⟨hz, hsigma, hrho, hK⟩ := physical_data
  have hv : 0 < vacMix rho sigma := by rw [vacancy_eq]; norm_num
  have hmem : ∀ t : Icc (0 : ℝ) 5, (t : ℝ) ∈ Icc (0 : ℝ) 5 := fun t => t.2
  refine exists_hs_real_series_radius_bound_of_changed_complex_lift z hz rho sigma hsigma hrho strengths
    hK hv (fun t : Icc (0 : ℝ) 5 => gam t) (fun t => complexAmplitudes (p₂ t))
    ⟨0, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩ ⟨5, by norm_num, le_rfl⟩
    (hγ.comp continuous_subtype_val) ?_ ?_ ?_ ?_ ?_ 84 (by norm_num) ?_ ?_ ?_
  · have hc : Continuous fun t : Icc (0 : ℝ) 5 => p₂ t := hp₂.1.restrict
    exact (continuous_pi fun j => (continuous_apply _).comp hc)
  · intro t
    exact (complex_root_iff _ _).mpr (hp₂.2.1 t (hmem t)).1
  · intro t
    have h := (hp₂.2.1 t (hmem t)).2
    rw [← complex_jacobian_det_dictionary] at h
    convert h using 2
  · change gam 1 = gam 5
    rw [← upos_one, ← upos_five, gam_loop]
  · intro h
    exact hne (complexAmplitudes_injective h)
  · intro t
    exact gam_norm_lt (hmem t)
  · change gam 0 = 0
    rw [← upos_zero, gam_upos (by norm_num) (by unfold G; positivity)]
    apply Complex.ext <;> simp [M3MonodromyPath.W]
  · change complexAmplitudes (p₂ 0) = _
    rw [hseed₂, complex_amplitudes_ofReal, point_seedX]

/-! ### List-level form, for concrete generated chains -/

def lastPosL : List Slab → ℕ × ℕ
  | [] => (0, 0)
  | x :: xs => lastPos (x.seg, x.s1) xs

def lastCellL : List Slab → Cell
  | [] => ⟨[], [], [], CBox.zero⟩
  | x :: xs => lastCell x.ends xs

def headPos : List Slab → ℕ × ℕ
  | [] => (1, 1)
  | x :: _ => (x.seg, x.s0)

def headCell : List Slab → Cell
  | [] => ⟨[], [], [], CBox.zero⟩
  | x :: _ => x.cell

/-- A chunked chain: the first chunk's own checks, the chunk junctions and every later chunk. -/
theorem chainRest_flatten (c : List Slab) (cs : List (List Slab)) (hne : c ≠ [])
    (hc : chainRest c = true)
    (hj : junctionsOK (lastPosL c) (lastCellL c) cs = true) (hcs : ∀ c' ∈ cs, chainRest c' = true) :
    chainRest (c ++ cs.flatten) = true := by
  cases c with
  | nil => exact absurd rfl hne
  | cons x xs =>
    simp only [chainRest, Bool.and_eq_true] at hc
    rw [List.cons_append]
    show (slabOK x && chainFrom (x.seg, x.s1) x.ends (xs ++ cs.flatten)) = true
    rw [chainFrom_append]
    simp only [Bool.and_eq_true]
    exact ⟨hc.1, hc.2, chainFrom_flatten cs _ _ hj hcs⟩

/-- **M3 Taylor radius from a checked chain**, with all hypotheses on concrete lists. -/
theorem radius_of_chainL (chain₀ rest : List Slab)
    (h₀ : chainRest chain₀ = true)
    (hrest : chainFrom (lastPosL chain₀) (lastCellL chain₀) rest = true)
    (hpos : headPos chain₀ = (0, 0))
    (hA : lastPosL chain₀ = (0, G))
    (hB : lastPos (lastPosL chain₀) rest = (4, G))
    (hdisj : boxDisjoint 4 (lastCellL chain₀) (lastCell (lastCellL chain₀) rest) = true)
    (hseed : seedOK (headCell chain₀) = true) :
    ∃ (p : ℝ → TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)
      (a : FormalMultilinearSeries ℝ ℝ (TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)),
      p 0 = (0, baseSeed z rho sigma) ∧ HasFPowerSeriesAt p a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • strengths) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) ∧
      a.radius ≤ ENNReal.ofReal 84 ∧ ∀ tau : ℝ, 84 < |tau| → ¬Summable (fun n => tau ^ n • a.coeff n) := by
  cases chain₀ with
  | nil => simp [headPos] at hpos
  | cons x xs =>
    simp only [headPos, Prod.mk.injEq] at hpos
    exact radius_of_chain x xs rest h₀ hrest hpos hA hB hdisj hseed

/-- info: 'FMSA.Convergence.M3TaylorRadius.point_seedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.point_seedX
/-- info: 'FMSA.Convergence.M3TaylorRadius.seedX_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.seedX_formula
/-- info: 'FMSA.Convergence.M3TaylorRadius.seedX_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.seedX_zero
/-- info: 'FMSA.Convergence.M3TaylorRadius.seedX_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.seedX_bounds
/-- info: 'FMSA.Convergence.M3TaylorRadius.seed_inBox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.seed_inBox
/-- info: 'FMSA.Convergence.M3TaylorRadius.seed_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.seed_root
/-- info: 'FMSA.Convergence.M3TaylorRadius.disjI_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.disjI_sound
/-- info: 'FMSA.Convergence.M3TaylorRadius.ne_of_boxDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.ne_of_boxDisjoint
/-- info: 'FMSA.Convergence.M3TaylorRadius.wC_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.wC_norm_lt
/-- info: 'FMSA.Convergence.M3TaylorRadius.gam_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.gam_norm_lt
/-- info: 'FMSA.Convergence.M3TaylorRadius.gam_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.gam_loop
/-- info: 'FMSA.Convergence.M3TaylorRadius.upos_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.upos_zero
/-- info: 'FMSA.Convergence.M3TaylorRadius.upos_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.upos_one
/-- info: 'FMSA.Convergence.M3TaylorRadius.upos_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.upos_five
/-- info: 'FMSA.Convergence.M3TaylorRadius.complexAmplitudes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.complexAmplitudes_injective
/-- info: 'FMSA.Convergence.M3TaylorRadius.radius_of_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.radius_of_chain
/-- info: 'FMSA.Convergence.M3TaylorRadius.chainRest_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.chainRest_flatten
/-- info: 'FMSA.Convergence.M3TaylorRadius.radius_of_chainL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3TaylorRadius.radius_of_chainL
end FMSA.Convergence.M3TaylorRadius
