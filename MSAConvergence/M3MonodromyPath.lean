import MSAConvergence.ComplexTaylorPaths
import MSAConvergence.M3TaylorSpec

/-! The M3 monodromy polygon and an executable slab-chain check.

The coupling path is the polygon `0 → V₀ → V₁ → V₂ → V₃ → V₀` (vertices in units of `1/64`),
parametrised by `u ∈ [0, 5]` with one unit per edge. A slab is a parameter range `[s₀, s₁]` on
one edge (numerators over `2^40`) with a slab cell and an endpoint cell. `chainFrom` checks all
slabs and the junctions between them; `chainFacts_of_chainFrom` turns a passing check into the
Prop-level `ChainFacts` used by `ComplexTaylorPaths.extend_chain`. -/
noncomputable section
namespace FMSA.Convergence.M3MonodromyPath
open Set ScaledIntegerIntervals ComplexTaylorModels ComplexTaylorSpecs ComplexTaylorCells
open ComplexTaylorPaths M3TaylorSpec

/-- Vertex numerators over `64`: `0, V₀, V₁, V₂, V₃, V₀`. -/
def W : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (-1332, 5185)
  | 2 => (-1316, 5185)
  | 3 => (-1316, 5201)
  | 4 => (-1332, 5201)
  | _ => (-1332, 5185)

def wC (k : ℕ) : ℂ := ⟨((W k).1 : ℝ) / 64, ((W k).2 : ℝ) / 64⟩

def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp01_of_le_zero {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 := by
  unfold clamp01; rw [min_eq_right (by linarith), max_eq_left h]
theorem clamp01_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  unfold clamp01; rw [min_eq_left h, max_eq_right (by norm_num)]
theorem clamp01_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  unfold clamp01; rw [min_eq_right h1, max_eq_right h0]

/-- The polygon, as a finite sum of clamped edge contributions. -/
def gam (u : ℝ) : ℂ := ∑ k ∈ Finset.range 5, (clamp01 (u - k) : ℂ) * (wC (k + 1) - wC k)

theorem gam_continuous : Continuous gam := by
  unfold gam clamp01
  fun_prop

/-- On edge `k` the polygon is affine. -/
theorem gam_edge {k : ℕ} (hk : k < 5) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    gam (k + l) = wC k + (l : ℂ) * (wC (k + 1) - wC k) := by
  have hc : ∀ j : ℕ, clamp01 ((k : ℝ) + l - j) = if j < k then 1 else if j = k then l else 0 := by
    intro j
    split_ifs with hjk hjk'
    · apply clamp01_of_one_le
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
      linarith
    · subst hjk'; rw [add_sub_cancel_left]; exact clamp01_of_mem h0 h1
    · apply clamp01_of_le_zero
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast (show k + 1 ≤ j by omega)
      linarith
  simp only [gam, Finset.sum_range_succ, Finset.sum_range_zero, hc]
  interval_cases k <;> apply Complex.ext <;> simp [wC, W] <;> ring

/-- The parameter grid. -/
def G : ℕ := 2 ^ 40

def upos (k s : ℕ) : ℝ := (k : ℝ) + (s : ℝ) / (G : ℝ)

theorem G_pos : (0 : ℝ) < (G : ℝ) := by unfold G; positivity

/-- `num / den` lies in `A` on the scale `S`. -/
def encQ (A : Interval) (num den : ℤ) : Bool := decide (A.lo * den ≤ num * S) && decide (num * S ≤ A.hi * den)

theorem encQ_sound {A : Interval} {num den : ℤ} (hden : 0 < den) (h : encQ A num den = true) :
    Encloses S A ((num : ℝ) / (den : ℝ)) := by
  simp only [encQ, Bool.and_eq_true, decide_eq_true_eq] at h
  have hS : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos
  have hd : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have h1 : (A.lo : ℝ) * den ≤ num * S := by exact_mod_cast h.1
  have h2 : (num : ℝ) * S ≤ A.hi * den := by exact_mod_cast h.2
  constructor
  · rw [div_le_div_iff₀ hS hd]; linarith
  · rw [div_le_div_iff₀ hd hS]; linarith

/-- The polygon point at `upos k s` lies in the coupling rectangle `T`. -/
def pin (T : CBox) (k s : ℕ) : Bool :=
  let a := W k
  let b := W (k + 1)
  encQ T.re (a.1 * G + s * (b.1 - a.1)) (64 * G) && encQ T.im (a.2 * G + s * (b.2 - a.2)) (64 * G)

theorem gam_upos {k s : ℕ} (hk : k < 5) (hs : s ≤ G) :
    gam (upos k s) = ⟨(((W k).1 * G + s * ((W (k + 1)).1 - (W k).1) : ℤ) : ℝ) / ((64 * G : ℤ) : ℝ),
      (((W k).2 * G + s * ((W (k + 1)).2 - (W k).2) : ℤ) : ℝ) / ((64 * G : ℤ) : ℝ)⟩ := by
  have hG := G_pos
  have h1 : (s : ℝ) / G ≤ 1 := by rw [div_le_one hG]; exact_mod_cast hs
  rw [upos, gam_edge hk (by positivity) h1]
  apply Complex.ext <;> simp [wC] <;> field_simp <;> ring

theorem pin_sound {T : CBox} {k s : ℕ} (hk : k < 5) (hs : s ≤ G) (h : pin T k s = true) :
    CEnc S T (gam (upos k s)) := by
  simp only [pin, Bool.and_eq_true] at h
  have hden : (0 : ℤ) < 64 * G := by unfold G; positivity
  rw [gam_upos hk hs]
  exact ⟨encQ_sound hden h.1, encQ_sound hden h.2⟩

/-- An enclosure holds on a segment if it holds at both ends. -/
theorem encloses_convex {A : Interval} {x y θ : ℝ} (hx : Encloses S A x) (hy : Encloses S A y)
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : Encloses S A (x + θ * (y - x)) := by
  constructor
  · nlinarith [hx.1, hy.1]
  · nlinarith [hx.2, hy.2]

theorem cenc_edge {T : CBox} {k s₀ s₁ : ℕ} (hk : k < 5) (h01 : s₀ ≤ s₁) (hs₁ : s₁ ≤ G)
    (h₀ : pin T k s₀ = true) (h₁ : pin T k s₁ = true) :
    ∀ t ∈ Icc (upos k s₀) (upos k s₁), CEnc S T (gam t) := by
  intro t ht
  have hG := G_pos
  have e0 := pin_sound hk (h01.trans hs₁) h₀
  have e1 := pin_sound hk hs₁ h₁
  set l₀ : ℝ := (s₀ : ℝ) / G
  set l₁ : ℝ := (s₁ : ℝ) / G
  have hl01 : l₀ ≤ l₁ := div_le_div_of_nonneg_right (by exact_mod_cast h01) hG.le
  have hl₀ : 0 ≤ l₀ := by positivity
  have hl₁ : l₁ ≤ 1 := by rw [div_le_one hG]; exact_mod_cast hs₁
  have htk : t = k + (t - k) := by ring
  have hl : t - k ∈ Icc l₀ l₁ := ⟨by simp only [upos] at ht; linarith [ht.1],
    by simp only [upos] at ht; linarith [ht.2]⟩
  rw [upos, gam_edge hk hl₀ (hl01.trans hl₁)] at e0
  rw [upos, gam_edge hk (hl₀.trans hl01) hl₁] at e1
  rw [htk, gam_edge hk (hl₀.trans hl.1) (hl.2.trans hl₁)]
  by_cases heq : l₀ = l₁
  · have : t - k = l₀ := le_antisymm (heq ▸ hl.2) hl.1
    rw [this]; exact e0
  · have hlt : 0 < l₁ - l₀ := sub_pos.mpr (lt_of_le_of_ne hl01 heq)
    set θ := (t - k - l₀) / (l₁ - l₀)
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hl.1]) hlt.le
    have hθ1 : θ ≤ 1 := by rw [div_le_one hlt]; linarith [hl.2]
    have hlin : t - k = l₀ + θ * (l₁ - l₀) := by
      simp only [θ]; field_simp; ring
    constructor
    · have := encloses_convex e0.1 e1.1 hθ0 hθ1
      convert this using 1; simp [hlin]; ring
    · have := encloses_convex e0.2 e1.2 hθ0 hθ1
      convert this using 1; simp [hlin]; ring

/-! ### Executable slabs and chains -/

/-- Literal helpers for generated data: a point box and a general box. -/
def pt (a b : ℤ) : CBox := ⟨⟨a, a⟩, ⟨b, b⟩⟩
def bx (a b c d : ℤ) : CBox := ⟨⟨a, b⟩, ⟨c, d⟩⟩

structure Slab where
  seg : ℕ
  s0 : ℕ
  s1 : ℕ
  cell : Cell
  ends : Cell

def slabOK (x : Slab) : Bool :=
  decide (x.seg < 5) && decide (x.s0 ≤ x.s1) && decide (x.s1 ≤ G) &&
    cellOK S 4 lI x.cell && cellOK S 4 lI x.ends && pin x.cell.T x.seg x.s0 &&
    pin x.cell.T x.seg x.s1 && pin x.ends.T x.seg x.s1 && boxSub 4 x.ends x.cell

theorem slabFacts_of_ok {x : Slab} (h : slabOK x = true) :
    SlabFacts gam S 4 lI (upos x.seg x.s0) (upos x.seg x.s1) x.cell x.ends := by
  simp only [slabOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, h01⟩, hs1⟩, hc⟩, he⟩, hp0⟩, hp1⟩, hpe⟩, hsub⟩ := h
  refine ⟨?_, hc, he, cenc_edge hk h01 hs1 hp0 hp1, pin_sound hk hs1 hpe, hsub⟩
  simp only [upos]
  have := G_pos
  gcongr

/-- Equal parameter positions, also across a vertex. -/
def posEq (p q : ℕ × ℕ) : Bool :=
  (decide (p.1 = q.1) && decide (p.2 = q.2)) ||
    (decide (p.1 + 1 = q.1) && decide (p.2 = G) && decide (q.2 = 0))

theorem upos_of_posEq {p q : ℕ × ℕ} (h : posEq p q = true) : upos p.1 p.2 = upos q.1 q.2 := by
  simp only [posEq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
  · rw [h1, h2]
  · simp only [upos, h2, h3, ← h1]
    have := G_pos
    push_cast
    field_simp
    ring

def chainFrom : ℕ × ℕ → Cell → List Slab → Bool
  | _, _, [] => true
  | p, E, x :: xs => posEq p (x.seg, x.s0) && boxSub 4 E x.cell && slabOK x &&
      chainFrom (x.seg, x.s1) x.ends xs

def toList (xs : List Slab) : SlabList :=
  xs.map fun x => (upos x.seg x.s0, upos x.seg x.s1, x.cell, x.ends)

def lastPos : ℕ × ℕ → List Slab → ℕ × ℕ
  | p, [] => p
  | _, x :: xs => lastPos (x.seg, x.s1) xs

def lastCell : Cell → List Slab → Cell
  | E, [] => E
  | _, x :: xs => lastCell x.ends xs

theorem chainFacts_of_chainFrom : ∀ (xs : List Slab) {p : ℕ × ℕ} {E : Cell},
    chainFrom p E xs = true → ChainFacts gam S 4 lI (upos p.1 p.2) E (toList xs) ∧
      chainEnd (upos p.1 p.2) E (toList xs) = (upos (lastPos p xs).1 (lastPos p xs).2, lastCell E xs)
  | [], p, E, _ => ⟨trivial, rfl⟩
  | x :: xs, p, E, h => by
    simp only [chainFrom, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, hb⟩, hx⟩, hrest⟩ := h
    obtain ⟨hf, he⟩ := chainFacts_of_chainFrom xs hrest
    refine ⟨⟨(upos_of_posEq hp).symm, slabFacts_of_ok hx, hb, hf⟩, ?_⟩
    simp only [toList, List.map_cons, chainEnd]
    exact he

theorem chainFrom_append : ∀ (l₁ l₂ : List Slab) (p : ℕ × ℕ) (E : Cell),
    chainFrom p E (l₁ ++ l₂) = (chainFrom p E l₁ && chainFrom (lastPos p l₁) (lastCell E l₁) l₂)
  | [], l₂, p, E => by simp [chainFrom, lastPos, lastCell]
  | x :: xs, l₂, p, E => by
    simp only [List.cons_append, chainFrom, lastPos, lastCell, chainFrom_append xs l₂, Bool.and_assoc]

/-- Everything a chunk of slabs checks internally, independent of what came before it. -/
def chainRest : List Slab → Bool
  | [] => true
  | x :: xs => slabOK x && chainFrom (x.seg, x.s1) x.ends xs

/-- The junctions between consecutive chunks, starting from position `p` and box `E`. -/
def junctionsOK : ℕ × ℕ → Cell → List (List Slab) → Bool
  | _, _, [] => true
  | _, _, [] :: _ => false
  | p, E, (x :: xs) :: cs => posEq p (x.seg, x.s0) && boxSub 4 E x.cell &&
      junctionsOK (lastPos (x.seg, x.s1) xs) (lastCell x.ends xs) cs

theorem chainFrom_flatten : ∀ (cs : List (List Slab)) (p : ℕ × ℕ) (E : Cell),
    junctionsOK p E cs = true → (∀ c ∈ cs, chainRest c = true) → chainFrom p E cs.flatten = true
  | [], _, _, _, _ => rfl
  | [] :: _, _, _, h, _ => by simp [junctionsOK] at h
  | (x :: xs) :: cs, p, E, hj, hc => by
    simp only [junctionsOK, Bool.and_eq_true] at hj
    have hx := hc (x :: xs) List.mem_cons_self
    simp only [chainRest, Bool.and_eq_true] at hx
    rw [List.flatten_cons, chainFrom_append]
    simp only [chainFrom, Bool.and_eq_true, lastPos, lastCell]
    exact ⟨⟨⟨⟨hj.1.1, hj.1.2⟩, hx.1⟩, hx.2⟩,
      chainFrom_flatten cs _ _ hj.2 fun c hc' => hc c (List.mem_cons_of_mem _ hc')⟩

/-- The junction part of `chainFrom`, without the slab checks. -/
def linksFrom : ℕ × ℕ → Cell → List Slab → Bool
  | _, _, [] => true
  | p, E, x :: xs => posEq p (x.seg, x.s0) && boxSub 4 E x.cell && linksFrom (x.seg, x.s1) x.ends xs

theorem chainFrom_of_links : ∀ (xs : List Slab) (p : ℕ × ℕ) (E : Cell),
    linksFrom p E xs = true → xs.all slabOK = true → chainFrom p E xs = true
  | [], _, _, _, _ => rfl
  | x :: xs, p, E, hl, ha => by
    simp only [linksFrom, Bool.and_eq_true] at hl
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [chainFrom, Bool.and_eq_true]
    exact ⟨⟨⟨hl.1.1, hl.1.2⟩, ha.1⟩, chainFrom_of_links xs _ _ hl.2 ha.2⟩

/-- A chunk passes if its slabs pass one by one and its internal junctions hold. -/
theorem chainRest_of_slabs (x : Slab) (xs : List Slab) (hx : slabOK x = true)
    (hl : linksFrom (x.seg, x.s1) x.ends xs = true) (ha : xs.all slabOK = true) :
    chainRest (x :: xs) = true := by
  simp only [chainRest, Bool.and_eq_true]
  exact ⟨hx, chainFrom_of_links xs _ _ hl ha⟩

/-- info: 'FMSA.Convergence.M3MonodromyPath.clamp01_of_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.clamp01_of_le_zero
/-- info: 'FMSA.Convergence.M3MonodromyPath.clamp01_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.clamp01_of_one_le
/-- info: 'FMSA.Convergence.M3MonodromyPath.clamp01_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.clamp01_of_mem
/-- info: 'FMSA.Convergence.M3MonodromyPath.gam_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.gam_continuous
/-- info: 'FMSA.Convergence.M3MonodromyPath.gam_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.gam_edge
/-- info: 'FMSA.Convergence.M3MonodromyPath.G_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.G_pos
/-- info: 'FMSA.Convergence.M3MonodromyPath.encQ_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.encQ_sound
/-- info: 'FMSA.Convergence.M3MonodromyPath.gam_upos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.gam_upos
/-- info: 'FMSA.Convergence.M3MonodromyPath.pin_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.pin_sound
/-- info: 'FMSA.Convergence.M3MonodromyPath.encloses_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.encloses_convex
/-- info: 'FMSA.Convergence.M3MonodromyPath.cenc_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.cenc_edge
/-- info: 'FMSA.Convergence.M3MonodromyPath.slabFacts_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.slabFacts_of_ok
/-- info: 'FMSA.Convergence.M3MonodromyPath.upos_of_posEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.upos_of_posEq
/-- info: 'FMSA.Convergence.M3MonodromyPath.chainFacts_of_chainFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.chainFacts_of_chainFrom
/-- info: 'FMSA.Convergence.M3MonodromyPath.chainFrom_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.chainFrom_append
/-- info: 'FMSA.Convergence.M3MonodromyPath.chainFrom_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.chainFrom_flatten
/-- info: 'FMSA.Convergence.M3MonodromyPath.chainFrom_of_links' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.chainFrom_of_links
/-- info: 'FMSA.Convergence.M3MonodromyPath.chainRest_of_slabs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3MonodromyPath.chainRest_of_slabs
end FMSA.Convergence.M3MonodromyPath
