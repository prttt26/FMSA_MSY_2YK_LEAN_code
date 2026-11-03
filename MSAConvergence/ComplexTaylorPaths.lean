import MSAConvergence.ComplexTaylorCells
import Mathlib.Topology.Order.ProjIcc

/-! Chaining cell lifts along a continuous coupling path into one continuous regular root lift.

A slab is a parameter interval `[a, c]` with two checked cells:
* a slab cell, whose coupling rectangle contains `γ t` for every `t ∈ [a, c]`;
* an endpoint cell at `c`, whose box lies in the slab box.

Consecutive slabs are glued at the endpoint box. Uniqueness in each slab box makes the two lifts
agree at the junction. -/
noncomputable section
namespace FMSA.Convergence.ComplexTaylorPaths
open Set ScaledIntegerIntervals ComplexTaylorModels ComplexTaylorSpecs ComplexTaylorCells
open ComplexPolynomialSystem

variable {s : ℤ} {n : ℕ} {F : Fin n → MvPolynomial (Option (Fin n)) ℝ} {lI : ℕ → SpecI} {lR : ℕ → SpecR}
variable (γ : ℝ → ℂ)

def InBox (s : ℤ) (n : ℕ) (d : Cell) (z : Fin n → ℂ) : Prop := ∀ i : Fin n, CEnc s (getB d.X i) (z i)

/-- Executable inclusion of root boxes. -/
def boxSub (n : ℕ) (A B : Cell) : Bool :=
  (List.range n).all fun i =>
    inside (getB A.X i).re (getB B.X i).re && inside (getB A.X i).im (getB B.X i).im

theorem inBox_mono (hs : 0 < s) {A B : Cell} (h : boxSub n A B = true) {z : Fin n → ℂ}
    (hz : InBox s n A z) : InBox s n B z := by
  intro i
  have hi := List.all_eq_true.mp h i (List.mem_range.mpr i.isLt)
  simp only [inside, Bool.and_eq_true, decide_eq_true_eq] at hi
  exact ⟨ScaledRectangleCertificates.encloses_mono s hs hi.1.1 hi.1.2 (hz i).1,
    ScaledRectangleCertificates.encloses_mono s hs hi.2.1 hi.2.2 (hz i).2⟩

/-- A continuous regular lift on `[a, b]` ending in the box of `E`. -/
def Ext (s : ℤ) (n : ℕ) (F : Fin n → MvPolynomial (Option (Fin n)) ℝ) (a b : ℝ)
    (p : ℝ → (Fin n → ℂ)) (E : Cell) : Prop :=
  ContinuousOn p (Icc a b) ∧
    (∀ t ∈ Icc a b, complexResidual F (γ t, p t) = 0 ∧ (complexJacobian F (γ t, p t)).det ≠ 0) ∧
    InBox s n E (p b)

/-- The checked facts about one slab on `[a, c]`. -/
structure SlabFacts (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) (a c : ℝ) (d e : Cell) : Prop where
  le : a ≤ c
  cell : cellOK s n lI d = true
  ends : cellOK s n lI e = true
  path : ∀ t ∈ Icc a c, CEnc s d.T (γ t)
  endT : CEnc s e.T (γ c)
  sub : boxSub n e d = true

variable {γ}

/-- The slab lift, extended to all of `ℝ` by clamping. -/
theorem slab_lift (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) (hγ : Continuous γ) {a c : ℝ} {d e : Cell}
    (h : SlabFacts γ s n lI a c d e) :
    ∃ q : ℝ → (Fin n → ℂ), Continuous q ∧ (∀ t ∈ Icc a c,
      InBox s n d (q t) ∧ complexResidual F (γ t, q t) = 0 ∧ (complexJacobian F (γ t, q t)).det ≠ 0 ∧
      ∀ z, InBox s n d z → complexResidual F (γ t, z) = 0 → z = q t) ∧ InBox s n e (q c) := by
  obtain ⟨p, hpc, hp⟩ := cell_lift (F := F) (lR := lR) hs hrel hF h.cell
    (fun t : Icc a c => γ t) (hγ.comp continuous_subtype_val) (fun t => h.path t t.2)
  refine ⟨IccExtend h.le p, hpc.Icc_extend', fun t ht => ?_, ?_⟩
  · rw [IccExtend_of_mem _ _ ht]
    exact hp ⟨t, ht⟩
  · obtain ⟨r, -, hr⟩ := cell_lift (F := F) (lR := lR) hs hrel hF h.ends
      (fun _ : Unit => γ c) continuous_const (fun _ => h.endT)
    obtain ⟨hrbox, hrroot, -, -⟩ := hr ()
    have hc : c ∈ Icc a c := ⟨h.le, le_rfl⟩
    rw [IccExtend_of_mem _ _ hc]
    have heq := (hp ⟨c, hc⟩).2.2.2 (r ()) (inBox_mono hs h.sub hrbox) hrroot
    rw [← heq]
    exact hrbox

/-- Extend a lift on `[a, b]` across one more slab `[b, c]`. -/
theorem extend_slab (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) (hγ : Continuous γ) {a b c : ℝ} {p : ℝ → (Fin n → ℂ)}
    {E d e : Cell} (hab : a ≤ b) (hp : Ext γ s n F a b p E) (h : SlabFacts γ s n lI b c d e)
    (hj : boxSub n E d = true) :
    ∃ p', Ext γ s n F a c p' e ∧ ∀ t ∈ Icc a b, p' t = p t := by
  obtain ⟨q, hqc, hq, hqe⟩ := slab_lift hs hrel hF hγ h
  have hb : b ∈ Icc b c := ⟨le_rfl, h.le⟩
  have hbb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hpq : p b = q b := (hq b hb).2.2.2 (p b) (inBox_mono hs hj hp.2.2) (hp.2.1 b hbb).1
  refine ⟨fun t => if t ≤ b then p t else q t, ⟨?_, ?_, ?_⟩, fun t ht => if_pos ht.2⟩
  · have h1 : ContinuousOn (fun t => if t ≤ b then p t else q t) (Icc a b) :=
      hp.1.congr fun t ht => if_pos ht.2
    have h2 : ContinuousOn (fun t => if t ≤ b then p t else q t) (Icc b c) := by
      refine hqc.continuousOn.congr fun t ht => ?_
      by_cases htb : t ≤ b
      · have : t = b := le_antisymm htb ht.1
        subst this; simp [hpq]
      · simp [htb]
    have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hab h.le] at this
  · intro t ht
    by_cases htb : t ≤ b
    · simp only [htb, if_true]; exact hp.2.1 t ⟨ht.1, htb⟩
    · simp only [htb, if_false]
      obtain ⟨-, hr, hd, -⟩ := hq t ⟨(not_le.mp htb).le, ht.2⟩
      exact ⟨hr, hd⟩
  · by_cases hcb : c ≤ b
    · have : c = b := le_antisymm hcb h.le
      subst this
      simp only [le_refl, if_true, hpq]; exact hqe
    · simp only [hcb, if_false]; exact hqe

/-- A list of slabs with their parameter intervals: `(a, c, slab cell, endpoint cell)`. -/
abbrev SlabList := List (ℝ × ℝ × Cell × Cell)

/-- Prop-level chain conditions: each slab is checked, starts where the previous one ended, and
its box contains the previous endpoint box. -/
def ChainFacts (γ : ℝ → ℂ) (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) : ℝ → Cell → SlabList → Prop
  | _, _, [] => True
  | b, E, x :: xs => x.1 = b ∧ SlabFacts γ s n lI x.1 x.2.1 x.2.2.1 x.2.2.2 ∧
      boxSub n E x.2.2.1 = true ∧ ChainFacts γ s n lI x.2.1 x.2.2.2 xs

def chainEnd : ℝ → Cell → SlabList → ℝ × Cell
  | b, E, [] => (b, E)
  | _, _, x :: xs => chainEnd x.2.1 x.2.2.2 xs

theorem extend_chain (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) (hγ : Continuous γ) :
    ∀ (xs : SlabList) {a b : ℝ} {p : ℝ → (Fin n → ℂ)} {E : Cell}, a ≤ b → Ext γ s n F a b p E →
      ChainFacts γ s n lI b E xs →
      ∃ p', Ext γ s n F a (chainEnd b E xs).1 p' (chainEnd b E xs).2 ∧ a ≤ (chainEnd b E xs).1 ∧
        ∀ t ∈ Icc a b, p' t = p t
  | [], a, b, p, E, hab, hp, _ => ⟨p, hp, hab, fun _ _ => rfl⟩
  | x :: xs, a, b, p, E, hab, hp, ⟨hx, hf, hj, hrest⟩ => by
    obtain ⟨b', c', d, e⟩ := x
    simp only at hx hf hj hrest
    subst hx
    obtain ⟨p1, hp1, heq1⟩ := extend_slab hs hrel hF hγ hab hp hf hj
    obtain ⟨p2, hp2, hle, heq2⟩ := extend_chain hs hrel hF hγ xs (hab.trans hf.le) hp1 hrest
    refine ⟨p2, hp2, hle, fun t ht => ?_⟩
    rw [heq2 t ⟨ht.1, ht.2.trans hf.le⟩, heq1 t ht]

/-- Starting a chain at a known root `z₀` inside the first slab box. -/
theorem start_chain (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) (hγ : Continuous γ) {a c : ℝ} {d e : Cell}
    (h : SlabFacts γ s n lI a c d e) {z₀ : Fin n → ℂ} (hz₀ : InBox s n d z₀)
    (hr₀ : complexResidual F (γ a, z₀) = 0) :
    ∃ p, Ext γ s n F a c p e ∧ p a = z₀ := by
  obtain ⟨q, hqc, hq, hqe⟩ := slab_lift hs hrel hF hγ h
  have ha : a ∈ Icc a c := ⟨le_rfl, h.le⟩
  refine ⟨q, ⟨hqc.continuousOn, fun t ht => ⟨(hq t ht).2.1, (hq t ht).2.2.1⟩, hqe⟩, ?_⟩
  exact ((hq a ha).2.2.2 z₀ hz₀ hr₀).symm

/-- info: 'FMSA.Convergence.ComplexTaylorPaths.inBox_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorPaths.inBox_mono
/-- info: 'FMSA.Convergence.ComplexTaylorPaths.slab_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorPaths.slab_lift
/-- info: 'FMSA.Convergence.ComplexTaylorPaths.extend_slab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorPaths.extend_slab
/-- info: 'FMSA.Convergence.ComplexTaylorPaths.extend_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorPaths.extend_chain
/-- info: 'FMSA.Convergence.ComplexTaylorPaths.start_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorPaths.start_chain
end FMSA.Convergence.ComplexTaylorPaths
