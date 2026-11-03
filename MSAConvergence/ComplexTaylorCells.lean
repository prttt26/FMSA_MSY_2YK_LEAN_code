import MSAConvergence.ComplexTaylorSpecs
import MSAConvergence.ComplexRectangleNewton
import MSAConvergence.ScaledRectangleCertificates

/-! One executable check per cell gives a continuous, unique, regular complex root lift.

A cell holds four pieces of data:
* expansion centres `Y`;
* a preconditioner `C`;
* a root box `X`;
* a coupling rectangle `T`.

`cellOK` checks two things over the whole box, by Taylor-model range bounds:
* the Newton map `z ↦ z - C F(τ, z)` maps `X` into itself;
* the weighted real rows of `1 - C J(τ, z)` are at most `3/4`.

`cell_lift` turns `cellOK = true` into the hypotheses of
`ComplexRectangleNewton.exists_continuous_regular_polynomial_lift_on_rectangle`, for every
continuous coupling path inside `T`. -/
noncomputable section
namespace FMSA.Convergence.ComplexTaylorCells
open ScaledIntegerIntervals ComplexTaylorModels ComplexTaylorSpecs ComplexPolynomialSystem
open ComplexRectangularCoordinates ScaledRectangleCertificates
open scoped BigOperators

structure Cell where
  Y : List CBox
  C : List (List CBox)
  X : List CBox
  T : CBox

def getB (l : List CBox) (i : ℕ) : CBox := l.getD i CBox.zero

namespace Cell
variable (d : Cell) (n : ℕ)
def cB (i k : ℕ) : CBox := getB (d.C.getD i []) k
/-- Expansion centres, zero past `n`. -/
def Yb (k : ℕ) : CBox := if k < n then getB d.Y k else CBox.zero
/-- Offset boxes `X - Y`, zero past `n`. -/
def hb (k : ℕ) : CBox := if k < n then (getB d.X k).add (getB d.Y k).neg else CBox.zero
end Cell

def newtonTM (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) (d : Cell) (i : ℕ) : TM :=
  (List.range n).foldl (fun acc k => add acc (neg (scale s (d.cB i k) (residTM s d.T (d.Yb n) (lI k)))))
    (shiftVar s (d.Yb n i) i)

def jacTM (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) (d : Cell) (i j : ℕ) : TM :=
  (List.range n).foldl
    (fun acc k => add acc (neg (scale s (d.cB i k) (residTM s d.T (d.Yb n) (derivI j (lI k))))))
    (if i = j then const (CBox.one s) else [])

def ordered (A : Interval) : Bool := decide (A.lo ≤ A.hi)
def proper (A : Interval) : Bool := decide (A.lo < A.hi)
def inside (A B : Interval) : Bool := decide (B.lo ≤ A.lo) && decide (A.hi ≤ B.hi)
def comp (b : Bool) (A : CBox) : Interval := if b then A.im else A.re
def width (d : Cell) (b : Bool) (j : ℕ) : ℤ := (comp b (getB d.X j)).hi - (comp b (getB d.X j)).lo
def entryU (E : CBox) (b b' : Bool) : ℤ := (if b = b' then E.re else E.im).absUpper

def rowSum (d : Cell) (n : ℕ) (Es : List CBox) (b : Bool) : ℤ :=
  ([false, true].map fun b' => ((List.range n).map fun j => entryU (getB Es j) b b' * width d b' j).sum).sum

def rowOK (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) (d : Cell) (i : ℕ) : Bool :=
  let Es := (List.range n).map fun j => range s (d.hb n) (jacTM s n lI d i j)
  [false, true].all fun b => decide (4 * rowSum d n Es b ≤ 3 * width d b i * s)

def mapOK (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) (d : Cell) (i : ℕ) : Bool :=
  let r := range s (d.hb n) (newtonTM s n lI d i)
  inside r.re (getB d.X i).re && inside r.im (getB d.X i).im

def boxesOK (n : ℕ) (d : Cell) (i : ℕ) : Bool :=
  proper (getB d.X i).re && proper (getB d.X i).im && ordered (getB d.Y i).re &&
    ordered (getB d.Y i).im && (List.range n).all fun k => ordered (d.cB i k).re && ordered (d.cB i k).im

def cellOK (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) (d : Cell) : Bool :=
  (List.range n).all fun i => boxesOK n d i && mapOK s n lI d i && rowOK s n lI d i

/-! ### Soundness -/

variable {s : ℤ}

/-- The lower corner of an ordered box, as an exact complex number. -/
def yv (s : ℤ) (B : CBox) : ℂ := ⟨(B.re.lo : ℝ) / (s : ℝ), (B.im.lo : ℝ) / (s : ℝ)⟩

theorem yv_sound (hs : 0 < s) {B : CBox} (h1 : B.re.lo ≤ B.re.hi) (h2 : B.im.lo ≤ B.im.hi) :
    CEnc s B (yv s B) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  refine ⟨⟨le_rfl, ?_⟩, ⟨le_rfl, ?_⟩⟩ <;>
    exact div_le_div_of_nonneg_right (by exact_mod_cast ‹_›) hsR.le

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]
    simp

theorem fin_sum_eq_list {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (g : ℕ → M)
    (hfg : ∀ k : Fin n, f k = g k) :
    ∑ k, f k = ((List.range n).map g).sum := by
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun k _ => hfg k

theorem rep_foldl_list {u : ℕ → TM} {f : ℕ → (ℕ → ℂ) → ℂ} :
    ∀ (l : List ℕ), (∀ k ∈ l, Rep s (u k) (f k)) → ∀ (acc : TM) {g : (ℕ → ℂ) → ℂ}, Rep s acc g →
      Rep s (l.foldl (fun a k => add a (u k)) acc) (fun h => g h + (l.map fun k => f k h).sum)
  | [], _, acc, g, hacc => rep_congr _ (fun h => by simp) hacc
  | k :: l, hu, acc, g, hacc => by
    refine rep_congr _ (fun h => ?_) (rep_foldl_list l (fun m hm => hu m (List.mem_cons_of_mem k hm)) _
      (rep_add hacc (hu k List.mem_cons_self)))
    simp only [List.map_cons, List.sum_cons]
    ring

theorem list_sum_map_neg {M : Type*} [AddCommGroup M] (g : ℕ → M) :
    ∀ l : List ℕ, (l.map fun k => -g k).sum = -(l.map g).sum
  | [] => by simp
  | k :: l => by simp [list_sum_map_neg g l, add_comm]

section Lift
variable {n : ℕ} (F : Fin n → MvPolynomial (Option (Fin n)) ℝ) (lI : ℕ → SpecI) (lR : ℕ → SpecR)

/-- Real/imaginary component intervals of the root box, as required by the rectangle theorem. -/
def boxB (d : Cell) (j : Bool × Fin n) : Interval := comp j.1 (getB d.X j.2)

theorem mem_box_iff (hs : 0 < s) (d : Cell) (hB : ∀ j : Bool × Fin n, (boxB d j).lo < (boxB d j).hi)
    (z : Fin n → ℂ) :
    normalizedCoordinates (fun j => radius s (boxB d j)) (fun j => (radius_pos s hs _ (hB j)).ne')
      (z - fun i => (⟨center s (boxB d (false, i)), center s (boxB d (true, i))⟩ : ℂ)) ∈
        Metric.closedBall 0 1 ↔ ∀ i : Fin n, CEnc s (getB d.X i) (z i) := by
  rw [complex_rectangle_iff_enclosed s hs (boxB d) hB z]
  constructor
  · intro h i
    exact ⟨by simpa [boxB, comp, coordinates_apply] using h (false, i),
      by simpa [boxB, comp, coordinates_apply] using h (true, i)⟩
  · rintro h ⟨b, i⟩
    cases b
    · simpa [boxB, comp, coordinates_apply] using (h i).1
    · simpa [boxB, comp, coordinates_apply] using (h i).2

variable {F lI lR}

/-- Unpacking the executable check for one row. -/
theorem cellOK_row {d : Cell} (hok : cellOK s n lI d = true) (i : Fin n) :
    boxesOK n d i = true ∧ mapOK s n lI d i = true ∧ rowOK s n lI d i = true := by
  have h := List.all_eq_true.mp hok i (List.mem_range.mpr i.isLt)
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem boxes_of_cellOK {d : Cell} (hok : cellOK s n lI d = true) (i : Fin n) :
    (getB d.X i).re.lo < (getB d.X i).re.hi ∧ (getB d.X i).im.lo < (getB d.X i).im.hi ∧
      (getB d.Y i).re.lo ≤ (getB d.Y i).re.hi ∧ (getB d.Y i).im.lo ≤ (getB d.Y i).im.hi ∧
      ∀ k : Fin n, (d.cB i k).re.lo ≤ (d.cB i k).re.hi ∧ (d.cB i k).im.lo ≤ (d.cB i k).im.hi := by
  have h := (cellOK_row hok i).1
  simp only [boxesOK, proper, ordered, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, fun k => h.2 k k.isLt⟩

/-- Exact centres, zero past `n`. -/
def yN (d : Cell) (n : ℕ) (k : ℕ) : ℂ := if k < n then yv s (getB d.Y k) else 0

theorem yN_sound (hs : 0 < s) {d : Cell} (hok : cellOK s n lI d = true) (k : ℕ) :
    CEnc s (d.Yb n k) (yN (s := s) d n k) := by
  unfold Cell.Yb yN
  split_ifs with hk
  · obtain ⟨-, -, h1, h2, -⟩ := boxes_of_cellOK hok ⟨k, hk⟩
    exact yv_sound hs h1 h2
  · exact czero_sound

/-- The exact preconditioner. -/
def Cmat (s : ℤ) (d : Cell) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i k => yv s (d.cB i k)

theorem offset_sound (hs : 0 < s) {d : Cell} (hok : cellOK s n lI d = true) {z : Fin n → ℂ}
    (hz : ∀ i : Fin n, CEnc s (getB d.X i) (z i)) (k : ℕ) :
    CEnc s (d.hb n k) (ext z k - yN (s := s) d n k) := by
  have hy := yN_sound (lI := lI) hs hok k
  unfold Cell.hb
  unfold Cell.Yb at hy
  split_ifs with hk
  · simp only [hk, if_true] at hy
    have := cadd_sound (hz ⟨k, hk⟩) (cneg_sound hy)
    simpa [ext, hk, sub_eq_add_neg] using this
  · simp only [hk, if_false] at hy
    simpa [ext, hk, yN] using czero_sound (s := s)

theorem cB_sound (hs : 0 < s) {d : Cell} (hok : cellOK s n lI d = true) (i : Fin n) {k : ℕ}
    (hk : k < n) : CEnc s (d.cB i k) (yv s (d.cB i k)) := by
  obtain ⟨h1, h2⟩ := (boxes_of_cellOK hok i).2.2.2.2 ⟨k, hk⟩
  exact yv_sound hs h1 h2

theorem newton_sound (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) {d : Cell} (hok : cellOK s n lI d = true)
    {τ : ℂ} (hT : CEnc s d.T τ) {z : Fin n → ℂ} (hz : ∀ i : Fin n, CEnc s (getB d.X i) (z i))
    (i : Fin n) : CEnc s (getB d.X i) ((z - (Cmat s d n).mulVec (complexResidual F (τ, z))) i) := by
  have hy := yN_sound (lI := lI) hs hok
  have hrep := rep_foldl_list (s := s) (List.range n)
    (u := fun k => neg (scale s (d.cB i k) (residTM s d.T (d.Yb n) (lI k))))
    (f := fun k h => -(yv s (d.cB i k) * specVal (lR k) τ (fun m => yN (s := s) d n m + h m)))
    (fun k hk => rep_neg _ (rep_scale hs (cB_sound hs hok i (List.mem_range.mp hk)) _
      (rep_residTM hs hy hT (hrel k))))
    _ (rep_shiftVar hs (hy i) i)
  have hr := range_sound hs (offset_sound (lI := lI) hs hok hz) hrep
  have hval : (z - (Cmat s d n).mulVec (complexResidual F (τ, z))) i =
      yN (s := s) d n i + (ext z i - yN (s := s) d n i) +
        ((List.range n).map fun k => -(yv s (d.cB i k) *
          specVal (lR k) τ (fun m => yN (s := s) d n m + (ext z m - yN (s := s) d n m)))).sum := by
    simp only [add_sub_cancel, Pi.sub_apply, Matrix.mulVec, dotProduct, Cmat, list_sum_map_neg]
    rw [fin_sum_eq_list (fun k => yv s (d.cB i k) * complexResidual F (τ, z) k)
      (fun k => yv s (d.cB i k) * specVal (lR k) τ (ext z))
      (fun k => by rw [complexResidual_spec F lR hF]), ext, dif_pos i.isLt, sub_eq_add_neg]
  rw [← hval] at hr
  have hm := (cellOK_row hok i).2.1
  simp only [mapOK, inside, Bool.and_eq_true, decide_eq_true_eq] at hm
  exact ⟨encloses_mono s hs hm.1.1 hm.1.2 hr.1, encloses_mono s hs hm.2.1 hm.2.2 hr.2⟩

theorem jac_sound (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) {d : Cell} (hok : cellOK s n lI d = true)
    {τ : ℂ} (hT : CEnc s d.T τ) {z : Fin n → ℂ} (hz : ∀ i : Fin n, CEnc s (getB d.X i) (z i))
    (i j : Fin n) : CEnc s (range s (d.hb n) (jacTM s n lI d i j))
      ((if i = j then 1 else 0) - ∑ k, Cmat s d n i k * complexJacobian F (τ, z) k j) := by
  have hy := yN_sound (lI := lI) hs hok
  have hbase : Rep s (if (i : ℕ) = (j : ℕ) then const (CBox.one s) else [])
      (fun _ => if i = j then (1 : ℂ) else 0) := by
    by_cases hij : i = j
    · simp only [hij, if_true]; exact rep_const (cone_sound hs)
    · have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      simp only [this, hij, if_false]; exact fun _ => rfl
  have hrep := rep_foldl_list (s := s) (List.range n)
    (u := fun k => neg (scale s (d.cB i k) (residTM s d.T (d.Yb n) (derivI j (lI k)))))
    (f := fun k h => -(yv s (d.cB i k) * specVal (derivR j (lR k)) τ (fun m => yN (s := s) d n m + h m)))
    (fun k hk => rep_neg _ (rep_scale hs (cB_sound hs hok i (List.mem_range.mp hk)) _
      (rep_residTM hs hy hT (derivRel j (hrel k)))))
    _ hbase
  have hr := range_sound hs (offset_sound (lI := lI) hs hok hz) hrep
  have hval : (if i = j then (1 : ℂ) else 0) - ∑ k, Cmat s d n i k * complexJacobian F (τ, z) k j =
      (if i = j then (1 : ℂ) else 0) +
        ((List.range n).map fun k => -(yv s (d.cB i k) *
          specVal (derivR j (lR k)) τ (fun m => yN (s := s) d n m + (ext z m - yN (s := s) d n m)))).sum := by
    simp only [add_sub_cancel, Cmat, list_sum_map_neg]
    rw [fin_sum_eq_list (fun k => yv s (d.cB i k) * complexJacobian F (τ, z) k j)
      (fun k => yv s (d.cB i k) * specVal (derivR j (lR k)) τ (ext z))
      (fun k => by rw [complexJacobian_spec F lR hF]), sub_eq_add_neg]
  rw [hval]
  exact hr

/-- The Jacobian rows of row `i`, one range box per column. -/
def jacRow (s : ℤ) (n : ℕ) (lI : ℕ → SpecI) (d : Cell) (i : ℕ) : List CBox :=
  (List.range n).map fun j => range s (d.hb n) (jacTM s n lI d i j)

theorem getB_jacRow {d : Cell} {i j : ℕ} (hj : j < n) :
    getB (jacRow s n lI d i) j = range s (d.hb n) (jacTM s n lI d i j) := by
  simp [getB, jacRow, List.getD_eq_getElem?_getD, hj]

theorem row_sound (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) {d : Cell} (hok : cellOK s n lI d = true)
    {τ : ℂ} (hT : CEnc s d.T τ) {z : Fin n → ℂ} (hz : ∀ i : Fin n, CEnc s (getB d.X i) (z i))
    (p : Bool × Fin n) :
    ∑ q, |normalizedRealMatrix (fun q => radius s (boxB d q))
      (1 - Cmat s d n * complexJacobian F (τ, z)) p q| ≤ ((3 : ℤ) : ℝ) / ((4 : ℤ) : ℝ) := by
  let w : Bool × Fin n → ℤ := fun q => width d q.1 q.2
  have hw : ∀ q, 0 < w q := by
    rintro ⟨b, j⟩
    obtain ⟨h1, h2, -⟩ := boxes_of_cellOK hok j
    cases b <;> simp [w, width, comp] <;> omega
  let u : (Bool × Fin n) → (Bool × Fin n) → ℤ :=
    fun p q => entryU (getB (jacRow s n lI d p.2) q.2) p.1 q.1
  have ha : ∀ p q, |realMatrix (1 - Cmat s d n * complexJacobian F (τ, z)) p q| ≤ (u p q : ℝ) / (s : ℝ) := by
    rintro ⟨b, i⟩ ⟨b', j⟩
    have hE0 := jac_sound hs hrel hF hok hT hz i j
    have hE : CEnc s (range s (d.hb n) (jacTM s n lI d i j))
        ((1 - Cmat s d n * complexJacobian F (τ, z)) i j) := by
      convert hE0 using 1
      simp [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply]
    simp only [u, getB_jacRow (lI := lI) (d := d) j.isLt, entryU]
    cases b <;> cases b' <;> simp only [realMatrix, if_true, if_false, Bool.false_eq_true, ↓reduceIte]
    · exact abs_sound s hs hE.1
    · rw [abs_neg]; exact abs_sound s hs hE.2
    · exact abs_sound s hs hE.2
    · exact abs_sound s hs hE.1
  have hcheck : ∀ p, (4 : ℤ) * ∑ q, u p q * w q ≤ 3 * w p * s := by
    rintro ⟨b, i⟩
    have hr := (cellOK_row hok i).2.2
    simp only [rowOK, List.all_eq_true, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false, decide_eq_true_eq, forall_eq_or_imp, forall_eq] at hr
    have hsum : ∑ q, u (b, i) q * w q = rowSum d n (jacRow s n lI d i) b := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool, rowSum]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [add_comm]
      congr 1 <;> exact fin_sum_eq_list _ _ (fun k => rfl)
    rw [hsum]
    cases b
    · exact hr.1
    · exact hr.2
  have hwt : (fun q => radius s (boxB d q)) = fun q => (w q : ℝ) / (2 * (s : ℝ)) := by
    funext q
    simp only [radius, boxB, w, width]
    push_cast
    ring
  rw [hwt]
  exact complex_normalized_row_bound s 4 3 hs (by norm_num) w hw u _ ha hcheck p

/-- **Cell lift.** A passing cell check gives a continuous, unique, regular root lift in the box
for every continuous coupling path inside the coupling rectangle. -/
theorem cell_lift (hs : 0 < s) (hrel : ∀ k, SpecRel s (lI k) (lR k))
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) {d : Cell} (hok : cellOK s n lI d = true)
    {S : Type*} [TopologicalSpace S] (gamma : S → ℂ) (hg : Continuous gamma)
    (hT : ∀ t, CEnc s d.T (gamma t)) :
    ∃ p : S → (Fin n → ℂ), Continuous p ∧ ∀ t,
      (∀ i : Fin n, CEnc s (getB d.X i) (p t i)) ∧ complexResidual F (gamma t, p t) = 0 ∧
      (complexJacobian F (gamma t, p t)).det ≠ 0 ∧
      ∀ z : Fin n → ℂ, (∀ i : Fin n, CEnc s (getB d.X i) (z i)) →
        complexResidual F (gamma t, z) = 0 → z = p t := by
  have hB : ∀ j : Bool × Fin n, (boxB d j).lo < (boxB d j).hi := by
    rintro ⟨b, i⟩
    obtain ⟨h1, h2, -⟩ := boxes_of_cellOK hok i
    cases b
    · exact h1
    · exact h2
  have hq : (3 / 4 : NNReal) < 1 := by
    rw [← NNReal.coe_lt_coe]; norm_num
  have hrow : ∀ t (z : Fin n → ℂ),
      normalizedCoordinates (fun j => radius s (boxB d j)) (fun j => (radius_pos s hs _ (hB j)).ne')
        (z - fun i => (⟨center s (boxB d (false, i)), center s (boxB d (true, i))⟩ : ℂ)) ∈
          Metric.closedBall 0 1 →
      ∀ p, ∑ q, |normalizedRealMatrix (fun j => radius s (boxB d j))
        (1 - Cmat s d n * complexJacobian F (gamma t, z)) p q| ≤ ((3 / 4 : NNReal) : ℝ) := by
    intro t z hz p
    have h := row_sound hs hrel hF hok (hT t) ((mem_box_iff hs d hB z).mp hz) p
    have h34 : ((3 : ℤ) : ℝ) / ((4 : ℤ) : ℝ) = ((3 / 4 : NNReal) : ℝ) := by norm_num
    rw [← h34]
    convert h
  have hmap : ∀ t (z : Fin n → ℂ),
      normalizedCoordinates (fun j => radius s (boxB d j)) (fun j => (radius_pos s hs _ (hB j)).ne')
        (z - fun i => (⟨center s (boxB d (false, i)), center s (boxB d (true, i))⟩ : ℂ)) ∈
          Metric.closedBall 0 1 →
      normalizedCoordinates (fun j => radius s (boxB d j)) (fun j => (radius_pos s hs _ (hB j)).ne')
        (z - (Cmat s d n).mulVec (complexResidual F (gamma t, z)) -
          fun i => (⟨center s (boxB d (false, i)), center s (boxB d (true, i))⟩ : ℂ)) ∈
          Metric.closedBall 0 1 := by
    intro t z hz
    exact (mem_box_iff hs d hB _).mpr fun i =>
      newton_sound hs hrel hF hok (hT t) ((mem_box_iff hs d hB z).mp hz) i
  obtain ⟨p, hpc, hp⟩ := ComplexRectangleNewton.exists_continuous_regular_polynomial_lift_on_rectangle
    F gamma hg (fun i => ⟨center s (boxB d (false, i)), center s (boxB d (true, i))⟩)
    (fun j => radius s (boxB d j)) (fun j => radius_pos s hs _ (hB j)) (Cmat s d n) (3 / 4) hq
    (fun t z hz p => by convert hrow t z hz p) hmap
  refine ⟨p, hpc, fun t => ?_⟩
  obtain ⟨hbox, hroot, hdet, huniq⟩ := hp t
  exact ⟨(mem_box_iff hs d hB (p t)).mp hbox, hroot, by convert hdet,
    fun z hz hzr => huniq z ((mem_box_iff hs d hB z).mpr hz) hzr⟩

end Lift

/-- info: 'FMSA.Convergence.ComplexTaylorCells.yv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.yv_sound
/-- info: 'FMSA.Convergence.ComplexTaylorCells.list_sum_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.list_sum_range
/-- info: 'FMSA.Convergence.ComplexTaylorCells.fin_sum_eq_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.fin_sum_eq_list
/-- info: 'FMSA.Convergence.ComplexTaylorCells.rep_foldl_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.rep_foldl_list
/-- info: 'FMSA.Convergence.ComplexTaylorCells.list_sum_map_neg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.list_sum_map_neg
/-- info: 'FMSA.Convergence.ComplexTaylorCells.mem_box_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.mem_box_iff
/-- info: 'FMSA.Convergence.ComplexTaylorCells.cellOK_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.cellOK_row
/-- info: 'FMSA.Convergence.ComplexTaylorCells.boxes_of_cellOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.boxes_of_cellOK
/-- info: 'FMSA.Convergence.ComplexTaylorCells.yN_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.yN_sound
/-- info: 'FMSA.Convergence.ComplexTaylorCells.offset_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.offset_sound
/-- info: 'FMSA.Convergence.ComplexTaylorCells.cB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.cB_sound
/-- info: 'FMSA.Convergence.ComplexTaylorCells.newton_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.newton_sound
/-- info: 'FMSA.Convergence.ComplexTaylorCells.jac_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.jac_sound
/-- info: 'FMSA.Convergence.ComplexTaylorCells.getB_jacRow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.getB_jacRow
/-- info: 'FMSA.Convergence.ComplexTaylorCells.row_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.row_sound
/-- info: 'FMSA.Convergence.ComplexTaylorCells.cell_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorCells.cell_lift
end FMSA.Convergence.ComplexTaylorCells
