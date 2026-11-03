import MSAConvergence.ScaledIntegerIntervals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Complex Taylor models on the scaled integer grid.

A Taylor model is a list of (exponent list, complex rectangle) terms. `Rep s t f` says that `f`
is a polynomial in the offsets `h` whose coefficients lie in the listed rectangles. Addition,
negation, scaling and multiplication are computable and preserve `Rep`. A range bound over a
box of offsets is sound. Every check is an executable integer computation; soundness is proved
once here for all inputs. -/
noncomputable section
namespace FMSA.Convergence.ComplexTaylorModels
open ScaledIntegerIntervals

/-- A complex rectangle: real and imaginary integer intervals at a common scale. -/
structure CBox where
  re : Interval
  im : Interval
  deriving DecidableEq

def CEnc (s : ℤ) (A : CBox) (z : ℂ) : Prop := Encloses s A.re z.re ∧ Encloses s A.im z.im

namespace CBox
def add (A B : CBox) : CBox := ⟨A.re.add B.re, A.im.add B.im⟩
def neg (A : CBox) : CBox := ⟨A.re.neg, A.im.neg⟩
def mul (s : ℤ) (A B : CBox) : CBox :=
  ⟨(A.re.mul s B.re).add (A.im.mul s B.im).neg, (A.re.mul s B.im).add (A.im.mul s B.re)⟩
def ofReal (A : Interval) : CBox := ⟨A, Interval.point 0⟩
def zero : CBox := ⟨Interval.point 0, Interval.point 0⟩
def one (s : ℤ) : CBox := ⟨Interval.point s, Interval.point 0⟩
def cpow (s : ℤ) (A : CBox) : ℕ → CBox
  | 0 => one s
  | n + 1 => (cpow s A n).mul s A
end CBox

variable {s : ℤ}

theorem cadd_sound {A B : CBox} {z w : ℂ} (hz : CEnc s A z) (hw : CEnc s B w) :
    CEnc s (A.add B) (z + w) :=
  ⟨by simpa only [CBox.add, Complex.add_re] using add_sound s hz.1 hw.1,
    by simpa only [CBox.add, Complex.add_im] using add_sound s hz.2 hw.2⟩

theorem cneg_sound {A : CBox} {z : ℂ} (hz : CEnc s A z) : CEnc s A.neg (-z) :=
  ⟨by simpa only [CBox.neg, Complex.neg_re] using neg_sound s hz.1,
    by simpa only [CBox.neg, Complex.neg_im] using neg_sound s hz.2⟩

theorem cmul_sound (hs : 0 < s) {A B : CBox} {z w : ℂ} (hz : CEnc s A z) (hw : CEnc s B w) :
    CEnc s (A.mul s B) (z * w) := by
  constructor
  · have h := add_sound s (mul_sound s hs hz.1 hw.1) (neg_sound s (mul_sound s hs hz.2 hw.2))
    simpa only [CBox.mul, Complex.mul_re, sub_eq_add_neg] using h
  · simpa only [CBox.mul, Complex.mul_im] using add_sound s (mul_sound s hs hz.1 hw.2) (mul_sound s hs hz.2 hw.1)

theorem point_zero_sound : Encloses s (Interval.point 0) 0 := by
  simp [Encloses, Interval.point]

theorem czero_sound : CEnc s CBox.zero 0 := ⟨point_zero_sound, point_zero_sound⟩

theorem cone_sound (hs : 0 < s) : CEnc s (CBox.one s) 1 := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨?_, point_zero_sound⟩
  simp [CBox.one, Encloses, Interval.point, div_self hsR]

theorem cofReal_sound {A : Interval} {x : ℝ} (hx : Encloses s A x) : CEnc s (CBox.ofReal A) (x : ℂ) :=
  ⟨by simpa [CBox.ofReal] using hx, by simpa [CBox.ofReal] using (point_zero_sound (s := s))⟩

theorem cpow_sound (hs : 0 < s) {A : CBox} {z : ℂ} (hz : CEnc s A z) :
    ∀ n, CEnc s (A.cpow s n) (z ^ n)
  | 0 => by simpa [CBox.cpow] using cone_sound hs
  | n + 1 => by simpa only [CBox.cpow, pow_succ] using cmul_sound hs (cpow_sound hs hz n) hz

/-! ### Monomials in list-indexed offsets -/

/-- `monoVal e h = ∏ᵢ h i ^ e[i]`. -/
def monoVal : List ℕ → (ℕ → ℂ) → ℂ
  | [], _ => 1
  | a :: e, h => h 0 ^ a * monoVal e (fun i => h (i + 1))

def eadd : List ℕ → List ℕ → List ℕ
  | [], f => f
  | a :: e, [] => a :: e
  | a :: e, b :: f => (a + b) :: eadd e f

theorem monoVal_eadd : ∀ (e f : List ℕ) (h : ℕ → ℂ), monoVal (eadd e f) h = monoVal e h * monoVal f h
  | [], f, h => by simp [eadd, monoVal]
  | a :: e, [], h => by simp [eadd, monoVal]
  | a :: e, b :: f, h => by
    simp only [eadd, monoVal, monoVal_eadd e f, pow_add]
    ring

/-- The exponent list of the single variable `h i`. -/
def unit : ℕ → List ℕ
  | 0 => [1]
  | i + 1 => 0 :: unit i

theorem monoVal_unit : ∀ (i : ℕ) (h : ℕ → ℂ), monoVal (unit i) h = h i
  | 0, h => by simp [unit, monoVal]
  | i + 1, h => by simp [unit, monoVal, monoVal_unit i]

/-! ### Taylor models -/

abbrev TM := List (List ℕ × CBox)

/-- `f h = ∑ₖ cₖ · monoVal eₖ h` for some `cₖ` in the listed rectangles. -/
def Rep (s : ℤ) : TM → ((ℕ → ℂ) → ℂ) → Prop
  | [], f => ∀ h, f h = 0
  | p :: t, f => ∃ c, CEnc s p.2 c ∧ Rep s t (fun h => f h - c * monoVal p.1 h)

theorem rep_congr : ∀ (t : TM) {f g : (ℕ → ℂ) → ℂ}, (∀ h, f h = g h) → Rep s t f → Rep s t g
  | [], f, g, hfg, ht => fun h => (hfg h).symm.trans (ht h)
  | p :: t, f, g, hfg, ⟨c, hc, ht⟩ =>
    ⟨c, hc, rep_congr t (fun h => by simp only [hfg h]) ht⟩

theorem rep_append : ∀ (t u : TM) {f g : (ℕ → ℂ) → ℂ}, Rep s t f → Rep s u g →
    Rep s (t ++ u) (fun h => f h + g h)
  | [], u, f, g, ht, hu => rep_congr u (fun h => by simp [ht h]) hu
  | p :: t, u, f, g, ⟨c, hc, ht⟩, hu =>
    ⟨c, hc, rep_congr _ (fun h => by ring) (rep_append t u ht hu)⟩

def ins (e : List ℕ) (A : CBox) : TM → TM
  | [] => [(e, A)]
  | p :: t => if e = p.1 then (p.1, p.2.add A) :: t else p :: ins e A t

theorem rep_ins (e : List ℕ) (A : CBox) {c : ℂ} (hc : CEnc s A c) :
    ∀ (t : TM) {f : (ℕ → ℂ) → ℂ}, Rep s t f → Rep s (ins e A t) (fun h => f h + c * monoVal e h)
  | [], f, ht => ⟨c, hc, fun h => by simp [ht h]⟩
  | p :: t, f, ⟨b, hb, ht⟩ => by
    unfold ins
    split_ifs with he
    · subst he
      exact ⟨b + c, cadd_sound hb hc, rep_congr t (fun h => by ring) ht⟩
    · exact ⟨b, hb, rep_congr _ (fun h => by ring) (rep_ins e A hc t ht)⟩

/-- Combine terms with equal exponents. -/
def norm (t : TM) : TM := t.foldl (fun acc p => ins p.1 p.2 acc) []

theorem rep_foldl : ∀ (t acc : TM) {f g : (ℕ → ℂ) → ℂ}, Rep s acc g → Rep s t f →
    Rep s (t.foldl (fun acc p => ins p.1 p.2 acc) acc) (fun h => g h + f h)
  | [], acc, f, g, hacc, ht => rep_congr acc (fun h => by simp [ht h]) hacc
  | p :: t, acc, f, g, hacc, ⟨c, hc, ht⟩ => by
    have h1 := rep_ins p.1 p.2 hc acc hacc
    exact rep_congr _ (fun h => by ring) (rep_foldl t _ h1 ht)

theorem rep_norm {t : TM} {f : (ℕ → ℂ) → ℂ} (ht : Rep s t f) : Rep s (norm t) f :=
  rep_congr _ (fun h => by ring) (rep_foldl t [] (g := fun _ => 0) (fun _ => rfl) ht)

def add (t u : TM) : TM := norm (t ++ u)

theorem rep_add {t u : TM} {f g : (ℕ → ℂ) → ℂ} (ht : Rep s t f) (hu : Rep s u g) :
    Rep s (add t u) (fun h => f h + g h) := rep_norm (rep_append t u ht hu)

def neg (t : TM) : TM := t.map fun p => (p.1, p.2.neg)

theorem rep_neg : ∀ (t : TM) {f : (ℕ → ℂ) → ℂ}, Rep s t f → Rep s (neg t) (fun h => -f h)
  | [], f, ht => fun h => by simp [ht h]
  | p :: t, f, ⟨c, hc, ht⟩ =>
    ⟨-c, cneg_sound hc, rep_congr _ (fun h => by ring) (rep_neg t ht)⟩

def scale (s : ℤ) (A : CBox) (t : TM) : TM := t.map fun p => (p.1, A.mul s p.2)

theorem rep_scale (hs : 0 < s) {A : CBox} {a : ℂ} (ha : CEnc s A a) :
    ∀ (t : TM) {f : (ℕ → ℂ) → ℂ}, Rep s t f → Rep s (scale s A t) (fun h => a * f h)
  | [], f, ht => fun h => by simp [ht h]
  | p :: t, f, ⟨c, hc, ht⟩ =>
    ⟨a * c, cmul_sound hs ha hc, rep_congr _ (fun h => by ring) (rep_scale hs ha t ht)⟩

theorem rep_mono_mul (hs : 0 < s) (e : List ℕ) {A : CBox} {a : ℂ} (ha : CEnc s A a) :
    ∀ (t : TM) {g : (ℕ → ℂ) → ℂ}, Rep s t g →
      Rep s (t.map fun q => (eadd e q.1, A.mul s q.2)) (fun h => a * monoVal e h * g h)
  | [], g, ht => fun h => by simp [ht h]
  | q :: t, g, ⟨c, hc, ht⟩ =>
    ⟨a * c, cmul_sound hs ha hc, rep_congr _ (fun h => by rw [monoVal_eadd]; ring)
      (rep_mono_mul hs e ha t ht)⟩

def mul (s : ℤ) (u t : TM) : TM :=
  norm (u.flatMap fun p => t.map fun q => (eadd p.1 q.1, p.2.mul s q.2))

theorem rep_flat (hs : 0 < s) (t : TM) {g : (ℕ → ℂ) → ℂ} (ht : Rep s t g) :
    ∀ (u : TM) {f : (ℕ → ℂ) → ℂ}, Rep s u f →
      Rep s (u.flatMap fun p => t.map fun q => (eadd p.1 q.1, p.2.mul s q.2)) (fun h => f h * g h)
  | [], f, hu => fun h => by simp [hu h]
  | p :: u, f, ⟨a, ha, hu⟩ => by
    rw [List.flatMap_cons]
    exact rep_congr _ (fun h => by ring) (rep_append _ _ (rep_mono_mul hs p.1 ha t ht) (rep_flat hs t ht u hu))

theorem rep_mul (hs : 0 < s) {u t : TM} {f g : (ℕ → ℂ) → ℂ} (hu : Rep s u f) (ht : Rep s t g) :
    Rep s (mul s u t) (fun h => f h * g h) := rep_norm (rep_flat hs t ht u hu)

def const (A : CBox) : TM := [([], A)]

theorem rep_const {A : CBox} {a : ℂ} (ha : CEnc s A a) : Rep s (const A) (fun _ => a) :=
  ⟨a, ha, fun h => by simp [monoVal]⟩

def pow (s : ℤ) (t : TM) : ℕ → TM
  | 0 => const (CBox.one s)
  | n + 1 => mul s (pow s t n) t

theorem rep_pow (hs : 0 < s) {t : TM} {f : (ℕ → ℂ) → ℂ} (ht : Rep s t f) :
    ∀ n, Rep s (pow s t n) (fun h => f h ^ n)
  | 0 => rep_congr _ (fun h => by simp) (rep_const (cone_sound hs))
  | n + 1 => rep_congr _ (fun h => by ring) (rep_mul hs (rep_pow hs ht n) ht)

/-- The offset variable `y + h i` around an enclosed center `y`. -/
def shiftVar (s : ℤ) (Y : CBox) (i : ℕ) : TM := [([], Y), (unit i, CBox.one s)]

theorem rep_shiftVar (hs : 0 < s) {Y : CBox} {y : ℂ} (hy : CEnc s Y y) (i : ℕ) :
    Rep s (shiftVar s Y i) (fun h => y + h i) :=
  ⟨y, hy, 1, cone_sound hs, fun h => by simp [monoVal, monoVal_unit]⟩

/-- `∏ₖ (y (k+o) + h (k+o)) ^ e[k]`, built from shifted variables starting at position `o`. -/
def monoTM (s : ℤ) (Y : ℕ → CBox) : ℕ → List ℕ → TM
  | _, [] => const (CBox.one s)
  | o, a :: e => mul s (pow s (shiftVar s (Y o) o) a) (monoTM s Y (o + 1) e)

theorem rep_monoTM (hs : 0 < s) {Y : ℕ → CBox} {y : ℕ → ℂ} (hy : ∀ k, CEnc s (Y k) (y k)) :
    ∀ (e : List ℕ) (o : ℕ),
      Rep s (monoTM s Y o e) (fun h => monoVal e (fun k => y (k + o) + h (k + o)))
  | [], o => rep_congr _ (fun h => by simp [monoVal]) (rep_const (cone_sound hs))
  | a :: e, o => by
    refine rep_congr _ (fun h => ?_) (rep_mul hs (rep_pow hs (rep_shiftVar hs (hy o) o) a)
      (rep_monoTM hs hy e (o + 1)))
    simp only [monoVal, zero_add]
    congr 2
    funext k
    rw [Nat.add_right_comm, Nat.add_assoc]

/-! ### Range bounds over a box of offsets -/

def monoBox (s : ℤ) : List ℕ → (ℕ → CBox) → CBox
  | [], _ => CBox.one s
  | a :: e, B => ((B 0).cpow s a).mul s (monoBox s e fun i => B (i + 1))

theorem monoBox_sound (hs : 0 < s) : ∀ (e : List ℕ) {B : ℕ → CBox} {h : ℕ → ℂ},
    (∀ i, CEnc s (B i) (h i)) → CEnc s (monoBox s e B) (monoVal e h)
  | [], B, h, _ => by simpa [monoBox, monoVal] using cone_sound hs
  | a :: e, B, h, hB => cmul_sound hs (cpow_sound hs (hB 0) a) (monoBox_sound hs e fun i => hB (i + 1))

def range (s : ℤ) (B : ℕ → CBox) (t : TM) : CBox :=
  t.foldl (fun acc p => acc.add (p.2.mul s (monoBox s p.1 B))) CBox.zero

theorem range_foldl_sound (hs : 0 < s) {B : ℕ → CBox} {h : ℕ → ℂ} (hB : ∀ i, CEnc s (B i) (h i)) :
    ∀ (t : TM) (acc : CBox) {x : ℂ} {f : (ℕ → ℂ) → ℂ}, CEnc s acc x → Rep s t f →
      CEnc s (t.foldl (fun acc p => acc.add (p.2.mul s (monoBox s p.1 B))) acc) (x + f h)
  | [], acc, x, f, hx, ht => by simpa [ht h] using hx
  | p :: t, acc, x, f, hx, ⟨c, hc, ht⟩ => by
    have h1 := cadd_sound hx (cmul_sound hs hc (monoBox_sound hs p.1 hB))
    have h2 := range_foldl_sound hs hB t _ h1 ht
    simpa [add_assoc] using h2

/-- The value of a represented polynomial at every enclosed offset lies in its range box. -/
theorem range_sound (hs : 0 < s) {B : ℕ → CBox} {h : ℕ → ℂ} (hB : ∀ i, CEnc s (B i) (h i))
    {t : TM} {f : (ℕ → ℂ) → ℂ} (ht : Rep s t f) : CEnc s (range s B t) (f h) := by
  simpa [range] using range_foldl_sound hs hB t CBox.zero czero_sound ht

/-- info: 'FMSA.Convergence.ComplexTaylorModels.cadd_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.cadd_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.cneg_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.cneg_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.cmul_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.cmul_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.point_zero_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.point_zero_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.czero_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.czero_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.cone_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.cone_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.cofReal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.cofReal_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.cpow_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.cpow_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.monoVal_eadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.monoVal_eadd
/-- info: 'FMSA.Convergence.ComplexTaylorModels.monoVal_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.monoVal_unit
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_congr
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_append
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_ins
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_foldl
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_norm
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_add
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_neg
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_scale
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_mono_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_mono_mul
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_flat
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_mul
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_const
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_pow
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_shiftVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_shiftVar
/-- info: 'FMSA.Convergence.ComplexTaylorModels.rep_monoTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.rep_monoTM
/-- info: 'FMSA.Convergence.ComplexTaylorModels.monoBox_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.monoBox_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.range_foldl_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.range_foldl_sound
/-- info: 'FMSA.Convergence.ComplexTaylorModels.range_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorModels.range_sound
end FMSA.Convergence.ComplexTaylorModels
