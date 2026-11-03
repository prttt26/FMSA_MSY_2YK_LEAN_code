import MSAConvergence.ComplexTaylorModels
import MSAConvergence.ComplexPolynomialSystem

/-! Coupling-affine polynomial specs: a list of (amplitude exponents, coupling power, coefficient)
terms. One spec gives three things:
* an `MvPolynomial` over `Option (Fin n)` (`none` is the coupling);
* its complex value;
* a Taylor model in the offsets around an enclosed centre.

Amplitude partial derivatives act on specs termwise and agree with `MvPolynomial.pderiv`. -/
noncomputable section
namespace FMSA.Convergence.ComplexTaylorSpecs
open ScaledIntegerIntervals ComplexTaylorModels ComplexPolynomialSystem

abbrev SpecR := List (List ℕ × ℕ × ℝ)
abbrev SpecI := List (List ℕ × ℕ × Interval)

def specVal (l : SpecR) (τ : ℂ) (x : ℕ → ℂ) : ℂ :=
  (l.map fun t => (t.2.2 : ℂ) * τ ^ t.2.1 * monoVal t.1 x).sum

/-- Interval and real specs with the same exponents and enclosed coefficients. -/
def SpecRel (s : ℤ) (lI : SpecI) (lR : SpecR) : Prop :=
  List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ Encloses s a.2.2 b.2.2) lI lR

def residTM (s : ℤ) (T : CBox) (Y : ℕ → CBox) (l : SpecI) : TM :=
  l.foldl (fun acc t => add acc (scale s ((CBox.ofReal t.2.2).mul s (T.cpow s t.2.1)) (monoTM s Y 0 t.1))) []

variable {s : ℤ}

theorem rep_residTM_foldl (hs : 0 < s) {Y : ℕ → CBox} {y : ℕ → ℂ} (hy : ∀ k, CEnc s (Y k) (y k))
    {T : CBox} {τ : ℂ} (hT : CEnc s T τ) {lI : SpecI} {lR : SpecR} (hrel : SpecRel s lI lR) :
    ∀ (acc : TM) {g : (ℕ → ℂ) → ℂ}, Rep s acc g →
      Rep s (lI.foldl (fun acc t => add acc (scale s ((CBox.ofReal t.2.2).mul s (T.cpow s t.2.1))
        (monoTM s Y 0 t.1))) acc) (fun h => g h + specVal lR τ (fun k => y k + h k)) := by
  induction hrel with
  | nil => intro acc g hacc; exact rep_congr _ (fun h => by simp [specVal]) hacc
  | @cons a b lI lR hab _ ih =>
    intro acc g hacc
    obtain ⟨he, hb, hc⟩ := hab
    have hterm := rep_scale hs (cmul_sound hs (cofReal_sound hc) (cpow_sound hs hT a.2.1)) _
      (rep_monoTM hs hy a.1 0)
    refine rep_congr _ (fun h => ?_) (ih _ (rep_add hacc hterm))
    simp only [specVal, List.map_cons, List.sum_cons, Nat.add_zero, he, hb]
    ring

theorem rep_residTM (hs : 0 < s) {Y : ℕ → CBox} {y : ℕ → ℂ} (hy : ∀ k, CEnc s (Y k) (y k))
    {T : CBox} {τ : ℂ} (hT : CEnc s T τ) {lI : SpecI} {lR : SpecR} (hrel : SpecRel s lI lR) :
    Rep s (residTM s T Y lI) (fun h => specVal lR τ (fun k => y k + h k)) :=
  rep_congr _ (fun h => by simp) (rep_residTM_foldl hs hy hT hrel [] (g := fun _ => 0) (fun _ => rfl))

/-! ### Partial derivatives of specs -/

def decr : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, a :: e => (a - 1) :: e
  | j + 1, a :: e => a :: decr j e

def derivR (j : ℕ) (l : SpecR) : SpecR :=
  l.filterMap fun t => if t.1.getD j 0 = 0 then none else some (decr j t.1, t.2.1, (t.1.getD j 0 : ℝ) * t.2.2)

def natScale (k : ℕ) (A : Interval) : Interval := ⟨k * A.lo, k * A.hi⟩

def derivI (j : ℕ) (l : SpecI) : SpecI :=
  l.filterMap fun t => if t.1.getD j 0 = 0 then none else some (decr j t.1, t.2.1, natScale (t.1.getD j 0) t.2.2)

theorem natScale_sound (k : ℕ) {A : Interval} {x : ℝ} (hx : Encloses s A x) :
    Encloses s (natScale k A) ((k : ℝ) * x) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · have := mul_le_mul_of_nonneg_left hx.1 hk
    simpa [natScale, mul_div_assoc] using this
  · have := mul_le_mul_of_nonneg_left hx.2 hk
    simpa [natScale, mul_div_assoc] using this

theorem derivRel (j : ℕ) {lI : SpecI} {lR : SpecR} (hrel : SpecRel s lI lR) :
    SpecRel s (derivI j lI) (derivR j lR) := by
  induction hrel with
  | nil => exact List.Forall₂.nil
  | @cons a b lI lR hab _ ih =>
    obtain ⟨he, hb, hc⟩ := hab
    simp only [derivI, derivR, List.filterMap_cons] at ih ⊢
    rw [he]
    split_ifs with h0
    · exact ih
    · exact List.Forall₂.cons ⟨rfl, hb, natScale_sound _ hc⟩ ih

/-! ### The polynomial of a spec -/

variable {n : ℕ}

def varP (o : ℕ) : MvPolynomial (Option (Fin n)) ℝ :=
  if h : o < n then MvPolynomial.X (some ⟨o, h⟩) else 0

def monoPoly : ℕ → List ℕ → MvPolynomial (Option (Fin n)) ℝ
  | _, [] => 1
  | o, a :: e => varP o ^ a * monoPoly (o + 1) e

def specPoly (l : SpecR) : MvPolynomial (Option (Fin n)) ℝ :=
  (l.map fun t => MvPolynomial.C t.2.2 * MvPolynomial.X none ^ t.2.1 * monoPoly 0 t.1).sum

/-- Amplitudes as a list-indexed sequence, zero past `n`. -/
def ext (z : Fin n → ℂ) (k : ℕ) : ℂ := if h : k < n then z ⟨k, h⟩ else 0

theorem eval_monoPoly (τ : ℂ) (z : Fin n → ℂ) : ∀ (e : List ℕ) (o : ℕ),
    MvPolynomial.eval₂Hom Complex.ofRealHom (point (τ, z)) (monoPoly o e) =
      monoVal e (fun k => ext z (k + o))
  | [], o => by simp [monoPoly, monoVal]
  | a :: e, o => by
    simp only [monoPoly, monoVal, map_mul, map_pow, eval_monoPoly τ z e (o + 1), zero_add]
    congr 1
    · congr 1
      unfold varP ext
      split_ifs with h <;> simp [point]
    · congr 1
      funext k
      rw [Nat.add_right_comm, Nat.add_assoc]

theorem eval_specPoly (τ : ℂ) (z : Fin n → ℂ) (l : SpecR) :
    MvPolynomial.eval₂Hom Complex.ofRealHom (point (τ, z)) (specPoly l) = specVal l τ (ext z) := by
  induction l with
  | nil => simp [specPoly, specVal]
  | cons t l ih =>
    simp only [specPoly, specVal, List.map_cons, List.sum_cons, map_add] at ih ⊢
    rw [ih, map_mul, map_mul, map_pow, eval_monoPoly τ z t.1 0]
    simp [point]

theorem pderiv_varP (j : Fin n) (o : ℕ) :
    MvPolynomial.pderiv (some j) (varP (n := n) o) = if (j : ℕ) = o then 1 else 0 := by
  unfold varP
  split_ifs with h hj hj
  · subst hj; simp [MvPolynomial.pderiv_X]
  · rw [MvPolynomial.pderiv_X]
    have : (some j : Option (Fin n)) ≠ some ⟨o, h⟩ := by
      intro he; apply hj; simp only [Option.some.injEq] at he; rw [he]
    simp [Pi.single_apply, this.symm]
  · exact absurd (hj ▸ j.isLt) h
  · simp

theorem pderiv_monoPoly (j : Fin n) : ∀ (e : List ℕ) (o : ℕ),
    MvPolynomial.pderiv (some j) (monoPoly (n := n) o e) =
      if o ≤ (j : ℕ) then MvPolynomial.C ((e.getD ((j : ℕ) - o) 0 : ℕ) : ℝ) * monoPoly o (decr ((j : ℕ) - o) e)
      else 0
  | [], o => by split_ifs <;> simp [monoPoly, decr]
  | a :: e, o => by
    have ih := pderiv_monoPoly j e (o + 1)
    simp only [monoPoly, Derivation.leibniz, Derivation.leibniz_pow, pderiv_varP, ih, smul_eq_mul]
    by_cases hjo : (j : ℕ) = o
    · subst hjo
      simp only [le_refl, if_true, Nat.sub_self, List.getD_cons_zero, decr, monoPoly,
        show ¬ ((j : ℕ) + 1 ≤ j) from by omega, if_false]
      simp [nsmul_eq_mul, mul_comm, mul_left_comm]
    · by_cases hlt : o ≤ (j : ℕ)
      · have hk : (j : ℕ) - o = ((j : ℕ) - (o + 1)) + 1 := by omega
        simp only [hjo, if_false, hlt, if_true, show o + 1 ≤ (j : ℕ) from by omega, hk,
          List.getD_cons_succ, decr, monoPoly]
        simp only [smul_zero, mul_zero, zero_add, smul_eq_mul]
        ring
      · simp only [hjo, if_false, hlt, show ¬ (o + 1 ≤ (j : ℕ)) from by omega]
        simp

theorem pderiv_specPoly (j : Fin n) (l : SpecR) :
    MvPolynomial.pderiv (some j) (specPoly (n := n) l) = specPoly (derivR j l) := by
  induction l with
  | nil => simp [specPoly, derivR]
  | cons t l ih =>
    have hx : MvPolynomial.pderiv (some j) (MvPolynomial.X (none : Option (Fin n)) : MvPolynomial _ ℝ) = 0 := by
      rw [MvPolynomial.pderiv_X]; simp
    have hterm : MvPolynomial.pderiv (some j)
        (MvPolynomial.C t.2.2 * MvPolynomial.X none ^ t.2.1 * monoPoly (n := n) 0 t.1) =
        MvPolynomial.C t.2.2 * MvPolynomial.X none ^ t.2.1 *
          (MvPolynomial.C ((t.1.getD j 0 : ℕ) : ℝ) * monoPoly 0 (decr j t.1)) := by
      rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hx, MvPolynomial.pderiv_C,
        pderiv_monoPoly j t.1 0]
      simp
    simp only [specPoly, derivR, List.map_cons, List.sum_cons, map_add, List.filterMap_cons] at ih ⊢
    rw [hterm]
    split_ifs with h0
    · rw [h0]; simpa using ih
    · simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      simp only [map_mul, Nat.cast_ofNat]
      ring

/-- A system given by specs: residual and Jacobian entries are spec values. -/
theorem complexResidual_spec (F : Fin n → MvPolynomial (Option (Fin n)) ℝ) (lR : ℕ → SpecR)
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) (τ : ℂ) (z : Fin n → ℂ) (i : Fin n) :
    complexResidual F (τ, z) i = specVal (lR i) τ (ext z) := by
  simp only [complexResidual, hF, eval_specPoly]

theorem complexJacobian_spec (F : Fin n → MvPolynomial (Option (Fin n)) ℝ) (lR : ℕ → SpecR)
    (hF : ∀ i : Fin n, F i = specPoly (lR i)) (τ : ℂ) (z : Fin n → ℂ) (i j : Fin n) :
    complexJacobian F (τ, z) i j = specVal (derivR j (lR i)) τ (ext z) := by
  simp only [complexJacobian, hF, pderiv_specPoly, eval_specPoly]

/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.rep_residTM_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.rep_residTM_foldl
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.rep_residTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.rep_residTM
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.natScale_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.natScale_sound
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.derivRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.derivRel
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.eval_monoPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.eval_monoPoly
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.eval_specPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.eval_specPoly
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.pderiv_varP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.pderiv_varP
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.pderiv_monoPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.pderiv_monoPoly
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.pderiv_specPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.pderiv_specPoly
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.complexResidual_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.complexResidual_spec
/-- info: 'FMSA.Convergence.ComplexTaylorSpecs.complexJacobian_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexTaylorSpecs.complexJacobian_spec
end FMSA.Convergence.ComplexTaylorSpecs
