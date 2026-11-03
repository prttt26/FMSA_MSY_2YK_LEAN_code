import MSAConvergence.PureFluidRSquarefreePoleRecursion

set_option linter.style.header false

/-! Closure rules for finite simple-pole spans on a selected set of
positive Yukawa rates, with identities required only off the poles. -/
noncomputable section
open Filter Topology Set
namespace FMSA.Convergence.PureFluidRSquarefreePoleSpan
open FMSA.Convergence.PureFluidRSimplePoleUniqueness
open FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidRSquarefreePoleRecursion
open FMSA.Convergence.PureFluidRFormalDispersion
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRWeightOddPart
open FMSA.Convergence.PureFluidRWeightPositivity
open MvPowerSeries
variable {T : Type*} [DecidableEq T]

def PoleRep (s : Finset T) (z : T → ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ a : T → ℝ, ∀ x : ℝ, (∀ t ∈ s, x + z t ≠ 0) →
    f x = ∑ t ∈ s, a t / (x + z t)

omit [DecidableEq T] in
theorem poleRep_zero (s : Finset T) (z : T → ℝ) :
    PoleRep s z (fun _ => 0) := by
  refine ⟨fun _ => 0, ?_⟩
  intro x _
  simp

omit [DecidableEq T] in
theorem poleRep_add
    (s : Finset T) (z : T → ℝ) (f g : ℝ → ℝ)
    (hf : PoleRep s z f) (hg : PoleRep s z g) :
    PoleRep s z (fun x => f x + g x) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun t => a t + b t, ?_⟩
  intro x hx
  change f x + g x = _
  rw [ha x hx, hb x hx]
  simp only [add_div, Finset.sum_add_distrib]

omit [DecidableEq T] in
theorem poleRep_const_mul
    (s : Finset T) (z : T → ℝ) (f : ℝ → ℝ) (c : ℝ)
    (hf : PoleRep s z f) :
    PoleRep s z (fun x => c * f x) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun t => c * a t, ?_⟩
  intro x hx
  change c * f x = _
  rw [ha x hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

omit [DecidableEq T] in
theorem poleRep_subset
    (s u : Finset T) (z : T → ℝ) (f : ℝ → ℝ)
    (hsu : s ⊆ u) (hf : PoleRep s z f) :
    PoleRep u z f := by
  classical
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun t => if t ∈ s then a t else 0, ?_⟩
  intro x hx
  have hxs : ∀ t ∈ s, x + z t ≠ 0 := fun t ht => hx t (hsu ht)
  rw [ha x hxs]
  calc
    (∑ t ∈ s, a t / (x + z t)) =
        ∑ t ∈ s, (if t ∈ s then a t else 0) / (x + z t) := by
          apply Finset.sum_congr rfl
          intro t ht
          simp [ht]
    _ = ∑ t ∈ u, (if t ∈ s then a t else 0) / (x + z t) := by
          apply Finset.sum_subset hsu
          intro t _ ht
          simp [ht]

/-- Adding a fresh pole factor preserves finite simple-pole form.
The equality is asserted only off the enlarged pole set. -/
theorem poleRep_fresh_mul
    (s : Finset T) (z : T → ℝ) (f : ℝ → ℝ) (t : T)
    (ht : t ∉ s) (hfresh : ∀ u ∈ s, z t ≠ z u)
    (hf : PoleRep s z f) :
    PoleRep (insert t s) z (fun x => f x * (x + z t)⁻¹) := by
  obtain ⟨a, ha⟩ := hf
  let b : T → ℝ := fun u =>
    if u = t then ∑ v ∈ s, a v / (z v - z t)
    else a u / (z t - z u)
  refine ⟨b, ?_⟩
  intro x hx
  have htx : x + z t ≠ 0 := hx t (Finset.mem_insert_self t s)
  have hsx : ∀ u ∈ s, x + z u ≠ 0 :=
    fun u hu => hx u (Finset.mem_insert_of_mem hu)
  change f x * (x + z t)⁻¹ = _
  rw [ha x hsx, simplePoleSum_mul_fresh_pole s z a t hfresh x htx hsx]
  rw [Finset.sum_insert ht]
  have hb (u : T) (hu : u ∈ s) :
      b u = a u / (z t - z u) := by
    have hut : u ≠ t := by
      intro h
      exact ht (h ▸ hu)
    simp [b, hut]
  rw [show b t = ∑ v ∈ s, a v / (z v - z t) by simp [b]]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [hb u hu]

omit [DecidableEq T] in
theorem poleRep_single
    (z : T → ℝ) (t : T) (c : ℝ) :
    PoleRep ({t} : Finset T) z (fun x => c / (x + z t)) := by
  classical
  refine ⟨fun u => if u = t then c else 0, ?_⟩
  intro x _
  simp

omit [DecidableEq T] in
theorem poleRep_finset_sum
    {ι : Type*} (I : Finset ι) (s : Finset T) (z : T → ℝ)
    (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ I, PoleRep s z (f i)) :
    PoleRep s z (fun x => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simpa using poleRep_zero s z
  | @insert i I hi ih =>
      have hfi : PoleRep s z (f i) := hf i (Finset.mem_insert_self i I)
      have hI : ∀ j ∈ I, PoleRep s z (f j) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using
        poleRep_add s z (f i) (fun x => ∑ j ∈ I, f j x) hfi (ih hI)

/-- Cauchy multiplication by an x-independent formal series preserves
the simple-pole span when every contributing second factor lies there. -/
theorem poleRep_coeff_mul_fixed
    (s : Finset T) (z : T → ℝ)
    (H : MvPowerSeries T ℝ) (F : ℝ → MvPowerSeries T ℝ)
    (hF : ∀ pq ∈ Finset.antidiagonal
        (FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial s),
      PoleRep s z (fun x => MvPowerSeries.coeff pq.2 (F x))) :
    PoleRep s z (fun x =>
      MvPowerSeries.coeff
        (FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial s)
        (H * F x)) := by
  classical
  let m := FMSA.Convergence.PureFluidRSquarefreeGeometric.squarefreeMonomial s
  have hterm (pq : (T →₀ ℕ) × (T →₀ ℕ))
      (hpq : pq ∈ Finset.antidiagonal m) :
      PoleRep s z (fun x =>
        MvPowerSeries.coeff pq.1 H * MvPowerSeries.coeff pq.2 (F x)) := by
    exact poleRep_const_mul s z
      (fun x => MvPowerSeries.coeff pq.2 (F x))
      (MvPowerSeries.coeff pq.1 H) (hF pq hpq)
  have hsum := poleRep_finset_sum (Finset.antidiagonal m) s z
    (fun pq x =>
      MvPowerSeries.coeff pq.1 H * MvPowerSeries.coeff pq.2 (F x))
    hterm
  simpa only [m, MvPowerSeries.coeff_mul] using hsum

/-- A constant contribution and a lower-support pole expansion enter
the r recursion with the same fresh pole. -/
theorem poleRep_fresh_affine
    (s : Finset T) (z : T → ℝ) (t : T) (ht : t ∈ s)
    (hfresh : ∀ u ∈ s.erase t, z t ≠ z u)
    (c : ℝ) (f : ℝ → ℝ)
    (hf : PoleRep (s.erase t) z f) :
    PoleRep s z (fun x => (x + z t)⁻¹ * (c + f x)) := by
  have hsingle : PoleRep s z (fun x => c / (x + z t)) :=
    poleRep_subset ({t} : Finset T) s z _
      (by simpa using ht) (poleRep_single z t c)
  have hnew : PoleRep s z (fun x => f x * (x + z t)⁻¹) := by
    simpa only [Finset.insert_erase ht] using
      poleRep_fresh_mul (s.erase t) z f t
        (by simp) hfresh hf
  have hsum := poleRep_add s z
    (fun x => c / (x + z t))
    (fun x => f x * (x + z t)⁻¹) hsingle hnew
  have heq : (fun x => (x + z t)⁻¹ * (c + f x)) =
      (fun x => c / (x + z t) + f x * (x + z t)⁻¹) := by
    funext x
    rw [div_eq_mul_inv]
    ring
  rw [heq]
  exact hsum

/-- Every squarefree off-node formal r coefficient has an
x-independent finite simple-pole expansion on its selected rates.
Equality is required only away from those poles. -/
theorem physicalFormalR_squarefree_poleRep
    [Fintype T] (z : T → ℝ) (s : Finset T)
    (hinj : Set.InjOn z s) :
    PoleRep s z (fun x =>
      MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x)) := by
  classical
  have hmain : ∀ n : ℕ, ∀ s : Finset T, s.card = n →
      Set.InjOn z s →
      PoleRep s z (fun x =>
        MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hinj
      by_cases hsne : s.Nonempty
      · have hterm (t : T) (ht : t ∈ s) :
            PoleRep s z (fun x => (x + z t)⁻¹ *
              MvPowerSeries.coeff (squarefreeMonomial (s.erase t))
                (physicalH z t *
                  (C (z t) - RSeries z t + physicalFormalR z x))) := by
          let u := s.erase t
          let H := physicalH z t
          let B := C (z t) - RSeries z t
          let c := MvPowerSeries.coeff (squarefreeMonomial u) (H * B)
          let f : ℝ → ℝ := fun x =>
            MvPowerSeries.coeff (squarefreeMonomial u) (H * physicalFormalR z x)
          have hmul : PoleRep u z f := by
            apply poleRep_coeff_mul_fixed u z H (fun x => physicalFormalR z x)
            intro pq hpq
            have hsum : pq.1 + pq.2 = squarefreeMonomial u :=
              Finset.mem_antidiagonal.mp hpq
            obtain ⟨_, hqsub, _, hqeq⟩ :=
              squarefree_antidiagonal_support u pq.1 pq.2 hsum
            have hcard : pq.2.support.card < n := by
              rw [← hs]
              exact (Finset.card_le_card hqsub).trans_lt
                (Finset.card_erase_lt_of_mem ht)
            have hinjq : Set.InjOn z pq.2.support :=
              hinj.mono (hqsub.trans (Finset.erase_subset t s))
            have hrep : PoleRep pq.2.support z
                (fun x => MvPowerSeries.coeff pq.2 (physicalFormalR z x)) := by
              simpa only [← hqeq] using
                (ih pq.2.support.card hcard pq.2.support rfl hinjq)
            exact poleRep_subset pq.2.support u z _ hqsub hrep
          have hfresh : ∀ v ∈ u, z t ≠ z v := by
            intro v hv hzv
            have hvS : v ∈ s := Finset.mem_of_mem_erase hv
            have htv : t ≠ v := by
              intro heq
              subst v
              exact (by simp : t ∉ s.erase t) hv
            exact htv (hinj ht hvS hzv)
          have haff := poleRep_fresh_affine s z t ht hfresh c f hmul
          have heq : (fun x => (x + z t)⁻¹ *
              MvPowerSeries.coeff (squarefreeMonomial u)
                (H * (B + physicalFormalR z x))) =
              (fun x => (x + z t)⁻¹ * (c + f x)) := by
            funext x
            simp only [mul_add, map_add, c, f]
          change PoleRep s z (fun x => (x + z t)⁻¹ *
            MvPowerSeries.coeff (squarefreeMonomial u)
              (H * (B + physicalFormalR z x)))
          rw [heq]
          exact haff
        have hsum := poleRep_finset_sum s s z
          (fun t x => (x + z t)⁻¹ *
            MvPowerSeries.coeff (squarefreeMonomial (s.erase t))
              (physicalH z t *
                (C (z t) - RSeries z t + physicalFormalR z x))) hterm
        have heq : (fun x =>
            MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x)) =
            (fun x => ∑ t ∈ s, (x + z t)⁻¹ *
              MvPowerSeries.coeff (squarefreeMonomial (s.erase t))
                (physicalH z t *
                  (C (z t) - RSeries z t + physicalFormalR z x))) := by
          funext x
          exact physicalFormalR_coeff_squarefree_recursion z x s
        rw [heq]
        exact hsum
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
        subst s
        have heq : (fun x =>
            MvPowerSeries.coeff (squarefreeMonomial (∅ : Finset T))
              (physicalFormalR z x)) = (fun _ => 0) := by
          funext x
          exact physicalFormalR_coeff_empty z x
        rw [heq]
        exact poleRep_zero ∅ z
  exact hmain s.card s rfl hinj

omit [DecidableEq T] in
/-- Near a selected negative pole, all finitely many full-system
denominators are nonzero on a punctured neighborhood, even when
unselected rates coincide with the selected rate. -/
theorem eventually_all_two_sided_pole_domain
    [Finite T] (z : T → ℝ) (hz : ∀ u, 0 < z u) (t : T) :
    ∀ᶠ x : ℝ in 𝓝[≠] (-z t),
      (∀ u, x + z u ≠ 0) ∧ (∀ u, -x + z u ≠ 0) := by
  letI : Fintype T := Fintype.ofFinite T
  have hplus : ∀ᶠ x : ℝ in 𝓝[≠] (-z t),
      ∀ u, x + z u ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro u
    by_cases hsame : z u = z t
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hne : x ≠ -z t := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hx
      intro hzero
      apply hne
      rw [hsame] at hzero
      linarith
    · have hpoint : -z t + z u ≠ 0 := by
        intro hzero
        apply hsame
        linarith
      have hc : ContinuousAt (fun x : ℝ => x + z u) (-z t) := by fun_prop
      exact (hc.eventually_ne hpoint).filter_mono nhdsWithin_le_nhds
  have hminus : ∀ᶠ x : ℝ in 𝓝[≠] (-z t),
      ∀ u, -x + z u ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro u
    have hpoint : -(-z t) + z u ≠ 0 := by
      simpa only [neg_neg] using (add_pos (hz t) (hz u)).ne'
    have hc : ContinuousAt (fun x : ℝ => -x + z u) (-z t) := by fun_prop
    exact (hc.eventually_ne hpoint).filter_mono nhdsWithin_le_nhds
  exact hplus.and hminus

omit [DecidableEq T] in
/-- The odd part determines a selected simple-pole expansion even
when its identity is available only where all full-system
denominators are nonzero. -/
theorem simplePoleSum_odd_injective_on_full_domain
    [Finite T] (s : Finset T) (z a b : T → ℝ)
    (hz : ∀ u, 0 < z u) (hinj : Set.InjOn z s)
    (hodd : ∀ x : ℝ,
      (∀ u, x + z u ≠ 0) →
      (∀ u, -x + z u ≠ 0) →
      (∑ t ∈ s, a t / (x + z t)) -
        (∑ t ∈ s, a t / (-x + z t)) =
      (∑ t ∈ s, b t / (x + z t)) -
        (∑ t ∈ s, b t / (-x + z t))) :
    ∀ t ∈ s, a t = b t := by
  let d : T → ℝ := fun t => a t - b t
  have hd (x : ℝ) : (∑ t ∈ s, d t / (x + z t)) =
      (∑ t ∈ s, a t / (x + z t)) -
        (∑ t ∈ s, b t / (x + z t)) := by
    simp only [d, sub_div, Finset.sum_sub_distrib]
  intro t ht
  have heven : (fun x => ∑ u ∈ s, d u / (x + z u)) =ᶠ[𝓝[≠] (-z t)]
      (fun x => ∑ u ∈ s, d u / (-x + z u)) := by
    filter_upwards [eventually_all_two_sided_pole_domain z hz t] with x hx
    rw [hd x, hd (-x)]
    linarith [hodd x hx.1 hx.2]
  exact sub_eq_zero.mp
    (simplePoleSum_subset_coeff_zero_of_eventually_even
      s z d (fun u _ => hz u) hinj t ht heven)

/-- The complete squarefree coefficient of the actual off-node
formal r coordinate is the explicit factorial W weight. This
identity is stated away from the selected negative poles. -/
theorem physicalFormalR_squarefree_eq_weight_off_poles
    [Fintype T] (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (hinj : Set.InjOn z s)
    (x : ℝ) (hx : ∀ t ∈ s, x + z t ≠ 0) :
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
      (Nat.factorial s.card : ℝ) * multilinearWeight s z x := by
  obtain ⟨a, ha⟩ := physicalFormalR_squarefree_poleRep z s hinj
  let b : T → ℝ := fun t =>
    (Nat.factorial s.card : ℝ) *
      (z t * ∏ u ∈ s.erase t, (2 * z u) / (z u ^ 2 - z t ^ 2))
  have hW (y : ℝ) :
      (Nat.factorial s.card : ℝ) * multilinearWeight s z y =
      ∑ t ∈ s, b t / (y + z t) := by
    unfold multilinearWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    dsimp [b]
    ring
  have hodd (y : ℝ)
      (hplus : ∀ u, y + z u ≠ 0)
      (hminus : ∀ u, -y + z u ≠ 0) :
      (∑ t ∈ s, a t / (y + z t)) -
        (∑ t ∈ s, a t / (-y + z t)) =
      (∑ t ∈ s, b t / (y + z t)) -
        (∑ t ∈ s, b t / (-y + z t)) := by
    have hAy := ha y (fun t _ => hplus t)
    have hAm := ha (-y) (fun t _ => hminus t)
    change MvPowerSeries.coeff (squarefreeMonomial s)
      (physicalFormalR z y) = _ at hAy
    change MvPowerSeries.coeff (squarefreeMonomial s)
      (physicalFormalR z (-y)) = _ at hAm
    have hdisp := physical_formal_squarefree_odd_eq_W_odd
      s hs z hz hinj y hplus
      (fun t => by simpa only [sub_eq_add_neg, add_comm] using hminus t)
    simp only [map_sub] at hdisp
    rw [hAy, hAm] at hdisp
    rw [mul_sub, hW y, hW (-y)] at hdisp
    exact hdisp
  have hab := simplePoleSum_odd_injective_on_full_domain
    s z a b hz hinj hodd
  calc
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
        ∑ t ∈ s, a t / (x + z t) := ha x hx
    _ = ∑ t ∈ s, b t / (x + z t) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hab t ht]
    _ = (Nat.factorial s.card : ℝ) * multilinearWeight s z x :=
      (hW x).symm

/-- Uniform full formula, including the empty selected set. -/
theorem physicalFormalR_squarefree_eq_weight_all
    [Fintype T] (s : Finset T)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (hinj : Set.InjOn z s)
    (x : ℝ) (hx : ∀ t ∈ s, x + z t ≠ 0) :
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
      (Nat.factorial s.card : ℝ) * multilinearWeight s z x := by
  by_cases hs : s.Nonempty
  · exact physicalFormalR_squarefree_eq_weight_off_poles
      s hs z hz hinj x hx
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [physicalFormalR_coeff_empty, multilinearWeight]

/-- Every nonempty squarefree coefficient of the formal r coordinate
is nonnegative at a positive off-node frequency. -/
theorem physicalFormalR_squarefree_coeff_nonneg
    [Fintype T] (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (hinj : Set.InjOn z s)
    (x : ℝ) (hx : 0 < x) :
    0 ≤ MvPowerSeries.coeff (squarefreeMonomial s)
      (physicalFormalR z x) := by
  have hden : ∀ t ∈ s, x + z t ≠ 0 :=
    fun t _ => (add_pos hx (hz t)).ne'
  rw [physicalFormalR_squarefree_eq_weight_off_poles s hs z hz hinj x hden]
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · simpa only [multilinearWeight] using
      multilinear_W_nonneg s z x hs hx (fun t _ => hz t) hinj

/-- The coefficient is strictly positive when the positive frequency
is distinct from all selected Yukawa rates. -/
theorem physicalFormalR_squarefree_coeff_pos
    [Fintype T] (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (hinj : Set.InjOn z s)
    (x : ℝ) (hx : 0 < x)
    (hxn : ∀ t ∈ s, x ≠ z t) :
    0 < MvPowerSeries.coeff (squarefreeMonomial s)
      (physicalFormalR z x) := by
  have hden : ∀ t ∈ s, x + z t ≠ 0 :=
    fun t _ => (add_pos hx (hz t)).ne'
  rw [physicalFormalR_squarefree_eq_weight_off_poles s hs z hz hinj x hden]
  apply mul_pos
  · exact Nat.cast_pos.mpr (Nat.factorial_pos _)
  · simpa only [multilinearWeight] using
      multilinear_W_pos s z x hs hx (fun t _ => hz t) hinj hxn

/-- The independently recursive r node series inherits nonnegative
squarefree coefficients from the off-node rational identity. -/
theorem RSeries_squarefree_coeff_nonneg
    [Fintype T] (s : Finset T) (hs : s.Nonempty)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (hinj : Set.InjOn z s) (t : T) :
    0 ≤ MvPowerSeries.coeff (squarefreeMonomial s)
      (RSeries z t) := by
  rw [← physicalFormalR_at_node z t]
  exact physicalFormalR_squarefree_coeff_nonneg s hs z hz hinj (z t) (hz t)

end FMSA.Convergence.PureFluidRSquarefreePoleSpan
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_zero
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_add
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_const_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_const_mul
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_subset
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_fresh_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_fresh_mul
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_single
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_finset_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_finset_sum
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_coeff_mul_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_coeff_mul_fixed
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_fresh_affine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.poleRep_fresh_affine
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_poleRep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_poleRep
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.eventually_all_two_sided_pole_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.eventually_all_two_sided_pole_domain
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.simplePoleSum_odd_injective_on_full_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.simplePoleSum_odd_injective_on_full_domain
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_eq_weight_off_poles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_eq_weight_off_poles
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_eq_weight_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_eq_weight_all
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_coeff_nonneg
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_coeff_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidRSquarefreePoleSpan.RSeries_squarefree_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSquarefreePoleSpan.RSeries_squarefree_coeff_nonneg
