import MSAConvergence.PureFluidRDistinctRateApprox
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option linter.style.header false
-- The common finite, decidable context is needed by polynomial
-- coefficient and copied-system proofs even when absent from a
-- particular theorem's conclusion.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! Split each tail variable into finitely many labelled copies. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRLabelSubstitution
open FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidHFormalPositivity
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRFormalDispersion
open FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidRDistinctRateApprox
variable {T : Type*} [Fintype T] [DecidableEq T]

abbrev TailCopies (m : T →₀ ℕ) := Σ t : T, Fin (m t)

def splitTheta (m : T →₀ ℕ) (t : T) :
    MvPowerSeries (TailCopies m) ℝ :=
  ∑ j : Fin (m t), X ⟨t, j⟩

omit [Fintype T] [DecidableEq T] in
theorem splitTheta_constantCoeff_zero
    (m : T →₀ ℕ) (t : T) :
    MvPowerSeries.constantCoeff (splitTheta m t) = 0 := by
  classical
  simp [splitTheta, MvPowerSeries.constantCoeff_X]

omit [DecidableEq T] in
set_option linter.unusedFintypeInType false in
theorem splitTheta_hasSubst (m : T →₀ ℕ) :
    MvPowerSeries.HasSubst (splitTheta m) := by
  classical
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero
    (splitTheta_constantCoeff_zero m)

omit [DecidableEq T] in
/-- A sum of split original tail variables groups exactly into the
sum over all labelled copies. -/
theorem splitTheta_sum_identity
    (m : T →₀ ℕ) (a : T → ℝ)
    (F : T → MvPowerSeries (TailCopies m) ℝ) :
    (∑ t, C (a t) * (splitTheta m t * F t)) =
      ∑ l : TailCopies m, C (a l.1) * (X l * F l.1) := by
  classical
  simp only [splitTheta, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_sigma]

/-- Substituting the sum of labelled generators into the original H
node series gives a solution of the copied-tail H node system. -/
theorem split_HNodeSystem
    (m : T →₀ ℕ) (z : T → ℝ) :
    HNodeSystem
      (fun a b : TailCopies m => (z a.1 + z b.1)⁻¹)
      (fun a : TailCopies m =>
        MvPowerSeries.subst (splitTheta m) (physicalH z a.1)) := by
  classical
  let ha := splitTheta_hasSubst m
  intro a
  have hs := congrArg (MvPowerSeries.substAlgHom (R := ℝ) ha)
    (HSeries_system (fun s t : T => (z s + z t)⁻¹) a.1)
  simp only [map_add, map_sum, map_one, map_mul,
    MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X ha,
    MvPowerSeries.subst_C] at hs
  change MvPowerSeries.subst (splitTheta m) (physicalH z a.1) =
    1 + ∑ t, C ((z a.1 + z t)⁻¹) *
      (splitTheta m t *
        (MvPowerSeries.subst (splitTheta m) (physicalH z a.1) *
         MvPowerSeries.subst (splitTheta m) (physicalH z t))) at hs
  rw [splitTheta_sum_identity m
    (fun t => (z a.1 + z t)⁻¹)
    (fun t => MvPowerSeries.subst (splitTheta m) (physicalH z a.1) *
      MvPowerSeries.subst (splitTheta m) (physicalH z t))] at hs
  exact hs

/-- At coincident copy rates, the copied H-node series is exactly
the original H-node series after the labelled-variable substitution. -/
theorem split_physicalH_eq_copy
    (m : T →₀ ℕ) (z : T → ℝ) (a : TailCopies m) :
    MvPowerSeries.subst (splitTheta m) (physicalH z a.1) =
      physicalH (fun l : TailCopies m => z l.1) a := by
  classical
  have hcopy : HNodeSystem
      (fun a b : TailCopies m => (z a.1 + z b.1)⁻¹)
      (fun a : TailCopies m => physicalH (fun l : TailCopies m => z l.1) a) := by
    simpa only [physicalH] using
      (HSeries_system (fun a b : TailCopies m => (z a.1 + z b.1)⁻¹))
  have h := HNodeSystem_unique
    (fun a b : TailCopies m => (z a.1 + z b.1)⁻¹)
    (fun a : TailCopies m =>
      MvPowerSeries.subst (splitTheta m) (physicalH z a.1))
    (fun a : TailCopies m => physicalH (fun l : TailCopies m => z l.1) a)
    (split_HNodeSystem m z) hcopy
  exact congrFun h a

/-- The substituted original R-node family solves the independently
recursive copied-tail R-node system. -/
theorem split_RNodeSystem
    (m : T →₀ ℕ) (z : T → ℝ) :
    RNodeSystem (fun l : TailCopies m => z l.1)
      (fun a : TailCopies m =>
        MvPowerSeries.subst (splitTheta m) (RSeries z a.1)) := by
  classical
  let ha := splitTheta_hasSubst m
  intro a
  have hs := congrArg (MvPowerSeries.substAlgHom (R := ℝ) ha)
    (RSeries_system z a.1)
  simp only [map_sum, map_mul, map_sub,
    MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X ha,
    MvPowerSeries.subst_C] at hs
  change MvPowerSeries.subst (splitTheta m) (RSeries z a.1) =
    ∑ t, C ((z a.1 + z t)⁻¹) *
      (splitTheta m t *
        ((MvPowerSeries.subst (splitTheta m) (physicalH z a.1) *
          MvPowerSeries.subst (splitTheta m) (physicalH z t)) *
            (C (z t) - MvPowerSeries.subst (splitTheta m) (RSeries z t)))) at hs
  rw [splitTheta_sum_identity m
    (fun t => (z a.1 + z t)⁻¹)
    (fun t =>
      ((MvPowerSeries.subst (splitTheta m) (physicalH z a.1) *
        MvPowerSeries.subst (splitTheta m) (physicalH z t)) *
          (C (z t) - MvPowerSeries.subst (splitTheta m) (RSeries z t))))] at hs
  simp_rw [split_physicalH_eq_copy m z] at hs
  exact hs

/-- At equal copy rates, the copied R-node series is exactly the
original R-node series after the labelled-variable substitution. -/
theorem split_RSeries_eq_copy
    (m : T →₀ ℕ) (z : T → ℝ) (a : TailCopies m) :
    MvPowerSeries.subst (splitTheta m) (RSeries z a.1) =
      RSeries (fun l : TailCopies m => z l.1) a := by
  classical
  have h := RNodeSystem_unique
    (fun l : TailCopies m => z l.1)
    (fun a : TailCopies m =>
      MvPowerSeries.subst (splitTheta m) (RSeries z a.1))
    (RSeries (fun l : TailCopies m => z l.1))
    (split_RNodeSystem m z)
    (RSeries_system (fun l : TailCopies m => z l.1))
  exact congrFun h a

/-- The substituted off-node r series obeys the copied-tail
degree-lowering resolvent equation with the copied H and R nodes. -/
theorem split_physicalFormalR_recursion
    (m : T →₀ ℕ) (z : T → ℝ) (x : ℝ) :
    MvPowerSeries.subst (splitTheta m) (physicalFormalR z x) =
      ∑ l : TailCopies m,
        C ((x + z l.1)⁻¹) *
          (X l * physicalH (fun a : TailCopies m => z a.1) l *
            (C (z l.1) -
              RSeries (fun a : TailCopies m => z a.1) l +
              MvPowerSeries.subst (splitTheta m) (physicalFormalR z x))) := by
  classical
  let ha := splitTheta_hasSubst m
  have hs := congrArg (MvPowerSeries.substAlgHom (R := ℝ) ha)
    (physicalFormalR_series_recursion z x)
  simp only [map_sum, map_mul, map_sub, map_add,
    MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X ha,
    MvPowerSeries.subst_C] at hs
  have hgroup : MvPowerSeries.subst (splitTheta m) (physicalFormalR z x) =
      ∑ t, C ((x + z t)⁻¹) *
        (splitTheta m t *
          (MvPowerSeries.subst (splitTheta m) (physicalH z t) *
            (C (z t) - MvPowerSeries.subst (splitTheta m) (RSeries z t) +
              MvPowerSeries.subst (splitTheta m) (physicalFormalR z x)))) := by
    simpa only [mul_assoc] using hs
  rw [splitTheta_sum_identity m (fun t => (x + z t)⁻¹)
    (fun t => MvPowerSeries.subst (splitTheta m) (physicalH z t) *
      (C (z t) - MvPowerSeries.subst (splitTheta m) (RSeries z t) +
        MvPowerSeries.subst (splitTheta m) (physicalFormalR z x)))] at hgroup
  simp_rw [split_physicalH_eq_copy m z,
    split_RSeries_eq_copy m z] at hgroup
  simpa only [mul_assoc] using hgroup

/-- With fixed H and R node families, the off-node r resolvent
equation has a unique multivariate formal solution. -/
theorem offnode_r_recursion_unique
    {U : Type*} [Fintype U]
    (z : U → ℝ) (x : ℝ)
    (H R : U → MvPowerSeries U ℝ)
    (A B : MvPowerSeries U ℝ)
    (hA : A = ∑ u, C ((x + z u)⁻¹) *
      (X u * H u * (C (z u) - R u + A)))
    (hB : B = ∑ u, C ((x + z u)⁻¹) *
      (X u * H u * (C (z u) - R u + B))) :
    A = B := by
  classical
  let W : MvPowerSeries U ℝ :=
    ∑ u, C ((x + z u)⁻¹) * (X u * H u)
  let G : MvPowerSeries U ℝ :=
    ∑ u, C ((x + z u)⁻¹) * (X u * H u * (C (z u) - R u))
  have hform (Y : MvPowerSeries U ℝ)
      (hY : Y = ∑ u, C ((x + z u)⁻¹) *
        (X u * H u * (C (z u) - R u + Y))) :
      Y = G + W * Y := by
    calc
      Y = ∑ u, C ((x + z u)⁻¹) *
        (X u * H u * (C (z u) - R u + Y)) := hY
      _ = G + W * Y := by
        dsimp [G, W]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring
  have hW0 : MvPowerSeries.constantCoeff W = 0 := by
    dsimp [W]
    simp [MvPowerSeries.constantCoeff_X]
  have hU : (1 - W) * (1 - W)⁻¹ = 1 := by
    apply MvPowerSeries.mul_inv_cancel
    simp [hW0]
  have hA' := hform A hA
  have hB' := hform B hB
  have hdiff : (1 - W) * (A - B) = 0 := by
    linear_combination hA' - hB'
  have hzero : A - B = 0 := by
    calc
      A - B = ((1 - W) * (1 - W)⁻¹) * (A - B) := by rw [hU, one_mul]
      _ = ((1 - W) * (A - B)) * (1 - W)⁻¹ := by ring
      _ = 0 := by rw [hdiff]; ring
  exact sub_eq_zero.mp hzero

/-- The actual off-node r series of equal-rate labelled copies is
the original off-node r series after splitting each tail variable. -/
theorem split_physicalFormalR_eq_copy
    (m : T →₀ ℕ) (z : T → ℝ) (x : ℝ) :
    MvPowerSeries.subst (splitTheta m) (physicalFormalR z x) =
      physicalFormalR (fun a : TailCopies m => z a.1) x := by
  classical
  let zc : TailCopies m → ℝ := fun a => z a.1
  let Hc : TailCopies m → MvPowerSeries (TailCopies m) ℝ :=
    physicalH zc
  let Rc : TailCopies m → MvPowerSeries (TailCopies m) ℝ :=
    RSeries zc
  apply offnode_r_recursion_unique zc x Hc Rc
  · simpa only [zc, Hc, Rc] using split_physicalFormalR_recursion m z x
  · simpa only [zc, Hc, Rc] using
      physicalFormalR_series_recursion zc x

/-- The multinomial count of the full squarefree monomial is the
factorial of the number of labelled variables. -/
theorem squarefree_multinomial_univ
    {U : Type*} [Fintype U] :
    (squarefreeMonomial (Finset.univ : Finset U)).multinomial =
      Nat.factorial (Fintype.card U) := by
  classical
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  simp [Nat.multinomial, squarefreeMonomial_apply]

/-- Coefficients of a power of the sum of all labelled generators. -/
theorem coeff_sum_X_pow
    {U : Type*} [Fintype U]
    (d : U →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff d
      ((∑ j : U, (X j : MvPowerSeries U ℝ)) ^ n) =
        if d.sum (fun _ v => v) = n then d.multinomial else 0 := by
  classical
  have hcoe :
      ((∑ j : U, MvPolynomial.X j : MvPolynomial U ℝ) : MvPowerSeries U ℝ) =
        ∑ j : U, (X j : MvPowerSeries U ℝ) := by
    change MvPolynomial.coeToMvPowerSeries.ringHom
      (∑ j : U, MvPolynomial.X j) = _
    simp
  rw [← hcoe, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe]
  exact MvPolynomial.coeff_sum_X_pow_of_fintype d n

/-- A single fibre contributes its factorial when all its labelled
copies are used exactly once. -/
theorem coeff_squarefree_sum_X_pow
    {U : Type*} [Fintype U] (n : ℕ) :
    MvPowerSeries.coeff (squarefreeMonomial (Finset.univ : Finset U))
      ((∑ j : U, (X j : MvPowerSeries U ℝ)) ^ n) =
        if Fintype.card U = n then (Nat.factorial (Fintype.card U) : ℝ)
        else 0 := by
  classical
  rw [coeff_sum_X_pow, squarefree_multinomial_univ]
  have hsum :
      (squarefreeMonomial (Finset.univ : Finset U)).sum (fun _ v => v) =
        Fintype.card U := by
    classical
    have hsupport :
        (squarefreeMonomial (Finset.univ : Finset U)).support =
          Finset.univ := by
      ext u
      simp [Finsupp.mem_support_iff, squarefreeMonomial_apply]
    simp [Finsupp.sum, hsupport, squarefreeMonomial_apply]
  rw [hsum]
  simp

/-- The full squarefree copied index merges back to the original
multiindex of copy counts. -/
theorem squarefree_copies_mapDomain
    (m : T →₀ ℕ) :
    (squarefreeMonomial (Finset.univ : Finset (TailCopies m))).mapDomain
      Sigma.fst = m := by
  classical
  let d : TailCopies m →₀ ℕ := squarefreeMonomial Finset.univ
  have hsupport : d.support = Finset.univ := by
    ext a
    simp [d, Finsupp.mem_support_iff, squarefreeMonomial_apply]
  have hsum : d.mapDomain Sigma.fst =
      ∑ a : TailCopies m, Finsupp.single a.1 1 := by
    rw [Finsupp.mapDomain, Finsupp.sum, hsupport]
    simp [d, squarefreeMonomial_apply]
  change d.mapDomain Sigma.fst = m
  rw [hsum]
  ext t
  simp [Fintype.sum_sigma]

/-- A split tail variable is a weighted sum over all copies,
with weight one exactly on its own fibre. -/
theorem splitTheta_eq_weighted_sum
    (m : T →₀ ℕ) (t : T) :
    splitTheta m t =
      ∑ a : TailCopies m,
        (if a.1 = t then (X a : MvPowerSeries (TailCopies m) ℝ) else 0) := by
  classical
  rw [Fintype.sum_sigma]
  simp only [splitTheta]
  symm
  rw [Finset.sum_eq_single t]
  · simp
  · intro u hu hut
    simp [hut]
  · intro ht
    exact False.elim (ht (Finset.mem_univ t))

/-- The coefficient of a power of one split variable has the
multinomial value and vanishes outside that variable's fibre. -/
theorem coeff_splitTheta_pow
    (m : T →₀ ℕ) (t : T) (d : TailCopies m →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff d ((splitTheta m t) ^ n) =
      if d.sum (fun _ v => v) = n then
        (d.multinomial : ℝ) *
          d.prod (fun a v => (if a.1 = t then (1 : ℝ) else 0) ^ v)
      else 0 := by
  classical
  let w : TailCopies m → ℝ := fun a => if a.1 = t then 1 else 0
  have hsplit : splitTheta m t =
      ∑ a : TailCopies m, w a • (X a : MvPowerSeries (TailCopies m) ℝ) := by
    rw [splitTheta_eq_weighted_sum]
    simp [w, ite_smul]
  have hcoe :
      ((∑ a : TailCopies m, w a • MvPolynomial.X a :
          MvPolynomial (TailCopies m) ℝ) : MvPowerSeries (TailCopies m) ℝ) =
        ∑ a : TailCopies m, w a • (X a : MvPowerSeries (TailCopies m) ℝ) := by
    change MvPolynomial.coeToMvPowerSeries.ringHom
      (∑ a : TailCopies m, w a • MvPolynomial.X a) = _
    simp
  rw [hsplit, ← hcoe, ← MvPolynomial.coe_pow,
    MvPolynomial.coeff_coe]
  simpa only [w] using
    (MvPolynomial.coeff_linearCombination_X_pow_of_fintype w d n)

/-- A nonzero coefficient of one split-variable power uses only
labelled copies belonging to that fibre. -/
theorem coeff_splitTheta_pow_support
    (m : T →₀ ℕ) (t : T) (d : TailCopies m →₀ ℕ) (n : ℕ)
    (h : MvPowerSeries.coeff d ((splitTheta m t) ^ n) ≠ 0) :
    ∀ a ∈ d.support, a.1 = t := by
  classical
  intro a ha
  by_contra hat
  have hd : d a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hp : 0 < d a := Nat.pos_of_ne_zero hd
  have hprod :
      d.prod (fun b v => (if b.1 = t then (1 : ℝ) else 0) ^ v) = 0 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_zero ha
    simp [hat, hp.ne']
  rw [coeff_splitTheta_pow, hprod] at h
  simp at h

/-- Nonzero coefficients of a split-variable power have exactly
that power's total degree. -/
theorem coeff_splitTheta_pow_degree
    (m : T →₀ ℕ) (t : T) (d : TailCopies m →₀ ℕ) (n : ℕ)
    (h : MvPowerSeries.coeff d ((splitTheta m t) ^ n) ≠ 0) :
    d.sum (fun _ v => v) = n := by
  rw [coeff_splitTheta_pow] at h
  split_ifs at h with hd
  · exact hd
  · simp at h

/-- On its own fibre, the coefficient is the ordinary
multinomial coefficient at the matching total degree. -/
theorem coeff_splitTheta_pow_of_support
    (m : T →₀ ℕ) (t : T) (d : TailCopies m →₀ ℕ) (n : ℕ)
    (hd : ∀ a ∈ d.support, a.1 = t) :
    MvPowerSeries.coeff d ((splitTheta m t) ^ n) =
      if d.sum (fun _ v => v) = n then (d.multinomial : ℝ) else 0 := by
  classical
  rw [coeff_splitTheta_pow]
  have hp :
      d.prod (fun a v => (if a.1 = t then (1 : ℝ) else 0) ^ v) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro a ha
    simp [hd a ha]
  rw [hp]
  simp

/-- A squarefree full-copy index has only one decomposition whose
part assigned to each original tail stays in its own fibre. -/
theorem full_copy_partition_unique
    (m : T →₀ ℕ) (l : T → TailCopies m →₀ ℕ)
    (hl : (∑ t : T, l t) =
      squarefreeMonomial (Finset.univ : Finset (TailCopies m)))
    (hs : ∀ t a, l t a ≠ 0 → a.1 = t) :
    ∀ t a, l t a = if a.1 = t then 1 else 0 := by
  classical
  intro t a
  by_cases ht : a.1 = t
  · have hsum := congrArg (fun q : TailCopies m →₀ ℕ => q a) hl
    rw [Finset.sum_apply'] at hsum
    have hsingle : (∑ u : T, l u a) = l a.1 a := by
      apply Finset.sum_eq_single a.1
      · intro u hu hne
        by_contra hn
        exact hne (hs u a hn).symm
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ a.1))
    rw [hsingle] at hsum
    simp only [squarefreeMonomial_apply, Finset.mem_univ,
      if_true] at hsum
    simpa [ht] using hsum
  · have hzero : l t a = 0 := by
      by_contra hn
      exact ht (hs t a hn)
    simp [ht, hzero]

/-- In the unique fibre-respecting decomposition, each part has
degree equal to the number of copies in its fibre. -/
theorem full_copy_partition_degree
    (m : T →₀ ℕ) (l : T → TailCopies m →₀ ℕ)
    (hl : (∑ t : T, l t) =
      squarefreeMonomial (Finset.univ : Finset (TailCopies m)))
    (hs : ∀ t a, l t a ≠ 0 → a.1 = t) (t : T) :
    (l t).sum (fun _ v => v) = m t := by
  classical
  have hp := full_copy_partition_unique m l hl hs
  change (l t).degree = m t
  rw [Finsupp.degree_eq_sum]
  rw [Fintype.sum_sigma]
  have hcard (u : T) :
      (if u = t then (Finset.univ : Finset (Fin (m u))) else ∅).card =
        if u = t then m u else 0 := by
    split_ifs <;> simp
  simp [hp, hcard]

/-- A nonzero product term in the full-copy coefficient can only
come from the original copy-count multiindex. -/
theorem full_copy_product_term_index
    (m e : T →₀ ℕ)
    (l : T →₀ (TailCopies m →₀ ℕ))
    (hl : l ∈ Finset.finsuppAntidiag Finset.univ
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m))))
    (hprod : (∏ t : T,
      MvPowerSeries.coeff (l t) ((splitTheta m t) ^ (e t))) ≠ 0) :
    e = m := by
  classical
  have hsum : (∑ t : T, l t) =
      squarefreeMonomial (Finset.univ : Finset (TailCopies m)) :=
    (Finset.mem_finsuppAntidiag.mp hl).1
  have hcoeff (t : T) :
      MvPowerSeries.coeff (l t) ((splitTheta m t) ^ (e t)) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) t (Finset.mem_univ t)
  have hs (t : T) (a : TailCopies m) (ha : l t a ≠ 0) : a.1 = t :=
    coeff_splitTheta_pow_support m t (l t) (e t) (hcoeff t) a
      (Finsupp.mem_support_iff.mpr ha)
  ext t
  have hdegree := coeff_splitTheta_pow_degree m t (l t) (e t) (hcoeff t)
  exact hdegree.symm.trans (full_copy_partition_degree m l hsum hs t)

/-- Every original multiindex other than the copy counts vanishes
when extracting the full squarefree copied coefficient. -/
theorem full_copy_product_coeff_zero_of_ne
    (m e : T →₀ ℕ) (hne : e ≠ m) :
    MvPowerSeries.coeff
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m)))
      (∏ t : T, (splitTheta m t) ^ (e t)) = 0 := by
  classical
  rw [MvPowerSeries.coeff_prod]
  apply Finset.sum_eq_zero
  intro l hl
  by_contra hprod
  exact hne (full_copy_product_term_index m e l hl hprod)

/-- The squarefree part assigned to a single original tail. -/
def fibreMonomial (m : T →₀ ℕ) (t : T) : TailCopies m →₀ ℕ :=
  squarefreeMonomial (Finset.univ.filter (fun a : TailCopies m => a.1 = t))

theorem fibreMonomial_apply (m : T →₀ ℕ) (t : T) (a : TailCopies m) :
    fibreMonomial m t a = if a.1 = t then 1 else 0 := by
  classical
  simp [fibreMonomial, squarefreeMonomial_apply]

/-- The canonical fibre parts sum to the full squarefree index. -/
theorem sum_fibreMonomial (m : T →₀ ℕ) :
    (∑ t : T, fibreMonomial m t) =
      squarefreeMonomial (Finset.univ : Finset (TailCopies m)) := by
  classical
  ext a
  rw [Finset.sum_apply']
  simp [fibreMonomial_apply, squarefreeMonomial_apply]

def canonicalPartition (m : T →₀ ℕ) :
    T →₀ (TailCopies m →₀ ℕ) :=
  Finsupp.onFinset Finset.univ (fibreMonomial m)
    (by intro t ht; exact Finset.mem_univ t)

theorem canonicalPartition_apply (m : T →₀ ℕ) (t : T) :
    canonicalPartition m t = fibreMonomial m t := by
  classical
  simp [canonicalPartition]

theorem canonicalPartition_mem (m : T →₀ ℕ) :
    canonicalPartition m ∈ Finset.finsuppAntidiag Finset.univ
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m))) := by
  classical
  rw [Finset.mem_finsuppAntidiag]
  constructor
  · simpa only [canonicalPartition_apply] using sum_fibreMonomial m
  · exact Finset.subset_univ _

theorem fibreMonomial_degree (m : T →₀ ℕ) (t : T) :
    (fibreMonomial m t).sum (fun _ v => v) = m t := by
  apply full_copy_partition_degree m (fibreMonomial m)
    (sum_fibreMonomial m)
  · intro u a ha
    have hp := fibreMonomial_apply m u a
    by_cases h : a.1 = u
    · exact h
    · simp [h] at hp
      exact False.elim (ha (hp.trans rfl))

theorem fibreMonomial_multinomial (m : T →₀ ℕ) (t : T) :
    (fibreMonomial m t).multinomial = Nat.factorial (m t) := by
  classical
  have hsupp : (fibreMonomial m t).support =
      Finset.univ.filter (fun a : TailCopies m => a.1 = t) := by
    ext a
    simp [Finsupp.mem_support_iff, fibreMonomial_apply]
  have hprod : (fibreMonomial m t).prod
      (fun _ n => Nat.factorial n) = 1 := by
    unfold Finsupp.prod
    rw [hsupp]
    apply Finset.prod_eq_one
    intro a ha
    have hat : a.1 = t := (Finset.mem_filter.mp ha).2
    simp [fibreMonomial_apply, hat]
  have hfun : (fun _ : TailCopies m => (id : ℕ → ℕ)) =
      (fun _ v => v) := rfl
  rw [Finsupp.multinomial, hfun, fibreMonomial_degree, hprod]
  simp

theorem coeff_fibreMonomial_splitTheta_pow (m : T →₀ ℕ) (t : T) :
    MvPowerSeries.coeff (fibreMonomial m t)
      ((splitTheta m t) ^ (m t)) = (Nat.factorial (m t) : ℝ) := by
  rw [coeff_splitTheta_pow_of_support]
  · simp [fibreMonomial_degree, fibreMonomial_multinomial]
  · intro a ha
    have hne : fibreMonomial m t a ≠ 0 := Finsupp.mem_support_iff.mp ha
    rw [fibreMonomial_apply] at hne
    by_cases h : a.1 = t
    · exact h
    · simp [h] at hne

/-- The only possibly nonzero summand of the full squarefree
coefficient product is the canonical fibre partition. -/
theorem full_copy_product_term_partition
    (m e : T →₀ ℕ)
    (l : T →₀ (TailCopies m →₀ ℕ))
    (hl : l ∈ Finset.finsuppAntidiag Finset.univ
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m))))
    (hprod : (∏ t : T,
      MvPowerSeries.coeff (l t) ((splitTheta m t) ^ (e t))) ≠ 0) :
    l = canonicalPartition m := by
  classical
  have hsum : (∑ t : T, l t) =
      squarefreeMonomial (Finset.univ : Finset (TailCopies m)) :=
    (Finset.mem_finsuppAntidiag.mp hl).1
  have hcoeff (t : T) :
      MvPowerSeries.coeff (l t) ((splitTheta m t) ^ (e t)) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) t (Finset.mem_univ t)
  have hs (t : T) (a : TailCopies m) (ha : l t a ≠ 0) : a.1 = t :=
    coeff_splitTheta_pow_support m t (l t) (e t) (hcoeff t) a
      (Finsupp.mem_support_iff.mpr ha)
  have hp := full_copy_partition_unique m l hsum hs
  ext t a
  rw [canonicalPartition_apply, fibreMonomial_apply]
  exact hp t a

/-- The full squarefree copied coefficient of the matching
split-variable monomial is the product of fibre factorials. -/
theorem full_copy_product_coeff_same
    (m : T →₀ ℕ) :
    MvPowerSeries.coeff
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m)))
      (∏ t : T, (splitTheta m t) ^ (m t)) =
        ∏ t : T, (Nat.factorial (m t) : ℝ) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (canonicalPartition m)]
  · simp only [canonicalPartition_apply,
      coeff_fibreMonomial_splitTheta_pow]
  · intro l hl hne
    by_contra hprod
    exact hne (full_copy_product_term_partition m m l hl hprod)
  · intro hnot
    exact False.elim (hnot (canonicalPartition_mem m))

/-- Exact copied squarefree coefficient for every original
monomial: it is supported only at the copy-count multiindex. -/
theorem full_copy_monomial_coeff
    (m e : T →₀ ℕ) :
    MvPowerSeries.coeff
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m)))
      (e.prod (fun t n => (splitTheta m t) ^ n)) =
        if e = m then ∏ t : T, (Nat.factorial (m t) : ℝ) else 0 := by
  classical
  rw [Finsupp.prod_fintype]
  · by_cases he : e = m
    · subst e
      simp [full_copy_product_coeff_same]
    · simp [he, full_copy_product_coeff_zero_of_ne m e he]
  · intro t
    simp

/-- Exact labelled-copy factorial extraction for an arbitrary
multivariate formal series. -/
theorem coeff_splitTheta_full_squarefree
    (m : T →₀ ℕ) (f : MvPowerSeries T ℝ) :
    MvPowerSeries.coeff
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m)))
      (MvPowerSeries.subst (splitTheta m) f) =
        (∏ t : T, (Nat.factorial (m t) : ℝ)) *
          MvPowerSeries.coeff m f := by
  classical
  rw [MvPowerSeries.coeff_subst (splitTheta_hasSubst m)]
  rw [finsum_eq_single _ m]
  · rw [full_copy_monomial_coeff]
    simp [smul_eq_mul, mul_comm]
  · intro e he
    rw [full_copy_monomial_coeff]
    simp [he]

/-- Every nonconstant coefficient of the actual pure-fluid formal
off-node r series is strictly positive at positive frequency and
positive tail rates, including repeated indices and coincident rates. -/
theorem physicalFormalR_coeff_pos_all
    (m : T →₀ ℕ) (hm : m ≠ 0)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 < x) :
    0 < MvPowerSeries.coeff m (physicalFormalR z x) := by
  classical
  let zc : TailCopies m → ℝ := fun a => z a.1
  have hzc : ∀ a : TailCopies m, 0 < zc a := fun a => hz a.1
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hm
  have hmt : 0 < m t := Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp ht)
  have hs : (Finset.univ : Finset (TailCopies m)).Nonempty := by
    exact ⟨⟨t, ⟨0, hmt⟩⟩, Finset.mem_univ _⟩
  have hcopy := physicalFormalR_squarefree_coeff_pos_any_rates
    (Finset.univ : Finset (TailCopies m)) hs zc hzc x hx
  rw [← split_physicalFormalR_eq_copy m z x,
    coeff_splitTheta_full_squarefree] at hcopy
  have hfactor : (0 : ℝ) <
      ∏ t : T, (Nat.factorial (m t) : ℝ) := by
    apply Finset.prod_pos
    intro t _
    exact_mod_cast Nat.factorial_pos (m t)
  exact pos_of_mul_pos_right hcopy (le_of_lt hfactor)

/-- The independently recursive r-node series also has strictly
positive coefficients at every nonzero multiindex. -/
theorem RSeries_coeff_pos_all
    (m : T →₀ ℕ) (hm : m ≠ 0)
    (z : T → ℝ) (hz : ∀ t, 0 < z t) (t : T) :
    0 < MvPowerSeries.coeff m (RSeries z t) := by
  rw [← physicalFormalR_at_node z t]
  exact physicalFormalR_coeff_pos_all m hm z hz (z t) (hz t)

end FMSA.Convergence.PureFluidRLabelSubstitution

/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_constantCoeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_constantCoeff_zero
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_hasSubst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_hasSubst
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_sum_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_sum_identity
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.split_HNodeSystem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.split_HNodeSystem
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.split_physicalH_eq_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.split_physicalH_eq_copy
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.split_RNodeSystem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.split_RNodeSystem
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.split_RSeries_eq_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.split_RSeries_eq_copy
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.split_physicalFormalR_recursion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.split_physicalFormalR_recursion
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.offnode_r_recursion_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.offnode_r_recursion_unique
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.split_physicalFormalR_eq_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.split_physicalFormalR_eq_copy
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.squarefree_multinomial_univ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.squarefree_multinomial_univ
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_sum_X_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_sum_X_pow
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_squarefree_sum_X_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_squarefree_sum_X_pow
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.squarefree_copies_mapDomain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.squarefree_copies_mapDomain
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_eq_weighted_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.splitTheta_eq_weighted_sum
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow_support
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow_degree
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow_of_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_pow_of_support
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_partition_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_partition_unique
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_partition_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_partition_degree
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_term_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_term_index
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_coeff_zero_of_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_coeff_zero_of_ne
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.fibreMonomial_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.fibreMonomial_apply
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.sum_fibreMonomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.sum_fibreMonomial
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.canonicalPartition_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.canonicalPartition_apply
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.canonicalPartition_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.canonicalPartition_mem
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.fibreMonomial_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.fibreMonomial_degree
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.fibreMonomial_multinomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.fibreMonomial_multinomial
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_fibreMonomial_splitTheta_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_fibreMonomial_splitTheta_pow
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_term_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_term_partition
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_coeff_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_product_coeff_same
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_monomial_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.full_copy_monomial_coeff
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_full_squarefree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.coeff_splitTheta_full_squarefree
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.physicalFormalR_coeff_pos_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.physicalFormalR_coeff_pos_all
/-- info: 'FMSA.Convergence.PureFluidRLabelSubstitution.RSeries_coeff_pos_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLabelSubstitution.RSeries_coeff_pos_all
