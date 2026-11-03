import MSAConvergence.IsolatedEndpointLimits
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.Infinite

/-! Constructed primitive coordinate relations for regular polynomial root
prefixes. Localizing the actual square residual quotient at its Jacobian
constructs finite generic algebras and exact saturated eliminants. Continuity
extends their primitive relations across exceptional coupling values; finite
artificial endpoint fibers give full limits without isolating original roots. -/

noncomputable section
open Polynomial Algebra
namespace FMSA.Convergence.SelectedBranchAlgebraicity

/-- Unit coefficient ideal prevents a polynomial becoming zero under ANY
coefficient specialization into a nontrivial ring. -/
theorem map_ne_zero_of_contentIdeal_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (P : Polynomial R) (hP : P.contentIdeal = ⊤) (f : R →+* S) :
    P.map f ≠ 0 := by
  have htop : (P.map f).contentIdeal = ⊤ := by
    rw [Polynomial.contentIdeal_map_eq_map_contentIdeal,hP,Ideal.map_top]
  intro hz
  have hbad : (⊥ : Ideal S) = ⊤ := by simpa only [hz,Polynomial.contentIdeal_zero] using htop
  exact bot_ne_top hbad

/-- A primitive coordinate relation over K[t] remains a NONZERO univariate
polynomial after specialization at EVERY finite endpoint, not only generic t. -/
theorem primitive_specialization_ne_zero
    {K : Type*} [Field K] (P : Polynomial (Polynomial K))
    (hP : P.IsPrimitive) (b : K) : P.map (Polynomial.evalRingHom b) ≠ 0 := by
  apply map_ne_zero_of_contentIdeal_eq_top P _ (Polynomial.evalRingHom b)
  exact (Polynomial.isPrimitive_iff_contentIdeal_eq_top P).mp hP

/-- Over a field the existing unramified/free finite theorem supplies
finite dimension, without assuming that the algebra is nontrivial. -/
theorem finite_of_unramified_finite_type
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Algebra.EssFiniteType K B] [Algebra.FormallyUnramified K B] :
    Module.Finite K B := Algebra.FormallyUnramified.finite_of_free K B

/-- A square unit-Jacobian presentation will supply relative dimension zero;
the established etale/unramified API then gives finite dimension over K. -/
theorem finite_of_standard_smooth_dimension_zero
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 K B] : Module.Finite K B := by
  exact finite_of_unramified_finite_type

section AlgebraDefinitions
variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

def determinantPolynomial (F : I → MvPolynomial I K) : MvPolynomial I K :=
  Matrix.det (fun i j => MvPolynomial.pderiv i (F j))

def augmentedRelations (F : I → MvPolynomial I K) :
    I ⊕ Unit → MvPolynomial (I ⊕ Unit) K :=
  Sum.elim (fun i => MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (F i))
    (fun _ => MvPolynomial.X (Sum.inr ()) *
      MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (determinantPolynomial F)-1)

abbrev regularQuotient (F : I → MvPolynomial I K) :=
  MvPolynomial (I ⊕ Unit) K ⧸ Ideal.span (Set.range (augmentedRelations F))

abbrev residualQuotient (F : I → MvPolynomial I K) :=
  MvPolynomial I K ⧸ Ideal.span (Set.range F)

def residualPresentation (F : I → MvPolynomial I K) :
    Algebra.PreSubmersivePresentation K (residualQuotient F) I I :=
  { __ := Algebra.Presentation.naive (v := F)
    map := id
    map_inj := Function.injective_id }

def residualDeterminant (F : I → MvPolynomial I K) : residualQuotient F :=
  Ideal.Quotient.mk _ (determinantPolynomial F)

abbrev regularLocalization (F : I → MvPolynomial I K) :=
  Localization.Away (residualDeterminant F)

def coordinatePolynomial (P : Polynomial K) (i : I) : MvPolynomial I K :=
  P.eval₂ MvPolynomial.C (MvPolynomial.X i)

end AlgebraDefinitions

section GenericJacobian
open MvPolynomial
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]







omit [Fintype I] in
private theorem extra_partial_rename (u : Unit) (P : MvPolynomial I K) :
    MvPolynomial.pderiv (Sum.inr u : I ⊕ Unit)
      (MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

/-- Inverting the original Jacobian adds one variable and relation. The
augmented square Jacobian determinant is exactly the square of the original.
No root, unit, finite-fiber or generic-position assumption is used. -/
theorem augmented_jacobian_determinant (F : I → MvPolynomial I K) :
    Matrix.det (fun i j => MvPolynomial.pderiv i (augmentedRelations F j)) =
      (MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (determinantPolynomial F))^2 := by
  have hmat : (fun i j => MvPolynomial.pderiv i (augmentedRelations F j)) =
      Matrix.fromBlocks
        (fun i j => MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (MvPolynomial.pderiv i (F j)))
        (fun i (_ : Unit) => MvPolynomial.X (Sum.inr ()) *
          MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (MvPolynomial.pderiv i (determinantPolynomial F)))
        0
        (fun (_ _ : Unit) => MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (determinantPolynomial F)) := by
    funext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · simp [augmentedRelations,MvPolynomial.pderiv_rename Sum.inl_injective]
    · simp [augmentedRelations,MvPolynomial.pderiv_rename Sum.inl_injective]
    · simp [augmentedRelations,extra_partial_rename]
    · simp [augmentedRelations,extra_partial_rename]
  rw [hmat,Matrix.det_fromBlocks_zero₂₁]
  have hdet : Matrix.det (fun i j => MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (MvPolynomial.pderiv i (F j))) =
      MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (determinantPolynomial F) := by
    let f : MvPolynomial I K →+* MvPolynomial (I ⊕ Unit) K :=
      (MvPolynomial.rename (Sum.inl : I → I ⊕ Unit)).toRingHom
    exact (RingHom.map_det f (fun i j => MvPolynomial.pderiv i (F j))).symm
  rw [hdet,Matrix.det_unique]
  ring

/-- The square residual with its Jacobian inverted is a FINITE algebra over
any coefficient field, even if its unsaturated zero fiber has extra components.
The zero algebra is permitted; nontriviality is not inserted as an assumption. -/
theorem regular_quotient_finite (F : I → MvPolynomial I K) :
    Module.Finite K (regularQuotient F) := by
  let P : Algebra.PreSubmersivePresentation K (regularQuotient F) (I ⊕ Unit) (I ⊕ Unit) :=
    { __ := Algebra.Presentation.naive (v := augmentedRelations F)
      map := id
      map_inj := Function.injective_id }
  let QI := Ideal.span (Set.range (augmentedRelations F))
  let delta : regularQuotient F :=
    Ideal.Quotient.mk QI (MvPolynomial.rename (Sum.inl : I → I ⊕ Unit) (determinantPolynomial F))
  let y : regularQuotient F := Ideal.Quotient.mk QI (MvPolynomial.X (Sum.inr ()))
  have hrel : y*delta=1 := by
    have hm : augmentedRelations F (Sum.inr ()) ∈ QI := Ideal.subset_span ⟨Sum.inr (),rfl⟩
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [augmentedRelations,Sum.elim_inr,map_sub,map_mul,map_one,sub_eq_zero] using hz
  have hunit : IsUnit delta := IsUnit.of_mul_eq_one y (by simpa only [mul_comm] using hrel)
  have hJac : P.jacobian = delta^2 := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have hmatrix : P.jacobiMatrix = fun i j => MvPolynomial.pderiv i (augmentedRelations F j) := by
      funext i j
      rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
      rfl
    rw [hmatrix,augmented_jacobian_determinant,map_pow]
    rfl
  let PP : Algebra.SubmersivePresentation K (regularQuotient F) (I ⊕ Unit) (I ⊕ Unit) :=
    { __ := P
      jacobian_isUnit := by rw [hJac]; exact hunit.pow 2 }
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 K (regularQuotient F) :=
    PP.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  exact finite_of_standard_smooth_dimension_zero

/-- Each coordinate in the constructed generic regular algebra has an
ACTUAL monic annihilating polynomial over the coefficient field. -/
theorem regular_quotient_coordinate_isIntegral (F : I → MvPolynomial I K) (i : I) :
    IsIntegral K (Ideal.Quotient.mk (Ideal.span (Set.range (augmentedRelations F)))
      (MvPolynomial.X (Sum.inl i))) := by
  letI := regular_quotient_finite F
  exact IsIntegral.of_finite K _









/-- The naive square residual presentation has the literal formal Jacobian
in the original quotient, with no generic nonzero premise. -/
theorem residualPresentation_jacobian (F : I → MvPolynomial I K) :
    (residualPresentation F).jacobian = residualDeterminant F := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have hm : (residualPresentation F).jacobiMatrix =
      fun i j => MvPolynomial.pderiv i (F j) := by
    funext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    rfl
  rw [hm]
  rfl

/-- The actual localization of the residual quotient at its Jacobian is
finite over the coefficient field. This version exposes the localization
needed to clear saturation powers in later coordinate identities. -/
theorem regular_localization_finite (F : I → MvPolynomial I K) :
    Module.Finite K (regularLocalization F) := by
  let P := residualPresentation F
  let Q : Algebra.PreSubmersivePresentation (residualQuotient F)
      (regularLocalization F) Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway (regularLocalization F) (residualDeterminant F)
  have hu : IsUnit (algebraMap (residualQuotient F) (regularLocalization F) (residualDeterminant F)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hQ : Q.jacobian = algebraMap (residualQuotient F) (regularLocalization F)
      (residualDeterminant F) := Algebra.PreSubmersivePresentation.localizationAway_jacobian _
  have hc : IsUnit (Q.comp P).jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      residualPresentation_jacobian,hQ,Algebra.smul_def]
    exact hu.mul hu
  let PP : Algebra.SubmersivePresentation K (regularLocalization F) (Unit ⊕ I) (Unit ⊕ I) :=
    { __ := Q.comp P
      jacobian_isUnit := hc }
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 K (regularLocalization F) :=
    PP.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  exact finite_of_standard_smooth_dimension_zero

/-- Monic coordinate relations are constructed inside the literal localized
quotient, without an assumed eliminant or finite root set. -/
theorem regular_localization_coordinate_isIntegral (F : I → MvPolynomial I K) (i : I) :
    IsIntegral K (algebraMap (residualQuotient F) (regularLocalization F)
      (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  letI := regular_localization_finite F
  exact IsIntegral.of_finite K _



omit [Fintype I] [DecidableEq I] in
/-- Coordinate polynomial evaluation commutes with every K-algebra map. -/
theorem map_coordinatePolynomial {B : Type*} [CommRing B] [Algebra K B]
    (f : MvPolynomial I K →ₐ[K] B) (P : Polynomial K) (i : I) :
    f (coordinatePolynomial P i) = Polynomial.aeval (f (MvPolynomial.X i)) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [coordinatePolynomial,Polynomial.map_add,Polynomial.eval₂_add,map_add] using congrArg₂ (·+·) hP hQ
  | monomial n c => simp [coordinatePolynomial,Polynomial.eval₂_monomial]

/-- A monic coordinate eliminant and a Jacobian saturation power are
CONSTRUCTED for every finite square polynomial system over a field.
The ideal membership is a genuine polynomial certificate, not a root-count
or finite-fiber premise. -/
theorem exists_saturated_monic_coordinate_relation (F : I → MvPolynomial I K) (i : I) :
    ∃ P : Polynomial K, P.Monic ∧ ∃ n : ℕ,
      determinantPolynomial F ^ n * coordinatePolynomial P i ∈ Ideal.span (Set.range F) := by
  obtain ⟨P,hP,hroot⟩ := regular_localization_coordinate_isIntegral F i
  let f : MvPolynomial I K →ₐ[K] regularLocalization F :=
    (IsScalarTower.toAlgHom K (residualQuotient F) (regularLocalization F)).comp
      (Ideal.Quotient.mkₐ K (Ideal.span (Set.range F)))
  have hz : algebraMap (residualQuotient F) (regularLocalization F)
      (Ideal.Quotient.mk _ (coordinatePolynomial P i)) = 0 := by
    change f (coordinatePolynomial P i)=0
    rw [map_coordinatePolynomial]
    exact hroot
  obtain ⟨⟨_,n,rfl⟩,hn⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (residualDeterminant F)) (regularLocalization F)
    (Ideal.Quotient.mk _ (coordinatePolynomial P i))).mp hz
  refine ⟨P,hP,n,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa only [map_mul,map_pow,residualDeterminant] using hn

end GenericJacobian

section CoefficientLocalization
open MvPolynomial
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Formal partials and their determinant commute with coefficient maps. -/
theorem determinantPolynomial_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (F : I → MvPolynomial I A) :
    determinantPolynomial (fun j => MvPolynomial.map f (F j)) =
      MvPolynomial.map f (determinantPolynomial F) := by
  unfold determinantPolynomial
  simp_rw [MvPolynomial.pderiv_map]
  let g : MvPolynomial I A →+* MvPolynomial I B := MvPolynomial.map f
  exact (RingHom.map_det g (fun i j => MvPolynomial.pderiv i (F j))).symm

omit [Fintype I] [DecidableEq I] in
/-- Scalar polynomial relations commute with the original coefficient map. -/
theorem coordinatePolynomial_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (P : Polynomial A) (i : I) :
    MvPolynomial.map f (coordinatePolynomial P i) = coordinatePolynomial (P.map f) i := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [coordinatePolynomial,Polynomial.map_add,Polynomial.eval₂_add,map_add] using congrArg₂ (·+·) hP hQ
  | monomial n c => simp [coordinatePolynomial,Polynomial.eval₂_monomial]

variable {A : Type*} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Clearing coefficient denominators in the generic regular algebra and
removing coefficient content constructs a PRIMITIVE coordinate relation over
the ORIGINAL coefficient ring. Nonzero scalar and Jacobian saturations are
explicit; no finite-fiber or preconstructed eliminant is assumed. -/
theorem exists_primitive_saturated_coordinate_relation
    (F : I → MvPolynomial I A) (i : I) :
    ∃ P : Polynomial A, P.IsPrimitive ∧ ∃ d : A, d ≠ 0 ∧ ∃ n : ℕ,
      MvPolynomial.C d * determinantPolynomial F ^ n * coordinatePolynomial P i ∈
        Ideal.span (Set.range F) := by
  let f : A →+* FractionRing A := algebraMap A (FractionRing A)
  let FK := fun j => MvPolynomial.map f (F j)
  obtain ⟨p,hp,n,hn⟩ := exists_saturated_monic_coordinate_relation FK i
  let q := IsLocalization.integerNormalization (nonZeroDivisors A) p
  have hq : q ≠ 0 := by
    exact fun h => hp.ne_zero ((IsLocalization.integerNormalization_eq_zero_iff
      (le_refl (nonZeroDivisors A)) p).mp h)
  obtain ⟨b,hb,hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
  have hqmap : q.map f = Polynomial.C (f b)*p := by
    rw [hbq,← IsScalarTower.algebraMap_smul (FractionRing A) b p,Polynomial.smul_eq_C_mul]
  have hqmem : determinantPolynomial FK ^ n * coordinatePolynomial (q.map f) i ∈
      Ideal.span (Set.range FK) := by
    rw [hqmap]
    have h := (Ideal.span (Set.range FK)).mul_mem_left (MvPolynomial.C (f b)) hn
    convert h using 1
    simp only [coordinatePolynomial,Polynomial.eval₂_mul,Polynomial.eval₂_C]
    ring
  let M := (nonZeroDivisors A).map (MvPolynomial.C : A →+* MvPolynomial I A)
  let J := Ideal.span (Set.range F)
  have hJI : Ideal.map (algebraMap (MvPolynomial I A) (MvPolynomial I (FractionRing A))) J =
      Ideal.span (Set.range FK) := by
    rw [Ideal.map_span,← Set.range_comp]
    rfl
  have hmap : algebraMap (MvPolynomial I A) (MvPolynomial I (FractionRing A))
      (determinantPolynomial F ^ n * coordinatePolynomial q i) ∈
      Ideal.map (algebraMap (MvPolynomial I A) (MvPolynomial I (FractionRing A))) J := by
    rw [hJI]
    change MvPolynomial.map f (determinantPolynomial F ^ n * coordinatePolynomial q i) ∈ _
    rw [map_mul,map_pow,← determinantPolynomial_map,coordinatePolynomial_map]
    exact hqmem
  obtain ⟨a,ha,hamem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M
    (MvPolynomial I (FractionRing A)) J
    (determinantPolynomial F ^ n * coordinatePolynomial q i)).mp hmap
  obtain ⟨d,hd,rfl⟩ := ha
  refine ⟨q.primPart,q.isPrimitive_primPart,d*q.content,
    mul_ne_zero (nonZeroDivisors.ne_zero hd) (fun hz => hq (Polynomial.content_eq_zero_iff.mp hz)),n,?_⟩
  rw [q.eq_C_content_mul_primPart] at hamem
  convert hamem using 1
  simp only [coordinatePolynomial,Polynomial.eval₂_mul,Polynomial.eval₂_C,map_mul]
  ring

end CoefficientLocalization

/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.map_ne_zero_of_contentIdeal_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.map_ne_zero_of_contentIdeal_eq_top
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.primitive_specialization_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.primitive_specialization_ne_zero
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.finite_of_unramified_finite_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.finite_of_unramified_finite_type
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.finite_of_standard_smooth_dimension_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.finite_of_standard_smooth_dimension_zero
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.augmented_jacobian_determinant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.augmented_jacobian_determinant
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.regular_quotient_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.regular_quotient_finite
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.regular_quotient_coordinate_isIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.regular_quotient_coordinate_isIntegral
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.residualPresentation_jacobian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.residualPresentation_jacobian
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.regular_localization_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.regular_localization_finite
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.regular_localization_coordinate_isIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.regular_localization_coordinate_isIntegral

/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.map_coordinatePolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.map_coordinatePolynomial
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.exists_saturated_monic_coordinate_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.exists_saturated_monic_coordinate_relation

/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.determinantPolynomial_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.determinantPolynomial_map
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.coordinatePolynomial_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.coordinatePolynomial_map
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.exists_primitive_saturated_coordinate_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.exists_primitive_saturated_coordinate_relation

open Set Filter Topology

/-- Nonzero polynomial scalar factors can be cancelled along a continuous
prefix even AT their finitely many zeros. No analyticity or supplied dense
set is needed, including at the left endpoint zero. -/
theorem continuous_zero_of_polynomial_product_on_Ico
    (d : Polynomial ℝ) (hd : d ≠ 0) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Ico a b))
    (hprod : ∀ t ∈ Ico a b, d.eval t * f t=0) :
    ∀ t ∈ Ico a b, f t=0 := by
  intro t ht
  by_contra hft
  have he := (hf t ht).tendsto.eventually_ne hft
  obtain ⟨e,hepos,he⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp he)
  let c := min b (t+e)
  have htc : t<c := lt_min ht.2 (by linarith)
  have hzero : Ioo t c ⊆ {x : ℝ | d.IsRoot x} := by
    intro x hx
    have hxs : x ∈ Ico a b := ⟨ht.1.trans hx.1.le,hx.2.trans_le (min_le_left _ _)⟩
    have hdist : dist x t < e := by
      rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hx.1)]
      have : x<t+e := hx.2.trans_le (min_le_right _ _)
      linarith
    exact (mul_eq_zero.mp (hprod x hxs)).resolve_right (he hdist hxs)
  exact (Set.Ioo_infinite htc).not_finite ((Polynomial.finite_setOf_isRoot hd).subset hzero)

/-- A bivariate coordinate polynomial is genuinely continuous in coupling
and amplitude, including every singular specialization of its leading term. -/
theorem continuous_specialized_eval (P : Polynomial (Polynomial ℝ)) :
    Continuous (fun x : ℝ × ℝ => (P.map (Polynomial.evalRingHom x.1)).eval x.2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      funext x
      simp only [Polynomial.map_add,Polynomial.eval_add,Pi.add_apply]
  | monomial n c =>
      have h : Continuous (fun x : ℝ × ℝ => c.eval x.1 * x.2 ^ n) :=
        (c.continuous.comp continuous_fst).mul (continuous_snd.pow n)
      convert h using 1
      funext x
      simp

section RegularRealPrefixes
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- Coordinate relations commute with arbitrary coefficient specializations. -/
theorem eval₂_coordinatePolynomial {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : I → B) (P : Polynomial A) (i : I) :
    MvPolynomial.eval₂Hom f x (coordinatePolynomial P i) = (P.map f).eval (x i) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [coordinatePolynomial,Polynomial.eval₂_add,map_add,
        Polynomial.map_add,Polynomial.eval_add] using congrArg₂ (·+·) hP hQ
  | monomial n c => simp [coordinatePolynomial,Polynomial.eval₂_monomial]

/-- At a regular root the constructed saturated identity gives a genuine
coordinate relation times ONLY its nonzero coupling polynomial. -/
theorem regular_root_polynomial_product_zero
    (F : I → MvPolynomial I (Polynomial ℝ)) (P : Polynomial (Polynomial ℝ))
    (d : Polynomial ℝ) (n : ℕ) (i : I)
    (hmem : MvPolynomial.C d * determinantPolynomial F ^ n * coordinatePolynomial P i ∈
      Ideal.span (Set.range F)) (t : ℝ) (x : I → ℝ)
    (hroot : ∀ j, MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x (F j)=0)
    (hreg : MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x (determinantPolynomial F) ≠ 0) :
    d.eval t * (P.map (Polynomial.evalRingHom t)).eval (x i)=0 := by
  let e := MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x
  have hk : Ideal.span (Set.range F) ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro Q ⟨j,rfl⟩
    exact hroot j
  have hz : e (MvPolynomial.C d * determinantPolynomial F ^ n * coordinatePolynomial P i)=0 := hk hmem
  simp only [map_mul,map_pow] at hz
  have hcoord : e (coordinatePolynomial P i) = (P.map (Polynomial.evalRingHom t)).eval (x i) :=
    eval₂_coordinatePolynomial _ _ _ _
  rw [hcoord] at hz
  have hd : e (MvPolynomial.C d)=d.eval t := by simp [e]
  rw [hd] at hz
  have hg : e (determinantPolynomial F) ≠ 0 := hreg
  have h : e (determinantPolynomial F)^n *
      (d.eval t * (P.map (Polynomial.evalRingHom t)).eval (x i))=0 := by
    convert hz using 1
    ring
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero n hg)

/-- Primitive coordinate relations are CONSTRUCTED for any continuous
regular root prefix of a finite square polynomial system. There is no
supplied algebraicity, coefficient relation, finite fiber or endpoint limit. -/
theorem exists_primitive_relations_on_regular_prefix
    (F : I → MvPolynomial I (Polynomial ℝ)) (p : ℝ → I → ℝ) (b : ℝ)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, ∀ j, MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (p t) (F j)=0)
    (hreg : ∀ t ∈ Ico 0 b,
      MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (p t) (determinantPolynomial F) ≠ 0) :
    ∃ P : I → Polynomial (Polynomial ℝ), (∀ i, (P i).IsPrimitive) ∧
      ∀ t ∈ Ico 0 b, ∀ i, ((P i).map (Polynomial.evalRingHom t)).eval (p t i)=0 := by
  choose P hP d hd n hn using (fun i : I => exists_primitive_saturated_coordinate_relation F i)
  refine ⟨P,hP,?_⟩
  have hrel (i : I) : ∀ t ∈ Ico 0 b, ((P i).map (Polynomial.evalRingHom t)).eval (p t i)=0 := by
    apply continuous_zero_of_polynomial_product_on_Ico (d i) (hd i) _ 0 b
    · exact (continuous_specialized_eval (P i)).comp_continuousOn
        (continuousOn_id.prodMk ((continuous_apply i).comp_continuousOn hp))
    · intro t ht
      exact regular_root_polynomial_product_zero F (P i) (d i) (n i) i (hn i) t (p t)
        (hroot t ht) (hreg t ht)
  exact fun t ht i => hrel i t ht

omit [DecidableEq I] in
/-- Every finite endpoint specialization of the constructed primitive
coordinate family has a finite candidate fiber, even when the original
residual's endpoint fiber is nonisolated or positive-dimensional. -/
theorem primitive_candidate_fiber_finite
    (P : I → Polynomial (Polynomial ℝ)) (hP : ∀ i, (P i).IsPrimitive) (b : ℝ) :
    {x : I → ℝ | ∀ i, ((P i).map (Polynomial.evalRingHom b)).eval (x i)=0}.Finite := by
  classical
  let S := {x : I → ℝ | ∀ i, ((P i).map (Polynomial.evalRingHom b)).eval (x i)=0}
  let A := fun i : I => {x : ℝ // Polynomial.IsRoot ((P i).map (Polynomial.evalRingHom b)) x}
  letI : ∀ i : I, Fintype (A i) := fun i =>
    (Polynomial.finite_setOf_isRoot (primitive_specialization_ne_zero (P i) (hP i) b)).fintype
  let f : S → ∀ i : I, A i := fun x i => ⟨x.val i,x.property i⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  letI : Finite S := Finite.of_injective f hf
  exact Set.toFinite S

end RegularRealPrefixes

/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.continuous_zero_of_polynomial_product_on_Ico' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.continuous_zero_of_polynomial_product_on_Ico
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.continuous_specialized_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.continuous_specialized_eval

/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.eval₂_coordinatePolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.eval₂_coordinatePolynomial
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.regular_root_polynomial_product_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.regular_root_polynomial_product_zero
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.exists_primitive_relations_on_regular_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.exists_primitive_relations_on_regular_prefix
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.primitive_candidate_fiber_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.primitive_candidate_fiber_finite

section CouplingRepacking
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Coupling is moved into the polynomial coefficient ring, while all
original amplitude coordinates remain independent variables. -/
def couplingCoefficientMap :
    MvPolynomial (Option I) ℝ →+* MvPolynomial I (Polynomial ℝ) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Polynomial.C)
    (fun u => u.elim (MvPolynomial.C Polynomial.X) MvPolynomial.X)

/-- Literal specialization used by the original BH polynomial dictionary. -/
def couplingSpecialize (t : ℝ) : MvPolynomial (Option I) ℝ →+* MvPolynomial I ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => u.elim (MvPolynomial.C t) MvPolynomial.X)

omit [Fintype I] [DecidableEq I] in
/-- Moving coupling into coefficients and then specializing is EXACTLY the
original specialization map, including all real coupling values. -/
theorem couplingCoefficientMap_specialize (t : ℝ) (P : MvPolynomial (Option I) ℝ) :
    MvPolynomial.map (Polynomial.evalRingHom t) (couplingCoefficientMap P) = couplingSpecialize t P := by
  have hh : (MvPolynomial.map (Polynomial.evalRingHom t)).comp (couplingCoefficientMap (I := I)) = couplingSpecialize t := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [couplingCoefficientMap,couplingSpecialize]
    · intro u
      cases u <;> simp [couplingCoefficientMap,couplingSpecialize]
  exact RingHom.congr_fun hh P

omit [Fintype I] [DecidableEq I] in
/-- Original point evaluation is recovered after coupling specialization. -/
theorem eval_couplingSpecialize (t : ℝ) (x : I → ℝ) (P : MvPolynomial (Option I) ℝ) :
    MvPolynomial.eval x (couplingSpecialize t P) =
      MvPolynomial.eval (fun u : Option I => u.elim t x) P := by
  have hh : (MvPolynomial.eval x).comp (couplingSpecialize t) =
      MvPolynomial.eval (fun u : Option I => u.elim t x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [couplingSpecialize]
    · intro u
      cases u <;> simp [couplingSpecialize]
  exact RingHom.congr_fun hh P

omit [Fintype I] [DecidableEq I] in
/-- Evaluating coefficient polynomials first is exactly generalized eval2. -/
theorem eval₂Hom_eq_eval_map (t : ℝ) (x : I → ℝ) (Q : MvPolynomial I (Polynomial ℝ)) :
    MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x Q =
      MvPolynomial.eval x (MvPolynomial.map (Polynomial.evalRingHom t) Q) := by
  have hh : MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x =
      (MvPolynomial.eval x).comp (MvPolynomial.map (Polynomial.evalRingHom t)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro u
      simp
  exact RingHom.congr_fun hh Q

omit [Fintype I] [DecidableEq I] in
/-- The repacked residual has EXACTLY the original roots, without any
algebraic approximation, denominator exclusion or physical sign premise. -/
theorem eval₂_couplingCoefficientMap (t : ℝ) (x : I → ℝ) (P : MvPolynomial (Option I) ℝ) :
    MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x (couplingCoefficientMap P) =
      MvPolynomial.eval (fun u : Option I => u.elim t x) P := by
  rw [eval₂Hom_eq_eval_map,couplingCoefficientMap_specialize,eval_couplingSpecialize]

/-- The repacked formal Jacobian determinant is exactly the original
specialized amplitude Jacobian determinant, with the standard equation/variable
row convention. No derivative nonsingularity is assumed. -/
theorem eval₂_couplingCoefficientMap_jacobian
    (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (x : I → ℝ) :
    MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x
      (determinantPolynomial (fun i => couplingCoefficientMap (F i))) =
      Matrix.det (fun i j => MvPolynomial.eval x
        (MvPolynomial.pderiv j (couplingSpecialize t (F i)))) := by
  rw [eval₂Hom_eq_eval_map,← determinantPolynomial_map]
  have hm : (fun i => MvPolynomial.map (Polynomial.evalRingHom t) (couplingCoefficientMap (F i))) =
      fun i => couplingSpecialize t (F i) := by
    funext i
    exact couplingCoefficientMap_specialize t (F i)
  rw [hm]
  unfold determinantPolynomial
  rw [RingHom.map_det]
  exact Matrix.det_transpose _

end CouplingRepacking

/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.couplingCoefficientMap_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.couplingCoefficientMap_specialize
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.eval_couplingSpecialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.eval_couplingSpecialize
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.eval₂Hom_eq_eval_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.eval₂Hom_eq_eval_map
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.eval₂_couplingCoefficientMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.eval₂_couplingCoefficientMap
/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.eval₂_couplingCoefficientMap_jacobian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.eval₂_couplingCoefficientMap_jacobian



/-- Every continuous regular root prefix of a finite square polynomial
system has its full finite left limit from ANY one approaching finite cluster.
The original endpoint root fiber may be singular, nonisolated or infinite.
No eliminant, finite-fiber premise, endpoint value or full limit is assumed. -/
theorem regular_polynomial_prefix_cluster_has_limit
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → MvPolynomial I (Polynomial ℝ)) (p : ℝ → I → ℝ) (b : ℝ) (hb : 0<b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, ∀ j, MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (p t) (F j)=0)
    (hreg : ∀ t ∈ Ico 0 b,
      MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) (p t) (determinantPolynomial F) ≠ 0)
    (a : I → ℝ) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Ico 0 b)
    (ht : Tendsto u atTop (𝓝 b)) (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a)) :
    Tendsto p (𝓝[<] b) (𝓝 a) := by
  obtain ⟨P,hP,hrel⟩ := exists_primitive_relations_on_regular_prefix F p b hp hroot hreg
  let R : ℝ × (I → ℝ) → I → ℝ :=
    fun x i => ((P i).map (Polynomial.evalRingHom x.1)).eval (x.2 i)
  have hR : Continuous R := by
    apply continuous_pi_iff.mpr
    intro i
    exact (continuous_specialized_eval (P i)).comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hr : ∀ t ∈ Ico 0 b, R (t,p t)=0 := by
    intro t ht
    funext i
    exact hrel t ht i
  have hfinite : {x : I → ℝ | R (b,x)=0}.Finite := by
    apply (primitive_candidate_fiber_finite P hP b).subset
    intro x hx i
    exact congrFun hx i
  exact FMSA.Convergence.IsolatedEndpointLimits.finite_fiber_cluster_has_limit R hR p b hb hp hr a u hu ht ha hfinite

/-- info: 'FMSA.Convergence.SelectedBranchAlgebraicity.regular_polynomial_prefix_cluster_has_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SelectedBranchAlgebraicity.regular_polynomial_prefix_cluster_has_limit

end FMSA.Convergence.SelectedBranchAlgebraicity
