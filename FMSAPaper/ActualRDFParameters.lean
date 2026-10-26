import FMSAPaper.VolterraResolvent
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearRDF
import LeanCode.YukawaOZMix.MSAMultiTailMixtureBasis
import Mathlib.Data.Matrix.Basis

/-! Smooth dependence of the constructed RDF on the actual BH amplitudes.
The compact Volterra inverse is unconditional; global decay is a separate issue. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped ContDiff BigOperators

namespace FMSA.Paper.ActualRDFParameters
open ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
open VolterraResolvent
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Fixed continuous dictionary for the recentered Baxter kernel. -/
def recenteredBasis (z : T → ℝ) (sigma : Fin N → ℝ) (b : BasisIndex T)
    (i : Fin N) (r : ℝ) : ℝ :=
  basisQp b * (min r (sigma i) - sigma i) +
    basisA b / 2 * (min r (sigma i) - sigma i)^2 +
    basisW b * exp (-basisRate z b * r) +
    basisC b * exp (-basisRate z b * (max r (sigma i) - sigma i))

@[fun_prop]
theorem recenteredBasis_continuous (z : T → ℝ) (sigma : Fin N → ℝ)
    (b : BasisIndex T) (i : Fin N) : Continuous (recenteredBasis z sigma b i) := by
  unfold recenteredBasis
  fun_prop

theorem recentered_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    nonlinearRecenteredQ z rho sigma p.1 p.2 i j r =
      ∑ b : BasisIndex T, bhCoefficient z rho sigma p i j b * recenteredBasis z sigma b i r := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, bhCoefficient, coefficient,
    recenteredBasis, basisRate, basisA, basisQp, basisW, basisC]
  simp only [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    if_true, if_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    nonlinearRecenteredQ, Finset.sum_add_distrib]
  simp only [mul_comm]
  ring


/-- Fixed dictionary for the affine/exponential G source. -/
def gSourceBasis (z : T → ℝ) (b : BasisIndex T) (r : ℝ) : ℝ :=
  (basisA b * r + basisQp b +
    basisRate z b * basisC b * exp (-basisRate z b * r)) / (2 * π)

@[fun_prop]
theorem gSourceBasis_continuous (z : T → ℝ) (b : BasisIndex T) :
    Continuous (gSourceBasis z b) := by unfold gSourceBasis; fun_prop

theorem gSource_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    nonlinearGSource z rho sigma p.1 p.2 r i j =
      ∑ b : BasisIndex T, bhCoefficient z rho sigma p i j b * gSourceBasis z b r := by
  change (_ + _ + _) / (2 * π) = _
  simp_rw [gSourceBasis, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, bhCoefficient, coefficient,
    basisRate, basisA, basisQp, basisC]
  simp [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  <;> ring


/-- A separate matrix type keeps the operator norm confined to the Volterra
codomain, preserving the existing amplitude-space norm and its derivatives. -/
def BaxterMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℝ

@[instance_reducible]
instance : NormedRing (BaxterMatrix N) := Matrix.linftyOpNormedRing
@[instance_reducible]
instance : NormedAlgebra ℝ (BaxterMatrix N) := Matrix.linftyOpNormedAlgebra
instance : CompleteSpace (BaxterMatrix N) := Matrix.instCompleteSpace _ _ _
def BaxterMatrix.toMatrix (M : BaxterMatrix N) : Matrix (Fin N) (Fin N) ℝ := M

def BaxterMatrix.ofMatrix (M : Matrix (Fin N) (Fin N) ℝ) : BaxterMatrix N := M

@[simp]
theorem BaxterMatrix.toMatrix_ofMatrix (M : Matrix (Fin N) (Fin N) ℝ) :
    (BaxterMatrix.ofMatrix M).toMatrix = M := rfl

@[ext]
theorem BaxterMatrix.ext {A B : BaxterMatrix N} (h : ∀ i j, A.toMatrix i j = B.toMatrix i j) : A = B :=
  funext fun i => funext fun j => h i j

/-- Entry extraction is bounded for the matrix operator norm. -/
def matrixEntry (i j : Fin N) : BaxterMatrix N →L[ℝ] ℝ where
  toFun M := M.toMatrix i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

@[simp]
theorem matrixEntry_ofMatrix (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixEntry i j (BaxterMatrix.ofMatrix M) = M i j := rfl

theorem matrixEntry_integral_mul (Q U : ℝ → BaxterMatrix N) (hQ : Continuous Q)
    (hU : Continuous U) (a b : ℝ) (i j : Fin N) :
    matrixEntry i j (∫ t in a..b, Q t * U t : BaxterMatrix N) =
      ∑ k, ∫ t in a..b, matrixEntry i k (Q t) * matrixEntry k j (U t) := by
  have hi : IntervalIntegrable (fun t => (Q t * U t : BaxterMatrix N)) volume a b :=
    (hQ.mul hU).intervalIntegrable a b
  calc
    matrixEntry i j (∫ t in a..b, Q t * U t : BaxterMatrix N) =
        ∫ t in a..b, matrixEntry i j (Q t * U t) :=
      ((matrixEntry i j).intervalIntegral_comp_comm hi).symm
    _ = _ := ?_

  have hm (A B : BaxterMatrix N) : matrixEntry i j (A * B) =
      ∑ k, matrixEntry i k A * matrixEntry k j B := rfl
  simp_rw [hm]
  rw [intervalIntegral.integral_finsetSum]
  intro k _
  exact (((matrixEntry i k).continuous.comp hQ).mul
    ((matrixEntry k j).continuous.comp hU)).intervalIntegrable a b

section MatrixNorm
variable {R : ℝ}

/-- A compact matrix dictionary with every amplitude confined to scalar coefficients. -/
def kernelBasis (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (b : BasisIndex T) : C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  VolterraResolvent.restrict hR (fun r => BaxterMatrix.ofMatrix (Matrix.single j i (rho i * recenteredBasis z sigma b i r))) (by
    change Continuous (fun r : ℝ => Matrix.single j i (rho i * recenteredBasis z sigma b i r))
    apply continuous_matrix
    intro a c
    simp only [Matrix.single_apply]
    split_ifs <;> fun_prop)

def gBasis (hR : 0 ≤ R) (z : T → ℝ) (i j : Fin N) (b : BasisIndex T) :
    C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  VolterraResolvent.restrict hR (fun r => BaxterMatrix.ofMatrix (Matrix.single j i (gSourceBasis z b r))) (by
    change Continuous (fun r : ℝ => Matrix.single j i (gSourceBasis z b r))
    apply continuous_matrix
    intro a c
    simp only [Matrix.single_apply]
    split_ifs <;> fun_prop)

theorem kernelBasis_entry (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (b : BasisIndex T) (r : Icc (0 : ℝ) R) (a c : Fin N) :
    matrixEntry a c (kernelBasis hR z rho sigma i j b r) =
      if j = a ∧ i = c then rho i * recenteredBasis z sigma b i r else 0 := rfl

theorem gBasis_entry (hR : 0 ≤ R) (z : T → ℝ) (i j : Fin N)
    (b : BasisIndex T) (r : Icc (0 : ℝ) R) (a c : Fin N) :
    matrixEntry a c (gBasis hR z i j b r) =
      if j = a ∧ i = c then gSourceBasis z b r else 0 := rfl

def kernelBundle (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) : C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  ∑ i, ∑ j, ∑ b : BasisIndex T, bhCoefficient z rho sigma p i j b • kernelBasis hR z rho sigma i j b

def gBundle (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) : C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  ∑ i, ∑ j, ∑ b : BasisIndex T, bhCoefficient z rho sigma p i j b • gBasis hR z i j b

theorem kernelBundle_contDiff (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    ContDiff ℝ ∞ (kernelBundle hR z rho sigma) := by
  unfold kernelBundle
  fun_prop

theorem gBundle_contDiff (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    ContDiff ℝ ∞ (gBundle hR z rho sigma) := by
  unfold gBundle
  fun_prop

theorem kernelBundle_apply (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) :
    kernelBundle hR z rho sigma p r = BaxterMatrix.ofMatrix (nonlinearCausalKernel z rho sigma p.1 p.2 r).transpose := by
  classical
  apply BaxterMatrix.ext
  intro a c
  simp only [BaxterMatrix.toMatrix_ofMatrix]
  change matrixEntry a c (kernelBundle hR z rho sigma p r) = _
  simp only [kernelBundle, ContinuousMap.sum_apply, ContinuousMap.smul_apply, map_sum, map_smul]
  simp only [kernelBasis_entry, smul_eq_mul, Matrix.transpose_apply, nonlinearCausalKernel, Matrix.of_apply]
  rw [recentered_eq_basis]
  simp [ite_and, mul_ite, Finset.mul_sum, mul_add, mul_comm, mul_left_comm, mul_assoc]

theorem gBundle_apply (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) :
    gBundle hR z rho sigma p r = BaxterMatrix.ofMatrix (nonlinearGSource z rho sigma p.1 p.2 r).transpose := by
  classical
  apply BaxterMatrix.ext
  intro a c
  simp only [BaxterMatrix.toMatrix_ofMatrix]
  change matrixEntry a c (gBundle hR z rho sigma p r) = _
  simp only [gBundle, ContinuousMap.sum_apply, ContinuousMap.smul_apply, map_sum, map_smul]
  simp only [gBasis_entry, smul_eq_mul, Matrix.transpose_apply]
  rw [gSource_eq_basis]
  simp [ite_and, mul_ite]

/-- The compact solution of the actual G-renewal equation. -/
def causalGBundle (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) : C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  solve hR (kernelBundle hR z rho sigma p) (gBundle hR z rho sigma p)

theorem causalGBundle_contDiff (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    ContDiff ℝ ∞ (causalGBundle hR z rho sigma) := by
  exact solve_contDiff_parametrized hR (kernelBundle hR z rho sigma) (gBundle hR z rho sigma)
    (kernelBundle_contDiff hR z rho sigma) (gBundle_contDiff hR z rho sigma)

set_option maxHeartbeats 800000 in
/-- Identification uses the proved actual G renewal, rather than assuming
that the RDF is a solution or a differentiable family. -/
theorem causalGBundle_apply (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) :
    causalGBundle hR z rho sigma p r = BaxterMatrix.ofMatrix (nonlinearCausalG z rho sigma p.1 p.2 r).transpose := by
  let u : C(Icc (0 : ℝ) R, BaxterMatrix N) := VolterraResolvent.restrict hR
    (fun t => BaxterMatrix.ofMatrix (nonlinearCausalG z rho sigma p.1 p.2 t).transpose)
    (continuous_matrix (fun i j => (nonlinearCausalG_continuous z rho sigma p.1 p.2).matrix_elem j i))
  have hu : residualOperator hR (kernelBundle hR z rho sigma p) u = gBundle hR z rho sigma p := by
    ext t i j
    change matrixEntry i j (u t) - matrixEntry i j (kernelOperator hR (kernelBundle hR z rho sigma p) u t) = _
    rw [kernelOperator_apply, gBundle_apply]
    have he : (∫ s in (0 : ℝ)..(t : ℝ),
        Set.IccExtend hR (kernelBundle hR z rho sigma p) ((t : ℝ) - s) *
          Set.IccExtend hR u s : BaxterMatrix N) =
        (∫ s in (0 : ℝ)..(t : ℝ),
          BaxterMatrix.ofMatrix (nonlinearCausalKernel z rho sigma p.1 p.2 ((t : ℝ) - s)).transpose *
            BaxterMatrix.ofMatrix (nonlinearCausalG z rho sigma p.1 p.2 s).transpose : BaxterMatrix N) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.2.1] at hs
      dsimp only
      rw [Set.IccExtend_of_mem hR _
          (show (t : ℝ) - s ∈ Icc (0 : ℝ) R from by constructor <;> linarith [hs.1, hs.2, t.2.2]),
        Set.IccExtend_of_mem hR _
          (show s ∈ Icc (0 : ℝ) R from ⟨hs.1, hs.2.trans t.2.2⟩), kernelBundle_apply]
      rfl
    rw [he, matrixEntry_integral_mul]
    · have h := nonlinearCausalG_renewal z rho sigma p.1 p.2 j i t t.2.1
      dsimp [u, VolterraResolvent.restrict]
      simpa only [matrixEntry_ofMatrix, Matrix.transpose_apply, mul_comm]
        using (sub_eq_iff_eq_add.mpr h)
    · exact (nonlinearCausalKernelTranspose_continuous z rho sigma p.1 p.2).comp
        (continuous_const.sub continuous_id)
    · exact continuous_matrix (fun i j =>
        (nonlinearCausalG_continuous z rho sigma p.1 p.2).matrix_elem j i)
  have hi := ContinuousLinearMap.isUnit_iff_bijective.mp
    (residualOperator_isUnit hR (kernelBundle hR z rho sigma p))
  have he : causalGBundle hR z rho sigma p = u := hi.1
    ((solve_spec hR _ _).trans hu.symm)
  exact congrArg (fun f : C(Icc (0 : ℝ) R, BaxterMatrix N) => f r) he

end MatrixNorm

/-- Actual G is smooth in amplitudes at each fixed nonnegative distance. -/
@[fun_prop]
theorem causalG_contDiff_nonneg (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N =>
      nonlinearCausalG z rho sigma p.1 p.2 r i j) := by
  let x : Icc (0 : ℝ) r := ⟨r, hr, le_rfl⟩
  let L : C(Icc (0 : ℝ) r, BaxterMatrix N) →L[ℝ] ℝ :=
    (matrixEntry j i).comp (ContinuousMap.evalCLM ℝ x)
  have h := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) r, BaxterMatrix N)) (F := ℝ) L).comp
      (causalGBundle_contDiff hr z rho sigma)
  convert h using 1
  funext p
  exact (congrArg (fun M : BaxterMatrix N => matrixEntry j i M) (causalGBundle_apply hr z rho sigma p x)).symm

/-- The extension below zero used by the existing construction is fixed. -/
theorem rdfExcess_eq_max (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (r : ℝ) :
    nonlinearRDFExcess z rho sigma p.1 p.2 r =
      nonlinearRDFExcess z rho sigma p.1 p.2 (max 0 r) := by
  unfold nonlinearRDFExcess FMSA.MixtureOzStar.matBaxterPsiOuterFun
  rw [max_eq_right (le_max_left (0 : ℝ) r)]

/-- Smoothness is derived for the actual constructed RDF excess, at all
amplitudes and fixed r, without a BH root or a weighted smallness premise. -/
@[fun_prop]
theorem rdfExcess_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N =>
      nonlinearRDFExcess z rho sigma p.1 p.2 r i j) := by
  have h := ((causalG_contDiff_nonneg z rho sigma i j (max 0 r) (le_max_left _ _)).sub
    (contDiff_const (c := max 0 r))).sub (contDiff_const (c := edgeHi sigma i j))
  convert h using 1
  funext p
  rw [rdfExcess_eq_max z rho sigma p r]
  simp only [nonlinearCausalG, Matrix.of_apply]
  ring

@[fun_prop]
theorem causalG_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N =>
      nonlinearCausalG z rho sigma p.1 p.2 r i j) := by
  unfold nonlinearCausalG
  exact ((rdfExcess_contDiff z rho sigma i j r).add contDiff_const).add contDiff_const

@[fun_prop]
theorem rdfMoment_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N =>
      nonlinearRDFMoment z rho sigma p.1 p.2 i j r) := by
  unfold nonlinearRDFMoment causalShift causalFull
  simp only [Set.indicator_apply]
  split_ifs <;> fun_prop

/-- The previously totalized fderiv of actual h is now justified by C-infinity. -/
@[fun_prop]
theorem h_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N =>
      nonlinearH z rho sigma p.1 p.2 i j r) :=
  (rdfMoment_contDiff z rho sigma i j r).div_const r

@[fun_prop]
theorem g_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N =>
      nonlinearG z rho sigma p.1 p.2 i j r) := by
  unfold nonlinearG
  split_ifs
  · exact contDiff_const
  · exact (causalG_contDiff z rho sigma i j _).div_const r

theorem h_hasFDerivAt (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N => nonlinearH z rho sigma a.1 a.2 i j r)
      (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearH z rho sigma a.1 a.2 i j r) p) p :=
  ((h_contDiff z rho sigma i j r).differentiable (by simp) p).hasFDerivAt

end FMSA.Paper.ActualRDFParameters

/-- info: 'FMSA.Paper.ActualRDFParameters.recenteredBasis_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.recenteredBasis_continuous
/-- info: 'FMSA.Paper.ActualRDFParameters.recentered_eq_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.recentered_eq_basis
/-- info: 'FMSA.Paper.ActualRDFParameters.gSourceBasis_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.gSourceBasis_continuous
/-- info: 'FMSA.Paper.ActualRDFParameters.gSource_eq_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.gSource_eq_basis
/-- info: 'FMSA.Paper.ActualRDFParameters.BaxterMatrix.toMatrix_ofMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.BaxterMatrix.toMatrix_ofMatrix
/-- info: 'FMSA.Paper.ActualRDFParameters.BaxterMatrix.ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.BaxterMatrix.ext
/-- info: 'FMSA.Paper.ActualRDFParameters.matrixEntry_ofMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.matrixEntry_ofMatrix
/-- info: 'FMSA.Paper.ActualRDFParameters.matrixEntry_integral_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.matrixEntry_integral_mul
/-- info: 'FMSA.Paper.ActualRDFParameters.kernelBasis_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.kernelBasis_entry
/-- info: 'FMSA.Paper.ActualRDFParameters.gBasis_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.gBasis_entry
/-- info: 'FMSA.Paper.ActualRDFParameters.kernelBundle_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.kernelBundle_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.gBundle_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.gBundle_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.kernelBundle_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.kernelBundle_apply
/-- info: 'FMSA.Paper.ActualRDFParameters.gBundle_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.gBundle_apply
/-- info: 'FMSA.Paper.ActualRDFParameters.causalGBundle_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.causalGBundle_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.causalGBundle_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.causalGBundle_apply
/-- info: 'FMSA.Paper.ActualRDFParameters.causalG_contDiff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.causalG_contDiff_nonneg
/-- info: 'FMSA.Paper.ActualRDFParameters.rdfExcess_eq_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.rdfExcess_eq_max
/-- info: 'FMSA.Paper.ActualRDFParameters.rdfExcess_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.rdfExcess_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.causalG_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.causalG_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.rdfMoment_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.rdfMoment_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.h_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.h_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.g_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.g_contDiff
/-- info: 'FMSA.Paper.ActualRDFParameters.h_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRDFParameters.h_hasFDerivAt
