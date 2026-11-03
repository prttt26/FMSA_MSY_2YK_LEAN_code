import MSAConvergence.FiniteKernelLaplace

/-! Actual equal-density, equal-diameter binary BH equations in exchange
channels. Kernel exchange symmetry is explicit; it is not inferred from
numerical evidence or from a supplied amplitude bound. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.BinaryCanonicalChannels
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.ScalarKernelSource FMSA.Convergence.FiniteKernelLaplace
open FMSA.Convergence.CanonicalNeighborhood
variable {T : Type*} [Fintype T]

abbrev Amp (T : Type*) := TailMatrix T 2 × TailMatrix T 2

def density (r : ℝ) : Fin 2 → ℝ := fun _ => r
def diameter (a : ℝ) : Fin 2 → ℝ := fun _ => a

def coeff (z : T → ℝ) (r a : ℝ) (p : Amp T) (i j : Fin 2) : Coeff T :=
  r • bhCoefficient z (density r) (diameter a) p i j

def KernelExchange (z : T → ℝ) (r a : ℝ) (p : Amp T) : Prop :=
  coeff z r a p 1 1 = coeff z r a p 0 0 ∧ coeff z r a p 1 0 = coeff z r a p 0 1

def sgn (b : Bool) : ℝ := if b then -1 else 1

def rowMode (v : Fin 2 → ℝ) (b : Bool) : ℝ := v 0 + sgn b * v 1

def modeCoeff (z : T → ℝ) (r a : ℝ) (p : Amp T) (b : Bool) : Coeff T :=
  coeff z r a p 0 0 + sgn b • coeff z r a p 0 1

def factor (z : T → ℝ) (r a : ℝ) (p : Amp T) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1-rdfMatrixLaplace (nonlinearCausalKernel z (density r) (diameter a) p.1 p.2) s

def modeFactor (z : T → ℝ) (r a : ℝ) (p : Amp T) (b : Bool) (s : ℂ) : ℂ :=
  1-laplace z a (modeCoeff z r a p b) s

private theorem laplace_add (z : T → ℝ) (hz : ∀ u, 0 < z u) (a : ℝ)
    (c d : Coeff T) (s : ℂ) (hs : 0 ≤ s.re) :
    laplace z a (c+d) s = laplace z a c s+laplace z a d s := by
  simp only [laplace_eq_sum z hz a (c+d) s hs,laplace_eq_sum z hz a c s hs,
    laplace_eq_sum z hz a d s hs,Pi.add_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]

/-- Entrywise identification with the honest ORIGINAL causal factor. -/
theorem factor_entry (z : T → ℝ) (r a : ℝ) (p : Amp T) (s : ℂ) (i j : Fin 2) :
    factor z r a p s i j = (if i=j then 1 else 0)-laplace z a (coeff z r a p i j) s := by
  rw [factor,Matrix.sub_apply,Matrix.one_apply,← actual_kernel_laplace]
  rfl

theorem mode_factor_formula (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ)
    (p : Amp T) (b : Bool) (s : ℂ) (hs : 0 ≤ s.re) :
    modeFactor z r a p b s = 1-laplace z a (coeff z r a p 0 0) s-
      (sgn b : ℂ)*laplace z a (coeff z r a p 0 1) s := by
  rw [modeFactor,modeCoeff,laplace_add z hz a _ _ s hs,laplace_smul z hz a _ _ s hs]
  ring

/-- Exchange symmetry factorizes the TRUE determinant at every closed-right
frequency. Density and diameter values are fixed, not fitted eigenvalues. -/
theorem factor_det_modes (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ)
    (p : Amp T) (hp : KernelExchange z r a p) (s : ℂ) (hs : 0 ≤ s.re) :
    (factor z r a p s).det = modeFactor z r a p false s*modeFactor z r a p true s := by
  rcases hp with ⟨h11,h10⟩
  rw [Matrix.det_fin_two]
  simp [factor_entry,h11,h10,mode_factor_formula z hz r a p false s hs,
    mode_factor_formula z hz r a p true s hs,sgn]
  ring

/-- ORIGINAL mixture canonicity gives both scalar channels' zero-freeness;
no channel inverse or channel canonicity is assumed. -/
theorem mode_factor_ne_zero (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ)
    (p : Amp T) (he : KernelExchange z r a p)
    (hc : p ∈ canonicalAmplitudes z (density r) (diameter a)) (b : Bool)
    (s : ℂ) (hs : 0 ≤ s.re) : modeFactor z r a p b s ≠ 0 := by
  have hd : (factor z r a p s).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hc s hs))
  rw [factor_det_modes z hz r a p he s hs] at hd
  cases b
  · exact (mul_ne_zero_iff.mp hd).1
  · exact (mul_ne_zero_iff.mp hd).2

theorem rate_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ) (ha : 0 ≤ a)
    (p : Amp T) (u : T) (i j : Fin 2) :
    laplace z a (coeff z r a p i j) (z u : ℂ) =
      ((r*dressedQhat z (density r) (diameter a) p.1 p.2 (z u) i j : ℝ) : ℂ) := by
  change laplace z (diameter a i) (density r i • bhCoefficient z (density r) (diameter a) p i j) _ = _
  rw [actual_kernel_laplace,FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_root_dictionary
    z hz (density r) (diameter a) (fun _ => ha)]
  simp [Matrix.diagonal_mul,FMSA.Convergence.ActualBHAmplitudeRecovery.rootTransformSymbol,
    nonlinearRootRecenteredTransform,edgeLo,density,diameter]

private theorem first_equation (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ) (ha : 0 ≤ a)
    (K : TailMatrix T 2) (p : Amp T) (hr : IsRoot z (density r) (diameter a) K p.1 p.2)
    (u : T) (i j : Fin 2) :
    ∑ l, (p.1 u i l : ℂ)*((if l=j then 1 else 0)-laplace z a (coeff z r a p j l) (z u : ℂ)) =
      ((2*Real.pi*K u i j/z u : ℝ) : ℂ) := by
  simp only [rate_laplace z hz r a ha]
  have h := hr.1 u i j
  simp only [firstLHS,edgeLo,diameter,density,sub_self,zero_div,mul_zero,Real.exp_zero,mul_one] at h
  fin_cases j <;> norm_num [Fin.sum_univ_two] at h ⊢
  all_goals
    have hc := congrArg Complex.ofReal h
    push_cast at hc ⊢
    linear_combination hc

/-- Both first-amplitude row channels satisfy their actual BH equations. -/
theorem first_mode_equation (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ) (ha : 0 ≤ a)
    (K : TailMatrix T 2) (p : Amp T) (hr : IsRoot z (density r) (diameter a) K p.1 p.2)
    (he : KernelExchange z r a p) (u : T) (i : Fin 2) (b : Bool) :
    (rowMode (p.1 u i) b : ℂ)*modeFactor z r a p b (z u : ℂ) =
      ((2*Real.pi/z u : ℝ) : ℂ)*(rowMode (K u i) b : ℂ) := by
  have h0 := first_equation z hz r a ha K p hr u i 0
  have h1 := first_equation z hz r a ha K p hr u i 1
  simp [Fin.sum_univ_two,he.1,he.2] at h0 h1
  rw [mode_factor_formula z hz r a p b (z u : ℂ) (by simpa using (hz u).le)]
  cases b <;> simp [rowMode,sgn]
  · linear_combination h0+h1
  · linear_combination h0-h1

private theorem second_equation (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ) (ha : 0 ≤ a)
    (K : TailMatrix T 2) (p : Amp T) (hr : IsRoot z (density r) (diameter a) K p.1 p.2)
    (u : T) (i j : Fin 2) :
    ((2*Real.pi*r : ℝ) : ℂ)*∑ l, (p.2 u i l : ℂ)*
      ((if l=j then 1 else 0)-laplace z a (coeff z r a p l j) (z u : ℂ)) =
      (sourceMap z (z u) (coeff z r a p i j) : ℂ) := by
  simp only [rate_laplace z hz r a ha]
  have h := hr.2 u i j
  simp only [secondLHS,edgeLo,diameter,density,sub_self,zero_div,mul_zero,Real.exp_zero,mul_one] at h
  have hs : sourceMap z (z u) (coeff z r a p i j) =
      r*secondRHS z (density r) (diameter a) p.1 p.2 u i j := by
    rw [coeff,map_smul,source_map_at_actual_rate z hz]
    rfl
  rw [hs]
  fin_cases j <;> norm_num [Fin.sum_univ_two] at h ⊢
  all_goals
    have hc := congrArg Complex.ofReal h
    push_cast at hc ⊢
    linear_combination (r : ℂ)*hc

/-- Second amplitudes use the SAME factors and the honest linear kernel
source. The row source is retained until exchange symmetry is applied. -/
theorem second_mode_equation (z : T → ℝ) (hz : ∀ u, 0 < z u) (r a : ℝ) (ha : 0 ≤ a)
    (K : TailMatrix T 2) (p : Amp T) (hr : IsRoot z (density r) (diameter a) K p.1 p.2)
    (he : KernelExchange z r a p) (u : T) (i : Fin 2) (b : Bool) :
    ((2*Real.pi*r : ℝ) : ℂ)*(rowMode (p.2 u i) b : ℂ)*modeFactor z r a p b (z u : ℂ) =
      (sourceMap z (z u) (coeff z r a p i 0+sgn b • coeff z r a p i 1) : ℂ) := by
  have h0 := second_equation z hz r a ha K p hr u i 0
  have h1 := second_equation z hz r a ha K p hr u i 1
  simp [Fin.sum_univ_two,he.1,he.2] at h0 h1
  rw [mode_factor_formula z hz r a p b (z u : ℂ) (by simpa using (hz u).le),map_add,map_smul]
  cases b <;> simp [rowMode,sgn,smul_eq_mul]
  · linear_combination h0+h1
  · linear_combination h0-h1

/-- The two row sources are the same channel source up to a unit sign. -/
theorem row_coeff_mode (z : T → ℝ) (r a : ℝ) (p : Amp T) (he : KernelExchange z r a p)
    (i : Fin 2) (b : Bool) : coeff z r a p i 0+sgn b • coeff z r a p i 1 =
      (if i=0 then (1 : ℝ) else sgn b) • modeCoeff z r a p b := by
  funext j
  fin_cases i <;> cases b
  all_goals simp [modeCoeff,sgn,he.1,he.2]
  all_goals ring

end FMSA.Convergence.BinaryCanonicalChannels
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.factor_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.factor_entry
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.mode_factor_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.mode_factor_formula
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.factor_det_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.factor_det_modes
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.mode_factor_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.mode_factor_ne_zero
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.rate_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.rate_laplace
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.first_mode_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.first_mode_equation
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.second_mode_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.second_mode_equation
/-- info: 'FMSA.Convergence.BinaryCanonicalChannels.row_coeff_mode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BinaryCanonicalChannels.row_coeff_mode
