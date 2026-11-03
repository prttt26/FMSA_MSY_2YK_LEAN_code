import MSAConvergence.PureFluidActualThetaEquation

set_option linter.style.header false

/-! Finite rational dispersion algebra for the pure-fluid H factor. -/
noncomputable section
open Real Filter Topology
open scoped BigOperators ComplexConjugate
namespace FMSA.Convergence.PureFluidHDispersion
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidActualPerTailWeights
open FMSA.Convergence.PureFluidNodeResidues
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.ExactMSA
variable {T : Type*} [Fintype T]

/-- The symmetric two-pole partial fraction. -/
theorem two_pole_fraction {R : Type*} [Field R] (a b s : R)
    (has : a+s ≠ 0) (hbs : b-s ≠ 0) (hab : a+b ≠ 0) :
    1/((a+s)*(b-s)) =
      (1/(a+s)+1/(b-s))/(a+b) := by
  field_simp [has,hbs,hab]
  ring

/-- Reorganize the double-pole product by swapping the two finite indices.
Coincident tail rates are allowed. -/
theorem double_pole_sum {R : Type*} [Field R]
    (z w : T → R) (s : R)
    (hplus : ∀ t, s+z t ≠ 0)
    (hminus : ∀ t, z t-s ≠ 0)
    (hpair : ∀ t u, z t+z u ≠ 0) :
    (∑ t, w t/(s+z t))*(∑ u, w u/(z u-s)) =
      ∑ t, (2*z t*w t/((z t)^2-s^2))*
        (∑ u, w u/(z t+z u)) := by
  classical
  have hterm (t u : T) :
      (w t/(s+z t))*(w u/(z u-s)) =
        (w t*w u/(z t+z u))*
          (1/(s+z t)+1/(z u-s)) := by
    have h := two_pole_fraction (z t) (z u) s
      (by simpa only [add_comm] using hplus t) (hminus u) (hpair t u)
    have h' : 1/((s+z t)*(z u-s)) =
        (1/(s+z t)+1/(z u-s))/(z t+z u) := by
      simpa only [add_comm (z t) s] using h
    calc
      (w t/(s+z t))*(w u/(z u-s)) =
          w t*w u*(1/((s+z t)*(z u-s))) := by
            field_simp [hplus t,hminus u]
      _ = (w t*w u/(z t+z u))*
          (1/(s+z t)+1/(z u-s)) := by rw [h']; ring
  have hswap :
      (∑ t, ∑ u, (w t*w u/(z t+z u))*(1/(z u-s))) =
      (∑ t, ∑ u, (w t*w u/(z t+z u))*(1/(z t-s))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    rw [add_comm (z u) (z t)]
    ring
  calc
    (∑ t, w t/(s+z t))*(∑ u, w u/(z u-s)) =
        ∑ t, ∑ u, (w t/(s+z t))*(w u/(z u-s)) := by
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
    _ = ∑ t, ∑ u, (w t*w u/(z t+z u))*
        (1/(s+z t)+1/(z u-s)) := by
          apply Finset.sum_congr rfl
          intro t _
          exact Finset.sum_congr rfl (fun u _ => hterm t u)
    _ = (∑ t, ∑ u, (w t*w u/(z t+z u))*(1/(s+z t)))+
        (∑ t, ∑ u, (w t*w u/(z t+z u))*(1/(z u-s))) := by
          simp_rw [mul_add,Finset.sum_add_distrib]
    _ = (∑ t, ∑ u, (w t*w u/(z t+z u))*(1/(s+z t)))+
        (∑ t, ∑ u, (w t*w u/(z t+z u))*(1/(z t-s))) := by rw [hswap]
    _ = ∑ t, (2*z t*w t/((z t)^2-s^2))*
        (∑ u, w u/(z t+z u)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro t _
          rw [← Finset.sum_add_distrib]
          calc
            ∑ u, ((w t*w u/(z t+z u))*(1/(s+z t))+
                (w t*w u/(z t+z u))*(1/(z t-s))) =
              ∑ u, (2*z t*w t/((z t)^2-s^2))*(w u/(z t+z u)) := by
                apply Finset.sum_congr rfl
                intro u _
                have hsq : (z t)^2-s^2 ≠ 0 := by
                  rw [show (z t)^2-s^2 = (z t+s)*(z t-s) by ring]
                  exact mul_ne_zero (by simpa only [add_comm] using hplus t) (hminus t)
                field_simp [hplus t,hminus t,hpair t u,hsq]
                ring
            _ = _ := by rw [Finset.mul_sum]

/-- The same finite rational U expression over an arbitrary field. -/
def fieldU {R : Type*} [Field R] (z w : T → R) (s : R) : R :=
  1-∑ t, w t/(s+z t)

/-- The dispersion identity is field algebra, hence it holds at complex
frequency as well as at real frequency. -/
theorem field_U_reflection_dispersion {R : Type*} [Field R]
    (z w : T → R) (s : R)
    (hplus : ∀ t, s+z t ≠ 0)
    (hminus : ∀ t, z t-s ≠ 0)
    (hpair : ∀ t u, z t+z u ≠ 0) :
    fieldU z w s*fieldU z w (-s) =
      1-∑ t, 2*z t*(w t*fieldU z w (z t))/((z t)^2-s^2) := by
  classical
  let a : R := ∑ t, w t/(s+z t)
  let b : R := ∑ t, w t/(z t-s)
  let c (t : T) : R := 2*z t*w t/((z t)^2-s^2)
  let e (t : T) : R := ∑ u, w u/(z t+z u)
  have hsq (t : T) : (z t)^2-s^2 ≠ 0 := by
    rw [show (z t)^2-s^2 = (z t+s)*(z t-s) by ring]
    exact mul_ne_zero (by simpa only [add_comm] using hplus t) (hminus t)
  have hlinear (t : T) : w t/(s+z t)+w t/(z t-s)=c t := by
    dsimp [c]
    field_simp [hplus t,hminus t,hsq t]
    ring
  have hab : a+b = ∑ t, c t := by
    dsimp [a,b]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => hlinear t)
  have hprod : a*b = ∑ t, c t*e t :=
    double_pole_sum z w s hplus hminus hpair
  have hnegative : (∑ t, w t/(-s+z t)) = b := by
    dsimp [b]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    ring
  have hnode (t : T) : fieldU z w (z t) = 1-e t := rfl
  calc
    fieldU z w s*fieldU z w (-s) = (1-a)*(1-b) := by
      unfold fieldU
      rw [hnegative]
    _ = 1-(∑ t, c t)+∑ t, c t*e t := by rw [← hab,← hprod]; ring
    _ = 1-∑ t, c t*(1-e t) := by
      simp_rw [mul_sub,Finset.sum_sub_distrib]
      simp only [mul_one]
      ring
    _ = 1-∑ t, 2*z t*(w t*fieldU z w (z t))/((z t)^2-s^2) := by
      apply congrArg (fun q : R => 1-q)
      apply Finset.sum_congr rfl
      intro t _
      rw [hnode]
      dsimp [c]
      ring

/-- The finite U factor has the even dispersion product with coefficients
`theta_t = w_t U(z_t)` for arbitrary finite rate families. -/
theorem candidate_U_reflection_dispersion
    (z w : T → ℝ) (s : ℝ)
    (hplus : ∀ t, s+z t ≠ 0)
    (hminus : ∀ t, z t-s ≠ 0)
    (hpair : ∀ t u, z t+z u ≠ 0) :
    candidateU z w s*candidateU z w (-s) =
      1-∑ t, 2*z t*(w t*candidateU z w (z t))/((z t)^2-s^2) := by
  simpa only [fieldU,candidateU] using
    field_U_reflection_dispersion z w s hplus hminus hpair

/-- The same finite U factor evaluated at complex frequency. -/
def complexU (z w : T → ℝ) (s : ℂ) : ℂ :=
  fieldU (fun t => (z t : ℂ)) (fun t => (w t : ℂ)) s

/-- On the imaginary axis the reflected finite factor is its conjugate. -/
theorem complexU_conj_imaginary (z w : T → ℝ) (k : ℝ) :
    conj (complexU z w (Complex.I*(k:ℂ))) =
      complexU z w (-(Complex.I*(k:ℂ))) := by
  unfold complexU fieldU
  simp [Complex.conj_ofReal, Complex.conj_I]

/-- Complex U agrees with the real candidate on real frequencies. -/
theorem complexU_ofReal (z w : T → ℝ) (s : ℝ) :
    complexU z w (s : ℂ) = (candidateU z w s : ℂ) := by
  simp [complexU,fieldU,candidateU]

omit [Fintype T] in
/-- Positive rates keep both imaginary-axis pole denominators nonzero. -/
theorem complex_axis_denominators_ne_zero (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (k : ℝ) (t : T) :
    Complex.I*(k:ℂ)+(z t:ℂ) ≠ 0 ∧
      (z t:ℂ)-Complex.I*(k:ℂ) ≠ 0 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact (hz t).ne' hr
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact (hz t).ne' hr

/-- On the imaginary axis the finite dispersion function is exactly
the nonnegative real norm square of the complex U factor. -/
theorem complexU_normSq_imaginary (z w : T → ℝ)
    (hz : ∀ t, 0 < z t) (k : ℝ) :
    Complex.normSq (complexU z w (Complex.I*(k:ℂ))) =
      1-∑ t, 2*z t*(w t*candidateU z w (z t))/((z t)^2+k^2) := by
  let s : ℂ := Complex.I*(k:ℂ)
  let zc : T → ℂ := fun t => (z t:ℂ)
  let wc : T → ℂ := fun t => (w t:ℂ)
  have hp : ∀ t, s+zc t ≠ 0 := fun t =>
    (complex_axis_denominators_ne_zero z hz k t).1
  have hm : ∀ t, zc t-s ≠ 0 := fun t =>
    (complex_axis_denominators_ne_zero z hz k t).2
  have hpair : ∀ t u, zc t+zc u ≠ 0 := by
    intro t u
    change (z t:ℂ)+(z u:ℂ) ≠ 0
    exact_mod_cast (add_pos (hz t) (hz u)).ne'
  have hdisp := field_U_reflection_dispersion zc wc s hp hm hpair
  have hterm (t : T) :
      2*zc t*(wc t*fieldU zc wc (zc t))/((zc t)^2-s^2) =
      ((2*z t*(w t*candidateU z w (z t))/((z t)^2+k^2) : ℝ) : ℂ) := by
    have hnode : fieldU zc wc (zc t) =
        (candidateU z w (z t) : ℂ) := complexU_ofReal z w (z t)
    have hden : (zc t)^2-s^2 = (((z t)^2+k^2 : ℝ) : ℂ) := by
      dsimp [zc,s]
      simp only [mul_pow, Complex.I_sq, Complex.ofReal_pow, Complex.ofReal_add]
      ring
    rw [hnode,hden]
    simp only [zc,wc,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_pow,Complex.ofReal_add, Complex.ofReal_ofNat]
  apply Complex.ofReal_injective
  calc
    ((Complex.normSq (complexU z w s) : ℝ) : ℂ) =
        complexU z w s*conj (complexU z w s) := by
          rw [Complex.mul_conj]
    _ = fieldU zc wc s*fieldU zc wc (-s) := by
          rw [complexU_conj_imaginary]
          rfl
    _ = 1-∑ t, 2*zc t*(wc t*fieldU zc wc (zc t))/((zc t)^2-s^2) := hdisp
    _ = ((1-∑ t, 2*z t*(w t*candidateU z w (z t))/
        ((z t)^2+k^2) : ℝ) : ℂ) := by
          simp_rw [hterm]
          simp

/-- A small positive discrete characteristic keeps the complex U factor
nonzero on the entire imaginary axis, uniformly over real wave numbers. -/
theorem complexU_ne_zero_imaginary_of_small_characteristic
    (z w : T → ℝ) (hz : ∀ t, 0 < z t)
    (hθ : ∀ t, 0 ≤ w t*candidateU z w (z t))
    (hsmall : (∑ t, 2*(w t*candidateU z w (z t))/z t) < 1)
    (k : ℝ) :
    complexU z w (Complex.I*(k:ℂ)) ≠ 0 := by
  have hterm (t : T) :
      2*z t*(w t*candidateU z w (z t))/((z t)^2+k^2) ≤
        2*(w t*candidateU z w (z t))/z t := by
    have hzsq : 0 < (z t)^2 := sq_pos_of_pos (hz t)
    have hd : 0 < (z t)^2+k^2 := add_pos_of_pos_of_nonneg hzsq (sq_nonneg k)
    have hnum : 0 ≤ 2*z t*(w t*candidateU z w (z t)) :=
      mul_nonneg (mul_nonneg (by norm_num) (hz t).le) (hθ t)
    have hdiv : 2*z t*(w t*candidateU z w (z t))/((z t)^2+k^2) ≤
        2*z t*(w t*candidateU z w (z t))/((z t)^2) := by
      apply (div_le_div_iff₀ hd hzsq).2
      nlinarith [mul_nonneg hnum (sq_nonneg k)]
    have heq : 2*z t*(w t*candidateU z w (z t))/((z t)^2) =
        2*(w t*candidateU z w (z t))/z t := by
      field_simp [(hz t).ne']
    exact hdiv.trans_eq heq
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hterm t)
  have hnorm : 0 < Complex.normSq
      (complexU z w (Complex.I*(k:ℂ))) := by
    rw [complexU_normSq_imaginary z w hz k]
    linarith
  exact Complex.normSq_pos.mp hnorm
/-- The actual inverse-dressing coordinates obey the finite dispersion
identity wherever their rational partial fractions are valid. -/
theorem actual_U_reflection_dispersion
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t)
    (s : ℝ) (hs : s ≠ 0)
    (hplus : ∀ t, s+z t ≠ 0)
    (hminus : ∀ t, z t-s ≠ 0) :
    actualU xi z D G s*actualU xi z D G (-s) =
      1-∑ t, 2*z t*actualTheta xi z D G t/((z t)^2-s^2) := by
  let w := actualWeight xi z D G
  have hp := actualU_eq_candidateU_explicit xi z D G hxi
    (fun t => (hz t).ne') s hs hplus
  have hm := actualU_eq_candidateU_explicit xi z D G hxi
    (fun t => (hz t).ne') (-s) (neg_ne_zero.mpr hs)
    (fun t => by simpa only [sub_eq_add_neg,add_comm] using hminus t)
  have hn (t : T) : actualU xi z D G (z t) = candidateU z w (z t) :=
    actualU_eq_candidateU_explicit xi z D G hxi
      (fun u => (hz u).ne') (z t) (hz t).ne'
      (fun u => (add_pos (hz t) (hz u)).ne')
  calc
    actualU xi z D G s*actualU xi z D G (-s) =
        candidateU z w s*candidateU z w (-s) := by rw [hp,hm]
    _ = 1-∑ t, 2*z t*(w t*candidateU z w (z t))/((z t)^2-s^2) :=
      candidate_U_reflection_dispersion z w s hplus hminus
        (fun t u => (add_pos (hz t) (hz u)).ne')
    _ = 1-∑ t, 2*z t*actualTheta xi z D G t/((z t)^2-s^2) := by
      apply congrArg (fun q : ℝ => 1-q)
      apply Finset.sum_congr rfl
      intro t _
      rw [actualTheta, hn t]

/-- The ORIGINAL BH inverse-dressing weights give the imaginary-axis
dispersion identity. This is an exact algebraic statement, independent of
whether the amplitudes solve the MSA equations. -/
theorem actual_complexU_normSq_imaginary
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t) (k : ℝ) :
    Complex.normSq (complexU z (actualWeight xi z D G)
      (Complex.I*(k:ℂ))) =
      1-∑ t, 2*z t*actualTheta xi z D G t/((z t)^2+k^2) := by
  rw [complexU_normSq_imaginary z (actualWeight xi z D G) hz k]
  apply congrArg (fun q : ℝ => 1-q)
  apply Finset.sum_congr rfl
  intro t _
  rw [actualTheta,
    actualU_eq_candidateU_explicit xi z D G hxi
      (fun u => (hz u).ne') (z t) (hz t).ne'
      (fun u => (add_pos (hz t) (hz u)).ne')]

/-- The finite actual dispersion sum cannot exceed one at any real
wave number, since it is one minus a complex norm square. -/
theorem actual_dispersion_sum_le_one
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t) (k : ℝ) :
    (∑ t, 2*z t*actualTheta xi z D G t/((z t)^2+k^2)) ≤ 1 := by
  have h := actual_complexU_normSq_imaginary xi z D G hxi hz k
  have hn := Complex.normSq_nonneg
    (complexU z (actualWeight xi z D G) (Complex.I*(k:ℂ)))
  linarith

/-- Nonnegative physical couplings give nonnegative actual theta weights
at every true root with nonzero factor nodes. Node U need not be positive. -/
theorem actual_theta_nonneg_of_nonneg_coupling
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : 0 < xi) (hz : ∀ t, 0 < z t)
    (hK : ∀ t, 0 ≤ K t)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ t, MultiTail.factor xi z D G (z t) ≠ 0)
    (t : T) :
    0 ≤ actualTheta xi z D G t := by
  have hrho : 0 ≤ rhoOf xi := by
    unfold rhoOf
    positivity
  have hsource : 0 ≤ 2*Real.pi*K t/z t := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (hK t))
      (hz t).le
  have hlam : 0 ≤ rhoOf xi*(2*Real.pi*K t/z t)/
      (MultiTail.factor xi z D G (z t))^2 :=
    div_nonneg (mul_nonneg hrho hsource) (sq_nonneg _)
  unfold actualTheta
  rw [actualWeight_eq_dressedStrength_mul_U_all_rates
    xi z K D G hz hroot hF t,
    dressedStrength_eq_coupling xi z K D G hroot t (hF t)]
  calc
    0 ≤ (rhoOf xi*(2*Real.pi*K t/z t)/
      (MultiTail.factor xi z D G (z t))^2)*
        (actualU xi z D G (z t))^2 :=
      mul_nonneg hlam (sq_nonneg _)
    _ = (rhoOf xi*(2*Real.pi*K t/z t)/
      (MultiTail.factor xi z D G (z t))^2*
        actualU xi z D G (z t))*actualU xi z D G (z t) := by ring

/-- At an actual nonnegative-coupling root, the discrete characteristic
lies in [0,1] at every real wave number. The upper bound is algebraic;
strictness requires a separate nonzero-U argument. -/
theorem actual_dispersion_sum_mem_unit_interval
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz : ∀ t, 0 < z t) (hK : ∀ t, 0 ≤ K t)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ t, MultiTail.factor xi z D G (z t) ≠ 0)
    (k : ℝ) :
    (∑ t, 2*z t*actualTheta xi z D G t/((z t)^2+k^2)) ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro t _
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (hz t).le)
        (actual_theta_nonneg_of_nonneg_coupling xi z K D G
          hxi0 hz hK hroot hF t))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · exact actual_dispersion_sum_le_one xi z D G hxi1.ne hz k

/-- The actual discrete characteristic vanishes at zero first amplitudes,
independently of the second-amplitude seed. -/
theorem actualTheta_zero_first_amplitudes
    (xi : ℝ) (z G : T → ℝ) (t : T) :
    actualTheta xi z (fun _ => 0) G t = 0 := by
  simp [actualTheta,actualWeight,tailAlpha,MultiTail.W,MultiTail.C]

/-- Every continuous amplitude path through a zero-first-amplitude seed
has a uniformly small discrete characteristic near zero coupling. -/
theorem actual_characteristic_small_eventually_on_seed
    (xi : ℝ) (z : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (Gbase : T → ℝ)
    (hp : ContinuousAt p 0)
    (hp0 : p 0 = ((fun _ => 0),Gbase)) :
    ∀ᶠ tau : ℝ in 𝓝 0,
      (∑ t, 2*actualTheta xi z (p tau).1 (p tau).2 t/z t) < 1 := by
  let f : ((T → ℝ) × (T → ℝ)) → ℝ := fun a =>
    ∑ t, 2*actualTheta xi z a.1 a.2 t/z t
  have hf : Continuous f := by
    dsimp [f]
    apply continuous_finsetSum
    intro t _
    have hw := actualWeight_continuous xi z t
    have hu := actualU_node_continuous_amplitudes xi z hxi hz t
    simpa [actualTheta] using
      ((continuous_const.mul (hw.mul hu)).div_const (z t))
  have hf0 : f (p 0) = 0 := by
    rw [hp0]
    simp only [f,actualTheta_zero_first_amplitudes,
      mul_zero,zero_div,Finset.sum_const_zero]
  have hlt : f (p 0) < 1 := by rw [hf0]; norm_num
  exact (hf.continuousAt.comp hp).eventually_lt continuousAt_const hlt

/-- Along an actual nonnegative-coupling HS-seeded root germ, the finite
complex U factor is nonzero at every imaginary frequency in one common
coupling neighbourhood. -/
theorem actual_complexU_axis_nonzero_eventually_on_seed_root
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hK : ∀ t, 0 ≤ K t)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (Gbase : T → ℝ)
    (hp : ContinuousAt p 0)
    (hp0 : p 0 = ((fun _ => 0),Gbase))
    (hroot : ∀ᶠ tau : ℝ in 𝓝 0,
      MultiTail.IsRoot xi z (fun t => tau*K t) (p tau).1 (p tau).2) :
    ∀ᶠ tau : ℝ in 𝓝 0,
      0 ≤ tau → ∀ k : ℝ,
        complexU z (actualWeight xi z (p tau).1 (p tau).2)
          (Complex.I*(k:ℂ)) ≠ 0 := by
  have hsmall := actual_characteristic_small_eventually_on_seed
    xi z hxi1.ne hz p Gbase hp hp0
  have hF := actual_factor_nodes_nonzero_eventually_of_continuous_seed
    xi hxi0 hxi1 z hz p Gbase hp hp0
  filter_upwards [hsmall,hF,hroot] with tau hs hf hr
  intro hτ k
  let w := actualWeight xi z (p tau).1 (p tau).2
  have hnode (t : T) :
      actualU xi z (p tau).1 (p tau).2 (z t) = candidateU z w (z t) :=
    actualU_eq_candidateU_explicit xi z (p tau).1 (p tau).2
      hxi1.ne (fun u => (hz u).ne') (z t) (hz t).ne'
      (fun u => (add_pos (hz t) (hz u)).ne')
  have hθ (t : T) : 0 ≤ w t*candidateU z w (z t) := by
    have h := actual_theta_nonneg_of_nonneg_coupling
      xi z (fun u => tau*K u) (p tau).1 (p tau).2
      hxi0 hz (fun u => mul_nonneg hτ (hK u)) hr hf t
    unfold actualTheta at h
    rw [hnode t] at h
    exact h
  have hs' : (∑ t, 2*(w t*candidateU z w (z t))/z t) < 1 := by
    convert hs using 1
    apply Finset.sum_congr rfl
    intro t _
    rw [actualTheta,hnode t]
  exact complexU_ne_zero_imaginary_of_small_characteristic
    z w hz hθ hs' k

/-- Physical pure-fluid data construct the genuine analytic HS root germ
with a uniform nonzero complex U factor on the entire imaginary axis for
all nearby nonnegative couplings. -/
theorem exists_analytic_hs_root_germ_with_uniform_axis_nonvanishing
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hK : ∀ t, 0 ≤ K t) :
    ∃ p : ℝ → (T → ℝ) × (T → ℝ),
      p 0 = ((fun _ => 0),fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      ∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau*K t) (p tau).1 (p tau).2 ∧
        (0 ≤ tau → ∀ k : ℝ,
          complexU z (actualWeight xi z (p tau).1 (p tau).2)
            (Complex.I*(k:ℂ)) ≠ 0) := by
  obtain ⟨p,hp0,hpa,hroot⟩ :=
    exists_analytic_hs_root_germ_with_theta_h_equations
      xi hxi0 hxi1 z K hz
  have hroot' : ∀ᶠ tau : ℝ in 𝓝 0,
      MultiTail.IsRoot xi z (fun t => tau*K t) (p tau).1 (p tau).2 :=
    hroot.mono (fun _ h => h.1)
  have haxis := actual_complexU_axis_nonzero_eventually_on_seed_root
    xi hxi0 hxi1 z K hz hK p (fun t => G0 xi (z t))
    hpa.continuousAt hp0 hroot'
  exact ⟨p,hp0,hpa,hroot'.and haxis⟩

end FMSA.Convergence.PureFluidHDispersion
/-- info: 'FMSA.Convergence.PureFluidHDispersion.two_pole_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.two_pole_fraction
/-- info: 'FMSA.Convergence.PureFluidHDispersion.double_pole_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.double_pole_sum
/-- info: 'FMSA.Convergence.PureFluidHDispersion.field_U_reflection_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.field_U_reflection_dispersion
/-- info: 'FMSA.Convergence.PureFluidHDispersion.candidate_U_reflection_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.candidate_U_reflection_dispersion
/-- info: 'FMSA.Convergence.PureFluidHDispersion.complexU_conj_imaginary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.complexU_conj_imaginary
/-- info: 'FMSA.Convergence.PureFluidHDispersion.complexU_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.complexU_ofReal
/-- info: 'FMSA.Convergence.PureFluidHDispersion.complex_axis_denominators_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.complex_axis_denominators_ne_zero
/-- info: 'FMSA.Convergence.PureFluidHDispersion.complexU_normSq_imaginary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.complexU_normSq_imaginary
/-- info: 'FMSA.Convergence.PureFluidHDispersion.complexU_ne_zero_imaginary_of_small_characteristic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.complexU_ne_zero_imaginary_of_small_characteristic
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actual_U_reflection_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actual_U_reflection_dispersion
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actual_complexU_normSq_imaginary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actual_complexU_normSq_imaginary
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actual_dispersion_sum_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actual_dispersion_sum_le_one
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actual_theta_nonneg_of_nonneg_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actual_theta_nonneg_of_nonneg_coupling
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actual_dispersion_sum_mem_unit_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actual_dispersion_sum_mem_unit_interval
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actualTheta_zero_first_amplitudes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actualTheta_zero_first_amplitudes
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actual_characteristic_small_eventually_on_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actual_characteristic_small_eventually_on_seed
/-- info: 'FMSA.Convergence.PureFluidHDispersion.actual_complexU_axis_nonzero_eventually_on_seed_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.actual_complexU_axis_nonzero_eventually_on_seed_root
/-- info: 'FMSA.Convergence.PureFluidHDispersion.exists_analytic_hs_root_germ_with_uniform_axis_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHDispersion.exists_analytic_hs_root_germ_with_uniform_axis_nonvanishing
