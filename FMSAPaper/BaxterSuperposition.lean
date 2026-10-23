import FMSAPaper.FiniteBasisJets

/-! Finite superposition of an affine/quadratic Baxter numerator. The integral
hypotheses are explicit here and discharged for actual Baxter factors downstream. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace FMSA.Paper.BaxterSuperposition

variable {T : Type*} [Fintype T]

theorem integral_product_sum (p q : ℝ → ℝ) (f g : T → ℝ → ℝ)
    (h00 : Integrable (fun t => p t * q t))
    (h10 : ∀ u, Integrable (fun t => f u t * q t))
    (h01 : ∀ v, Integrable (fun t => p t * g v t))
    (h11 : ∀ u v, Integrable (fun t => f u t * g v t)) :
    (∫ t, (p t + ∑ u, f u t) * (q t + ∑ v, g v t)) =
      (∫ t, p t * q t) + (∑ u, ∫ t, f u t * q t) +
        (∑ v, ∫ t, p t * g v t) + ∑ u, ∑ v, ∫ t, f u t * g v t := by
  have hi10 := integrable_finsetSum Finset.univ (fun u _ => h10 u)
  have hi01 := integrable_finsetSum Finset.univ (fun v _ => h01 v)
  have hi11 := integrable_finsetSum Finset.univ (fun u _ =>
    integrable_finsetSum Finset.univ (fun v _ => h11 u v))
  have he (t : ℝ) : (p t + ∑ u, f u t) * (q t + ∑ v, g v t) =
      (p t * q t + (∑ u, f u t * q t)) +
        ((∑ v, p t * g v t) + ∑ u, ∑ v, f u t * g v t) := by
    simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun v u => f u t * g v t)]
  simp_rw [he]
  have hsplit := integral_add (h00.add hi10) (hi01.add hi11)
  simp only [Pi.add_apply] at hsplit
  rw [hsplit]
  rw [integral_add h00 hi10, integral_add hi01 hi11]
  rw [integral_finsetSum _ (fun u _ => h10 u), integral_finsetSum _ (fun v _ => h01 v),
    integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => h11 u v))]
  simp_rw [integral_finsetSum _ (fun v _ => h11 _ v)]
  ring

theorem integral_product_pair (p q f g : ℝ → ℝ)
    (h00 : Integrable (fun t => p t * q t))
    (h10 : Integrable (fun t => f t * q t))
    (h01 : Integrable (fun t => p t * g t))
    (h11 : Integrable (fun t => f t * g t)) :
    (∫ t, (p t + f t) * (q t + g t)) =
      (∫ t, p t * q t) + (∫ t, f t * q t) +
        (∫ t, p t * g t) + ∫ t, f t * g t := by
  simpa only [Fintype.sum_unique] using
    integral_product_sum (T := Unit) p q (fun _ => f) (fun _ => g) h00
      (fun _ => h10) (fun _ => h01) (fun _ _ => h11)

theorem quadratic_superposition (d0 b00 : ℝ) (d b10 b01 : T → ℝ) (b11 : T → T → ℝ) :
    -(d0 + ∑ u, d u) + (b00 + (∑ u, b10 u) + (∑ u, b01 u) + ∑ u, ∑ v, b11 u v) =
      (-d0 + b00) +
        (∑ u, ((-(d0 + d u) + (b00 + b10 u + b01 u + b11 u u)) - (-d0 + b00))) +
          (∑ u, ∑ v, b11 u v) - ∑ u, b11 u u := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

variable {N : ℕ}

def cross (rho : Fin N → ℝ) (Q D : Fin N → Fin N → ℝ → ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  ∑ l, rho l * ∫ t : ℝ, D i l (t+r) * Q j l t

def numerator (rho : Fin N → ℝ) (Q D : Fin N → Fin N → ℝ → ℝ)
    (i j : Fin N) (r : ℝ) : ℝ := -D i j r + cross rho Q D i j r

theorem cross_add_sum (rho : Fin N → ℝ) (P D : Fin N → Fin N → ℝ → ℝ)
    (F G : T → Fin N → Fin N → ℝ → ℝ) (i j : Fin N) (r : ℝ)
    (h00 : ∀ l, Integrable (fun t => D i l (t+r) * P j l t))
    (h10 : ∀ u l, Integrable (fun t => G u i l (t+r) * P j l t))
    (h01 : ∀ v l, Integrable (fun t => D i l (t+r) * F v j l t))
    (h11 : ∀ u v l, Integrable (fun t => G u i l (t+r) * F v j l t)) :
    cross rho (fun a b t => P a b t + ∑ u, F u a b t)
      (fun a b t => D a b t + ∑ u, G u a b t) i j r =
      cross rho P D i j r + (∑ u, cross rho P (G u) i j r) +
        (∑ v, cross rho (F v) D i j r) + ∑ u, ∑ v, cross rho (F v) (G u) i j r := by
  unfold cross
  simp_rw [integral_product_sum _ _ _ _ (h00 _) (fun u => h10 u _)
    (fun v => h01 v _) (fun u v => h11 u v _)]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun l u => rho l * ∫ t : ℝ, G u i l (t+r) * P j l t),
    Finset.sum_comm (f := fun l v => rho l * ∫ t : ℝ, D i l (t+r) * F v j l t)]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.sum_comm

theorem numerator_superposition (rho : Fin N → ℝ) (P D : Fin N → Fin N → ℝ → ℝ)
    (F G : T → Fin N → Fin N → ℝ → ℝ) (i j : Fin N) (r : ℝ)
    (h00 : ∀ l, Integrable (fun t => D i l (t+r) * P j l t))
    (h10 : ∀ u l, Integrable (fun t => G u i l (t+r) * P j l t))
    (h01 : ∀ v l, Integrable (fun t => D i l (t+r) * F v j l t))
    (h11 : ∀ u v l, Integrable (fun t => G u i l (t+r) * F v j l t)) :
    numerator rho (fun a b t => P a b t + ∑ u, F u a b t)
      (fun a b t => D a b t + ∑ u, G u a b t) i j r =
      numerator rho P D i j r +
        (∑ u, (numerator rho (fun a b t => P a b t + F u a b t)
          (fun a b t => D a b t + G u a b t) i j r - numerator rho P D i j r)) +
        (∑ u, ∑ v, cross rho (F v) (G u) i j r) - ∑ u, cross rho (F u) (G u) i j r := by
  have hp (u : T) : cross rho (fun a b t => P a b t + F u a b t)
      (fun a b t => D a b t + G u a b t) i j r =
        cross rho P D i j r + cross rho P (G u) i j r +
          cross rho (F u) D i j r + cross rho (F u) (G u) i j r := by
    simpa only [Fintype.sum_unique] using cross_add_sum (T := Unit)
      rho P D (fun _ => F u) (fun _ => G u) i j r (h00) (fun _ => h10 u)
        (fun _ => h01 u) (fun _ _ => h11 u u)
  unfold numerator
  rw [cross_add_sum rho P D F G i j r h00 h10 h01 h11]
  simp_rw [hp]
  exact quadratic_superposition _ _ _ _ _ _

end FMSA.Paper.BaxterSuperposition

/-- info: 'FMSA.Paper.BaxterSuperposition.integral_product_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSuperposition.integral_product_sum

/-- info: 'FMSA.Paper.BaxterSuperposition.integral_product_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSuperposition.integral_product_pair

/-- info: 'FMSA.Paper.BaxterSuperposition.quadratic_superposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSuperposition.quadratic_superposition

/-- info: 'FMSA.Paper.BaxterSuperposition.cross_add_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSuperposition.cross_add_sum

/-- info: 'FMSA.Paper.BaxterSuperposition.numerator_superposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterSuperposition.numerator_superposition
