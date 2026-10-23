import Mathlib

/-! Rational blocks for the finite-tail RDF spectral identity. No RDF hypotheses. -/
noncomputable section
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail.RDFAlgebra

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

def polyT (a h b s : 𝕜) : 𝕜 := s + b + (a - h) / s - a / s ^ 2
def polyP (a h s : 𝕜) : 𝕜 := a / s ^ 2 + h / s
def tailT (z w s : 𝕜) : 𝕜 := z * w / (s + z)
def tailP (z c s : 𝕜) : 𝕜 := z * c / (s + z)

def headBlock (a h b s : 𝕜) : 𝕜 :=
  polyT a h b s * polyT a h b (-s) - polyP a h s * polyP a h (-s) + s ^ 2
def mixedBlock (a h b z w c s : 𝕜) : 𝕜 :=
  polyT a h b s * tailT z w (-s) + tailT z w s * polyT a h b (-s) -
    polyP a h s * tailP z c (-s) - tailP z c s * polyP a h (-s) +
    2 * s ^ 2 / (s ^ 2 - z ^ 2) * (w * polyT a h b z - c * polyP a h z)
def pairBlock (z w c v d e s : 𝕜) : 𝕜 :=
  tailT z w s * tailT v d (-s) - tailP z c s * tailP v e (-s) +
    2 * s ^ 2 / (s ^ 2 - z ^ 2) * (w * tailT v d z - c * tailP v e z)
def mixedConstant (a h b z w c : 𝕜) : 𝕜 :=
  2 * b * w + 2 * (a - h) * (w / z) - 2 * a * ((w + c) / z ^ 2) - 2 * h * (c / z)

theorem head_identity (a h b s : 𝕜) (hs : s ≠ 0) :
    headBlock a h b s = b ^ 2 - 2 * (a - h) + (-a ^ 2 + 2 * a * h - 2 * a * b) / s ^ 2 := by
  unfold headBlock polyT polyP
  field_simp [hs]
  ring

theorem mixed_identity (a h b z w c s : 𝕜) (hs : s ≠ 0) (hz : z ≠ 0)
    (hp : s + z ≠ 0) (hm : s - z ≠ 0) :
    mixedBlock a h b z w c s = -2 * a * (w + c) / s ^ 2 + mixedConstant a h b z w c := by
  have hd : s ^ 2 - z ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hp hm
  have hn : -s + z ≠ 0 := by
    convert neg_ne_zero.mpr hm using 1 <;> ring
  unfold mixedBlock mixedConstant polyT polyP tailT tailP
  field_simp [hs, hz, hp, hn, hd]
  ring

/-- Polarization includes equal rates, with no z-v denominator. -/
theorem pair_identity (z w c v d e s : 𝕜)
    (hpz : s + z ≠ 0) (hmz : s - z ≠ 0)
    (hpv : s + v ≠ 0) (hmv : s - v ≠ 0) (hzv : z + v ≠ 0) :
    pairBlock z w c v d e s + pairBlock v d e z w c s = 2 * (w * d - c * e) := by
  have hdz : s ^ 2 - z ^ 2 ≠ 0 := by rw [sq_sub_sq]; exact mul_ne_zero hpz hmz
  have hdv : s ^ 2 - v ^ 2 ≠ 0 := by rw [sq_sub_sq]; exact mul_ne_zero hpv hmv
  have hnz : -s + z ≠ 0 := by
    convert neg_ne_zero.mpr hmz using 1 <;> ring
  have hnv : -s + v ≠ 0 := by
    convert neg_ne_zero.mpr hmv using 1 <;> ring
  unfold pairBlock tailT tailP
  field_simp [hpz, hnz, hpv, hnv, hzv, add_comm v z, hdz, hdv]
  ring

variable {ι : Type*} [Fintype ι]

def T (a h b : 𝕜) (z w : ι → 𝕜) (s : 𝕜) : 𝕜 := polyT a h b s + ∑ u, tailT (z u) (w u) s
def P (a h : 𝕜) (z c : ι → 𝕜) (s : 𝕜) : 𝕜 := polyP a h s + ∑ u, tailP (z u) (c u) s

/-- Exact finite-sum assembly, prior to imposing the physical core moments or BH root. -/
theorem sum_identity (a h b s : 𝕜) (z w c : ι → 𝕜) (hs : s ≠ 0)
    (hz : ∀ u, z u ≠ 0) (hp : ∀ u, s + z u ≠ 0) (hm : ∀ u, s - z u ≠ 0)
    (hzz : ∀ u t, z u + z t ≠ 0) :
    T a h b z w s * T a h b z w (-s) - P a h z c s * P a h z c (-s) + s ^ 2 +
      ∑ u, 2 * s ^ 2 / (s ^ 2 - (z u) ^ 2) *
        (w u * T a h b z w (z u) - c u * P a h z c (z u)) =
      (b + ∑ u, w u) ^ 2 - (∑ u, c u) ^ 2 -
      2 * (a - h) * (1 - ∑ u, w u / z u) -
      2 * a * (∑ u, (w u + c u) / (z u) ^ 2) - 2 * h * (∑ u, c u / z u) +
      (-a ^ 2 + 2 * a * h - 2 * a * b - 2 * a * (∑ u, (w u + c u))) / s ^ 2 := by
  have he : T a h b z w s * T a h b z w (-s) - P a h z c s * P a h z c (-s) + s ^ 2 +
      (∑ u, 2 * s ^ 2 / (s ^ 2 - (z u) ^ 2) *
        (w u * T a h b z w (z u) - c u * P a h z c (z u))) =
      headBlock a h b s + (∑ u, mixedBlock a h b (z u) (w u) (c u) s) +
        ∑ u, ∑ t, pairBlock (z u) (w u) (c u) (z t) (w t) (c t) s := by
    unfold T P headBlock mixedBlock pairBlock
    simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun u t => tailT (z t) (w t) s * tailT (z u) (w u) (-s)),
      Finset.sum_comm (f := fun u t => tailP (z t) (c t) s * tailP (z u) (c u) (-s))]
    ring
  have hpair : (∑ u, ∑ t, pairBlock (z u) (w u) (c u) (z t) (w t) (c t) s) =
      (∑ u, w u) ^ 2 - (∑ u, c u) ^ 2 := by
    let f := fun u t => pairBlock (z u) (w u) (c u) (z t) (w t) (c t) s
    have heq (u t : ι) : f u t + f t u = 2 * (w u * w t - c u * c t) :=
      pair_identity _ _ _ _ _ _ s (hp u) (hm u) (hp t) (hm t) (hzz u t)
    have hswap : (∑ u, ∑ t, f t u) = ∑ u, ∑ t, f u t := Finset.sum_comm
    have hh : (∑ u, ∑ t, (f u t + f t u)) = 2 * ∑ u, ∑ t, f u t := by
      simp only [Finset.sum_add_distrib]
      rw [hswap]
      ring
    simp_rw [heq] at hh
    simp only [Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul] at hh
    change (∑ u, ∑ t, f u t) = _
    apply mul_left_cancel₀ (two_ne_zero : (2 : 𝕜) ≠ 0)
    linear_combination -hh
  rw [he, hpair, head_identity _ _ _ s hs]
  simp_rw [mixed_identity a h b _ _ _ s hs (hz _) (hp _) (hm _)]
  simp only [mixedConstant, div_eq_mul_inv, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

def dictionary (a h : 𝕜) (z w c : ι → 𝕜) (E s : 𝕜) : 𝕜 :=
  (1 - s - E) / s ^ 2 * h + (1 - s + s ^ 2 / 2 - E) / s ^ 3 * a +
    ∑ u, ((w u + c u * E) / (s + z u) + c u * (1 - E) / s)

/-- Separating the exponential part leaves a rational function T. -/
theorem recenter_identity (a h E s : 𝕜) (z w c : ι → 𝕜)
    (hs : s ≠ 0) (hp : ∀ u, s + z u ≠ 0) :
    T a h (h - a / 2 - ∑ u, (w u + c u)) z w s =
      s - s * dictionary a h z w c E s - E * P a h z c s := by
  have hh : polyT a h (h - a / 2) s =
      s - s * ((1 - s - E) / s ^ 2 * h + (1 - s + s ^ 2 / 2 - E) / s ^ 3 * a) -
        E * polyP a h s := by
    unfold polyT polyP
    field_simp [hs]
    ring
  have ht (u : ι) : -(w u + c u) + tailT (z u) (w u) s =
      -s * ((w u + c u * E) / (s + z u) + c u * (1 - E) / s) -
        E * tailP (z u) (c u) s := by
    unfold tailT tailP
    field_simp [hs, hp u]
    ring
  have he : T a h (h - a / 2 - ∑ u, (w u + c u)) z w s =
      polyT a h (h - a / 2) s + ∑ u, (-(w u + c u) + tailT (z u) (w u) s) := by
    unfold T polyT
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  rw [he, hh]
  simp_rw [ht]
  unfold dictionary P
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end FMSA.ExactMSA.MultiTail.RDFAlgebra
