import LongTails.Proofs.CachedJacobianHalpern
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.CachedJacobianOuter

open CachedJacobianHalpern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma prefix_bound {a D : ℝ} {k : ℕ} {B C P : ℕ → ℝ} {v z e : ℕ → E}
    (ha : 0 < a) (hD : 0 ≤ D)
    (hB : ∀ t ≤ k, 0 ≤ B t)
    (hC : ∀ t ≤ k, a * (B t) ^ 2 ≤ 3 * C t)
    (hz : ∀ t ≤ k, ‖z t‖ ≤ D)
    (hP : ∀ t ≤ k, P t = 2 * B t * ⟪v t, z t⟫ + C t * ‖v t‖ ^ 2)
    (hinit : P 0 ≤ 4 * D ^ 2 / a)
    (hstep : ∀ t < k, P (t + 1) ≤ P t +
      (3 / (2 * a)) * (t + 2 : ℝ) ^ 2 * ‖e (t + 1)‖ ^ 2 +
      2 * B (t + 1) * ‖v (t + 1)‖ * ‖e (t + 1)‖)
    (he₁ : ∑ t ∈ Finset.range (k + 1), ‖e t‖ ≤ D)
    (he₂ : ∑ t ∈ Finset.range (k + 1), (t + 1 : ℝ) ^ 2 * ‖e t‖ ^ 2 ≤ D ^ 2) :
    ∀ t ≤ k, a * B t * ‖v t‖ ≤ 20 * D := by
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (Finset.range (k + 1))
    (fun t => a * B t * ‖v t‖) ⟨0, by simp⟩
  have hik : i ≤ k := by simpa using hi
  let W := a * B i * ‖v i‖
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg ha.le (hB i hik)) (norm_nonneg _)
  have hm (t : ℕ) (ht : t ≤ k) : a * B t * ‖v t‖ ≤ W :=
    himax t (by simpa using ht)
  let Q : ℕ → ℝ := fun t =>
    (3 / (2 * a)) * ((t : ℝ) + 1) ^ 2 * ‖e t‖ ^ 2 + (2 / a) * W * ‖e t‖
  have hQ (t : ℕ) : 0 ≤ Q t := by dsimp [Q]; positivity
  have hstep' (t : ℕ) (ht : t < k) : P (t + 1) ≤ P t + Q (t + 1) := by
    have hh := mul_le_mul_of_nonneg_right (hm (t + 1) (by omega))
      (show 0 ≤ (2 / a) * ‖e (t + 1)‖ by positivity)
    have heq : (a * B (t + 1) * ‖v (t + 1)‖) * ((2 / a) * ‖e (t + 1)‖) =
        2 * B (t + 1) * ‖v (t + 1)‖ * ‖e (t + 1)‖ := by field_simp
    rw [heq] at hh
    have hh' := hstep t ht
    dsimp [Q]
    push_cast
    linarith
  have hsum (t : ℕ) (ht : t ≤ k) : P t ≤ P 0 + ∑ j ∈ Finset.range (t + 1), Q j := by
    induction t with
    | zero => simpa using hQ 0
    | succ t ih =>
      have hh := hstep' t (by omega)
      have hi := ih (by omega)
      rw [Finset.sum_range_succ]
      linarith
  have hsub : ∑ j ∈ Finset.range (i + 1), Q j ≤ ∑ j ∈ Finset.range (k + 1), Q j :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun j _ _ => hQ j)
  have hqsum : ∑ j ∈ Finset.range (k + 1), Q j ≤
      (3 / (2 * a)) * D ^ 2 + (2 / a) * W * D := by
    simp only [Q, Finset.sum_add_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    exact add_le_add
      (mul_le_mul_of_nonneg_left he₂ (by positivity))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he₁ hW) (by positivity))
  have hupper : P i ≤ (6 * D ^ 2 + 2 * W * D) / a := by
    have hh := hsum i hik
    have hnn : 0 ≤ D ^ 2 / (2 * a) := by positivity
    have heq : 4 * D ^ 2 / a + ((3 / (2 * a)) * D ^ 2 + (2 / a) * W * D) +
        D ^ 2 / (2 * a) = (6 * D ^ 2 + 2 * W * D) / a := by ring
    linarith
  have hlower := potential_lower_bound (v := v i) ha (hB i hik) (hz i hik) (hC i hik)
  rw [← hP i hik] at hlower
  have hu := (le_div_iff₀ ha).mp hupper
  have hwquad : W ^ 2 ≤ 12 * D * W + 18 * D ^ 2 := by
    change W ^ 2 - 6 * D * W ≤ 3 * a * P i at hlower
    nlinarith
  have hwmax := prefix_quadratic_bound hD hW hwquad
  exact fun t ht => (hm t ht).trans hwmax

noncomputable def weight (t : ℕ) : ℝ := ((t : ℝ) + 1) * (t + 2) / 2

noncomputable def coefficient (a : ℝ) (t : ℕ) : ℝ := a * t * (t + 1) * (t + 2) * (t + 3) / 12

noncomputable def stepSize (a : ℝ) (t : ℕ) : ℝ := a * (t + 3) / 3

noncomputable def potential (a : ℝ) (anchor : E) (u v : ℕ → E) (t : ℕ) : ℝ :=
  2 * weight t * ⟪v t, u t - anchor⟫ + coefficient a (t + 1) * ‖v t‖ ^ 2

lemma weight_nonneg (t : ℕ) : 0 ≤ weight t := by unfold weight; positivity

lemma coefficient_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℕ) : 0 ≤ coefficient a t := by
  unfold coefficient
  positivity

lemma weight_coefficient {a : ℝ} (ha : 0 ≤ a) (t : ℕ) :
    a * (weight t) ^ 2 ≤ 3 * coefficient a (t + 1) := by
  unfold weight coefficient
  push_cast
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg ha (show 0 ≤ (t : ℝ) ^ 3 by positivity),
    mul_nonneg ha (show 0 ≤ (t : ℝ) ^ 2 by positivity), mul_nonneg ha ht]

lemma coefficient_step_bound {a : ℝ} (ha : 0 < a) (t : ℕ) :
    2 * coefficient a t / (stepSize a t) ^ 2 ≤ (3 / (2 * a)) * (t + 1 : ℝ) ^ 2 := by
  unfold coefficient stepSize
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have hden : 0 < a * ((t : ℝ) + 3) / 3 := by positivity
  apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
  field_simp
  nlinarith [sq_nonneg (t : ℝ)]

lemma initial_potential_bound {a D : ℝ} {anchor u v e : E}
    (ha : 0 < a) (hD : 0 ≤ D) (hu : ‖u - anchor‖ ≤ D) (he : ‖e‖ ≤ D)
    (hrel : e = u - anchor + a • v) :
    2 * ⟪v, u - anchor⟫ + 2 * a * ‖v‖ ^ 2 ≤ 4 * D ^ 2 / a := by
  have hav : a * ‖v‖ ≤ 2 * D := by
    have hvec : a • v = e - (u - anchor) := by rw [hrel]; module
    have hnorm := norm_sub_le e (u - anchor)
    rw [← hvec, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hnorm
    linarith
  have hid : 2 * ⟪v, u - anchor⟫ + 2 * a * ‖v‖ ^ 2 = 2 * ⟪v, e⟫ := by
    rw [hrel, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  rw [hid]
  apply (le_div_iff₀ ha).mpr
  have hcs := real_inner_le_norm v e
  have hmul := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 2 * a by positivity)
  have herr := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * a * ‖v‖ by positivity)
  have hprod := mul_le_mul_of_nonneg_right hav (show 0 ≤ 2 * D by positivity)
  nlinarith

lemma certified_prefix {a D : ℝ} {k : ℕ} {anchor : E} {u v e : ℕ → E}
    (ha : 0 < a) (hD : 0 ≤ D)
    (hdiam : ∀ t ≤ k, ‖u t - anchor‖ ≤ D)
    (hzero : e 0 = u 0 - anchor + a • v 0) (hezero : ‖e 0‖ ≤ D)
    (hrec : ∀ t < k, u (t + 1) - u t =
      -(2 / (t + 3 : ℝ)) • (u t - anchor) - stepSize a (t + 1) • v (t + 1) + e (t + 1))
    (hmono : ∀ t < k, 0 ≤ ⟪v (t + 1) - v t, u (t + 1) - u t⟫)
    (he₁ : ∑ t ∈ Finset.range (k + 1), ‖e t‖ ≤ D)
    (he₂ : ∑ t ∈ Finset.range (k + 1), (t + 1 : ℝ) ^ 2 * ‖e t‖ ^ 2 ≤ D ^ 2) :
    ‖v k‖ ≤ 40 * D / (a * (k + 1 : ℝ) ^ 2) := by
  let P := potential a anchor u v
  have hinit : P 0 ≤ 4 * D ^ 2 / a := by
    have heq : P 0 = 2 * ⟪v 0, u 0 - anchor⟫ + 2 * a * ‖v 0‖ ^ 2 := by
      dsimp [P, potential, weight, coefficient]
      norm_num only [Nat.cast_zero, Nat.cast_one]
      ring
    rw [heq]
    exact initial_potential_bound ha hD (hdiam 0 (Nat.zero_le k)) hezero hzero
  have hstep (t : ℕ) (ht : t < k) : P (t + 1) ≤ P t +
      (3 / (2 * a)) * (t + 2 : ℝ) ^ 2 * ‖e (t + 1)‖ ^ 2 +
      2 * weight (t + 1) * ‖v (t + 1)‖ * ‖e (t + 1)‖ := by
    have hrel := hrec t ht
    have hid := potential_identity (a := a) (t := (t : ℝ) + 1)
      (u := u (t + 1)) (up := u t) (v := v (t + 1)) (vp := v t)
      (anchor := anchor) (e := e (t + 1))
      (by positivity : (t : ℝ) + 1 + 2 ≠ 0)
      (by simpa only [stepSize, Nat.cast_add, Nat.cast_one,
        show (t : ℝ) + 1 + 2 = t + 3 by ring] using hrel)
    have hid' : P (t + 1) - P t =
        -coefficient a (t + 1) * ‖v (t + 1) - v t‖ ^ 2 -
        (((t : ℝ) + 1) * (t + 2) * (t + 3) / 2) *
          ⟪v (t + 1) - v t, u (t + 1) - u t⟫ +
        (2 * coefficient a (t + 1) / stepSize a (t + 1)) *
          ⟪v (t + 1) - v t, e (t + 1)⟫ +
        2 * weight (t + 1) * ⟪v (t + 1), e (t + 1)⟫ := by
      convert hid using 1 <;> simp only [P, potential, weight, coefficient, stepSize, Nat.cast_add, Nat.cast_one]
      · ring
      · field_simp
        ring
    have hη : 0 < stepSize a (t + 1) := by unfold stepSize; positivity
    have hb := energy_step_bound (coefficient_nonneg ha.le _) (by positivity)
      (weight_nonneg _) hη (hmono t ht) hid'
    have hc := coefficient_step_bound ha (t + 1)
    push_cast at hc
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖e (t + 1)‖)
    linarith
  have hbound := prefix_bound ha hD (fun t _ => weight_nonneg t)
    (fun t _ => weight_coefficient ha.le t) hdiam (fun _ _ => rfl) hinit hstep he₁ he₂ k le_rfl
  apply (le_div_iff₀ (by positivity : 0 < a * (k + 1 : ℝ) ^ 2)).mpr
  have hc : a * (k + 1 : ℝ) ^ 2 ≤ 2 * a * weight k := by
    unfold weight
    nlinarith [mul_nonneg ha.le (Nat.cast_nonneg k)]
  have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg (v k))
  nlinarith

end LongTails.Proofs.CachedJacobianOuter
