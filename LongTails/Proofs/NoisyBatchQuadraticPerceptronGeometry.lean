import LongTails.Setups.NoisyBatchQuadraticPerceptron
import LongTails.Proofs.QuadraticPerceptronBatchPotential

namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry

open Classical LongTails.Setups.NoisyBatchQuadraticPerceptron
open scoped RealInnerProductSpace

noncomputable def positive {P : Public} (data : Data P) (c : Features P.dimension) : ℝ :=
  (∑ i : Fin P.count, max ⟪data i, c⟫ 0) / (P.count : ℝ)

noncomputable def negative {P : Public} (data : Data P) (c : Features P.dimension) : ℝ :=
  (∑ i : Fin P.count, max (-⟪data i, c⟫) 0) / (P.count : ℝ)

noncomputable def mean {P : Public} (data : Data P) : Features P.dimension :=
  (P.count : ℝ)⁻¹ • ∑ i : Fin P.count, data i

noncomputable def positiveVector {P : Public} (data : Data P) (c : Features P.dimension) :
    Features P.dimension :=
  (P.count : ℝ)⁻¹ • ∑ i : Fin P.count, if 0 < ⟪data i, c⟫ then data i else 0

lemma positive_negative_scalar (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases h : 0 ≤ x
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

lemma positive_negative_difference (P : Public) (data : Data P) (c : Features P.dimension) :
    positive data c - negative data c = ⟪mean data, c⟫ := by
  unfold positive negative mean
  rw [← sub_div, real_inner_smul_left, sum_inner, ← Finset.sum_sub_distrib]
  simp_rw [positive_negative_scalar]
  ring

lemma positive_nonneg (P : Public) (data : Data P) (c : Features P.dimension) :
    0 ≤ positive data c := by
  unfold positive
  positivity

lemma negative_nonneg (P : Public) (data : Data P) (c : Features P.dimension) :
    0 ≤ negative data c := by
  unfold negative
  positivity

lemma hinge_sum_bound (P : Public) (data : Data P) (c : Features P.dimension)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    positive data c + negative data c ≤ P.radius * ‖c‖ := by
  have hn : (0 : ℝ) < P.count := Nat.cast_pos.mpr P.count.pos
  have hpoint (i : Fin P.count) : max ⟪data i, c⟫ 0 + max (-⟪data i, c⟫) 0 ≤
      P.radius * ‖c‖ := by
    have hi := abs_real_inner_le_norm (data i) c
    have hm := mul_le_mul_of_nonneg_right (hR i) (norm_nonneg c)
    by_cases h : 0 ≤ ⟪data i, c⟫
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h] at *
      linarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)] at *
      linarith
  unfold positive negative
  rw [← add_div, ← Finset.sum_add_distrib, div_le_iff₀ hn]
  simpa [mul_comm, mul_left_comm, mul_assoc] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)

lemma positive_support (P : Public) (data : Data P) (c e : Features P.dimension) :
    positive data c + ⟪positiveVector data c, e⟫ ≤ positive data (c + e) := by
  have hn : (0 : ℝ) ≤ P.count := by positivity
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    QuadraticPerceptronBatchPotential.positive_part_support ⟪data i, c⟫ ⟪data i, e⟫)
  have hh := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn)
  have hi (i : Fin P.count) : ⟪if 0 < ⟪data i, c⟫ then data i else 0, e⟫ =
      if 0 < ⟪data i, c⟫ then ⟪data i, e⟫ else 0 := by
    split_ifs <;> simp
  unfold positive positiveVector
  rw [real_inner_smul_left, sum_inner]
  simp_rw [hi, inner_add_right]
  simpa only [Finset.sum_add_distrib, mul_add, div_eq_mul_inv, mul_comm] using hh

lemma norm_average_le (P : Public) (a : Fin P.count → Features P.dimension)
    (hR : ∀ i, ‖a i‖ ≤ P.radius) :
    ‖(P.count : ℝ)⁻¹ • ∑ i : Fin P.count, a i‖ ≤ P.radius := by
  have hn : (0 : ℝ) < P.count := Nat.cast_pos.mpr P.count.pos
  have hs : ‖∑ i : Fin P.count, a i‖ ≤ (P.count : ℝ) * P.radius := by
    calc
      _ ≤ ∑ i : Fin P.count, ‖a i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin P.count, P.radius := Finset.sum_le_sum fun i _ => hR i
      _ = _ := by simp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (P.count : ℝ)⁻¹ * ((P.count : ℝ) * P.radius) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
    _ = P.radius := by rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

lemma norm_mean_le (P : Public) (data : Data P)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) : ‖mean data‖ ≤ P.radius :=
  norm_average_le P data hR

lemma norm_positiveVector_le (P : Public) (data : Data P) (c : Features P.dimension)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) : ‖positiveVector data c‖ ≤ P.radius := by
  apply norm_average_le
  intro i
  split_ifs
  · exact hR i
  · simpa using (norm_nonneg (data i)).trans (hR i)

lemma negative_component (P : Public) (data : Data P) (c : Features P.dimension)
    (i : Fin P.count) : -(P.count : ℝ) * negative data c ≤ ⟪data i, c⟫ := by
  have hn : (P.count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr P.count.pos)
  have hs : max (-⟪data i, c⟫) 0 ≤ ∑ j : Fin P.count, max (-⟪data j, c⟫) 0 :=
    Finset.single_le_sum (fun j _ => le_max_right (-⟪data j, c⟫) 0) (Finset.mem_univ i)
  have he : (P.count : ℝ) * negative data c = ∑ j : Fin P.count, max (-⟪data j, c⟫) 0 := by
    unfold negative
    field_simp
  have hm := le_max_left (-⟪data i, c⟫) 0
  nlinarith

lemma inner_subset_le_positive (P : Public) (data : Data P)
    (chosen : Fin P.count → Prop) (c : Features P.dimension) :
    ⟪(P.count : ℝ)⁻¹ • ∑ i : Fin P.count, if chosen i then data i else 0, c⟫ ≤
      positive data c := by
  have hn : (0 : ℝ) ≤ (P.count : ℝ)⁻¹ := by positivity
  have hs : (∑ i : Fin P.count, ⟪if chosen i then data i else 0, c⟫) ≤
      ∑ i : Fin P.count, max ⟪data i, c⟫ 0 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_max_left _ _
    · simp
  rw [real_inner_smul_left, sum_inner]
  unfold positive
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hs hn

lemma positive_neg (P : Public) (data : Data P) (c : Features P.dimension) :
    positive data (-c) = negative data c := by
  simp [positive, negative]

lemma negative_neg (P : Public) (data : Data P) (c : Features P.dimension) :
    negative data (-c) = positive data c := by
  simp [positive, negative]

lemma abs_positive_shift_le (P : Public) (data : Data P) (c e : Features P.dimension)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    |positive data (c + e) - positive data c| ≤ P.radius * ‖e‖ := by
  have hl := positive_support P data c e
  have hu := positive_support P data (c + e) (-e)
  have hc : c + e + -e = c := by abel
  rw [hc, inner_neg_right] at hu
  have hi (x : Features P.dimension) : |⟪positiveVector data x, e⟫| ≤ P.radius * ‖e‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_positiveVector_le P data x hR) (norm_nonneg e))
  have h₁ := (abs_le.mp (hi c)).1
  have h₂ := (abs_le.mp (hi (c + e))).2
  rw [abs_le]
  constructor <;> linarith

noncomputable def selected {P : Public} (data : Data P)
    (c : Features P.dimension) (v : ℝ) : Features P.dimension :=
  (P.count : ℝ)⁻¹ • ∑ i : Fin P.count, if v * ⟪data i, c⟫ ≤ 0 then data i else 0

lemma norm_selected_le (P : Public) (data : Data P) (c : Features P.dimension) (v : ℝ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) : ‖selected data c v‖ ≤ P.radius := by
  apply norm_average_le
  intro i
  split_ifs
  · exact hR i
  · simpa using (norm_nonneg (data i)).trans (hR i)

lemma selected_inner_pos (P : Public) (data : Data P) (c : Features P.dimension)
    (v : ℝ) (hv : 0 < v) : ⟪selected data c v, c⟫ = -negative data c := by
  have hp (i : Fin P.count) :
      ⟪if v * ⟪data i, c⟫ ≤ 0 then data i else 0, c⟫ = -max (-⟪data i, c⟫) 0 := by
    by_cases h : ⟪data i, c⟫ ≤ 0
    · rw [ite_eq_left (mul_nonpos_of_nonneg_of_nonpos hv.le h), max_eq_left (by linarith)]
      ring
    · rw [ite_eq_right (not_le.mpr (mul_pos hv (lt_of_not_ge h))), max_eq_right (by linarith)]
      simp
  unfold selected negative
  rw [real_inner_smul_left, sum_inner]
  simp_rw [hp]
  rw [Finset.sum_neg_distrib]
  ring

lemma selected_inner_neg (P : Public) (data : Data P) (c : Features P.dimension)
    (v : ℝ) (hv : v < 0) : ⟪selected data c v, c⟫ = positive data c := by
  have hp (i : Fin P.count) :
      ⟪if v * ⟪data i, c⟫ ≤ 0 then data i else 0, c⟫ = max ⟪data i, c⟫ 0 := by
    by_cases h : 0 ≤ ⟪data i, c⟫
    · rw [ite_eq_left (mul_nonpos_of_nonpos_of_nonneg hv.le h), max_eq_left h]
    · rw [ite_eq_right (not_le.mpr (mul_pos_of_neg_of_neg hv (lt_of_not_ge h))),
        max_eq_right (le_of_not_ge h)]
      simp
  unfold selected positive
  rw [real_inner_smul_left, sum_inner]
  simp_rw [hp]
  ring

lemma selected_zero (P : Public) (data : Data P) (c : Features P.dimension) :
    selected data c 0 = mean data := by simp [selected, mean]

lemma selected_inner_lower (P : Public) (data : Data P)
    (c e : Features P.dimension) (v : ℝ) :
    -negative data e ≤ ⟪selected data c v, e⟫ := by
  have h := inner_subset_le_positive P data (fun i => v * ⟪data i, c⟫ ≤ 0) (-e)
  rw [positive_neg, inner_neg_right] at h
  change -negative data e ≤ ⟪selected data c v, e⟫
  change -⟪selected data c v, e⟫ ≤ negative data e at h
  linarith

lemma selected_inner_upper (P : Public) (data : Data P)
    (c e : Features P.dimension) (v : ℝ) :
    ⟪selected data c v, e⟫ ≤ positive data e :=
  inner_subset_le_positive P data (fun i => v * ⟪data i, c⟫ ≤ 0) e

lemma positive_step_upper (P : Public) (data : Data P)
    (c : Features P.dimension) (v η : ℝ) (hv : 0 ≤ v) (hη : 0 ≤ η)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    positive data (c + (η * v) • selected data c v) ≤
      positive data c + η * v * P.radius ^ 2 := by
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have h := (abs_le.mp (abs_positive_shift_le P data c ((η * v) • selected data c v) hR)).2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hη hv)] at h
  have hb := mul_le_mul_of_nonneg_left (norm_selected_le P data c v hR)
    (mul_nonneg hr (mul_nonneg hη hv))
  nlinarith

lemma inherited_gap (P : Public) (data : Data P)
    (c : Features P.dimension) (v η : ℝ) (hv : 0 < v) (hη : 0 ≤ η) :
    v * (1 - η ^ 2 * ‖selected data c v‖ ^ 2) ≤
      η * negative data (c + (η * v) • selected data c v) +
        (v - η * negative data c) := by
  have h := selected_inner_lower P data c (c + (η * v) • selected data c v) v
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    selected_inner_pos P data c v hv] at h
  have hm := mul_le_mul_of_nonneg_left h hη
  nlinarith

noncomputable def potential {P : Public} (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) : ℝ :=
  ‖c‖ ^ 2 - v ^ 2 + η * v * ⟪mean data, c⟫ +
    2 * ((max (v - η * positive data c) 0) ^ 2 +
      (max (-v - η * negative data c) 0) ^ 2)

lemma potential_bounds (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hη : 0 ≤ η)
    (hsmall : η * P.radius ≤ 1 / 16) (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    (‖c‖ ^ 2 + v ^ 2) / 2 ≤ potential data η c v ∧
      potential data η c v ≤ 2 * (‖c‖ ^ 2 + v ^ 2) := by
  have hp := positive_nonneg P data c
  have hq := negative_nonneg P data c
  have ha : 0 ≤ η * positive data c := mul_nonneg hη hp
  have hb : 0 ≤ η * negative data c := mul_nonneg hη hq
  have hh := mul_le_mul_of_nonneg_left (hinge_sum_bound P data c hR) hη
  have hs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg c)
  have hab : η * positive data c + η * negative data c ≤ ‖c‖ / 16 := by nlinarith
  have hm := positive_negative_difference P data c
  unfold potential
  rw [← hm]
  by_cases hv : 0 ≤ v
  · rw [max_eq_right (show -v - η * negative data c ≤ 0 by linarith)]
    have h := QuadraticPerceptronBatchPotential.potential_bounds ‖c‖ v
      (η * positive data c) (η * negative data c) (norm_nonneg c) hv ha hb hab
    constructor <;> nlinarith [h.1, h.2]
  · rw [max_eq_right (show v - η * positive data c ≤ 0 by linarith)]
    have h := QuadraticPerceptronBatchPotential.potential_bounds ‖c‖ (-v)
      (η * negative data c) (η * positive data c) (norm_nonneg c) (by linarith) hb ha (by linarith)
    constructor <;> nlinarith [h.1, h.2]
lemma penalty_support_upper (v e η p p' a : ℝ) (hη : 0 ≤ η) (hp : p + a ≤ p') :
    (max (v + e - η * p') 0) ^ 2 ≤ (max (v - η * p) 0) ^ 2 +
      2 * max (v - η * p) 0 * (e - η * a) + (e - η * a) ^ 2 := by
  have hm := mul_le_mul_of_nonneg_left hp hη
  have hmax : max (v + e - η * p') 0 ≤ max ((v - η * p) + (e - η * a)) 0 :=
    max_le_max (by nlinarith) le_rfl
  have hs : (max (v + e - η * p') 0) ^ 2 ≤
      (max ((v - η * p) + (e - η * a)) 0) ^ 2 := by
    nlinarith [le_max_right (v + e - η * p') 0,
      le_max_right ((v - η * p) + (e - η * a)) 0]
  exact hs.trans (QuadraticPerceptronBatchPotential.positive_square_add_le _ _)
lemma perturbation_remainder (s r a b m η R : ℝ) (hs : 0 ≤ s)
    (hη : 0 ≤ η) (hsmall : η * R ≤ 1 / 16)
    (ha : |a| ≤ R * s) (hb : |b| ≤ R * s) (hm : |m| ≤ R * s) :
    s ^ 2 - r ^ 2 + η * r * m +
      2 * (r - η * a) ^ 2 + 2 * (-r + η * b) ^ 2 ≤ 6 * (s ^ 2 + r ^ 2) := by
  have bound (x : ℝ) (hx : |x| ≤ R * s) : (η * x) ^ 2 ≤ s ^ 2 / 256 := by
    have h₁ := mul_le_mul_of_nonneg_left hx hη
    have h₂ := mul_le_mul_of_nonneg_right hsmall hs
    have he : |η * x| = η * |x| := by rw [abs_mul, abs_of_nonneg hη]
    rw [← he] at h₁
    have h₃ : |η * x| ≤ s / 16 := by nlinarith
    nlinarith [sq_abs (η * x), abs_nonneg (η * x)]
  have ha₂ := bound a ha
  have hb₂ := bound b hb
  have hm₂ := bound m hm
  have hra : (r - η * a) ^ 2 ≤ 2 * r ^ 2 + 2 * (η * a) ^ 2 := by
    nlinarith [sq_nonneg (r + η * a)]
  have hrb : (-r + η * b) ^ 2 ≤ 2 * r ^ 2 + 2 * (η * b) ^ 2 := by
    nlinarith [sq_nonneg (r + η * b)]
  have cross : η * r * m ≤ r ^ 2 / 16 + 4 * (η * m) ^ 2 := by
    nlinarith [sq_nonneg (r / 4 - 2 * η * m)]
  nlinarith [sq_nonneg s, sq_nonneg r,
    sq_nonneg (r - 4 * η * a), sq_nonneg (r - 4 * η * b)]
lemma potential_perturbation (P : Public) (data : Data P) (η : ℝ)
    (c e : Features P.dimension) (v r : ℝ) (hη : 0 ≤ η)
    (hsmall : η * P.radius ≤ 1 / 16) (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    potential data η (c + e) (v + r) ≤ potential data η c v +
      (2 * ⟪c, e⟫ - 2 * v * r + η * r * ⟪mean data, c⟫ +
        η * v * ⟪mean data, e⟫ +
        4 * max (v - η * positive data c) 0 * (r - η * ⟪positiveVector data c, e⟫) +
        4 * max (-v - η * negative data c) 0 * (-r + η * ⟪positiveVector data (-c), e⟫)) +
      6 * (‖e‖ ^ 2 + r ^ 2) := by
  have hp := penalty_support_upper v r η (positive data c) (positive data (c + e))
    ⟪positiveVector data c, e⟫ hη (positive_support P data c e)
  have hn := positive_support P data (-c) (-e)
  rw [← neg_add, positive_neg, positive_neg, inner_neg_right] at hn
  have hq := penalty_support_upper (-v) (-r) η (negative data c)
    (negative data (c + e)) (-⟪positiveVector data (-c), e⟫) hη hn
  have hi (x : Features P.dimension) (hx : ‖x‖ ≤ P.radius) :
      |⟪x, e⟫| ≤ P.radius * ‖e‖ :=
    (abs_real_inner_le_norm x e).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg e))
  have hr := perturbation_remainder ‖e‖ r ⟪positiveVector data c, e⟫
    ⟪positiveVector data (-c), e⟫ ⟪mean data, e⟫ η P.radius (norm_nonneg e) hη hsmall
    (hi _ (norm_positiveVector_le P data c hR))
    (hi _ (norm_positiveVector_le P data (-c) hR)) (hi _ (norm_mean_le P data hR))
  have hneg : -v + -r - η * negative data (c + e) = -(v + r) - η * negative data (c + e) := by ring
  rw [hneg] at hq
  unfold potential
  rw [norm_add_sq_real, inner_add_right]
  nlinarith [hp, hq, hr]
end LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
