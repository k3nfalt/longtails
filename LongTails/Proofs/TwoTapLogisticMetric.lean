import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoTapLogisticMetric

open LongTails.Setups.TwoSampleQuadraticPerceptron
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

variable {d : ℕ}

lemma filter_energy (a b : ℝ) (g : Features d) :
    4 * ‖a • g + b • shift g‖ ^ 2 =
      (a + b) ^ 2 * ‖g + shift g‖ ^ 2 + (a - b) ^ 2 * ‖g - shift g‖ ^ 2 := by
  simp only [norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, real_inner_smul_left, real_inner_smul_right, norm_shift]
  ring

lemma margin_increment (η a b : ℝ) (x v g : Features d) :
    let h := a • g + b • shift g
    let s := ⟪g, v⟫
    let t := ⟪shift g, v⟫
    margin .conv d x ((a + η * s, b + η * t), v + η • h) -
        margin .conv d x ((a, b), v) =
      η * (⟪a • x + b • shift x, h⟫ + s * ⟪x, v⟫ + t * ⟪shift x, v⟫) +
        η ^ 2 * (s * ⟪x, h⟫ + t * ⟪shift x, h⟫) := by
  dsimp only [margin]
  simp only [inner_add_left, real_inner_smul_left, inner_add_right, real_inner_smul_right]
  ring

lemma paired_tap_change (η a b : ℝ) (v g k : Features d) :
    let h := a • g + b • shift g
    let next := v + η • h
    (η * ⟪g, v⟫ + η * ⟪k, next⟫, η * ⟪shift g, v⟫ + η * ⟪shift k, next⟫) =
      (η * ⟪g + k, v⟫ + η ^ 2 * ⟪k, h⟫,
       η * ⟪shift (g + k), v⟫ + η ^ 2 * ⟪shift k, h⟫) := by
  dsimp only
  simp only [shift_add, inner_add_left, inner_add_right, real_inner_smul_right]
  congr 1 <;> ring

lemma alternating_mode_damping (a b : ℝ) (g : Features d) :
    let h := a • g + b • shift g
    (⟪g + shift g, h⟫, ⟪g - shift g, h⟫) =
      ((a + b) * (‖g‖ ^ 2 + ⟪g, shift g⟫), (a - b) * (‖g‖ ^ 2 - ⟪g, shift g⟫)) := by
  dsimp only
  simp only [inner_sub_left, inner_add_left, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_shift, real_inner_comm g (shift g)]
  congr 1 <;> ring

lemma sigmoid_secant (x y : ℝ) :
    4 * (Real.sigmoid y - Real.sigmoid x) ^ 2 ≤
      (Real.sigmoid y - Real.sigmoid x) * (y - x) := by
  wlog h : x ≤ y generalizing x y
  · have hs := this y x (le_of_not_ge h)
    nlinarith
  rcases h.eq_or_lt with rfl | h
  · simp
  obtain ⟨z, _, hz⟩ := exists_deriv_eq_slope Real.sigmoid h continuous_sigmoid.continuousOn
    (fun t _ => (Real.hasDerivAt_sigmoid t).differentiableAt.differentiableWithinAt)
  rw [Real.deriv_sigmoid] at hz
  have hd : 0 ≤ Real.sigmoid y - Real.sigmoid x :=
    sub_nonneg.mpr (Real.sigmoid_strictMono.monotone h.le)
  have hb : (Real.sigmoid y - Real.sigmoid x) / (y - x) ≤ 1 / 4 := by
    rw [← hz]
    nlinarith [sq_nonneg (Real.sigmoid z - 1 / 2)]
  have ht := (div_le_iff₀ (sub_pos.mpr h)).mp hb
  nlinarith [mul_nonneg hd (show 0 ≤ (y - x) - 4 * (Real.sigmoid y - Real.sigmoid x) by
    linarith)]

lemma rough_secant_bound {n : ℕ} (b : Fin n → Features d) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (L : ℝ) (hL : 0 ≤ L)
    (hcov : ∀ s : Fin n → ℝ, let u := ∑ i, (p i * s i) • b i
      ‖u - shift u‖ ^ 2 ≤ 2 * L * ∑ i, p i * s i ^ 2) (x y : Features d) :
    let s := fun i => Real.sigmoid (-⟪b i, x⟫) - Real.sigmoid (-⟪b i, y⟫)
    let u := ∑ i, (p i * s i) • b i
    2 * ‖u - shift u‖ ^ 2 ≤ L * ⟪u, y - x⟫ := by
  intro s u
  have hsum : 4 * ∑ i, p i * s i ^ 2 ≤ ⟪u, y - x⟫ := by
    simp only [u, sum_inner, real_inner_smul_left, inner_sub_right, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hi := mul_le_mul_of_nonneg_left (sigmoid_secant (-⟪b i, y⟫) (-⟪b i, x⟫)) (hp i)
    dsimp [s]
    linarith only [hi]
  have hnorm := hcov s
  change ‖u - shift u‖ ^ 2 ≤ _ at hnorm
  linarith only [hnorm, mul_le_mul_of_nonneg_left hsum hL]

lemma radial_increment (η a b : ℝ) (v g : Features d) :
    let h := a • g + b • shift g
    let j := ⟪g, v⟫
    let k := ⟪shift g, v⟫
    ((a + η * j) ^ 2 + (b + η * k) ^ 2 + ‖v + η • h‖ ^ 2) -
        (a ^ 2 + b ^ 2 + ‖v‖ ^ 2) =
      4 * η * (a * j + b * k) + η ^ 2 * (j ^ 2 + k ^ 2 + ‖h‖ ^ 2) := by
  dsimp only
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, inner_add_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm v g, real_inner_comm v (shift g)]
  ring

lemma finite_margin_radial_bonus (m : ℝ) :
    m * Real.sigmoid (-m) = min m 0 + |m| * Real.sigmoid (-|m|) := by
  by_cases hm : 0 ≤ m
  · simp [abs_of_nonneg hm, min_eq_right hm]
  · have hm' := (lt_of_not_ge hm).le
    rw [abs_of_nonpos hm', neg_neg, min_eq_left hm', Real.sigmoid_neg]
    ring

lemma shift_sum_smul {n : ℕ} (x : Fin n → Features d) (v : Fin n → ℝ) :
    shift (∑ i, v i • x i) = ∑ i, v i • shift (x i) := by
  classical
  generalize (Finset.univ : Finset (Fin n)) = t
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert j t hj ih => simp [hj, shift_add, shift_smul, ih]

lemma radial_margin_sum {n : ℕ} (x : Fin n → Features d) (p : Fin n → ℝ)
    (a b : ℝ) (v : Features d) :
    let m := fun i => margin .conv d (x i) ((a,b),v)
    let g := ∑ i, (p i * Real.sigmoid (-m i)) • x i
    a * ⟪g,v⟫ + b * ⟪shift g,v⟫ =
      ∑ i, p i * (min (m i) 0 + |m i| * Real.sigmoid (-|m i|)) := by
  intro m g
  simp_rw [← finite_margin_radial_bonus]
  dsimp only [g]
  rw [shift_sum_smul]
  simp only [sum_inner, real_inner_smul_left, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [m, margin]
  ring

lemma capped_motion {n : ℕ} (x : Fin n → Features d) (y w : Features d)
    (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc 0 1) (h : ℝ) (hh : 0 ≤ h) :
    ⟪y, w + h • ∑ i, q i • x i⟫ ≤ ⟪y,w⟫ + h * ∑ i, max 0 ⟪y,x i⟫ := by
  rw [inner_add_right, real_inner_smul_right, inner_sum]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hh
  apply Finset.sum_le_sum
  intro i _
  rw [real_inner_smul_right]
  by_cases H : 0 ≤ ⟪y,x i⟫
  · simpa [max_eq_right H] using mul_le_mul_of_nonneg_right (hq i).2 H
  · exact (mul_nonpos_of_nonneg_of_nonpos (hq i).1 (le_of_not_ge H)).trans (le_max_left _ _)

lemma mixture_delay {n : ℕ} (x : Fin n → Features d) (α : Fin n → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hα' : ∑ i, α i = 1) (y : Features d) (hy : y = ∑ i, α i • x i)
    (w : ℕ → Features d) (q : ℕ → Fin n → ℝ) (hq : ∀ t i, q t i ∈ Set.Icc 0 1)
    (h : ℝ) (hh : 0 ≤ h) (step : ∀ t, w (t+1) = w t + h • ∑ i, q t i • x i)
    (T : ℕ) (hT : ⟪y,w 0⟫ + T*(h*∑ i, max 0 ⟪y,x i⟫) ≤ 0) :
    ¬∀ i, 0 < ⟪x i,w T⟫ := by
  have bound (t : ℕ) : ⟪y,w t⟫ ≤ ⟪y,w 0⟫ + t*(h*∑ i, max 0 ⟪y,x i⟫) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [step]
      have H := capped_motion x y (w t) (q t) (hq t) h hh
      push_cast
      linarith
  have he := (bound T).trans hT
  intro H
  have hi : ∃ i, 0 < α i := by
    by_contra! han
    have hz : ∀ i, α i = 0 := fun i => le_antisymm (han i) (hα i)
    simp [hz] at hα'
  obtain ⟨j,hj⟩ := hi
  rw [hy, sum_inner] at he
  simp only [real_inner_smul_left] at he
  exact (not_lt_of_ge he) (Finset.sum_pos' (fun i _ => mul_nonneg (hα i) (H i).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (H j)⟩)

end LongTails.Proofs.TwoTapLogisticMetric
