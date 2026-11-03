import LongTails.Proofs.TwoSidedPerceptronLinearComparison
import LongTails.Proofs.TwoSidedPerceptronGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronInstances

open LongTails.Setups.TwoSidedConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift ones)
open TwoSampleQuadraticPerceptronEmbedding
open ManySampleConvolutionalPerceptronGeometry (axis_norm)
open TwoSidedPerceptronLinearComparison

lemma iteNeg {α : Type*} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by
  simp [h]

lemma itePos {α : Type*} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

lemma fin_ne {d a b : ℕ} {ha : a < d} {hb : b < d} (h : a ≠ b) : (⟨a, ha⟩ : Fin d) ≠ ⟨b, hb⟩ :=
  fun e => h (congrArg Fin.val e)

noncomputable def unitVector {d : ℕ} (i : Fin d) : Features d := EuclideanSpace.single i 1

noncomputable def base (k : ℕ) : Features (4 * k + 8) :=
  (1 / 8 : ℝ) • (unitVector ⟨0, by omega⟩ - unitVector ⟨1, by omega⟩)

noncomputable def alt (k : ℕ) : Features (4 * k + 8) :=
  (1 / 4 : ℝ) • (unitVector ⟨2, by omega⟩ - unitVector ⟨3, by omega⟩)

noncomputable def priv (k : ℕ) (i : Fin (2 * k + 2)) : Features (4 * k + 8) :=
  (1 / 8 : ℝ) • (unitVector ⟨2 * i.val + 4, by have := i.isLt; omega⟩ -
    unitVector ⟨2 * i.val + 5, by have := i.isLt; omega⟩)

def toSum (k : ℕ) (i : Fin (2 * k + 2)) : Fin (k + 1) ⊕ Fin (k + 1) :=
  if i.val % 2 = 0 then Sum.inl ⟨i.val / 2, by have := i.isLt; omega⟩
  else Sum.inr ⟨i.val / 2, by have := i.isLt; omega⟩

noncomputable def residual (k : ℕ) : Fin (k + 1) ⊕ Fin (k + 1) → Features (4 * k + 8)
  | Sum.inl j => base k + alt k + priv k ⟨2 * j.val, by have := j.isLt; omega⟩
  | Sum.inr j => base k - alt k + priv k ⟨2 * j.val + 1, by have := j.isLt; omega⟩

lemma unit_norm {d : ℕ} (i : Fin d) : ‖unitVector i‖ = 1 := by simp [unitVector]

lemma unit_inner {d : ℕ} (i j : Fin d) : ⟪unitVector i, unitVector j⟫ = if i = j then 1 else 0 := by
  simp [unitVector, EuclideanSpace.inner_single_left]

lemma unit_inner_self {d : ℕ} (i : Fin d) : ⟪unitVector i, unitVector i⟫ = 1 := by
  rw [unit_inner]; simp

lemma unit_inner_ne {d a b : ℕ} {ha : a < d} {hb : b < d} (h : a ≠ b) :
    ⟪unitVector (⟨a, ha⟩ : Fin d), unitVector ⟨b, hb⟩⟫ = 0 := by
  rw [unit_inner, iteNeg (fin_ne h)]

lemma unit_axis_inner {d : ℕ} (i : Fin d) : ⟪axis d, unitVector i⟫ = (Real.sqrt d)⁻¹ := by
  simp [axis, LongTails.Setups.ManySampleConvolutionalPerceptron.axis, unitVector,
    EuclideanSpace.inner_single_right, ones]

lemma unit_coord {d : ℕ} (i j : Fin d) : unitVector i j = if j = i then 1 else 0 := by
  simp [unitVector]

lemma coord_diff {d : ℕ} (a b : ℕ) (ha : a < d) (hb : b < d) (c : ℝ) (j : Fin d) :
    (c • (unitVector (⟨a, ha⟩ : Fin d) - unitVector ⟨b, hb⟩)) j =
      (if j.val = a then c else 0) - (if j.val = b then c else 0) := by
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, unit_coord, Fin.ext_iff]
  split_ifs <;> ring

lemma diff_norm {d : ℕ} {i j : Fin d} (h : i ≠ j) :
    ‖unitVector i - unitVector j‖ = Real.sqrt 2 := by
  have hsq : ‖unitVector i - unitVector j‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, unit_norm, unit_norm, unit_inner, iteNeg h]; norm_num
  have h0 := norm_nonneg (unitVector i - unitVector j)
  rw [← Real.sqrt_sq h0, hsq]

lemma diff_axis {d : ℕ} (i j : Fin d) : ⟪axis d, unitVector i - unitVector j⟫ = 0 := by
  simp only [inner_sub_right, unit_axis_inner, sub_self]

lemma base_norm (k : ℕ) : ‖base k‖ = Real.sqrt 2 / 8 := by
  rw [base, norm_smul, diff_norm (fin_ne (by omega)), Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1 / 8)]; ring

lemma alt_norm (k : ℕ) : ‖alt k‖ = Real.sqrt 2 / 4 := by
  rw [alt, norm_smul, diff_norm (fin_ne (by omega)), Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1 / 4)]; ring

lemma priv_norm (k : ℕ) (i : Fin (2 * k + 2)) : ‖priv k i‖ = Real.sqrt 2 / 8 := by
  rw [priv, norm_smul, diff_norm (fin_ne (by omega)), Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1 / 8)]; ring

lemma residual_norm (k : ℕ) (i : Fin (k + 1) ⊕ Fin (k + 1)) :
    ‖residual k i‖ ≤ (Real.sqrt 2)⁻¹ := by
  have hs := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; nlinarith
  rw [hinv]
  cases i with
  | inl j =>
    simp only [residual]
    calc
      _ ≤ ‖base k + alt k‖ + ‖priv k _‖ := norm_add_le _ _
      _ ≤ ‖base k‖ + ‖alt k‖ + ‖priv k _‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [base_norm, alt_norm, priv_norm]; ring
  | inr j =>
    simp only [residual]
    calc
      _ ≤ ‖base k - alt k‖ + ‖priv k _‖ := norm_add_le _ _
      _ ≤ ‖base k‖ + ‖alt k‖ + ‖priv k _‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by rw [base_norm, alt_norm, priv_norm]; ring

lemma base_centered (k : ℕ) : ⟪axis (4 * k + 8), base k⟫ = 0 := by
  simp only [base, real_inner_smul_right, diff_axis, mul_zero]

lemma alt_centered (k : ℕ) : ⟪axis (4 * k + 8), alt k⟫ = 0 := by
  simp only [alt, real_inner_smul_right, diff_axis, mul_zero]

lemma priv_centered (k : ℕ) (i : Fin (2 * k + 2)) : ⟪axis (4 * k + 8), priv k i⟫ = 0 := by
  simp only [priv, real_inner_smul_right, diff_axis, mul_zero]

lemma residual_centered (k : ℕ) (i : Fin (k + 1) ⊕ Fin (k + 1)) :
    ⟪axis (4 * k + 8), residual k i⟫ = 0 := by
  cases i <;> simp only [residual, inner_add_right, inner_sub_right, base_centered, alt_centered,
    priv_centered, add_zero, sub_zero]

noncomputable def family (k : ℕ) : Family (Features (4 * k + 8)) (k + 1) where
  e := axis (4 * k + 8)
  u := residual k
  e_unit := axis_norm (by omega)
  centered := residual_centered k
  u_norm := residual_norm k

noncomputable def dataset (k : ℕ) (μ : ℝ) : Data (4 * k + 8) (2 * k + 1) := fun i =>
  sample (family k) μ (toSum k i)

noncomputable def params (k : ℕ) (μ : ℝ) : Params :=
  ⟨4 * k + 8, 2 * k + 1, 1, 1 + μ, μ, 1 / 6⟩

section Coordinates

variable (k : ℕ)

lemma residual_zero (i : Fin (k + 1) ⊕ Fin (k + 1)) : residual k i ⟨0, by omega⟩ = 1 / 8 := by
  cases i <;> simp only [residual, base, alt, priv, PiLp.add_apply, PiLp.sub_apply, coord_diff] <;>
    split_ifs <;> first | contradiction | omega | norm_num

lemma residual_one (i : Fin (k + 1) ⊕ Fin (k + 1)) : residual k i ⟨1, by omega⟩ = -1 / 8 := by
  cases i <;> simp only [residual, base, alt, priv, PiLp.add_apply, PiLp.sub_apply, coord_diff] <;>
    split_ifs <;> first | contradiction | omega | norm_num

lemma rotate_one : (finRotate (4 * k + 8)).symm ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  apply Fin.ext
  have hj : (⟨1, by omega⟩ : Fin (4 * k + 8)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  rw [coe_finRotate_symm_of_ne_zero hj]
  rfl

lemma derivative_margin (i : Fin (k + 1) ⊕ Fin (k + 1)) :
    (1 / 6 : ℝ) ≤ ⟪derivative (residual k i), -unitVector ⟨1, by omega⟩⟫ := by
  have hcoord : (derivative (residual k i)) ⟨1, by omega⟩ = -(Real.sqrt 2)⁻¹ / 4 := by
    simp only [derivative, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, shift_apply, rotate_one]
    rw [residual_one, residual_zero]; ring
  have hinner : ⟪derivative (residual k i), -unitVector ⟨1, by omega⟩⟫ =
      -((derivative (residual k i)) ⟨1, by omega⟩) := by
    rw [inner_neg_right, unitVector, EuclideanSpace.inner_single_right]
    simp
  rw [hinner, hcoord]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have : (2 / 3 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]; linarith
  linarith

end Coordinates

noncomputable def geometry (k : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    Geometry (dataset k μ) 1 (1 + μ) μ (1 / 6) where
  background i := weight μ (toSum k i)
  defect i := residual k (toSum k i)
  separator := -unitVector ⟨1, by omega⟩
  sample_eq i := rfl
  background_lower i := by
    cases toSum k i with
    | inl j => simp [weight]
    | inr j =>
      simp only [weight, abs_neg]
      rw [abs_of_nonneg (by linarith)]; linarith
  background_upper i := by
    cases toSum k i with
    | inl j => simp only [weight, abs_one]; linarith
    | inr j =>
      simp only [weight, abs_neg]
      rw [abs_of_nonneg (by linarith)]
  centered i := residual_centered k _
  defect_norm i := residual_norm k _
  separator_unit := by rw [norm_neg, unit_norm]
  derivative_margin i := derivative_margin k _

section Gram

variable (k : ℕ)

lemma inner_diff_diff (a b c d : ℕ) (ha : a < 4 * k + 8) (hb : b < 4 * k + 8)
    (hc : c < 4 * k + 8) (hd : d < 4 * k + 8) (x y : ℝ)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ⟪x • (unitVector (⟨a, ha⟩ : Fin (4 * k + 8)) - unitVector ⟨b, hb⟩),
      y • (unitVector (⟨c, hc⟩ : Fin (4 * k + 8)) - unitVector ⟨d, hd⟩)⟫ = 0 := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    unit_inner_ne hac, unit_inner_ne had, unit_inner_ne hbc, unit_inner_ne hbd]
  ring

lemma inner_diff_self (a b : ℕ) (ha : a < 4 * k + 8) (hb : b < 4 * k + 8) (x : ℝ) (hab : a ≠ b) :
    ⟪x • (unitVector (⟨a, ha⟩ : Fin (4 * k + 8)) - unitVector ⟨b, hb⟩),
      x • (unitVector (⟨a, ha⟩ : Fin (4 * k + 8)) - unitVector ⟨b, hb⟩)⟫ = 2 * x ^ 2 := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    unit_inner_ne hab, unit_inner_ne (Ne.symm hab), unit_inner_self]
  ring

lemma gram_cross (j j' : Fin (k + 1)) :
    ⟪residual k (Sum.inl j), residual k (Sum.inr j')⟫ < 0 := by
  have hb : ⟪base k, base k⟫ = 1 / 32 := by
    unfold base; rw [inner_diff_self k 0 1 (by omega) (by omega) _ (by omega)]; norm_num
  have ha : ⟪alt k, alt k⟫ = 1 / 8 := by
    unfold alt; rw [inner_diff_self k 2 3 (by omega) (by omega) _ (by omega)]; norm_num
  have hba : ⟪base k, alt k⟫ = 0 := by
    unfold base alt
    exact inner_diff_diff k 0 1 2 3 _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hab : ⟪alt k, base k⟫ = 0 := by rw [real_inner_comm]; exact hba
  have hbp : ∀ i, ⟪base k, priv k i⟫ = 0 := fun i => by
    unfold base priv
    exact inner_diff_diff k 0 1 _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hpb : ∀ i, ⟪priv k i, base k⟫ = 0 := fun i => by rw [real_inner_comm]; exact hbp i
  have hap : ∀ i, ⟪alt k, priv k i⟫ = 0 := fun i => by
    unfold alt priv
    exact inner_diff_diff k 2 3 _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hpa : ∀ i, ⟪priv k i, alt k⟫ = 0 := fun i => by rw [real_inner_comm]; exact hap i
  have hpp : ⟪priv k ⟨2 * j.val, by have := j.isLt; omega⟩,
      priv k ⟨2 * j'.val + 1, by have := j'.isLt; omega⟩⟫ = 0 := by
    simp only [priv]
    exact inner_diff_diff k _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  simp only [residual, inner_add_left, inner_add_right, inner_sub_right, hb, ha,
    hba, hab, hbp, hpb, hap, hpa, hpp]
  norm_num

end Gram

lemma residual_toSum (k : ℕ) (i' : Fin (2 * k + 2)) :
    residual k (toSum k i') =
      base k + (if i'.val % 2 = 0 then alt k else -alt k) + priv k i' := by
  unfold toSum
  by_cases h : i'.val % 2 = 0
  · rw [itePos h, itePos h]
    simp only [residual]
    congr 1
    exact congrArg (priv k) (Fin.ext (by show 2 * (i'.val / 2) = i'.val; omega))
  · rw [iteNeg h, iteNeg h]
    simp only [residual, sub_eq_add_neg]
    congr 1
    exact congrArg (priv k) (Fin.ext (by show 2 * (i'.val / 2) + 1 = i'.val; omega))

lemma residual_coordinate (k : ℕ) (i i' : Fin (2 * k + 2)) :
    residual k (toSum k i') ⟨2 * i.val + 4, by have := i.isLt; omega⟩ =
      if i = i' then 1 / 8 else 0 := by
  have hb : base k ⟨2 * i.val + 4, by have := i.isLt; omega⟩ = 0 := by
    simp only [base, coord_diff]
    rw [iteNeg (by omega), iteNeg (by omega)]; ring
  have ha : alt k ⟨2 * i.val + 4, by have := i.isLt; omega⟩ = 0 := by
    simp only [alt, coord_diff]
    rw [iteNeg (by omega), iteNeg (by omega)]; ring
  have ha' : (if i'.val % 2 = 0 then alt k else -alt k) ⟨2 * i.val + 4, by have := i.isLt; omega⟩
      = 0 := by
    split_ifs
    · exact ha
    · rw [PiLp.neg_apply, ha, neg_zero]
  have hpriv : priv k i' ⟨2 * i.val + 4, by have := i.isLt; omega⟩ =
      if i = i' then 1 / 8 else 0 := by
    simp only [priv, coord_diff]
    rw [iteNeg (by omega : ¬ (2 * i.val + 4 = 2 * i'.val + 5)), sub_zero]
    by_cases h : i = i'
    · subst h; simp
    · rw [iteNeg h, iteNeg (fun e => h (Fin.ext (by omega)))]
  rw [residual_toSum, PiLp.add_apply, PiLp.add_apply, hb, ha', hpriv, zero_add, zero_add]

lemma residual_independent (k : ℕ) :
    LinearIndependent ℝ (fun i : Fin (2 * k + 2) => residual k (toSum k i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hi := congrArg (fun x : Features (4 * k + 8) => x ⟨2 * i.val + 4, by have := i.isLt; omega⟩) ha
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hi
  simp_rw [residual_coordinate] at hi
  simp only [mul_ite, mul_zero] at hi
  simp at hi
  linarith

lemma dataset_visit (k : ℕ) (μ : ℝ) (t : ℕ) :
    dataset k μ ⟨t % (2 * k + 2), Nat.mod_lt _ (by omega)⟩ =
      sample (family k) μ (visit (k + 1) (by omega) t) := by
  unfold dataset visit toSum
  have h1 : t % (2 * k + 2) % 2 = t % 2 := Nat.mod_mod_of_dvd t ⟨k + 1, by ring⟩
  have h2 : t % (2 * k + 2) / 2 = t / 2 % (k + 1) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring]; exact Nat.mod_mul_right_div_self t 2 (k + 1)
  simp only [h1, h2]

lemma params_valid (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ48 : μ ≤ 1 / 2 ^ 48) :
    spec.valid (params k μ) := by
  have hμ1 : μ ≤ 1 := by
    have : (1 : ℝ) / 2 ^ 48 ≤ 1 := by norm_num
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < 4 * k + 8; omega
  · show (0 : ℝ) < 1; norm_num
  · show (1 : ℝ) ≤ 1 + μ; linarith
  · exact hμ
  · show (0 : ℝ) < 1 / 6; norm_num
  · show (1 / 6 : ℝ) * μ * ⌈2 ^ 24 * ((1 + μ) / 1) ^ 2 * (1 + Real.log (1 + 1 / μ)) / (1 / 6) ^ 3⌉₊ ≤
      3 * (1 + μ) / 2
    set L := Real.log (1 + 1 / μ) with hL
    have hμinv : 0 ≤ 1 / μ := by positivity
    have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
    set y := (2 : ℝ) ^ 24 * ((1 + μ) / 1) ^ 2 * (1 + L) / (1 / 6) ^ 3 with hy
    have hy0 : 0 ≤ y := by positivity
    have hceil : (⌈y⌉₊ : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hy0).le
    have hy1 : 0 < 1 + 1 / μ := by positivity
    set r := Real.sqrt (Real.sqrt (1 + 1 / μ)) with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hy1)
    have hr4 : r ^ 4 = 1 + 1 / μ := by
      have h1 : r ^ 2 = Real.sqrt (1 + 1 / μ) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have h2 : (Real.sqrt (1 + 1 / μ)) ^ 2 = 1 + 1 / μ := Real.sq_sqrt hy1.le
      calc r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ = _ := by rw [h1, h2]
    have hlogr : L = 4 * Real.log r := by
      rw [hL, ← hr4, Real.log_pow]; push_cast; ring
    have hLr : L ≤ 4 * r := by
      rw [hlogr]
      have := Real.log_le_sub_one_of_pos hrpos
      linarith
    have hμr : μ * r ≤ 1 / 2 ^ 35 := by
      have h4 : (μ * r) ^ 4 ≤ (1 / 2 ^ 35) ^ 4 := by
        rw [mul_pow, hr4]
        have e : μ ^ 4 * (1 + 1 / μ) = μ ^ 4 + μ ^ 3 := by field_simp; try ring
        rw [e]
        have hμ3 : μ ^ 3 ≤ (1 / 2 ^ 48) ^ 3 := pow_le_pow_left₀ hμ.le hμ48 3
        have hμ4 : μ ^ 4 ≤ (1 / 2 ^ 48) ^ 4 := pow_le_pow_left₀ hμ.le hμ48 4
        have hnum : ((1 : ℝ) / 2 ^ 48) ^ 4 + (1 / 2 ^ 48) ^ 3 ≤ (1 / 2 ^ 35) ^ 4 := by norm_num
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h4
    have hμL : μ * L ≤ 4 * (1 / 2 ^ 35) := by
      have := mul_le_mul_of_nonneg_left hLr hμ.le
      linarith
    have hyμ : μ * y ≤ 7247757312 * (μ + μ * L) := by
      have e : y = 3623878656 * (1 + μ) ^ 2 * (1 + L) := by rw [hy]; ring
      rw [e]
      have h1 : (1 + μ) ^ 2 ≤ 2 := by nlinarith
      have h2 : 0 ≤ μ * (1 + L) := by positivity
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      have e2 : μ * (3623878656 * (1 + μ) ^ 2 * (1 + L)) =
          3623878656 * ((1 + μ) ^ 2 * (μ * (1 + L))) := by ring
      rw [e2]
      linarith [h3]
    have hsum : μ + μ * L ≤ 5 * (1 / 2 ^ 35) := by
      have : (1 : ℝ) / 2 ^ 48 ≤ 1 / 2 ^ 35 := by norm_num
      linarith
    have hprod : (7247757312 : ℝ) * (μ + μ * L) ≤ 7247757312 * (5 * (1 / 2 ^ 35)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    have hnum : (7247757312 : ℝ) * (5 * (1 / 2 ^ 35)) ≤ 2 := by norm_num
    have hfinal : 1 / 6 * μ * (y + 1) ≤ 3 * (1 + μ) / 2 := by
      have e : 1 / 6 * μ * (y + 1) = (μ * y + μ) / 6 := by ring
      rw [e]
      linarith
    calc 1 / 6 * μ * (⌈y⌉₊ : ℝ) ≤ 1 / 6 * μ * (y + 1) := by gcongr
      _ ≤ _ := hfinal

end LongTails.Proofs.TwoSidedPerceptronInstances
