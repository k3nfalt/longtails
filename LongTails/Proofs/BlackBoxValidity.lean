import LongTails.Algorithms.BlackBoxDiagonalAccelerated
import LongTails.Proofs.MetricAcceleratedStep

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.BlackBoxDiagonal

open OracleTemplate.OnlineMetricAccelerated (inner_eq_sum secant_bounds)

variable {d : ℕ}

structure BHyp (f : Vec d → ℝ) (w : Fin d → ℝ) (μ : ℝ) : Prop where
  w_pos : ∀ i, 0 < w i
  μ_pos : 0 < μ
  μ_le : μ ≤ 1
  smooth : ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + (∑ i, w i * (y i - x i) ^ 2) / 2
  sc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ * (∑ i, w i * (y i - x i) ^ 2) / 2 ≤ f y

lemma dot_eq_inner (g v : Vec d) : dot g v = ⟪g, v⟫ := (inner_eq_sum g v).symm

namespace BHyp

variable {f : Vec d → ℝ} {w : Fin d → ℝ} {μ : ℝ}

lemma conv (H : BHyp f w μ) (x y : Vec d) : f x + dot (gradient f x) (y - x) ≤ f y := by
  rw [dot_eq_inner]
  have h := H.sc x y
  have : 0 ≤ μ * (∑ i, w i * (y i - x i) ^ 2) / 2 :=
    div_nonneg (mul_nonneg H.μ_pos.le
      (Finset.sum_nonneg fun i _ => mul_nonneg (H.w_pos i).le (sq_nonneg _))) (by norm_num)
  linarith

lemma smooth_m (H : BHyp f w μ) {m : Fin d → ℝ} (hm : ∀ i, w i ≤ m i) (x y : Vec d) :
    f y ≤ f x + dot (gradient f x) (y - x) + (∑ i, m i * (y i - x i) ^ 2) / 2 := by
  rw [dot_eq_inner]
  have h := H.smooth x y
  have : ∑ i, w i * (y i - x i) ^ 2 ≤ ∑ i, m i * (y i - x i) ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (sq_nonneg _)
  linarith

lemma cocoercive (H : BHyp f w μ) {m : Fin d → ℝ} (hm : ∀ i, w i ≤ m i) (x y : Vec d) :
    (∑ i, (gradient f y i - gradient f x i) ^ 2 / m i) / 2 ≤
      f y - f x - dot (gradient f x) (y - x) := by
  have hmpos : ∀ i, 0 < m i := fun i => lt_of_lt_of_le (H.w_pos i) (hm i)
  set Δ : Vec d := gradient f y - gradient f x
  set u : Vec d := WithLp.toLp 2 (fun i => y i - Δ i / m i)
  have h1 := H.smooth_m hm y u
  have h2 := H.conv x u
  have e1 : dot (gradient f y) (u - y) = -∑ i, gradient f y i * Δ i / m i := by
    unfold dot; rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u, PiLp.sub_apply]; ring
  have e2 : ∑ i, m i * (u i - y i) ^ 2 = ∑ i, Δ i ^ 2 / m i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u]
    have := (hmpos i).ne'
    field_simp
    ring
  have e3 : dot (gradient f x) (u - x) = dot (gradient f x) (y - x) -
      ∑ i, gradient f x i * Δ i / m i := by
    unfold dot; rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u, PiLp.sub_apply]; ring
  have e4 : ∑ i, gradient f y i * Δ i / m i - ∑ i, gradient f x i * Δ i / m i =
      ∑ i, Δ i ^ 2 / m i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Δ, PiLp.sub_apply]; ring
  have e5 : ∑ i, (gradient f y i - gradient f x i) ^ 2 / m i = ∑ i, Δ i ^ 2 / m i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Δ, PiLp.sub_apply]
  rw [e5]
  rw [e1, e2] at h1
  rw [e3] at h2
  linarith

lemma sc_m (H : BHyp f w μ) {m : Fin d → ℝ} {μ' : ℝ} (hμ' : 0 ≤ μ') (hμμ : 4 * μ' ≤ μ)
    (hm : ∀ i, m i ≤ 4 * w i) (x y : Vec d) :
    μ' / 2 * ∑ i, m i * (y i - x i) ^ 2 ≤ f y - f x - dot (gradient f x) (y - x) := by
  rw [dot_eq_inner]
  have h := H.sc x y
  have hs : ∑ i, m i * (y i - x i) ^ 2 ≤ 4 * ∑ i, w i * (y i - x i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [hm i, sq_nonneg (y i - x i)]
  have hw : 0 ≤ ∑ i, w i * (y i - x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (H.w_pos i).le (sq_nonneg _)
  have := mul_le_mul_of_nonneg_left hs hμ'
  nlinarith

end BHyp

lemma exp_neg_eq (θ : Fin d → ℝ) (k : Fin d) : Real.exp (-θ k) = 1 / metric θ k := by
  rw [Real.exp_neg, metric, inv_eq_one_div]

lemma metric_pos (θ : Fin d → ℝ) (k : Fin d) : 0 < metric θ k := Real.exp_pos _

lemma cutCoco_val (fy fx : ℝ) (y x gy gx : Vec d) (θ : Fin d → ℝ) :
    (cutCoco fy fx y x gy gx).val θ =
      (∑ i, (gx i - gy i) ^ 2 / metric θ i) / 2 - (fy - fx - dot gx (y - x)) := by
  unfold Cut.val cutCoco
  simp only [zero_mul, Finset.sum_const_zero, add_zero, exp_neg_eq]
  rw [Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

lemma cutSc_val (μ fy fx : ℝ) (y x gx : Vec d) (θ : Fin d → ℝ) :
    (cutSc μ fy fx y x gx).val θ =
      μ / 2 * ∑ i, metric θ i * (y i - x i) ^ 2 - (fy - fx - dot gx (y - x)) := by
  unfold Cut.val cutSc
  simp only [zero_mul, Finset.sum_const_zero, zero_add]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by unfold metric; ring

lemma cutMono_val (μ : ℝ) (x y gx gy : Vec d) (θ : Fin d → ℝ) :
    (cutMono μ x y gx gy).val θ =
      μ * ∑ i, metric θ i * (x i - y i) ^ 2 - dot (gx - gy) (x - y) := by
  unfold Cut.val cutMono
  simp only [zero_mul, Finset.sum_const_zero, zero_add]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by unfold metric; ring

lemma cutCocoMono_val (x y gx gy : Vec d) (θ : Fin d → ℝ) :
    (cutCocoMono x y gx gy).val θ =
      ∑ i, (gx i - gy i) ^ 2 / metric θ i - dot (gx - gy) (x - y) := by
  unfold Cut.val cutCocoMono
  simp only [zero_mul, Finset.sum_const_zero, add_zero, exp_neg_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

namespace BHyp

variable {f : Vec d → ℝ} {w : Fin d → ℝ} {μ : ℝ}

lemma valid_coco (H : BHyp f w μ) {θ : Fin d → ℝ} (hm : ∀ i, w i ≤ metric θ i) (x y : Vec d) :
    (cutCoco (f y) (f x) y x (gradient f y) (gradient f x)).val θ ≤ 0 := by
  rw [cutCoco_val]
  have := H.cocoercive hm x y
  have e : ∑ i, (gradient f x i - gradient f y i) ^ 2 / metric θ i =
      ∑ i, (gradient f y i - gradient f x i) ^ 2 / metric θ i :=
    Finset.sum_congr rfl fun i _ => by ring
  linarith

lemma valid_sc (H : BHyp f w μ) {θ : Fin d → ℝ} {μ' : ℝ} (hμ' : 0 ≤ μ') (hμμ : 4 * μ' ≤ μ)
    (hm : ∀ i, metric θ i ≤ 4 * w i) (x y : Vec d) :
    (cutSc μ' (f y) (f x) y x (gradient f x)).val θ ≤ 0 := by
  rw [cutSc_val]
  have := H.sc_m hμ' hμμ hm x y
  linarith

lemma valid_mono (H : BHyp f w μ) {θ : Fin d → ℝ} {μ' : ℝ} (hμ' : 0 ≤ μ') (hμμ : 4 * μ' ≤ μ)
    (hm : ∀ i, metric θ i ≤ 4 * w i) (x y : Vec d) :
    (cutMono μ' x y (gradient f x) (gradient f y)).val θ ≤ 0 := by
  rw [cutMono_val]
  have h1 := H.sc_m hμ' hμμ hm x y
  have h2 := H.sc_m hμ' hμμ hm y x
  have e1 : ∑ i, metric θ i * (y i - x i) ^ 2 = ∑ i, metric θ i * (x i - y i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have e2 : dot (gradient f x - gradient f y) (x - y) =
      -dot (gradient f x) (y - x) - dot (gradient f y) (x - y) := by
    unfold dot
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]; ring
  rw [e1] at h1
  linarith

lemma valid_cocomono (H : BHyp f w μ) {θ : Fin d → ℝ} (hm : ∀ i, w i ≤ metric θ i)
    (x y : Vec d) :
    (cutCocoMono x y (gradient f x) (gradient f y)).val θ ≤ 0 := by
  rw [cutCocoMono_val]
  have h1 := H.cocoercive hm x y
  have h2 := H.cocoercive hm y x
  have e1 : ∑ i, (gradient f x i - gradient f y i) ^ 2 / metric θ i =
      ∑ i, (gradient f y i - gradient f x i) ^ 2 / metric θ i :=
    Finset.sum_congr rfl fun i _ => by ring
  have e2 : dot (gradient f x - gradient f y) (x - y) =
      -dot (gradient f x) (y - x) - dot (gradient f y) (x - y) := by
    unfold dot
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]; ring
  rw [e1] at h2 ⊢
  linarith

end BHyp

lemma ball_metric {w θ : Fin d → ℝ} (hw : ∀ i, 0 < w i)
    (hball : sqn (fun k => θ k - (Real.log (w k) + Real.log 2)) ≤ Real.log 2 ^ 2) (i : Fin d) :
    w i ≤ metric θ i ∧ metric θ i ≤ 4 * w i := by
  have hi : (θ i - (Real.log (w i) + Real.log 2)) ^ 2 ≤ Real.log 2 ^ 2 :=
    le_trans (Finset.single_le_sum (f := fun k => (θ k - (Real.log (w k) + Real.log 2)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)) hball
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have habs := abs_le_of_sq_le_sq' hi hl2.le
  unfold metric
  constructor
  · have : Real.log (w i) ≤ θ i := by linarith [habs.1]
    calc w i = Real.exp (Real.log (w i)) := (Real.exp_log (hw i)).symm
      _ ≤ Real.exp (θ i) := Real.exp_le_exp.mpr this
  · have : θ i ≤ Real.log (4 * w i) := by
      rw [Real.log_mul (by norm_num) (hw i).ne', show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.log_pow]
      push_cast
      linarith [habs.2]
    calc Real.exp (θ i) ≤ Real.exp (Real.log (4 * w i)) := Real.exp_le_exp.mpr this
      _ = 4 * w i := Real.exp_log (by have := hw i; positivity)

end OracleTemplate.BlackBoxDiagonal
