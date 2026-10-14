import LongTails.Algorithms.TerminalClipping
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

lemma confidence_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (8 / δ) := by
  apply Real.log_pos
  rw [lt_div_iff₀ hδ]
  linarith

lemma confidence_ge_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ Real.log (8 / δ) := by
  have h2 := Real.log_two_gt_d9
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h8 : (8 : ℝ) ≤ 8 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8
  rw [he] at hh
  linarith

lemma stepSize_pos {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) : 0 < stepSize B δ T t := by
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hm : 0 < ((T - t : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt ht)
  have hq := confidence_pos hδ hδ1
  unfold stepSize
  positivity

lemma weight_bounds {T t : ℕ} (ht : t < T) :
    (1 : ℝ) / 2 ≤ weight T t ∧ weight T t ≤ 1 := by
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hs : ((t + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast ht
  unfold weight
  have hd : 0 < 2 * (T : ℝ) := by positivity
  have hupper : ((t + 1 : ℕ) : ℝ) / (2 * T) ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hlower : 0 ≤ ((t + 1 : ℕ) : ℝ) / (2 * T) := by positivity
  constructor <;> linarith

lemma weight_terminal_nonneg {T : ℕ} (hT : 0 < T) : 0 ≤ weight T T := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  unfold weight
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * (T : ℝ))).mpr
  push_cast
  linarith

lemma weight_difference (T t : ℕ) :
    weight T (t + 1) - weight T t = -1 / (2 * (T : ℝ)) := by
  unfold weight
  push_cast
  ring

lemma tailWeight_pos {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) : 0 < tailWeight B δ T t := by
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hm : (1 : ℝ) ≤ (T - t : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt ht)
  have hf : 0 < 3 * (T : ℝ) + 2 * (T - t : ℕ) - 2 := by linarith
  have hq := confidence_pos hδ hδ1
  unfold tailWeight
  dsimp
  positivity

lemma tailWeight_lower {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) :
    ((T - t : ℕ) : ℝ) ^ 2 /
      (4 * T * (4096 * B * Real.sqrt T * Real.log (8 / δ))) ≤ tailWeight B δ T t := by
  let m : ℝ := (T - t : ℕ)
  let D := 4096 * B * Real.sqrt T * Real.log (8 / δ)
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (Nat.sub_pos_of_lt ht)
  have hq := confidence_pos hδ hδ1
  have hD : 0 < D := by dsimp [D]; positivity
  have h1 : m ^ 2 ≤ m * (m + 1) := by nlinarith
  have h2 : 3 * (T : ℝ) ≤ 3 * T + 2 * m - 2 := by linarith
  have hp := mul_le_mul h1 h2 (by positivity : 0 ≤ 3 * (T : ℝ)) (by positivity : 0 ≤ m * (m + 1))
  have hd : 0 < 12 * (T : ℝ) ^ 2 * D := by positivity
  have hh := div_le_div_of_nonneg_right hp hd.le
  change m ^ 2 / (4 * T * D) ≤ m * (m + 1) * (3 * T + 2 * m - 2) / (12 * (T : ℝ) ^ 2 * D)
  calc
    _ = (m ^ 2 * (3 * T)) / (12 * (T : ℝ) ^ 2 * D) := by field_simp; ring
    _ ≤ _ := hh

lemma tailWeight_terminal (B δ : ℝ) (T : ℕ) : tailWeight B δ T T = 0 := by
  simp [tailWeight]

lemma tailWeight_step (B δ : ℝ) {T t : ℕ} (ht : t < T) :
    tailWeight B δ T t - tailWeight B δ T (t + 1) =
      weight T t * stepSize B δ T t := by
  have hT : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt ht)
  have ht' : t ≤ T := ht.le
  have hs : t + 1 ≤ T := ht
  unfold tailWeight weight stepSize
  push_cast [Nat.cast_sub ht', Nat.cast_sub hs]
  by_cases h : 4096 * B * Real.sqrt T * Real.log (8 / δ) = 0
  · simp [h]
  · field_simp
    ring

lemma tailWeight_sum (B δ : ℝ) {T t : ℕ} (ht : t ≤ T) :
    tailWeight B δ T t =
      ∑ s ∈ Finset.Ico t T, weight T s * stepSize B δ T s := by
  induction ht using Nat.decreasingInduction with
  | self => simp [tailWeight_terminal]
  | of_succ t hlt ih =>
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ← ih]
    linarith [tailWeight_step B δ hlt]

lemma tailWeight_prev_ge {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) : tailWeight B δ T t ≤ tailWeight B δ T (t - 1) := by
  by_cases hz : t = 0
  · subst t
    rfl
  · have hp : t - 1 < T := by omega
    have hs := tailWeight_step B δ hp
    rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at hs
    have hw : 0 ≤ weight T (t - 1) := by linarith [(weight_bounds hp).1]
    have he := (stepSize_pos hB hδ hδ1 hp).le
    nlinarith [mul_nonneg hw he]

lemma influenceScale_bound {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) :
    influenceScale B δ T t ≤ 4 / ((T - t : ℕ) : ℝ) := by
  let m : ℝ := (T - t : ℕ)
  let D := 4096 * B * Real.sqrt T * Real.log (8 / δ)
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (Nat.sub_pos_of_lt ht)
  have hq := confidence_pos hδ hδ1
  have hD : 0 < D := by dsimp [D]; positivity
  have hS := tailWeight_pos hB hδ hδ1 (show t - 1 < T by omega)
  have hl := (tailWeight_lower hB hδ hδ1 ht).trans (tailWeight_prev_ge hB hδ hδ1 ht)
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 4 / m by positivity)
  have he : 4 / m * (m ^ 2 / (4 * T * D)) = stepSize B δ T t := by
    unfold stepSize
    change 4 / m * (m ^ 2 / (4 * T * D)) = m / (D * T)
    field_simp
  change 4 / m * (m ^ 2 / (4 * T * D)) ≤ _ at hh
  rw [he] at hh
  unfold influenceScale
  apply (div_le_iff₀ hS).mpr
  have hw := mul_le_mul_of_nonneg_right (weight_bounds ht).2
    (stepSize_pos hB hδ hδ1 ht).le
  have hw' : weight T t * stepSize B δ T t ≤ stepSize B δ T t := by
    simpa only [one_mul] using hw
  exact hw'.trans hh

lemma step_influenceScale_bound {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) :
    stepSize B δ T t * influenceScale B δ T t ≤
      4 / (4096 * B * Real.sqrt T * Real.log (8 / δ) * T) := by
  have hm : ((T - t : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (Nat.sub_pos_of_lt ht))
  have hh := mul_le_mul_of_nonneg_left (influenceScale_bound hB hδ hδ1 ht)
    (stepSize_pos hB hδ hδ1 ht).le
  apply hh.trans_eq
  unfold stepSize
  field_simp

lemma comparator_ratio_bounds {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) :
    0 ≤ tailWeight B δ T t / tailWeight B δ T (t - 1) ∧
      tailWeight B δ T t / tailWeight B δ T (t - 1) ≤ 1 := by
  have hs := tailWeight_pos hB hδ hδ1 ht
  have hp := tailWeight_pos hB hδ hδ1 (show t - 1 < T by omega)
  exact ⟨div_nonneg hs.le hp.le, (div_le_one hp).mpr (tailWeight_prev_ge hB hδ hδ1 ht)⟩

lemma nextAuxiliary_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) {r : ℝ} {x p : E} (hx : ‖x‖ ≤ r) (hp : ‖p‖ ≤ r) :
    ‖nextAuxiliary B δ T t x p‖ ≤ r := by
  let a := tailWeight B δ T t / tailWeight B δ T (t - 1)
  have ha := (comparator_ratio_bounds hB hδ hδ1 ht).1
  have hb : 0 ≤ 1 - a := by dsimp [a]; linarith [(comparator_ratio_bounds hB hδ hδ1 ht).2]
  change ‖a • p + (1 - a) • x‖ ≤ r
  calc
    _ ≤ ‖a • p‖ + ‖(1 - a) • x‖ := norm_add_le _ _
    _ = a * ‖p‖ + (1 - a) * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + (1 - a) * r := add_le_add
      (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hx hb)
    _ = r := by ring

lemma stepSize_after (B δ : ℝ) {T t : ℕ} (ht : T ≤ t) : stepSize B δ T t = 0 := by
  simp [stepSize, Nat.sub_eq_zero_of_le ht]

lemma tailWeight_after (B δ : ℝ) {T t : ℕ} (ht : T ≤ t) : tailWeight B δ T t = 0 := by
  simp [tailWeight, Nat.sub_eq_zero_of_le ht]

lemma influenceScale_after (B δ : ℝ) {T t : ℕ} (ht : T ≤ t) :
    influenceScale B δ T t = 0 := by simp [influenceScale, stepSize_after B δ ht]

lemma nextAuxiliary_after {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B δ : ℝ) {T t : ℕ} (ht : T ≤ t) (x p : E) : nextAuxiliary B δ T t x p = x := by
  simp [nextAuxiliary, tailWeight_after B δ ht]

lemma stepSize_le_base {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (hT : 0 < T) :
    stepSize B δ T t ≤ 1 / (4096 * B * Real.sqrt T * Real.log (8 / δ)) := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hq := confidence_pos hδ hδ1
  let D := 4096 * B * Real.sqrt T * Real.log (8 / δ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hm : ((T - t : ℕ) : ℝ) ≤ T := by exact_mod_cast (Nat.sub_le T t)
  change ((T - t : ℕ) : ℝ) / (D * T) ≤ 1 / D
  apply (div_le_iff₀ (by positivity : 0 < D * T)).mpr
  have he : 1 / D * (D * T) = T := by field_simp
  rw [he]
  exact hm

lemma influenceScale_nonneg {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) : 0 ≤ influenceScale B δ T t := by
  have hw : 0 ≤ weight T t := by linarith [(weight_bounds ht).1]
  have he := (stepSize_pos hB hδ hδ1 ht).le
  have hs := (tailWeight_pos hB hδ hδ1 (show t - 1 < T by omega)).le
  unfold influenceScale
  positivity

lemma squared_step_weight_bound {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) :
    weight T t * (stepSize B δ T t) ^ 2 / tailWeight B δ T t ≤
      4 / (4096 * B * Real.sqrt T * Real.log (8 / δ) * T) := by
  let D := 4096 * B * Real.sqrt T * Real.log (8 / δ)
  let m : ℝ := (T - t : ℕ)
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (Nat.sub_pos_of_lt ht)
  have hq := confidence_pos hδ hδ1
  have hD : 0 < D := by dsimp [D]; positivity
  have hl := tailWeight_lower hB hδ hδ1 ht
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 4 / (D * T) by positivity)
  have he : 4 / (D * T) * (m ^ 2 / (4 * T * D)) = (stepSize B δ T t) ^ 2 := by
    unfold stepSize
    change 4 / (D * T) * (m ^ 2 / (4 * T * D)) = (m / (D * T)) ^ 2
    field_simp

  change 4 / (D * T) * (m ^ 2 / (4 * T * D)) ≤ _ at hh
  rw [he] at hh
  apply (div_le_iff₀ (tailWeight_pos hB hδ hδ1 ht)).mpr
  exact (mul_le_mul_of_nonneg_right (weight_bounds ht).2 (sq_nonneg _)).trans
    (by simpa only [one_mul, D] using hh)

lemma initial_tailWeight_lower {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T : ℕ} (hT : 0 < T) :
    (T : ℝ) / (4 * (4096 * B * Real.sqrt T * Real.log (8 / δ))) ≤ tailWeight B δ T 0 := by
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hT)
  have hh := tailWeight_lower hB hδ hδ1 hT
  simp only [Nat.sub_zero] at hh
  convert hh using 1; field_simp

lemma optimizer_influence_bound {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) :
    weight T t * stepSize B δ T t / tailWeight B δ T 0 ≤ 4 / (T : ℝ) := by
  have hT : 0 < T := Nat.zero_lt_of_lt ht
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hq := confidence_pos hδ hδ1
  have hden : 4096 * B * Real.sqrt T * Real.log (8 / δ) ≠ 0 := by positivity
  have hh := mul_le_mul_of_nonneg_left (initial_tailWeight_lower hB hδ hδ1 hT)
    (show 0 ≤ 4 / (T : ℝ) by positivity)
  have he : 4 / (T : ℝ) * (T / (4 * (4096 * B * Real.sqrt T * Real.log (8 / δ)))) =
      1 / (4096 * B * Real.sqrt T * Real.log (8 / δ)) := by field_simp
  rw [he] at hh
  apply (div_le_iff₀ (tailWeight_pos hB hδ hδ1 hT)).mpr
  have hw := mul_le_mul_of_nonneg_right (weight_bounds ht).2 (stepSize_pos hB hδ hδ1 ht).le
  have hw' : weight T t * stepSize B δ T t ≤ stepSize B δ T t := by simpa only [one_mul] using hw
  exact hw'.trans ((stepSize_le_base hB hδ hδ1 hT).trans hh)

lemma negative_potential_bound {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) :
    (4096 * B * Real.sqrt T * Real.log (8 / δ)) / 16 * (influenceScale B δ T t) ^ 2 ≤
      1 / (4 * T * tailWeight B δ T (t - 1)) := by
  let D := 4096 * B * Real.sqrt T * Real.log (8 / δ)
  let S := tailWeight B δ T (t - 1)
  let a := influenceScale B δ T t
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hq := confidence_pos hδ hδ1
  have hD : 0 < D := by dsimp [D]; positivity
  have hS : 0 < S := tailWeight_pos hB hδ hδ1 (show t - 1 < T by omega)
  have ha : 0 ≤ a := influenceScale_nonneg hB hδ hδ1 ht
  have he : S * a = weight T t * stepSize B δ T t := by
    change S * (weight T t * stepSize B δ T t / S) = _
    field_simp
  have hstep := step_influenceScale_bound hB hδ hδ1 ht
  have hw := mul_le_mul_of_nonneg_right (weight_bounds ht).2
    (mul_nonneg (stepSize_pos hB hδ hδ1 ht).le ha)
  have hsa : S * a ^ 2 ≤ 4 / (D * T) := by
    calc
      _ = weight T t * (stepSize B δ T t * a) := by
        calc
          _ = (S * a) * a := by ring
          _ = _ := by rw [he]; ring
      _ ≤ stepSize B δ T t * a := by simpa only [one_mul] using hw
      _ ≤ _ := hstep
  change D / 16 * a ^ 2 ≤ 1 / (4 * T * S)
  apply (le_div_iff₀ (by positivity : 0 < 4 * (T : ℝ) * S)).mpr
  have hh := mul_le_mul_of_nonneg_left hsa (show 0 ≤ D * T / 4 by positivity)
  have hr : D * T / 4 * (4 / (D * T)) = 1 := by field_simp
  rw [hr] at hh
  convert hh using 1; ring

lemma initial_energy_bound {B δ D r : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T : ℕ} (hT : 0 < T) (hD : 0 ≤ D) (hr : r ^ 2 ≤ D) :
    weight T 0 * (r ^ 2 / (2 * tailWeight B δ T 0)) ≤
      8192 * B * D * Real.log (8 / δ) / Real.sqrt T := by
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have hq := confidence_pos hδ hδ1
  have hS := tailWeight_pos hB hδ hδ1 hT
  let J := 8192 * B * Real.log (8 / δ) / Real.sqrt T
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hh := mul_le_mul_of_nonneg_left (initial_tailWeight_lower hB hδ hδ1 hT)
    (show 0 ≤ 2 * J by positivity)
  have he : 2 * J * ((T : ℝ) / (4 * (4096 * B * Real.sqrt T * Real.log (8 / δ)))) = 1 := by
    dsimp [J]
    field_simp
    nlinarith [Real.sq_sqrt ht.le]
  rw [he] at hh
  have hcoef : 1 / (2 * tailWeight B δ T 0) ≤ J := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hw := mul_le_mul_of_nonneg_right (weight_bounds hT).2
    (show 0 ≤ r ^ 2 / (2 * tailWeight B δ T 0) by positivity)
  have hr' := div_le_div_of_nonneg_right hr (show 0 ≤ 2 * tailWeight B δ T 0 by positivity)
  have hlast := mul_le_mul_of_nonneg_left hcoef hD
  calc
    _ ≤ r ^ 2 / (2 * tailWeight B δ T 0) := by simpa only [one_mul] using hw
    _ ≤ D / (2 * tailWeight B δ T 0) := hr'
    _ ≤ D * J := by convert hlast using 1; ring
    _ = _ := by dsimp [J]; ring

lemma deterministic_cost_step_bound {B δ D : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) (hD : 0 ≤ D) :
    (weight T t * (stepSize B δ T t) ^ 2 / tailWeight B δ T t) * (18 * B ^ 2 * D) ≤
      B * D * Real.log (8 / δ) / (Real.sqrt T * T) := by
  have hT : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hq := confidence_ge_one hδ hδ1
  have hqp := confidence_pos hδ hδ1
  have hh := mul_le_mul_of_nonneg_right (squared_step_weight_bound hB hδ hδ1 ht)
    (show 0 ≤ 18 * B ^ 2 * D by positivity)
  have hscalar : 72 / (4096 * Real.log (8 / δ)) ≤ Real.log (8 / δ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hscalar
    (show 0 ≤ B * D / (Real.sqrt T * T) by positivity)
  apply hh.trans
  convert hm using 1 <;> field_simp; ring

end OracleTemplate.TerminalClipping
