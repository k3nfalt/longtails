import LongTails.Algorithms.SublevelRobustGradient
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OracleTemplate.SublevelRobustGradient

structure Valid (L τ α σ Δ ε : ℝ) : Prop where
  hL : 0 < L
  hτ : 0 < τ
  hα1 : 1 ≤ α
  hα2 : α < 2
  hσ : 0 ≤ σ
  hΔ : 0 ≤ Δ
  hε : 0 < ε

variable {L τ α σ Δ ε : ℝ}

lemma rate_pos (h : Valid L τ α σ Δ ε) : 0 < rate L τ α ε := by
  unfold rate
  have hα0 : 0 < α := by linarith [h.hα1]
  have h2 : 0 < 2 - α := by linarith [h.hα2]
  have := h.hL
  have := h.hτ
  have := h.hε
  have h1 : 0 < τ ^ (2 / α) := Real.rpow_pos_of_pos h.hτ _
  have h3 : 0 < (ε / 4) ^ (-(2 - α) / α) := Real.rpow_pos_of_pos (by positivity) _
  positivity

lemma rate_le_steps (_h : Valid L τ α σ Δ ε) : rate L τ α ε ≤ (steps L τ α ε : ℝ) := by
  unfold steps
  push_cast
  linarith [Nat.le_ceil (rate L τ α ε)]

lemma steps_le_rate (h : Valid L τ α σ Δ ε) : (steps L τ α ε : ℝ) ≤ rate L τ α ε + 2 := by
  unfold steps
  push_cast
  have := Nat.ceil_lt_add_one (rate_pos h).le
  linarith

lemma steps_pos : 0 < steps L τ α ε := by
  unfold steps; omega

lemma steps_pos_real : (0 : ℝ) < steps L τ α ε := by
  exact_mod_cast steps_pos

lemma radius_sq (h : Valid L τ α σ Δ ε) :
    (radius L τ α ε / 2) ^ 2 = L * ε / (8 * steps L τ α ε) := by
  unfold radius
  have hpos : 0 ≤ L * ε / (8 * steps L τ α ε) := by
    have := h.hL
    have := h.hε
    have := steps_pos_real (L := L) (τ := τ) (α := α) (ε := ε)
    positivity
  rw [show 2 * Real.sqrt (L * ε / (8 * steps L τ α ε)) / 2 = Real.sqrt (L * ε / (8 * steps L τ α ε))
    by ring]
  exact Real.sq_sqrt hpos

lemma radius_pos (h : Valid L τ α σ Δ ε) : 0 < radius L τ α ε := by
  unfold radius
  have := h.hL
  have := h.hε
  have := steps_pos_real (L := L) (τ := τ) (α := α) (ε := ε)
  positivity

lemma nu_le (h : Valid L τ α σ Δ ε) :
    L * ε / (8 * steps L τ α ε) ≤ ((ε / 4) / τ) ^ (2 / α) / 8 := by
  have hα0 : 0 < α := by linarith [h.hα1]
  have hα1 := h.hα1
  have h2 : 0 < 2 - α := by linarith [h.hα2]
  have hL := h.hL
  have hτ := h.hτ
  have hε := h.hε
  have hr := rate_le_steps h
  have hrpos := rate_pos h
  have hK := steps_pos_real (L := L) (τ := τ) (α := α) (ε := ε)
  have h1 : L * ε / (8 * steps L τ α ε) ≤ L * ε / (8 * rate L τ α ε) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  refine h1.trans ?_
  have hτp : 0 < τ ^ (2 / α) := Real.rpow_pos_of_pos hτ _
  have hq : (ε / 4 / τ) ^ (2 / α) = (ε / 4) ^ (2 / α) / τ ^ (2 / α) :=
    Real.div_rpow (by positivity) hτ.le _
  have hsplit : (ε / 4) ^ (2 / α) = (ε / 4) * (ε / 4) ^ ((2 - α) / α) := by
    have : (2 : ℝ) / α = 1 + (2 - α) / α := by
      field_simp
      ring
    rw [this, Real.rpow_add (by positivity), Real.rpow_one]
  have hneg : (ε / 4) ^ (-(2 - α) / α) = ((ε / 4) ^ ((2 - α) / α))⁻¹ := by
    rw [neg_div, Real.rpow_neg (by positivity)]
  have hεq : 0 < (ε / 4) ^ ((2 - α) / α) := Real.rpow_pos_of_pos (by positivity) _
  have hid : L * ε / (8 * rate L τ α ε) =
      (7 * (2 - α) / (64 * α)) * ((ε / 4) / τ) ^ (2 / α) := by
    unfold rate
    rw [hq, hsplit, hneg]
    field_simp
    ring
  rw [hid]
  have hpos : 0 ≤ ((ε / 4) / τ) ^ (2 / α) := Real.rpow_nonneg (by positivity) _
  have hc : 7 * (2 - α) / (64 * α) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc (7 * (2 - α) / (64 * α)) * ((ε / 4) / τ) ^ (2 / α)
      ≤ (1 / 8) * ((ε / 4) / τ) ^ (2 / α) := mul_le_mul_of_nonneg_right hc hpos
    _ = ((ε / 4) / τ) ^ (2 / α) / 8 := by ring

lemma steps_nu (h : Valid L τ α σ Δ ε) :
    (steps L τ α ε : ℝ) * (L * ε / (8 * steps L τ α ε)) / (2 * L) = ε / 4 / 4 := by
  have hK := steps_pos_real (L := L) (τ := τ) (α := α) (ε := ε)
  have hL := h.hL
  field_simp
  ring

lemma six_le_subbatches : 6 ≤ subbatches L τ α Δ ε := by
  unfold subbatches; omega

lemma one_le_subbatches_real : (1 : ℝ) ≤ subbatches L τ α Δ ε := by
  have := six_le_subbatches (L := L) (τ := τ) (α := α) (Δ := Δ) (ε := ε)
  exact_mod_cast (by omega : 1 ≤ subbatches L τ α Δ ε)

lemma noise_nonneg (h : Valid L τ α σ Δ ε) : 0 ≤ noise L τ α σ ε := by
  unfold noise
  have hα0 : 0 < α := by linarith [h.hα1]
  have h2 : 0 < 2 - α := by linarith [h.hα2]
  have := h.hL
  have := h.hε
  have h1 : 0 ≤ τ ^ (2 / α) := (Real.rpow_pos_of_pos h.hτ _).le
  have h3 : 0 ≤ ε ^ (-(2 / α)) := (Real.rpow_pos_of_pos h.hε _).le
  have := h.hσ
  positivity

lemma rate_sigma_le (h : Valid L τ α σ Δ ε) :
    (rate L τ α ε + 2) * σ ^ 2 / (L * ε) ≤ noise L τ α σ ε := by
  have hα0 : 0 < α := by linarith [h.hα1]
  have h2 : 0 < 2 - α := by linarith [h.hα2]
  have hL := h.hL
  have hε := h.hε
  have hτ := h.hτ
  have hσ := h.hσ
  unfold noise rate
  have hα1 := h.hα1
  have hq : (2 - α) / α ≤ 1 := by
    rw [div_le_one hα0]; linarith
  have hq0 : 0 ≤ (2 - α) / α := by positivity
  have hpow : (ε / 4) ^ (-(2 - α) / α) ≤ 4 * ε ^ (-((2 - α) / α)) := by
    rw [neg_div, Real.rpow_neg (by positivity), Real.div_rpow hε.le (by norm_num),
      Real.rpow_neg hε.le]
    have h4 : (4 : ℝ) ^ ((2 - α) / α) ≤ 4 := by
      calc (4 : ℝ) ^ ((2 - α) / α) ≤ (4 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
        _ = 4 := Real.rpow_one 4
    have hεp : 0 < ε ^ ((2 - α) / α) := Real.rpow_pos_of_pos hε _
    have h4p : 0 < (4 : ℝ) ^ ((2 - α) / α) := Real.rpow_pos_of_pos (by norm_num) _
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h4 (inv_nonneg.mpr hεp.le)
  have hεsplit : ε ^ (-(2 / α)) = ε ^ (-((2 - α) / α)) / ε := by
    rw [← Real.rpow_sub_one hε.ne']
    congr 1
    field_simp
    ring
  have hτp : 0 < τ ^ (2 / α) := Real.rpow_pos_of_pos hτ _
  have hεn : 0 < ε ^ (-((2 - α) / α)) := Real.rpow_pos_of_pos hε _
  rw [hεsplit]
  rw [add_mul, add_div]
  have hmain : 32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * (ε / 4) ^ (-(2 - α) / α) * σ ^ 2 /
      (L * ε) ≤ 19 * α / (2 - α) * τ ^ (2 / α) * σ ^ 2 * (ε ^ (-((2 - α) / α)) / ε) := by
    have hc : 32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * (ε / 4) ^ (-(2 - α) / α) * σ ^ 2 /
        (L * ε) = (32 / 7) * (α / (2 - α)) * τ ^ (2 / α) * σ ^ 2 *
          ((ε / 4) ^ (-(2 - α) / α) / ε) := by
      field_simp
    rw [hc]
    have hd : 19 * α / (2 - α) * τ ^ (2 / α) * σ ^ 2 * (ε ^ (-((2 - α) / α)) / ε) =
        (19 / 4) * (α / (2 - α)) * τ ^ (2 / α) * σ ^ 2 * ((4 * ε ^ (-((2 - α) / α))) / ε) := by
      field_simp
    rw [hd]
    have hcoef : 0 ≤ (α / (2 - α)) * τ ^ (2 / α) * σ ^ 2 := by positivity
    have hpow' : (ε / 4) ^ (-(2 - α) / α) / ε ≤ (4 * ε ^ (-((2 - α) / α))) / ε :=
      div_le_div_of_nonneg_right hpow hε.le
    have hpp : 0 ≤ (ε / 4) ^ (-(2 - α) / α) / ε := by
      have := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < ε / 4) (-(2 - α) / α)
      positivity
    calc (32 / 7) * (α / (2 - α)) * τ ^ (2 / α) * σ ^ 2 * ((ε / 4) ^ (-(2 - α) / α) / ε)
        ≤ (19 / 4) * (α / (2 - α)) * τ ^ (2 / α) * σ ^ 2 * ((ε / 4) ^ (-(2 - α) / α) / ε) := by
          apply mul_le_mul_of_nonneg_right _ hpp
          have : (32 / 7 : ℝ) ≤ 19 / 4 := by norm_num
          nlinarith [hcoef]
      _ ≤ (19 / 4) * (α / (2 - α)) * τ ^ (2 / α) * σ ^ 2 * ((4 * ε ^ (-((2 - α) / α))) / ε) := by
          apply mul_le_mul_of_nonneg_left hpow'
          positivity
  have hrest : 2 * σ ^ 2 / (L * ε) ≤ 2 * σ ^ 2 / (L * ε) := le_rfl
  linarith

lemma subsize_ge (_h : Valid L τ α σ Δ ε) :
    (1152 + 16 * subbatches L τ α Δ ε) * noise L τ α σ ε ≤ (subsize L τ α σ Δ ε : ℝ) := by
  unfold subsize
  push_cast
  linarith [Nat.le_ceil ((1152 + 16 * (subbatches L τ α Δ ε : ℝ)) * noise L τ α σ ε)]

lemma subsize_pos_real : (0 : ℝ) < subsize L τ α σ Δ ε := by
  exact_mod_cast subsize_pos L τ α σ Δ ε

lemma subsize_lower (h : Valid L τ α σ Δ ε) :
    (1152 + 16 * subbatches L τ α Δ ε) * ((steps L τ α ε : ℝ) * σ ^ 2 / (L * ε)) ≤
      (subsize L τ α σ Δ ε : ℝ) := by
  have hb := subsize_ge h
  have hn := rate_sigma_le h
  have hKle := steps_le_rate h
  have hL := h.hL
  have hε := h.hε
  have hσ := h.hσ
  have hm := one_le_subbatches_real (L := L) (τ := τ) (α := α) (Δ := Δ) (ε := ε)
  have h1 : (steps L τ α ε : ℝ) * σ ^ 2 / (L * ε) ≤ (rate L τ α ε + 2) * σ ^ 2 / (L * ε) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hKle (by positivity)
  have hc : 0 ≤ 1152 + 16 * (subbatches L τ α Δ ε : ℝ) := by positivity
  calc (1152 + 16 * subbatches L τ α Δ ε) * ((steps L τ α ε : ℝ) * σ ^ 2 / (L * ε))
      ≤ (1152 + 16 * subbatches L τ α Δ ε) * noise L τ α σ ε :=
        mul_le_mul_of_nonneg_left (h1.trans hn) hc
    _ ≤ _ := hb

lemma variance_batch (h : Valid L τ α σ Δ ε) :
    144 * σ ^ 2 ≤ (subsize L τ α σ Δ ε : ℝ) * (L * ε / (8 * steps L τ α ε)) := by
  have hL := h.hL
  have hε := h.hε
  have hK := steps_pos_real (L := L) (τ := τ) (α := α) (ε := ε)
  have hm := one_le_subbatches_real (L := L) (τ := τ) (α := α) (Δ := Δ) (ε := ε)
  have hb := subsize_lower h
  have hσ := h.hσ
  have hν : 0 < L * ε / (8 * steps L τ α ε) := by positivity
  calc 144 * σ ^ 2 = (1152 * ((steps L τ α ε : ℝ) * σ ^ 2 / (L * ε))) *
        (L * ε / (8 * steps L τ α ε)) := by
          field_simp
          ring
    _ ≤ ((1152 + 16 * subbatches L τ α Δ ε) * ((steps L τ α ε : ℝ) * σ ^ 2 / (L * ε))) *
        (L * ε / (8 * steps L τ α ε)) := by
          apply mul_le_mul_of_nonneg_right _ hν.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hν.le

lemma second_moment_budget (h : Valid L τ α σ Δ ε) :
    (steps L τ α ε : ℝ) * (subbatches L τ α Δ ε * (σ ^ 2 / subsize L τ α σ Δ ε)) / (2 * L) ≤
      ε / 32 := by
  have hL := h.hL
  have hε := h.hε
  have hK := steps_pos_real (L := L) (τ := τ) (α := α) (ε := ε)
  have hm := one_le_subbatches_real (L := L) (τ := τ) (α := α) (Δ := Δ) (ε := ε)
  have hb := subsize_lower h
  have hbpos := subsize_pos_real (L := L) (τ := τ) (α := α) (σ := σ) (Δ := Δ) (ε := ε)
  have hσ := h.hσ
  by_cases hσ0 : σ = 0
  · subst hσ0
    simp
    positivity
  have hσp : 0 < σ ^ 2 := by positivity
  have hb16 : 16 * subbatches L τ α Δ ε * ((steps L τ α ε : ℝ) * σ ^ 2 / (L * ε)) ≤
      (subsize L τ α σ Δ ε : ℝ) := by
    refine le_trans ?_ hb
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hkey : (steps L τ α ε : ℝ) * (subbatches L τ α Δ ε * (σ ^ 2 / subsize L τ α σ Δ ε)) /
      (2 * L) = ((16 * subbatches L τ α Δ ε * ((steps L τ α ε : ℝ) * σ ^ 2 / (L * ε))) /
        subsize L τ α σ Δ ε) * (ε / 32) := by
    field_simp
    ring
  rw [hkey]
  have hfrac : (16 * subbatches L τ α Δ ε * ((steps L τ α ε : ℝ) * σ ^ 2 / (L * ε))) /
      subsize L τ α σ Δ ε ≤ 1 := by
    rw [div_le_one hbpos]
    exact hb16
  calc _ ≤ 1 * (ε / 32) := mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = ε / 32 := by ring

lemma two_pow_ceil_logb {y : ℝ} (hy : 0 < y) : y ≤ (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ := by
  by_cases hy1 : y ≤ 1
  · calc y ≤ 1 := hy1
      _ ≤ (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ := one_le_pow₀ (by norm_num)
  · rw [not_le] at hy1
    have hlog : 0 < Real.logb 2 y := Real.logb_pos (by norm_num) hy1
    have hc : Real.logb 2 y ≤ (⌈Real.logb 2 y⌉₊ : ℝ) := Nat.le_ceil _
    calc y = (2 : ℝ) ^ (Real.logb 2 y) := (Real.rpow_logb (by norm_num) (by norm_num) hy).symm
      _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 y⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hc
      _ = (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ := Real.rpow_natCast _ _

lemma failure_budget (h : Valid L τ α σ Δ ε) :
    Δ * steps L τ α ε * (1 / 2 : ℝ) ^ subbatches L τ α Δ ε ≤ ε / 32 := by
  have hL := h.hL
  have hε := h.hε
  have hK := steps_pos_real (L := L) (τ := τ) (α := α) (ε := ε)
  have hKle := steps_le_rate h
  have hr := rate_pos h
  have hΔ := h.hΔ
  rcases eq_or_lt_of_le hΔ with hΔ0 | hΔp
  · rw [← hΔ0]; simp; positivity
  have hy : 0 < 32 * (rate L τ α ε + 2) * Δ / ε := by positivity
  have hpow : 32 * (rate L τ α ε + 2) * Δ / ε ≤ (2 : ℝ) ^ subbatches L τ α Δ ε := by
    unfold subbatches
    calc 32 * (rate L τ α ε + 2) * Δ / ε ≤ (2 : ℝ) ^ ⌈Real.logb 2 (32 * (rate L τ α ε + 2) * Δ / ε)⌉₊ :=
          two_pow_ceil_logb hy
      _ ≤ (2 : ℝ) ^ (6 + ⌈Real.logb 2 (32 * (rate L τ α ε + 2) * Δ / ε)⌉₊) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (1 / 2 : ℝ) ^ subbatches L τ α Δ ε = 1 / (2 : ℝ) ^ subbatches L τ α Δ ε :=
    one_div_pow _ _
  rw [h2]
  have hpos : 0 < (2 : ℝ) ^ subbatches L τ α Δ ε := by positivity
  calc Δ * steps L τ α ε * (1 / (2 : ℝ) ^ subbatches L τ α Δ ε)
      ≤ Δ * steps L τ α ε * (1 / (32 * (rate L τ α ε + 2) * Δ / ε)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact one_div_le_one_div_of_le hy hpow
    _ = (steps L τ α ε : ℝ) / (rate L τ α ε + 2) * (ε / 32) := by
        field_simp
    _ ≤ 1 * (ε / 32) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_one (by positivity)]
        exact hKle
    _ = ε / 32 := by ring

end OracleTemplate.SublevelRobustGradient
