import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.MuonTuning

lemma noise_scale {e s a : ℝ} (he : 0 < e) (hs : 0 ≤ s) (ha : 0 < a)
    (hnoise : 4096 * s ^ 2 ≤ a * e ^ 2) :
    Real.sqrt (1 / a) * s ≤ e / 64 := by
  have hsqrt := Real.sq_sqrt (show 0 ≤ 1 / a by positivity)
  have hsq : (Real.sqrt (1 / a) * s) ^ 2 ≤ (e / 64) ^ 2 := by
    rw [mul_pow, hsqrt]
    apply (mul_le_mul_iff_right₀ ha).mp
    field_simp
    nlinarith
  have hn : 0 ≤ Real.sqrt (1 / a) * s := by positivity
  nlinarith [sq_nonneg (Real.sqrt (1 / a) * s - e / 64)]

lemma step_scale {e Δ : ℝ} {T : ℕ} (he : 0 < e) (hT : 0 < T) :
    (Δ / (e * T)) * e * T = Δ := by
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  field_simp

lemma drift_scale {e Δ L a D : ℝ} {T : ℕ}
    (he : 0 < e) (ha : 0 < a) (hT : 0 < T)
    (hD : L * Δ = D * e ^ 2) (hbudget : 64 * a * D ≤ (T : ℝ)) :
    L * (Δ / (e * T)) / (1 / a) ≤ e / 64 := by
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  apply (mul_le_mul_iff_right₀ (show 0 < 64 * e * T by positivity)).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hbudget (sq_nonneg e)]

lemma overhead_scale {e Δ a x H : ℝ} {T : ℕ}
    (he : 0 < e) (hΔ : 0 ≤ Δ) (hT : 0 < T)
    (hbudget : 384 * a * x * H ^ 2 ≤ (T : ℝ)) :
    (Δ / (e * T)) * (96 * e * a * x * H ^ 2) ≤ Δ / 4 := by
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * e * T by positivity)).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hbudget hΔ]

lemma ema_decay {a H : ℝ} {K : ℕ} (ha : 1 ≤ a)
    (hK : 2 * a * H ≤ (K : ℝ)) :
    (1 - 1 / a) ^ K ≤ Real.exp (-2 * H) := by
  have ha0 : 0 < a := by linarith
  have hα : 1 / a ≤ 1 := (div_le_one ha0).mpr ha
  have hb : 1 - 1 / a ≤ Real.exp (-(1 / a)) := by
    linarith [Real.add_one_le_exp (-(1 / a))]
  have hk := mul_le_mul_of_nonneg_left hK (show 0 ≤ 1 / a by positivity)
  have hcancel : a * (1 / a) = 1 := by field_simp
  calc
    _ ≤ (Real.exp (-(1 / a))) ^ K := pow_le_pow_left₀ (by linarith) hb K
    _ = Real.exp ((K : ℝ) * (-(1 / a))) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

lemma exponential_cutoff {e B H : ℝ} (he : 0 ≤ e)
    (hB : B ≤ e * H * Real.exp H / 4194304) :
    Real.exp (-2 * H) * B ≤ e / 64 := by
  have hH : H ≤ Real.exp H := by linarith [Real.add_one_le_exp H]
  have hprod : Real.exp H * Real.exp (-H) = 1 := by
    rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right hH (Real.exp_pos (-H)).le
  rw [hprod] at hm
  have heq : Real.exp (-2 * H) * Real.exp H = Real.exp (-H) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-2 * H) * (e * H * Real.exp H / 4194304) :=
      mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
    _ = e / 4194304 * (H * Real.exp (-H)) := by rw [← heq]; ring
    _ ≤ e / 4194304 := by
      simpa using mul_le_mul_of_nonneg_left hm (show 0 ≤ e / 4194304 by positivity)
    _ ≤ e / 64 := by linarith

lemma confidence_scale {a D γ : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    12 ≤ Real.log (1073741824 * a * D / γ) ∧
      Real.exp (Real.log (1073741824 * a * D / γ)) = 1073741824 * a * D / γ := by
  have ha0 : 0 < a := by linarith
  have hD0 : 0 < D := by linarith
  have harg : 0 < 1073741824 * a * D / γ := by positivity
  have had : 1 ≤ a * D := by nlinarith
  have hbase : (2 : ℝ) ^ 30 ≤ 1073741824 * a * D / γ := by
    apply (le_div_iff₀ hγ).mpr
    norm_num
    nlinarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 30) hbase
  rw [Real.log_pow] at hl
  constructor
  · nlinarith [Real.log_two_gt_d9]
  · exact Real.exp_log harg

lemma lag_count_bounds {a H : ℝ} (ha : 1 ≤ a) (hH : 1 ≤ H) :
    2 ≤ ⌈2 * a * H⌉₊ ∧ 2 * a * H ≤ (⌈2 * a * H⌉₊ : ℝ) ∧
      (⌈2 * a * H⌉₊ : ℝ) ≤ 3 * a * H := by
  have hprod : 1 ≤ a * H := by nlinarith
  have hlo := Nat.le_ceil (2 * a * H)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2 * a * H by nlinarith)
  refine ⟨?_, hlo, by linarith⟩
  have hh : (2 : ℝ) ≤ (⌈2 * a * H⌉₊ : ℝ) := by nlinarith
  exact_mod_cast hh

lemma training_count_bounds {a D H : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 1 ≤ H) :
    0 < ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊ ∧
      1048576 * a * (D + Real.sqrt D * H ^ 2) ≤
        (⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊ : ℝ) ∧
      (⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊ : ℝ) ≤ 4194304 * a * D * H ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hD0 : 0 < D := by linarith
  have hs := Real.sq_sqrt hD0.le
  have hs0 := Real.sqrt_nonneg D
  have hsD : Real.sqrt D ≤ D := by nlinarith
  have hHsq : 1 ≤ H ^ 2 := by nlinarith
  have hbase : 1 ≤ a * D * H ^ 2 := by
    have had : 1 ≤ a * D := by nlinarith
    nlinarith
  have hterm1 := mul_le_mul_of_nonneg_left hHsq hD0.le
  have hterm2 := mul_le_mul_of_nonneg_right hsD (sq_nonneg H)
  have hsum : D + Real.sqrt D * H ^ 2 ≤ 2 * D * H ^ 2 := by nlinarith
  have hbig := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1048576 * a by positivity)
  have hpos : 0 < 1048576 * a * (D + Real.sqrt D * H ^ 2) := by positivity
  refine ⟨Nat.ceil_pos.mpr hpos, Nat.le_ceil _, ?_⟩
  have hh := Nat.ceil_lt_add_one hpos.le
  nlinarith

lemma noise_radius_bound {e s a D H γ : ℝ} {T : ℕ}
    (he : 0 ≤ e) (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hnoise : 4096 * s ^ 2 ≤ a * e ^ 2)
    (hT : (T : ℝ) ≤ 4194304 * a * D * H ^ 2) :
    s * Real.sqrt (2 * (T : ℝ) / γ) ≤ 64 * e * a * D * H / γ := by
  have ha0 : 0 ≤ a := by linarith
  have hD0 : 0 < D := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hv : s ^ 2 ≤ a * e ^ 2 / 4096 := by linarith
  have hf : γ / (2 * D) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hsq : (s * Real.sqrt (2 * (T : ℝ) / γ)) ^ 2 ≤ (64 * e * a * D * H / γ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (T : ℝ) / γ)]
    calc
      _ ≤ (a * e ^ 2 / 4096) * (2 * (4194304 * a * D * H ^ 2) / γ) := by
        gcongr
      _ = (64 * e * a * D * H / γ) ^ 2 * (γ / (2 * D)) := by
        field_simp
        ring
      _ ≤ (64 * e * a * D * H / γ) ^ 2 := by
        simpa using mul_le_mul_of_nonneg_left hf (sq_nonneg (64 * e * a * D * H / γ))
  have hright : 0 ≤ 64 * e * a * D * H / γ := by positivity
  nlinarith [sq_nonneg (s * Real.sqrt (2 * (T : ℝ) / γ) - 64 * e * a * D * H / γ)]

lemma residue_tail_bound {a D H γ : ℝ} {K T : ℕ}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 0 ≤ H) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hTpos : 0 < T) (hK : (K : ℝ) ≤ 3 * a * H)
    (hT : (T : ℝ) ≤ 4194304 * a * D * H ^ 2)
    (hexp : Real.exp H = 1073741824 * a * D / γ) :
    (K : ℝ) * (T + 1) * Real.exp (-(6 * H)) ≤ γ / 2 := by
  have ha0 : 0 ≤ a := by linarith
  have hD0 : 0 ≤ D := by linarith
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have ht' : (T : ℝ) + 1 ≤ 2 * (4194304 * a * D * H ^ 2) := by linarith
  have hprod := mul_le_mul hK ht' (show 0 ≤ (T : ℝ) + 1 by positivity)
    (show 0 ≤ 3 * a * H by positivity)
  have harg : 2 * (K : ℝ) * (T + 1) / γ ≤ 50331648 * a ^ 2 * D * H ^ 3 / γ := by
    apply (div_le_div_iff_of_pos_right hγ).mpr
    nlinarith
  have hbase : a ^ 2 * D / γ ≤ (a * D / γ) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hγ)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left (show γ ≤ D by linarith)
      (show 0 ≤ a ^ 2 * D by positivity)]
  have hcoef : 50331648 * a ^ 2 * D / γ ≤ (Real.exp H) ^ 2 := by
    rw [hexp]
    calc
      _ = 50331648 * (a ^ 2 * D / γ) := by ring
      _ ≤ 50331648 * (a * D / γ) ^ 2 := mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ ≤ (1073741824 * a * D / γ) ^ 2 := by
        rw [show (1073741824 * a * D / γ) ^ 2 =
          1073741824 ^ 2 * (a * D / γ) ^ 2 by ring]
        nlinarith [sq_nonneg (a * D / γ)]
  have hpow : H ^ 3 ≤ (Real.exp H) ^ 3 :=
    pow_le_pow_left₀ hH (by linarith [Real.add_one_le_exp H]) 3
  have harg' : 2 * (K : ℝ) * (T + 1) / γ ≤ Real.exp (6 * H) := by
    calc
      _ ≤ 50331648 * a ^ 2 * D * H ^ 3 / γ := harg
      _ = (50331648 * a ^ 2 * D / γ) * H ^ 3 := by ring
      _ ≤ (Real.exp H) ^ 2 * (Real.exp H) ^ 3 :=
        mul_le_mul hcoef hpow (by positivity) (by positivity)
      _ = Real.exp (5 * H) := by
        rw [← pow_add]
        simpa using (Real.exp_nat_mul H 5).symm
      _ ≤ Real.exp (6 * H) := Real.exp_le_exp.mpr (by linarith)
  have hcancel : Real.exp (6 * H) * Real.exp (-(6 * H)) = 1 := by
    rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right harg'
    (show 0 ≤ γ / 2 * Real.exp (-(6 * H)) by positivity)
  have heq : (2 * (K : ℝ) * (T + 1) / γ) * (γ / 2 * Real.exp (-(6 * H))) =
      (K : ℝ) * (T + 1) * Real.exp (-(6 * H)) := by field_simp
  rw [heq] at hm
  calc
    _ ≤ Real.exp (6 * H) * (γ / 2 * Real.exp (-(6 * H))) := hm
    _ = γ / 2 := by nlinarith [hcancel]

lemma initial_gradient_scale {g e D : ℝ} (he : 0 ≤ e) (hD : 1 ≤ D)
    (hg : g ^ 2 ≤ 2 * e ^ 2 * D) : g ≤ 2 * e * D := by
  have hD0 : 0 ≤ D := by linarith
  have hh := mul_nonneg (sq_nonneg e) (show 0 ≤ 4 * D ^ 2 - 2 * D by nlinarith)
  have hp : 0 ≤ 2 * e * D := by positivity
  nlinarith [sq_nonneg (g - 2 * e * D)]

lemma tracker_threshold {g R e a D H γ : ℝ}
    (he : 0 ≤ e) (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hg : g ≤ 2 * e * D)
    (hR : R ≤ 64 * e * a * D * H / γ)
    (hexp : Real.exp H = 1073741824 * a * D / γ) :
    2 * (g + e * D) + R ≤ e * H * Real.exp H / 4194304 := by
  have ha0 : 0 ≤ a := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hah : 1 ≤ a * H := by nlinarith
  have hbase : D ≤ a * D * H / γ := by
    apply (le_div_iff₀ hγ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hγ1 hD0,
      mul_le_mul_of_nonneg_left hah hD0]
  have hs := mul_le_mul_of_nonneg_left hbase he
  have hp : 0 ≤ e * a * D * H / γ := by positivity
  calc
    _ ≤ 256 * e * a * D * H / γ := by
      simp only [div_eq_mul_inv] at hR hs hp ⊢
      nlinarith
    _ = e * H * Real.exp H / 4194304 := by rw [hexp]; ring

lemma sqrt_gap_scale {L Δ e D : ℝ} (he : 0 ≤ e) (hD : 0 ≤ D)
    (hscale : L * Δ = D * e ^ 2) : Real.sqrt (L * Δ) = e * Real.sqrt D := by
  rw [hscale, Real.sqrt_mul hD, Real.sqrt_sq_eq_abs, abs_of_nonneg he]
  ring

lemma training_budget_suffices {a D H : ℝ} {T : ℕ} (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hT : 1048576 * a * (D + Real.sqrt D * H ^ 2) ≤ (T : ℝ)) :
    64 * a * D ≤ (T : ℝ) ∧ 384 * a * Real.sqrt D * H ^ 2 ≤ (T : ℝ) := by
  have hterm : 0 ≤ a * Real.sqrt D * H ^ 2 := by positivity
  have had : 0 ≤ a * D := mul_nonneg ha hD
  constructor <;> nlinarith

lemma validation_batch_bounds {e s a : ℝ} (he : 0 < e) (ha : 1 ≤ a)
    (hnoise : 4096 * s ^ 2 ≤ a * e ^ 2) :
    0 < max 1 ⌈144 * s ^ 2 / e ^ 2⌉₊ ∧
      16 * s ^ 2 ≤ (max 1 ⌈144 * s ^ 2 / e ^ 2⌉₊ : ℕ) * (e / 3) ^ 2 ∧
        ((max 1 ⌈144 * s ^ 2 / e ^ 2⌉₊ : ℕ) : ℝ) ≤ 2 * a := by
  have hz : 0 ≤ 144 * s ^ 2 / e ^ 2 := by positivity
  have hlo : 144 * s ^ 2 / e ^ 2 ≤ ((max 1 ⌈144 * s ^ 2 / e ^ 2⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 ⌈144 * s ^ 2 / e ^ 2⌉₊))
  have hb := (div_le_iff₀ (sq_pos_of_pos he)).mp hlo
  have hupper : 144 * s ^ 2 / e ^ 2 ≤ a := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    nlinarith [sq_nonneg s]
  have hceil := Nat.ceil_lt_add_one hz
  refine ⟨lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _), by nlinarith, ?_⟩
  rw [Nat.cast_max]
  norm_num only [Nat.cast_one]
  apply max_le <;> linarith

lemma validation_draw_bounds {a D H γ : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D)
    (hH : 1 ≤ H) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hexp : Real.exp H = 1073741824 * a * D / γ) :
    0 < ⌈Real.log (1 / γ) / Real.log 2⌉₊ ∧
      (⌈Real.log (1 / γ) / Real.log 2⌉₊ : ℝ) ≤ 3 * H ∧
        (1 / 2 : ℝ) ^ ⌈Real.log (1 / γ) / Real.log 2⌉₊ ≤ γ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 1 < 1 / γ := (one_lt_div hγ).mpr hγ1
  have hl : 0 < Real.log (1 / γ) := Real.log_pos harg
  have hq : 0 < Real.log (1 / γ) / Real.log 2 := div_pos hl hl2
  have haD : 1 ≤ a * D := by nlinarith
  have hlog : Real.log (1 / γ) ≤ H := by
    apply (Real.log_le_iff_le_exp (by positivity : 0 < 1 / γ)).mpr
    rw [hexp]
    exact (div_le_div_iff_of_pos_right hγ).mpr (by nlinarith)
  have hratio : Real.log (1 / γ) / Real.log 2 ≤ 2 * H := by
    apply (div_le_iff₀ hl2).mpr
    nlinarith [Real.log_two_gt_d9]
  have hhi := Nat.ceil_lt_add_one hq.le
  have hlo := Nat.le_ceil (Real.log (1 / γ) / Real.log 2)
  have hmul := (div_le_iff₀ hl2).mp hlo
  refine ⟨Nat.ceil_pos.mpr hq, by linarith, ?_⟩
  have hehalf : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← hehalf, ← Real.exp_nat_mul]
  apply (Real.le_log_iff_exp_le hγ).mp
  rw [one_div, Real.log_inv] at hmul ⊢
  nlinarith

lemma validation_block_bounds {a D H γ : ℝ} {Q : ℕ}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 1 ≤ H) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hQ : 0 < Q) (hQhi : (Q : ℝ) ≤ 3 * H)
    (hexp : Real.exp H = 1073741824 * a * D / γ) :
    0 < ⌈8 * Real.log ((Q : ℝ) / γ)⌉₊ ∧
      (⌈8 * Real.log ((Q : ℝ) / γ)⌉₊ : ℝ) ≤ 17 * H ∧
        (Q : ℝ) * Real.exp (-(3 * (⌈8 * Real.log ((Q : ℝ) / γ)⌉₊ : ℝ) / 8)) ≤ γ := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hqp : 0 < (Q : ℝ) := by linarith
  have hH0 : 0 ≤ H := by linarith
  have had : 1 ≤ a * D := by nlinarith
  have hc : 3 ≤ 1073741824 * a * D := by nlinarith
  have harg : (Q : ℝ) / γ ≤ H * Real.exp H := by
    rw [hexp, ← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hγ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hH0]
  have hexp2 : Real.exp (2 * H) = Real.exp H * Real.exp H := by
    rw [show 2 * H = H + H by ring, Real.exp_add]
  have hlog : Real.log ((Q : ℝ) / γ) ≤ 2 * H := by
    apply (Real.log_le_iff_le_exp (by positivity : 0 < (Q : ℝ) / γ)).mpr
    rw [hexp2]
    exact harg.trans (mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp H]) (Real.exp_pos H).le)
  have hlogpos : 0 < Real.log ((Q : ℝ) / γ) := Real.log_pos
    ((one_lt_div hγ).mpr (by linarith))
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 8 * Real.log ((Q : ℝ) / γ) by positivity)
  have hlo := Nat.le_ceil (8 * Real.log ((Q : ℝ) / γ))
  refine ⟨Nat.ceil_pos.mpr (by positivity), by linarith, ?_⟩
  have htail : Real.exp (-(3 * (⌈8 * Real.log ((Q : ℝ) / γ)⌉₊ : ℝ) / 8)) ≤ γ / Q := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < γ / Q)).mp
    rw [Real.log_div (ne_of_gt hγ) (ne_of_gt hqp)]
    rw [Real.log_div (ne_of_gt hqp) (ne_of_gt hγ)] at hlo hlogpos ⊢
    linarith
  calc
    _ ≤ (Q : ℝ) * (γ / Q) := mul_le_mul_of_nonneg_left htail hqp.le
    _ = γ := by field_simp

lemma total_cost_bound {a D H : ℝ} {Q b k : ℕ}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hQ : (Q : ℝ) ≤ 3 * H) (hb : (b : ℝ) ≤ 2 * a) (hk : (k : ℝ) ≤ 17 * H) :
    ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊ + Q * b * k ≤
      ⌈2097152 * a * (D + Real.sqrt D * H ^ 2)⌉₊ := by
  have ha0 : 0 ≤ a := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hx : 1 ≤ Real.sqrt D := by nlinarith [Real.sq_sqrt hD0, Real.sqrt_nonneg D]
  have hcost : (Q : ℝ) * b * k ≤ 102 * a * H ^ 2 := by
    calc
      _ ≤ (3 * H) * (2 * a) * (17 * H) := by gcongr
      _ = _ := by ring
  have hroot := mul_le_mul_of_nonneg_left hx (show 0 ≤ a * H ^ 2 by positivity)
  have had : 1 ≤ a * D := by nlinarith
  have hbase : 1 ≤ a * (D + Real.sqrt D * H ^ 2) := by
    nlinarith [mul_nonneg ha0 (mul_nonneg (Real.sqrt_nonneg D) (sq_nonneg H))]
  have hhi := Nat.ceil_lt_add_one
    (show 0 ≤ 1048576 * a * (D + Real.sqrt D * H ^ 2) by positivity)
  have hlo := Nat.le_ceil (2097152 * a * (D + Real.sqrt D * H ^ 2))
  have hc : ((⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊ + Q * b * k : ℕ) : ℝ) ≤
      (⌈2097152 * a * (D + Real.sqrt D * H ^ 2)⌉₊ : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hc

lemma public_budget_domination {a D H A R J : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (haA : a ≤ 262144 * A) (hDR : D ≤ 64 * R) (hHJ : H ≤ J) :
    ⌈2097152 * a * (D + Real.sqrt D * H ^ 2)⌉₊ ≤
      ⌈35184372088832 * A * (R + Real.sqrt R * J ^ 2)⌉₊ := by
  have hroot : Real.sqrt D ≤ 8 * Real.sqrt R := by
    have hh := Real.sqrt_le_sqrt hDR
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)] at hh
    norm_num at hh
    exact hh
  have hJ : 0 ≤ J := hH.trans hHJ
  have hraw : 2097152 * a * (D + Real.sqrt D * H ^ 2) ≤
      2097152 * (262144 * A) * (64 * R + (8 * Real.sqrt R) * J ^ 2) := by
    gcongr
  apply Nat.ceil_mono
  have hp : 0 ≤ A * Real.sqrt R * J ^ 2 := by positivity
  nlinarith

lemma hard_parameter_bounds {L Δ s ε δ : ℝ}
    (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hhard : ε ^ 2 < 2 * L * Δ) :
    let e := ε / 8
    let γ := δ / 4
    let D := L * Δ / e ^ 2
    let a := max 1 (4096 * s ^ 2 / e ^ 2)
    let H := Real.log (1073741824 * a * D / γ)
    0 < L ∧ 0 < Δ ∧ 1 ≤ D ∧ 1 ≤ a ∧ 1 ≤ H ∧
      4096 * s ^ 2 ≤ a * e ^ 2 ∧ L * Δ = D * e ^ 2 ∧
        Real.exp H = 1073741824 * a * D / γ := by
  let e := ε / 8
  let γ := δ / 4
  let D := L * Δ / e ^ 2
  let a := max 1 (4096 * s ^ 2 / e ^ 2)
  have he : 0 < e := by dsimp [e]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith
  have hLp : 0 < L := by nlinarith [sq_pos_of_pos hε]
  have hΔp : 0 < Δ := by nlinarith [sq_pos_of_pos hε]
  have hD : 1 ≤ D := by
    apply (one_le_div (sq_pos_of_pos he)).mpr
    dsimp [e]
    nlinarith
  have ha : 1 ≤ a := le_max_left _ _
  have hnoise : 4096 * s ^ 2 ≤ a * e ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos he)).mp (le_max_right _ _)
  have hscale : L * Δ = D * e ^ 2 := by dsimp [D]; field_simp
  have hh := confidence_scale ha hD hγ hγ1
  exact ⟨hLp, hΔp, hD, ha, le_trans (by norm_num : (1 : ℝ) ≤ 12) hh.1, hnoise, hscale, hh.2⟩

lemma public_parameter_comparison {L Δ s ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hpositive : 0 < L * Δ) :
    let a := max 1 (4096 * s ^ 2 / (ε / 8) ^ 2)
    let D := L * Δ / (ε / 8) ^ 2
    let A := 1 + s ^ 2 / ε ^ 2
    let R := 1 + L * Δ / ε ^ 2
    a ≤ 262144 * A ∧ D ≤ 64 * R ∧
      Real.log (1073741824 * a * D / (δ / 4)) ≤
        Real.log (72057594037927936 * A * R / δ) := by
  let a := max 1 (4096 * s ^ 2 / (ε / 8) ^ 2)
  let D := L * Δ / (ε / 8) ^ 2
  let A := 1 + s ^ 2 / ε ^ 2
  let R := 1 + L * Δ / ε ^ 2
  have heq : 4096 * s ^ 2 / (ε / 8) ^ 2 = 262144 * (s ^ 2 / ε ^ 2) := by ring
  have hDeq : D = 64 * (L * Δ / ε ^ 2) := by dsimp [D]; ring
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have ha : a ≤ 262144 * A := by
    dsimp [a, A]
    rw [heq]
    apply max_le <;> nlinarith [div_nonneg (sq_nonneg s) (sq_nonneg ε)]
  have hD : D ≤ 64 * R := by rw [hDeq]; dsimp [R]; linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hD0 : 0 < D := by dsimp [D]; positivity
  refine ⟨ha, hD, ?_⟩
  apply Real.log_le_log (by positivity : 0 < 1073741824 * a * D / (δ / 4))
  rw [show 1073741824 * a * D / (δ / 4) = 4294967296 * a * D / δ by ring]
  apply (div_le_div_iff_of_pos_right hδ).mpr
  have hprod := mul_le_mul ha hD hD0.le (show 0 ≤ 262144 * A by positivity)
  nlinarith

end LongTails.Proofs.MuonTuning
