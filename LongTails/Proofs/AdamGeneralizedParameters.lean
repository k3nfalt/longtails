import LongTails.Algorithms.GeneralizedSmoothAdam
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Proofs.AdamGeneralizedParameters

lemma scale_controls {d : ℕ} {u K δ : ℝ} (hu : 0 ≤ u) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hscale : u * (d + 1) * (1 + K) ^ 2 ≤ δ) :
    u * K ≤ δ ∧ u * K * Real.sqrt d ≤ δ ∧
      u * K * d * (1 + K) ≤ δ ∧ u ^ 2 * K ^ 2 * d * (1 + K) ≤ δ ^ 2 := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hs2 := Real.sq_sqrt hd
  have hsD : Real.sqrt d ≤ d + 1 := by nlinarith [sq_nonneg (Real.sqrt d - 1)]
  have hH : 0 ≤ 1 + K := by linarith
  have hbasic : u * K ≤ δ := by
    have hweight : K ≤ (d + 1) * (1 + K) ^ 2 := by
      have hh := mul_nonneg hd (sq_nonneg (1 + K))
      nlinarith [sq_nonneg K]
    have hh := mul_le_mul_of_nonneg_left hweight hu
    nlinarith
  have hsqrt : u * K * Real.sqrt d * (1 + K) ≤ δ := by
    have hw : K * Real.sqrt d * (1 + K) ≤ (d + 1) * (1 + K) ^ 2 := by
      have hh := mul_le_mul (show K ≤ 1 + K by linarith) hsD hs hH
      have hh' := mul_le_mul_of_nonneg_right hh hH
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hw hu
    nlinarith
  have hsqrt0 : 0 ≤ u * K * Real.sqrt d := by positivity
  have hsqrt' : u * K * Real.sqrt d ≤ δ := by
    nlinarith [mul_nonneg hsqrt0 hK]
  have hlinear : u * K * d * (1 + K) ≤ δ := by
    have hw : K * d * (1 + K) ≤ (d + 1) * (1 + K) ^ 2 := by
      have hh := mul_le_mul (show K ≤ 1 + K by linarith) (show (d : ℝ) ≤ d + 1 by linarith) hd hH
      have hh' := mul_le_mul_of_nonneg_right hh hH
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hw hu
    nlinarith
  have hquad : u ^ 2 * K ^ 2 * d * (1 + K) ≤ δ ^ 2 := by
    have hh := mul_le_mul hsqrt hsqrt' hsqrt0 hδ
    have he : (u * K * Real.sqrt d * (1 + K)) * (u * K * Real.sqrt d) =
        u ^ 2 * K ^ 2 * d * (1 + K) := by
      calc
        _ = u ^ 2 * K ^ 2 * (Real.sqrt d) ^ 2 * (1 + K) := by ring
        _ = _ := by rw [hs2]
    rw [he] at hh
    nlinarith
  exact ⟨hbasic, hsqrt', hlinear, hquad⟩

lemma log_curvature_scale {K : ℝ} (hK : 0 ≤ K) : Real.log (1 + 2 * K ^ 2) ≤ 4 * K := by
  have hpos : 0 < 1 + 2 * K := by positivity
  have hh := Real.log_le_log (by positivity : 0 < 1 + 2 * K ^ 2)
    (show 1 + 2 * K ^ 2 ≤ (1 + 2 * K) ^ 2 by nlinarith [sq_nonneg K])
  rw [Real.log_pow] at hh
  have hl := Real.log_le_sub_one_of_pos hpos
  norm_num at hh
  linarith

lemma scale_envelopes {d : ℕ} {β K : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hK : 0 ≤ K) :
    let a := (1 - β) ^ 2 / (2 ^ 20 * (d + 1) * (1 + K) ^ 2)
    0 < a ∧ 0 ≤ β / (1 - β) ∧
      a * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ) ∧
      (β / (1 - β) * a) * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ) := by
  dsimp
  have hb : 0 < 1 - β := by linarith
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hk : 0 < 1 + K := by positivity
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · have he : (1 - β) ^ 2 / (2 ^ 20 * (d + 1) * (1 + K) ^ 2) * (d + 1) * (1 + K) ^ 2 =
        (1 - β) ^ 2 / 2 ^ 20 := by field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  · have he : (β / (1 - β) * ((1 - β) ^ 2 / (2 ^ 20 * (d + 1) * (1 + K) ^ 2))) *
        (d + 1) * (1 + K) ^ 2 = β * (1 - β) / 2 ^ 20 := by field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg β]

lemma log_calibration {d : ℕ} {a r K : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hscale : a * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (hrscale : (r * a) * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ)) :
    let c := d * (3 * K ^ 2 * (1 + r ^ 2) * a ^ 2 + 3 * K * r * a)
    0 ≤ c ∧ c ≤ 1 / 64 ∧
      K * r * a * Real.sqrt d + 12 * K * a + c * (2 + Real.log (1 + 2 * K ^ 2)) ≤ 1 ∧
      128 * (2 * a * K * Real.sqrt d) ≤ 1 ∧ 8192 * (4 * a ^ 2 * K ^ 2) ≤ 1 / 4 := by
  let c := d * (3 * K ^ 2 * (1 + r ^ 2) * a ^ 2 + 3 * K * r * a)
  have h1 := scale_controls ha hK (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 20) hscale
  have h2 := scale_controls (mul_nonneg hr ha) hK (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 20) hrscale
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : c * (1 + K) ≤ (1 / 2 ^ 18 : ℝ) := by
    dsimp [c]
    nlinarith [h1.2.2.2, h2.2.2.1, h2.2.2.2]
  have hc' : c ≤ (1 / 2 ^ 18 : ℝ) := by nlinarith [mul_nonneg hc0 hK]
  refine ⟨hc0, by linarith, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left (log_curvature_scale hK) hc0
    have hh' : c * (2 + 4 * K) ≤ 4 * c * (1 + K) := by nlinarith
    change K * r * a * Real.sqrt d + 12 * K * a + c * (2 + Real.log (1 + 2 * K ^ 2)) ≤ 1
    nlinarith [h1.1, h2.2.1]
  · nlinarith [h1.2.1]
  · have hp := pow_le_pow_left₀ (mul_nonneg ha hK) h1.1 2
    nlinarith

lemma variance_scale {T : ℕ} (hT : 0 < T) (a K σ : ℝ) :
    (128 : ℝ) ^ 2 * T * ((a / Real.sqrt T) ^ 2 * K ^ 2 * σ ^ 2 / ((1 + σ ^ 2) / 4)) / 2 ≤
      8192 * (4 * a ^ 2 * K ^ 2) := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hv : 0 < 1 + σ ^ 2 := by positivity
  have he : (128 : ℝ) ^ 2 * T * ((a / Real.sqrt T) ^ 2 * K ^ 2 * σ ^ 2 / ((1 + σ ^ 2) / 4)) / 2 =
      (8192 * (4 * a ^ 2 * K ^ 2)) * (σ ^ 2 / (1 + σ ^ 2)) := by
    rw [div_pow, Real.sq_sqrt ht.le]
    field_simp
    ring
  rw [he]
  apply mul_le_of_le_one_right (by positivity)
  exact (div_le_one hv).2 (by linarith)

lemma exponential_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    2 * Real.exp x ≤ 3 := by
  have hbound : |x| ≤ 1 := by rw [abs_of_nonneg hx]; linarith
  have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hbound)).2
  have hs := mul_self_le_mul_self hx hx1
  nlinarith

lemma original_calibration {d : ℕ} {a r K : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hscale : a * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (hrscale : (r * a) * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ)) :
    d * (K ^ 2 * (1 + r ^ 2) * a ^ 2 + 6 * K * r * a) ≤ 1 ∧
      24 * K * a ≤ 1 ∧ K * (1 + 4 * r) * a * Real.sqrt d ≤ 1 / 2 := by
  have h1 := scale_controls ha hK (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 20) hscale
  have h2 := scale_controls (mul_nonneg hr ha) hK (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 20) hrscale
  have hc := (log_calibration ha hr hK hscale hrscale).2.1
  refine ⟨?_, ?_, ?_⟩
  · have hh : 0 ≤ (d : ℝ) * K ^ 2 * (1 + r ^ 2) * a ^ 2 := by positivity
    nlinarith
  · nlinarith [h1.1]
  · nlinarith [h1.2.1, h2.2.1]

lemma geometry_scale {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) :
    let K := 4 * (1 + L0 + L1)
    1 ≤ K ∧ L1 ≤ K ∧ L0 + 2 * L1 * K ≤ K ^ 2 := by
  dsimp
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg L0, sq_nonneg L1, mul_nonneg hL0 hL1]

lemma signal_moment_constant {K Φ a : ℝ} (hK : 4 ≤ K) (hΦ : 1 ≤ Φ)
    (ha : 0 ≤ a) (haK : a * K ≤ 1) :
    4 * ((Φ - 1) ^ 2 + (128 * K ^ 2 * (16 * Φ ^ 2) ^ 4 + 32 * (16 * Φ ^ 2) ^ 2) +
      (16 * Φ ^ 2) ^ 2 + 4 * a ^ 2 * K ^ 2 * (16 * Φ ^ 2) ^ 2) ≤ (2048 * K ^ 2 * Φ ^ 4) ^ 2 := by
  have hk : 0 ≤ K := by linarith
  have hφ : 0 ≤ Φ := by linarith
  have hφ2 : 1 ≤ Φ ^ 2 := by nlinarith
  have hφ4 : 1 ≤ Φ ^ 4 := by nlinarith [sq_nonneg (Φ ^ 2 - 1)]
  have hφ24 : Φ ^ 2 ≤ Φ ^ 4 := by nlinarith
  have hφ48 : Φ ^ 4 ≤ Φ ^ 8 := by nlinarith [sq_nonneg (Φ ^ 4 - 1)]
  have hk2 : 16 ≤ K ^ 2 := by nlinarith
  have ha2 : a ^ 2 * K ^ 2 ≤ 1 := by nlinarith [mul_nonneg ha hk]
  have hd : (Φ - 1) ^ 2 ≤ (16 * Φ ^ 2) ^ 2 := by nlinarith
  have hc : 0 ≤ (16 * Φ ^ 2) ^ 2 := sq_nonneg _
  have hnoise := mul_le_mul_of_nonneg_right ha2 hc
  have hsmall : (16 * Φ ^ 2) ^ 2 ≤ K ^ 2 * (16 * Φ ^ 2) ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hk2 (show 0 ≤ Φ ^ 8 by positivity)
    nlinarith
  have hbig : 1024 * K ^ 2 * (16 * Φ ^ 2) ^ 4 ≤ (2048 * K ^ 2 * Φ ^ 4) ^ 2 := by
    have hh := mul_nonneg (show 0 ≤ K ^ 2 - 16 by linarith) (show 0 ≤ K ^ 2 * Φ ^ 8 by positivity)
    nlinarith
  nlinarith
lemma simplify_rate {d : ℕ} {K β v Φ t : ℝ} (hK : 4 ≤ K) (hβ : β < 1)
    (ht : 0 < t) :
    let a := (1 - β) ^ 2 / (2 ^ 20 * (d + 1) * (1 + K) ^ 2)
    (64 * K * Real.sqrt v * Φ ^ 2) * (2048 * K ^ 2 * Φ ^ 4) / (a * t) ≤
      2 ^ 38 * (d + 1) * K ^ 5 * Real.sqrt v * Φ ^ 6 / ((1 - β) ^ 2 * t) := by
  have hb : 0 < 1 - β := by linarith
  have hk : 0 < 1 + K := by linarith
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hke : (1 + K) ^ 2 ≤ 2 * K ^ 2 := by nlinarith
  dsimp
  have he : (64 * K * Real.sqrt v * Φ ^ 2) * (2048 * K ^ 2 * Φ ^ 4) /
      (((1 - β) ^ 2 / (2 ^ 20 * (d + 1) * (1 + K) ^ 2)) * t) =
      (2 ^ 37 * (d + 1) * K ^ 3 * Real.sqrt v * Φ ^ 6) * (1 + K) ^ 2 / ((1 - β) ^ 2 * t) := by
    field_simp; ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := mul_le_mul_of_nonneg_left hke (by positivity : 0 ≤ 2 ^ 37 * (d + 1) * K ^ 3 * Real.sqrt v * Φ ^ 6)
  convert hh using 1; ring
lemma horizon_memory {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) {T : ℕ}
    (hT : 2 / (1 - β) ≤ (T : ℝ)) :
    2 ≤ T ∧ (1 + β) / 2 ≤ 1 - 1 / (T : ℝ) := by
  have hb : 0 < 1 - β := by linarith
  have ht2 : (2 : ℝ) ≤ T := by
    have hh : (2 : ℝ) ≤ 2 / (1 - β) := (le_div_iff₀ hb).2 (by nlinarith)
    exact hh.trans hT
  have ht : (0 : ℝ) < T := by linarith
  refine ⟨by exact_mod_cast ht2, ?_⟩
  have hh := (div_le_iff₀ hb).1 hT
  have hi : 1 / (T : ℝ) ≤ (1 - β) / 2 := (div_le_iff₀ ht).2 (by nlinarith)
  linarith
lemma square_root_accuracy {N b ε T : ℝ} (hb : 0 < b) (hε : 0 < ε) (hT : 0 < T)
    (hbound : N ^ 2 ≤ ε ^ 4 * b ^ 4 * T) : N / (b ^ 2 * Real.sqrt T) ≤ ε ^ 2 := by
  have hd : 0 < b ^ 2 * Real.sqrt T := by positivity
  apply (div_le_iff₀ hd).2
  have hh : (ε ^ 2 * (b ^ 2 * Real.sqrt T)) ^ 2 = ε ^ 4 * b ^ 4 * T := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]
    ring
  have hp : 0 ≤ ε ^ 2 * (b ^ 2 * Real.sqrt T) := by positivity
  nlinarith [sq_nonneg (N - ε ^ 2 * (b ^ 2 * Real.sqrt T))]

lemma horizon_accuracy {d : ℕ} {S σ Φ β ε T : ℝ} (hβ : β < 1) (hε : 0 < ε) (hT : 0 < T)
    (hbudget : 2 ^ 100 * (d + 1) ^ 2 * S ^ 10 * (1 + σ ^ 2) * Φ ^ 12 /
      ((1 - β) ^ 4 * ε ^ 4) ≤ T) :
    2 ^ 38 * (d + 1) * (4 * S) ^ 5 * Real.sqrt (1 + σ ^ 2) * Φ ^ 6 /
      ((1 - β) ^ 2 * Real.sqrt T) ≤ ε ^ 2 := by
  have hb : 0 < 1 - β := by linarith
  have hv : 0 ≤ 1 + σ ^ 2 := by positivity
  apply square_root_accuracy hb hε hT
  have hh := (div_le_iff₀ (by positivity : 0 < (1 - β) ^ 4 * ε ^ 4)).1 hbudget
  have he : (2 ^ 38 * (d + 1) * (4 * S) ^ 5 * Real.sqrt (1 + σ ^ 2) * Φ ^ 6) ^ 2 =
      2 ^ 96 * (d + 1) ^ 2 * S ^ 10 * (1 + σ ^ 2) * Φ ^ 12 := by
    simp only [mul_pow, Real.sq_sqrt hv]
    ring
  rw [he]
  have hnon : 0 ≤ (d + 1 : ℝ) ^ 2 * S ^ 10 * (1 + σ ^ 2) * Φ ^ 12 := by positivity
  nlinarith
end LongTails.Proofs.AdamGeneralizedParameters
