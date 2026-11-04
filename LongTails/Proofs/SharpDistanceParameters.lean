import LongTails.Proofs.SharpEnvelopeParameters

namespace LongTails.Proofs.SharpDistanceParameters

open OracleTemplate LongTails.Algorithms.SharpEnvelope SharpEnvelopeParameters

noncomputable def iterations (b : ℕ) : ℕ := ⌈4096 * (b : ℝ) ^ 16 * (1 + Real.log b)⌉₊

lemma warm_logarithm {L μ : ℝ} {b d i : ℕ} (hb : 2 ≤ b)
    (hμ : 0 < μ) (hrel : L = ratio b * μ) :
    Real.log (1 + (L + μ) / (32 * precision b d i ^ 2 * μ)) ≤ 64 * (1 + Real.log b) := by
  let β := precision b d i
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hβ : 0 < β := precision_pos (by omega) d i
  have hp := precision_lower (by omega : 1 ≤ b) d i
  change 1 / (100 * (b : ℝ) ^ 12) ≤ β at hp
  have hprod : 1 / 100 ≤ β * (b : ℝ) ^ 12 := by
    rw [div_le_iff₀ (by positivity)] at hp
    nlinarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 100) hprod 2
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ (b : ℝ) ^ 32 by positivity)
  have hsum : L + μ = 4 * (b : ℝ) ^ 32 * μ := by rw [hrel, ratio]; ring
  have hid : (L + μ) / (32 * β ^ 2 * μ) = (b : ℝ) ^ 32 / (8 * β ^ 2) := by
    rw [hsum]
    field_simp
    norm_num
  have hratio : (b : ℝ) ^ 32 / (8 * β ^ 2) ≤ 1250 * (b : ℝ) ^ 56 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hm]
  have hb56 : (1 : ℝ) ≤ (b : ℝ) ^ 56 := one_le_pow₀ (by linarith)
  have hsum' : 1 + (b : ℝ) ^ 32 / (8 * β ^ 2) ≤ 2048 * (b : ℝ) ^ 56 := by
    linarith
  change Real.log (1 + (L + μ) / (32 * β ^ 2 * μ)) ≤ _
  rw [hid]
  have hlog := Real.log_le_log (by positivity : 0 < 1 + (b : ℝ) ^ 32 / (8 * β ^ 2)) hsum'
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl2048 : Real.log 2048 ≤ 11 := by
    have he : (2048 : ℝ) = 2 ^ 11 := by norm_num
    rw [he, Real.log_pow]
    norm_num
    linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  norm_num at hlog
  linarith

lemma warm_transient {L μ : ℝ} {b d i : ℕ} (hb : 16 ≤ b) (hi : i ≤ d)
    (hμ : 0 < μ) (hrel : L = ratio b * μ) :
    (1 - InexactGradient.momentum (L + μ) μ (2 * precision b d i) / 2) ^ (iterations b) * (L + μ) ≤
      32 * precision b d i ^ 2 * μ := by
  let β := precision b d i
  let θ := InexactGradient.momentum (L + μ) μ (2 * β)
  have hβ : 0 < β := precision_pos (by omega) d i
  have hβsmall : β ≤ 1 / 32 := precision_small (by omega) hi
  have hL0 : 0 < L := by rw [hrel]; exact mul_pos (ratio_pos (by omega)) hμ
  have hL : μ ≤ L + μ := by linarith
  obtain ⟨ht0, ht1, _⟩ := InexactGradient.momentum_bounds hμ hL
    (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  refine PLGradient.geometric_budget 2 θ (L + μ) (32 * β ^ 2 * μ) ht0 (by linarith)
    (by linarith) (by positivity) (iterations b) ?_
  apply Nat.ceil_le.mpr
  have hc := warm_momentum (by omega : 1 ≤ b) hi hμ hrel
  have hl := warm_logarithm (d := d) (i := i) (by omega : 2 ≤ b) hμ hrel
  have hn : 0 ≤ Real.log (1 + (L + μ) / (32 * β ^ 2 * μ)) :=
    Real.log_nonneg (by
      have hp : 0 ≤ (L + μ) / (32 * β ^ 2 * μ) := by positivity
      linarith)
  have hh := mul_le_mul hc hl hn (by positivity : 0 ≤ 32 * (b : ℝ) ^ 16)
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hbR
  have hc : 4096 * (b : ℝ) ^ 16 * (1 + Real.log b) ≤ iterations b := Nat.le_ceil _
  change 2 / θ * Real.log (1 + (L + μ) / (32 * β ^ 2 * μ)) ≤ _ at hh
  dsimp only [θ, β] at hh ⊢
  nlinarith only [hh, hc, mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ b) 16)
    (show 0 ≤ 1 + Real.log b by linarith)]

lemma refinement_transient {b d : ℕ} (hb : 16 ≤ b)
    (hd : 16 * ((d : ℝ) + 1) ≤ b) :
    (1 - momentum b) ^ iterations b ≤ (1 / (8 * ((d : ℝ) + 1))) ^ 2 / 4096 := by
  let τ : ℝ := 1 / (8 * ((d : ℝ) + 1))
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hb0 : (0 : ℝ) < b := by linarith
  have ht : 0 < momentum b := by unfold momentum; positivity
  have ht1 : momentum b ≤ 1 := by
    unfold momentum
    apply (div_le_one (by positivity)).mpr
    have hp := one_le_pow₀ hbR (n := 16)
    linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hD : 0 ≤ (d : ℝ) + 1 := by positivity
  have hdsq := pow_le_pow_left₀ (show 0 ≤ 16 * ((d : ℝ) + 1) by positivity) hd 2
  have hr : 4096 / τ ^ 2 ≤ 1024 * (b : ℝ) ^ 2 := by
    dsimp [τ]
    field_simp
    nlinarith only [hdsq]
  have hb2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := one_le_pow₀ hbR
  have hl := Real.log_le_log (show 0 < 1 + 4096 / τ ^ 2 by positivity)
    (show 1 + 4096 / τ ^ 2 ≤ 2048 * (b : ℝ) ^ 2 by linarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hbR
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl2048 : Real.log 2048 ≤ 11 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlogbound : Real.log (1 + 4096 / τ ^ 2) ≤ 1024 * (1 + Real.log b) := by
    norm_num at hl
    linarith
  have hm : 1 / momentum b = 4 * (b : ℝ) ^ 16 := by unfold momentum; field_simp
  have hn : ⌈1 / momentum b * Real.log (1 + 4096 / τ ^ 2)⌉₊ ≤ iterations b := by
    apply Nat.ceil_le.mpr
    rw [hm]
    have hh := mul_le_mul_of_nonneg_left hlogbound (show 0 ≤ 4 * (b : ℝ) ^ 16 by positivity)
    have hc : 4096 * (b : ℝ) ^ 16 * (1 + Real.log b) ≤ iterations b := Nat.le_ceil _
    nlinarith only [hh, hc]
  have hh := PLGradient.geometric_budget 1 (momentum b) 4096 (τ ^ 2)
    ht ht1 (by norm_num) (by positivity) (iterations b) hn
  dsimp only [τ] at hh
  norm_num only [div_one] at hh
  linarith

end LongTails.Proofs.SharpDistanceParameters
