import LongTails.Setups.PointwiseHessianStationarity
import LongTails.Proofs.RelativeHessianLocalized

namespace LongTails.Proofs.RelativeHessianTuning

open LongTails.Setups.PointwiseHessianStationarity

noncomputable def scale (p : Params) : ℝ := p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)
noncomputable def frequency (p : Params) : ℝ := Real.sqrt (p.L₀ + p.L₁ * p.ε) / (2 ^ 30 * Real.sqrt p.ε)
noncomputable def amplitude (p : Params) : ℝ := 16 * p.ε / frequency p
noncomputable def limit (p : Params) : ℕ := ⌊scale p / 2 ^ 39⌋₊
def edges (b : ℕ) : ℕ := 2 * b + 1

lemma curvature_pos {p : Params} (hp : broadSpec.valid p) : 0 < p.L₀ + p.L₁ * p.ε := by
  obtain ⟨h₀, h₁, hs, _, _, hε⟩ := hp
  by_cases hz : p.L₀ = 0
  · have hL : 0 < p.L₁ := by linarith
    simpa only [hz, zero_add] using mul_pos hL hε
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne h₀ (Ne.symm hz)) (mul_nonneg h₁ hε.le)

lemma frequency_pos {p : Params} (hp : broadSpec.valid p) : 0 < frequency p := by
  unfold frequency
  exact div_pos (Real.sqrt_pos.2 (curvature_pos hp)) (mul_pos (by norm_num) (Real.sqrt_pos.2 hp.2.2.2.2.2))

lemma amplitude_pos {p : Params} (hp : broadSpec.valid p) : 0 < amplitude p := by
  unfold amplitude
  exact div_pos (mul_pos (by norm_num) hp.2.2.2.2.2) (frequency_pos hp)

lemma product {p : Params} (hp : broadSpec.valid p) : amplitude p * frequency p = 16 * p.ε := by
  unfold amplitude
  exact div_mul_cancel₀ _ (frequency_pos hp).ne'

lemma frequency_square {p : Params} (hp : broadSpec.valid p) :
    frequency p ^ 2 = (p.L₀ + p.L₁ * p.ε) / (2 ^ 60 * p.ε) := by
  unfold frequency
  rw [div_pow, mul_pow, Real.sq_sqrt (curvature_pos hp).le, Real.sq_sqrt hp.2.2.2.2.2.le]
  norm_num

lemma absolute_scale {p : Params} (hp : broadSpec.valid p) :
    2 ^ 56 * amplitude p * frequency p ^ 3 = p.L₀ + p.L₁ * p.ε := by
  have hε := hp.2.2.2.2.2
  calc
    _ = 2 ^ 56 * (amplitude p * frequency p) * frequency p ^ 2 := by ring
    _ = 2 ^ 56 * (16 * p.ε) * ((p.L₀ + p.L₁ * p.ε) / (2 ^ 60 * p.ε)) := by rw [product hp, frequency_square hp]
    _ = _ := by field_simp; ring

lemma relative_scale {p : Params} (hp : broadSpec.valid p) :
    2 ^ 56 * frequency p ^ 2 * p.ε ≤ p.L₀ + p.L₁ * p.ε := by
  rw [frequency_square hp]
  have hε := hp.2.2.2.2.2
  have he : 2 ^ 56 * ((p.L₀ + p.L₁ * p.ε) / (2 ^ 60 * p.ε)) * p.ε =
      (p.L₀ + p.L₁ * p.ε) / 16 := by field_simp; ring
  rw [he]
  linarith [curvature_pos hp]

lemma scale_pos {p : Params} (hp : broadSpec.valid p) : 0 < scale p := by
  unfold scale
  exact div_pos (mul_pos hp.2.2.2.1 (Real.sqrt_pos.2 (curvature_pos hp)))
    (mul_pos hp.2.2.2.2.2 (Real.sqrt_pos.2 hp.2.2.2.2.2))

lemma amplitude_scale {p : Params} (hp : broadSpec.valid p) : amplitude p * scale p = 2 ^ 34 * p.Δ := by
  have hε := hp.2.2.2.2.2
  have hsε := Real.sqrt_pos.2 hε
  have hsL := Real.sqrt_pos.2 (curvature_pos hp)
  have hsL' : Real.sqrt (p.L₀ + p.ε * p.L₁) ≠ 0 := by simpa [mul_comm] using hsL.ne'
  unfold amplitude frequency scale
  field_simp [hsε.ne', hsL.ne', hsL', hε.ne']
  ring

lemma budget_count {p : Params} (hp : spec.valid p) {b : ℕ} (hb : b ≤ limit p) :
    (2 : ℝ) ^ 38 * (b + 1 : ℕ) ≤ scale p := by
  have hs : 2 ^ 39 ≤ scale p := hp.2.2.1
  have hbcast : (b : ℝ) ≤ (limit p : ℝ) := by exact_mod_cast hb
  have hb' : (b : ℝ) ≤ scale p / 2 ^ 39 :=
    hbcast.trans (Nat.floor_le (div_nonneg (scale_pos hp.1).le (by norm_num)))
  have hmul := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 39)).mp hb'
  push_cast
  nlinarith

lemma gap_budget {p : Params} (hp : spec.valid p) {b : ℕ} (hb : b ≤ limit p) :
    amplitude p * (4 * (edges b + 1 : ℕ)) ≤ p.Δ := by
  have hm := mul_le_mul_of_nonneg_left (budget_count hp hb) (amplitude_pos hp.1).le
  rw [amplitude_scale hp.1] at hm
  unfold edges
  push_cast at hm ⊢
  nlinarith [hp.1.2.2.2.1]

lemma count_le_ceil {p : Params} (hp : spec.valid p) {b : ℕ} (hb : b ≤ limit p) :
    edges b + 1 ≤ 1 + ⌈scale p⌉₊ := by
  have hn : ((edges b + 1 : ℕ) : ℝ) ≤ scale p := by
    have h := budget_count hp hb
    unfold edges
    push_cast at h ⊢
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  have hh : edges b + 1 ≤ ⌈scale p⌉₊ := by exact_mod_cast hn.trans (Nat.le_ceil (scale p))
  omega

lemma dimension_budget {p : Params} (hp : spec.valid p) {b : ℕ} (hb : b ≤ limit p) :
    0 < (p.d : ℝ) / 2 ∧ (p.d : ℝ) / 2 + (edges b + 1 : ℕ) ≤ p.d ∧
    4 * (b + 1 : ℕ) * (edges b + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius (edges b)) ^ 2 / (1 / 20) ^ 2) ≤ (p.d : ℝ) / 2 := by
  let M := 1 + ⌈scale p⌉₊
  let N := edges b + 1
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by dsimp [M]; omega)
  have hN : (0 : ℝ) ≤ N := by positivity
  have hNM : (N : ℝ) ≤ M := by exact_mod_cast count_le_ceil hp hb
  have hM4 : (M : ℝ) ≤ (M : ℝ) ^ 4 := le_self_pow₀ hM (by norm_num)
  have hNM4 : (N : ℝ) ≤ (M : ℝ) ^ 4 := hNM.trans hM4
  have hpow : (N : ℝ) ^ 4 ≤ (M : ℝ) ^ 4 := pow_le_pow_left₀ hN hNM 4
  have hd : (2 : ℝ) ^ 140 * (M : ℝ) ^ 4 ≤ p.d := by exact_mod_cast hp.2.2.2
  refine ⟨by nlinarith, by change (p.d : ℝ) / 2 + N ≤ p.d; nlinarith, ?_⟩
  have hbN : ((b + 1 : ℕ) : ℝ) ≤ N := by dsimp [N, edges]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) b]
  calc
    _ = 6400 * 2 ^ 120 * (b + 1 : ℕ) * (N : ℝ) ^ 3 := by
      dsimp [N, RelativeHessianLocalized.radius]
      ring
    _ ≤ 6400 * 2 ^ 120 * (N : ℝ) ^ 4 := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hbN (pow_nonneg hN 3))
        (by norm_num : (0 : ℝ) ≤ 6400 * 2 ^ 120)
      nlinarith
    _ ≤ 6400 * 2 ^ 120 * (M : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ _ := by nlinarith

lemma pure_relative_nonempty : ∃ p : Params, spec.valid p ∧ p.L₀ = 0 ∧ p.L₁ = 1 := by
  let p : Params := ⟨2 ^ 140 * (1 + 2 ^ 39) ^ 4, 0, 1, 2 ^ 39, 16, 1⟩
  refine ⟨p, ?_, rfl, rfl⟩
  norm_num [spec, broadSpec, p]

end LongTails.Proofs.RelativeHessianTuning
