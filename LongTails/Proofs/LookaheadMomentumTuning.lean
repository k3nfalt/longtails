import LongTails.Proofs.LookaheadMomentumMain
import LongTails.Proofs.LookaheadMomentumTaylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.LookaheadMomentum

open LongTails.Proofs.LookaheadMomentumTaylor

noncomputable def tγ (σ ε : ℝ) : ℝ := ε ^ 2 / (ε ^ 2 + 300 * σ ^ 2)

noncomputable def tr (L₁ L₂ L₃ ε : ℝ) : ℝ :=
  max (ε / (32 * L₁)) (max (Real.sqrt (ε / (40 * L₂))) ((ε / (56 * L₃)) ^ (1 / 3 : ℝ)))

noncomputable def tη (L₁ L₂ L₃ σ ε : ℝ) : ℝ := min (tγ σ ε * tr L₁ L₂ L₃ ε) (ε / (2 * L₁))

noncomputable def tunedConfig (L₁ L₂ L₃ σ Δ ε : ℝ) : Config where
  n0 := ⌈1 / tγ σ ε⌉₊
  T := ⌈5 * Δ / (tη L₁ L₂ L₃ σ ε * ε)⌉₊
  γ := tγ σ ε
  η := tη L₁ L₂ L₃ σ ε

noncomputable def complexity (L₁ L₂ L₃ ε : ℝ) : ℝ :=
  min (L₁ / ε) (min (Real.sqrt (L₂ / ε)) ((L₃ / ε) ^ (1 / 3 : ℝ)))

variable {L₁ L₂ L₃ σ Δ ε : ℝ}

lemma tγ_pos (hε : 0 < ε) : 0 < tγ σ ε := by unfold tγ; positivity

lemma tγ_le_one (hε : 0 < ε) : tγ σ ε ≤ 1 := by
  unfold tγ
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg σ]

lemma tγ_inv (hε : 0 < ε) : 1 / tγ σ ε = 1 + 300 * σ ^ 2 / ε ^ 2 := by
  unfold tγ
  field_simp

lemma tγ_noise (hε : 0 < ε) : tγ σ ε * σ ^ 2 ≤ ε ^ 2 / 300 := by
  unfold tγ
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg σ, sq_nonneg ε, mul_nonneg (sq_nonneg ε) (sq_nonneg ε)]

lemma cube_rpow {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma one_le_of_one_le_pow {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : n ≠ 0) (h : 1 ≤ y ^ n) : 1 ≤ y := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.mpr (pow_lt_one₀ hy hc hn))

lemma tr_pos (hL₁ : 0 < L₁) (hε : 0 < ε) : 0 < tr L₁ L₂ L₃ ε :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

lemma tη_pos (hL₁ : 0 < L₁) (hε : 0 < ε) : 0 < tη L₁ L₂ L₃ σ ε :=
  lt_min (mul_pos (tγ_pos hε) (tr_pos hL₁ hε)) (by positivity)

lemma tr_case (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) (hε : 0 < ε) :
    32 * L₁ * tr L₁ L₂ L₃ ε ≤ ε ∨ 40 * L₂ * tr L₁ L₂ L₃ ε ^ 2 ≤ ε ∨
      56 * L₃ * tr L₁ L₂ L₃ ε ^ 3 ≤ ε := by
  unfold tr
  rcases max_choice (ε / (32 * L₁)) (max (Real.sqrt (ε / (40 * L₂))) ((ε / (56 * L₃)) ^ (1 / 3 : ℝ)))
    with h | h
  · left
    rw [h]
    exact le_of_eq (by field_simp)
  · rw [h]
    rcases max_choice (Real.sqrt (ε / (40 * L₂))) ((ε / (56 * L₃)) ^ (1 / 3 : ℝ)) with h' | h'
    · right; left
      rw [h', Real.sq_sqrt (by positivity)]
      exact le_of_eq (by field_simp)
    · right; right
      rw [h', cube_rpow (by positivity)]
      exact le_of_eq (by field_simp)

lemma inv_tr_le (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) (hε : 0 < ε) :
    1 / tr L₁ L₂ L₃ ε ≤ 32 * complexity L₁ L₂ L₃ ε := by
  have hr := tr_pos (L₂ := L₂) (L₃ := L₃) hL₁ hε
  rw [div_le_iff₀ hr]
  unfold complexity
  have h1 : ε / (32 * L₁) ≤ tr L₁ L₂ L₃ ε := le_max_left _ _
  have h2 : Real.sqrt (ε / (40 * L₂)) ≤ tr L₁ L₂ L₃ ε :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h3 : (ε / (56 * L₃)) ^ (1 / 3 : ℝ) ≤ tr L₁ L₂ L₃ ε :=
    (le_max_right _ _).trans (le_max_right _ _)
  rcases min_choice (L₁ / ε) (min (Real.sqrt (L₂ / ε)) ((L₃ / ε) ^ (1 / 3 : ℝ))) with h | h
  · rw [h]
    calc (1 : ℝ) = 32 * (L₁ / ε) * (ε / (32 * L₁)) := by field_simp
      _ ≤ 32 * (L₁ / ε) * tr L₁ L₂ L₃ ε := mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [h]
    rcases min_choice (Real.sqrt (L₂ / ε)) ((L₃ / ε) ^ (1 / 3 : ℝ)) with h' | h'
    · rw [h']
      have hy : 1 ≤ 32 * Real.sqrt (L₂ / ε) * Real.sqrt (ε / (40 * L₂)) := by
        apply one_le_of_one_le_pow (by positivity) (two_ne_zero)
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        have e : (32 : ℝ) ^ 2 * (L₂ / ε) * (ε / (40 * L₂)) = 1024 / 40 := by
          field_simp
          norm_num
        rw [e]; norm_num
      exact hy.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    · rw [h']
      have hy : 1 ≤ 32 * (L₃ / ε) ^ (1 / 3 : ℝ) * (ε / (56 * L₃)) ^ (1 / 3 : ℝ) := by
        apply one_le_of_one_le_pow (by positivity) (three_ne_zero)
        rw [mul_pow, mul_pow, cube_rpow (by positivity), cube_rpow (by positivity)]
        have e : (32 : ℝ) ^ 3 * (L₃ / ε) * (ε / (56 * L₃)) = 32768 / 56 := by
          field_simp
          norm_num
        rw [e]; norm_num
      exact hy.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

lemma complexity_le (hL₁ : 0 < L₁) (hL₃ : 0 < L₃) (hε : 0 < ε) :
    0 ≤ complexity L₁ L₂ L₃ ε ∧ complexity L₁ L₂ L₃ ε ≤ L₁ / ε := by
  unfold complexity
  exact ⟨le_min (by positivity) (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)),
    min_le_left _ _⟩

section Coefficients

variable {γ : ℝ}

lemma coeff_identities (hγ : 0 < γ) :
    (1 - γ) * (2 - γ) / 2 * (-1) + γ * (2 - γ) * ((1 - γ) / γ) +
        -(γ * (1 - γ) / 2) * ((2 - γ) / γ) = 0 ∧
    (1 - γ) * (2 - γ) / 2 * (-1) ^ 2 + γ * (2 - γ) * ((1 - γ) / γ) ^ 2 +
        -(γ * (1 - γ) / 2) * ((2 - γ) / γ) ^ 2 = 0 := by
  constructor <;> field_simp <;> ring

lemma coeff_first (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    |(1 - γ) * (2 - γ) / 2| * |(-1 : ℝ)| + |γ * (2 - γ)| * |(1 - γ) / γ| +
        |-(γ * (1 - γ) / 2)| * |(2 - γ) / γ| ≤ 4 := by
  have hu : 0 ≤ 1 - γ := by linarith
  have hv : 0 < 2 - γ := by linarith
  rw [abs_of_nonneg (by positivity), abs_neg, abs_one, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), abs_neg, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  have e : (1 - γ) * (2 - γ) / 2 * 1 + γ * (2 - γ) * ((1 - γ) / γ) +
      γ * (1 - γ) / 2 * ((2 - γ) / γ) = 2 * ((1 - γ) * (2 - γ)) := by field_simp; ring
  rw [e]
  nlinarith [mul_nonneg hu hγ.le]

lemma coeff_second (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    |(1 - γ) * (2 - γ) / 2| * (-1 : ℝ) ^ 2 + |γ * (2 - γ)| * ((1 - γ) / γ) ^ 2 +
        |-(γ * (1 - γ) / 2)| * ((2 - γ) / γ) ^ 2 ≤ 5 / γ := by
  have hu : 0 ≤ 1 - γ := by linarith
  have hu1 : 1 - γ ≤ 1 := by linarith
  have hv : 0 < 2 - γ := by linarith
  have hv2 : 2 - γ ≤ 2 := by linarith
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), abs_neg,
    abs_of_nonneg (by positivity)]
  have e : (1 - γ) * (2 - γ) / 2 * (-1 : ℝ) ^ 2 + γ * (2 - γ) * ((1 - γ) / γ) ^ 2 +
      γ * (1 - γ) / 2 * ((2 - γ) / γ) ^ 2 =
      (γ * ((1 - γ) * (2 - γ)) / 2 + (2 - γ) * (1 - γ) ^ 2 + (1 - γ) * (2 - γ) ^ 2 / 2) / γ := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hγ.le
  have p1 : (1 - γ) * (2 - γ) ≤ 2 := by nlinarith
  have p2 : (2 - γ) * (1 - γ) ^ 2 ≤ 2 := by
    have : (1 - γ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hv.le]
  have p3 : (1 - γ) * (2 - γ) ^ 2 ≤ 4 := by
    have : (2 - γ) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hu, mul_nonneg hu (sq_nonneg (2 - γ))]
  have p0 : γ * ((1 - γ) * (2 - γ)) ≤ 2 := by
    nlinarith [mul_nonneg hu hv.le, mul_le_mul_of_nonneg_right hγ1 (mul_nonneg hu hv.le)]
  linarith

lemma coeff_third (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    |(1 - γ) * (2 - γ) / 2| * |(-1 : ℝ)| ^ 3 + |γ * (2 - γ)| * |(1 - γ) / γ| ^ 3 +
        |-(γ * (1 - γ) / 2)| * |(2 - γ) / γ| ^ 3 ≤ 7 / γ ^ 2 := by
  have hu : 0 ≤ 1 - γ := by linarith
  have hu1 : 1 - γ ≤ 1 := by linarith
  have hv : 0 < 2 - γ := by linarith
  have hv2 : 2 - γ ≤ 2 := by linarith
  rw [abs_of_nonneg (by positivity), abs_neg, abs_one, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), abs_neg, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  have e : (1 - γ) * (2 - γ) / 2 * (1 : ℝ) ^ 3 + γ * (2 - γ) * ((1 - γ) / γ) ^ 3 +
      γ * (1 - γ) / 2 * ((2 - γ) / γ) ^ 3 =
      (γ ^ 2 * ((1 - γ) * (2 - γ)) / 2 + (2 - γ) * (1 - γ) ^ 3 + (1 - γ) * (2 - γ) ^ 3 / 2) /
        γ ^ 2 := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have p1 : (1 - γ) * (2 - γ) ≤ 2 := by nlinarith
  have p2 : (2 - γ) * (1 - γ) ^ 3 ≤ 2 := by
    have : (1 - γ) ^ 3 ≤ 1 := pow_le_one₀ hu hu1
    nlinarith [mul_le_mul_of_nonneg_left this hv.le]
  have p3 : (1 - γ) * (2 - γ) ^ 3 ≤ 8 := by
    have : (2 - γ) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hv.le hv2 3
    nlinarith [mul_le_mul_of_nonneg_left this hu, mul_nonneg hu (pow_nonneg hv.le 3)]
  have p0 : γ ^ 2 * ((1 - γ) * (2 - γ)) ≤ 2 := by
    have hg2 : γ ^ 2 ≤ 1 := pow_le_one₀ hγ.le hγ1
    nlinarith [mul_nonneg hu hv.le, mul_le_mul_of_nonneg_right hg2 (mul_nonneg hu hv.le)]
  linarith

end Coefficients

section Drift

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {grad : E → E} {hess : E → E →L[ℝ] E} {third : E → E →L[ℝ] E →L[ℝ] E}

lemma drift_le (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃)
    (hd : ∀ x, HasFDerivAt grad (hess x) x) (hd₂ : ∀ x, HasFDerivAt hess (third x) x)
    (hl₁ : ∀ x y, ‖grad x - grad y‖ ≤ L₁ * ‖x - y‖)
    (hl₂ : ∀ x y, ‖hess x - hess y‖ ≤ L₂ * ‖x - y‖)
    (hl₃ : ∀ x y, ‖third x - third y‖ ≤ L₃ * ‖x - y‖)
    (cfg : Config) (hγ : 0 < cfg.γ) (hγ1 : cfg.γ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : cfg.η ≤ cfg.γ * r)
    (hcase : 32 * L₁ * r ≤ ε ∨ 40 * L₂ * r ^ 2 ≤ ε ∨ 56 * L₃ * r ^ 3 ≤ ε)
    (x x' : E) (hx : ‖x' - x‖ ≤ cfg.η) : ‖drift cfg grad x x'‖ ≤ cfg.γ * (ε / 8) := by
  have e : x' + (-1 : ℝ) • (x' - x) = x := by rw [neg_one_smul]; abel
  have hn := norm_nonneg (x' - x)
  have hdr : ‖x' - x‖ ≤ cfg.γ * r := hx.trans hr
  obtain ⟨hi₁, hi₂⟩ := coeff_identities hγ
  rcases hcase with hc | hc | hc
  · have key := three_point_first hl₁ x' (x' - x) (keep cfg) (weightNear cfg) (weightFar cfg)
      (-1) ((1 - cfg.γ) / cfg.γ) ((2 - cfg.γ) / cfg.γ)
    rw [e] at key
    change ‖drift cfg grad x x'‖ ≤ _ at key
    refine key.trans ?_
    have hco := coeff_first hγ hγ1
    change |keep cfg| * |(-1 : ℝ)| + |weightNear cfg| * |(1 - cfg.γ) / cfg.γ| +
      |weightFar cfg| * |(2 - cfg.γ) / cfg.γ| ≤ 4 at hco
    calc L₁ * ‖x' - x‖ * _ ≤ L₁ * (cfg.γ * r) * 4 := by gcongr
      _ ≤ cfg.γ * (ε / 8) := by nlinarith [mul_le_mul_of_nonneg_left hc hγ.le]
  · have key := three_point_second hL₂ hd hl₂ x' (x' - x) (keep cfg) (weightNear cfg)
      (weightFar cfg) (-1) ((1 - cfg.γ) / cfg.γ) ((2 - cfg.γ) / cfg.γ) hi₁
    rw [e] at key
    change ‖drift cfg grad x x'‖ ≤ _ at key
    refine key.trans ?_
    have hco := coeff_second hγ hγ1
    change |keep cfg| * (-1 : ℝ) ^ 2 + |weightNear cfg| * ((1 - cfg.γ) / cfg.γ) ^ 2 +
      |weightFar cfg| * ((2 - cfg.γ) / cfg.γ) ^ 2 ≤ 5 / cfg.γ at hco
    have hsq : ‖x' - x‖ ^ 2 ≤ (cfg.γ * r) ^ 2 := pow_le_pow_left₀ hn hdr 2
    calc L₂ * ‖x' - x‖ ^ 2 * _ ≤ L₂ * (cfg.γ * r) ^ 2 * (5 / cfg.γ) := by gcongr
      _ = cfg.γ * (5 * L₂ * r ^ 2) := by field_simp
      _ ≤ cfg.γ * (ε / 8) := by
          apply mul_le_mul_of_nonneg_left _ hγ.le
          linarith
  · have key := three_point_third hL₃ hd hd₂ hl₃ x' (x' - x) (keep cfg) (weightNear cfg)
      (weightFar cfg) (-1) ((1 - cfg.γ) / cfg.γ) ((2 - cfg.γ) / cfg.γ) hi₁ hi₂
    rw [e] at key
    change ‖drift cfg grad x x'‖ ≤ _ at key
    refine key.trans ?_
    have hco := coeff_third hγ hγ1
    change |keep cfg| * |(-1 : ℝ)| ^ 3 + |weightNear cfg| * |(1 - cfg.γ) / cfg.γ| ^ 3 +
      |weightFar cfg| * |(2 - cfg.γ) / cfg.γ| ^ 3 ≤ 7 / cfg.γ ^ 2 at hco
    have hcu : ‖x' - x‖ ^ 3 ≤ (cfg.γ * r) ^ 3 := pow_le_pow_left₀ hn hdr 3
    calc L₃ * ‖x' - x‖ ^ 3 * _ ≤ L₃ * (cfg.γ * r) ^ 3 * (7 / cfg.γ ^ 2) := by gcongr
      _ = cfg.γ * (7 * L₃ * r ^ 3) := by field_simp
      _ ≤ cfg.γ * (ε / 8) := by
          apply mul_le_mul_of_nonneg_left _ hγ.le
          linarith

end Drift

lemma tuned_hyp (hL₁ : 0 < L₁) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    CfgHyp (tunedConfig L₁ L₂ L₃ σ Δ ε) L₁ σ Δ
      ((1 - keep (tunedConfig L₁ L₂ L₃ σ Δ ε)) * (ε / 8)) ε := by
  have hγ := tγ_pos (σ := σ) hε
  have hγ1 := tγ_le_one (σ := σ) hε
  have hη := tη_pos (L₂ := L₂) (L₃ := L₃) (σ := σ) hL₁ hε
  have hk := keep_bounds (cfg := tunedConfig L₁ L₂ L₃ σ Δ ε) hγ hγ1
  have hn0 : 1 ≤ ⌈1 / tγ σ ε⌉₊ := Nat.one_le_iff_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))
  refine ⟨hn0, hγ, hγ1, hη, hε, ?_, ?_, ?_, ?_, hΔ⟩
  · have h1 : (1 - keep (tunedConfig L₁ L₂ L₃ σ Δ ε)) ≠ 0 := by linarith [hk.2]
    rw [mul_div_cancel_left₀ _ h1]
    linarith
  · have h : tη L₁ L₂ L₃ σ ε ≤ ε / (2 * L₁) := min_le_right _ _
    calc L₁ / 2 * tη L₁ L₂ L₃ σ ε ≤ L₁ / 2 * (ε / (2 * L₁)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ε / 4 := by field_simp; ring
  · change 10 * (σ ^ 2 / (⌈1 / tγ σ ε⌉₊ : ℝ) + 5 * tγ σ ε * σ ^ 2) / ε ≤ ε / 5
    have hceil : 1 / tγ σ ε ≤ (⌈1 / tγ σ ε⌉₊ : ℝ) := Nat.le_ceil _
    have hpos : (0 : ℝ) < ⌈1 / tγ σ ε⌉₊ := by exact_mod_cast hn0
    have h1 : σ ^ 2 / (⌈1 / tγ σ ε⌉₊ : ℝ) ≤ tγ σ ε * σ ^ 2 := by
      rw [div_le_iff₀ hpos]
      have : 1 ≤ tγ σ ε * (⌈1 / tγ σ ε⌉₊ : ℝ) := by
        have := mul_le_mul_of_nonneg_left hceil hγ.le
        rwa [mul_one_div_cancel hγ.ne'] at this
      nlinarith [sq_nonneg σ]
    have h2 := tγ_noise (σ := σ) hε
    rw [div_le_iff₀ hε]
    nlinarith
  · change Δ / tη L₁ L₂ L₃ σ ε ≤ ((⌈5 * Δ / (tη L₁ L₂ L₃ σ ε * ε)⌉₊ : ℝ) + 1) * (ε / 5)
    have hceil : 5 * Δ / (tη L₁ L₂ L₃ σ ε * ε) ≤ (⌈5 * Δ / (tη L₁ L₂ L₃ σ ε * ε)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have e : Δ / tη L₁ L₂ L₃ σ ε = 5 * Δ / (tη L₁ L₂ L₃ σ ε * ε) * (ε / 5) := by field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith

lemma tuned_calls (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (tunedConfig L₁ L₂ L₃ σ Δ ε).n0 + 2 * (tunedConfig L₁ L₂ L₃ σ Δ ε).T ≤
      ⌈100000 * (1 + σ ^ 2 / ε ^ 2 + L₁ * Δ / ε ^ 2 +
        Δ * σ ^ 2 / ε ^ 3 * complexity L₁ L₂ L₃ ε)⌉₊ := by
  have hγ := tγ_pos (σ := σ) hε
  have hη := tη_pos (L₂ := L₂) (L₃ := L₃) (σ := σ) hL₁ hε
  have hr := tr_pos (L₂ := L₂) (L₃ := L₃) hL₁ hε
  obtain ⟨hM0, hM1⟩ := complexity_le (L₂ := L₂) hL₁ hL₃ hε
  set M := complexity L₁ L₂ L₃ ε
  have hinvr := inv_tr_le hL₁ hL₂ hL₃ hε
  have hn : ((tunedConfig L₁ L₂ L₃ σ Δ ε).n0 : ℝ) ≤ 1 / tγ σ ε + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hT : ((tunedConfig L₁ L₂ L₃ σ Δ ε).T : ℝ) ≤ 5 * Δ / (tη L₁ L₂ L₃ σ ε * ε) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hinvη : 1 / tη L₁ L₂ L₃ σ ε ≤ 32 * M * (1 / tγ σ ε) + 2 * L₁ / ε := by
    unfold tη
    rcases min_choice (tγ σ ε * tr L₁ L₂ L₃ ε) (ε / (2 * L₁)) with h | h
    · rw [h]
      have e : 1 / (tγ σ ε * tr L₁ L₂ L₃ ε) = 1 / tr L₁ L₂ L₃ ε * (1 / tγ σ ε) := by field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_right hinvr (by positivity : (0 : ℝ) ≤ 1 / tγ σ ε)
      have h2 : 0 ≤ 2 * L₁ / ε := by positivity
      linarith
    · rw [h]
      have e : 1 / (ε / (2 * L₁)) = 2 * L₁ / ε := by field_simp
      rw [e]
      have : 0 ≤ 32 * M * (1 / tγ σ ε) := by positivity
      linarith
  have hmain : 5 * Δ / (tη L₁ L₂ L₃ σ ε * ε) ≤
      5 * Δ / ε * (32 * M * (1 + 300 * σ ^ 2 / ε ^ 2) + 2 * L₁ / ε) := by
    have e : 5 * Δ / (tη L₁ L₂ L₃ σ ε * ε) = 5 * Δ / ε * (1 / tη L₁ L₂ L₃ σ ε) := by field_simp
    rw [e, ← tγ_inv (σ := σ) hε]
    exact mul_le_mul_of_nonneg_left hinvη (by positivity)
  have hreal : (((tunedConfig L₁ L₂ L₃ σ Δ ε).n0 + 2 * (tunedConfig L₁ L₂ L₃ σ Δ ε).T : ℕ) : ℝ) ≤
      100000 * (1 + σ ^ 2 / ε ^ 2 + L₁ * Δ / ε ^ 2 + Δ * σ ^ 2 / ε ^ 3 * M) := by
    push_cast
    rw [tγ_inv hε] at hn
    have hs : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
    have hLΔ : 0 ≤ L₁ * Δ / ε ^ 2 := by positivity
    have hlast : 0 ≤ Δ * σ ^ 2 / ε ^ 3 * M := by positivity
    have e1 : 5 * Δ / ε * (32 * M * (1 + 300 * σ ^ 2 / ε ^ 2) + 2 * L₁ / ε) =
        160 * (Δ / ε * M) + 48000 * (Δ * σ ^ 2 / ε ^ 3 * M) + 10 * (L₁ * Δ / ε ^ 2) := by
      field_simp; ring
    have e2 : Δ / ε * M ≤ L₁ * Δ / ε ^ 2 := by
      have := mul_le_mul_of_nonneg_left hM1 (by positivity : (0 : ℝ) ≤ Δ / ε)
      calc Δ / ε * M ≤ Δ / ε * (L₁ / ε) := this
        _ = L₁ * Δ / ε ^ 2 := by field_simp
    have e3 : 300 * σ ^ 2 / ε ^ 2 = 300 * (σ ^ 2 / ε ^ 2) := by ring
    rw [e1] at hmain
    rw [e3] at hn
    linarith
  exact Nat.cast_le.mp (hreal.trans (Nat.le_ceil _))

end OracleTemplate.LookaheadMomentum
