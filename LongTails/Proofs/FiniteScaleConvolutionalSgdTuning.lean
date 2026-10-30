import LongTails.Proofs.FiniteScaleConvolutionalSgdStopping
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdTuning

lemma initial_scale_bounds (P η ε V : ℝ) (hP : 1 ≤ P) (hη : 0 < η)
    (hε : 0 < ε) (hε₁ : ε ^ 2 ≤ 1) (hV : 0 ≤ V) :
    let scale := Real.sqrt (P * (η + V ^ 2) / ε ^ 2)
    0 < scale ∧ V ≤ scale ∧ V ≤ scale * ε ∧ η / scale ^ 2 ≤ ε ^ 2 / P := by
  let scale := Real.sqrt (P * (η + V ^ 2) / ε ^ 2)
  have hPpos : 0 < P := by linarith
  have hε₂ : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hs : scale ^ 2 = P * (η + V ^ 2) / ε ^ 2 := Real.sq_sqrt (by positivity)
  have he : scale ^ 2 * ε ^ 2 = P * (η + V ^ 2) := (eq_div_iff hε₂.ne').mp hs
  have hPV := mul_le_mul_of_nonneg_right hP (sq_nonneg V)
  have hPη : 0 ≤ P * η := by positivity
  have hbase : V ^ 2 ≤ scale ^ 2 * ε ^ 2 := by nlinarith
  have hεs := mul_le_mul_of_nonneg_left hε₁ (sq_nonneg scale)
  have hVscale : V ≤ scale := by nlinarith
  have hVε : V ≤ scale * ε := by nlinarith [mul_pos hscale hε]
  have hthermal : η / scale ^ 2 ≤ ε ^ 2 / P := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hscale) hPpos).2
    nlinarith [mul_nonneg hPpos.le (sq_nonneg V)]
  exact ⟨hscale, hVscale, hVε, hthermal⟩

lemma logarithm_lower (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    1 ≤ Real.log (24 / δ) := by
  apply (Real.le_log_iff_exp_le (show 0 < 24 / δ by positivity)).2
  have hh : 24 ≤ 24 / δ := (le_div_iff₀ hδ).2 (by nlinarith)
  linarith [Real.exp_one_lt_three]

lemma burn_ceiling_bounds (N ρ L : ℝ) (hN : 1 ≤ N) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hL : 1 ≤ L) :
    48 * N / ρ ^ 2 * L ≤ (⌈48 * N / ρ ^ 2 * L⌉₊ : ℝ) ∧
      (⌈48 * N / ρ ^ 2 * L⌉₊ : ℝ) ≤ 49 * N / ρ ^ 2 * L ∧
      4 * (⌈48 * N / ρ ^ 2 * L⌉₊ : ℝ) + 1 ≤ 197 * N / ρ ^ 2 * L := by
  have hρ₂ : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
  have hNL : 1 ≤ N * L := by nlinarith
  have hX : 1 ≤ N / ρ ^ 2 * L := by
    calc
      _ ≤ N * L / ρ ^ 2 := (le_div_iff₀ hρ₂).2 (by nlinarith)
      _ = _ := by ring
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 48 * N / ρ ^ 2 * L by positivity)
  refine ⟨Nat.le_ceil _, ?_, ?_⟩
  all_goals
    ring_nf at hX hceil ⊢
    linarith

lemma early_radius_lower (T₀ : ℕ) : (1 : ℝ) ≤ 4 * (T₀ : ℝ) + 1 := by
  have hh : (0 : ℝ) ≤ T₀ := Nat.cast_nonneg _
  linarith

lemma radius_bounds (N ρ κ L δ H₀ : ℝ) (hN : 1 ≤ N) (hρ : 0 < ρ)
    (hρκ : ρ ≤ κ / 1000) (hκ₁ : κ ≤ 1 / 4)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hH₀ : 1 ≤ H₀)
    (hH₀upper : H₀ ≤ 197 * N / ρ ^ 2 * L) :
    let H := 10000 * N / ρ ^ 2 * L
    let F := 1000 * N * δ * H₀ / ρ ^ 2
    H₀ ≤ H / 10 ∧ 1000 ≤ κ * H ∧ δ ≤ F ∧ 2 * F ≤ δ * H ^ 2 / 100 := by
  dsimp
  have hρ₂ : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hρ₁ : ρ ≤ 1 := by linarith
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
  have hX : 1 ≤ N / ρ ^ 2 * L := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hρ₂).2 (by nlinarith)
  have hNL : N ≤ N * L := by nlinarith
  have hXNL : N / ρ ^ 2 ≤ N / ρ ^ 2 * L := by
    exact le_mul_of_one_le_right (by positivity) hL
  have hκρ : ρ ^ 2 ≤ κ := by nlinarith
  have hκX : 1 ≤ κ * (N / ρ ^ 2 * L) := by
    rw [div_mul_eq_mul_div, ← mul_div_assoc]
    apply (le_div_iff₀ hρ₂).2
    nlinarith
  have hδF : δ ≤ 1000 * N * δ * H₀ / ρ ^ 2 := by
    apply (le_div_iff₀ hρ₂).2
    have hNH : 1 ≤ N * H₀ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hρsq hδ.le,
      mul_le_mul_of_nonneg_left hNH hδ.le]
  have hFupper : 1000 * N * δ * H₀ / ρ ^ 2 ≤
      197000 * δ * (N / ρ ^ 2 * L) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hH₀upper
      (show 0 ≤ 1000 * δ * (N / ρ ^ 2) by positivity)
    have hh₂ := mul_le_mul_of_nonneg_left hXNL
      (show 0 ≤ 197000 * δ * (N / ρ ^ 2 * L) by positivity)
    ring_nf at hh hh₂ ⊢
    linarith
  refine ⟨?_, ?_, hδF, ?_⟩
  · ring_nf at hX hH₀upper ⊢
    linarith
  · ring_nf at hκX ⊢
    linarith
  · have hn : 0 ≤ δ * (N / ρ ^ 2 * L) ^ 2 := by positivity
    ring_nf at hFupper hn ⊢
    linarith

lemma total_time_bounds (N κ X : ℝ) (T₀ : ℕ) (hN : 1 ≤ N) (hκ : 0 < κ)
    (hκ₁ : κ ≤ 1 / 4) (hX : 1 ≤ X) (hT₀ : (T₀ : ℝ) ≤ 49 * X) :
    let T₁ := ⌈96 * N * (10000 * X) / κ⌉₊
    T₀ < T₀ + T₁ ∧ (T₀ + T₁ : ℕ) ≤ 1000000 * N * X / κ ∧
      2 * N * (6 * (10000 * X) / κ) / (T₀ + T₁ - T₀ : ℕ) ≤ 1 / 8 := by
  dsimp
  have harg : 0 < 96 * N * (10000 * X) / κ := by positivity
  have hl := Nat.le_ceil (96 * N * (10000 * X) / κ)
  have hu := Nat.ceil_lt_add_one harg.le
  have hpos : 0 < ⌈96 * N * (10000 * X) / κ⌉₊ := Nat.ceil_pos.mpr harg
  refine ⟨Nat.lt_add_of_pos_right hpos, ?_, ?_⟩
  · push_cast
    have hdom : X ≤ N * X / κ := by
      apply (le_div_iff₀ hκ).2
      nlinarith
    ring_nf at hu hdom ⊢
    linarith
  · rw [Nat.add_sub_cancel_left]
    apply (div_le_iff₀ (show (0 : ℝ) < ⌈96 * N * (10000 * X) / κ⌉₊ by exact_mod_cast hpos)).2
    ring_nf at hl ⊢
    linarith

lemma scaled_contrast_bound (N ρ κ L δ : ℝ) (hN : 0 < N) (hρ : 0 < ρ)
    (hκ : 0 < κ)
    (hsmall : δ * L ^ 2 ≤ κ ^ 3 * ρ ^ 4 / (10000000000000000000000 * N ^ 3)) :
    δ * (N / ρ ^ 2 * L) ^ 2 * N / κ ≤ κ ^ 2 / 10000000000000000000000 := by
  have hh := (le_div_iff₀ (show 0 < 10000000000000000000000 * N ^ 3 by positivity)).1 hsmall
  rw [show δ * (N / ρ ^ 2 * L) ^ 2 * N / κ = δ * L ^ 2 * N ^ 3 / (ρ ^ 4 * κ) by
    field_simp]
  apply (div_le_iff₀ (show 0 < ρ ^ 4 * κ by positivity)).2
  nlinarith only [hh]

lemma total_perturbation_bound (N ρ κ L δ T : ℝ) (hN : 0 < N) (hρ : 0 < ρ)
    (hκ : 0 < κ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hsmall : δ * L ^ 2 ≤ κ ^ 3 * ρ ^ 4 / (10000000000000000000000 * N ^ 3))
    (hT : T ≤ 1000000 * N * (N / ρ ^ 2 * L) / κ) :
    δ * (10000 * N / ρ ^ 2 * L) * T ≤ κ ^ 2 / 1000000000000 := by
  have hh := mul_le_mul_of_nonneg_left hT
    (show 0 ≤ δ * (10000 * N / ρ ^ 2 * L) by positivity)
  have hs := scaled_contrast_bound N ρ κ L δ hN hρ hκ hsmall
  ring_nf at hh hs ⊢
  linarith

lemma floor_le_perturbation (N ρ L δ H₀ T : ℝ) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hH₀ : H₀ ≤ 197 * N / ρ ^ 2 * L)
    (hT : 48 * N / ρ ^ 2 * L ≤ T) :
    1000 * N * δ * H₀ / ρ ^ 2 ≤ δ * (10000 * N / ρ ^ 2 * L) * T := by
  have hX : 0 ≤ N / ρ ^ 2 * L := by positivity
  have hNX : N / ρ ^ 2 ≤ N / ρ ^ 2 * L := le_mul_of_one_le_right (by positivity) hL
  have h₁ := mul_le_mul_of_nonneg_left hH₀ (show 0 ≤ 1000 * N * δ / ρ ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hNX (show 0 ≤ 197000 * δ * (N / ρ ^ 2 * L) by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hT (show 0 ≤ δ * (10000 * N / ρ ^ 2 * L) by positivity)
  have hn : 0 ≤ δ * (N / ρ ^ 2 * L) ^ 2 := by positivity
  ring_nf at h₁ h₂ h₃ hn ⊢
  linarith

lemma smallness_bounds (δ κ H H₀ F T T₀ : ℝ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hκ₁ : κ ≤ 1 / 4) (hH₀ : 0 ≤ H₀) (hH₀H : H₀ ≤ H) (hT₀ : 0 ≤ T₀)
    (hT₀T : T₀ ≤ T) (hT : 1 ≤ T) (hF : F ≤ δ * H * T)
    (hsmall : δ * H * T ≤ κ ^ 2 / 1000000000000) :
    δ * H₀ * T₀ ≤ 1 / 100 ∧ δ * H₀ ≤ 1 ∧ F ≤ (κ / 1000) ^ 2 / 4 ∧
      30 * δ * H * T ≤ (κ / 1000) ^ 2 / 4 ∧ δ * H * T ≤ 1 / 4 ∧
      δ * H ≤ κ / 1000 := by
  have hH : 0 ≤ H := hH₀.trans hH₀H
  have hd : 0 ≤ δ * H := mul_nonneg hδ hH
  have hdT : δ * H ≤ δ * H * T := le_mul_of_one_le_right hd hT
  have hd₀ : δ * H₀ ≤ δ * H := mul_le_mul_of_nonneg_left hH₀H hδ
  have he : δ * H₀ * T₀ ≤ δ * H * T :=
    mul_le_mul hd₀ hT₀T hT₀ hd
  have hk : κ ^ 2 ≤ κ / 4 := by nlinarith
  constructor
  · nlinarith only [he, hsmall, hk, hκ₁]
  constructor
  · nlinarith only [hd₀, hdT, hsmall, hk, hκ₁]
  constructor
  · nlinarith only [hF, hsmall, sq_nonneg κ]
  constructor
  · nlinarith only [hsmall, sq_nonneg κ]
  constructor
  · nlinarith only [hsmall, hk, hκ₁]
  · nlinarith only [hdT, hsmall, hk, hκ]

lemma burn_decay (N ρ δ F : ℝ) (T₀ : ℕ) (hN : 1 ≤ N) (hρ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hF : δ ≤ F)
    (hT₀ : 48 * N / ρ ^ 2 * Real.log (24 / δ) ≤ (T₀ : ℝ)) :
    (1 - ρ ^ 2 / (24 * N)) ^ T₀ * 3 / F ≤ 1 / 8 := by
  have hNpos : 0 < N := by linarith
  have hFpos : 0 < F := hδ.trans_le hF
  have hρ₂ : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have ha : 0 ≤ 1 - ρ ^ 2 / (24 * N) := by
    have hh : ρ ^ 2 / (24 * N) ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
    linarith
  have hp := pow_le_pow_left₀ ha (Real.one_sub_le_exp_neg (ρ ^ 2 / (24 * N))) T₀
  rw [← Real.exp_nat_mul] at hp
  have hL := logarithm_lower δ hδ hδ₁
  have htime : Real.log (24 / δ) ≤ (T₀ : ℝ) * (ρ ^ 2 / (24 * N)) := by
    have hh := mul_le_mul_of_nonneg_right hT₀ (show 0 ≤ ρ ^ 2 / (24 * N) by positivity)
    have he : (48 * N / ρ ^ 2 * Real.log (24 / δ)) * (ρ ^ 2 / (24 * N)) =
        2 * Real.log (24 / δ) := by field_simp; ring
    rw [he] at hh
    linarith
  have he : Real.exp ((T₀ : ℝ) * -(ρ ^ 2 / (24 * N))) ≤ δ / 24 := by
    calc
      _ ≤ Real.exp (-Real.log (24 / δ)) := Real.exp_le_exp.mpr (by nlinarith only [htime])
      _ = δ / 24 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  apply (div_le_iff₀ hFpos).2
  linarith [hp.trans he]

lemma thermal_bounds (δ H₀ H : ℝ) (T : ℕ) (hδ : 0 ≤ δ) (hH₀ : 1 ≤ H₀)
    (hH₀H : H₀ ≤ H) :
    0 ≤ δ / (T + 1) ∧ δ / (T + 1) ≤ δ * H₀ ∧ δ / (T + 1) ≤ δ * H ∧
      (T : ℝ) * (δ / (T + 1)) ≤ δ := by
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hden : (0 : ℝ) < T + 1 := by positivity
  have hz : δ / (T + 1) ≤ δ := (div_le_iff₀ hden).2 (by nlinarith)
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hH₀ hδ]
  · nlinarith [mul_le_mul_of_nonneg_left (hH₀.trans hH₀H) hδ]
  · rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).2 (by nlinarith)

lemma tuning_conditions (N ρ κ δ : ℝ) (hN : 1 ≤ N) (hρ : 0 < ρ)
    (hρκ : ρ ≤ κ / 1000) (hκ : 0 < κ) (hκ₁ : κ ≤ 1 / 4)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hsmall : δ * (Real.log (24 / δ)) ^ 2 ≤
      κ ^ 3 * ρ ^ 4 / (10000000000000000000000 * N ^ 3)) :
    let L := Real.log (24 / δ)
    let T₀ := ⌈48 * N / ρ ^ 2 * L⌉₊
    let H₀ := 4 * (T₀ : ℝ) + 1
    let H := 10000 * N / ρ ^ 2 * L
    let F := 1000 * N * δ * H₀ / ρ ^ 2
    let T := T₀ + ⌈96 * N * H / κ⌉₊
    let ζ := δ / ((T : ℝ) + 1)
    T₀ < T ∧ 0 < F ∧ δ * H₀ * (T₀ : ℝ) ≤ 1 / 100 ∧
      δ * H₀ ≤ 1 ∧ ζ ≤ δ * H₀ ∧ 1000 * N * (δ * H₀) ≤ ρ ^ 2 * F ∧
      H₀ ≤ H / 10 ∧ 1000 ≤ κ * H ∧ F ≤ (κ / 1000) ^ 2 / 4 ∧
      2 * F ≤ δ * H ^ 2 / 100 ∧ 30 * δ * H * (T : ℝ) ≤ (κ / 1000) ^ 2 / 4 ∧
      δ * H * (T : ℝ) ≤ 1 / 4 ∧ δ * H ≤ κ / 1000 ∧
      0 ≤ ζ ∧ ζ ≤ δ * H ∧ (T : ℝ) * ζ ≤ δ ∧
      (1 - ρ ^ 2 / (24 * N)) ^ T₀ * 3 / F ≤ 1 / 8 ∧
      2 * N * (6 * H / κ) / (T - T₀ : ℕ) ≤ 1 / 8 ∧
      (T : ℝ) ≤ 1000000 * N * (N / ρ ^ 2 * L) / κ := by
  dsimp only
  let L := Real.log (24 / δ)
  let X := N / ρ ^ 2 * L
  let T₀ := ⌈48 * N / ρ ^ 2 * L⌉₊
  let H₀ := 4 * (T₀ : ℝ) + 1
  let H := 10000 * N / ρ ^ 2 * L
  let F := 1000 * N * δ * H₀ / ρ ^ 2
  let T := T₀ + ⌈96 * N * H / κ⌉₊
  let ζ := δ / ((T : ℝ) + 1)
  change T₀ < T ∧ 0 < F ∧ δ * H₀ * (T₀ : ℝ) ≤ 1 / 100 ∧
    δ * H₀ ≤ 1 ∧ ζ ≤ δ * H₀ ∧ 1000 * N * (δ * H₀) ≤ ρ ^ 2 * F ∧
    H₀ ≤ H / 10 ∧ 1000 ≤ κ * H ∧ F ≤ (κ / 1000) ^ 2 / 4 ∧
    2 * F ≤ δ * H ^ 2 / 100 ∧ 30 * δ * H * (T : ℝ) ≤ (κ / 1000) ^ 2 / 4 ∧
    δ * H * (T : ℝ) ≤ 1 / 4 ∧ δ * H ≤ κ / 1000 ∧
    0 ≤ ζ ∧ ζ ≤ δ * H ∧ (T : ℝ) * ζ ≤ δ ∧
    (1 - ρ ^ 2 / (24 * N)) ^ T₀ * 3 / F ≤ 1 / 8 ∧
    2 * N * (6 * H / κ) / (T - T₀ : ℕ) ≤ 1 / 8 ∧
    (T : ℝ) ≤ 1000000 * N * X / κ
  have hNpos : 0 < N := by linarith
  have hρ₁ : ρ ≤ 1 := by linarith
  have hL : 1 ≤ L := logarithm_lower δ hδ hδ₁
  have hX : 1 ≤ X := by
    dsimp [X]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).2
    nlinarith
  have hHdef : H = 10000 * X := by dsimp [H, X]; ring
  obtain ⟨hT₀lo, hT₀hi, hH₀hi⟩ := burn_ceiling_bounds N ρ L hN hρ hρ₁ hL
  change 48 * N / ρ ^ 2 * L ≤ (T₀ : ℝ) at hT₀lo
  change (T₀ : ℝ) ≤ 49 * N / ρ ^ 2 * L at hT₀hi
  change H₀ ≤ 197 * N / ρ ^ 2 * L at hH₀hi
  have hH₀lo : 1 ≤ H₀ := early_radius_lower T₀
  obtain ⟨hH₀H, hκH, hδF, hFscale⟩ :=
    radius_bounds N ρ κ L δ H₀ hN hρ hρκ hκ₁ hL hδ hH₀lo hH₀hi
  change H₀ ≤ H / 10 at hH₀H
  change 1000 ≤ κ * H at hκH
  change δ ≤ F at hδF
  change 2 * F ≤ δ * H ^ 2 / 100 at hFscale
  have ht₀ : (T₀ : ℝ) ≤ 49 * X := by
    dsimp [X]
    convert hT₀hi using 1
    ring
  have htimes := total_time_bounds N κ X T₀ hN hκ hκ₁ hX ht₀
  rw [← hHdef] at htimes
  change T₀ < T ∧ (T : ℝ) ≤ 1000000 * N * X / κ ∧
    2 * N * (6 * H / κ) / (T - T₀ : ℕ) ≤ 1 / 8 at htimes
  obtain ⟨hTlt, hTupper, hbudget⟩ := htimes
  have hT₀T : (T₀ : ℝ) ≤ T := by exact_mod_cast hTlt.le
  have hTlo : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le T₀) hTlt))
  have hpert := total_perturbation_bound N ρ κ L δ T hNpos hρ hκ (by linarith) hδ.le hsmall hTupper
  change δ * H * (T : ℝ) ≤ κ ^ 2 / 1000000000000 at hpert
  have hFpert : F ≤ δ * H * (T : ℝ) := floor_le_perturbation N ρ L δ H₀ T hNpos.le
    hρ hL hδ.le hH₀hi (hT₀lo.trans hT₀T)
  have hH₀H' : H₀ ≤ H := by linarith
  obtain ⟨hearly, hdH₀, hFsmall, hmean, htime, hdH⟩ := smallness_bounds δ κ H H₀ F T T₀
    hδ.le hκ hκ₁ (by linarith) hH₀H' (Nat.cast_nonneg _) hT₀T hTlo hFpert hpert
  obtain ⟨hζ, hζ₀, hζH, hthermal⟩ := thermal_bounds δ H₀ H T hδ.le hH₀lo hH₀H'
  have hfloor : 1000 * N * (δ * H₀) ≤ ρ ^ 2 * F := by
    dsimp [F]
    field_simp
    norm_num
  have hdecay := burn_decay N ρ δ F T₀ hN hρ hρ₁ hδ hδ₁ hδF hT₀lo
  exact ⟨hTlt, hδ.trans_le hδF, hearly, hdH₀, hζ₀, hfloor, hH₀H, hκH,
    hFsmall, hFscale, hmean, htime, hdH, hζ, hζH, hthermal, hdecay, hbudget, hTupper⟩

open LongTails.Setups.FiniteScaleConvolutionalSgd
open LongTails.Algorithms.FiniteScaleConvolutionalSgd
open FiniteScaleConvolutionalSgdGeometry

lemma parameter_bounds (p : Params) (hp : spec.valid p) :
    0 < stepSize p.input ∧ 0 < stepSize p.input * p.input.contrast ∧
      0 < backgroundStep p.input ∧ backgroundStep p.input ≤ p.input.derivativeMargin / 1000 := by
  rcases hp with ⟨_, hg, hgR, hμ, hκ, _, _, _, _, _, _, _, _, _⟩
  have hR : 0 < p.input.upper := hg.trans_le hgR
  have hη : 0 < stepSize p.input := by unfold stepSize; positivity
  refine ⟨hη, mul_pos hη hμ, mul_pos hη hg, ?_⟩
  unfold backgroundStep stepSize
  have hh := mul_le_mul_of_nonneg_left hgR hη.le
  have he : p.input.derivativeMargin / (1000 * p.input.upper) * p.input.upper =
      p.input.derivativeMargin / 1000 := by field_simp
  exact hh.trans_eq he

lemma initial_conditions (p : Params) (hp : spec.valid p) :
    let q := p.input
    let η := stepSize q
    let ε := η * q.contrast
    let s := LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale q
    let K := s ^ 2 / η
    0 < s ∧ 0 < K ∧ 1 / K ≤ perturbation q / ((runSteps q : ℝ) + 1) ∧
      FiniteScaleConvolutionalSgdDynamics.meanPotential (initialState q s ε) ≤ 3 ∧
      ‖(initialState q s ε).z‖ ≤ 1 := by
  obtain ⟨hη, hε, _, _⟩ := parameter_bounds p hp
  rcases hp with ⟨hd, _, _, _, _, _, ha, _, _, hδ₁, _, _, _, _⟩
  have hP : (1 : ℝ) ≤ (period p.input : ℝ) := by
    change (1 : ℝ) ≤ (runSteps p.input + 1 : ℕ)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hs := initial_scale_bounds (period p.input : ℝ) (stepSize p.input)
    (stepSize p.input * p.input.contrast) ‖p.input.initialReadout‖ hP hη hε hδ₁ (norm_nonneg _)
  change 0 < LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale p.input ∧
    ‖p.input.initialReadout‖ ≤ LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale p.input ∧
    ‖p.input.initialReadout‖ ≤ LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale p.input *
      (stepSize p.input * p.input.contrast) ∧
    stepSize p.input / LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale p.input ^ 2 ≤
      perturbation p.input / (period p.input : ℝ) at hs
  dsimp only
  obtain ⟨hq, hz⟩ := initialState_readout_bounds p.input _ _ hd hs.1 hε hs.2.1 hs.2.2.1
  refine ⟨hs.1, div_pos (sq_pos_of_pos hs.1) hη, ?_,
    FiniteScaleConvolutionalSgdDynamics.mean_potential_box_bound _ ha hq, hz⟩
  simpa only [one_div_div, one_mul, period, PNat.mk_coe, Nat.cast_add, Nat.cast_one] using hs.2.2.2

open MeasureTheory
open FiniteScaleConvolutionalSgdProcess
open FiniteScaleConvolutionalSgdStopping
open ManySampleConvolutionalPerceptronGeometry (plusFeature minusFeature)

lemma normalized_failure (p : Params) (hp : spec.valid p) (data : Data p.input)
    (G : Geometry p.input data)
    (ξ : ℕ → p.input.sampling.Ω → Fin p.input.count)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype (Fin p.input.count)).toMeasure p.input.sampling.law) :
    let q := p.input
    let η := stepSize q
    let s := LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale q
    (q.sampling.law : Measure q.sampling.Ω) {ω | NoSeparation (s ^ 2 / η) (perturbation q)
      (fun i => η * G.background i) (fun i => plusFeature (G.defect i))
      (fun i => minusFeature (G.defect i)) (initialState q s (η * q.contrast))
      (fun j => ξ j ω) (runSteps q)} ≤ ENNReal.ofReal (1 / 4) := by
  obtain ⟨hη, hε, hρ, hρκ⟩ := parameter_bounds p hp
  obtain ⟨_, hK, hKζ, hW, hz⟩ := initial_conditions p hp
  rcases hp with ⟨_, hg, hgR, _, hκ, hκ₁, _, htlo, hthi, hδ₁, hsmall, _, _, _⟩
  let q := p.input
  let η := stepSize q
  let δ := perturbation q
  let ρ := backgroundStep q
  let κ := q.derivativeMargin
  let H₀ := 4 * (burnSteps q : ℝ) + 1
  let F := 1000 * (q.count : ℝ) * δ * H₀ / ρ ^ 2
  let ζ := δ / ((runSteps q : ℝ) + 1)
  have hδ : 0 < δ := by
    dsimp [δ, perturbation]
    exact sq_pos_of_pos hε
  have hN : (1 : ℝ) ≤ (q.count : ℝ) := by exact_mod_cast q.count.pos
  norm_num at hsmall
  have hc := tuning_conditions (q.count : ℝ) ρ κ δ hN hρ hρκ hκ hκ₁ hδ hδ₁ hsmall
  change burnSteps q < runSteps q ∧ 0 < F ∧ δ * H₀ * (burnSteps q : ℝ) ≤ 1 / 100 ∧
    δ * H₀ ≤ 1 ∧ ζ ≤ δ * H₀ ∧ 1000 * (q.count : ℝ) * (δ * H₀) ≤ ρ ^ 2 * F ∧
    H₀ ≤ radius q / 10 ∧ 1000 ≤ κ * radius q ∧ F ≤ (κ / 1000) ^ 2 / 4 ∧
    2 * F ≤ δ * radius q ^ 2 / 100 ∧
    30 * δ * radius q * (runSteps q : ℝ) ≤ (κ / 1000) ^ 2 / 4 ∧
    δ * radius q * (runSteps q : ℝ) ≤ 1 / 4 ∧ δ * radius q ≤ κ / 1000 ∧
    0 ≤ ζ ∧ ζ ≤ δ * radius q ∧ (runSteps q : ℝ) * ζ ≤ δ ∧
    (1 - ρ ^ 2 / (24 * (q.count : ℝ))) ^ burnSteps q * 3 / F ≤ 1 / 8 ∧
    2 * (q.count : ℝ) * (6 * radius q / κ) / (runSteps q - burnSteps q : ℕ) ≤ 1 / 8 ∧
    (runSteps q : ℝ) ≤ 1000000 * (q.count : ℝ) *
      ((q.count : ℝ) / ρ ^ 2 * Real.log (24 / δ)) / κ at hc
  obtain ⟨hT, hF, hearly, hdH₀, hζ₀, hfloor, hH₀H, hH, hFsmall, hFscale,
    hmean, htime, hdH, hζ, hζH, hthermal, hdecay, hbudget, _⟩ := hc
  have hlo (i : Fin q.count) : ρ ≤ |η * G.background i| := by
    rw [abs_mul, abs_of_pos hη]
    exact mul_le_mul_of_nonneg_left (G.background_lower i) hη.le
  have hhi (i : Fin q.count) : |η * G.background i| ≤ κ / 1000 := by
    rw [abs_mul, abs_of_pos hη]
    have hh := mul_le_mul_of_nonneg_left (G.background_upper i) hη.le
    have he : η * q.upper = κ / 1000 := by
      dsimp [η, stepSize, κ]
      have hR : q.upper ≠ 0 := (hg.trans_le hgR).ne'
      field_simp
    exact hh.trans_eq he
  have hp' (i : Fin q.count) : ‖plusFeature (G.defect i)‖ ≤ 1 :=
    (feature_norm_bounds _ (G.defect_norm i)).1
  have hr' (i : Fin q.count) : ‖minusFeature (G.defect i)‖ ≤ 1 :=
    (feature_norm_bounds _ (G.defect_norm i)).2
  have hrun := one_run_failure q.sampling.law ξ hξ
    (LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale q ^ 2 / η)
    δ κ (κ / 1000) (κ / 1000) (radius q) H₀ F ρ ζ
    (fun i => η * G.background i) (fun i => plusFeature (G.defect i))
    (fun i => minusFeature (G.defect i))
    (initialState q (LongTails.Algorithms.FiniteScaleConvolutionalSgd.scale q) (η * q.contrast))
    G.separator (burnSteps q) (runSteps q) hT hK hKζ hδ hκ hκ₁ hρ.le hF
    (by positivity) le_rfl (by positivity) le_rfl rfl hearly hdH₀ hζ₀
    (by simpa using hfloor) hH₀H hH hFsmall hFscale hmean htime hdH hζ hζH hthermal
    hW hz ⟨htlo, hthi⟩ G.separator_unit.le hlo hhi hp' hr' G.derivative_margin
    (by simpa using hdecay) (by simpa using hbudget)
  exact hrun

lemma confidence_repetitions (p : ℝ) (hp : 0 < p) (hp₁ : p < 1) :
    let M := ⌈Real.log (1 / p)⌉₊ + 1
    (1 / 4 : ℝ) ^ M ≤ p ∧ (M : ℝ) ≤ 2 * (1 + Real.log (1 / p)) := by
  have hlog : 0 ≤ Real.log (1 / p) := Real.log_nonneg ((le_div_iff₀ hp).2 (by linarith))
  have hceil := Nat.le_ceil (Real.log (1 / p))
  have hceil₁ := Nat.ceil_lt_add_one hlog
  have hbase : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have hh : (1 / 4 : ℝ) ≤ 1 / Real.exp 1 := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (Real.exp_pos _)).2
      linarith [Real.exp_one_lt_three]
    simpa only [one_div] using hh
  constructor
  · have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hbase (⌈Real.log (1 / p)⌉₊ + 1)
    rw [← Real.exp_nat_mul] at hh
    calc
      _ ≤ Real.exp (((⌈Real.log (1 / p)⌉₊ + 1 : ℕ) : ℝ) * -1) := hh
      _ ≤ Real.exp (-Real.log (1 / p)) := Real.exp_le_exp.mpr (by push_cast; linarith)
      _ = p := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  · push_cast
    linarith

lemma cycle_cost_bound (N T M : ℕ) (κ X C : ℝ) (hN : 1 ≤ N) (hκ : 0 < κ)
    (hκ₁ : κ ≤ 1 / 4) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hT : (T : ℝ) ≤ 1000000 * N * X / κ) (hM : (M : ℝ) ≤ 2 * C) :
    (((T + 1) * (N + 1) * M : ℕ) : ℝ) ≤ 100000000 * (N : ℝ) ^ 2 * X / κ * C := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase : 1 ≤ (N : ℝ) * X / κ := (le_div_iff₀ hκ).2 (by nlinarith)
  have hperiod : ((T + 1 : ℕ) : ℝ) ≤ 1000001 * N * X / κ := by
    push_cast
    ring_nf at hT hbase ⊢
    linarith
  have hcount : ((N + 1 : ℕ) : ℝ) ≤ 2 * N := by push_cast; linarith
  have hh := mul_le_mul
    (mul_le_mul hperiod hcount (Nat.cast_nonneg _) (by positivity)) hM
    (Nat.cast_nonneg _) (by positivity)
  have hn : 0 ≤ (N : ℝ) ^ 2 * X / κ * C := by positivity
  push_cast at hh ⊢
  ring_nf at hh hn ⊢
  linarith

lemma run_time_bound (p : Params) (hp : spec.valid p) :
    (runSteps p.input : ℝ) ≤ 1000000 * (p.input.count : ℝ) *
      ((p.input.count : ℝ) / backgroundStep p.input ^ 2 * Real.log (24 / perturbation p.input)) /
        p.input.derivativeMargin := by
  obtain ⟨_, hε, hρ, hρκ⟩ := parameter_bounds p hp
  rcases hp with ⟨_, _, _, _, hκ, hκ₁, _, _, _, hδ₁, hsmall, _, _, _⟩
  norm_num at hsmall
  have hδ : 0 < perturbation p.input := sq_pos_of_pos hε
  have hN : (1 : ℝ) ≤ (p.input.count : ℝ) := by exact_mod_cast p.input.count.pos
  have hc := tuning_conditions (p.input.count : ℝ) (backgroundStep p.input)
    p.input.derivativeMargin (perturbation p.input) hN hρ hρκ hκ hκ₁ hδ hδ₁ hsmall
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT⟩
  exact hT

lemma total_budget_bound (p : Params) (hp : spec.valid p) :
    (period p.input : ℕ) * ((p.input.count : ℕ) + 1) * (⌈Real.log (1 / p.failure)⌉₊ + 1) ≤
      ⌈100000000000000 * (p.input.count : ℝ) ^ 3 * (p.input.upper / p.input.lower) ^ 2 /
        p.input.derivativeMargin ^ 3 *
        Real.log (24000000 * p.input.upper ^ 2 / (p.input.derivativeMargin ^ 2 * p.input.contrast ^ 2)) *
        (1 + Real.log (1 / p.failure))⌉₊ := by
  have htime := run_time_bound p hp
  obtain ⟨_, hε, hρ, hρκ⟩ := parameter_bounds p hp
  rcases hp with ⟨_, hg, hgR, hμ, hκ, hκ₁, _, _, _, hδ₁, _, hfailure, hfailure₁, _⟩
  have hR : 0 < p.input.upper := hg.trans_le hgR
  have hδ : 0 < perturbation p.input := sq_pos_of_pos hε
  have hL := logarithm_lower (perturbation p.input) hδ hδ₁
  have hρ₁ : backgroundStep p.input ≤ 1 := by linarith
  have hN : (1 : ℝ) ≤ (p.input.count : ℝ) := by exact_mod_cast p.input.count.pos
  have hX : 1 ≤ (p.input.count : ℝ) / backgroundStep p.input ^ 2 *
      Real.log (24 / perturbation p.input) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).2
    nlinarith
  have hlog : 0 ≤ Real.log (1 / p.failure) :=
    Real.log_nonneg ((le_div_iff₀ hfailure).2 (by linarith))
  have hM := (confidence_repetitions p.failure hfailure hfailure₁).2
  have hcost := cycle_cost_bound (p.input.count : ℕ) (runSteps p.input)
    (⌈Real.log (1 / p.failure)⌉₊ + 1) p.input.derivativeMargin
    ((p.input.count : ℝ) / backgroundStep p.input ^ 2 * Real.log (24 / perturbation p.input))
    (1 + Real.log (1 / p.failure)) p.input.count.pos hκ hκ₁ hX (by linarith) htime hM
  have hearg : 24 / perturbation p.input =
      24000000 * p.input.upper ^ 2 / (p.input.derivativeMargin ^ 2 * p.input.contrast ^ 2) := by
    dsimp [perturbation, stepSize]
    field_simp
    ring
  rw [hearg] at hcost
  have he : 100000000 * (p.input.count : ℝ) ^ 2 *
      ((p.input.count : ℝ) / backgroundStep p.input ^ 2 *
        Real.log (24000000 * p.input.upper ^ 2 / (p.input.derivativeMargin ^ 2 * p.input.contrast ^ 2))) /
        p.input.derivativeMargin * (1 + Real.log (1 / p.failure)) =
      100000000000000 * (p.input.count : ℝ) ^ 3 * (p.input.upper / p.input.lower) ^ 2 /
        p.input.derivativeMargin ^ 3 *
        Real.log (24000000 * p.input.upper ^ 2 / (p.input.derivativeMargin ^ 2 * p.input.contrast ^ 2)) *
        (1 + Real.log (1 / p.failure)) := by
    dsimp [backgroundStep, stepSize]
    field_simp
    ring
  rw [he] at hcost
  exact_mod_cast hcost.trans (Nat.le_ceil _)

end LongTails.Proofs.FiniteScaleConvolutionalSgdTuning
