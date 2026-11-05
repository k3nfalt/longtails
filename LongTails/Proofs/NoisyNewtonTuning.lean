import LongTails.Algorithms.NoisyDampedNewton
import LongTails.Proofs.NoisyMsAccounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.NoisyNewtonTuning

open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton

lemma confidence_lower (p : Params) (hp : spec.valid p) : 100 ≤ confidence p := by
  rcases hp with ⟨hM₀, hM₁, hρ, hδ, hσ, hR, hΔ, hε, hβ, hβ₁⟩
  let X := 2 + p.Δ / p.ε + p.δ * p.R ^ 2 / p.ε + p.M₀ * p.R ^ 3 / p.ε +
    p.M₁ * p.R ^ 2 + (p.R / p.ρ) ^ 2 + 1 / p.β + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2
  have hβ' : 1 ≤ 1 / p.β := (le_div_iff₀ hβ).mpr (by linarith)
  have hX : 3 ≤ X := by
    dsimp [X]
    have h₁ : 0 ≤ p.Δ / p.ε := by positivity
    have h₂ : 0 ≤ p.δ * p.R ^ 2 / p.ε := by positivity
    have h₃ : 0 ≤ p.M₀ * p.R ^ 3 / p.ε := by positivity
    have h₄ : 0 ≤ p.M₁ * p.R ^ 2 := by positivity
    have h₅ : 0 ≤ (p.R / p.ρ) ^ 2 := sq_nonneg _
    have h₆ : 0 ≤ p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 := by positivity
    linarith
  have hl : 1 ≤ Real.log X := (Real.le_log_iff_exp_le (by linarith : 0 < X)).mpr
    (Real.exp_one_lt_three.le.trans hX)
  change 100 ≤ 100 * Real.log X
  linarith

lemma target_pos (p : Params) (hp : spec.valid p) : 0 < target p := by
  rcases hp with ⟨_, _, _, _, _, hR, _, hε, _, _⟩
  unfold target
  positivity

lemma tolerance_bounds (p : Params) (hp : spec.valid p) :
    0 < tolerance p ∧ tolerance p ≤ 1 / 4 := by
  have hl := confidence_lower p hp
  unfold tolerance
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 262144 * confidence p)).mpr
    linarith

lemma modelRadius_pos (p : Params) (hp : spec.valid p) (a : ℝ) (ha : 0 < a) :
    0 < modelRadius p a := by
  have hl := confidence_lower p hp
  have hε := hp.2.2.2.2.2.2.2.1
  unfold modelRadius
  positivity

lemma modelRadius_half_square (p : Params) (hp : spec.valid p) (a : ℝ) (ha : 0 < a) :
    (modelRadius p a / 2) ^ 2 = p.ε / (1073741824 * confidence p ^ 2 * a) := by
  have hl := confidence_lower p hp
  have hε := hp.2.2.2.2.2.2.2.1
  unfold modelRadius
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.sq_sqrt (by positivity)]

lemma modelSize_variance (p : Params) (hp : spec.valid p) (a : ℝ) (ha : 0 < a) :
    p.σ ^ 2 / (modelSize p a : ℝ) ≤ modelRadius p a ^ 2 / 576 := by
  have hB := modelRadius_pos p hp a ha
  have hm : 0 < (modelSize p a : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hc : 576 * p.σ ^ 2 / modelRadius p a ^ 2 ≤ (modelSize p a : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hc' := (div_le_iff₀ (sq_pos_of_pos hB)).mp hc
  apply (div_le_iff₀ hm).mpr
  nlinarith only [hc']

lemma updateSize_variance (p : Params) (hp : spec.valid p) (a : ℝ) (ha : 0 < a) :
    p.σ ^ 2 / (updateSize p a : ℝ) ≤ p.ε / (16777216 * a * confidence p ^ 2) := by
  have hl := confidence_lower p hp
  have hε := hp.2.2.2.2.2.2.2.1
  have hm : 0 < (updateSize p a : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hc : 16777216 * p.σ ^ 2 * a * confidence p ^ 2 / p.ε ≤ (updateSize p a : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hc' := (div_le_iff₀ hε).mp hc
  apply (div_le_div_iff₀ hm (by positivity : 0 < 16777216 * a * confidence p ^ 2)).mpr
  nlinarith only [hc']

lemma initial_properties (p : Params) (hp : spec.valid p) :
    0 < (initialIterate p).A ∧ (initialIterate p).A ≤ target p / 4 ∧
      0 < (initialIterate p).guess := by
  have hT := target_pos p hp
  have hR := hp.2.2.2.2.2.1
  have hΔ := hp.2.2.2.2.2.2.1
  refine ⟨?_, min_le_left _ _, ?_⟩
  · change 0 < min (target p / 4) (p.R ^ 2 / (2 * p.Δ))
    positivity
  · change 0 < 2 / target p
    positivity

lemma correction_mgf_small (R a ℓ : ℝ) (hR : 0 < R) (ha : 0 < a) (hℓ : 1 ≤ ℓ) :
    (ℓ / R ^ 2) * (a * (3 * R / (512 * a * ℓ)) * (5 * R) +
      (1 / 2 : ℝ) * a ^ 2 * (3 * R / (512 * a * ℓ)) ^ 2) ≤ 1 := by
  have hl : 0 < ℓ := by linarith
  have he : (ℓ / R ^ 2) * (a * (3 * R / (512 * a * ℓ)) * (5 * R) +
      (1 / 2 : ℝ) * a ^ 2 * (3 * R / (512 * a * ℓ)) ^ 2) =
      15 / 512 + 9 / (524288 * ℓ) := by
    field_simp
    ring
  rw [he]
  have hh : 9 / (524288 * ℓ) ≤ 9 / 524288 := by gcongr; linarith
  linarith

lemma correction_mgf_exponent (R a ℓ v : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hℓ : 1 ≤ ℓ) (hv : 0 ≤ v) :
    (ℓ / R ^ 2) * (a * (5 * R) * (512 * a * ℓ * v / R) + (1 / 2 : ℝ) * a ^ 2 * v) +
      2 * (ℓ / R ^ 2) ^ 2 * (a ^ 2 * (5 * R) ^ 2 +
        (1 / 2 : ℝ) ^ 2 * a ^ 4 * (3 * R / (512 * a * ℓ)) ^ 2) * v ≤
      2611 * ℓ ^ 2 * a ^ 2 * v / R ^ 2 := by
  have hl : 0 < ℓ := by linarith
  have he : (ℓ / R ^ 2) * (a * (5 * R) * (512 * a * ℓ * v / R) + (1 / 2 : ℝ) * a ^ 2 * v) +
      2 * (ℓ / R ^ 2) ^ 2 * (a ^ 2 * (5 * R) ^ 2 +
        (1 / 2 : ℝ) ^ 2 * a ^ 4 * (3 * R / (512 * a * ℓ)) ^ 2) * v =
      (2610 + 1 / (2 * ℓ) + 9 / (524288 * ℓ ^ 2)) * (ℓ ^ 2 * a ^ 2 * v / R ^ 2) := by
    field_simp
    ring
  rw [he]
  have h₁ : 1 / (2 * ℓ) ≤ 1 / 2 := by gcongr; linarith
  have h₂ : 9 / (524288 * ℓ ^ 2) ≤ 9 / 524288 := by gcongr; nlinarith
  have hc : 2610 + 1 / (2 * ℓ) + 9 / (524288 * ℓ ^ 2) ≤ 2611 := by linarith
  convert mul_le_mul_of_nonneg_right hc (show 0 ≤ ℓ ^ 2 * a ^ 2 * v / R ^ 2 by positivity) using 1; ring

lemma correction_mgf_budget (R a ℓ ε : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε) :
    2611 * ℓ ^ 2 * a ^ 2 * (ε / (16777216 * a * ℓ ^ 2)) / R ^ 2 ≤ ε * a / (4096 * R ^ 2) := by
  have he : 2611 * ℓ ^ 2 * a ^ 2 * (ε / (16777216 * a * ℓ ^ 2)) / R ^ 2 =
      (2611 / 16777216 : ℝ) * (ε * a / R ^ 2) := by field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_right (by norm_num : (2611 / 16777216 : ℝ) ≤ 1 / 4096)
    (show 0 ≤ ε * a / R ^ 2 by positivity)
  convert hh using 1; ring

lemma tentativeWeight_cap {E : Type*} (s : OracleTemplate.GeneralizedAccelerated.Iterate E)
    (W : ℝ) (hW : 0 < W) (hA : 0 ≤ s.A) (hcap : s.A ≤ W / 2)
    (hη : 2 / W ≤ s.guess) : OracleTemplate.GeneralizedAccelerated.tentativeWeight s ≤ W := by
  have hηp : 0 < s.guess := lt_of_lt_of_le (by positivity) hη
  have hw := (div_le_iff₀ hW).mp hη
  have hmul := mul_le_mul_of_nonneg_right hw hW.le
  apply LongTails.Proofs.NoisyMsAccounting.quadratic_root_upper s.guess s.A
    (OracleTemplate.GeneralizedAccelerated.tentativeWeight s) W hηp
    (OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos s hηp)
    (OracleTemplate.GeneralizedAccelerated.tentativeWeight_equation s hA hηp)
  · linarith
  · nlinarith only [hmul, hcap, hW.le]

lemma actualWeight_bounds {E : Type*} (t : Trial E) (hη : 0 < t.previous.guess)
    (hτ : t.previous.guess ≤ t.curvature) :
    0 < actualWeight t ∧ actualWeight t ≤ OracleTemplate.GeneralizedAccelerated.tentativeWeight t.previous := by
  have ht := hη.trans_le hτ
  have hp := OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos t.previous hη
  constructor
  · exact mul_pos (div_pos hη ht) hp
  · exact mul_le_of_le_one_left hp.le ((div_le_one ht).mpr hτ)

lemma finish_weight_cap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Trial E) (floor W : ℝ) (hW : 0 < W) (hA : 0 ≤ t.previous.A)
    (hcap : t.previous.A ≤ W / 2) (hη : 2 / W ≤ t.previous.guess)
    (hτ : t.previous.guess ≤ t.curvature) (u : E) :
    t.previous.A < (finish floor t u).A ∧ (finish floor t u).A ≤ 3 * W / 2 := by
  have hηp : 0 < t.previous.guess := lt_of_lt_of_le (by positivity) hη
  have ha := actualWeight_bounds t hηp hτ
  have hp := tentativeWeight_cap t.previous W hW hA hcap hη
  change t.previous.A < t.previous.A + actualWeight t ∧ t.previous.A + actualWeight t ≤ _
  constructor <;> linarith

lemma finish_floor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Trial E) (floor : ℝ) (hf : 0 ≤ floor) (hη : floor ≤ t.previous.guess) (u : E) :
    floor ≤ (finish floor t u).guess := by
  unfold finish
  dsimp only
  split_ifs
  · exact le_max_left _ _
  · linarith

lemma confidence_log_inv_beta (p : Params) (hp : spec.valid p) :
    Real.log (1 / p.β) ≤ confidence p / 100 := by
  rcases hp with ⟨hM₀, hM₁, hρ, hδ, hσ, hR, hΔ, hε, hβ, hβ₁⟩
  let X := 2 + p.Δ / p.ε + p.δ * p.R ^ 2 / p.ε + p.M₀ * p.R ^ 3 / p.ε +
    p.M₁ * p.R ^ 2 + (p.R / p.ρ) ^ 2 + 1 / p.β + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2
  have hrest : 0 ≤ 2 + p.Δ / p.ε + p.δ * p.R ^ 2 / p.ε + p.M₀ * p.R ^ 3 / p.ε +
      p.M₁ * p.R ^ 2 + (p.R / p.ρ) ^ 2 + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 := by positivity
  have hX : 1 / p.β ≤ X := by dsimp [X]; linarith
  have hh := Real.log_le_log (by positivity : 0 < 1 / p.β) hX
  change Real.log (1 / p.β) ≤ (100 * Real.log X) / 100
  linarith

lemma noise_tail_probability_bound (p : Params) (hp : spec.valid p) :
    Real.exp (48 / 4096 - 2 * confidence p) ≤ p.β / 4 := by
  have hβ := hp.2.2.2.2.2.2.2.2.1
  have hl := confidence_lower p hp
  have hb := confidence_log_inv_beta p hp
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hh
    exact hh
  have he : Real.log (p.β / 4) = -Real.log (1 / p.β) - Real.log 4 := by
    rw [Real.log_div hβ.ne' (by norm_num), Real.log_div (by norm_num) hβ.ne', Real.log_one]
    ring
  calc
    _ ≤ Real.exp (Real.log (p.β / 4)) := by
      apply Real.exp_le_exp.mpr
      rw [he]
      linarith
    _ = _ := Real.exp_log (by positivity)

noncomputable def shape (p : Params) : ℝ :=
  1 + (p.M₁ * p.R ^ 2) ^ (1 / 3 : ℝ) + (p.R / p.ρ) ^ (2 / 3 : ℝ) +
    (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) + Real.sqrt (p.δ * p.R ^ 2 / p.ε)

noncomputable def countScale (p : Params) : ℝ := 1048576 * shape p * confidence p

noncomputable def horizon (p : Params) : ℕ := ⌈1073741824 * shape p * confidence p ^ 2⌉₊

lemma shape_bounds (p : Params) (hp : spec.valid p) :
    1 ≤ shape p ∧ (p.M₁ * p.R ^ 2) ^ (1 / 3 : ℝ) ≤ shape p ∧
      (p.R / p.ρ) ^ (2 / 3 : ℝ) ≤ shape p ∧
      (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) ≤ shape p ∧
      Real.sqrt (p.δ * p.R ^ 2 / p.ε) ≤ shape p := by
  rcases hp with ⟨hM₀, hM₁, hρ, hδ, hσ, hR, hΔ, hε, hβ, hβ₁⟩
  have h₁ : 0 ≤ (p.M₁ * p.R ^ 2) ^ (1 / 3 : ℝ) := by positivity
  have h₂ : 0 ≤ (p.R / p.ρ) ^ (2 / 3 : ℝ) := by positivity
  have h₃ : 0 ≤ (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) := by positivity
  have h₄ := Real.sqrt_nonneg (p.δ * p.R ^ 2 / p.ε)
  unfold shape
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma countScale_pos (p : Params) (hp : spec.valid p) : 0 < countScale p := by
  have hs := (shape_bounds p hp).1
  have hl := confidence_lower p hp
  unfold countScale
  positivity

lemma horizon_pos (p : Params) (hp : spec.valid p) : 0 < horizon p := by
  have hs := (shape_bounds p hp).1
  have hl := confidence_lower p hp
  unfold horizon
  exact Nat.ceil_pos.mpr (by positivity)

lemma shape_power_bounds (p : Params) (hp : spec.valid p) :
    p.M₁ * p.R ^ 2 ≤ shape p ^ 3 ∧ (p.R / p.ρ) ^ 2 ≤ shape p ^ 3 ∧
      (p.M₀ * p.R ^ 3 / p.ε) ^ 2 ≤ shape p ^ 7 ∧ p.δ * p.R ^ 2 / p.ε ≤ shape p ^ 2 := by
  have hs := shape_bounds p hp
  rcases hp with ⟨hM₀, hM₁, hρ, hδ, hσ, hR, hΔ, hε, hβ, hβ₁⟩
  have h₁ := pow_le_pow_left₀ (by positivity : 0 ≤ (p.M₁ * p.R ^ 2) ^ (1 / 3 : ℝ)) hs.2.1 3
  have h₂ := pow_le_pow_left₀ (by positivity : 0 ≤ (p.R / p.ρ) ^ (2 / 3 : ℝ)) hs.2.2.1 3
  have h₃ := pow_le_pow_left₀ (by positivity : 0 ≤ (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ)) hs.2.2.2.1 7
  have h₄ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs.2.2.2.2 2
  rw [← Real.rpow_mul_natCast (by positivity)] at h₁ h₂ h₃
  norm_num at h₁ h₂ h₃
  rw [Real.sq_sqrt (by positivity)] at h₄
  exact ⟨h₁, h₂, h₃, h₄⟩

lemma scaleBase_bounds (p : Params) (hp : spec.valid p) :
    3 ≤ scaleBase p ∧ p.Δ / p.ε ≤ scaleBase p ∧ p.δ * p.R ^ 2 / p.ε ≤ scaleBase p ∧
    p.M₀ * p.R ^ 3 / p.ε ≤ scaleBase p ∧ p.M₁ * p.R ^ 2 ≤ scaleBase p ∧
    p.R / p.ρ ≤ scaleBase p ∧ 1 / p.β ≤ scaleBase p ∧
    p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 ≤ scaleBase p := by
  rcases hp with ⟨hM₀, hM₁, hρ, hδ, hσ, hR, hΔ, hε, hβ, hβ₁⟩
  have h₁ : 0 ≤ p.Δ / p.ε := by positivity
  have h₂ : 0 ≤ p.δ * p.R ^ 2 / p.ε := by positivity
  have h₃ : 0 ≤ p.M₀ * p.R ^ 3 / p.ε := by positivity
  have h₄ : 0 ≤ p.M₁ * p.R ^ 2 := by positivity
  have h₅ := sq_nonneg (p.R / p.ρ)
  have h₆ : 1 ≤ 1 / p.β := (le_div_iff₀ hβ).mpr (by linarith)
  have h₇ : 0 ≤ p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 := by positivity
  unfold scaleBase
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_, by linarith, by linarith⟩
  nlinarith only [h₁, h₂, h₃, h₄, h₆, h₇, sq_nonneg (p.R / p.ρ - 1)]

lemma shape_le_scaleBase (p : Params) (hp : spec.valid p) : shape p ≤ 5 * scaleBase p := by
  have hb := scaleBase_bounds p hp
  have hX : 1 ≤ scaleBase p := by linarith [hb.1]
  have h₁ : (p.M₁ * p.R ^ 2) ^ (1 / 3 : ℝ) ≤ scaleBase p :=
    (Real.rpow_le_rpow (mul_nonneg hp.2.1 (sq_nonneg p.R)) hb.2.2.2.2.1 (by norm_num)).trans
      (Real.rpow_le_self_of_one_le hX (by norm_num))
  have h₂ : (p.R / p.ρ) ^ (2 / 3 : ℝ) ≤ scaleBase p :=
    (Real.rpow_le_rpow (div_nonneg hp.2.2.2.2.2.1.le hp.2.2.1.le) hb.2.2.2.2.2.1 (by norm_num)).trans
      (Real.rpow_le_self_of_one_le hX (by norm_num))
  have h₃ : (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) ≤ scaleBase p := by
    have hM₀ := hp.1
    have hR := hp.2.2.2.2.2.1
    have hε := hp.2.2.2.2.2.2.2.1
    exact (Real.rpow_le_rpow (by positivity) hb.2.2.2.1 (by norm_num)).trans
      (Real.rpow_le_self_of_one_le hX (by norm_num))
  have h₄ : Real.sqrt (p.δ * p.R ^ 2 / p.ε) ≤ scaleBase p := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, hb.2.2.1.trans (by nlinarith only [hX, sq_nonneg (scaleBase p - 1)])⟩
  unfold shape
  linarith

lemma countScale_delta_cutoff (p : Params) (hp : spec.valid p) :
    16 * p.δ * target p ≤ tolerance p * countScale p ^ 2 := by
  have hs := (shape_power_bounds p hp).2.2.2
  have hl := confidence_lower p hp
  have hl0 : confidence p ≠ 0 := by linarith
  have he : tolerance p * countScale p ^ 2 =
      4194304 * shape p ^ 2 * confidence p := by
    unfold tolerance countScale
    field_simp [hl0]
    ring
  rw [he]
  calc
    16 * p.δ * target p = 512 * (p.δ * p.R ^ 2 / p.ε) := by unfold target; ring
    _ ≤ 512 * shape p ^ 2 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ _ := by
      have hh := mul_nonneg (sq_nonneg (shape p))
        (show 0 ≤ 4194304 * confidence p - 512 by linarith)
      nlinarith only [hh]

lemma countScale_rejection_cutoffs (p : Params) (hp : spec.valid p) :
    4 * (24 * p.R ^ 2) ≤ countScale p ^ 3 * p.ρ ^ 2 ∧
    16 * p.M₁ * (24 * p.R ^ 2) ≤ countScale p ^ 3 * tolerance p ∧
    256 * p.M₀ ^ 2 * target p ^ 2 * (24 * p.R ^ 2) ≤
      tolerance p ^ 2 * countScale p ^ 7 := by
  have hs := shape_power_bounds p hp
  have hs0 : 0 ≤ shape p := le_trans (by norm_num) (shape_bounds p hp).1
  have hl := confidence_lower p hp
  have hl1 : 1 ≤ confidence p := by linarith
  have hl0 : confidence p ≠ 0 := by linarith
  have hρ := hp.2.2.1
  have hε := hp.2.2.2.2.2.2.2.1
  have hpow3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hl1 3
  have hpow2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hl1 2
  have hpow5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hl1 5
  norm_num only [one_pow] at hpow3 hpow2 hpow5
  constructor
  · calc
      4 * (24 * p.R ^ 2) = 96 * ((p.R / p.ρ) ^ 2 * p.ρ ^ 2) := by
        field_simp
        ring
      _ ≤ 96 * (shape p ^ 3 * p.ρ ^ 2) := by gcongr; exact hs.2.1
      _ ≤ countScale p ^ 3 * p.ρ ^ 2 := by
        unfold countScale
        have hh := mul_le_mul_of_nonneg_right
          (show (96 : ℝ) ≤ 1048576 ^ 3 * confidence p ^ 3 by nlinarith only [hpow3])
          (show 0 ≤ shape p ^ 3 * p.ρ ^ 2 by positivity)
        nlinarith only [hh]
  constructor
  · have he : countScale p ^ 3 * tolerance p =
        4398046511104 * shape p ^ 3 * confidence p ^ 2 := by
      unfold countScale tolerance
      field_simp [hl0]
      ring
    rw [he]
    calc
      16 * p.M₁ * (24 * p.R ^ 2) = 384 * (p.M₁ * p.R ^ 2) := by ring
      _ ≤ 384 * shape p ^ 3 := mul_le_mul_of_nonneg_left hs.1 (by norm_num)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right
          (show (384 : ℝ) ≤ 4398046511104 * confidence p ^ 2 by nlinarith only [hpow2])
          (show 0 ≤ shape p ^ 3 by positivity)
        nlinarith only [hh]
  · have he : tolerance p ^ 2 * countScale p ^ 7 =
        20282409603651670423947251286016 * shape p ^ 7 * confidence p ^ 5 := by
      unfold countScale tolerance
      field_simp [hl0]
      ring
    rw [he]
    calc
      256 * p.M₀ ^ 2 * target p ^ 2 * (24 * p.R ^ 2) =
          6291456 * (p.M₀ * p.R ^ 3 / p.ε) ^ 2 := by unfold target; ring
      _ ≤ 6291456 * shape p ^ 7 := mul_le_mul_of_nonneg_left hs.2.2.1 (by norm_num)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right
          (show (6291456 : ℝ) ≤ 20282409603651670423947251286016 * confidence p ^ 5 by
            nlinarith only [hpow5]) (show 0 ≤ shape p ^ 7 by positivity)
        nlinarith only [hh]

lemma horizon_dominates_count (p : Params) (hp : spec.valid p) :
    6 * countScale p + 2 * (2 * countScale p + 1) * confidence p +
      20 * confidence p < (horizon p : ℝ) := by
  have hs := (shape_bounds p hp).1
  have hl := confidence_lower p hp
  have hQ : 1 ≤ countScale p := by
    unfold countScale
    nlinarith only [hs, hl, mul_nonneg (by linarith : 0 ≤ shape p - 1)
      (by linarith : 0 ≤ confidence p - 100)]
  have hN : 1024 * countScale p * confidence p ≤ (horizon p : ℝ) := by
    calc
      _ = 1073741824 * shape p * confidence p ^ 2 := by unfold countScale; ring
      _ ≤ _ := Nat.le_ceil _
  have h₁ : countScale p ≤ countScale p * confidence p := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ countScale p)
      (by linarith : 0 ≤ confidence p - 1)]
  have h₂ : confidence p ≤ countScale p * confidence p := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ countScale p - 1)
      (by linarith : 0 ≤ confidence p)]
  nlinarith only [hN, h₁, h₂, hl]

lemma countScale_log_bound (p : Params) (hp : spec.valid p) :
    Real.log (countScale p) ≤ confidence p := by
  have hX := (scaleBase_bounds p hp).1
  have hX0 : 0 < scaleBase p := by linarith
  have hs := shape_le_scaleBase p hp
  have hl := confidence_lower p hp
  have hlX : confidence p ≤ 100 * scaleBase p := by
    have hh := Real.log_le_sub_one_of_pos hX0
    unfold confidence
    linarith
  have hQ : countScale p ≤ (2 : ℝ) ^ 30 * scaleBase p ^ 2 := by
    calc
      _ ≤ 1048576 * (5 * scaleBase p) * (100 * scaleBase p) := by
        unfold countScale
        gcongr
      _ ≤ _ := by nlinarith only [sq_nonneg (scaleBase p)]
  have hh := Real.log_le_log (countScale_pos p hp) hQ
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hh
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he : confidence p = 100 * Real.log (scaleBase p) := rfl
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma initial_target_ratio (p : Params) (hp : spec.valid p) :
    target p / (initialIterate p).A ≤ 64 * scaleBase p := by
  have hW := target_pos p hp
  have hX := (scaleBase_bounds p hp).1
  have hΔX := (scaleBase_bounds p hp).2.1
  have hR := hp.2.2.2.2.2.1
  have hΔ := hp.2.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.1
  change target p / min (target p / 4) (p.R ^ 2 / (2 * p.Δ)) ≤ _
  rcases le_total (target p / 4) (p.R ^ 2 / (2 * p.Δ)) with h | h
  · rw [min_eq_left h]
    have he : target p / (target p / 4) = 4 := by field_simp
    rw [he]
    linarith
  · rw [min_eq_right h]
    have he : target p / (p.R ^ 2 / (2 * p.Δ)) = 64 * (p.Δ / p.ε) := by
      unfold target
      field_simp
      ring
    rw [he]
    linarith

lemma iterate_log_ratio (p : Params) (hp : spec.valid p) (A : ℝ)
    (hA : 0 < A) (hcap : A ≤ 3 * target p / 2) :
    Real.log A - Real.log (initialIterate p).A ≤ confidence p := by
  have hA₀ := (initial_properties p hp).1
  have hX := (scaleBase_bounds p hp).1
  have hX0 : 0 < scaleBase p := by linarith
  have hr := initial_target_ratio p hp
  have hl := confidence_lower p hp
  have hb : A / (initialIterate p).A ≤ 128 * scaleBase p := by
    have hh := div_le_div_of_nonneg_right hcap hA₀.le
    have he : (3 * target p / 2) / (initialIterate p).A =
        3 / 2 * (target p / (initialIterate p).A) := by ring
    rw [he] at hh
    linarith
  have hh := Real.log_le_log (div_pos hA hA₀) hb
  rw [Real.log_div hA.ne' hA₀.ne', Real.log_mul (by norm_num) hX0.ne'] at hh
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have he : confidence p = 100 * Real.log (scaleBase p) := rfl
  rw [h128] at hh
  linarith

lemma initial_threshold_bound (p : Params) (hp : spec.valid p) :
    (LongTails.Proofs.NoisyMsAccounting.dyadicThreshold (curvatureFloor p)
      (countScale p ^ 2 / (initialIterate p).A) : ℝ) ≤ 10 * confidence p := by
  have hW := target_pos p hp
  have hA := (initial_properties p hp).1
  have hcap := (initial_properties p hp).2.1
  have hf : 0 < curvatureFloor p := by unfold curvatureFloor; positivity
  have hQ := countScale_pos p hp
  have hs := (shape_bounds p hp).1
  have hl := confidence_lower p hp
  have hQ1 : 1 ≤ countScale p := by
    unfold countScale
    nlinarith only [hs, hl, mul_nonneg (by linarith : 0 ≤ shape p - 1)
      (by linarith : 0 ≤ confidence p - 100)]
  have hsmall : curvatureFloor p ≤ countScale p ^ 2 / (initialIterate p).A := by
    apply (le_div_iff₀ hA).mpr
    have hh := mul_le_mul_of_nonneg_left hcap hf.le
    have he : curvatureFloor p * (target p / 4) = 1 / 2 := by
      unfold curvatureFloor
      field_simp
      norm_num
    rw [he] at hh
    nlinarith only [hh, hQ1, sq_nonneg (countScale p - 1)]
  have ht := LongTails.Proofs.NoisyMsAccounting.dyadic_threshold_log
    (curvatureFloor p) (countScale p ^ 2 / (initialIterate p).A) hf hsmall
  have hX := (scaleBase_bounds p hp).1
  have hX0 : 0 < scaleBase p := by linarith
  have hr := initial_target_ratio p hp
  have hb : (countScale p ^ 2 / (initialIterate p).A) / curvatureFloor p ≤
      32 * countScale p ^ 2 * scaleBase p := by
    have he : (countScale p ^ 2 / (initialIterate p).A) / curvatureFloor p =
        countScale p ^ 2 / 2 * (target p / (initialIterate p).A) := by
      unfold curvatureFloor
      field_simp
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ countScale p ^ 2 / 2 by positivity)
    nlinarith only [hh]
  have hh := Real.log_le_log (by positivity :
    0 < (countScale p ^ 2 / (initialIterate p).A) / curvatureFloor p) hb
  rw [Real.log_mul (by positivity) hX0.ne', Real.log_mul (by norm_num) (by positivity),
    Real.log_pow] at hh
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  rw [h32] at hh
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2low : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hlogQ := countScale_log_bound p hp
  have he : confidence p = 100 * Real.log (scaleBase p) := rfl
  have hb' : Real.log ((countScale p ^ 2 / (initialIterate p).A) / curvatureFloor p) ≤
      3 * confidence p := by norm_num only [Nat.cast_ofNat] at hh; linarith
  have hd : Real.log ((countScale p ^ 2 / (initialIterate p).A) / curvatureFloor p) /
      Real.log 2 ≤ 6 * confidence p := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith only [hb', mul_nonneg (by linarith : 0 ≤ confidence p)
      (by linarith : 0 ≤ Real.log 2 - 1 / 2)]
  linarith

end LongTails.Proofs.NoisyNewtonTuning
