import LongTails.Algorithms.HolderNoiseVarianceReduction
import LongTails.Proofs.HolderNoiseScales

namespace OracleTemplate.HolderNoise

open DyadicHolder

lemma calls_eq_off (cfg : DyadicConfig) : calls cfg = off cfg (cfg.K + 1) :=
  (off_eq_sum cfg _).symm

lemma select_calls (a b : DyadicConfig) :
    calls (selectConfig a b) = min (calls a) (calls b) := by
  unfold selectConfig
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

lemma anchor_calls (L σ Δ ε : ℝ) :
    calls (anchorConfig L σ Δ ε) = (tK L Δ ε + 1) * tbA σ ε := by
  simp [calls, anchorConfig, DyadicConfig.batch, DyadicConfig.pos, tK, tbA, Nat.mod_one]

lemma anchor_calls_le {L σ Δ ε : ℝ} (hL : 0 < L)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (calls (anchorConfig L σ Δ ε) : ℝ) ≤
      600 * (1 + (L * Δ + σ ^ 2) / ε ^ 2 + L * Δ * σ ^ 2 / ε ^ 4) := by
  have hK : (tK L Δ ε : ℝ) ≤ 16 * L * Δ / ε ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hA : (tbA σ ε : ℝ) ≤ 32 * σ ^ 2 / ε ^ 2 + 2 := by
    unfold tbA
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 32 * σ ^ 2 / ε ^ 2 by positivity)
    linarith
  rw [anchor_calls]
  push_cast
  have hprod := mul_le_mul (by linarith : (tK L Δ ε : ℝ) + 1 ≤
    16 * L * Δ / ε ^ 2 + 2) hA (Nat.cast_nonneg _) (by positivity)
  have hx : 0 ≤ L * Δ / ε ^ 2 := by positivity
  have hy : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have hxy := mul_nonneg hx hy
  have he : L * Δ * σ ^ 2 / ε ^ 4 = (L * Δ / ε ^ 2) * (σ ^ 2 / ε ^ 2) := by ring
  rw [he, add_div]
  rw [show 16 * L * Δ / ε ^ 2 = 16 * (L * Δ / ε ^ 2) by ring,
    show 32 * σ ^ 2 / ε ^ 2 = 32 * (σ ^ 2 / ε ^ 2) by ring] at hprod
  nlinarith

lemma low_calls_le {L M ν σ Δ ε : ℝ} (hL : 0 < L) (hM : 0 ≤ M)
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (calls (tcfg L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε) : ℝ) ≤
      3200 * (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2 *
        (1 + (L * Δ + σ ^ 2) / ε ^ 2 + Δ * M * (L / ε) ^ (1 - 2 * ν) / ε ^ 3) := by
  have hη : 0 < tEta L ε := by unfold tEta; positivity
  have ht : TuneHyp L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε :=
    ⟨hL, by positivity, le_rfl, by norm_num, hσ, hΔ, hε⟩
  have hc := ht.calls
  norm_num only [show 1 / (2 * (1 / 2 : ℝ)) = 1 by norm_num,
    show 2 - 1 / (1 / 2 : ℝ) = 0 by norm_num, Real.rpow_one, Real.rpow_zero, mul_one] at hc
  have he := LongTails.Proofs.HolderNoiseScales.effective_scale_le hL hε hν
  have hs : Δ * (M * tEta L ε ^ (2 * ν - 1)) / ε ^ 3 ≤
      4 * (Δ * M * (L / ε) ^ (1 - 2 * ν) / ε ^ 3) := by
    calc _ ≤ Δ * (M * (4 * (L / ε) ^ (1 - 2 * ν))) / ε ^ 3 := by
          gcongr
          exact he
      _ = _ := by ring
  have hb : 0 ≤ 1 + (L * Δ + σ ^ 2) / ε ^ 2 := by positivity
  rw [calls_eq_off]
  refine hc.trans ?_
  have hfac : 0 ≤ (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hfac hb, mul_le_mul_of_nonneg_left hs hfac]

lemma combined_calls_le {L M ν σ Δ ε : ℝ} (hL : 0 < L) (hM : 0 ≤ M)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let a := if ν ≤ 1 / 2 then tcfg L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε
      else tcfg L M ν σ Δ ε
    (calls (selectConfig a (anchorConfig L σ Δ ε)) : ℝ) ≤
      min (600 * (1 + (L * Δ + σ ^ 2) / ε ^ 2 + L * Δ * σ ^ 2 / ε ^ 4))
        (3200 * (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2 *
          (1 + (L * Δ + σ ^ 2) / ε ^ 2 +
            max (Δ * M * (L / ε) ^ (1 - 2 * ν) / ε ^ 3)
              (Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3))) := by
  let a := if ν ≤ 1 / 2 then tcfg L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε
    else tcfg L M ν σ Δ ε
  let c := 3200 * (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2
  let b := 1 + (L * Δ + σ ^ 2) / ε ^ 2
  let s := L * Δ * σ ^ 2 / ε ^ 4
  let t := max (Δ * M * (L / ε) ^ (1 - 2 * ν) / ε ^ 3)
    (Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ha : (calls a : ℝ) ≤ c * (b + t) := by
    dsimp only [a]
    split_ifs with hhalf
    · refine (low_calls_le hL hM hν.le hσ hΔ hε).trans ?_
      change c * (b + _) ≤ c * (b + t)
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_max_left _ _)) hc0
    · have H : TuneHyp L M ν σ Δ ε :=
        ⟨hL, hM, (lt_of_not_ge hhalf).le, hν1, hσ, hΔ, hε⟩
      rw [calls_eq_off]
      refine H.calls.trans ?_
      have hT := le_max_right (Δ * M * (L / ε) ^ (1 - 2 * ν) / ε ^ 3)
        (Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3)
      change _ ≤ c * (b + t)
      have hfac : 0 ≤ (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2 := sq_nonneg _
      dsimp [c, b, t] at *
      nlinarith [mul_le_mul_of_nonneg_left hT hfac,
        mul_nonneg hfac hb, mul_nonneg hfac ht]
  have ha' : (calls (anchorConfig L σ Δ ε) : ℝ) ≤ 600 * (b + s) :=
    anchor_calls_le hL hΔ hε
  change (calls (selectConfig a (anchorConfig L σ Δ ε)) : ℝ) ≤ min (600 * (b + s)) (c * (b + t))
  rw [select_calls, Nat.cast_min]
  exact le_min ((min_le_right _ _).trans ha') ((min_le_left _ _).trans ha)

lemma variation_cost_factor {L M ν σ Δ ε : ℝ} (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) :
    max (Δ * M * (L / ε) ^ (1 - 2 * ν) / ε ^ 3)
      (Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3) =
      Δ / ε ^ 3 * max (M * (L / ε) ^ (1 - 2 * ν))
        (M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν)) := by
  rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ Δ / ε ^ 3)]
  congr 1 <;> ring

end OracleTemplate.HolderNoise
