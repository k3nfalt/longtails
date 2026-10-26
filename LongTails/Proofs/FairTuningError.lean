import LongTails.Proofs.FairTuning

namespace OracleTemplate.FairVarianceReduction

lemma tune_refresh_leading {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    (r + ε) ^ 2 / (tuneRefreshBatch r ε : ℝ) ≤ ε ^ 2 / (2 : ℝ) ^ 20 := by
  have hb : (0 : ℝ) < tuneRefreshBatch r ε := by exact_mod_cast tuneRefreshBatch_pos hr hε
  have hc := Nat.le_ceil ((2 : ℝ) ^ 20 * (r + ε) ^ 2 / ε ^ 2)
  change (2 : ℝ) ^ 20 * (r + ε) ^ 2 / ε ^ 2 ≤ (tuneRefreshBatch r ε : ℝ) at hc
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  apply (div_le_iff₀ hb).mpr
  nlinarith

lemma tune_increment_leading {L κ r Δ ε : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hε : 0 < ε) :
    (tunePeriod L κ Δ ε : ℝ) * (2 : ℝ) ^ 23 * (r + ε) ^ 2 * κ ^ 2 * (tuneStep L ε) ^ 2 /
      (tuneIncrementBatch L κ r Δ ε : ℝ) ≤ ε ^ 2 / (2 : ℝ) ^ 32 := by
  have hb : (0 : ℝ) < tuneIncrementBatch L κ r Δ ε := by
    exact_mod_cast tuneIncrementBatch_pos L κ r Δ ε
  let X := (2 : ℝ) ^ 43 * (tunePeriod L κ Δ ε : ℝ) * κ ^ 2 * (r + ε) ^ 2 / L ^ 2
  have hc : X ≤ (tuneIncrementBatch L κ r Δ ε : ℝ) := by
    have hh := Nat.le_ceil X
    change X ≤ (1 + ⌈X⌉₊ : ℕ)
    push_cast
    linarith
  have hratio : X / (tuneIncrementBatch L κ r Δ ε : ℝ) ≤ 1 := (div_le_iff₀ hb).mpr (by simpa using hc)
  have he : (tunePeriod L κ Δ ε : ℝ) * (2 : ℝ) ^ 23 * (r + ε) ^ 2 * κ ^ 2 * (tuneStep L ε) ^ 2 /
      (tuneIncrementBatch L κ r Δ ε : ℝ) =
      (X / (tuneIncrementBatch L κ r Δ ε : ℝ)) * (ε ^ 2 / (2 : ℝ) ^ 32) := by
    dsimp [X, tuneStep]
    field_simp
    ring
  rw [he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ ε ^ 2 / (2 : ℝ) ^ 32)

lemma tune_increment_bias_leading {L κ r Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ)
    (hr : 0 ≤ r) (hε : 0 < ε) :
    ((tunePeriod L κ Δ ε - 1 : ℕ) : ℝ) * (2 / tuneClip r ε) *
      ((2 : ℝ) ^ 23 * (r + ε) ^ 2 * (κ ^ 2 * (tuneStep L ε) ^ 2)) ≤ ε / 65536 := by
  have hq := tunePeriod_pos (Δ := Δ) hL hκ hε
  by_cases hq1 : tunePeriod L κ Δ ε = 1
  · simp only [hq1, Nat.sub_self, Nat.cast_zero, zero_mul]
    positivity
  · have hlarge := tunePeriod_large (Δ := Δ) hL hκ hε (by omega)
    have hR : 0 < r + ε := by positivity
    have he : ((tunePeriod L κ Δ ε - 1 : ℕ) : ℝ) * (2 / tuneClip r ε) *
        ((2 : ℝ) ^ 23 * (r + ε) ^ 2 * (κ ^ 2 * (tuneStep L ε) ^ 2)) =
        ((tunePeriod L κ Δ ε - 1 : ℕ) : ℝ) * (κ * ε / L) ^ 2 * ε / 131072 := by
      unfold tuneClip tuneStep
      field_simp
      ring
    rw [he]
    have hu : 0 ≤ κ * ε / L := by positivity
    have hu1 : κ * ε / L ≤ 1 := (div_le_iff₀ hL).mpr (by linarith [hlarge.1])
    have hqu : (tunePeriod L κ Δ ε : ℝ) * (κ * ε / L) ≤ 2 := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hL).mpr hlarge.2
    have hspan : ((tunePeriod L κ Δ ε - 1 : ℕ) : ℝ) ≤ (tunePeriod L κ Δ ε : ℝ) := by
      exact_mod_cast Nat.sub_le (tunePeriod L κ Δ ε) 1
    have hsu := (mul_le_mul_of_nonneg_right hspan hu).trans hqu
    have hs2 : ((tunePeriod L κ Δ ε - 1 : ℕ) : ℝ) * (κ * ε / L) ^ 2 ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_left hu1
        (mul_nonneg (Nat.cast_nonneg (tunePeriod L κ Δ ε - 1)) hu)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs2 hε.le]

lemma rare_error_floors {G B R ε δ T s b0 b M : ℝ}
    (hG : 0 ≤ G) (hB : 0 < B) (hR : 0 ≤ R) (hε : 0 < ε) (hδ0 : 0 ≤ δ)
    (hT : 1 ≤ T) (hs0 : 0 ≤ s) (hsT : s ≤ T) (hb0 : 1 ≤ b0) (hb : 1 ≤ b)
    (hM : G + B + R + ε ≤ M)
    (hδ : δ ≤ ε ^ 2 / ((2 : ℝ) ^ 53 * T * M ^ 2))
    (hclip : 2 / B * ((2 : ℝ) ^ 23 * R ^ 2) ≤ ε) :
    (2 * G + 3 * R) ^ 2 * δ / b0 + s * (((2 : ℝ) ^ 23 * R ^ 2 + 8 * B ^ 2) * δ / b) ≤
      ε ^ 2 / 4096 ∧
    (2 * G + 3 * R) * δ + s * (2 / B * ((2 : ℝ) ^ 23 * R ^ 2) + 4 * B) * δ ≤ ε / 1024 := by
  have hMp : 0 < M := by linarith
  have hRM : R ≤ M := by linarith
  have hBM : B ≤ M := by linarith
  have hεM : ε ≤ M := by linarith
  have hden : 0 < (2 : ℝ) ^ 53 * T * M ^ 2 := by positivity
  have hd := (le_div_iff₀ hden).mp hδ
  have hd2 : T * M ^ 2 * δ ≤ ε ^ 2 / (2 : ℝ) ^ 53 := by nlinarith
  have hd1 : T * M * δ ≤ ε / (2 : ℝ) ^ 53 := by
    have hm := mul_le_mul_of_nonneg_left hεM (show 0 ≤ T * M * δ by positivity)
    have he : T * M * δ * ε ≤ ε ^ 2 / (2 : ℝ) ^ 53 := by nlinarith
    nlinarith
  have hbase : M ^ 2 * δ ≤ T * M ^ 2 * δ := by
    have := mul_le_mul_of_nonneg_right hT (show 0 ≤ M ^ 2 * δ by positivity)
    nlinarith
  have ha : (2 * G + 3 * R) ^ 2 ≤ 9 * M ^ 2 := by
    have hlin : 0 ≤ 2 * G + 3 * R := by positivity
    have hlin' : 2 * G + 3 * R ≤ 3 * M := by linarith
    nlinarith [pow_le_pow_left₀ hlin hlin' 2]
  have hb' : (2 : ℝ) ^ 23 * R ^ 2 + 8 * B ^ 2 ≤ 16777216 * M ^ 2 := by
    have hr2 := pow_le_pow_left₀ hR hRM 2
    have hb2 := pow_le_pow_left₀ hB.le hBM 2
    norm_num
    nlinarith [sq_nonneg M]
  have hf0 : (2 * G + 3 * R) ^ 2 * δ / b0 ≤ 9 * T * M ^ 2 * δ := by
    have hi := div_le_self (show 0 ≤ (2 * G + 3 * R) ^ 2 * δ by positivity) hb0
    have hh := mul_le_mul_of_nonneg_right ha hδ0
    nlinarith
  have hf1 : s * (((2 : ℝ) ^ 23 * R ^ 2 + 8 * B ^ 2) * δ / b) ≤ 16777216 * T * M ^ 2 * δ := by
    have hi := div_le_self (show 0 ≤ ((2 : ℝ) ^ 23 * R ^ 2 + 8 * B ^ 2) * δ by positivity) hb
    have hh := mul_le_mul_of_nonneg_right hb' hδ0
    have hs := mul_le_mul_of_nonneg_left (hi.trans hh) hs0
    have ht := mul_le_mul_of_nonneg_right hsT (show 0 ≤ 16777216 * M ^ 2 * δ by positivity)
    nlinarith
  constructor
  · nlinarith [sq_nonneg ε]
  · have hbias0 : (2 * G + 3 * R) * δ ≤ 3 * T * M * δ := by
      have hh := mul_le_mul_of_nonneg_right (show 2 * G + 3 * R ≤ 3 * M by linarith) hδ0
      have ht := mul_le_mul_of_nonneg_right hT (show 0 ≤ M * δ by positivity)
      nlinarith
    have hbias1 : s * (2 / B * ((2 : ℝ) ^ 23 * R ^ 2) + 4 * B) * δ ≤ 5 * T * M * δ := by
      have hh : 2 / B * ((2 : ℝ) ^ 23 * R ^ 2) + 4 * B ≤ 5 * M := by linarith
      have hmul := mul_le_mul_of_nonneg_left hh hs0
      have ht := mul_le_mul_of_nonneg_right hsT (show 0 ≤ 5 * M by positivity)
      have he := mul_le_mul_of_nonneg_right (hmul.trans ht) hδ0
      nlinarith
    nlinarith

lemma tuned_error_bound {L κ r Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ)
    (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let cfg := tunedConfig L κ r Δ ε
    let δ := (1 / 4 : ℝ) ^ tuneBlockQuarter L r Δ ε
    let V0 := 9 * cfg.R ^ 2 + (2 * cfg.G + 3 * cfg.R) ^ 2 * δ
    let V1 := (2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + δ) + 8 * cfg.B ^ 2 * δ
    let β0 := (2 * cfg.G + 3 * cfg.R) * δ
    let β1 := 2 / cfg.B * ((2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + δ)) + 4 * cfg.B * δ
    Real.sqrt (V0 / cfg.b0 + ((cfg.q - 1 : ℕ) : ℝ) * (V1 / cfg.b)) +
      (β0 + ((cfg.q - 1 : ℕ) : ℝ) * β1) ≤ ε / 16 := by
  dsimp only
  let cfg := tunedConfig L κ r Δ ε
  let δ := (1 / 4 : ℝ) ^ tuneBlockQuarter L r Δ ε
  have hR : 0 < cfg.R := tuneRadius_pos hr hε
  have hG : 0 ≤ cfg.G := tuneGradientBound_nonneg hL hε
  have hB : 0 < cfg.B := tuneClip_pos hr hε
  have hT : (1 : ℝ) ≤ cfg.T := by exact_mod_cast tuneIterations_pos L Δ ε
  have hb0 : (1 : ℝ) ≤ cfg.b0 := by exact_mod_cast tuneRefreshBatch_pos hr hε
  have hb : (1 : ℝ) ≤ cfg.b := by exact_mod_cast tuneIncrementBatch_pos L κ r Δ ε
  have hspan : ((cfg.q - 1 : ℕ) : ℝ) ≤ (cfg.q : ℝ) := by exact_mod_cast Nat.sub_le cfg.q 1
  have hqT : (cfg.q : ℝ) ≤ cfg.T := by exact_mod_cast tunePeriod_le_iterations hL hκ hε
  have hclip : 2 / cfg.B * ((2 : ℝ) ^ 23 * cfg.R ^ 2) ≤ ε := by
    have he : 2 / cfg.B * ((2 : ℝ) ^ 23 * cfg.R ^ 2) = ε / 32 := by
      dsimp [cfg, tunedConfig, tuneClip, tuneRadius]
      have hRp : 0 < r + ε := by positivity
      field_simp
      norm_num
    rw [he]
    linarith
  have hf := rare_error_floors hG hB hR.le hε (show 0 ≤ δ by dsimp [δ]; positivity)
    hT (Nat.cast_nonneg (cfg.q - 1)) (hspan.trans hqT) hb0 hb le_rfl
    (tune_failure_scale (κ := κ) hL hr hΔ hε) hclip
  have hrlead := tune_refresh_leading hr hε
  change cfg.R ^ 2 / (cfg.b0 : ℝ) ≤ ε ^ 2 / (2 : ℝ) ^ 20 at hrlead
  have hilead := tune_increment_leading (κ := κ) (Δ := Δ) hL hr hε
  change (cfg.q : ℝ) * (2 : ℝ) ^ 23 * cfg.R ^ 2 * κ ^ 2 * cfg.η ^ 2 / cfg.b ≤
    ε ^ 2 / (2 : ℝ) ^ 32 at hilead
  have hslead : ((cfg.q - 1 : ℕ) : ℝ) * (2 : ℝ) ^ 23 * cfg.R ^ 2 * κ ^ 2 * cfg.η ^ 2 / cfg.b ≤
      ε ^ 2 / (2 : ℝ) ^ 32 := by
    apply le_trans _ hilead
    gcongr
  have hbias := tune_increment_bias_leading (Δ := Δ) hL hκ hr hε
  change ((cfg.q - 1 : ℕ) : ℝ) * (2 / cfg.B) *
    ((2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2)) ≤ ε / 65536 at hbias
  have hv : (9 * cfg.R ^ 2 + (2 * cfg.G + 3 * cfg.R) ^ 2 * δ) / cfg.b0 +
      ((cfg.q - 1 : ℕ) : ℝ) *
        (((2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + δ) + 8 * cfg.B ^ 2 * δ) / cfg.b) ≤ ε ^ 2 / 1024 := by
    calc
      _ = 9 * (cfg.R ^ 2 / cfg.b0) +
          ((cfg.q - 1 : ℕ) : ℝ) * (2 : ℝ) ^ 23 * cfg.R ^ 2 * κ ^ 2 * cfg.η ^ 2 / cfg.b +
          ((2 * cfg.G + 3 * cfg.R) ^ 2 * δ / cfg.b0 +
            ((cfg.q - 1 : ℕ) : ℝ) * (((2 : ℝ) ^ 23 * cfg.R ^ 2 + 8 * cfg.B ^ 2) * δ / cfg.b)) := by ring
      _ ≤ 9 * (ε ^ 2 / (2 : ℝ) ^ 20) + ε ^ 2 / (2 : ℝ) ^ 32 + ε ^ 2 / 4096 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hrlead (by norm_num)) hslead) hf.1
      _ ≤ ε ^ 2 / 1024 := by nlinarith [sq_nonneg ε]
  have hd : (2 * cfg.G + 3 * cfg.R) * δ + ((cfg.q - 1 : ℕ) : ℝ) *
      (2 / cfg.B * ((2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + δ)) + 4 * cfg.B * δ) ≤ ε / 32 := by
    nlinarith [hf.2]
  have hsqrt := Real.sqrt_le_iff.mpr ⟨show 0 ≤ ε / 32 by positivity,
    show (9 * cfg.R ^ 2 + (2 * cfg.G + 3 * cfg.R) ^ 2 * δ) / cfg.b0 +
      ((cfg.q - 1 : ℕ) : ℝ) *
        (((2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + δ) + 8 * cfg.B ^ 2 * δ) / cfg.b) ≤ (ε / 32) ^ 2 by nlinarith⟩
  change Real.sqrt _ + _ ≤ ε / 16
  linarith

end OracleTemplate.FairVarianceReduction
