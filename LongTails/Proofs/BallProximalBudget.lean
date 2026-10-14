import LongTails.Proofs.BallProximalProfile

namespace OracleTemplate.BallProximal

noncomputable section

def accuracyCoefficient (Δ ε : ℝ) : ℝ :=
  min (1 / 2) (max 0 (1 - ε / Δ)) ^ 2 + max 0 (Real.log (Δ / (2 * ε))) / 2

lemma coefficient_high {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (he : ε < Δ)
    (hh : Δ ≤ 2 * ε) : accuracyCoefficient Δ ε = (1 - ε / Δ) ^ 2 := by
  have hratio : ε / Δ < 1 := (div_lt_one hΔ).mpr he
  have hhalf : 1 - ε / Δ ≤ 1 / 2 := by
    have hr := (le_div_iff₀ hΔ).mpr (show (1 / 2 : ℝ) * Δ ≤ ε by linarith)
    linarith
  have hlog : Real.log (Δ / (2 * ε)) ≤ 0 := Real.log_nonpos
    (by positivity) ((div_le_one (by positivity)).mpr hh)
  unfold accuracyCoefficient
  rw [max_eq_right (show 0 ≤ 1 - ε / Δ by linarith), min_eq_right hhalf, max_eq_left hlog]
  ring

lemma coefficient_low {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε)
    (hh : 2 * ε < Δ) :
    accuracyCoefficient Δ ε = 1 / 4 + Real.log (Δ / (2 * ε)) / 2 := by
  have hr : ε / Δ < 1 / 2 := (div_lt_iff₀ hΔ).mpr (by linarith)
  have hlog : 0 < Real.log (Δ / (2 * ε)) :=
    Real.log_pos ((one_lt_div (by positivity)).mpr hh)
  rw [accuracyCoefficient, max_eq_right (by linarith : 0 ≤ 1 - ε / Δ),
    min_eq_left (by linarith : (1 / 2 : ℝ) ≤ 1 - ε / Δ), max_eq_right hlog.le]
  ring

lemma high_gap_target_strict {H A g Δ ε R : ℝ} (hH : 0 ≤ H) (hA : 0 < A)
    (hε : 0 < ε) (heg : ε < g) (hgA : A ≤ g) (hΔ : A + g ≤ Δ) (hR : 0 < R)
    (henergy : H ^ 2 * (A + g) ^ 2 ≤ A ^ 2 * R ^ 2) :
    H ^ 2 < R ^ 2 * accuracyCoefficient Δ ε := by
  have hg : 0 < g := lt_trans hε heg
  have hD : 0 < Δ := by linarith
  have heD : ε < Δ := by linarith
  have hsum : 0 < A + g := by positivity
  have hbound : H * (A + g) ≤ A * R := by
    by_contra hbad
    have hm := mul_pos (sub_pos.mpr (lt_of_not_ge hbad))
      (show 0 < H * (A + g) + A * R by positivity)
    nlinarith only [hm, henergy]
  by_cases hh : Δ ≤ 2 * ε
  · rw [coefficient_high hD hε heD hh]
    have hratio : 0 < 1 - ε / Δ := by have := (div_lt_one hD).mpr heD; linarith
    have hgap : A < (A + g) * (1 - ε / Δ) := by
      have hm := mul_le_mul_of_nonneg_left hΔ hg.le
      have hs := mul_lt_mul_of_pos_left heg hsum
      apply (mul_lt_mul_iff_right₀ hD).mp
      field_simp
      nlinarith
    have hb : H < R * (1 - ε / Δ) := by
      have hm := mul_lt_mul_of_pos_left hgap hR
      nlinarith
    have hpos : 0 < R * (1 - ε / Δ) := mul_pos hR hratio
    nlinarith [mul_pos (sub_pos.mpr hb) (show 0 < R * (1 - ε / Δ) + H by linarith)]
  · have hh' : 2 * ε < Δ := by linarith
    rw [coefficient_low hD hε hh']
    have hb : H ≤ R / 2 := by nlinarith
    have hl : 0 < Real.log (Δ / (2 * ε)) :=
      Real.log_pos ((one_lt_div (by positivity)).mpr hh')
    have hp := mul_pos (sq_pos_of_pos hR) hl
    nlinarith [sq_nonneg (R / 2 - H)]

lemma low_gap_target_strict {H A g Δ ε R : ℝ} (_hH : 0 ≤ H) (hε : 0 < ε)
    (heg : ε < g) (hgA : g < A) (hΔ : A + g ≤ Δ) (hR : 0 < R)
    (henergy : 4 * H ^ 2 ≤ (1 + 2 * Real.log ((A + g) / (2 * g))) * R ^ 2) :
    H ^ 2 < R ^ 2 * accuracyCoefficient Δ ε := by
  have hg : 0 < g := lt_trans hε heg
  have hD : 0 < Δ := by linarith
  have hh : 2 * ε < Δ := by linarith
  rw [coefficient_low hD hε hh]
  have hratio : (A + g) / (2 * g) < Δ / (2 * ε) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_left hΔ hg.le
    have h2 := mul_lt_mul_of_pos_left heg (show 0 < A + g by linarith)
    nlinarith
  have hAg : 0 < A + g := by linarith
  have hlog := Real.log_lt_log (show 0 < (A + g) / (2 * g) by positivity) hratio
  have hm := mul_lt_mul_of_pos_right hlog (sq_pos_of_pos hR)
  nlinarith


lemma coefficient_nonneg (Δ ε : ℝ) : 0 ≤ accuracyCoefficient Δ ε := by
  unfold accuracyCoefficient
  positivity

lemma coefficient_zero {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (he : Δ ≤ ε) :
    accuracyCoefficient Δ ε = 0 := by
  have hr : 1 ≤ ε / Δ := (one_le_div hΔ).mpr he
  have hl : Real.log (Δ / (2 * ε)) ≤ 0 := Real.log_nonpos
    (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  simp [accuracyCoefficient, max_eq_left (show 1 - ε / Δ ≤ 0 by linarith),
    max_eq_left hl]

lemma profile_target_strict {qs : List (ℝ × ℝ)} {m g Δ ε R : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (heg : ε < g) (hR : 0 ≤ R)
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, m ≤ q.2)
    (hA : 0 < profileMass qs) (hΔ : profileMass qs + g ≤ Δ)
    (henergy : profileWork g qs + (g / m) ^ 2 ≤ R ^ 2) :
    (profileTime qs) ^ 2 < R ^ 2 * accuracyCoefficient Δ ε := by
  have hg : 0 < g := lt_trans hε heg
  have hapos := fun q hq => lt_of_lt_of_le hm (ha q hq)
  have hn := profile_nonneg ht hapos
  have hw := profile_work_nonneg hg.le ht hapos
  have hRp : 0 < R := by nlinarith [sq_pos_of_pos (div_pos hg hm)]
  rcases le_total (profileMass qs) g with hAg | hgA
  · have hh := profile_high_gap hm ht ha hA hAg
    have hmul := mul_le_mul_of_nonneg_left henergy (sq_nonneg (profileMass qs))
    exact high_gap_target_strict hn.1 hA hε heg hAg hΔ hRp (by nlinarith)
  · by_cases heq : g = profileMass qs
    · have hAg : profileMass qs ≤ g := by rw [heq]
      have hh := profile_high_gap hm ht ha hA hAg
      have hmul := mul_le_mul_of_nonneg_left henergy (sq_nonneg (profileMass qs))
      exact high_gap_target_strict hn.1 hA hε heg hAg hΔ hRp (by nlinarith)
    · have hlt : g < profileMass qs := lt_of_le_of_ne hgA heq
      have hh := profile_low_gap hm ht ha hg hlt
      have hl : 0 < Real.log ((profileMass qs + g) / (2 * g)) :=
        Real.log_pos ((one_lt_div (by positivity)).mpr (by linarith))
      have hmul := mul_le_mul_of_nonneg_left henergy
        (show 0 ≤ 1 + 2 * Real.log ((profileMass qs + g) / (2 * g)) by linarith)
      exact low_gap_target_strict hn.1 hε heg hlt hΔ hRp (by nlinarith)


lemma coefficient_pos {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (he : ε < Δ) :
    0 < accuracyCoefficient Δ ε := by
  by_cases hh : Δ ≤ 2 * ε
  · rw [coefficient_high hΔ hε he hh]
    apply sq_pos_of_pos
    have := (div_lt_one hΔ).mpr he
    linarith
  · rw [coefficient_low hΔ hε (by linarith)]
    have hl : 0 < Real.log (Δ / (2 * ε)) :=
      Real.log_pos ((one_lt_div (by positivity)).mpr (by linarith))
    linarith

lemma budget_positive {R t Δ ε : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hΔ : 0 < Δ) (hε : 0 < ε) (he : ε < Δ) :
    0 < ⌈min ((R / t) ^ 2) ((R / t) * Real.sqrt (accuracyCoefficient Δ ε))⌉₊ := by
  have hp : 0 < min ((R / t) ^ 2) ((R / t) * Real.sqrt (accuracyCoefficient Δ ε)) :=
    lt_min (sq_pos_of_pos (div_pos hR ht))
      (mul_pos (div_pos hR ht) (Real.sqrt_pos.mpr (coefficient_pos hΔ hε he)))
  exact Nat.ceil_pos.mpr hp

lemma budget_contradiction {K : ℕ} {R t Δ ε : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (hK : ⌈min ((R / t) ^ 2) ((R / t) * Real.sqrt (accuracyCoefficient Δ ε))⌉₊ ≤ K)
    (h1 : (K : ℝ) * t ^ 2 < R ^ 2)
    (h2 : ((K : ℝ) * t) ^ 2 < R ^ 2 * accuracyCoefficient Δ ε) : False := by
  have hk : min ((R / t) ^ 2) ((R / t) * Real.sqrt (accuracyCoefficient Δ ε)) ≤ (K : ℝ) :=
    Nat.ceil_le.mp hK
  rcases le_total ((R / t) ^ 2) ((R / t) * Real.sqrt (accuracyCoefficient Δ ε)) with hh | hh
  · rw [min_eq_left hh] at hk
    have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg t)
    have he : (R / t) ^ 2 * t ^ 2 = R ^ 2 := by field_simp
    rw [he] at hm
    linarith
  · rw [min_eq_right hh] at hk
    have hm := mul_le_mul_of_nonneg_right hk ht.le
    have he : (R / t) * Real.sqrt (accuracyCoefficient Δ ε) * t =
        R * Real.sqrt (accuracyCoefficient Δ ε) := by field_simp
    rw [he] at hm
    have hp := pow_le_pow_left₀ (mul_nonneg hR (Real.sqrt_nonneg _)) hm 2
    rw [mul_pow, Real.sq_sqrt (coefficient_nonneg Δ ε)] at hp
    linarith

end

end OracleTemplate.BallProximal
