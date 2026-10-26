import LongTails.Proofs.AdamComparisonTuning

namespace LongTails.Proofs.AdamTravelBound

lemma endpoint_sum_le (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (T : ℕ) :
    ∑ j ∈ Finset.range T, (A j + A (j + 1)) ≤ 2 * ∑ j ∈ Finset.range (T + 1), A j := by
  rw [Finset.sum_add_distrib]
  have h₁ : ∑ j ∈ Finset.range T, A j ≤ ∑ j ∈ Finset.range (T + 1), A j := by
    rw [Finset.sum_range_succ]
    linarith [hA T]
  have h₂ : ∑ j ∈ Finset.range T, A (j + 1) ≤ ∑ j ∈ Finset.range (T + 1), A j := by
    rw [Finset.sum_range_succ']
    linarith [hA 0]
  linarith

lemma absorbed_travel (A d : ℕ → ℝ) (T : ℕ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1 / 2) (hA : ∀ j, 0 ≤ A j)
    (hd : ∀ j < T, d j ≤ κ * (A j + A (j + 1) + d j)) :
    ∑ j ∈ Finset.range T, d j ≤ 4 * κ * ∑ j ∈ Finset.range (T + 1), A j := by
  have hpoint (j : ℕ) (hj : j < T) : d j ≤ 2 * κ * (A j + A (j + 1)) := by
    by_cases hdj : 0 ≤ d j
    · nlinarith [hd j hj, mul_nonneg (sub_nonneg.mpr hκ₁) hdj]
    · exact (le_of_lt (lt_of_not_ge hdj)).trans (mul_nonneg (by positivity) (add_nonneg (hA j) (hA (j + 1))))
  calc
    _ ≤ ∑ j ∈ Finset.range T, 2 * κ * (A j + A (j + 1)) :=
      Finset.sum_le_sum (fun j hj => hpoint j (Finset.mem_range.mp hj))
    _ = 2 * κ * ∑ j ∈ Finset.range T, (A j + A (j + 1)) := by rw [Finset.mul_sum]
    _ ≤ 2 * κ * (2 * ∑ j ∈ Finset.range (T + 1), A j) :=
      mul_le_mul_of_nonneg_left (endpoint_sum_le A hA T) (by positivity)
    _ = _ := by ring

lemma travel_from_barrier {ε D V Q : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hQ : Q ≤ ε) (hbarrier : 2 * ε * D ≤ D * Q + 4 * ε * V) :
    D / 4 ≤ V := by
  have := mul_le_mul_of_nonneg_left hQ hD
  nlinarith

lemma finite_barrier {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty I]
    (q : I → Ω → ℝ) (V : Ω → ℝ) {ε D : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hq : (∑ j, ∑ ω, q j ω) ≤ (Fintype.card I : ℝ) * Fintype.card Ω * ε)
    (hbarrier : ∀ j ω, 2 * ε * D ≤ D * q j ω + 4 * ε * V ω) :
    (Fintype.card Ω : ℝ) * D / 4 ≤ ∑ ω, V ω := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hbarrier j ω))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_left hq hD
  have hi : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hmain : (Fintype.card I : ℝ) * ε *
      ((Fintype.card Ω : ℝ) * D - 4 * ∑ ω, V ω) ≤ 0 := by nlinarith
  by_contra h
  have hp : 0 < (Fintype.card Ω : ℝ) * D - 4 * ∑ ω, V ω := by linarith
  exact (not_lt_of_ge hmain) (mul_pos (mul_pos hi hε) hp)

lemma cost_dichotomy {R L Δ ε V S : ℝ} {B T : ℕ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hB : 0 < B)
    (hS : L / 2 * S ≤ ε * (T + 1))
    (hV : Δ / (16 * ε) ≤ V)
    (htravel : 32 * B * T ^ 2 / R ≤ (1 / 2 : ℝ) →
      V ≤ 4 * (32 * B * T ^ 2 / R) * S) :
    R ≤ 64 * (B * (T + 1) : ℝ) ^ 2 ∨
      R * L * Δ ≤ 4096 * ε ^ 2 * (B * (T + 1) : ℝ) ^ 3 := by
  have hB₁ : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hT : (0 : ℝ) ≤ T := by positivity
  have hT₁ : (T : ℝ) ≤ T + 1 := by linarith
  by_cases hk : 32 * B * T ^ 2 / R ≤ (1 / 2 : ℝ)
  · right
    have hv := htravel hk
    have hlow : Δ ≤ 16 * ε * V := by
      have := (div_le_iff₀ (show 0 < 16 * ε by positivity)).mp hV
      nlinarith
    have hv' : R * V ≤ 128 * B * T ^ 2 * S := by
      have := mul_le_mul_of_nonneg_left hv hR.le
      field_simp at this
      nlinarith
    have h₁ := mul_le_mul_of_nonneg_left hv' (show 0 ≤ 16 * ε * L by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ R * L by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hS (show 0 ≤ 4096 * ε * B * T ^ 2 by positivity)
    have hraw : R * L * Δ ≤ 4096 * ε ^ 2 * B * T ^ 2 * (T + 1) := by nlinarith
    have hpow : (B : ℝ) * T ^ 2 * (T + 1) ≤ (B * (T + 1) : ℝ) ^ 3 := by
      have hb : (B : ℝ) ≤ (B : ℝ) ^ 3 := by nlinarith [sq_nonneg ((B : ℝ) - 1)]
      have ht := pow_le_pow_left₀ hT hT₁ 2
      calc
        _ ≤ (B : ℝ) * (T + 1) ^ 2 * (T + 1) := by gcongr
        _ = (B : ℝ) * (T + 1) ^ 3 := by ring
        _ ≤ (B : ℝ) ^ 3 * (T + 1) ^ 3 := by gcongr
        _ = _ := by ring
    exact hraw.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4096 * ε ^ 2 by positivity)])
  · left
    have hk' : R < 64 * B * T ^ 2 := by
      have := (lt_div_iff₀ hR).mp (lt_of_not_ge hk)
      linarith
    have hpow : (B : ℝ) * T ^ 2 ≤ (B * (T + 1) : ℝ) ^ 2 := by
      have hb : (B : ℝ) ≤ (B : ℝ) ^ 2 := by nlinarith
      calc
        _ ≤ (B : ℝ) ^ 2 * (T + 1) ^ 2 := by gcongr
        _ = _ := by ring
    nlinarith

end LongTails.Proofs.AdamTravelBound
