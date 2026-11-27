import LongTails.Proofs.SlidingLowerCorners

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SlidingLowerScaling

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingLowerHiding SlidingLowerAdmissible SlidingLowerFailure SlidingLowerCorners

noncomputable def chainLength (q : Params) : ℕ := ⌊q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 20⌋₊

noncomputable def coinProb (q : Params) : ℝ :=
  if q.σ ^ 2 ≤ 2 ^ 17 * q.ε ^ 2 then 1 else 2 ^ 17 * q.ε ^ 2 / q.σ ^ 2

noncomputable def scale (q : Params) : Scale :=
  ⟨coinProb q, 10 * q.ε * (22000 * q.ε / q.ℓ), 22000 * q.ε / q.ℓ,
    5280 * (1 + Real.sqrt (chainLength q))⟩

lemma valid_facts (q : Params) (hq : spec.valid q) :
    0 < q.ℓ ∧ q.ℓ ≤ q.L ∧ 0 ≤ q.σ ∧ 0 < q.ε ∧ 2 ^ 62 ≤ q.ℓ * q.Δ / q.ε ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hq
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  linarith

lemma coinProb_bounds (q : Params) (hε : 0 < q.ε) :
    0 < coinProb q ∧ coinProb q ≤ 1 := by
  unfold coinProb
  split_ifs with h
  · exact ⟨one_pos, le_rfl⟩
  · push Not at h
    have hσ : 0 < q.σ ^ 2 := lt_of_le_of_lt (by positivity) h
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hσ]
    exact h.le

lemma chainLength_bounds (q : Params) (hX : 2 ^ 62 ≤ q.ℓ * q.Δ / q.ε ^ 2) :
    (chainLength q : ℝ) ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 20 ∧
      q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 21 ≤ chainLength q := by
  have h0 : 0 ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 20 := by
    apply div_nonneg _ (by norm_num); linarith
  refine ⟨Nat.floor_le h0, ?_⟩
  have h1 := Nat.sub_one_lt_floor (q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 20)
  unfold chainLength
  have : q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 21 ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 20 - 1 := by
    have : (2 : ℝ) ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 21 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    have e : q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 20 = 2 * (q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 21) := by ring
    linarith
  linarith

lemma scale_valid (q : Params) (hq : spec.valid q) :
    Valid q (chainLength q) (scale q) := by
  obtain ⟨hℓ, hL, hσ, hε, hX⟩ := valid_facts q hq
  have hp := coinProb_bounds q hε
  have hT := chainLength_bounds q hX
  refine ⟨hp.1, hp.2, by simp only [scale]; positivity, by simp only [scale]; positivity, le_rfl,
    ?_, hL, ?_, ?_⟩
  · simp only [scale]
    field_simp
    ring
  · simp only [scale]
    have hXe : q.ℓ * q.Δ / q.ε ^ 2 * q.ε ^ 2 = q.ℓ * q.Δ := by field_simp
    have hT1 := hT.1
    have key : 4 * 220000 * (1 + q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 20) ≤ q.ℓ * q.Δ / q.ε ^ 2 := by
      nlinarith
    have e : 10 * q.ε * (22000 * q.ε / q.ℓ) * (4 + 4 * (chainLength q : ℝ)) =
        4 * 220000 * (1 + chainLength q) * q.ε ^ 2 / q.ℓ := by field_simp; ring
    rw [e, div_le_iff₀ hℓ]
    have h2 : 4 * 220000 * (1 + (chainLength q : ℝ)) * q.ε ^ 2 ≤
        q.ℓ * q.Δ / q.ε ^ 2 * q.ε ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    rw [hXe] at h2
    linarith
  · simp only [scale]
    have e : 10 * q.ε * (22000 * q.ε / q.ℓ) / (22000 * q.ε / q.ℓ) = 10 * q.ε := by
      field_simp
    rw [e]
    unfold coinProb
    split_ifs with h
    · simp
      positivity
    · push Not at h
      have hσ2 : 0 < q.σ ^ 2 := lt_of_le_of_lt (by positivity) h
      rw [one_div, inv_div]
      have : q.σ ^ 2 / (2 ^ 17 * q.ε ^ 2) - 1 ≤ q.σ ^ 2 / (2 ^ 17 * q.ε ^ 2) := by linarith
      have h3 : 576 * (10 * q.ε) ^ 2 * (q.σ ^ 2 / (2 ^ 17 * q.ε ^ 2)) ≤ q.σ ^ 2 := by
        field_simp
        nlinarith [sq_nonneg q.σ, sq_nonneg q.ε]
      have h4 : 0 ≤ 576 * (10 * q.ε) ^ 2 := by positivity
      nlinarith

lemma cmin_bound (q : Params) (hq : spec.valid q) :
    q.ε ^ 2 / (8 * q.ℓ) < (5 / 8) * cmin q (scale q) := by
  obtain ⟨hℓ, _, _, hε, _⟩ := valid_facts q hq
  unfold cmin
  simp only [scale]
  have e1 : (10 * q.ε * (22000 * q.ε / q.ℓ) / (22000 * q.ε / q.ℓ)) ^ 2 / (288 * q.ℓ) =
      100 * q.ε ^ 2 / (288 * q.ℓ) := by field_simp; ring
  have e2 : 49 * q.ℓ * (22000 * q.ε / q.ℓ) ^ 2 / 512 = 49 * 22000 ^ 2 * q.ε ^ 2 / (512 * q.ℓ) := by
    field_simp
  rw [e1, e2]
  have h1 : 100 * q.ε ^ 2 / (288 * q.ℓ) ≤ 49 * 22000 ^ 2 * q.ε ^ 2 / (512 * q.ℓ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg q.ε]
  rw [min_eq_left h1]
  rw [div_lt_iff₀ (by positivity)]
  have : (5 / 8) * (100 * q.ε ^ 2 / (288 * q.ℓ)) * (8 * q.ℓ) = 500 / 288 * q.ε ^ 2 := by
    field_simp; ring
  rw [this]
  nlinarith [sq_pos_of_pos hε]

end LongTails.Proofs.SlidingLowerScaling
