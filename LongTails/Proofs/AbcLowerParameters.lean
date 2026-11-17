import LongTails.Proofs.AbcLowerMeasure
import LongTails.Setups.HighDimensionalAbcNoiseNonconvex

open scoped BigOperators

namespace LongTails.Proofs.AbcLowerParameters

open LongTails.Proofs.AbcHardOracle
open LongTails.Setups.HighDimensionalAbcNoiseNonconvex

noncomputable def lowerBudget (q : Params) : ℕ :=
  ⌊q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / (2 ^ 53 * q.ε ^ 2)⌋₊

noncomputable def amplitude (q : Params) : ℝ := 3686400 * q.ε ^ 2 / q.L

noncomputable def stepScale (q : Params) : ℝ := 61440 * q.ε / q.L

noncomputable def scaleOf (q : Params) (hL : 0 < q.L) (hε : 0 < q.ε) : Scale :=
  ⟨amplitude q, stepScale q, by unfold amplitude; positivity, by unfold stepScale; positivity⟩

noncomputable def chainLength (q : Params) : ℕ := ⌊q.L * q.Δ / (11059200 * q.ε ^ 2)⌋₊

noncomputable def secretScale (q : Params) : ℝ := 1740 ^ 2 * q.ε ^ 2

noncomputable def levelBudget (q : Params) (n m : ℕ) : ℝ :=
  6 * q.A * amplitude q * ((n : ℝ) - m) + 9 * q.B * q.ε ^ 2 + q.C

noncomputable def revealProb (q : Params) (n m : ℕ) : ℝ :=
  secretScale q / max (secretScale q) (levelBudget q n m)

noncomputable def halfBudget (q : Params) : ℝ :=
  q.A * q.Δ / 3 + 9 * q.B * q.ε ^ 2 + q.C

noncomputable def revealBar (q : Params) : ℝ :=
  secretScale q / max (secretScale q) (halfBudget q)

lemma amplitude_ratio (q : Params) (hL : 0 < q.L) (hε : 0 < q.ε) :
    amplitude q / stepScale q = 60 * q.ε := by
  unfold amplitude stepScale; field_simp; try ring

lemma smoothness_eq (q : Params) (hL : 0 < q.L) (hε : 0 < q.ε) :
    1024 * amplitude q / stepScale q ^ 2 = q.L := by
  unfold amplitude stepScale; field_simp; try ring

lemma secretScale_pos (q : Params) (hε : 0 < q.ε) : 0 < secretScale q := by
  unfold secretScale; positivity

lemma revealProb_pos (q : Params) (hε : 0 < q.ε) (n m : ℕ) : 0 < revealProb q n m := by
  unfold revealProb
  exact div_pos (secretScale_pos q hε) (lt_max_of_lt_left (secretScale_pos q hε))

lemma revealProb_le (q : Params) (hε : 0 < q.ε) (n m : ℕ) : revealProb q n m ≤ 1 := by
  unfold revealProb
  rw [div_le_one (lt_max_of_lt_left (secretScale_pos q hε))]
  exact le_max_left _ _

lemma revealBar_nonneg (q : Params) (hε : 0 < q.ε) : 0 ≤ revealBar q := by
  unfold revealBar
  exact (div_pos (secretScale_pos q hε) (lt_max_of_lt_left (secretScale_pos q hε))).le

lemma revealBar_le (q : Params) (hε : 0 < q.ε) : revealBar q ≤ 1 := by
  unfold revealBar
  rw [div_le_one (lt_max_of_lt_left (secretScale_pos q hε))]
  exact le_max_left _ _

lemma variance_le_budget (q : Params) (hε : 0 < q.ε) (n m : ℕ) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s ≤ 1740 * q.ε) (hb : 0 ≤ levelBudget q n m) :
    (1 / revealProb q n m - 1) * s ^ 2 ≤ levelBudget q n m := by
  have hc := secretScale_pos q hε
  have hmax : 0 < max (secretScale q) (levelBudget q n m) := lt_max_of_lt_left hc
  have hinv : 1 / revealProb q n m = max (secretScale q) (levelBudget q n m) / secretScale q := by
    unfold revealProb; field_simp
  rw [hinv]
  have hs2 : s ^ 2 ≤ secretScale q := by
    unfold secretScale; nlinarith
  have hge : 0 ≤ max (secretScale q) (levelBudget q n m) / secretScale q - 1 := by
    rw [sub_nonneg, le_div_iff₀ hc, one_mul]; exact le_max_left _ _
  calc _ ≤ (max (secretScale q) (levelBudget q n m) / secretScale q - 1) * secretScale q :=
        mul_le_mul_of_nonneg_left hs2 hge
    _ = max (secretScale q) (levelBudget q n m) - secretScale q := by field_simp
    _ ≤ levelBudget q n m := by
        rcases le_total (secretScale q) (levelBudget q n m) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith

lemma revealProb_le_bar (q : Params) (hε : 0 < q.ε) (n m : ℕ)
    (hb : halfBudget q ≤ levelBudget q n m) : revealProb q n m ≤ revealBar q := by
  unfold revealProb revealBar
  apply div_le_div_of_nonneg_left (secretScale_pos q hε).le (lt_max_of_lt_left (secretScale_pos q hε))
  exact max_le_max le_rfl hb


section Regime

variable (q : Params) (hv : spec.valid q)
include hv

lemma ratio_ge : 6 ≤ q.L * q.Δ / (11059200 * q.ε ^ 2) := by
  obtain ⟨hL, _, _, _, hε, hreg, _⟩ := hv
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg q.ε]

lemma chainLength_ge : 6 ≤ chainLength q := by
  unfold chainLength
  exact Nat.le_floor (by exact_mod_cast ratio_ge q hv)

lemma chainLength_le : (chainLength q : ℝ) ≤ q.L * q.Δ / (11059200 * q.ε ^ 2) :=
  Nat.floor_le (by linarith [ratio_ge q hv])

lemma chainLength_lower : q.L * q.Δ / (22118400 * q.ε ^ 2) ≤ chainLength q := by
  have h := ratio_ge q hv
  have hf := Nat.lt_floor_add_one (q.L * q.Δ / (11059200 * q.ε ^ 2))
  unfold chainLength
  obtain ⟨hL, _, _, _, hε, _, _⟩ := hv
  have he : q.L * q.Δ / (22118400 * q.ε ^ 2) = (q.L * q.Δ / (11059200 * q.ε ^ 2)) / 2 := by
    field_simp; try ring
  rw [he]
  linarith

lemma amplitude_chain_le : 3 * amplitude q * chainLength q ≤ q.Δ := by
  have h := chainLength_le q hv
  obtain ⟨hL, _, _, _, hε, _, _⟩ := hv
  have ha : 0 ≤ amplitude q := by unfold amplitude; positivity
  have hm := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 3 * amplitude q)
  have he : 3 * amplitude q * (q.L * q.Δ / (11059200 * q.ε ^ 2)) = q.Δ := by
    unfold amplitude; field_simp; try ring
  linarith

lemma amplitude_chain_ge : q.Δ / 6 ≤ amplitude q * chainLength q := by
  have h := chainLength_lower q hv
  obtain ⟨hL, _, _, _, hε, _, _⟩ := hv
  have ha : 0 ≤ amplitude q := by unfold amplitude; positivity
  have hm := mul_le_mul_of_nonneg_left h ha
  have he : amplitude q * (q.L * q.Δ / (22118400 * q.ε ^ 2)) = q.Δ / 6 := by
    unfold amplitude; field_simp; try ring
  linarith

lemma half_le_level (m : ℕ) (hm : m ≤ (chainLength q - 1) / 2) :
    halfBudget q ≤ levelBudget q (chainLength q - 1) m := by
  have hT := chainLength_ge q hv
  have hg := amplitude_chain_ge q hv
  obtain ⟨hL, hA, _, _, hε, _, _⟩ := hv
  have hn : (chainLength q : ℝ) / 3 ≤ ((chainLength q - 1 : ℕ) : ℝ) - m := by
    have h2 : 2 * ((chainLength q - 1) / 2) ≤ chainLength q - 1 := Nat.mul_div_le _ _
    have h3 : 3 * m + chainLength q ≤ 3 * (chainLength q - 1) := by omega
    have h4 : ((3 * m + chainLength q : ℕ) : ℝ) ≤ ((3 * (chainLength q - 1) : ℕ) : ℝ) := by
      exact_mod_cast h3
    push_cast at h4
    linarith
  have ha : 0 ≤ amplitude q := by unfold amplitude; positivity
  unfold halfBudget levelBudget
  have hA' : q.A * q.Δ / 3 ≤ 6 * q.A * amplitude q * (((chainLength q - 1 : ℕ) : ℝ) - m) := by
    have h5 := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 6 * q.A * amplitude q)
    have h6 := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 2 * q.A)
    nlinarith
  linarith

lemma regime_size_nonneg : 0 ≤ 1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2 := by
  obtain ⟨hL, hA, hB, hC, hε, hreg, _⟩ := hv
  have hΔ : 0 ≤ q.Δ := by nlinarith [sq_nonneg q.ε]
  positivity

lemma budget_reveal (N : ℕ) (hN : N ≤ lowerBudget q) :
    (N : ℝ) * revealBar q / (((chainLength q - 1) / 2 + 1 : ℕ) : ℝ) ≤ 1 / 8 := by
  have hT := chainLength_ge q hv
  have hlow := chainLength_lower q hv
  have hX := regime_size_nonneg q hv
  obtain ⟨hL, hA, hB, hC, hε, hreg, _⟩ := hv
  have hΔ : 0 ≤ q.Δ := by nlinarith [sq_nonneg q.ε]
  set T := chainLength q
  set Mh := (T - 1) / 2
  have hM : (T : ℝ) ≤ 2 * ((Mh + 1 : ℕ) : ℝ) := by
    have : T ≤ 2 * (Mh + 1) := by omega
    exact_mod_cast this
  have hc := secretScale_pos q hε
  have hh : 0 ≤ halfBudget q := by unfold halfBudget; positivity
  have hbar : revealBar q ≤ 2 * secretScale q / (secretScale q + halfBudget q) := by
    unfold revealBar
    rw [div_le_div_iff₀ (lt_max_of_lt_left hc) (by positivity)]
    have hm1 : secretScale q ≤ max (secretScale q) (halfBudget q) := le_max_left _ _
    have hm2 : halfBudget q ≤ max (secretScale q) (halfBudget q) := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hm1 hc.le, mul_le_mul_of_nonneg_left hm2 hc.le]
  have hNr : (N : ℝ) ≤ q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) /
      (2 ^ 53 * q.ε ^ 2) :=
    (Nat.cast_le.mpr hN).trans (Nat.floor_le (by positivity))
  have hsum : secretScale q * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / 9082800 ≤
      secretScale q + halfBudget q := by
    unfold secretScale halfBudget
    have he : 1740 ^ 2 * q.ε ^ 2 * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / 9082800 =
        (q.ε ^ 2 + q.B * q.ε ^ 2 + q.A * q.Δ + q.C) / 3 := by field_simp; try ring
    rw [he]
    nlinarith [sq_nonneg q.ε]
  have hpos : 0 < (((Mh + 1 : ℕ) : ℝ)) := by positivity
  rw [div_le_iff₀ hpos]
  have key : (N : ℝ) * (2 * secretScale q / (secretScale q + halfBudget q)) ≤
      (T : ℝ) / 16 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have h1 : (N : ℝ) * 2 * secretScale q ≤ 2 * secretScale q * (q.L * q.Δ *
        (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / (2 ^ 53 * q.ε ^ 2)) := by nlinarith
    have h2 : 2 * secretScale q * (q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) /
        (2 ^ 53 * q.ε ^ 2)) ≤ (q.L * q.Δ / (22118400 * q.ε ^ 2)) / 16 *
        (secretScale q * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / 9082800) := by
      have hk : 0 ≤ secretScale q * (q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2)) :=
        by positivity
      have he1 : 2 * secretScale q * (q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) /
          (2 ^ 53 * q.ε ^ 2)) = secretScale q * (q.L * q.Δ *
          (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2)) / q.ε ^ 2 * (2 / 2 ^ 53) := by
        field_simp
      have he2 : (q.L * q.Δ / (22118400 * q.ε ^ 2)) / 16 *
          (secretScale q * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / 9082800) =
          secretScale q * (q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2)) / q.ε ^ 2 *
          (1 / (22118400 * 16 * 9082800)) := by
        field_simp
      rw [he1, he2]
      apply mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    have h3 : (q.L * q.Δ / (22118400 * q.ε ^ 2)) / 16 *
        (secretScale q * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / 9082800) ≤
        (T : ℝ) / 16 * (secretScale q + halfBudget q) := by
      apply mul_le_mul (by linarith) hsum (by positivity) (by positivity)
    nlinarith
  have hb2 := mul_le_mul_of_nonneg_left hbar (Nat.cast_nonneg N)
  nlinarith

lemma dimension_room (N : ℕ) (hN : N ≤ lowerBudget q) :
    (chainLength q : ℝ) + 2 ^ 31 * ((N : ℝ) + 1) * (chainLength q : ℝ) ^ 3 ≤ q.d := by
  have hT := chainLength_le q hv
  have hX := regime_size_nonneg q hv
  obtain ⟨hL, hA, hB, hC, hε, hreg, hd⟩ := hv
  have hΔ : 0 ≤ q.Δ := by nlinarith [sq_nonneg q.ε]
  set X := 1 + q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / q.ε ^ 2
  have hX1 : 1 ≤ X := by
    have : 0 ≤ q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / q.ε ^ 2 := by
      positivity
    linarith
  have hTX : (chainLength q : ℝ) ≤ X := by
    refine hT.trans ?_
    have h1 : q.L * q.Δ / (11059200 * q.ε ^ 2) ≤ q.L * q.Δ / q.ε ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_nonneg q.ε]
    have h2 : q.L * q.Δ / q.ε ^ 2 ≤ q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) /
        q.ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 1 ≤ 1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2 := by
        have : 0 ≤ q.A * q.Δ / q.ε ^ 2 := by positivity
        have : 0 ≤ q.C / q.ε ^ 2 := by positivity
        linarith
      nlinarith [mul_nonneg hL.le hΔ]
    linarith
  have hNX : (N : ℝ) ≤ X := by
    have hNr : (N : ℝ) ≤ q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) /
        (2 ^ 53 * q.ε ^ 2) := (Nat.cast_le.mpr hN).trans (Nat.floor_le (by positivity))
    have : q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / (2 ^ 53 * q.ε ^ 2) ≤
        q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / q.ε ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_nonneg q.ε]
    linarith
  have hT0 : (0 : ℝ) ≤ chainLength q := Nat.cast_nonneg _
  have h3 : (chainLength q : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hT0 hTX 3
  have hX3 : 0 ≤ X ^ 3 := by positivity
  calc _ ≤ X + 2 ^ 31 * (2 * X) * X ^ 3 := by
        gcongr
        linarith
    _ ≤ 2 ^ 40 * X ^ 4 := by nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1) hX1 3]
    _ ≤ q.d := hd

end Regime

end LongTails.Proofs.AbcLowerParameters
