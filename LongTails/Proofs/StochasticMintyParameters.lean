import LongTails.Setups.HighDimensionalStochasticWeakMinty
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.StochasticMintyParameters

open LongTails.Setups.HighDimensionalStochasticWeakMinty

noncomputable def ratio (q : Params) : ℝ := (q.L * q.R / (28 * q.ε)) ^ 2

noncomputable def links (q : Params) : ℕ := ⌊ratio q⌋₊

noncomputable def chainDim (q : Params) : ℕ := links q - 1

noncomputable def strength (q : Params) : ℝ := q.L / 6

noncomputable def width (q : Params) : ℝ := 28 * q.ε / q.L

noncomputable def wall (q : Params) : ℝ := 2 * width q * Real.sqrt (links q)

noncomputable def revealBar (q : Params) : ℝ := 1 / (1 + 9 * q.σ ^ 2 / (196 * q.ε ^ 2))

noncomputable def lowerBudget (q : Params) : ℕ :=
  ⌊q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * q.ε ^ 4)⌋₊

lemma wall_sq (q : Params) : wall q ^ 2 = 4 * (links q : ℝ) * width q ^ 2 := by
  unfold wall
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

section Valid

variable (q : Params) (hv : spec.valid q)
include hv

lemma pos_L : 0 < q.L := hv.1.1

lemma pos_ε : 0 < q.ε := hv.1.2.2.2.2.2

lemma pos_R : 0 < q.R := by
  have hL := pos_L q hv
  have hε := pos_ε q hv
  have h := hv.2.1
  have : 0 < q.L * q.R := by nlinarith
  exact pos_of_mul_pos_right this hL.le

lemma ratio_ge : 1336 ≤ ratio q := by
  have hL := pos_L q hv
  have hε := pos_ε q hv
  have h := hv.2.1
  have h1 : 2 ^ 10 / 28 ≤ q.L * q.R / (28 * q.ε) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : (2 ^ 10 / 28 : ℝ) ^ 2 ≤ (q.L * q.R / (28 * q.ε)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) h1 2
  unfold ratio
  nlinarith

lemma ratio_eq : ratio q = q.L ^ 2 * q.R ^ 2 / (784 * q.ε ^ 2) := by
  have hε := pos_ε q hv
  unfold ratio
  rw [div_pow, mul_pow, mul_pow]
  ring

lemma links_pos : 1 ≤ links q := by
  unfold links
  exact Nat.le_floor (by have := ratio_ge q hv; push_cast; linarith)

lemma chainDim_succ : chainDim q + 1 = links q := by
  have := links_pos q hv
  unfold chainDim
  omega

lemma links_le : (links q : ℝ) ≤ ratio q :=
  Nat.floor_le (by have := ratio_ge q hv; linarith)

lemma links_ge : ratio q / 2 ≤ links q := by
  have h := Nat.lt_floor_add_one (ratio q)
  have hr := ratio_ge q hv
  unfold links
  linarith

lemma width_pos : 0 < width q := by
  have hL := pos_L q hv
  have hε := pos_ε q hv
  unfold width
  positivity

lemma strength_pos : 0 < strength q := by
  have hL := pos_L q hv
  unfold strength
  positivity

lemma strength_width : strength q * width q = 14 * q.ε / 3 := by
  have hL := pos_L q hv
  unfold strength width
  field_simp
  ring

lemma wall_pos : 0 < wall q := by
  have hw := width_pos q hv
  have hk : (0 : ℝ) < links q := by exact_mod_cast links_pos q hv
  unfold wall
  positivity

lemma links_width : (links q : ℝ) * width q ^ 2 ≤ q.R ^ 2 := by
  have hL := pos_L q hv
  have hε := pos_ε q hv
  have h := links_le q hv
  have hw : width q ^ 2 * ratio q = q.R ^ 2 := by
    unfold width ratio
    field_simp
  have hw2 : 0 ≤ width q ^ 2 := sq_nonneg _
  nlinarith

lemma revealBar_pos : 0 < revealBar q := by
  have hε := pos_ε q hv
  unfold revealBar
  positivity

lemma revealBar_le : revealBar q ≤ 1 := by
  have hε := pos_ε q hv
  unfold revealBar
  rw [div_le_one (by positivity)]
  have : 0 ≤ 9 * q.σ ^ 2 / (196 * q.ε ^ 2) := by positivity
  linarith

lemma revealBar_variance :
    (1 / revealBar q - 1) * (strength q ^ 2 * width q ^ 2) = q.σ ^ 2 := by
  have hε := pos_ε q hv
  have h := strength_width q hv
  have e : strength q ^ 2 * width q ^ 2 = (strength q * width q) ^ 2 := by ring
  rw [e, h]
  unfold revealBar
  rw [one_div_one_div]
  field_simp
  ring

lemma floor_gap : 4 * q.ε ^ 2 ≤ 3 * strength q ^ 2 * width q ^ 2 / 16 := by
  have h := strength_width q hv
  have e : 3 * strength q ^ 2 * width q ^ 2 / 16 = 3 * (strength q * width q) ^ 2 / 16 := by ring
  rw [e, h]
  nlinarith [sq_nonneg q.ε]

lemma budget_le (N : ℕ) (hN : N ≤ lowerBudget q) :
    (N : ℝ) ≤ q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * q.ε ^ 4) := by
  have hε := pos_ε q hv
  have h0 : 0 ≤ q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * q.ε ^ 4) := by positivity
  exact (Nat.cast_le.mpr hN).trans (Nat.floor_le h0)

lemma reveal_tail (N : ℕ) (hN : N ≤ lowerBudget q) :
    (N : ℝ) * revealBar q / ((chainDim q : ℝ) + 1) ≤ 1 / 8 := by
  have hε := pos_ε q hv
  have hL := pos_L q hv
  have hNle := budget_le q hv N hN
  have hK := links_ge q hv
  rw [ratio_eq q hv] at hK
  have hc : ((chainDim q : ℝ) + 1) = links q := by
    rw [← chainDim_succ q hv]; push_cast; ring
  rw [hc]
  have hKpos : (0 : ℝ) < links q := by exact_mod_cast links_pos q hv
  rw [div_le_iff₀ hKpos]
  have he2 : 0 < q.ε ^ 2 := by positivity
  have hs2 : 0 ≤ q.σ ^ 2 := sq_nonneg _
  have ha : 0 ≤ q.L ^ 2 * q.R ^ 2 := by positivity
  have hden : 0 < 196 * q.ε ^ 2 + 9 * q.σ ^ 2 := by positivity
  have hrb : revealBar q = 196 * q.ε ^ 2 / (196 * q.ε ^ 2 + 9 * q.σ ^ 2) := by
    unfold revealBar
    field_simp
  have he4 : q.ε ^ 4 = (q.ε ^ 2) ^ 2 := by ring
  rw [he4] at hNle
  have hX : (N : ℝ) * (196 * q.ε ^ 2) ≤
      q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * (q.ε ^ 2) ^ 2) * (196 * q.ε ^ 2) :=
    mul_le_mul_of_nonneg_right hNle (by positivity)
  have hmain : q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * (q.ε ^ 2) ^ 2) *
      (196 * q.ε ^ 2) ≤
      1 / 8 * (q.L ^ 2 * q.R ^ 2 / (784 * q.ε ^ 2) / 2) * (196 * q.ε ^ 2 + 9 * q.σ ^ 2) := by
    have e1 : q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * (q.ε ^ 2) ^ 2) *
        (196 * q.ε ^ 2) = q.L ^ 2 * q.R ^ 2 * (196 * (q.ε ^ 2 + q.σ ^ 2)) / (2 ^ 19 * q.ε ^ 2) := by
      field_simp
    have e2 : 1 / 8 * (q.L ^ 2 * q.R ^ 2 / (784 * q.ε ^ 2) / 2) * (196 * q.ε ^ 2 + 9 * q.σ ^ 2) =
        q.L ^ 2 * q.R ^ 2 * (196 * q.ε ^ 2 + 9 * q.σ ^ 2) / (12544 * q.ε ^ 2) := by
      field_simp
      ring
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 196 * (q.ε ^ 2 + q.σ ^ 2) * 12544 ≤ (196 * q.ε ^ 2 + 9 * q.σ ^ 2) * 2 ^ 19 := by
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg ha he2.le)
    nlinarith
  rw [hrb, mul_div_assoc', div_le_iff₀ hden]
  have hK' : 1 / 8 * (q.L ^ 2 * q.R ^ 2 / (784 * q.ε ^ 2) / 2) * (196 * q.ε ^ 2 + 9 * q.σ ^ 2) ≤
      1 / 8 * (links q : ℝ) * (196 * q.ε ^ 2 + 9 * q.σ ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hden.le
    linarith
  nlinarith

lemma dimension_room (N : ℕ) (hN : N ≤ lowerBudget q) :
    8 * (((N + 1 : ℕ) : ℝ) * ((chainDim q + 1 : ℕ) : ℝ) * (64 * ((chainDim q + 1 : ℕ) : ℝ))) +
      ((chainDim q + 1 : ℕ) : ℝ) ≤ q.d := by
  have hε := pos_ε q hv
  have hL := pos_L q hv
  have hNle := budget_le q hv N hN
  have hd := hv.2.2
  have hK := links_le q hv
  have hT1 := ratio_ge q hv
  have hTe := ratio_eq q hv
  have hc : ((chainDim q + 1 : ℕ) : ℝ) = links q := by rw [chainDim_succ q hv]
  rw [hc]
  push_cast
  obtain ⟨T, hT⟩ : ∃ T, T = ratio q := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = (q.ε ^ 2 + q.σ ^ 2) / q.ε ^ 2 := ⟨_, rfl⟩
  rw [← hT] at hK hT1 hTe
  have hS1 : 1 ≤ S := by
    rw [hS, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg q.σ]
  have hX : q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * q.ε ^ 4) = 784 * T * S / 2 ^ 19 := by
    rw [hTe, hS]
    field_simp
  have hZ : q.L ^ 6 * q.R ^ 6 * (q.ε ^ 2 + q.σ ^ 2) = (784 * T) ^ 3 * S * q.ε ^ 8 := by
    rw [hTe, hS]
    field_simp
  rw [hX] at hNle
  have hdT : (784 * T) ^ 3 * S ≤ q.d := by
    have h8 : 0 < q.ε ^ 8 := by positivity
    rw [hZ] at hd
    nlinarith
  have hKpos : (0 : ℝ) ≤ links q := Nat.cast_nonneg _
  have hN1 : (N : ℝ) + 1 ≤ 2 * (784 * T * S / 2 ^ 19) := by
    have : 1 ≤ 784 * T * S / 2 ^ 19 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    linarith
  have hK2 : (links q : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hKpos hK 2
  have hprod : ((N : ℝ) + 1) * (links q : ℝ) ^ 2 ≤ 2 * (784 * T * S / 2 ^ 19) * T ^ 2 :=
    mul_le_mul hN1 hK2 (sq_nonneg _) (by positivity)
  have hT0 : 0 ≤ T := by linarith
  have hfin : 512 * (2 * (784 * T * S / 2 ^ 19) * T ^ 2) + T ≤ (784 * T) ^ 3 * S := by
    have hT3 : T ≤ T ^ 3 * S := by
      have : 1 ≤ T ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hS1 (by positivity : (0 : ℝ) ≤ T ^ 3)]
    nlinarith [pow_nonneg hT0 3, mul_nonneg (pow_nonneg hT0 3) (by linarith : (0 : ℝ) ≤ S)]
  nlinarith

end Valid

end LongTails.Proofs.StochasticMintyParameters
