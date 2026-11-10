import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.ParameterFreeNsgdmGrid

noncomputable def runRate (L Δ σ p T α η : ℝ) : ℝ :=
  Δ / (η * T) + 3 * L * η / α + 12 * σ / (α * T) + 12 * σ * α ^ ((p - 1) / p)

noncomputable def optMomentum (L Δ σ p T : ℝ) : ℝ :=
  if σ = 0 then 1 else min 1 (max (1 / T) ((L * Δ / (σ ^ 2 * T)) ^ (p / (3 * p - 2))))

noncomputable def optStep (L Δ σ p T : ℝ) : ℝ :=
  Real.sqrt (Δ * optMomentum L Δ σ p T / (3 * L * T))

noncomputable def tunedRate (L Δ σ p T : ℝ) : ℝ :=
  Real.exp (1 / 2) * (2 * Real.sqrt (3 * L * Δ / (optMomentum L Δ σ p T * T))) +
    12 * Real.exp (1 / 4) * σ * optMomentum L Δ σ p T ^ ((p - 1) / p) +
    12 * σ / (optMomentum L Δ σ p T * T)

lemma optMomentum_pos {L Δ σ p T : ℝ} (hT : 0 < T) :
    0 < optMomentum L Δ σ p T := by
  unfold optMomentum
  split_ifs
  · exact one_pos
  · exact lt_min one_pos (lt_max_of_lt_left (by positivity))

lemma optMomentum_le_one {L Δ σ p T : ℝ} : optMomentum L Δ σ p T ≤ 1 := by
  unfold optMomentum
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma inv_le_optMomentum {L Δ σ p T : ℝ} (hT : 1 ≤ T) : 1 / T ≤ optMomentum L Δ σ p T := by
  unfold optMomentum
  split_ifs
  · exact (div_le_one (by linarith)).mpr hT
  · exact le_min ((div_le_one (by linarith)).mpr hT) (le_max_left _ _)

lemma runRate_mono {L Δ σ p T α η αs ηs : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hT : 0 < T) (hαs : 0 < αs) (hηs : 0 < ηs)
    (hα1 : αs ≤ α) (hα2 : α ≤ Real.exp (1 / 2) * αs) (hη1 : ηs ≤ η) (hη2 : η ≤ Real.exp (1 / 2) * ηs) :
    runRate L Δ σ p T α η ≤
      Real.exp (1 / 2) * (Δ / (ηs * T) + 3 * L * ηs / αs) +
        12 * Real.exp (1 / 4) * σ * αs ^ ((p - 1) / p) + 12 * σ / (αs * T) := by
  unfold runRate
  have hα0 : 0 < α := lt_of_lt_of_le hαs hα1
  have he : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
  have h1 : Δ / (η * T) ≤ Δ / (ηs * T) := by
    apply div_le_div_of_nonneg_left hΔ.le (by positivity)
    exact mul_le_mul_of_nonneg_right hη1 hT.le
  have h1' : Δ / (ηs * T) ≤ Real.exp (1 / 2) * (Δ / (ηs * T)) :=
    le_mul_of_one_le_left (by positivity) he
  have h2 : 3 * L * η / α ≤ Real.exp (1 / 2) * (3 * L * ηs / αs) := by
    rw [mul_div_assoc', ← mul_assoc]
    apply div_le_div₀ (by positivity) _ hαs hα1
    calc 3 * L * η ≤ 3 * L * (Real.exp (1 / 2) * ηs) := by gcongr
      _ = Real.exp (1 / 2) * (3 * L) * ηs := by ring
  have h3 : 12 * σ / (α * T) ≤ 12 * σ / (αs * T) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hα1 hT.le
  have h4 : 12 * σ * α ^ ((p - 1) / p) ≤ 12 * Real.exp (1 / 4) * σ * αs ^ ((p - 1) / p) := by
    have hq0 : 0 ≤ (p - 1) / p := by positivity
    have hq1 : (p - 1) / p ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith [hp2]
    calc 12 * σ * α ^ ((p - 1) / p) ≤ 12 * σ * (Real.exp (1 / 2) * αs) ^ ((p - 1) / p) := by
          gcongr
      _ = 12 * σ * (Real.exp (1 / 2) ^ ((p - 1) / p) * αs ^ ((p - 1) / p)) := by
          rw [Real.mul_rpow (Real.exp_pos _).le hαs.le]
      _ ≤ 12 * σ * (Real.exp (1 / 4) * αs ^ ((p - 1) / p)) := by
          gcongr
          rw [← Real.exp_mul]
          apply Real.exp_le_exp.mpr
          nlinarith
      _ = 12 * Real.exp (1 / 4) * σ * αs ^ ((p - 1) / p) := by ring
  linarith

lemma optStep_balance {L Δ σ p T : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hT : 0 < T) :
    Δ / (optStep L Δ σ p T * T) + 3 * L * optStep L Δ σ p T / optMomentum L Δ σ p T =
      2 * Real.sqrt (3 * L * Δ / (optMomentum L Δ σ p T * T)) := by
  have hα := optMomentum_pos (L := L) (Δ := Δ) (σ := σ) (p := p) hT
  set a := optMomentum L Δ σ p T with ha
  have hin : 0 < Δ * a / (3 * L * T) := by positivity
  unfold optStep
  rw [← ha]
  set s := Real.sqrt (Δ * a / (3 * L * T)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hin
  have hs2 : s ^ 2 = Δ * a / (3 * L * T) := Real.sq_sqrt hin.le
  have hgoal : Real.sqrt (3 * L * Δ / (a * T)) = 3 * L * s / a := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have : 3 * L * s / a * (3 * L * s / a) = 9 * L ^ 2 * s ^ 2 / a ^ 2 := by ring
    rw [this, hs2]
    field_simp
    ring
  rw [hgoal]
  have h1 : Δ / (s * T) = 3 * L * s / a := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have : 3 * L * s * (s * T) = 3 * L * T * s ^ 2 := by ring
    rw [this, hs2]
    field_simp
    try ring
  rw [h1]
  try ring

lemma exists_momentum_index {a : ℝ} {k : ℕ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hlow : 1 / (2 : ℝ) ^ k ≤ a) :
    ∃ i : ℕ, i ≤ 2 * k ∧ a ≤ Real.exp (-(i : ℝ) / 2) ∧ Real.exp (-(i : ℝ) / 2) ≤ Real.exp (1 / 2) * a := by
  have hlog : 0 ≤ -2 * Real.log a := by
    have := Real.log_nonpos ha0.le ha1
    linarith
  refine ⟨⌊-2 * Real.log a⌋₊, ?_, ?_, ?_⟩
  · have h1 : Real.log a ≥ -(k : ℝ) * Real.log 2 := by
      have := Real.log_le_log (by positivity) hlow
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow] at this
      linarith
    have h2 : (⌊-2 * Real.log a⌋₊ : ℝ) ≤ -2 * Real.log a := Nat.floor_le hlog
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have h4 : (⌊-2 * Real.log a⌋₊ : ℝ) ≤ 2 * k := by
      nlinarith
    exact_mod_cast h4
  · have := Nat.floor_le hlog
    calc a = Real.exp (Real.log a) := (Real.exp_log ha0).symm
      _ ≤ Real.exp (-(⌊-2 * Real.log a⌋₊ : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
  · have := Nat.lt_floor_add_one (-2 * Real.log a)
    calc Real.exp (-(⌊-2 * Real.log a⌋₊ : ℝ) / 2) ≤ Real.exp (1 / 2 + Real.log a) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (1 / 2) * a := by rw [Real.exp_add, Real.exp_log ha0]

lemma exists_step_index {s : ℝ} {k : ℕ} (hs0 : 0 < s)
    (hlow : 1 / ((2 : ℝ) ^ k) ^ 2 ≤ s) (hhigh : s ≤ (2 : ℝ) ^ k) :
    ∃ j : ℕ, j ≤ 5 * k ∧ s ≤ Real.exp ((k : ℝ) - (j : ℝ) / 2) ∧
      Real.exp ((k : ℝ) - (j : ℝ) / 2) ≤ Real.exp (1 / 2) * s := by
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl2' : (3 : ℝ) / 4 ≤ 1 := by norm_num
  have hlog_hi : Real.log s ≤ k := by
    have := Real.log_le_log hs0 hhigh
    rw [Real.log_pow] at this
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hlog_lo : -(2 * k) * Real.log 2 ≤ Real.log s := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have harg : 0 ≤ 2 * ((k : ℝ) - Real.log s) := by linarith
  refine ⟨⌊2 * ((k : ℝ) - Real.log s)⌋₊, ?_, ?_, ?_⟩
  · have h2 : (⌊2 * ((k : ℝ) - Real.log s)⌋₊ : ℝ) ≤ 2 * ((k : ℝ) - Real.log s) := Nat.floor_le harg
    have hl2'' : 4 * Real.log 2 ≤ 3 := by
      have h := Real.add_one_le_exp (3 / 4 : ℝ)
      have h' : (2 : ℝ) ≤ Real.exp (3 / 4) := by
        have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
        norm_num at this
        linarith
      have := Real.log_le_log (by norm_num) h'
      rw [Real.log_exp] at this
      linarith
    have h4 : (⌊2 * ((k : ℝ) - Real.log s)⌋₊ : ℝ) ≤ 5 * k := by nlinarith
    exact_mod_cast h4
  · have := Nat.floor_le harg
    calc s = Real.exp (Real.log s) := (Real.exp_log hs0).symm
      _ ≤ Real.exp ((k : ℝ) - (⌊2 * ((k : ℝ) - Real.log s)⌋₊ : ℝ) / 2) :=
          Real.exp_le_exp.mpr (by linarith)
  · have := Nat.lt_floor_add_one (2 * ((k : ℝ) - Real.log s))
    calc Real.exp ((k : ℝ) - (⌊2 * ((k : ℝ) - Real.log s)⌋₊ : ℝ) / 2) ≤ Real.exp (1 / 2 + Real.log s) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (1 / 2) * s := by rw [Real.exp_add, Real.exp_log hs0]

lemma exists_grid_run {L Δ σ p : ℝ} {k : ℕ} (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hp : 1 < p)
    (hp2 : p ≤ 2) (hlow : 1 / ((2 : ℝ) ^ k) ^ 2 ≤ optStep L Δ σ p (2 ^ k))
    (hhigh : optStep L Δ σ p (2 ^ k) ≤ (2 : ℝ) ^ k) :
    ∃ i j : ℕ, i ≤ 2 * k ∧ j ≤ 5 * k ∧
      runRate L Δ σ p (2 ^ k) (Real.exp (-(i : ℝ) / 2)) (Real.exp ((k : ℝ) - (j : ℝ) / 2)) ≤
        tunedRate L Δ σ p (2 ^ k) := by
  have hT : (0 : ℝ) < 2 ^ k := by positivity
  have hT1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hα := optMomentum_pos (L := L) (Δ := Δ) (σ := σ) (p := p) hT
  have hs : 0 < optStep L Δ σ p (2 ^ k) := by
    unfold optStep; exact Real.sqrt_pos.mpr (by positivity)
  obtain ⟨i, hi, hai, hai'⟩ := exists_momentum_index hα optMomentum_le_one
    (inv_le_optMomentum (L := L) (Δ := Δ) (σ := σ) (p := p) hT1)
  obtain ⟨j, hj, hsj, hsj'⟩ := exists_step_index hs hlow hhigh
  refine ⟨i, j, hi, hj, ?_⟩
  have hmono := runRate_mono hL hΔ hσ hp hp2 hT hα hs hai hai' hsj hsj'
  rw [optStep_balance hL hΔ hT] at hmono
  unfold tunedRate
  linarith

end LongTails.Proofs.ParameterFreeNsgdmGrid
