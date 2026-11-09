import LongTails.Algorithms.QuasarCubicNewton

noncomputable section

namespace LongTails.Proofs.QuasarCubicTuning

open LongTails.Setups.QuasarConvexHessianLipschitz
open LongTails.Algorithms.QuasarCubicNewton
open LongTails.Proofs.QuasarCubicPotential

def ratio (p : Params) : ℝ := 8388608 * p.H * p.R ^ 3 / (p.γ ^ 4 * p.ε)

def radius (p : Params) : ℝ := 200 * p.R / p.γ

def gap (p : Params) : ℝ := 1 / 2 ^ depth p

def coupleError (p : Params) : ℝ :=
  1536 * p.H ^ 3 * radius p ^ 3 / (p.γ ^ 3 * reg p ^ 2)

def searchError (p : Params) : ℝ :=
  gap p * radius p ^ 2 * (p.L₀ / 2 + p.H * radius p) / p.γ

variable {p : Params}

lemma iterations_ge : ratio p ^ (3 / 8 : ℝ) ≤ iterations p := Nat.le_ceil _

lemma cbrt_cube : ((iterations p : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = iterations p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

lemma reg_eq : reg p = 270 * p.H * (iterations p : ℝ) ^ (1 / 3 : ℝ) / p.γ := rfl

lemma gap_pos : 0 < gap p := by unfold gap; positivity

lemma gap_le_one : gap p ≤ 1 := by
  unfold gap
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

lemma depth_bound : 27 * (ratio p + 1) ^ 2 * (p.L₀ / (p.H * p.R) + 32768) / p.γ ^ 2 <
    2 ^ depth p := by
  set m := ⌈27 * (ratio p + 1) ^ 2 * (p.L₀ / (p.H * p.R) + 32768) / p.γ ^ 2⌉₊
  have h1 : 27 * (ratio p + 1) ^ 2 * (p.L₀ / (p.H * p.R) + 32768) / p.γ ^ 2 ≤ m :=
    Nat.le_ceil _
  have h2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have h3 : (m : ℝ) < 2 ^ depth p := by
    unfold depth
    exact_mod_cast h2
  exact lt_of_le_of_lt h1 h3

lemma gap_mul_le : gap p * (27 * (ratio p + 1) ^ 2 * (p.L₀ / (p.H * p.R) + 32768) / p.γ ^ 2) ≤ 1 := by
  have h := depth_bound (p := p)
  unfold gap
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  exact h.le


section

variable (hp : spec.valid p)
include hp

lemma ratio_pos : 0 < ratio p := by
  obtain ⟨hH, hγ, -, hR, -, hε⟩ := id hp
  unfold ratio; positivity

lemma iterations_pos : 1 ≤ iterations p := by
  have := ratio_pos hp
  unfold iterations
  rw [Nat.one_le_ceil_iff]
  change 0 < ratio p ^ (3 / 8 : ℝ)
  positivity

lemma iterations_le : (iterations p : ℝ) ≤ ratio p ^ (3 / 8 : ℝ) + 1 :=
  (Nat.ceil_lt_add_one (by have := ratio_pos hp; positivity)).le

lemma cbrt_ge_one : 1 ≤ (iterations p : ℝ) ^ (1 / 3 : ℝ) :=
  Real.one_le_rpow (by exact_mod_cast iterations_pos hp) (by norm_num)

lemma reg_ge : 2 * p.H ≤ reg p := by
  obtain ⟨hH, hγ, hγ1, -, -, -⟩ := id hp
  have hk := cbrt_ge_one hp
  rw [reg_eq, le_div_iff₀ hγ]
  nlinarith

lemma reg_ge' : 270 * p.H / p.γ ≤ reg p := by
  obtain ⟨hH, hγ, hγ1, -, -, -⟩ := id hp
  have hk := cbrt_ge_one hp
  rw [reg_eq]
  apply div_le_div_of_nonneg_right _ hγ.le
  nlinarith

lemma reg_pos : 0 < reg p := by
  have := reg_ge hp; have := hp.1; linarith

lemma radius_ge : 200 * p.R ≤ radius p := by
  obtain ⟨-, hγ, hγ1, hR, -, -⟩ := id hp
  unfold radius
  rw [le_div_iff₀ hγ]
  nlinarith

lemma gap_small : gap p ≤ p.γ ^ 2 / 32768 := by
  obtain ⟨hH, hγ, hγ1, hR, hL, -⟩ := id hp
  have h := gap_mul_le (p := p)
  have hr := ratio_pos hp
  have hq : 32768 / p.γ ^ 2 ≤ 27 * (ratio p + 1) ^ 2 * (p.L₀ / (p.H * p.R) + 32768) / p.γ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 1 ≤ (ratio p + 1) ^ 2 := by nlinarith
    have : 0 ≤ p.L₀ / (p.H * p.R) := by positivity
    nlinarith
  have hg := gap_pos (p := p)
  have h2 : gap p * (32768 / p.γ ^ 2) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hq hg.le) h
  rw [le_div_iff₀ (by norm_num)]
  rw [mul_div_assoc'] at h2
  rw [div_le_one (by positivity)] at h2
  linarith

lemma gap_le_step : gap p ≤ p.γ * reg p * p.R ^ 2 / (48 * p.H * radius p ^ 2) := by
  obtain ⟨hH, hγ, hγ1, hR, hL, -⟩ := id hp
  have hg := gap_small hp
  have hM := reg_ge' hp
  have hrad : radius p ^ 2 = 40000 * p.R ^ 2 / p.γ ^ 2 := by unfold radius; field_simp; ring
  rw [hrad]
  have : p.γ * (270 * p.H / p.γ) * p.R ^ 2 / (48 * p.H * (40000 * p.R ^ 2 / p.γ ^ 2)) =
      270 * p.γ ^ 2 / 1920000 := by field_simp; ring
  have hmono : p.γ * (270 * p.H / p.γ) * p.R ^ 2 / (48 * p.H * (40000 * p.R ^ 2 / p.γ ^ 2)) ≤
      p.γ * reg p * p.R ^ 2 / (48 * p.H * (40000 * p.R ^ 2 / p.γ ^ 2)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hM hγ.le
  rw [this] at hmono
  have : p.γ ^ 2 / 32768 ≤ 270 * p.γ ^ 2 / 1920000 := by
    have := sq_nonneg p.γ
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  linarith

omit hp in
lemma reg_cube : reg p ^ 3 = 270 ^ 3 * p.H ^ 3 * iterations p / p.γ ^ 3 := by
  rw [reg_eq, div_pow, mul_pow, mul_pow, cbrt_cube]

lemma couple_budget : (iterations p : ℝ) * coupleError p ≤ 7776 * reg p / p.γ ^ 3 / 12 * p.R ^ 3 := by
  obtain ⟨hH, hγ, hγ1, hR, hL, -⟩ := id hp
  have hM := reg_pos hp
  have hc := reg_cube (p := p)
  have hK : (0 : ℝ) < iterations p := by exact_mod_cast iterations_pos hp
  unfold coupleError radius
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have e : 7776 * reg p / p.γ ^ 3 / 12 * p.R ^ 3 * (p.γ ^ 3 * reg p ^ 2) =
      648 * reg p ^ 3 * p.R ^ 3 := by field_simp; ring
  rw [e, hc]
  have e2 : (iterations p : ℝ) * (1536 * p.H ^ 3 * (200 * p.R / p.γ) ^ 3) =
      12288000000 * p.H ^ 3 * p.R ^ 3 * iterations p / p.γ ^ 3 := by field_simp; ring
  rw [e2]
  apply le_of_eq_of_le (b := 12288000000 * p.H ^ 3 * p.R ^ 3 * iterations p / p.γ ^ 3) rfl
  rw [div_le_iff₀ (by positivity)]
  have e3 : 648 * (270 ^ 3 * p.H ^ 3 * ↑(iterations p) / p.γ ^ 3) * p.R ^ 3 * p.γ ^ 3 =
      12754584000 * p.H ^ 3 * p.R ^ 3 * iterations p := by field_simp; ring
  rw [e3]
  have : 0 ≤ p.H ^ 3 * p.R ^ 3 * iterations p := by positivity
  nlinarith

lemma iter_plus_cube : ((iterations p : ℝ) + 1) ^ 3 ≤ 27 * (ratio p + 1) ^ 2 := by
  have hr := ratio_pos hp
  have hle := iterations_le hp
  set u := ratio p ^ (3 / 8 : ℝ)
  have hu : 0 ≤ u := by positivity
  have h1 : ((iterations p : ℝ) + 1) ^ 3 ≤ (u + 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  refine h1.trans ?_
  by_cases hu1 : u ≤ 1
  · have h3 : (u + 2) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    nlinarith [sq_nonneg (ratio p)]
  · push Not at hu1
    have hu3 : u ^ 3 = ratio p ^ (9 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
    have hr1 : 1 ≤ ratio p := by
      by_contra hc; push Not at hc
      have : u ≤ 1 := Real.rpow_le_one hr.le hc.le (by norm_num)
      linarith
    have h98 : ratio p ^ (9 / 8 : ℝ) ≤ ratio p ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
    rw [Real.rpow_two] at h98
    have h3 : (u + 2) ^ 3 ≤ (3 * u) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h4 : (3 * u) ^ 3 = 27 * u ^ 3 := by ring
    nlinarith [sq_nonneg (ratio p)]

lemma search_budget : total (iterations p) * searchError p ≤ 7776 * reg p / p.γ ^ 3 / 12 * p.R ^ 3 := by
  obtain ⟨hH, hγ, hγ1, hR, hL, -⟩ := id hp
  have htot : total (iterations p) ≤ 27 * (ratio p + 1) ^ 2 :=
    (total_upper _).trans (iter_plus_cube hp)
  have hg := gap_mul_le (p := p)
  have hgp := gap_pos (p := p)
  have hM := reg_ge' hp
  have hX : 0 < 27 * (ratio p + 1) ^ 2 := by have := ratio_pos hp; positivity
  set Q := p.L₀ / (p.H * p.R) + 32768
  have hQ : 0 < Q := by positivity
  have hgt : total (iterations p) * gap p ≤ p.γ ^ 2 / Q := by
    have h1 : total (iterations p) * gap p ≤ 27 * (ratio p + 1) ^ 2 * gap p :=
      mul_le_mul_of_nonneg_right htot hgp.le
    have h2 : 27 * (ratio p + 1) ^ 2 * gap p ≤ p.γ ^ 2 / Q := by
      rw [le_div_iff₀ hQ]
      have : gap p * (27 * (ratio p + 1) ^ 2 * Q / p.γ ^ 2) ≤ 1 := hg
      rw [mul_div_assoc', div_le_one (by positivity)] at this
      linarith
    linarith
  unfold searchError radius
  have e : total (iterations p) * (gap p * (200 * p.R / p.γ) ^ 2 *
      (p.L₀ / 2 + p.H * (200 * p.R / p.γ)) / p.γ) =
      (total (iterations p) * gap p) * (40000 * p.R ^ 2 * (p.L₀ / 2 + 200 * p.H * p.R / p.γ) / p.γ ^ 3) := by
    field_simp; ring
  rw [e]
  have hpos : 0 ≤ 40000 * p.R ^ 2 * (p.L₀ / 2 + 200 * p.H * p.R / p.γ) / p.γ ^ 3 := by positivity
  refine (mul_le_mul_of_nonneg_right hgt hpos).trans ?_
  have hrhs : 7776 * (270 * p.H / p.γ) / p.γ ^ 3 / 12 * p.R ^ 3 ≤ 7776 * reg p / p.γ ^ 3 / 12 * p.R ^ 3 := by
    gcongr
  refine le_trans ?_ hrhs
  have e2 : p.γ ^ 2 / Q * (40000 * p.R ^ 2 * (p.L₀ / 2 + 200 * p.H * p.R / p.γ) / p.γ ^ 3) =
      40000 * p.R ^ 2 * (p.L₀ * p.γ / 2 + 200 * p.H * p.R) / (Q * p.γ ^ 2) := by
    field_simp
  rw [e2, div_le_iff₀ (by positivity)]
  have e3 : 7776 * (270 * p.H / p.γ) / p.γ ^ 3 / 12 * p.R ^ 3 * (Q * p.γ ^ 2) =
      174960 * p.H * p.R ^ 3 * Q / p.γ ^ 2 := by field_simp; ring
  rw [e3, le_div_iff₀ (by positivity)]
  have hQe : p.H * p.R * Q = p.L₀ + 32768 * p.H * p.R := by
    simp only [Q]; field_simp
  have hγ2 : p.γ ^ 2 ≤ 1 := by nlinarith
  have hγ3 : p.γ ^ 3 ≤ 1 := by nlinarith
  have hLγ : p.L₀ * p.γ ≤ p.L₀ := by nlinarith
  have hb : 40000 * p.R ^ 2 * (p.L₀ * p.γ / 2 + 200 * p.H * p.R) * p.γ ^ 2 ≤
      40000 * p.R ^ 2 * (p.L₀ / 2 + 200 * p.H * p.R) := by
    have h0 : 0 ≤ 40000 * p.R ^ 2 * (p.L₀ * p.γ / 2 + 200 * p.H * p.R) := by positivity
    have h1 : 40000 * p.R ^ 2 * (p.L₀ * p.γ / 2 + 200 * p.H * p.R) * p.γ ^ 2 ≤
        40000 * p.R ^ 2 * (p.L₀ * p.γ / 2 + 200 * p.H * p.R) := by nlinarith
    have h2 : 40000 * p.R ^ 2 * (p.L₀ * p.γ / 2 + 200 * p.H * p.R) ≤
        40000 * p.R ^ 2 * (p.L₀ / 2 + 200 * p.H * p.R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    linarith
  have hfin : 40000 * p.R ^ 2 * (p.L₀ / 2 + 200 * p.H * p.R) ≤ 174960 * p.H * p.R ^ 3 * Q := by
    have : 174960 * p.H * p.R ^ 3 * Q = 174960 * p.R ^ 2 * (p.H * p.R * Q) := by ring
    rw [this, hQe]
    have : 0 ≤ p.R ^ 2 * p.L₀ := by positivity
    have : 0 ≤ p.H * p.R ^ 3 := by positivity
    nlinarith
  linarith

lemma final_rate : 7776 * reg p / p.γ ^ 3 / 3 * p.R ^ 3 / total (iterations p) ≤ p.ε := by
  obtain ⟨hH, hγ, hγ1, hR, hL, hε⟩ := id hp
  have hK1 := iterations_pos hp
  have hK : (0 : ℝ) < iterations p := by exact_mod_cast hK1
  set κ := (iterations p : ℝ) ^ (1 / 3 : ℝ)
  have hκ : 1 ≤ κ := cbrt_ge_one hp
  have hκ3 : κ ^ 3 = iterations p := cbrt_cube
  have hge := iterations_ge (p := p)
  have hκ8 : ratio p ≤ κ ^ 8 := by
    have h1 : ratio p ^ (3 / 8 : ℝ) ≤ κ ^ 3 := by rw [hκ3]; exact hge
    have h2 : (ratio p ^ (3 / 8 : ℝ)) ^ (8 / 3 : ℝ) ≤ (κ ^ 3) ^ (8 / 3 : ℝ) :=
      Real.rpow_le_rpow (by have := ratio_pos ⟨hH, hγ, hγ1, hR, hL, hε⟩; positivity) h1 (by norm_num)
    rw [← Real.rpow_mul (ratio_pos ⟨hH, hγ, hγ1, hR, hL, hε⟩).le] at h2
    rw [← Real.rpow_natCast κ 3, ← Real.rpow_mul (by positivity)] at h2
    norm_num at h2
    have : κ ^ (8 : ℝ) = κ ^ 8 := by exact_mod_cast Real.rpow_natCast κ 8
    linarith
  have htot := total_lower (iterations p)
  rw [← hκ3] at htot
  have htp : 0 < κ ^ 9 / 6 := by positivity
  have e : (κ ^ 3) ^ 3 = κ ^ 9 := by ring
  rw [e] at htot
  rw [div_le_iff₀ (lt_of_lt_of_le htp htot)]
  have hreg : reg p = 270 * p.H * κ / p.γ := rfl
  rw [hreg]
  have hrat : 8388608 * p.H * p.R ^ 3 ≤ p.γ ^ 4 * p.ε * κ ^ 8 := by
    have : ratio p * (p.γ ^ 4 * p.ε) = 8388608 * p.H * p.R ^ 3 := by
      unfold ratio; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hκ8 (by positivity : 0 ≤ p.γ ^ 4 * p.ε)]
  have hlhs : 7776 * (270 * p.H * κ / p.γ) / p.γ ^ 3 / 3 * p.R ^ 3 = 699840 * p.H * κ * p.R ^ 3 / p.γ ^ 4 := by
    field_simp; ring
  rw [hlhs, div_le_iff₀ (by positivity)]
  have h1 : p.ε * (κ ^ 9 / 6) * p.γ ^ 4 = κ * (p.γ ^ 4 * p.ε * κ ^ 8) / 6 := by ring
  have h2 : p.ε * total (iterations p) * p.γ ^ 4 ≥ p.ε * (κ ^ 9 / 6) * p.γ ^ 4 := by
    have := mul_le_mul_of_nonneg_left htot hε.le
    nlinarith [pow_pos hγ 4]
  have h3 : κ * (8388608 * p.H * p.R ^ 3) ≤ κ * (p.γ ^ 4 * p.ε * κ ^ 8) :=
    mul_le_mul_of_nonneg_left hrat (by linarith)
  have h4 : 0 ≤ p.H * κ * p.R ^ 3 := by positivity
  nlinarith

end

end LongTails.Proofs.QuasarCubicTuning
