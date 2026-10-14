import LongTails.Algorithms.QuadraticReshuffling
import Mathlib.Tactic

namespace OracleTemplate.QuadraticReshuffling

open LongTails.Setups.QuadraticFiniteSum

lemma epochScale_lower_bounds (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    32 * p.L / p.μ ≤ epochScale p ∧
    64 * p.L * Real.sqrt p.L * p.G / ((p.n : ℝ) * p.μ ^ 2 * Real.sqrt p.ε) ≤ epochScale p ∧
    4 * (p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) * p.μ ^ 4 * p.ε)) ^ (1 / 3 : ℝ) ≤ epochScale p := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have ha : 0 ≤ 32 * p.L / p.μ := by positivity
  have hb : 0 ≤ 64 * p.L * Real.sqrt p.L * p.G / ((p.n : ℝ) * p.μ ^ 2 * Real.sqrt p.ε) := by positivity
  have hc : 0 ≤ 4 * (p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) * p.μ ^ 4 * p.ε)) ^ (1 / 3 : ℝ) := by positivity
  unfold epochScale
  constructor
  · linarith
  constructor <;> linarith

lemma epochScale_pos (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) : 0 < epochScale p :=
  (by positivity : 0 < 32 * p.L / p.μ).trans_le (epochScale_lower_bounds p hL hμ hG hε).1

lemma stepSize_pos (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) : 0 < stepSize p := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hq := epochScale_pos p hL hμ hG hε
  unfold stepSize
  positivity

lemma stepSize_small (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) : stepSize p * p.n * p.L ≤ 1 / 32 := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.n
  have hq := epochScale_pos p hL hμ hG hε
  have hb := (div_le_iff₀ hμ).mp (epochScale_lower_bounds p hL hμ hG hε).1
  have he : stepSize p * p.n * p.L = p.L / (p.μ * epochScale p) := by
    unfold stepSize
    field_simp
  rw [he]
  apply (div_le_iff₀ (mul_pos hμ hq)).mpr
  nlinarith

lemma stepSize_identity (p : Params) (hμ : p.μ ≠ 0) :
    stepSize p * p.n * p.μ = 1 / epochScale p := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.n
  unfold stepSize
  field_simp

lemma bias_tuning (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    512 * stepSize p ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ ^ 2 ≤ p.ε / 8 := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hq := epochScale_pos p hL hμ hG hε
  let a := p.L * Real.sqrt p.L * p.G / ((p.n : ℝ) * p.μ ^ 2 * Real.sqrt p.ε)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : 64 * a ≤ epochScale p := by
    convert (epochScale_lower_bounds p hL hμ hG hε).2.1 using 1; dsimp [a]; ring
  have ha2 : a ^ 2 = p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) ^ 2 * p.μ ^ 4 * p.ε) := by
    dsimp [a]
    simp only [div_pow, mul_pow, Real.sq_sqrt hL.le, Real.sq_sqrt hε.le, ← pow_mul]
    ring
  have hs := pow_le_pow_left₀ (show 0 ≤ 64 * a by positivity) ha 2
  have he : 512 * stepSize p ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ ^ 2 =
      512 * a ^ 2 * p.ε / epochScale p ^ 2 := by
    rw [ha2]
    unfold stepSize
    field_simp
  rw [he]
  apply (div_le_iff₀ (pow_pos hq 2)).mpr
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ p.ε / 8 by positivity)
  nlinarith

lemma variance_tuning (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    4 * stepSize p ^ 3 * (p.n : ℝ) ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ ≤ p.ε / 16 := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hq := epochScale_pos p hL hμ hG hε
  let c := (p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) * p.μ ^ 4 * p.ε)) ^ (1 / 3 : ℝ)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : 4 * c ≤ epochScale p := (epochScale_lower_bounds p hL hμ hG hε).2.2
  have hc3 : c ^ 3 = p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) * p.μ ^ 4 * p.ε) := by
    rw [← Real.rpow_natCast c 3]
    dsimp [c]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  have hs := pow_le_pow_left₀ (show 0 ≤ 4 * c by positivity) hc 3
  have he : 4 * stepSize p ^ 3 * (p.n : ℝ) ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ =
      4 * c ^ 3 * p.ε / epochScale p ^ 3 := by
    rw [hc3]
    unfold stepSize
    field_simp
  rw [he]
  apply (div_le_iff₀ (pow_pos hq 3)).mpr
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ p.ε / 16 by positivity)
  nlinarith

lemma geometric_log_budget {q D ε : ℝ} (hq : 0 < q) (hq1 : 1 ≤ 2 * q)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    D / 2 * (1 - 1 / (2 * q)) ^ ⌈2 * q * Real.log (1 + D / ε)⌉₊ ≤ ε / 2 := by
  let K := ⌈2 * q * Real.log (1 + D / ε)⌉₊
  have harg : 0 < 1 + D / ε := by positivity
  have hr : 0 ≤ 1 - 1 / (2 * q) := by
    have hdiv : 1 / (2 * q) ≤ 1 := (div_le_one (by positivity)).mpr hq1
    linarith
  have hK : 2 * q * Real.log (1 + D / ε) ≤ (K : ℝ) := Nat.le_ceil _
  have hlog : Real.log (1 + D / ε) ≤ (K : ℝ) / (2 * q) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hp : (1 - 1 / (2 * q)) ^ K ≤ 1 / (1 + D / ε) := by
    calc
      _ ≤ (Real.exp (-1 / (2 * q))) ^ K := pow_le_pow_left₀ hr
        (by simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-1 / (2 * q))) K
      _ = Real.exp ((K : ℝ) * (-1 / (2 * q))) := (Real.exp_nat_mul _ K).symm
      _ ≤ Real.exp (-Real.log (1 + D / ε)) := Real.exp_le_exp.mpr (by
        have hh := neg_le_neg hlog
        convert hh using 1; ring)
      _ = _ := by rw [Real.exp_neg, Real.exp_log harg, one_div]
  calc
    _ ≤ D / 2 * (1 / (1 + D / ε)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ε / 2 * (D / (ε + D)) := by field_simp
    _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one (by positivity : 0 < ε + D)).mpr (by linarith)) (by positivity)
    _ = _ := mul_one _

lemma initialization_tuning (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hμL : p.μ ≤ p.L) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    p.L * p.R ^ 2 / 2 * (1 - stepSize p * p.n * p.μ / 2) ^ epochCount p ≤ p.ε / 2 := by
  have hq := epochScale_pos p hL hμ hG hε
  have hb := (div_le_iff₀ hμ).mp (epochScale_lower_bounds p hL hμ hG hε).1
  have hq32 : 32 ≤ epochScale p := by
    apply (mul_le_mul_iff_left₀ hμ).mp
    exact (mul_le_mul_of_nonneg_left hμL (by norm_num : (0 : ℝ) ≤ 32)).trans hb
  have he : stepSize p * p.n * p.μ / 2 = 1 / (2 * epochScale p) := by
    rw [stepSize_identity p hμ.ne']
    ring
  rw [he]
  exact geometric_log_budget hq (by linarith) (by positivity) hε

lemma epochCount_formula (p : Params) :
    epochCount p = ⌈(64 * p.L / p.μ + 128 * p.L * Real.sqrt p.L * p.G /
      ((p.n : ℝ) * p.μ ^ 2 * Real.sqrt p.ε) +
      8 * (p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) * p.μ ^ 4 * p.ε)) ^ (1 / 3 : ℝ)) *
      Real.log (1 + p.L * p.R ^ 2 / p.ε)⌉₊ := by
  unfold epochCount epochScale
  congr 1
  ring

end OracleTemplate.QuadraticReshuffling
