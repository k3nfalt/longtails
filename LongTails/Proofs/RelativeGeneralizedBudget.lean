import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace OracleTemplate.RelativeGeneralized

lemma logarithmic_bound {U r : ℝ} (hU : 2 ≤ U) (hr : 0 < r)
    (hs : r ^ 2 ≤ 9 * (2 : ℝ) ^ 60 * U ^ 6) :
    Real.log r ≤ 40 * (1 + Real.log U) := by
  have hU0 : 0 < U := by linarith
  have hb : r ≤ (2 : ℝ) ^ 32 * U ^ 3 := by
    have hpow : 9 * (2 : ℝ) ^ 60 * U ^ 6 ≤ ((2 : ℝ) ^ 32 * U ^ 3) ^ 2 := by
      nlinarith [sq_nonneg (U ^ 3)]
    exact (sq_le_sq₀ hr.le (by positivity)).mp (hs.trans hpow)
  have hl := Real.log_le_log hr hb
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hl
  have hl2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hlU := Real.log_nonneg (show 1 ≤ U by linarith)
  norm_num at hl
  linarith

lemma scalar_budget_terms {T q α H N : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hα : 0 ≤ α) (hH : 1 ≤ H) (hN : 0 < N)
    (hbudget : (2 : ℝ) ^ 60 *
      (Real.sqrt T + α ^ 2 * T + (1 + q) * H + α ^ 2 * q ^ 2 * H ^ 2) ≤ N) :
    2 * Real.sqrt T + α * Real.sqrt (N * T) + 160 * (1 + q) * H +
      80 * α * q * H * Real.sqrt N < N / 12288 := by
  have hs0 := Real.sqrt_nonneg T
  have hn0 := Real.sqrt_nonneg N
  have hnt0 := Real.sqrt_nonneg (N * T)
  have h1 : (2 : ℝ) ^ 60 * Real.sqrt T ≤ N := by
    nlinarith [mul_nonneg (sq_nonneg α) hT,
      mul_nonneg (sq_nonneg (α * q)) (sq_nonneg H)]
  have h2 : (2 : ℝ) ^ 60 * (α ^ 2 * T) ≤ N := by
    nlinarith [mul_nonneg (sq_nonneg (α * q)) (sq_nonneg H)]
  have h3 : (2 : ℝ) ^ 60 * ((1 + q) * H) ≤ N := by
    nlinarith [mul_nonneg (sq_nonneg α) hT,
      mul_nonneg (sq_nonneg (α * q)) (sq_nonneg H)]
  have h4 : (2 : ℝ) ^ 60 * (α ^ 2 * q ^ 2 * H ^ 2) ≤ N := by
    nlinarith [mul_nonneg (sq_nonneg α) hT]
  have h2' : (2 : ℝ) ^ 30 * (α * Real.sqrt (N * T)) ≤ N := by
    have hs := Real.sq_sqrt (mul_nonneg hN.le hT)
    have hh := mul_le_mul_of_nonneg_left h2 hN.le
    have hs' : ((2 : ℝ) ^ 30 * (α * Real.sqrt (N * T))) ^ 2 ≤ N ^ 2 := by
      nlinarith
    exact (sq_le_sq₀ (by positivity) hN.le).mp hs'
  have h4' : (2 : ℝ) ^ 30 * (α * q * H * Real.sqrt N) ≤ N := by
    have hs := Real.sq_sqrt hN.le
    have hh := mul_le_mul_of_nonneg_left h4 hN.le
    have hs' : ((2 : ℝ) ^ 30 * (α * q * H * Real.sqrt N)) ^ 2 ≤ N ^ 2 := by
      nlinarith
    exact (sq_le_sq₀ (by positivity) hN.le).mp hs'
  nlinarith

lemma budget_envelope {T q d α : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q) (hd : 0 ≤ d)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    let U := 2 + T + q + d
    let H := 1 + Real.log U
    let S := Real.sqrt T + α ^ 2 * T + (1 + q) * H + α ^ 2 * q ^ 2 * H ^ 2
    2 ≤ U ∧ 1 ≤ H ∧ H ≤ U ∧ 1 ≤ S ∧ S ≤ 4 * U ^ 4 := by
  dsimp only
  let U := 2 + T + q + d
  let H := 1 + Real.log U
  let S := Real.sqrt T + α ^ 2 * T + (1 + q) * H + α ^ 2 * q ^ 2 * H ^ 2
  change 2 ≤ U ∧ 1 ≤ H ∧ H ≤ U ∧ 1 ≤ S ∧ S ≤ 4 * U ^ 4
  have hU : 2 ≤ U := by dsimp [U]; linarith
  have hU0 : 0 < U := by linarith
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ U by linarith)
    dsimp [H]; linarith
  have hHU : H ≤ U := by
    have hh := Real.log_le_sub_one_of_pos hU0
    dsimp [H]; linarith
  have hTU : T ≤ U := by dsimp [U]; linarith
  have hqU : 1 + q ≤ U := by dsimp [U]; linarith
  have hsT : Real.sqrt T ≤ U := by
    have hh := Real.sq_sqrt hT
    have hroot := Real.sqrt_nonneg T
    nlinarith
  have ha2 : α ^ 2 ≤ 1 := by nlinarith
  have h2 : α ^ 2 * T ≤ U := (mul_le_mul_of_nonneg_right ha2 hT).trans (by simpa)
  have h3 : (1 + q) * H ≤ U ^ 2 := by
    calc
      _ ≤ U * U := mul_le_mul hqU hHU (by linarith) hU0.le
      _ = _ := by ring
  have h4 : α ^ 2 * q ^ 2 * H ^ 2 ≤ U ^ 4 := by
    have hq2 : q ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hq (by linarith) 2
    have hH2 : H ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (by linarith) hHU 2
    calc
      _ ≤ 1 * U ^ 2 * U ^ 2 := by gcongr
      _ = _ := by ring
  have hS : 1 ≤ S := by
    have hh : 1 ≤ (1 + q) * H := by nlinarith
    dsimp [S]
    nlinarith [Real.sqrt_nonneg T, mul_nonneg (sq_nonneg α) hT,
      mul_nonneg (sq_nonneg (α * q)) (sq_nonneg H)]
  refine ⟨hU, hH, hHU, hS, ?_⟩
  have hUU : U ≤ U ^ 2 := by nlinarith
  have hU4 : U ^ 2 ≤ U ^ 4 := by nlinarith [sq_nonneg (U ^ 2 - 1)]
  dsimp [S]
  nlinarith

lemma ceiling_budget_bounds {S U : ℝ} (hS : 1 ≤ S) (hU : 2 ≤ U)
    (hSU : S ≤ 4 * U ^ 4) :
    let N := ⌈(2 : ℝ) ^ 60 * S⌉₊
    0 < N ∧ (2 : ℝ) ^ 60 * S ≤ N ∧ (N : ℝ) ≤ 8 * (2 : ℝ) ^ 60 * U ^ 4 := by
  dsimp only
  have hb := Nat.le_ceil ((2 : ℝ) ^ 60 * S)
  have hu := Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ 60 * S by positivity)
  have hn : 0 < (⌈(2 : ℝ) ^ 60 * S⌉₊ : ℝ) := by nlinarith
  refine ⟨by exact_mod_cast hn, hb, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hSU (show (0 : ℝ) ≤ 2 ^ 60 by positivity)
  have hp : 1 ≤ U ^ 4 := by nlinarith [sq_nonneg (U ^ 2 - 1)]
  nlinarith

lemma numeric_accuracy {T q d α N s0 sN : ℝ}
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hd : 0 < d) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : 0 < sN) (hinit : s0 ^ 2 * d = 1)
    (hbudget : (2 : ℝ) ^ 60 * (Real.sqrt T + α ^ 2 * T +
      (1 + q) * (1 + Real.log (2 + T + q + d)) +
      α ^ 2 * q ^ 2 * (1 + Real.log (2 + T + q + d)) ^ 2) ≤ N)
    (hupper : N ≤ 8 * (2 : ℝ) ^ 60 * (2 + T + q + d) ^ 4)
    (hprogress : N / 12288 ≤
      (sN + 2 * (1 + q * Real.sqrt (2 + α ^ 2 * N)) * Real.log sN) -
      (s0 + 2 * (1 + q * Real.sqrt (2 + α ^ 2 * N)) * Real.log s0)) :
    (2 + α ^ 2 * N) * T ≤ sN ^ 2 := by
  let U := 2 + T + q + d
  let H := 1 + Real.log U
  let B := 2 + α ^ 2 * N
  let Q := 1 + q * Real.sqrt B
  have hU : 2 ≤ U := by dsimp [U]; linarith
  have hU0 : 0 < U := by linarith
  have hH : 1 ≤ H := (budget_envelope hT hq hd.le hα hα1).2.1
  have hB : 0 < B := by dsimp [B]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  change B * T ≤ sN ^ 2
  by_contra hfail
  have hfail' : sN ^ 2 ≤ B * T := (lt_of_not_ge hfail).le
  have hBupper : B ≤ 9 * (2 : ℝ) ^ 60 * U ^ 4 := by
    have ha : α ^ 2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right ha hN.le
    have hu4 : 1 ≤ U ^ 4 := by nlinarith [sq_nonneg (U ^ 2 - 1)]
    change N ≤ 8 * (2 : ℝ) ^ 60 * U ^ 4 at hupper
    dsimp [B]
    nlinarith
  have hTle : T ≤ U := by dsimp [U]; linarith
  have hdle : d ≤ U := by dsimp [U]; linarith
  have hratio : (sN / s0) ^ 2 = sN ^ 2 * d := by
    field_simp
    nlinarith [congrArg (fun r : ℝ => sN ^ 2 * r) hinit]
  have hratioBound : (sN / s0) ^ 2 ≤ 9 * (2 : ℝ) ^ 60 * U ^ 6 := by
    rw [hratio]
    calc
      _ ≤ B * T * d := mul_le_mul_of_nonneg_right hfail' hd.le
      _ ≤ (9 * (2 : ℝ) ^ 60 * U ^ 4) * U * U := by gcongr
      _ = _ := by ring
  have hlog := logarithmic_bound hU (div_pos hsN hs0) hratioBound
  rw [Real.log_div hsN.ne' hs0.ne'] at hlog
  change Real.log sN - Real.log s0 ≤ 40 * H at hlog
  have hrootB : Real.sqrt B ≤ 2 + α * Real.sqrt N := by
    have hb := Real.sq_sqrt hB.le
    have hn := Real.sq_sqrt hN.le
    have hbn := Real.sqrt_nonneg B
    have hnn := Real.sqrt_nonneg N
    dsimp [B] at hb
    have hn2 := congrArg (fun v : ℝ => α ^ 2 * v) hn
    nlinarith only [hb, hn2, hbn, hnn, hα, mul_nonneg hα hnn]
  have hQbound : Q ≤ 2 * (1 + q) + α * q * Real.sqrt N := by
    have hh := mul_le_mul_of_nonneg_left hrootB hq
    dsimp [Q]
    nlinarith only [hh]
  have hsNbound : sN ≤ 2 * Real.sqrt T + α * Real.sqrt (N * T) := by
    have ht := Real.sq_sqrt hT
    have hnt := Real.sq_sqrt (mul_nonneg hN.le hT)
    have ht0 := Real.sqrt_nonneg T
    have hnt0 := Real.sqrt_nonneg (N * T)
    have hh : sN ^ 2 ≤ (2 * Real.sqrt T + α * Real.sqrt (N * T)) ^ 2 := by
      dsimp [B] at hfail'
      have hn2 := congrArg (fun v : ℝ => α ^ 2 * v) hnt
      nlinarith only [hfail', ht, hn2, hT, mul_nonneg (mul_nonneg hα ht0) hnt0]
    exact (sq_le_sq₀ hsN.le (by positivity)).mp hh
  have hlogscale := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * Q by positivity)
  have hQscale := mul_le_mul_of_nonneg_right hQbound (show 0 ≤ 80 * H by linarith)
  have hsmall := scalar_budget_terms hT hq hα hH hN hbudget
  change N / 12288 ≤ (sN + 2 * Q * Real.log sN) - (s0 + 2 * Q * Real.log s0) at hprogress
  nlinarith only [hprogress, hlogscale, hQscale, hsNbound, hsmall, hs0]

end OracleTemplate.RelativeGeneralized
