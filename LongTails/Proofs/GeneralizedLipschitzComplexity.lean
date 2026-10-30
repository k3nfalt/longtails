import LongTails.Proofs.GeneralizedLipschitzPilot
import LongTails.Proofs.GeneralizedLipschitzWarmStart
open scoped BigOperators
namespace LongTails.Proofs.GeneralizedLipschitzComplexity
lemma log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hl hu ⊢
  exact ⟨hl, hu⟩
lemma max_one_ceil_le {x U : ℝ} (hx : 0 ≤ x) (hU : 1 ≤ U) (h : x + 1 ≤ U) :
    ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ U := by
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le hU ((Nat.ceil_lt_add_one hx).le.trans h)
lemma tree_leaves_bound (n : ℕ) (hn : 0 < n) :
    (3 : ℕ) ^ Nat.clog 2 n ≤ 4 * n ^ 2 := by
  have h2 : (2 : ℕ) ^ Nat.clog 2 n ≤ 2 * n := by
    by_cases hn1 : n ≤ 1
    · have he : n = 1 := by omega
      subst n
      norm_num
    · have hclog : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
      have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < n)
      have he : Nat.clog 2 n = (Nat.clog 2 n).pred + 1 := (Nat.succ_pred_eq_of_pos hclog).symm
      rw [he, pow_succ]
      nlinarith
  have h3 : (3 : ℕ) ^ Nat.clog 2 n ≤ 4 ^ Nat.clog 2 n := Nat.pow_le_pow_left (by norm_num) _
  have he : (4 : ℕ) ^ Nat.clog 2 n = (2 ^ Nat.clog 2 n) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 (Nat.clog 2 n), pow_mul]
  rw [he] at h3
  nlinarith [Nat.pow_le_pow_left h2 2]
lemma logarithmic_envelope {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let κ := max 1 a
    let L := 1 + Real.log (2 + a + b)
    1 ≤ κ ∧ κ ≤ 1 + a ∧ (3 / 2 : ℝ) ≤ L ∧ Real.log κ ≤ L ∧ 0 ≤ Real.log L ∧ Real.log L ≤ L := by
  let κ := max 1 a
  let L := 1 + Real.log (2 + a + b)
  have hκ : 1 ≤ κ := le_max_left _ _
  have hκa : κ ≤ 1 + a := max_le (by linarith) (by linarith)
  have hU : (2 : ℝ) ≤ 2 + a + b := by linarith
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU
  have hL : (3 / 2 : ℝ) ≤ L := by dsimp [L]; linarith [log_two_bounds.1]
  have hlogκ : Real.log κ ≤ Real.log (2 + a + b) := Real.log_le_log (by linarith) (by linarith)
  refine ⟨hκ, hκa, hL, ?_, Real.log_nonneg (by linarith), ?_⟩
  · linarith
  · exact (Real.log_le_sub_one_of_pos (show 0 < L by linarith)).trans (by linarith)
lemma burn_horizon_cost {κ : ℝ} (hκ : 1 ≤ κ) :
    let T := ⌈204800 * κ ^ 2⌉₊
    0 < T ∧ (T : ℝ) ≤ 2 ^ 18 * κ ^ 2 ∧ (100 * T : ℝ) ≤ 2 ^ 25 * κ ^ 2 := by
  have hκp : 0 < κ := by linarith
  have hp : 0 < 204800 * κ ^ 2 := by positivity
  have hl := Nat.le_ceil (204800 * κ ^ 2)
  have hu := (Nat.ceil_lt_add_one hp.le).le
  have ht : (0 : ℝ) < ⌈204800 * κ ^ 2⌉₊ := hp.trans_le hl
  refine ⟨by exact_mod_cast ht, ?_, ?_⟩ <;> norm_num <;> nlinarith
lemma raw_count_cost {κ L : ℝ} (hκ : 1 ≤ κ) (hL : (3 / 2 : ℝ) ≤ L) (hlogκ : Real.log κ ≤ L) :
    let T := ⌈204800 * κ ^ 2⌉₊
    let δ : ℝ := 1 / (100 * T)
    let n := max 1 ⌈16 * κ * Real.log (9 / δ)⌉₊
    (n : ℝ) ≤ 512 * κ * L := by
  let T := ⌈204800 * κ ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  have ht := burn_horizon_cost hκ
  have hTp : (0 : ℝ) < T := by exact_mod_cast ht.1
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast ht.1
  have hκp : 0 < κ := by linarith
  have he : 9 / δ = 900 * T := by dsimp [δ]; field_simp; norm_num
  have h9 : 9 / δ ≤ (2 : ℝ) ^ 29 * κ ^ 2 := by rw [he]; nlinarith [ht.2.1]
  have hlog := Real.log_le_log (by rw [he]; positivity : 0 < 9 / δ) h9
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hκp.ne'), Real.log_pow, Real.log_pow] at hlog
  have hlogb : Real.log (9 / δ) ≤ 31 * L := by
    norm_num at hlog
    nlinarith [log_two_bounds.2]
  have hlog0 : 0 ≤ Real.log (9 / δ) := Real.log_nonneg (by rw [he]; nlinarith)
  have hkL : 1 ≤ κ * L := by nlinarith
  apply max_one_ceil_le (by positivity) (by nlinarith : 1 ≤ 512 * κ * L)
  change 16 * κ * Real.log (9 / δ) + 1 ≤ 512 * κ * L
  have hm := mul_le_mul_of_nonneg_left hlogb (show 0 ≤ 16 * κ by positivity)
  nlinarith
lemma raw_bracket_cost {κ L : ℝ} (hκ : 1 ≤ κ) (hL : (3 / 2 : ℝ) ≤ L) (hlogκ : Real.log κ ≤ L) :
    let T := ⌈204800 * κ ^ 2⌉₊
    let δ : ℝ := 1 / (100 * T)
    let n := max 1 ⌈16 * κ * Real.log (9 / δ)⌉₊
    let K := 2 * κ + Real.sqrt (9 * (n : ℝ) / δ)
    2 * κ ≤ K ∧ K ≤ 2 ^ 20 * κ ^ 2 * L := by
  let T := ⌈204800 * κ ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  let n := max 1 ⌈16 * κ * Real.log (9 / δ)⌉₊
  have ht := burn_horizon_cost hκ
  have hn := raw_count_cost hκ hL hlogκ
  have hTp : (0 : ℝ) < T := by exact_mod_cast ht.1
  have hκp : 0 < κ := by linarith
  have hLp : 0 < L := by linarith
  have hkL : 1 ≤ κ * L := by nlinarith
  have he : 9 * (n : ℝ) / δ = 900 * (n : ℝ) * T := by dsimp [δ]; field_simp; ring
  have hm : (n : ℝ) * T ≤ (512 * κ * L) * (2 ^ 18 * κ ^ 2) :=
    mul_le_mul hn ht.2.1 (Nat.cast_nonneg T) (show 0 ≤ 512 * κ * L by positivity)
  have hrad : 9 * (n : ℝ) / δ ≤ (2 ^ 19 * κ ^ 2 * L) ^ 2 := by
    rw [he]
    have hx := mul_le_mul_of_nonneg_left hkL (show 0 ≤ (2 : ℝ) ^ 38 * κ ^ 3 * L by positivity)
    nlinarith
  have hs : Real.sqrt (9 * (n : ℝ) / δ) ≤ 2 ^ 19 * κ ^ 2 * L :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hrad⟩
  change 2 * κ ≤ 2 * κ + Real.sqrt (9 * (n : ℝ) / δ) ∧
    2 * κ + Real.sqrt (9 * (n : ℝ) / δ) ≤ 2 ^ 20 * κ ^ 2 * L
  refine ⟨by linarith [Real.sqrt_nonneg (9 * (n : ℝ) / δ)], ?_⟩
  have hx := mul_le_mul_of_nonneg_left hkL hκp.le
  nlinarith

lemma scales_cost {κ L : ℝ} (hκ : 1 ≤ κ) (hL : (3 / 2 : ℝ) ≤ L) (hlogκ : Real.log κ ≤ L) :
    let T := ⌈204800 * κ ^ 2⌉₊
    let δ : ℝ := 1 / (100 * T)
    let n := max 1 ⌈16 * κ * Real.log (9 / δ)⌉₊
    let K := 2 * κ + Real.sqrt (9 * (n : ℝ) / δ)
    let J := ⌈Real.log (2 * K) / Real.log 2⌉₊ + 2
    (J : ℝ) ≤ 32 * L := by
  let T := ⌈204800 * κ ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  let n := max 1 ⌈16 * κ * Real.log (9 / δ)⌉₊
  let K := 2 * κ + Real.sqrt (9 * (n : ℝ) / δ)
  have hK : 2 * κ ≤ K ∧ K ≤ 2 ^ 20 * κ ^ 2 * L := raw_bracket_cost hκ hL hlogκ
  have hκp : 0 < κ := by linarith
  have hLp : 0 < L := by linarith
  have hKp : 0 < K := by linarith [hK.1]
  have hbound : 2 * K ≤ (2 : ℝ) ^ 21 * κ ^ 2 * L := by nlinarith [hK.2]
  have hlog := Real.log_le_log (by positivity : 0 < 2 * K) hbound
  rw [Real.log_mul (by positivity) hLp.ne', Real.log_mul (by positivity) (pow_ne_zero _ hκp.ne'),
    Real.log_pow, Real.log_pow] at hlog
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hlog2 : 0 < Real.log 2 := by linarith [log_two_bounds.1]
  have hratio : Real.log (2 * K) / Real.log 2 ≤ 21 + 6 * L := by
    apply (div_le_iff₀ hlog2).mpr
    have hm := mul_le_mul_of_nonneg_left log_two_bounds.1 (show 0 ≤ 6 * L by positivity)
    norm_num at hlog
    nlinarith
  have hlog0 : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by nlinarith [hK.1])
  have hc := (Nat.ceil_lt_add_one (div_nonneg hlog0 hlog2.le)).le
  change ((⌈Real.log (2 * K) / Real.log 2⌉₊ + 2 : ℕ) : ℝ) ≤ 32 * L
  push_cast
  nlinarith

lemma pilot_log_cost {κ L : ℝ} (hκ : 1 ≤ κ) (hL : (3 / 2 : ℝ) ≤ L) (hlogκ : Real.log κ ≤ L)
    (J : ℕ) (hJ : 0 < J) (hJL : (J : ℝ) ≤ 32 * L) :
    let T := ⌈204800 * κ ^ 2⌉₊
    let δ : ℝ := 1 / (100 * T)
    0 < Real.log (3 * (J : ℝ) / δ) ∧ Real.log (3 * (J : ℝ) / δ) ≤ 25 * L := by
  let T := ⌈204800 * κ ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  have ht := burn_horizon_cost hκ
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast ht.1
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hκp : 0 < κ := by linarith
  have hLp : 0 < L := by linarith
  have he : 3 * (J : ℝ) / δ = 300 * J * T := by dsimp [δ]; field_simp; ring
  have hp : 1 < 3 * (J : ℝ) / δ := by rw [he]; nlinarith
  have hm := mul_le_mul hJL ht.2.1 (Nat.cast_nonneg T) (show 0 ≤ 32 * L by positivity)
  have hbound : 3 * (J : ℝ) / δ ≤ (2 : ℝ) ^ 32 * κ ^ 2 * L := by rw [he]; nlinarith
  have hlog := Real.log_le_log (by linarith : 0 < 3 * (J : ℝ) / δ) hbound
  rw [Real.log_mul (by positivity) hLp.ne', Real.log_mul (by positivity) (pow_ne_zero _ hκp.ne'),
    Real.log_pow, Real.log_pow] at hlog
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  change 0 < Real.log (3 * (J : ℝ) / δ) ∧ Real.log (3 * (J : ℝ) / δ) ≤ 25 * L
  refine ⟨Real.log_pos hp, ?_⟩
  norm_num at hlog
  nlinarith [log_two_bounds.2]
lemma tree_and_repetitions_cost {L z : ℝ} (hL : (3 / 2 : ℝ) ≤ L) (hz : 0 < z) (hzL : z ≤ 25 * L) :
    let m := ⌈z / Real.log 4⌉₊
    ((3 ^ Nat.clog 2 m : ℕ) : ℝ) ≤ 2 ^ 12 * L ^ 2 ∧
      ((max 1 ⌈z / Real.log 2⌉₊ : ℕ) : ℝ) ≤ 64 * L := by
  have hlog2 : 0 < Real.log 2 := by linarith [log_two_bounds.1]
  have hlog4 : 1 ≤ Real.log 4 := by
    have he : Real.log 4 = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [he]
    linarith [log_two_bounds.1]
  have hlog4p : 0 < Real.log 4 := by linarith
  have hm0 : 0 < ⌈z / Real.log 4⌉₊ := by
    have hp := (div_pos hz hlog4p).trans_le (Nat.le_ceil (z / Real.log 4))
    exact_mod_cast hp
  have hr : z / Real.log 4 ≤ 25 * L := by
    apply (div_le_iff₀ hlog4p).mpr
    have hh := mul_le_mul_of_nonneg_left hlog4 (show 0 ≤ 25 * L by linarith)
    nlinarith
  have hm : (⌈z / Real.log 4⌉₊ : ℝ) ≤ 32 * L := by
    have hh := (Nat.ceil_lt_add_one (div_pos hz hlog4p).le).le
    linarith
  have ht : ((3 ^ Nat.clog 2 ⌈z / Real.log 4⌉₊ : ℕ) : ℝ) ≤ 4 * (⌈z / Real.log 4⌉₊ : ℝ) ^ 2 := by
    exact_mod_cast tree_leaves_bound _ hm0
  refine ⟨?_, ?_⟩
  · have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌈z / Real.log 4⌉₊) hm 2
    nlinarith
  · apply max_one_ceil_le (div_pos hz hlog2).le (by linarith : 1 ≤ 64 * L)
    have hr2 : z / Real.log 2 ≤ 50 * L := by
      apply (div_le_iff₀ hlog2).mpr
      have hh := mul_le_mul_of_nonneg_left log_two_bounds.1 (show 0 ≤ 50 * L by linarith)
      nlinarith
    linarith


open LongTails.Algorithms.GeneralizedLipschitzPilot
lemma burn_total_cost {κ L : ℝ} (hκ : 1 ≤ κ) (hL : (3 / 2 : ℝ) ≤ L) (hlogκ : Real.log κ ≤ L) :
    let T := ⌈204800 * κ ^ 2⌉₊
    let δ : ℝ := 1 / (100 * T)
    ((T * (tuning κ δ).calls : ℕ) : ℝ) ≤ 2 ^ 64 * κ ^ 3 * L ^ 3 := by
  let T := ⌈204800 * κ ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  let c := tuning κ δ
  have hκp : 0 < κ := by linarith
  have hLp : 0 < L := by linarith
  have hraw : (c.rawCount : ℝ) ≤ 512 * κ * L := raw_count_cost hκ hL hlogκ
  have hscales : (c.scales : ℝ) ≤ 32 * L := scales_cost hκ hL hlogκ
  have hJp : 0 < c.scales := by dsimp [c, tuning]; omega
  have hlog := pilot_log_cost hκ hL hlogκ c.scales hJp hscales
  have htree := tree_and_repetitions_cost hL hlog.1 hlog.2
  have hleafN : ((3 ^ c.depth : ℕ) : ℝ) ≤ 2 ^ 12 * L ^ 2 := htree.1
  have hleaf : (3 : ℝ) ^ c.depth ≤ 2 ^ 12 * L ^ 2 := by exact_mod_cast hleafN
  have hreps : (c.repetitions : ℝ) ≤ 64 * L := htree.2
  have hq : (c.momentCount : ℝ) ≤ 2 ^ 27 * κ := by
    apply max_one_ceil_le (by positivity : 0 ≤ 67108864 * κ) (by nlinarith : 1 ≤ (2 : ℝ) ^ 27 * κ)
    nlinarith
  have hm : (c.meanCount : ℝ) ≤ 2 ^ 14 * κ := by
    apply max_one_ceil_le (by positivity : 0 ≤ 9216 * κ) (by nlinarith : 1 ≤ (2 : ℝ) ^ 14 * κ)
    nlinarith
  have hu : (c.updateCount : ℝ) ≤ 32 * κ := by
    apply max_one_ceil_le (by positivity : 0 ≤ 16 * κ) (by nlinarith : 1 ≤ 32 * κ)
    nlinarith
  have hscale : (c.scaleCalls : ℝ) ≤ 2 ^ 40 * κ * L ^ 2 := by
    have hqpart := mul_le_mul hleaf hq (Nat.cast_nonneg c.momentCount) (show 0 ≤ 2 ^ 12 * L ^ 2 by positivity)
    have hmpart := mul_le_mul hreps hm (Nat.cast_nonneg c.meanCount) (show 0 ≤ 64 * L by positivity)
    have hLL : L ≤ L ^ 2 := by nlinarith
    have hLL' := mul_le_mul_of_nonneg_left hLL (show 0 ≤ (2 : ℝ) ^ 20 * κ by positivity)
    change ((3 ^ c.depth * c.momentCount + c.repetitions * c.meanCount : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith
  have hcalls : (c.calls : ℝ) ≤ 2 ^ 46 * κ * L ^ 3 := by
    have hmid := mul_le_mul hscales hscale (Nat.cast_nonneg c.scaleCalls) (show 0 ≤ 32 * L by positivity)
    have hLL : L ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
    have hL1 : (1 : ℝ) ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
    have hraw' := mul_le_mul_of_nonneg_left hLL (show 0 ≤ 512 * κ by positivity)
    have hu' := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ 32 * κ by positivity)
    change ((c.rawCount + c.scales * c.scaleCalls + c.updateCount : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith
  have ht : (T : ℝ) ≤ 2 ^ 18 * κ ^ 2 := (burn_horizon_cost hκ).2.1
  have htotal := mul_le_mul ht hcalls (Nat.cast_nonneg c.calls) (show 0 ≤ 2 ^ 18 * κ ^ 2 by positivity)
  change ((T * c.calls : ℕ) : ℝ) ≤ _
  push_cast
  nlinarith [htotal]

lemma phase_block_cost {κ : ℝ} (hκ : 1 ≤ κ) :
    let T := ⌈(192 * κ) ^ 2⌉₊
    0 < T ∧ (T : ℝ) ≤ 2 ^ 16 * κ ^ 2 := by
  have hκp : 0 < κ := by linarith
  have hp : 0 < (192 * κ) ^ 2 := by positivity
  have hl := Nat.le_ceil ((192 * κ) ^ 2)
  have hu := (Nat.ceil_lt_add_one hp.le).le
  refine ⟨by exact_mod_cast hp.trans_le hl, ?_⟩
  nlinarith
lemma phase_inverse_step_cost {κ b : ℝ} (hκ : 1 ≤ κ) (hb : 0 < b) :
    let T := ⌈(192 * κ) ^ 2⌉₊
    let α := min (1 / (32 * T * κ)) (min ((1 / (960 * b)) ^ 2) (1 / (61440 * T * b)))
    0 < α ∧ α⁻¹ ≤ 2 ^ 32 * (κ ^ 3 + κ ^ 2 * b + b ^ 2) := by
  let T := ⌈(192 * κ) ^ 2⌉₊
  let A := 1 / (32 * T * κ)
  let B := (1 / (960 * b)) ^ 2
  let C := 1 / (61440 * T * b)
  have ht := phase_block_cost hκ
  have hTp : (0 : ℝ) < T := by exact_mod_cast ht.1
  have hκp : 0 < κ := by linarith
  have hκ3 : 0 ≤ κ ^ 3 := by positivity
  have hκ2b : 0 ≤ κ ^ 2 * b := by positivity
  have hb2 : 0 ≤ b ^ 2 := by positivity
  have hA : A⁻¹ ≤ 2 ^ 32 * (κ ^ 3 + κ ^ 2 * b + b ^ 2) := by
    dsimp [A]
    rw [one_div, inv_inv]
    have hh := mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ 32 * κ by positivity)
    nlinarith
  have hB : B⁻¹ ≤ 2 ^ 32 * (κ ^ 3 + κ ^ 2 * b + b ^ 2) := by
    dsimp [B]
    simp only [one_div, inv_pow, inv_inv]
    nlinarith
  have hC : C⁻¹ ≤ 2 ^ 32 * (κ ^ 3 + κ ^ 2 * b + b ^ 2) := by
    dsimp [C]
    rw [one_div, inv_inv]
    have hh := mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ 61440 * b by positivity)
    nlinarith
  change 0 < min A (min B C) ∧ (min A (min B C))⁻¹ ≤ _
  refine ⟨by dsimp [A, B, C]; positivity, ?_⟩
  rcases min_choice A (min B C) with ha | ha
  · rw [ha]; exact hA
  · rw [ha]
    rcases min_choice B C with hc | hc
    · rw [hc]; exact hB
    · rw [hc]; exact hC
lemma phase_log_cost {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    let L := 1 + Real.log (2 + a + b)
    0 < Real.log (max 2 (40960 * b)) ∧ Real.log (max 2 (40960 * b)) ≤ 12 * L := by
  let L := 1 + Real.log (2 + a + b)
  have henv := logarithmic_envelope ha hb.le
  have hL : (3 / 2 : ℝ) ≤ L := henv.2.2.1
  have hU : 0 < 2 + a + b := by positivity
  have hp : 1 < max 2 (40960 * b) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
  have hbound : max 2 (40960 * b) ≤ (2 : ℝ) ^ 16 * (2 + a + b) := max_le (by nlinarith) (by nlinarith)
  have hh := Real.log_le_log (by linarith : 0 < max 2 (40960 * b)) hbound
  rw [Real.log_mul (by positivity) hU.ne', Real.log_pow] at hh
  refine ⟨Real.log_pos hp, ?_⟩
  change Real.log (max 2 (40960 * b)) ≤ 12 * L
  have he : Real.log (2 + a + b) = L - 1 := by dsimp [L]; ring
  rw [he] at hh
  norm_num at hh
  nlinarith [log_two_bounds.2]
lemma phase_horizon_cost {a b κ : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hκ : 1 ≤ κ) :
    let L := 1 + Real.log (2 + a + b)
    let T := ⌈(192 * κ) ^ 2⌉₊
    let α := min (1 / (32 * T * κ)) (min ((1 / (960 * b)) ^ 2) (1 / (61440 * T * b)))
    ((⌈(2 / α) * Real.log (max 2 (40960 * b))⌉₊ : ℕ) : ℝ) ≤
      2 ^ 38 * (κ ^ 3 + κ ^ 2 * b + b ^ 2) * L := by
  let L := 1 + Real.log (2 + a + b)
  let T := ⌈(192 * κ) ^ 2⌉₊
  let α := min (1 / (32 * T * κ)) (min ((1 / (960 * b)) ^ 2) (1 / (61440 * T * b)))
  let S := κ ^ 3 + κ ^ 2 * b + b ^ 2
  have hα : 0 < α ∧ α⁻¹ ≤ 2 ^ 32 * S := phase_inverse_step_cost hκ hb
  have hz := phase_log_cost ha hb
  have hL : (3 / 2 : ℝ) ≤ L := (logarithmic_envelope ha hb.le).2.2.1
  have hS : 1 ≤ S := by dsimp [S]; nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg κ) hb.le]
  have hx : 0 ≤ (2 / α) * Real.log (max 2 (40960 * b)) := mul_nonneg (div_nonneg (by norm_num) hα.1.le) hz.1.le
  have hc := (Nat.ceil_lt_add_one hx).le
  have hh := mul_le_mul hα.2 hz.2 hz.1.le (show 0 ≤ 2 ^ 32 * S by positivity)
  change ((⌈(2 / α) * Real.log (max 2 (40960 * b))⌉₊ : ℕ) : ℝ) ≤ 2 ^ 38 * S * L
  rw [div_eq_mul_inv]
  rw [div_eq_mul_inv] at hc
  change α⁻¹ * Real.log (max 2 (40960 * b)) ≤ 2 ^ 32 * S * (12 * L) at hh
  have hSL : 1 ≤ S * L := by nlinarith
  nlinarith

lemma physical_tuning {R G G0 ε : ℝ} (hR : 0 < R) (hG0 : 0 < G0) (hε : 0 < ε) :
    let D := 2 * R
    let e := ε / 20
    let τ := ⌈(96 * D * G) ^ 2⌉₊
    let κ := R * G
    let b := R * G0 / ε
    τ = ⌈(192 * κ) ^ 2⌉₊ ∧
    min (1 / (16 * τ * (D * G))) (min ((e / (24 * D * G0)) ^ 2) (e / (1536 * τ * D * G0))) =
      min (1 / (32 * τ * κ)) (min ((1 / (960 * b)) ^ 2) (1 / (61440 * τ * b))) ∧
    1024 * D * G0 / e = 40960 * b := by
  dsimp only
  refine ⟨by congr 2; ring, ?_, ?_⟩
  · congr 1
    · congr 1; ring
    · congr 1
      · congr 1
        field_simp
        ring
      · by_cases ht : (⌈(96 * (2 * R) * G) ^ 2⌉₊ : ℝ) = 0
        · simp [ht]
        · field_simp
          ring
  · field_simp
    ring
lemma normalized_parameters {R G1 : ℝ} (hR : 0 < R) :
    R * max G1 (1 / R) = max 1 (R * G1) := by
  rw [mul_max_of_nonneg _ _ hR.le]
  field_simp
  exact max_comm _ _
lemma total_cost {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    let κ := max 1 a
    let L := 1 + Real.log (2 + a + b)
    let T := ⌈204800 * κ ^ 2⌉₊
    let δ : ℝ := 1 / (100 * T)
    let τ := ⌈(192 * κ) ^ 2⌉₊
    let α := min (1 / (32 * τ * κ)) (min ((1 / (960 * b)) ^ 2) (1 / (61440 * τ * b)))
    let K := ⌈(2 / α) * Real.log (max 2 (40960 * b))⌉₊
    T * (LongTails.Algorithms.GeneralizedLipschitzPilot.tuning κ δ).calls + K ≤
      ⌈2 ^ 66 * ((1 + a) ^ 3 + (1 + a) ^ 2 * b + b ^ 2) * L ^ 3⌉₊ := by
  let κ := max 1 a
  let L := 1 + Real.log (2 + a + b)
  let T := ⌈204800 * κ ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  let τ := ⌈(192 * κ) ^ 2⌉₊
  let α := min (1 / (32 * τ * κ)) (min ((1 / (960 * b)) ^ 2) (1 / (61440 * τ * b)))
  let K := ⌈(2 / α) * Real.log (max 2 (40960 * b))⌉₊
  let S := κ ^ 3 + κ ^ 2 * b + b ^ 2
  let U := (1 + a) ^ 3 + (1 + a) ^ 2 * b + b ^ 2
  have he := logarithmic_envelope ha hb.le
  have hκ : 1 ≤ κ := he.1
  have hL : (3 / 2 : ℝ) ≤ L := he.2.2.1
  have hburn := burn_total_cost hκ hL he.2.2.2.1
  have hwarm : (K : ℝ) ≤ 2 ^ 38 * S * L := phase_horizon_cost ha hb hκ
  have hκ2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ κ) he.2.1 2
  have hκ3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ κ) he.2.1 3
  have hS : S ≤ U := by
    have hh := mul_le_mul_of_nonneg_right hκ2 hb.le
    dsimp [S, U]
    linarith
  have hκS : κ ^ 3 ≤ S := by dsimp [S]; nlinarith [mul_nonneg (sq_nonneg κ) hb.le, sq_nonneg b]
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hLL : L ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
  have h1 := mul_le_mul_of_nonneg_right hκS hL3
  have h2 := mul_le_mul_of_nonneg_left hLL hS0
  have h3 := mul_le_mul_of_nonneg_right hS hL3
  have hsum : ((T * (LongTails.Algorithms.GeneralizedLipschitzPilot.tuning κ δ).calls + K : ℕ) : ℝ) ≤ 2 ^ 66 * U * L ^ 3 := by
    push_cast
    change ((T * (LongTails.Algorithms.GeneralizedLipschitzPilot.tuning κ δ).calls : ℕ) : ℝ) ≤ _ at hburn
    push_cast at hburn
    nlinarith
  apply (Nat.cast_le (α := ℝ)).mp
  exact hsum.trans (Nat.le_ceil _)
lemma execution_cost {R G0 G1 ε : ℝ} (hR : 0 < R) (hG0 : 0 < G0) (hG1 : 0 ≤ G1) (hε : 0 < ε) :
    let G := max G1 (1 / R)
    let T := ⌈204800 * (R * G) ^ 2⌉₊
    let δ : ℝ := 1 / (100 * T)
    let D := 2 * R
    let e := ε / 20
    let τ := ⌈(96 * D * G) ^ 2⌉₊
    let α := min (1 / (16 * τ * (D * G))) (min ((e / (24 * D * G0)) ^ 2) (e / (1536 * τ * D * G0)))
    let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / e))⌉₊
    T * (LongTails.Algorithms.GeneralizedLipschitzPilot.tuning (R * G) δ).calls + K ≤
      ⌈2 ^ 66 * ((1 + R * G1) ^ 3 + (1 + R * G1) ^ 2 * (R * G0 / ε) + (R * G0 / ε) ^ 2) * (1 + Real.log (2 + R * G1 + R * G0 / ε)) ^ 3⌉₊ := by
  let G := max G1 (1 / R)
  have ht := physical_tuning (G := G) hR hG0 hε
  dsimp only at ht ⊢
  rw [ht.2.1, ht.2.2, ht.1]
  rw [normalized_parameters hR]
  exact total_cost (mul_nonneg hR.le hG1) (div_pos (mul_pos hR hG0) hε)

end LongTails.Proofs.GeneralizedLipschitzComplexity
