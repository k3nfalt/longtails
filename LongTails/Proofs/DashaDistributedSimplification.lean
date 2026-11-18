import LongTails.Proofs.DashaDistributedBudget

namespace LongTails.Proofs.DashaDistributedSimplification

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open DashaPrecisionCutoff DashaScalingParameters
open LongTails.Algorithms.DashaCyclic

variable {p : Params}

lemma variance_le_zero_precision (c : Choice p) : variance p c ≤ variance p { c with precision := 0 } := by
  have hq := multiplier_ge_one c
  have hp : (1 : ℝ) ≤ 4 ^ c.precision := one_le_pow₀ (by norm_num)
  have ha := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) < 1 by norm_num) hp
  norm_num at ha
  unfold variance
  norm_num only [pow_zero, div_one]
  nlinarith

lemma amortized_log (K Y : ℝ) (hK : 1 ≤ K) (hY : 0 ≤ Y) :
    K * Real.log (1 + Y) ≤ K * Real.log K + Y := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hY0 : 0 < 1 + Y := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hY0 hK0)
  rw [Real.log_div hY0.ne' hK0.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hK0.le
  have he : K * ((1 + Y) / K - 1) = 1 + Y - K := by
    field_simp
  rw [he] at hm
  nlinarith

lemma amortized_iterated_log (K Z : ℝ) (hK : 1 ≤ K) (hZ : 0 ≤ Z) :
    K * Real.log (1 + Real.log (1 + Z)) ≤ K * Real.log K + Real.log (1 + Z) :=
  amortized_log K (Real.log (1 + Z)) hK (Real.log_nonneg (by linarith))

lemma size_le_log (n : ℕ) : (Nat.size n : ℝ) ≤ 1 + 2 * Real.log (1 + (n : ℝ)) := by
  have hnlog : 0 ≤ Real.log (1 + (n : ℝ)) := Real.log_nonneg (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  cases hs : Nat.size n with
  | zero => simp only [Nat.cast_zero]; linarith
  | succ m =>
    have hm : 2 ^ m ≤ n := Nat.lt_size.mp (by omega)
    have hm' : (2 : ℝ) ^ m ≤ 1 + (n : ℝ) := by
      have hc : (2 : ℝ) ^ m ≤ (n : ℝ) := by exact_mod_cast hm
      linarith
    have hl := Real.log_le_log (pow_pos (show (0 : ℝ) < 2 by norm_num) m) hm'
    rw [Real.log_pow] at hl
    have htwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at htwo
    have hmul := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ m by positivity)
    push_cast
    nlinarith

lemma size_ceil_le_log (x : ℝ) (hx : 0 ≤ x) :
    (Nat.size ⌈x⌉₊ : ℝ) ≤ 1 + 2 * Real.log (2 + x) := by
  have hc := Nat.ceil_lt_add_one hx
  have hl := Real.log_le_log (show (0 : ℝ) < 1 + (⌈x⌉₊ : ℝ) by positivity)
    (show 1 + (⌈x⌉₊ : ℝ) ≤ 2 + x by linarith)
  exact (size_le_log ⌈x⌉₊).trans (by linarith)

lemma double_size_ceil_le_log (x : ℝ) (hx : 0 ≤ x) :
    (Nat.size (Nat.size ⌈x⌉₊) : ℝ) ≤ 3 + 2 * Real.log (1 + Real.log (2 + x)) := by
  have hi := size_ceil_le_log x hx
  have hl := Real.log_le_log (show (0 : ℝ) < 1 + (Nat.size ⌈x⌉₊ : ℝ) by positivity)
    (show 1 + (Nat.size ⌈x⌉₊ : ℝ) ≤ 2 * (1 + Real.log (2 + x)) by linarith)
  have hlog : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hb := size_le_log (Nat.size ⌈x⌉₊)
  linarith

open LongTails.Algorithms.DashaDistributed LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaDistributedTrackedParameters

lemma tracked_roundBits_le_log (c : Choice p) (initializer : Option (Choice p))
    (modularInitialization : Bool) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (roundBits p (trackedConfig p c initializer modularInitialization) : ℝ) ≤
      ((c.block.val : ℝ) + 1) * (c.precision + 9 +
        2 * Real.log (1 + (roundCount p c initializer : ℝ)) +
        2 * Real.log (1 + Real.log (2 + trackingInputBound p c initializer))) := by
  have hb := (DashaDistributedBudget.tracked_roundBits_sum_comparison c initializer
    modularInitialization hL hH hG hε).1
  have hU := (DashaDistributedBudget.tracking_range_growth c initializer hL hH hG hε).1
  have hK := size_le_log (roundCount p c initializer)
  have he := double_size_ceil_le_log (trackingInputBound p c initializer) (by linarith)
  have hb' : (roundBits p (trackedConfig p c initializer modularInitialization) : ℝ) ≤
      ((c.block.val : ℝ) + 1) * ((c.precision : ℝ) + Nat.size (roundCount p c initializer) +
        Nat.size (Nat.size ⌈trackingInputBound p c initializer⌉₊) + 5) := by exact_mod_cast hb
  exact hb'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

lemma variance_le_three_multiplier (c : Choice p) :
    variance p c ≤ 3 * multiplier c.block - 1 := by
  have h := variance_le_zero_precision c
  norm_num [variance] at h ⊢
  exact h

lemma factor_le_five_multiplier (c : Choice p) :
    factor (variance p c) ≤ 5 * multiplier c.block := by
  have hq := multiplier_ge_one c
  have hq0 : 0 ≤ multiplier c.block := by linarith
  have hv := variance_le_three_multiplier c
  apply (factor_mono (variance_nonneg c) (show variance p c ≤ 3 * multiplier c.block by linarith)).trans
  apply (sq_le_sq₀ (factor_nonneg _) (by positivity)).mp
  rw [factor_sq (by positivity)]
  have hp := mul_nonneg hq0 (show 0 ≤ multiplier c.block - 1 by linarith)
  nlinarith

lemma denominator_le_multiplier (c : Choice p) (hH : 0 ≤ p.Lhat) :
    denominator p c ≤ min p.L p.Lhat + 5 * p.Lhat * multiplier c.block / Real.sqrt (p.n : ℝ) := by
  rw [denominator_factor]
  have hm := mul_le_mul_of_nonneg_left (factor_le_five_multiplier c)
    (show 0 ≤ p.Lhat / Real.sqrt (p.n : ℝ) by positivity)
  calc
    _ ≤ min p.L p.Lhat + (p.Lhat / Real.sqrt (p.n : ℝ)) * (5 * multiplier c.block) := add_le_add le_rfl hm
    _ = _ := by ring

lemma initialPenalty_le_multipliers (c initializer : Choice p) :
    initialPenalty p c initializer ≤
      36 * multiplier c.block * multiplier initializer.block * p.G ^ 2 / (p.n : ℝ) := by
  have hv := variance_le_three_multiplier c
  have hv0 := variance_nonneg c
  have hi := variance_le_three_multiplier initializer
  have hi0 := variance_nonneg initializer
  have hq := multiplier_ge_one c
  have hq0 : 0 ≤ 12 * multiplier c.block := by positivity
  have hm := mul_le_mul (show 4 * variance p c + 1 ≤ 12 * multiplier c.block by linarith)
    (show variance p initializer ≤ 3 * multiplier initializer.block by linarith) hi0 hq0
  unfold initialPenalty
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hg := mul_le_mul_of_nonneg_right hm (sq_nonneg p.G)
  nlinarith only [hg]

lemma sparseIterations_le_multipliers (c initializer : Choice p)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    (sparseIterations p c initializer : ℝ) ≤
      160 * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2 +
        p.Lhat * p.Δ * multiplier c.block / (p.ε ^ 2 * Real.sqrt (p.n : ℝ)) +
        multiplier c.block * multiplier initializer.block * p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) := by
  have hD0 := denominator_pos c hL hH
  have hv0 := variance_nonneg c
  have hi0 := variance_nonneg initializer
  have hP0 : 0 ≤ initialPenalty p c initializer := by unfold initialPenalty; positivity
  have harg : 0 ≤ (32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2 := by positivity
  have hceil := (Nat.ceil_lt_add_one harg).le
  have hD := mul_le_mul_of_nonneg_left (denominator_le_multiplier c hH.le)
    (show 0 ≤ 32 * p.Δ by positivity)
  have hP := mul_le_mul_of_nonneg_left (initialPenalty_le_multipliers c initializer)
    (show (0 : ℝ) ≤ 4 by norm_num)
  have hab := div_le_div_of_nonneg_right (add_le_add hD hP) (sq_nonneg p.ε)
  have hq := multiplier_ge_one c
  have hq0 := multiplier_ge_one initializer
  have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
  have hz : 0 ≤ multiplier c.block * multiplier initializer.block * p.G ^ 2 /
      ((p.n : ℝ) * p.ε ^ 2) := by positivity
  change ((1 + ⌈(32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2⌉₊ : ℕ) : ℝ) ≤ _
  push_cast
  have he :
      160 * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2 +
        p.Lhat * p.Δ * multiplier c.block / (p.ε ^ 2 * Real.sqrt (p.n : ℝ)) +
        multiplier c.block * multiplier initializer.block * p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) -
      (2 + (32 * p.Δ * (min p.L p.Lhat + 5 * p.Lhat * multiplier c.block / Real.sqrt (p.n : ℝ)) +
        4 * (36 * multiplier c.block * multiplier initializer.block * p.G ^ 2 / (p.n : ℝ))) / p.ε ^ 2) =
      158 + 128 * (min p.L p.Lhat * p.Δ / p.ε ^ 2) +
        16 * (multiplier c.block * multiplier initializer.block * p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) := by
    ring
  linarith

lemma multiplier_le_dimension (c : Choice p) : multiplier c.block ≤ (p.d : ℝ) := by
  unfold multiplier
  apply (div_le_iff₀ (by positivity)).mpr
  have hd : (0 : ℝ) ≤ p.d := by positivity
  have hk : (0 : ℝ) ≤ c.block.val := by positivity
  nlinarith

lemma spacing_lower_bound (c : Choice p) (hε : 0 < p.ε) :
    p.ε * Real.sqrt (p.n : ℝ) / (32 * (p.d : ℝ)) ≤ spacing p c := by
  have hv := variance_le_three_multiplier c
  have hq := multiplier_le_dimension c
  have hv0 := variance_nonneg c
  have hd : (0 : ℝ) < p.d := by positivity
  have hden : 256 * (p.d : ℝ) * (variance p c + 1) ≤ 1024 * (p.d : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left (show variance p c + 1 ≤ 3 * (p.d : ℝ) by linarith)
      (show 0 ≤ 256 * (p.d : ℝ) by positivity)
    nlinarith
  have hb := div_le_div_of_nonneg_left (show 0 ≤ p.ε ^ 2 * (p.n : ℝ) by positivity)
    (show 0 < 256 * (p.d : ℝ) * (variance p c + 1) by positivity) hden
  apply (sq_le_sq₀ (by positivity) (spacing_pos c hε).le).mp
  rw [spacing_sq]
  convert hb using 1
  norm_num [div_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ p.n by positivity)]

lemma divide_by_spacing_le (c : Choice p) (hε : 0 < p.ε) (Y : ℝ) (hY : 0 ≤ Y) :
    Y / spacing p c ≤ 32 * (p.d : ℝ) * Y / (p.ε * Real.sqrt (p.n : ℝ)) := by
  have hb := div_le_div_of_nonneg_left hY
    (show 0 < p.ε * Real.sqrt (p.n : ℝ) / (32 * (p.d : ℝ)) by positivity)
    (spacing_lower_bound c hε)
  calc
    _ ≤ Y / (p.ε * Real.sqrt (p.n : ℝ) / (32 * (p.d : ℝ))) := hb
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring

lemma stepSize_le_gap (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hε : 0 < p.ε)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    stepSize p c ≤ 2 * p.Δ / p.ε ^ 2 := by
  have hLeffPos : 0 < min p.L p.Lhat := lt_min hL hH
  have hD := denominator_pos c hL hH
  have hbase : min p.L p.Lhat ≤ denominator p c := by
    unfold denominator
    exact le_add_of_nonneg_right (mul_nonneg hH.le (Real.sqrt_nonneg _))
  have hη : stepSize p c ≤ 1 / min p.L p.Lhat := by
    unfold stepSize
    exact div_le_div_of_nonneg_left (by norm_num) hLeffPos (by linarith)
  have hi : 1 / min p.L p.Lhat ≤ 2 * p.Δ / p.ε ^ 2 := by
    apply (div_le_div_iff₀ hLeffPos (sq_pos_of_pos hε)).mpr
    nlinarith
  exact hη.trans hi

lemma exists_block_between (d : ℕ+) (t : ℝ) (ht : 0 ≤ t) :
    ∃ k : Fin d, min (d : ℝ) t ≤ (k.val : ℝ) + 1 ∧ (k.val : ℝ) + 1 ≤ 1 + t := by
  let K : ℕ := min (d : ℕ) (max 1 ⌈t⌉₊)
  have hK : 1 ≤ K := le_min d.pos (le_max_left _ _)
  have hKd : K ≤ d := min_le_left _ _
  let k : Fin d := ⟨K - 1, by omega⟩
  have hk : (k.val : ℝ) + 1 = (K : ℝ) := by
    have he : k.val + 1 = K := by dsimp [k]; omega
    exact_mod_cast he
  refine ⟨k, ?_, ?_⟩ <;> rw [hk]
  · have he : (K : ℝ) = min (d : ℝ) (max 1 (⌈t⌉₊ : ℝ)) := by simp [K]
    rw [he]
    exact min_le_min le_rfl ((Nat.le_ceil t).trans (le_max_right _ _))
  · have he : (K : ℝ) ≤ max 1 (⌈t⌉₊ : ℝ) := by exact_mod_cast (min_le_right (d : ℕ) (max 1 ⌈t⌉₊))
    exact he.trans (max_le (by linarith) (by linarith [Nat.ceil_lt_add_one ht]))

lemma two_pow_size_ceil_ge (u : ℝ) : u ≤ (2 : ℝ) ^ Nat.size ⌈u⌉₊ := by
  have h : (⌈u⌉₊ : ℝ) < (2 : ℝ) ^ Nat.size ⌈u⌉₊ := by exact_mod_cast Nat.lt_size_self ⌈u⌉₊
  exact (Nat.le_ceil u).trans h.le

lemma four_pow_size_ceil_ge (u : ℝ) : u ≤ (4 : ℝ) ^ Nat.size ⌈u⌉₊ := by
  exact (two_pow_size_ceil_ge u).trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)

lemma full_multiplier (c : Choice p) (hk : c.block.val + 1 = p.d) : multiplier c.block = 1 := by
  unfold multiplier
  have hc : (c.block.val : ℝ) + 1 = (p.d : ℝ) := by exact_mod_cast hk
  rw [hc]
  exact div_self (by positivity)

lemma full_variance (c : Choice p) (hk : c.block.val + 1 = p.d) :
    variance p c = 2 / (4 : ℝ) ^ c.precision := by
  unfold variance
  rw [full_multiplier c hk]
  ring

lemma full_factor_le (c : Choice p) (hk : c.block.val + 1 = p.d) :
    factor (variance p c) ≤ 4 / (2 : ℝ) ^ c.precision := by
  have hv0 := variance_nonneg c
  have hv := variance_le_three_multiplier c
  rw [full_multiplier c hk] at hv
  have hm := mul_le_mul_of_nonneg_left (show 2 * variance p c + 1 ≤ 5 by linarith) hv0
  have hp : (4 / (2 : ℝ) ^ c.precision) ^ 2 = 16 / (4 : ℝ) ^ c.precision := by
    rw [div_pow, power_four c.precision]
    norm_num
  apply (sq_le_sq₀ (factor_nonneg _) (by positivity)).mp
  rw [factor_sq hv0, hp]
  rw [full_variance c hk] at hm ⊢
  have hpos : 0 ≤ 1 / (4 : ℝ) ^ c.precision := by positivity
  ring_nf at hm hpos ⊢
  nlinarith only [hm, hpos]

lemma full_denominator_le (c : Choice p) (hk : c.block.val + 1 = p.d) (hH : 0 ≤ p.Lhat) :
    denominator p c ≤ min p.L p.Lhat +
      4 * p.Lhat / (Real.sqrt (p.n : ℝ) * (2 : ℝ) ^ c.precision) := by
  rw [denominator_factor]
  have hm := mul_le_mul_of_nonneg_left (full_factor_le c hk)
    (show 0 ≤ p.Lhat / Real.sqrt (p.n : ℝ) by positivity)
  calc
    _ ≤ min p.L p.Lhat + (p.Lhat / Real.sqrt (p.n : ℝ)) * (4 / (2 : ℝ) ^ c.precision) := add_le_add le_rfl hm
    _ = _ := by ring

lemma full_initialPenalty_le (c initializer : Choice p) (hk : initializer.block.val + 1 = p.d) :
    initialPenalty p c initializer ≤
      24 * multiplier c.block * p.G ^ 2 / ((p.n : ℝ) * (4 : ℝ) ^ initializer.precision) := by
  have hv := variance_le_three_multiplier c
  have hm := mul_le_mul_of_nonneg_right (show 4 * variance p c + 1 ≤ 12 * multiplier c.block by linarith)
    (show 0 ≤ (2 / (4 : ℝ) ^ initializer.precision) * p.G ^ 2 / (p.n : ℝ) by positivity)
  unfold initialPenalty
  rw [full_variance initializer hk]
  convert hm using 1 <;> ring

lemma sparseIterations_le_of_bounds (c initializer : Choice p)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ)
    (D E : ℝ) (hD : denominator p c ≤ D) (hE : initialPenalty p c initializer ≤ E) :
    (sparseIterations p c initializer : ℝ) ≤ 2 + (32 * p.Δ * D + 4 * E) / p.ε ^ 2 := by
  have hd := denominator_pos c hL hH
  have hv := variance_nonneg c
  have hi := variance_nonneg initializer
  have hP : 0 ≤ initialPenalty p c initializer := by unfold initialPenalty; positivity
  have harg : 0 ≤ (32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2 := by positivity
  have hc := (Nat.ceil_lt_add_one harg).le
  have hm := div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hD (show 0 ≤ 32 * p.Δ by positivity))
      (mul_le_mul_of_nonneg_left hE (show (0 : ℝ) ≤ 4 by norm_num))) (sq_nonneg p.ε)
  change ((1 + ⌈(32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2⌉₊ : ℕ) : ℝ) ≤ _
  push_cast
  linarith

lemma full_initial_iterations_le (c initializer : Choice p) (hk : initializer.block.val + 1 = p.d)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) :
    (sparseIterations p c initializer : ℝ) ≤
      160 * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2 +
        p.Lhat * p.Δ * multiplier c.block / (p.ε ^ 2 * Real.sqrt (p.n : ℝ)) +
        multiplier c.block * p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2 * (4 : ℝ) ^ initializer.precision)) := by
  have hb := sparseIterations_le_of_bounds c initializer hL hH hΔ _ _
    (denominator_le_multiplier c hH.le) (full_initialPenalty_le c initializer hk)
  have hq := multiplier_ge_one c
  have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
  have hz : 0 ≤ multiplier c.block * p.G ^ 2 /
      ((p.n : ℝ) * p.ε ^ 2 * (4 : ℝ) ^ initializer.precision) := by positivity
  ring_nf at hb ha hz ⊢
  linarith

lemma full_iterations_le (c initializer : Choice p)
    (hk : c.block.val + 1 = p.d) (hi : initializer.block.val + 1 = p.d)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) :
    (sparseIterations p c initializer : ℝ) ≤
      128 * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2 +
        p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ) * (2 : ℝ) ^ c.precision) +
        p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2 * (4 : ℝ) ^ initializer.precision)) := by
  have hP := full_initialPenalty_le c initializer hi
  rw [full_multiplier c hk] at hP
  have hb := sparseIterations_le_of_bounds c initializer hL hH hΔ _ _
    (full_denominator_le c hk hH.le) hP
  have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
  have hz : 0 ≤ p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2 * (4 : ℝ) ^ initializer.precision) := by positivity
  ring_nf at hb ha hz ⊢
  linarith

lemma initialEnvelope_div_le (c : Choice p) (initializer : Option (Choice p))
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    trackingInitialEnvelope p c initializer / spacing p c ≤
      globalInitialBound p / spacing p c + 3 * (p.d : ℝ) * (p.G / spacing p c) +
        3 * Real.sqrt (p.d : ℝ) := by
  have hρ := spacing_pos c hε
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  cases initializer with
  | none =>
    have he : trackingInitialEnvelope p c none / spacing p c =
        globalInitialBound p / spacing p c + 3 * Real.sqrt (p.d : ℝ) := by
      unfold trackingInitialEnvelope
      dsimp only
      field_simp
      ring
    rw [he]
    have hg : 0 ≤ 3 * (p.d : ℝ) * (p.G / spacing p c) := by positivity
    linarith
  | some initializer =>
    have hq := multiplier_le_dimension initializer
    have hm := mul_le_mul_of_nonneg_right (show 2 * multiplier initializer.block + 1 ≤ 3 * (p.d : ℝ) by linarith)
      (show 0 ≤ p.G / spacing p c by positivity)
    have he : trackingInitialEnvelope p c (some initializer) / spacing p c =
        globalInitialBound p / spacing p c + (2 * multiplier initializer.block + 1) * (p.G / spacing p c) +
          3 * Real.sqrt (p.d : ℝ) := by
      unfold trackingInitialEnvelope
      dsimp only
      field_simp
    rw [he]
    linarith

lemma trackingInput_le_simple (c : Choice p) (initializer : Option (Choice p))
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG : 0 ≤ p.G) (hε : 0 < p.ε)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    trackingInputBound p c initializer ≤
      (p.d : ℝ) * (1 + 2 * Real.sqrt (p.n : ℝ) * p.Lhat * p.Δ / p.ε ^ 2) *
        (32 * (p.d : ℝ) * globalInitialBound p / (p.ε * Real.sqrt (p.n : ℝ)) +
          96 * (p.d : ℝ) ^ 2 * p.G / (p.ε * Real.sqrt (p.n : ℝ)) + 3 * Real.sqrt (p.d : ℝ)) := by
  have hρ := spacing_pos c hε
  have hη := stepSize_pos c hL hH
  have hJ0 : 0 ≤ globalInitialBound p := by unfold globalInitialBound; positivity
  have hR0 : 0 ≤ trackingInitialEnvelope p c initializer := by
    unfold trackingInitialEnvelope
    cases initializer <;> simp only [multiplier] <;> positivity
  have hJ := divide_by_spacing_le c hε (globalInitialBound p) hJ0
  have hGG := divide_by_spacing_le c hε p.G hG
  have hR : trackingInitialEnvelope p c initializer / spacing p c ≤
      32 * (p.d : ℝ) * globalInitialBound p / (p.ε * Real.sqrt (p.n : ℝ)) +
        96 * (p.d : ℝ) ^ 2 * p.G / (p.ε * Real.sqrt (p.n : ℝ)) + 3 * Real.sqrt (p.d : ℝ) := by
    apply (initialEnvelope_div_le c initializer hG hε).trans
    have hm := mul_le_mul_of_nonneg_left hGG (show 0 ≤ 3 * (p.d : ℝ) by positivity)
    have hs := add_le_add (add_le_add hJ hm) (le_refl (3 * Real.sqrt (p.d : ℝ)))
    convert hs using 1
    ring
  have ht := mul_le_mul_of_nonneg_left (stepSize_le_gap c hL hH hε hgap)
    (show 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat by positivity)
  have hfactor : multiplier c.block * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) ≤
      (p.d : ℝ) * (1 + 2 * Real.sqrt (p.n : ℝ) * p.Lhat * p.Δ / p.ε ^ 2) := by
    apply mul_le_mul (multiplier_le_dimension c) _ (by positivity) (by positivity)
    convert add_le_add le_rfl ht using 1
    ring
  have hfactor0 : 0 ≤ (p.d : ℝ) * (1 + 2 * Real.sqrt (p.n : ℝ) * p.Lhat * p.Δ / p.ε ^ 2) :=
    (show 0 ≤ multiplier c.block * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) by
      unfold multiplier
      positivity).trans hfactor
  calc
    _ = (multiplier c.block * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c)) *
        (trackingInitialEnvelope p c initializer / spacing p c) := by unfold trackingInputBound; ring
    _ ≤ _ := mul_le_mul hfactor hR (div_nonneg hR0 hρ.le) hfactor0

lemma globalInitialBound_scaled (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    globalInitialBound p / (p.ε * Real.sqrt (p.n : ℝ)) ≤
      (3 / 2 : ℝ) * Real.sqrt (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2) := by
  have hJ0 : 0 ≤ globalInitialBound p := by unfold globalInitialBound; positivity
  have hJ := min_le_right p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ))
  have hJ2 : globalInitialBound p ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ := by
    have hs := (sq_le_sq₀ hJ0 (Real.sqrt_nonneg _)).mpr hJ
    rwa [Real.sq_sqrt (by positivity)] at hs
  have hn : (1 : ℝ) ≤ Real.sqrt (p.n : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p.n by exact_mod_cast p.n.pos)
  have hdiv : globalInitialBound p / (p.ε * Real.sqrt (p.n : ℝ)) ≤ globalInitialBound p / p.ε :=
    div_le_div_of_nonneg_left hJ0 hε (by nlinarith)
  apply hdiv.trans
  have hs : (globalInitialBound p / p.ε) ^ 2 ≤ 2 * (min p.L p.Lhat * p.Δ / p.ε ^ 2) := by
    rw [div_pow]
    have hb := div_le_div_of_nonneg_right hJ2 (sq_nonneg p.ε)
    convert hb using 1
    ring
  have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
  have hr := Real.sq_sqrt (show 0 ≤ 1 + min p.L p.Lhat * p.Δ / p.ε ^ 2 by positivity)
  apply (sq_le_sq₀ (div_nonneg hJ0 hε.le) (by positivity)).mp
  nlinarith

lemma scaled_G_eq_sqrt (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    p.G / (p.ε * Real.sqrt (p.n : ℝ)) = Real.sqrt (p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) := by
  have he : (p.G / (p.ε * Real.sqrt (p.n : ℝ))) ^ 2 = p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [← he, Real.sqrt_sq (by positivity)]

lemma range_product_le (n d N X Z : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) :
    d * (1 + 2 * n * X) * (48 * d * Real.sqrt N + 96 * d ^ 2 * Real.sqrt Z + 3 * Real.sqrt d) ≤
      512 * (n * d) ^ 3 * (1 + X) * (1 + N) * (1 + Z) := by
  have hn0 : 0 ≤ n := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hdsq : d ≤ d ^ 2 := by nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd)]
  have hdroot : Real.sqrt d ≤ d := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hd0).mp
    rw [Real.sq_sqrt hd0]
    exact hdsq
  have hNroot : Real.sqrt N ≤ N := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hN0).mp
    rw [Real.sq_sqrt hN0]
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hN)]
  have hZroot : Real.sqrt Z ≤ 1 + Z := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hZ]
    nlinarith [sq_nonneg Z]
  have h1 := mul_le_mul_of_nonneg_left
    (mul_le_mul hdsq hNroot (Real.sqrt_nonneg _) (sq_nonneg d)) (show (0 : ℝ) ≤ 48 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hZroot (show 0 ≤ 96 * d ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left (hdroot.trans hdsq) (show (0 : ℝ) ≤ 3 by norm_num)
  have hc := mul_le_mul_of_nonneg_left
    (show 48 * N + 96 * (1 + Z) + 3 ≤ 147 * (1 + N + Z) by linarith) (sq_nonneg d)
  have hR : 48 * d * Real.sqrt N + 96 * d ^ 2 * Real.sqrt Z + 3 * Real.sqrt d ≤
      147 * d ^ 2 * (1 + N + Z) := by nlinarith only [h1, h2, h3, hc]
  have hf := mul_le_mul_of_nonneg_left
    (show 1 + 2 * n * X ≤ 3 * n * (1 + X) by nlinarith [mul_nonneg hn0 hX]) hd0
  have hfactor : d * (1 + 2 * n * X) ≤ 3 * n * d * (1 + X) := by nlinarith only [hf]
  have hncube : n ≤ n ^ 3 := by
    have hp := mul_le_mul_of_nonneg_left (one_le_pow₀ hn : (1 : ℝ) ≤ n ^ 2) hn0
    nlinarith only [hp]
  have hmn : 441 * n ≤ 512 * n ^ 3 := by nlinarith [pow_nonneg hn0 3]
  have hpre := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmn (pow_nonneg hd0 3)) (show 0 ≤ 1 + X by positivity)
  have hsum : 1 + N + Z ≤ (1 + N) * (1 + Z) := by nlinarith [mul_nonneg hN0 hZ]
  calc
    _ ≤ (3 * n * d * (1 + X)) * (147 * d ^ 2 * (1 + N + Z)) :=
      mul_le_mul hfactor hR (by positivity) (by positivity)
    _ = 441 * n * d ^ 3 * (1 + X) * (1 + N + Z) := by ring
    _ ≤ 512 * n ^ 3 * d ^ 3 * (1 + X) * ((1 + N) * (1 + Z)) :=
      mul_le_mul hpre hsum (by positivity) (by positivity)
    _ = _ := by ring

lemma trackingInput_le_scaled_noise (c : Choice p) (initializer : Option (Choice p)) (Z : ℝ)
    (hZ : 0 ≤ Z) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (hnoise : ∀ c₀, initializer = some c₀ → p.G / (p.ε * Real.sqrt (p.n : ℝ)) ≤ Real.sqrt Z) :
    trackingInputBound p c initializer ≤ 512 * ((p.n : ℝ) * p.d) ^ 3 *
      (1 + p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ))) *
      (2 + min p.L p.Lhat * p.Δ / p.ε ^ 2) * (1 + Z) := by
  let N := 1 + min p.L p.Lhat * p.Δ / p.ε ^ 2
  let X := p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ))
  have hN : 1 ≤ N := by
    dsimp [N]
    have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
    linarith
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  have hρ := spacing_pos c hε
  have hη := stepSize_pos c hL hH
  have hJ0 : 0 ≤ globalInitialBound p := by unfold globalInitialBound; positivity
  have hJ := globalInitialBound_scaled hL hH hΔ hG hε
  change globalInitialBound p / (p.ε * Real.sqrt (p.n : ℝ)) ≤ (3 / 2 : ℝ) * Real.sqrt N at hJ
  have hJρ : globalInitialBound p / spacing p c ≤ 48 * (p.d : ℝ) * Real.sqrt N := by
    apply (divide_by_spacing_le c hε (globalInitialBound p) hJ0).trans
    have hm := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 32 * (p.d : ℝ) by positivity)
    convert hm using 1 <;> ring
  have hR : trackingInitialEnvelope p c initializer / spacing p c ≤
      48 * (p.d : ℝ) * Real.sqrt N + 96 * (p.d : ℝ) ^ 2 * Real.sqrt Z + 3 * Real.sqrt (p.d : ℝ) := by
    cases initializer with
    | none =>
      have he : trackingInitialEnvelope p c none / spacing p c =
          globalInitialBound p / spacing p c + 3 * Real.sqrt (p.d : ℝ) := by
        unfold trackingInitialEnvelope
        dsimp only
        field_simp
        ring
      rw [he]
      have hz0 : 0 ≤ 96 * (p.d : ℝ) ^ 2 * Real.sqrt Z := by positivity
      linarith
    | some initializer =>
      have hg := mul_le_mul_of_nonneg_left (hnoise initializer rfl)
        (show 0 ≤ 32 * (p.d : ℝ) by positivity)
      have hgρ : p.G / spacing p c ≤ 32 * (p.d : ℝ) * Real.sqrt Z := by
        apply (divide_by_spacing_le c hε p.G hG).trans
        convert hg using 1
        ring
      have hm := mul_le_mul_of_nonneg_left hgρ (show 0 ≤ 3 * (p.d : ℝ) by positivity)
      have hb := initialEnvelope_div_le c (some initializer) hG hε
      nlinarith only [hb, hJρ, hm]
  have hR0 : 0 ≤ trackingInitialEnvelope p c initializer := by
    unfold trackingInitialEnvelope
    cases initializer <;> simp only [multiplier] <;> positivity
  have ht := mul_le_mul_of_nonneg_left (stepSize_le_gap c hL hH hε hgap)
    (show 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat by positivity)
  have hfactor : multiplier c.block * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) ≤
      (p.d : ℝ) * (1 + 2 * Real.sqrt (p.n : ℝ) * p.Lhat * p.Δ / p.ε ^ 2) := by
    apply mul_le_mul (multiplier_le_dimension c) _ (by positivity) (by positivity)
    convert add_le_add le_rfl ht using 1
    ring
  have hroot : (p.n : ℝ) / Real.sqrt (p.n : ℝ) = Real.sqrt (p.n : ℝ) := by
    apply (div_eq_iff (show Real.sqrt (p.n : ℝ) ≠ 0 by positivity)).mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ p.n by positivity)]
  have hXe : 2 * Real.sqrt (p.n : ℝ) * p.Lhat * p.Δ / p.ε ^ 2 = 2 * (p.n : ℝ) * X := by
    calc
      _ = 2 * (p.Lhat * p.Δ / p.ε ^ 2) * ((p.n : ℝ) / Real.sqrt (p.n : ℝ)) := by rw [hroot]; ring
      _ = _ := by dsimp [X]; ring
  have hb : trackingInputBound p c initializer ≤
      512 * ((p.n : ℝ) * p.d) ^ 3 * (1 + X) * (1 + N) * (1 + Z) := by
    calc
      _ = (multiplier c.block * (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c)) *
          (trackingInitialEnvelope p c initializer / spacing p c) := by unfold trackingInputBound; ring
      _ ≤ ((p.d : ℝ) * (1 + 2 * Real.sqrt (p.n : ℝ) * p.Lhat * p.Δ / p.ε ^ 2)) *
          (48 * (p.d : ℝ) * Real.sqrt N + 96 * (p.d : ℝ) ^ 2 * Real.sqrt Z + 3 * Real.sqrt (p.d : ℝ)) :=
        mul_le_mul hfactor hR (div_nonneg hR0 hρ.le) (by positivity)
      _ = (p.d : ℝ) * (1 + 2 * (p.n : ℝ) * X) *
          (48 * (p.d : ℝ) * Real.sqrt N + 96 * (p.d : ℝ) ^ 2 * Real.sqrt Z + 3 * Real.sqrt (p.d : ℝ)) := by rw [hXe]
      _ ≤ _ := range_product_le _ _ _ _ _ hn hd hN hX hZ
  convert hb using 1
  dsimp [N, X]
  ring

lemma trackingInput_le_normalized (c : Choice p) (initializer : Option (Choice p))
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    trackingInputBound p c initializer ≤ 512 * ((p.n : ℝ) * p.d) ^ 3 *
      (1 + p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ))) *
      (2 + min p.L p.Lhat * p.Δ / p.ε ^ 2) * (1 + p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) :=
  trackingInput_le_scaled_noise c initializer _ (by positivity) hL hH hΔ hG hε hgap
    (fun _ _ => (scaled_G_eq_sqrt hG hε).le)

lemma trackingInput_none_le_normalized (c : Choice p)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    trackingInputBound p c none ≤ 512 * ((p.n : ℝ) * p.d) ^ 3 *
      (1 + p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ))) *
      (2 + min p.L p.Lhat * p.Δ / p.ε ^ 2) := by
  simpa only [add_zero, mul_one] using
    trackingInput_le_scaled_noise c none 0 (by norm_num) hL hH hΔ hG hε hgap (by simp)

lemma iterations_le_sparseIterations (c initializer : Choice p) :
    (iterations p c : ℕ) ≤ (sparseIterations p c initializer : ℕ) := by
  have hv := variance_nonneg c
  have hi := variance_nonneg initializer
  have hP : 0 ≤ initialPenalty p c initializer := by unfold initialPenalty; positivity
  change 1 + ⌈32 * p.Δ * denominator p c / p.ε ^ 2⌉₊ ≤
    1 + ⌈(32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2⌉₊
  apply Nat.add_le_add_left
  apply Nat.ceil_le_ceil
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg p.ε)

end LongTails.Proofs.DashaDistributedSimplification
