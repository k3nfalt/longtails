import LongTails.Proofs.DashaDistributedSimplification

namespace LongTails.Proofs.DashaDistributedLogBounds

noncomputable def logScale (w N X : ℝ) : ℝ :=
  2 + Real.log (N + X) + Real.log (1 + Real.log w)

lemma one_add_four_le_product (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    1 + a + b + c + d ≤ (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  calc
    _ ≤ (1 + a + b + c) * (1 + d) := by nlinarith [mul_nonneg (show 0 ≤ a + b + c by positivity) hd]
    _ ≤ ((1 + a + b) * (1 + c)) * (1 + d) :=
      mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (add_nonneg ha hb) hc]) (by positivity)
    _ ≤ ((1 + a) * (1 + b) * (1 + c)) * (1 + d) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by nlinarith [mul_nonneg ha hb]) (by positivity)) (by positivity)

lemma loglog_range_le (w N X Z U : ℝ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hU : 1 ≤ U)
    (hbound : U ≤ 512 * w ^ 3 * (1 + X) * (1 + N) * (1 + Z)) :
    Real.log (1 + Real.log (2 + U)) ≤
      3 * (2 + Real.log (N + X) + Real.log (1 + Real.log w)) + Real.log (1 + Real.log (1 + Z)) := by
  have hw0 : 0 < w := by linarith
  have hN0 : 0 < N := by linarith
  have hU0 : 0 < U := by linarith
  have ha : 0 ≤ Real.log w := Real.log_nonneg hw
  have hb : 0 ≤ Real.log (1 + X) := Real.log_nonneg (by linarith)
  have hc : 0 ≤ Real.log (1 + N) := Real.log_nonneg (by linarith)
  have hd : 0 ≤ Real.log (1 + Z) := Real.log_nonneg (by linarith)
  have hn : 0 ≤ Real.log (N + X) := Real.log_nonneg (by linarith)
  have hi : 0 ≤ Real.log (1 + Real.log w) := Real.log_nonneg (by linarith)
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h2048 : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = (2 : ℝ) ^ 11 by norm_num, Real.log_pow]
    norm_num
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hbig : 2 + U ≤ 2048 * w ^ 3 * (1 + X) * (1 + N) * (1 + Z) := by
    nlinarith only [hbound, hU]
  have hlog := Real.log_le_log (show 0 < 2 + U by positivity) hbig
  have he : Real.log (2048 * w ^ 3 * (1 + X) * (1 + N) * (1 + Z)) =
      11 * Real.log 2 + 3 * Real.log w + Real.log (1 + X) + Real.log (1 + N) + Real.log (1 + Z) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow, h2048]
    norm_num
  rw [he] at hlog
  have hp := one_add_four_le_product (Real.log w) (Real.log (1 + X)) (Real.log (1 + N)) (Real.log (1 + Z)) ha hb hc hd
  have hp16 := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 16 by norm_num)
  have hprod : 1 + Real.log (2 + U) ≤
      16 * (1 + Real.log w) * (1 + Real.log (1 + X)) * (1 + Real.log (1 + N)) * (1 + Real.log (1 + Z)) := by
    nlinarith only [hlog, htwo, hp16, ha, hb, hc, hd]
  have hlogU : 0 ≤ Real.log (2 + U) := Real.log_nonneg (by linarith)
  have hout := Real.log_le_log (show 0 < 1 + Real.log (2 + U) by positivity) hprod
  have heout : Real.log (16 * (1 + Real.log w) * (1 + Real.log (1 + X)) *
      (1 + Real.log (1 + N)) * (1 + Real.log (1 + Z))) =
      4 * Real.log 2 + Real.log (1 + Real.log w) + Real.log (1 + Real.log (1 + X)) +
        Real.log (1 + Real.log (1 + N)) + Real.log (1 + Real.log (1 + Z)) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [h16]
  rw [heout] at hout
  have hb1 : Real.log (1 + Real.log (1 + X)) ≤ Real.log (1 + X) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log (1 + X) by positivity)
    linarith
  have hb2 := Real.log_le_log (show 0 < 1 + X by positivity) (show 1 + X ≤ N + X by linarith)
  have hc1 : Real.log (1 + Real.log (1 + N)) ≤ Real.log (1 + N) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log (1 + N) by positivity)
    linarith
  have hc2 := Real.log_le_log (show 0 < 1 + N by positivity) (show 1 + N ≤ 2 * (N + X) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hc2
  linarith

lemma two_le_logScale (w N X : ℝ) (hw : 1 ≤ w) (hN : 1 ≤ N) (hX : 0 ≤ X) :
    2 ≤ logScale w N X := by
  have hwlog := Real.log_nonneg hw
  have hi := Real.log_nonneg (show 1 ≤ 1 + Real.log w by linarith)
  have hn := Real.log_nonneg (show 1 ≤ N + X by linarith)
  unfold logScale
  linarith

lemma size_ceil_le_log_one_add (x : ℝ) (hx : 0 ≤ x) :
    (Nat.size ⌈x⌉₊ : ℝ) ≤ 3 + 2 * Real.log (1 + x) := by
  have hb := DashaDistributedSimplification.size_ceil_le_log x hx
  have hl := Real.log_le_log (show 0 < 2 + x by positivity) (show 2 + x ≤ 2 * (1 + x) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

lemma precision_le_logScale (w N X : ℝ) (hw : 1 ≤ w) (hN : 1 ≤ N) (hX : 0 ≤ X) :
    (Nat.size ⌈X / N⌉₊ : ℝ) ≤ 2 * logScale w N X := by
  have hN0 : 0 < N := by linarith
  have hb := DashaDistributedSimplification.size_ceil_le_log (X / N) (by positivity)
  have hdiv : X / N ≤ X := by
    apply (div_le_iff₀ hN0).mpr
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hN)]
  have hl := Real.log_le_log (show 0 < 2 + X / N by positivity)
    (show 2 + X / N ≤ 2 * (N + X) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hwlog := Real.log_nonneg hw
  have hi := Real.log_nonneg (show 1 ≤ 1 + Real.log w by linarith)
  unfold logScale
  linarith

lemma log_iterations_le_scale (w N X K : ℝ) (hw : 1 ≤ w) (hN : 1 ≤ N) (hX : 0 ≤ X)
    (hK : 0 ≤ K) (hbound : K ≤ 480 * N) :
    Real.log (1 + K) ≤ 5 * logScale w N X := by
  have hn : 0 ≤ Real.log (N + X) := Real.log_nonneg (by linarith)
  have hwlog := Real.log_nonneg hw
  have hi := Real.log_nonneg (show 1 ≤ 1 + Real.log w by linarith)
  have hl := Real.log_le_log (show 0 < 1 + K by positivity)
    (show 1 + K ≤ 512 * (N + X) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  have h512 : Real.log (512 : ℝ) = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = (2 : ℝ) ^ 9 by norm_num, Real.log_pow]
    norm_num
  rw [h512] at hl
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  unfold logScale
  linarith

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaDistributedParameters LongTails.Algorithms.DashaDistributedTrackedParameters

variable {p : Params}

lemma tracked_roundBits_le_scale (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (Z : ℝ) (hZ : 0 ≤ Z) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (hnoise : ∀ c₀, initializer = some c₀ → p.G / (p.ε * Real.sqrt (p.n : ℝ)) ≤ Real.sqrt Z) :
    (roundBits p (trackedConfig p c initializer modularInitialization) : ℝ) ≤
      ((c.block.val : ℝ) + 1) * (c.precision + 9 + 2 * Real.log (1 + (roundCount p c initializer : ℝ)) +
        6 * logScale ((p.n : ℝ) * p.d) (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2)
          (p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ))) + 2 * Real.log (1 + Real.log (1 + Z))) := by
  let N := 1 + min p.L p.Lhat * p.Δ / p.ε ^ 2
  let X := p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ))
  let w := (p.n : ℝ) * p.d
  let U := trackingInputBound p c initializer
  have hN : 1 ≤ N := by
    dsimp [N]
    have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
    linarith
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hw : 1 ≤ w := by
    have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
    have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
    dsimp [w]
    nlinarith
  have hU : 1 ≤ U := (DashaDistributedBudget.tracking_range_growth c initializer hL hH hG hε).1
  have hbound : U ≤ 512 * w ^ 3 * (1 + X) * (1 + N) * (1 + Z) := by
    have h := DashaDistributedSimplification.trackingInput_le_scaled_noise c initializer Z hZ hL hH hΔ hG hε hgap hnoise
    convert h using 1
    dsimp [w, X, N]
    ring
  have hl := loglog_range_le w N X Z U hw hN hX hZ hU hbound
  have hp := DashaDistributedSimplification.tracked_roundBits_le_log c initializer modularInitialization hL hH hG hε
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _ ≤ (c.precision : ℝ) + 9 + 2 * Real.log (1 + (roundCount p c initializer : ℝ)) +
    6 * logScale w N X + 2 * Real.log (1 + Real.log (1 + Z))
  unfold logScale
  linarith only [hl]

lemma packet_total_le (P k d K B r Z : ℝ) (hk : 0 ≤ k) (hkd : k ≤ d)
    (hK : 1 ≤ K) (hB : 2 ≤ B) (hr : r ≤ 2 * B) (hlogK : Real.log (1 + K) ≤ 5 * B)
    (hZ : 0 ≤ Z)
    (hP : P ≤ k * (r + 9 + 2 * Real.log (1 + K) + 6 * B + 2 * Real.log (1 + Real.log (1 + Z)))) :
    K * P ≤ 40 * k * K * B + 2 * d * Real.log (1 + Z) := by
  have hK0 : 0 ≤ K := by linarith
  have hZlog : 0 ≤ Real.log (1 + Z) := Real.log_nonneg (by linarith)
  have ha := DashaDistributedSimplification.amortized_iterated_log K Z hK hZ
  have hl := Real.log_le_log (show 0 < K by linarith) (show K ≤ 1 + K by linarith)
  have hkl := mul_le_mul_of_nonneg_left hl hK0
  have ha' : K * Real.log (1 + Real.log (1 + Z)) ≤ K * Real.log (1 + K) + Real.log (1 + Z) := by linarith
  have hm := mul_le_mul_of_nonneg_left ha' (show 0 ≤ 2 * k by positivity)
  have hp := mul_le_mul_of_nonneg_left hP hK0
  have hinner : r + 9 + 6 * B + 4 * Real.log (1 + K) ≤ 40 * B := by linarith
  have hb := mul_le_mul_of_nonneg_left hinner (mul_nonneg hk hK0)
  have hi := mul_le_mul_of_nonneg_right hkd (show 0 ≤ 2 * Real.log (1 + Z) by positivity)
  nlinarith only [hm, hp, hb, hi]

lemma packet_total_small_noise_le (P k K B r Z : ℝ) (hk : 0 ≤ k)
    (hK : 1 ≤ K) (hB : 2 ≤ B) (hr : r ≤ 2 * B) (hlogK : Real.log (1 + K) ≤ 5 * B)
    (hZ : 0 ≤ Z) (hZ1 : Z ≤ 1)
    (hP : P ≤ k * (r + 9 + 2 * Real.log (1 + K) + 6 * B + 2 * Real.log (1 + Real.log (1 + Z)))) :
    K * P ≤ 40 * k * K * B := by
  have hZlog : 0 ≤ Real.log (1 + Z) := Real.log_nonneg (by linarith)
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + Z by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log (1 + Z) by positivity)
  have hi : r + 9 + 2 * Real.log (1 + K) + 6 * B + 2 * Real.log (1 + Real.log (1 + Z)) ≤ 40 * B := by linarith
  have hp := hP.trans (mul_le_mul_of_nonneg_left hi hk)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ K by linarith)
  nlinarith only [hm]

noncomputable def initialLogScale (d N : ℝ) : ℝ := 1 + Real.log (1 + Real.log (d * N))

noncomputable def modularLogScale (w N : ℝ) : ℝ := 1 + Real.log (w * N)

lemma initialLogScale_bounds (w d N X : ℝ) (hd : 1 ≤ d) (hwd : d ≤ w)
    (hN : 1 ≤ N) (hX : 0 ≤ X) :
    1 ≤ initialLogScale d N ∧ initialLogScale d N ≤ logScale w N X ∧
      initialLogScale d N ≤ modularLogScale w N := by
  have hd0 : 0 < d := by linarith
  have hw0 : 0 < w := by linarith
  have hN0 : 0 < N := by linarith
  have hdn : 1 ≤ d * N := by nlinarith [mul_le_mul hd hN (by norm_num) hd0.le]
  have hdnlog : 0 ≤ Real.log (d * N) := Real.log_nonneg hdn
  have hwlog : 0 ≤ Real.log w := Real.log_nonneg (hd.trans hwd)
  have hnlog : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos hN0
  have hdw := Real.log_le_log hd0 hwd
  have hmult := mul_le_mul_of_nonneg_right hN hwlog
  have hprod : Real.log (d * N) = Real.log d + Real.log N := Real.log_mul hd0.ne' hN0.ne'
  have hinner : 1 + Real.log (d * N) ≤ N * (1 + Real.log w) := by nlinarith only [hnlog, hdw, hmult, hprod]
  have hout := Real.log_le_log (show 0 < 1 + Real.log (d * N) by positivity) hinner
  rw [Real.log_mul hN0.ne' (by positivity)] at hout
  have hNX := Real.log_le_log hN0 (show N ≤ N + X by linarith)
  have hiter : 0 ≤ Real.log (1 + Real.log (d * N)) := Real.log_nonneg (by linarith)
  have hsum := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log (d * N) by positivity)
  have hmono := Real.log_le_log (mul_pos hd0 hN0) (mul_le_mul_of_nonneg_right hwd hN0.le)
  unfold initialLogScale logScale modularLogScale
  constructor
  · linarith
  constructor <;> linarith

lemma log_two_pow_le (m : ℕ) : Real.log ((2 : ℝ) ^ m) ≤ (m : ℝ) := by
  rw [Real.log_pow]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hm := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ m by positivity)
  nlinarith

lemma loglog_initial_le (d N Z u : ℝ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hZ : 0 ≤ Z) (hu : 0 ≤ u) (hbound : u ≤ 32 * d * Real.sqrt Z) :
    Real.log (1 + Real.log (2 + u)) ≤ initialLogScale d N + 2 + Real.log (1 + Z) := by
  have hd0 : 0 < d := by linarith
  have hdlog : 0 ≤ Real.log d := Real.log_nonneg hd
  have hZlog : 0 ≤ Real.log (1 + Z) := Real.log_nonneg (by linarith)
  have hZroot : Real.sqrt Z ≤ 1 + Z := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hZ]
    nlinarith [sq_nonneg Z]
  have hm := mul_le_mul_of_nonneg_left hZroot (show 0 ≤ 32 * d by positivity)
  have hbig : 2 + u ≤ 64 * d * (1 + Z) := by
    nlinarith [mul_nonneg hd0.le hZ]
  have hl := Real.log_le_log (show 0 < 2 + u by positivity) hbig
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hd0.ne'] at hl
  have h64 : Real.log (64 : ℝ) ≤ 6 := by
    have h := log_two_pow_le 6
    norm_num at h
    exact h
  have h8 : Real.log (8 : ℝ) ≤ 3 := by
    have h := log_two_pow_le 3
    norm_num at h
    exact h
  have hprod : 1 + Real.log (2 + u) ≤ 8 * (1 + Real.log d) * (1 + Real.log (1 + Z)) := by
    nlinarith [mul_nonneg hdlog hZlog]
  have hulog : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  have hout := Real.log_le_log (show 0 < 1 + Real.log (2 + u) by positivity) hprod
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)] at hout
  have hz := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log (1 + Z) by positivity)
  have hdn : d ≤ d * N := by nlinarith [mul_le_mul_of_nonneg_left hN hd0.le]
  have hlogdn := Real.log_le_log hd0 hdn
  have hiter := Real.log_le_log (show 0 < 1 + Real.log d by positivity) (add_le_add le_rfl hlogdn)
  unfold initialLogScale
  linarith

lemma dense_width_le (t u : ℝ) (ht : 1 ≤ t) (hu : 0 ≤ u) (hbound : u ≤ 49 * t) :
    (Nat.size ⌈u⌉₊ : ℝ) + 1 ≤ 16 * (1 + Real.log t) := by
  have ht0 : 0 < t := by linarith
  have hlogt := Real.log_nonneg ht
  have hb := DashaDistributedSimplification.size_ceil_le_log u hu
  have hl := Real.log_le_log (show 0 < 2 + u by positivity) (show 2 + u ≤ 64 * t by linarith)
  rw [Real.log_mul (by norm_num) ht0.ne'] at hl
  have h64 : Real.log (64 : ℝ) ≤ 6 := by
    have h := log_two_pow_le 6
    norm_num at h
    exact h
  linarith

lemma float_word_le (d N Z u : ℝ) (s : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hZ : 0 ≤ Z) (hu : 0 ≤ u) (hbound : u ≤ 32 * d * Real.sqrt Z) :
    (s : ℝ) + Nat.size (Nat.size ⌈u⌉₊) + 3 ≤
      s + 10 + 2 * initialLogScale d N + 2 * Real.log (1 + Z) := by
  have hb := DashaDistributedSimplification.double_size_ceil_le_log u hu
  have hl := loglog_initial_le d N Z u hd hN hZ hu hbound
  linarith

end LongTails.Proofs.DashaDistributedLogBounds
