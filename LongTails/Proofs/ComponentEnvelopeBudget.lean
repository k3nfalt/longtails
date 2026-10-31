import LongTails.Proofs.ComponentEnvelopeOracle
namespace OracleTemplate.ComponentEnvelope
lemma epoch_count_scalar {n κ Q : ℝ} (hn : 1 ≤ n) (hκ : 0 ≤ κ) (hQ : 0 ≤ Q) :
    (⌈Real.sqrt (7200 * (κ / n + 8 * Q ^ 2))⌉₊ : ℝ) ≤
      1 + 85 * Real.sqrt (κ / n) + 240 * Q := by
  have hn0 : 0 < n := by linarith
  have hk : 0 ≤ κ / n := div_nonneg hκ hn0.le
  have hsq := Real.sq_sqrt hk
  have hs := Real.sqrt_nonneg (κ / n)
  have hbound : Real.sqrt (7200 * (κ / n + 8 * Q ^ 2)) ≤ 85 * Real.sqrt (κ / n) + 240 * Q := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hp : 0 ≤ Real.sqrt (κ / n) * Q := mul_nonneg hs hQ
    nlinarith
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (7200 * (κ / n + 8 * Q ^ 2)))
  linarith
lemma epoch_work_scalar {n κ Q S : ℝ} (hn : 1 ≤ n) (hκ : 0 ≤ κ)
    (hS : S ≤ 1 + 85 * Real.sqrt (κ / n) + 240 * Q) :
    n * (4 + 2 * S) + 752 * n * Q ^ 2 ≤ 1000 * (n * (1 + Q ^ 2) + Real.sqrt (n * κ)) := by
  have hn0 : 0 < n := by linarith
  have hsqrt : n * Real.sqrt (κ / n) = Real.sqrt (n * κ) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt (div_nonneg hκ hn0.le), Real.sq_sqrt (mul_nonneg hn0.le hκ)]
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hS hn0.le
  rw [mul_add, mul_add, mul_one, show n * (85 * Real.sqrt (κ / n)) = 85 * (n * Real.sqrt (κ / n)) by ring, hsqrt] at hscaled
  have hQ2 := mul_nonneg hn0.le (sq_nonneg (Q - 1))
  have hpos := Real.sqrt_nonneg (n * κ)
  have hquad := mul_nonneg hn0.le (sq_nonneg Q)
  nlinarith
lemma inner_log_scalar {n κ Q S : ℝ} (hn : 1 ≤ n) (hκ : 0 ≤ κ) (hQ : 0 ≤ Q) (hS0 : 0 ≤ S)
    (hS : S ≤ 1 + 85 * Real.sqrt (κ / n) + 240 * Q) :
    Real.log (4 + Q + 1048576 * n * (S + 4) ^ 3 * (1 + Q)) ≤
      40 * Real.log (2 + n + κ + Q ^ 2) := by
  let X := 2 + n + κ + Q ^ 2
  have hX : 3 ≤ X := by dsimp [X]; nlinarith [sq_nonneg Q]
  have hn0 : 0 < n := by linarith
  have hnx : n ≤ X := by dsimp [X]; nlinarith [sq_nonneg Q]
  have hQx : Q ≤ X := by dsimp [X]; nlinarith [sq_nonneg (Q - 1)]
  have hkx : Real.sqrt (κ / n) ≤ X := by
    have hdiv : κ / n ≤ κ := (div_le_iff₀ hn0).mpr (by nlinarith)
    have hs := Real.sq_sqrt (div_nonneg hκ hn0.le)
    have hpos := Real.sqrt_nonneg (κ / n)
    have hk : Real.sqrt (κ / n) ≤ 1 + κ := by nlinarith [sq_nonneg κ]
    dsimp [X]
    nlinarith [sq_nonneg Q]
  have hSx : S + 4 ≤ 331 * X := by linarith
  have h1Q : 1 + Q ≤ 2 * X := by linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ S + 4 by linarith) hSx 3
  have hbig : 1048576 * n * (S + 4) ^ 3 * (1 + Q) ≤ 2097152 * 331 ^ 3 * X ^ 5 := by
    calc
      _ ≤ 1048576 * X * (331 * X) ^ 3 * (2 * X) := by gcongr
      _ = _ := by ring
  have hX1 : 1 ≤ X := by linarith
  have hpower : X ≤ X ^ 5 := by
    calc X = X ^ 1 := (pow_one X).symm
         _ ≤ X ^ 5 := pow_le_pow_right₀ hX1 (by omega)
  have hA : 4 + Q + 1048576 * n * (S + 4) ^ 3 * (1 + Q) ≤ (5 + 2097152 * 331 ^ 3) * X ^ 5 := by
    have hsmall : 4 + Q ≤ 5 * X := by linarith
    linarith
  have hconst : (5 + 2097152 * 331 ^ 3 : ℝ) ≤ X ^ 35 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hX 35
    have hc : (5 + 2097152 * 331 ^ 3 : ℝ) ≤ 3 ^ 35 := by norm_num
    exact hc.trans hp
  have hA40 : 4 + Q + 1048576 * n * (S + 4) ^ 3 * (1 + Q) ≤ X ^ 40 := by
    have hm := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ X ^ 5)
    have heq : X ^ 35 * X ^ 5 = X ^ 40 := by rw [← pow_add]
    rw [heq] at hm
    exact hA.trans hm
  have hpos : 0 < 4 + Q + 1048576 * n * (S + 4) ^ 3 * (1 + Q) := by positivity
  have hlog := Real.log_le_log hpos hA40
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  exact hlog

open LongTails.Setups.InterpolatedGeneralizedFiniteSum
lemma public_budget_suffices (p : Params) (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε) (hR : 0 < p.R) :
    6 * (4096 * Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) / tolerance p)) *
      ((p.n : ℝ) * (4 + 2 * epochCount p) + 752 * p.n * (p.L1 * p.R) ^ 2) ≤
    (⌈1073741824 * ((p.n : ℝ) * (1 + p.L1 ^ 2 * p.R ^ 2) + Real.sqrt (p.n * p.L0 * p.R ^ 2 / p.ε)) *
      Real.log (2 + p.n + p.L0 * p.R ^ 2 / p.ε + p.L1 ^ 2 * p.R ^ 2)⌉₊ : ℝ) := by
  let n := (p.n : ℝ)
  let κ := p.L0 * p.R ^ 2 / p.ε
  let Q := p.L1 * p.R
  let S := (epochCount p : ℝ)
  let X := 2 + n + κ + Q ^ 2
  let B := n * (1 + Q ^ 2) + Real.sqrt (n * κ)
  have hn : 1 ≤ n := by
    change (1 : ℝ) ≤ p.n
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.n))
  have hpn : (p.n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.n)
  have hn0 : 0 < n := by linarith
  have hk : 0 ≤ κ := by dsimp [κ]; positivity
  have hQ : 0 ≤ Q := mul_nonneg h1 hR.le
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hμ := smoothing_pos p h0 he
  have hζ := tolerance_pos p h0 he hR
  have hcountid : 7200 * smoothing p * p.R ^ 2 / (n * p.ε) = 7200 * (κ / n + 8 * Q ^ 2) := by
    dsimp [κ, Q, smoothing, n]
    field_simp [hpn]
  have hS : S ≤ 1 + 85 * Real.sqrt (κ / n) + 240 * Q := by
    dsimp [S, epochCount]
    change (⌈Real.sqrt (7200 * smoothing p * p.R ^ 2 / (n * p.ε))⌉₊ : ℝ) ≤ _
    rw [hcountid]
    exact epoch_count_scalar hn hk hQ
  have hwork := epoch_work_scalar hn hk hS
  have hlog := inner_log_scalar hn hk hQ hS0 hS
  have hlogid : smoothing p * p.R * (1 + Q) / tolerance p = 1048576 * n * (S + 4) ^ 3 * (1 + Q) := by
    dsimp [tolerance, n, S]
    field_simp
  rw [← hlogid] at hlog
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [sq_nonneg Q]
  have hlogpos : 0 ≤ Real.log X := Real.log_nonneg hX
  have hW : 0 ≤ n * (4 + 2 * S) + 752 * n * Q ^ 2 := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmul := mul_le_mul hlog hwork hW (show 0 ≤ 40 * Real.log X by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 6 * 4096)
  have hpos : 0 ≤ B * Real.log X := mul_nonneg hB hlogpos
  have hfinal : 6 * (4096 * Real.log (4 + Q + smoothing p * p.R * (1 + Q) / tolerance p)) *
      (n * (4 + 2 * S) + 752 * n * Q ^ 2) ≤ 1073741824 * B * Real.log X := by
    dsimp only [B, X] at hpos
    dsimp only [B, X]
    nlinarith
  have htarget : 1073741824 * B * Real.log X =
      1073741824 * ((p.n : ℝ) * (1 + p.L1 ^ 2 * p.R ^ 2) + Real.sqrt (p.n * p.L0 * p.R ^ 2 / p.ε)) *
        Real.log (2 + p.n + p.L0 * p.R ^ 2 / p.ε + p.L1 ^ 2 * p.R ^ 2) := by
    dsimp [B, X, n, κ, Q]
    congr 3 <;> ring_nf
  rw [htarget] at hfinal
  exact hfinal.trans (Nat.le_ceil _)

end OracleTemplate.ComponentEnvelope
