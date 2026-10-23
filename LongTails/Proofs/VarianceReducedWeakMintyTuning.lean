import LongTails.Algorithms.VarianceReducedWeakMinty
import LongTails.Proofs.VarianceReducedWeakMintyAlgebra
import LongTails.Proofs.WeakMintyPicard

namespace OracleTemplate.VarianceReducedWeakMinty

lemma tuning_parameters {δ L : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) :
    let η := (2 - δ) / (2 * L)
    let s := δ / (2 - δ)
    0 < η ∧ 0 < s ∧ s ≤ 1 ∧ δ / 2 ≤ s ∧ η * L < 1 ∧
      δ / 2 ≤ 1 - η ^ 2 * L ^ 2 ∧ 1 - η ^ 2 * L ^ 2 ≤ 1 ∧
      s * η = δ / (2 * L) := by
  dsimp only
  have hd : 0 < 2 - δ := by linarith
  have hη : 0 < (2 - δ) / (2 * L) := div_pos hd (by positivity)
  have hs : 0 < δ / (2 - δ) := div_pos hδ hd
  have hηeq : (2 - δ) / (2 * L) * L = 1 - δ / 2 := by field_simp
  have hsq : ((2 - δ) / (2 * L)) ^ 2 * L ^ 2 = (1 - δ / 2) ^ 2 := by
    rw [← mul_pow, hηeq]
  refine ⟨hη, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hd]; linarith
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [hηeq]; linarith
  · rw [hsq]; nlinarith
  · rw [hsq]; nlinarith [sq_nonneg (1 - δ / 2)]
  · field_simp

lemma tuning_power {δ h s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hhlo : δ / 2 ≤ h) (hhhi : h ≤ 1) (hs : δ / 2 ≤ s) :
    (1 - h / 2) ^ ⌈32 / δ * Real.log (65536 / δ ^ 2)⌉₊ ≤ s ^ 2 / 8192 := by
  have hh := WeakMintyPicard.power_bound (δ := δ / 8) (by positivity) (by linarith)
    (K := ⌈32 / δ * Real.log (65536 / δ ^ 2)⌉₊) (by
      have ha : 4 / (δ / 8) = 32 / δ := by ring
      have hb : 1024 / (δ / 8) ^ 2 = 65536 / δ ^ 2 := by ring
      rw [ha, hb]
      exact Nat.le_ceil _)
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - h / 2)
    (show 1 - h / 2 ≤ 1 - δ / 8 / 4 by linarith)
    ⌈32 / δ * Real.log (65536 / δ ^ 2)⌉₊
  have hs0 : 0 ≤ s := by linarith
  nlinarith

lemma tuning_noise {δ L Λ η s h : ℝ} {q b : ℕ}
    (hδ : 0 < δ) (hL : 0 < L) (hh : 0 < h) (hs : 0 ≤ s)
    (hη : η ^ 2 * L ^ 2 ≤ 1) (hhδ : δ / 2 ≤ h) (hsδ : δ / 2 ≤ s)
    (hq : 0 < q) (hb : 0 < b)
    (hbatch : 524288 * (q : ℝ) * Λ ^ 2 / (L ^ 2 * δ ^ 3) ≤ b) :
    η ^ 2 * (Λ ^ 2 / b) / h ≤ s ^ 2 * (q : ℝ)⁻¹ / 65536 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hprod : δ ^ 3 / 8 ≤ h * s ^ 2 := by
    have hs2 : δ ^ 2 / 4 ≤ s ^ 2 := by nlinarith
    have ht := mul_le_mul hhδ hs2 (by positivity : 0 ≤ δ ^ 2 / 4) hh.le
    nlinarith only [ht]
  have hbnd := (div_le_iff₀ (show 0 < L ^ 2 * δ ^ 3 by positivity)).mp hbatch
  have h1 := mul_le_mul_of_nonneg_left hbnd (sq_nonneg η)
  have h2 := mul_le_mul_of_nonneg_right hη (show 0 ≤ (b : ℝ) * δ ^ 3 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hprod hb'.le
  have hfinal : 65536 * η ^ 2 * Λ ^ 2 * (q : ℝ) ≤ (b : ℝ) * h * s ^ 2 := by
    nlinarith only [h1, h2, h3]
  apply (div_le_iff₀ hh).mpr
  rw [div_eq_mul_inv]
  apply (mul_le_mul_iff_right₀ hb').mp
  apply (mul_le_mul_iff_right₀ hq').mp
  field_simp at hfinal ⊢
  nlinarith only [hfinal]

lemma tuning_iterations {δ L radius ε : ℝ} {q M : ℕ}
    (hδ : 0 < δ) (_hL : 0 < L) (hε : 0 < ε) (hq : 0 < q) (hM : 0 < M)
    (hcount : 128 * L ^ 2 * radius ^ 2 / (δ ^ 2 * (q : ℝ) * ε ^ 2) ≤ M) :
    128 * L ^ 2 * radius ^ 2 / (δ ^ 2 * (q * M : ℕ)) ≤ ε ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hh := (div_le_iff₀ (show 0 < δ ^ 2 * (q : ℝ) * ε ^ 2 by positivity)).mp hcount
  rw [div_le_iff₀ (by positivity)]
  push_cast
  nlinarith only [hh]

lemma inner_length_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((⌈32 / δ * Real.log (65536 / δ ^ 2)⌉₊ + 1 : ℕ) : ℝ) + 1 ≤
      1024 * Real.log (2 / δ) / δ := by
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlg : Real.log (2 / δ) = Real.log 2 - Real.log δ :=
    Real.log_div (by norm_num) hδ.ne'
  have hbig : Real.log (65536 / δ ^ 2) = 16 * Real.log 2 - 2 * Real.log δ := by
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hδ.ne'), Real.log_pow]
    rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, Real.log_pow]
    norm_num
  have hpos : 0 ≤ 32 / δ * Real.log (65536 / δ ^ 2) := by
    rw [hbig]
    exact mul_nonneg (by positivity) (by linarith)
  have hc := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one hpos) hδ
  have he : δ * (32 / δ * Real.log (65536 / δ ^ 2) + 1) =
      32 * Real.log (65536 / δ ^ 2) + δ := by field_simp
  rw [he, hbig] at hc
  rw [le_div_iff₀ hδ, hlg, hbig]
  push_cast
  nlinarith

open LongTails.Setups.FiniteSumWeakMintyInclusion

lemma valid_margin (p : Params) (hp : spec.valid p) : 0 < margin p ∧ margin p ≤ 1 := by
  rcases hp with ⟨_, hL, _, hρ, hρL, _, _⟩
  dsimp [margin]
  constructor
  · linarith
  · nlinarith [mul_nonneg hρ hL.le]

lemma epoch_length_two (p : Params) : 2 ≤ epochLength p := by
  unfold epochLength
  split <;> omega

lemma batch_size_pos (p : Params) (hp : spec.valid p) : 0 < batchSize p := by
  have hδ := (valid_margin p hp).1
  have hL := hp.2.1
  have hΛ : 0 < p.Λ := lt_of_lt_of_le hL hp.2.2.1
  have hq : 0 < epochLength p := NeZero.pos _
  unfold batchSize
  split
  · omega
  · apply Nat.ceil_pos.mpr
    positivity

lemma tuned_noise (p : Params) (hp : spec.valid p) :
    let η := (2 - margin p) / (2 * p.L)
    let s := margin p / (2 - margin p)
    let h := 1 - η ^ 2 * p.L ^ 2
    η ^ 2 * (if useExact p then 0 else p.Λ ^ 2 / batchSize p) / h ≤
      s ^ 2 * (epochLength p : ℝ)⁻¹ / 65536 := by
  obtain ⟨hδ, hδ1⟩ := valid_margin p hp
  obtain ⟨hη, hs, _, _, _, hhlo, _, _⟩ := tuning_parameters hδ hδ1 hp.2.1
  dsimp only
  split
  · simp only [mul_zero, zero_div]
    positivity
  · apply tuning_noise hδ hp.2.1 (by linarith) hs.le (by nlinarith) hhlo
      (tuning_parameters hδ hδ1 hp.2.1).2.2.2.1 (NeZero.pos _) (batch_size_pos p hp)
    rename_i he
    simp only [batchSize, he]
    exact Nat.le_ceil _

end OracleTemplate.VarianceReducedWeakMinty
