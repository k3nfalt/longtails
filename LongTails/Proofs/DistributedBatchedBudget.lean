import LongTails.Proofs.DistributedBatchedSgd

namespace LongTails.Proofs.DistributedBatchedBudget

open DistributedTemplate
open LongTails.Setups.DistributedSmoothNonconvex
open LongTails.Algorithms.DistributedBatchedSgd

variable {p : Params}

lemma iterations_le : (iterations p : ℕ) ≤ 16 * (1 + ⌈p.L * p.Δ / p.ε⌉₊) := by
  have ha := Nat.le_ceil (p.L * p.Δ / p.ε)
  apply max_le (by omega)
  apply Nat.ceil_le.mpr
  push_cast
  calc
    16 * p.L * p.Δ / p.ε = 16 * (p.L * p.Δ / p.ε) := by ring
    _ ≤ _ := by linarith

lemma batch_le : targetBatch p ≤ 256 * (1 + ⌈p.σ ^ 2 / p.ε⌉₊) := by
  have hr := Nat.le_ceil (p.σ ^ 2 / p.ε)
  apply max_le (by omega)
  apply Nat.ceil_le.mpr
  push_cast
  calc
    256 * p.σ ^ 2 / p.ε = 256 * (p.σ ^ 2 / p.ε) := by ring
    _ ≤ _ := by linarith

lemma width_le (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    ((config p).width : ℕ) ≤ 32 + 4 * Nat.log2 (2 + p.d + ⌈p.L * p.Δ / p.ε⌉₊ + ⌈p.σ ^ 2 / p.ε⌉₊) := by
  let s := 2 + p.d + ⌈p.L * p.Δ / p.ε⌉₊ + ⌈p.σ ^ 2 / p.ε⌉₊
  let N := 2 ^ 24 * s ^ 4
  have hs : (1 : ℝ) ≤ s := by
    have : 1 ≤ s := by dsimp [s]; omega
    exact_mod_cast this
  have hd : (p.d : ℝ) ≤ s := by
    exact_mod_cast (show p.d ≤ s by dsimp [s]; omega)
  have ha : p.L * p.Δ / p.ε ≤ s := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈p.L * p.Δ / p.ε⌉₊ ≤ s by dsimp [s]; omega))
  have hr : p.σ ^ 2 / p.ε ≤ s := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈p.σ ^ 2 / p.ε⌉₊ ≤ s by dsimp [s]; omega))
  have hk : ((iterations p : ℕ) : ℝ) ≤ 16 * s := by
    have hi := iterations_le (p := p)
    have hi' : (iterations p : ℕ) ≤ 16 * s := by dsimp [s]; omega
    exact_mod_cast hi'
  have ha0 : 0 ≤ p.L * p.Δ / p.ε := by positivity
  have hr0 : 0 ≤ p.σ ^ 2 / p.ε := by positivity
  let q : ℝ := 1 + 8192 * p.d * ((iterations p : ℕ) : ℝ) ^ 2 +
    16 * p.d * (1280 * p.L * p.Δ / p.ε + 160 + 163840 * (p.σ ^ 2 / p.ε) ^ 2 +
      2560 * (iterations p : ℕ) * p.L * p.Δ / p.ε)
  have hq : q ≤ N := by
    have hq' : q ≤ 1 + 8192 * (s : ℝ) * (16 * s) ^ 2 +
        16 * s * (1280 * s + 160 + 163840 * (s : ℝ) ^ 2 + 2560 * (16 * s) * s) := by
      dsimp [q]
      have he1 : 1280 * p.L * p.Δ / p.ε = 1280 * (p.L * p.Δ / p.ε) := by ring
      have he2 : 2560 * (iterations p : ℕ) * p.L * p.Δ / p.ε =
          2560 * (iterations p : ℕ) * (p.L * p.Δ / p.ε) := by ring
      rw [he1, he2]
      gcongr
    have h12 : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
    have h23 : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (s : ℝ)) (sub_nonneg.mpr hs)]
    have h34 : (s : ℝ) ^ 3 ≤ (s : ℝ) ^ 4 := by nlinarith [mul_nonneg (pow_nonneg (by positivity : 0 ≤ (s : ℝ)) 3) (sub_nonneg.mpr hs)]
    dsimp [N]
    push_cast
    nlinarith
  have hN : (1 : ℝ) ≤ N := by
    have hn0 : 0 < N := by dsimp [N, s]; positivity
    have hn : 1 ≤ N := hn0
    exact_mod_cast hn
  have hceil : ⌈Real.sqrt q⌉₊ ≤ N := by
    apply Nat.ceil_le.mpr
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hpow : N < 2 ^ (28 + 4 * Nat.log2 s) := by
    have h := Nat.lt_log2_self (n := s)
    have h4 : s ^ 4 < (2 ^ (Nat.log2 s + 1)) ^ 4 := by gcongr
    have hm := Nat.mul_lt_mul_of_pos_left h4 (by decide : 0 < 2 ^ 24)
    calc
      N < 2 ^ 24 * (2 ^ (Nat.log2 s + 1)) ^ 4 := hm
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hw := (Nat.size_le_size hceil).trans (Nat.size_le.mpr hpow)
  change Nat.size ⌈Real.sqrt q⌉₊ + 1 ≤ 32 + 4 * Nat.log2 s
  omega

lemma computation_le (hh : ∀ i, 0 < p.h i) :
    computationTime p (config p) ≤ 512 * sInf (Set.range (fun i : Fin p.n =>
      p.h i + (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / throughput p i)) := by
  let : Nonempty (Fin p.n) := ⟨⟨0, p.n.pos⟩⟩
  let f := fun i : Fin p.n => p.h i + (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / throughput p i
  have hb : (targetBatch p : Time) ≤ 256 * (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) := by
    exact_mod_cast batch_le (p := p)
  obtain ⟨_, _, hmin⟩ := DistributedBatchedSgd.batchTime_minimizes (p := p)
  have hall (i : Fin p.n) : computationTime p (config p) ≤ 512 * f i := by
    have hterm : max (p.h i) ((targetBatch p : Time) / throughput p i) ≤ 256 * f i := by
      apply max_le
      · exact (le_add_of_nonneg_right zero_le).trans (le_mul_of_one_le_left zero_le (by norm_num))
      · calc
          _ ≤ (256 * (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ)) / throughput p i := div_le_div_of_nonneg_right hb zero_le
          _ = 256 * ((1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / throughput p i) := by rw [mul_div_assoc]
          _ ≤ 256 * f i := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le) zero_le
    calc
      _ ≤ candidateTime p i := (DistributedBatchedSgd.configured_computation_time hh).trans (hmin i)
      _ ≤ 2 * (256 * f i) := mul_le_mul_of_nonneg_left hterm zero_le
      _ = 512 * f i := by ring
  have hi : computationTime p (config p) / 512 ≤ sInf (Set.range f) := by
    apply le_csInf (Set.range_nonempty (f := f))
    rintro _ ⟨i, rfl⟩
    exact (div_le_iff₀ (by norm_num : (0 : Time) < 512)).mpr (by simpa [mul_comm] using hall i)
  exact (div_le_iff₀ (by norm_num : (0 : Time) < 512)).mp hi |>.trans_eq (mul_comm _ _)

lemma budget_le (hh : ∀ i, 0 < p.h i)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    timeBudget p (config p) ≤ 8192 * (1 + ⌈p.L * p.Δ / p.ε⌉₊ : ℕ) *
      (sInf (Set.range (fun i : Fin p.n => p.h i + (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / throughput p i)) +
        p.l + p.b * (p.d * (32 + 4 * Nat.log2 (2 + p.d + ⌈p.L * p.Δ / p.ε⌉₊ + ⌈p.σ ^ 2 / p.ε⌉₊)) + clockBits : ℕ)) := by
  let τ := sInf (Set.range (fun i : Fin p.n => p.h i + (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / throughput p i))
  let c := p.l + p.b * (p.d * (32 + 4 * Nat.log2 (2 + p.d + ⌈p.L * p.Δ / p.ε⌉₊ + ⌈p.σ ^ 2 / p.ε⌉₊)) + clockBits : ℕ)
  have hk : ((iterations p : ℕ) : Time) ≤ 16 * (1 + ⌈p.L * p.Δ / p.ε⌉₊ : ℕ) := by
    exact_mod_cast iterations_le (p := p)
  have hc : p.l + p.b * (p.d * (config p).width + clockBits : ℕ) ≤ c := by
    dsimp [c]
    gcongr
    exact width_le hL hΔ hε
  have ht := computation_le hh
  calc
    timeBudget p (config p) = (iterations p : ℕ) * (computationTime p (config p) + 2 * (p.l + p.b * (p.d * (config p).width + clockBits : ℕ))) := by
      simp only [timeBudget, show (config p).slack = 0 from rfl, add_zero]
      rfl
    _ ≤ (16 * (1 + ⌈p.L * p.Δ / p.ε⌉₊ : ℕ)) * (512 * τ + 512 * c) := by
      gcongr
      norm_num
    _ = _ := by dsimp [τ, c]; ring

lemma simple_budget_le (hh : ∀ i, 0 < p.h i)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    timeBudget p (config p) ≤ 262144 * (1 + ⌈p.L * p.Δ / p.ε⌉₊ : ℕ) *
      (sInf (Set.range (fun i : Fin p.n => p.h i + (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / throughput p i)) +
        p.l + p.b * (p.d * (1 + Nat.log2 (2 + p.d + ⌈p.L * p.Δ / p.ε⌉₊ + ⌈p.σ ^ 2 / p.ε⌉₊)) + clockBits : ℕ)) := by
  apply (budget_le hh hL hΔ hε).trans
  let τ := sInf (Set.range (fun i : Fin p.n => p.h i + (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / throughput p i))
  let w := Nat.log2 (2 + p.d + ⌈p.L * p.Δ / p.ε⌉₊ + ⌈p.σ ^ 2 / p.ε⌉₊)
  have hw : 32 + 4 * w ≤ 32 * (1 + w) := by omega
  have hc : τ + p.l + p.b * (p.d * (32 + 4 * w) + clockBits : ℕ) ≤
      32 * (τ + p.l + p.b * (p.d * (1 + w) + clockBits : ℕ)) := by
    calc
      _ ≤ 32 * τ + 32 * p.l + p.b * (p.d * (32 * (1 + w)) + 32 * clockBits : ℕ) := by
        gcongr
        · exact le_mul_of_one_le_left zero_le (by norm_num)
        · exact le_mul_of_one_le_left zero_le (by norm_num)
        · omega
      _ = _ := by push_cast; ring
  calc
    _ ≤ 8192 * (1 + ⌈p.L * p.Δ / p.ε⌉₊ : ℕ) * (32 * (τ + p.l + p.b * (p.d * (1 + w) + clockBits : ℕ))) := mul_le_mul_of_nonneg_left hc zero_le
    _ = _ := by dsimp [τ, w]; ring

lemma withBudget_time (T : Time) (hT : timeBudget p (config p) ≤ T) :
    timeBudget p (withBudget p T) = T := by
  have hz : timeBudget p (config p) = (config p).iterations * roundTime p (config p) := by
    simp only [timeBudget, show (config p).slack = 0 from rfl, add_zero]
  change (config p).iterations * roundTime p (config p) + (T - timeBudget p (config p)) = T
  rw [← hz]
  exact add_tsub_cancel_of_le hT

lemma trajectory_slack (cfg : Config p) (slack : Time)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : Samples p) (k : ℕ) :
    trajectory p { cfg with slack := slack } g samples k = trajectory p cfg g samples k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change trajectory p { cfg with slack := slack } g samples k - (1 / p.L) •
        estimate p cfg g (trajectory p { cfg with slack := slack } g samples k) k samples = _
      rw [ih]
      rfl

lemma withBudget_output (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (seed : Fin (config p).iterations × Samples p) :
    output p (withBudget p T) g seed = output p (config p) g seed :=
  trajectory_slack (config p) _ g seed.2 seed.1.val

end LongTails.Proofs.DistributedBatchedBudget
