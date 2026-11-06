import LongTails.Proofs.StochasticEqualityRestoration
namespace LongTails.Proofs.StochasticEqualityCost
open LongTails.Algorithms.StochasticEquality
open LongTails.Setups.StochasticRegularEqualities LongTails.Proofs.StochasticEqualityTuning
lemma reset_card_bound (T q : ℕ) :
    ((Finset.range T).filter (fun k => k % q = 0)).card ≤ T / q + 1 := by
  have hh := Finset.card_le_card_of_injOn (s := (Finset.range T).filter (fun k => k % q = 0))
    (t := Finset.range (T / q + 1)) (fun k => k / q) (by
      intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hk.1.le)) (by
      intro a ha b hb he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
      change a / q = b / q at he
      have hA := Nat.mod_add_div a q
      have hB := Nat.mod_add_div b q
      rw [ha.2, he] at hA
      rw [hb.2] at hB
      omega)
  simpa only [Finset.card_range] using hh

lemma batch_sum_bound (cfg : Config) (T : ℕ) :
    ∑ k ∈ Finset.range T, batchSize cfg k ≤
      (T / cfg.epoch + 1) * cfg.resetBatch + T * cfg.incrementBatch := by
  have hh : ∑ k ∈ Finset.range T, batchSize cfg k ≤
      ∑ k ∈ Finset.range T, ((if k % cfg.epoch = 0 then (cfg.resetBatch : ℕ) else 0) + cfg.incrementBatch) := by
    apply Finset.sum_le_sum
    intro k hk
    unfold batchSize
    split_ifs <;> omega
  rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hh
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  exact hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right cfg.resetBatch (reset_card_bound T cfg.epoch)) _)
lemma reset_cost_ratio {S B q : ℝ} (hS : 0 < S) (hB : 0 < B) (hq : 0 < q)
    (hql : S ^ 2 * Real.sqrt B / 10 ≤ q) : B / q ≤ 10 * Real.sqrt B / S ^ 2 := by
  apply (div_le_iff₀ hq).mpr
  have hh := mul_le_mul_of_nonneg_left hql (show 0 ≤ 10 * Real.sqrt B / S ^ 2 by positivity)
  have he : (10 * Real.sqrt B / S ^ 2) * (S ^ 2 * Real.sqrt B / 10) = B := by
    field_simp
    nlinarith only [Real.sq_sqrt hB.le]
  rw [he] at hh
  exact hh

lemma increment_cost_ratio {S B q b : ℝ} (hS : 1 ≤ S)
    (hqu : q ≤ S ^ 2 * Real.sqrt B / 10 + 1) (hb : b ≤ 100 * q / S ^ 4 + 1) :
    b ≤ 10 * Real.sqrt B / S ^ 2 + 101 := by
  have hS0 : 0 < S := by linarith only [hS]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqu (by norm_num : (0 : ℝ) ≤ 100))
    (pow_nonneg hS0.le 4)
  have he : 100 * (S ^ 2 * Real.sqrt B / 10 + 1) / S ^ 4 =
      10 * Real.sqrt B / S ^ 2 + 100 / S ^ 4 := by field_simp; ring
  rw [he] at hh
  have h100 : 100 / S ^ 4 ≤ (100 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hpow : 1 ≤ S ^ 4 := one_le_pow₀ hS
    linarith only [hpow]
  linarith only [hb, hh, h100]
lemma training_samples_bound (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    ((∑ k ∈ Finset.range cfg.steps, batchSize cfg k : ℕ) : ℝ) ≤
      (cfg.steps : ℝ) * (20 * Real.sqrt (cfg.resetBatch : ℝ) / S ^ 2 + 101) + cfg.resetBatch := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  have hS1 : 1 ≤ S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hS0 : 0 < S := by linarith only [hS1]
  have hB : 0 < (cfg.resetBatch : ℝ) := by exact_mod_cast cfg.resetBatch.pos
  have hq : 0 < (cfg.epoch : ℝ) := by exact_mod_cast cfg.epoch.pos
  have hql : S ^ 2 * Real.sqrt (cfg.resetBatch : ℝ) / 10 ≤ (cfg.epoch : ℝ) := positiveCeil_lower _
  have hqu : (cfg.epoch : ℝ) ≤ S ^ 2 * Real.sqrt (cfg.resetBatch : ℝ) / 10 + 1 :=
    positiveCeil_upper (by positivity)
  have hb : (cfg.incrementBatch : ℝ) ≤ 100 * (cfg.epoch : ℝ) / S ^ 4 + 1 :=
    positiveCeil_upper (by positivity)
  have hr := reset_cost_ratio hS0 hB hq hql
  have hb' := increment_cost_ratio hS1 hqu hb
  have hh : ((∑ k ∈ Finset.range cfg.steps, batchSize cfg k : ℕ) : ℝ) ≤
      (((cfg.steps : ℕ) / cfg.epoch + 1 : ℕ) : ℝ) * cfg.resetBatch + (cfg.steps : ℝ) * cfg.incrementBatch := by
    exact_mod_cast batch_sum_bound cfg cfg.steps
  have hd : (((cfg.steps : ℕ) / cfg.epoch : ℕ) : ℝ) ≤ (cfg.steps : ℝ) / cfg.epoch := Nat.cast_div_le
  have hfirst := mul_le_mul_of_nonneg_right (add_le_add hd (le_refl (1 : ℝ))) hB.le
  simp only [Nat.cast_add, Nat.cast_one] at hh
  have he : ((cfg.steps : ℝ) / cfg.epoch + 1) * cfg.resetBatch + (cfg.steps : ℝ) * cfg.incrementBatch =
      (cfg.steps : ℝ) * ((cfg.resetBatch : ℝ) / cfg.epoch + cfg.incrementBatch) + cfg.resetBatch := by ring
  apply (hh.trans (add_le_add hfirst le_rfl)).trans
  rw [he]
  have hs : (cfg.resetBatch : ℝ) / cfg.epoch + cfg.incrementBatch ≤
      20 * Real.sqrt (cfg.resetBatch : ℝ) / S ^ 2 + 101 := by
    exact (add_le_add hr hb').trans_eq (by ring)
  exact add_le_add (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (cfg.steps : ℝ))) le_rfl

lemma reset_batch_sqrt_bound (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    Real.sqrt ((tuning p.toPublic).resetBatch : ℝ) ≤ 1 + 10 ^ 16 * S ^ 24 * p.σ / p.ε := by
  let S := scale p.toPublic
  have hS0 : 0 < S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hσ := hp.2.2.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hB : ((tuning p.toPublic).resetBatch : ℝ) ≤ 10 ^ 32 * S ^ 48 * p.σ ^ 2 / p.ε ^ 2 + 1 :=
    positiveCeil_upper (by positivity)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, hB.trans ?_⟩
  have he : 10 ^ 32 * S ^ 48 * p.σ ^ 2 / p.ε ^ 2 = (10 ^ 16 * S ^ 24 * p.σ / p.ε) ^ 2 := by ring
  rw [he]
  nlinarith only [show 0 ≤ 10 ^ 16 * S ^ 24 * p.σ / p.ε by positivity]

set_option maxRecDepth 4096 in
lemma training_samples_budget (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    ((∑ k ∈ Finset.range cfg.steps, batchSize cfg k : ℕ) : ℝ) ≤
      10 ^ 42 * (S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε) / p.ε ^ 2 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  have hS1 : 1 ≤ S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hS0 : 0 < S := by linarith only [hS1]
  have hσ := hp.2.2.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hε1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hε2 : p.ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
  have hroot := reset_batch_sqrt_bound p hp
  have hcoef : 20 * Real.sqrt (cfg.resetBatch : ℝ) / S ^ 2 + 101 ≤
      121 + 2 * 10 ^ 17 * S ^ 22 * p.σ / p.ε := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 20)) (sq_nonneg S)
    have he : 20 * (1 + 10 ^ 16 * S ^ 24 * p.σ / p.ε) / S ^ 2 =
        20 / S ^ 2 + 2 * 10 ^ 17 * S ^ 22 * p.σ / p.ε := by field_simp; ring
    rw [he] at hh
    have h20 : 20 / S ^ 2 ≤ (20 : ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos hS0)).mpr
      have hh : 1 ≤ S ^ 2 := one_le_pow₀ hS1
      linarith only [hh]
    linarith only [hh, h20]
  have hT := (tuning_variance_parameters p hp).2.1
  have hB : (cfg.resetBatch : ℝ) ≤ 10 ^ 32 * S ^ 48 * p.σ ^ 2 / p.ε ^ 2 + 1 :=
    positiveCeil_upper (by positivity)
  have hh := (training_samples_bound p hp).trans (add_le_add
    (mul_le_mul hT hcoef (by positivity) (by positivity)) hB)
  have he : (2 * (10 ^ 24 * S ^ 38 / p.ε ^ 2)) *
      (121 + 2 * 10 ^ 17 * S ^ 22 * p.σ / p.ε) +
      (10 ^ 32 * S ^ 48 * p.σ ^ 2 / p.ε ^ 2 + 1) =
      (242 * 10 ^ 24 * S ^ 38 + 4 * 10 ^ 41 * (S ^ 60 * p.σ / p.ε) +
        10 ^ 32 * (S ^ 48 * p.σ ^ 2) + p.ε ^ 2) / p.ε ^ 2 := by field_simp; ring
  rw [he] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg p.ε)
  have hA : 1 ≤ S ^ 38 := one_le_pow₀ hS1
  have hB0 : 0 ≤ S ^ 48 * p.σ ^ 2 := by positivity
  have hC0 : 0 ≤ S ^ 60 * p.σ / p.ε := by positivity
  nlinarith only [hε2, hA, hB0, hC0]

lemma restoration_samples_budget (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    (cfg.restoreBatch : ℝ) * cfg.restoreGroups * cfg.restoreSteps ≤
      10 ^ 27 * (S ^ 38 + S ^ 48 * p.σ ^ 2) / p.ε ^ 2 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  let l := 1 + Real.log S
  have hS1 : 1 ≤ S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hS0 : 0 < S := by linarith only [hS1]
  have hl : 1 ≤ l := by dsimp [l]; linarith only [Real.log_nonneg hS1]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hε1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hε2 : p.ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
  have hN : (cfg.restoreSteps : ℝ) ≤ 8192 * S ^ 4 * l := by
    have hnom : 1 ≤ 4096 * S ^ 4 * l := by
      have hh : 1 ≤ S ^ 4 := one_le_pow₀ hS1
      nlinarith only [hh, hl]
    have hh := positiveCeil_le_twice hnom
    change (cfg.restoreSteps : ℝ) ≤ 2 * (4096 * S ^ 4 * l) at hh
    nlinarith only [hh]
  have hk : (cfg.restoreGroups : ℝ) ≤ 200 * l := by
    have hh := positiveCeil_le_twice (show 1 ≤ 100 * l by linarith only [hl])
    change (cfg.restoreGroups : ℝ) ≤ 2 * (100 * l) at hh
    linarith only [hh]
  have hB : (cfg.restoreBatch : ℝ) ≤ 1 + 10 ^ 19 * S ^ 18 * p.σ ^ 2 := by
    have hh := positiveCeil_upper (show 0 ≤ 10 ^ 19 * S ^ 18 * p.σ ^ 2 by positivity)
    change (cfg.restoreBatch : ℝ) ≤ 10 ^ 19 * S ^ 18 * p.σ ^ 2 + 1 at hh
    linarith only [hh]
  have hh := mul_le_mul (mul_le_mul hB hk (by positivity) (by positivity)) hN (by positivity) (by positivity)
  have he : (1 + 10 ^ 19 * S ^ 18 * p.σ ^ 2) * (200 * l) * (8192 * S ^ 4 * l) =
      (1638400 * S ^ 4 * (1 + 10 ^ 19 * S ^ 18 * p.σ ^ 2)) * l ^ 2 := by ring
  rw [he] at hh
  have hl2 := log_factor_square hS1
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hl2
    (show 0 ≤ 1638400 * S ^ 4 * (1 + 10 ^ 19 * S ^ 18 * p.σ ^ 2) by positivity))
  have hb : (cfg.restoreBatch : ℝ) * cfg.restoreGroups * cfg.restoreSteps ≤
      10 ^ 27 * (S ^ 38 + S ^ 48 * p.σ ^ 2) := by
    have h5 : S ^ 5 ≤ S ^ 38 := pow_le_pow_right₀ hS1 (by norm_num)
    have h23 : S ^ 23 * p.σ ^ 2 ≤ S ^ 48 * p.σ ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS1 (by norm_num : 23 ≤ 48)) (sq_nonneg p.σ)
    nlinarith only [hh', h5, h23, pow_nonneg hS0.le 38, show 0 ≤ S ^ 48 * p.σ ^ 2 by positivity]
  apply hb.trans
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  exact mul_le_of_le_one_right (by positivity) hε2

lemma repetition_cost_bounds (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let l := 1 + Real.log (S / p.ε)
    1 ≤ l ∧ l ≤ S ^ 38 / p.ε ^ 2 ∧
      ((tuning p.toPublic).trials : ℝ) ≤ 201 * l ∧
      ((tuning p.toPublic).validationGroups : ℝ) ≤ 301 * l := by
  let S := scale p.toPublic
  let l := 1 + Real.log (S / p.ε)
  have hS1 : 1 ≤ S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hS0 : 0 < S := by linarith only [hS1]
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hε1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hl : 1 ≤ l := by
    have hh : 1 ≤ S / p.ε := (le_div_iff₀ hε).mpr (by linarith only [hS1, hε1])
    dsimp [l]
    linarith only [Real.log_nonneg hh]
  have hupper : l ≤ S ^ 38 / p.ε ^ 2 := by
    have hh : l ≤ S / p.ε := by dsimp [l]; linarith only [Real.log_le_sub_one_of_pos (div_pos hS0 hε)]
    apply hh.trans
    apply (div_le_div_iff₀ hε (sq_pos_of_pos hε)).mpr
    have hpow : S ≤ S ^ 38 := le_self_pow₀ hS1 (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hε1 hS0.le
    have hb := mul_le_mul_of_nonneg_right (hm.trans (by simpa only [mul_one] using hpow)) hε.le
    nlinarith only [hb]
  have hR : ((tuning p.toPublic).trials : ℝ) ≤ 201 * l := by
    have hh := positiveCeil_upper (show 0 ≤ 200 * l by linarith only [hl])
    change ((tuning p.toPublic).trials : ℝ) ≤ 200 * l + 1 at hh
    linarith only [hh, hl]
  have hk : ((tuning p.toPublic).validationGroups : ℝ) ≤ 301 * l := by
    have hh := positiveCeil_upper (show 0 ≤ 300 * l by linarith only [hl])
    change ((tuning p.toPublic).validationGroups : ℝ) ≤ 300 * l + 1 at hh
    linarith only [hh, hl]
  exact ⟨hl, hupper, hR, hk⟩

lemma validation_samples_budget (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let l := 1 + Real.log (S / p.ε)
    let cfg := tuning p.toPublic
    (cfg.validationBatch : ℝ) * cfg.validationGroups ≤
      10 ^ 18 * (S ^ 38 + S ^ 14 * p.σ ^ 2 * l) / p.ε ^ 2 := by
  let S := scale p.toPublic
  let l := 1 + Real.log (S / p.ε)
  let cfg := tuning p.toPublic
  have ⟨hl, hlu, _, hk⟩ := repetition_cost_bounds p hp
  have hS0 : 0 < S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hl0 : 0 ≤ l := by dsimp [l, S]; linarith only [hl]
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hB : (cfg.validationBatch : ℝ) ≤ 1 + 10 ^ 15 * S ^ 14 * p.σ ^ 2 / p.ε ^ 2 := by
    have hh := positiveCeil_upper (show 0 ≤ 10 ^ 15 * S ^ 14 * p.σ ^ 2 / p.ε ^ 2 by positivity)
    change (cfg.validationBatch : ℝ) ≤ 10 ^ 15 * S ^ 14 * p.σ ^ 2 / p.ε ^ 2 + 1 at hh
    linarith only [hh]
  have hh := mul_le_mul hB hk (by positivity) (by positivity)
  have he : (1 + 10 ^ 15 * S ^ 14 * p.σ ^ 2 / p.ε ^ 2) * (301 * l) =
      301 * l + 301 * 10 ^ 15 * S ^ 14 * p.σ ^ 2 * l / p.ε ^ 2 := by ring
  rw [he] at hh
  have hh' := hh.trans (add_le_add (mul_le_mul_of_nonneg_left hlu (by norm_num : (0 : ℝ) ≤ 301)) le_rfl)
  have he' : 301 * (S ^ 38 / p.ε ^ 2) + 301 * 10 ^ 15 * S ^ 14 * p.σ ^ 2 * l / p.ε ^ 2 =
      (301 * S ^ 38 + 301 * 10 ^ 15 * (S ^ 14 * p.σ ^ 2 * l)) / p.ε ^ 2 := by ring
  rw [he'] at hh'
  apply hh'.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg p.ε)
  have hA : 0 ≤ S ^ 38 := by positivity
  have hB0 : 0 ≤ S ^ 14 * p.σ ^ 2 * l := by positivity
  nlinarith only [hA, hB0]

set_option maxRecDepth 4096 in
lemma calls_budget_bound (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let l := 1 + Real.log (S / p.ε)
    (calls (tuning p.toPublic) : ℝ) ≤
      10 ^ 47 * (((S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε) * l +
        S ^ 14 * p.σ ^ 2 * l ^ 2) / p.ε ^ 2) := by
  let S := scale p.toPublic
  let l := 1 + Real.log (S / p.ε)
  let cfg := tuning p.toPublic
  have hS0 : 0 < S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hσ := hp.2.2.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 : 0 ≤ l := by have hh := (repetition_cost_bounds p hp).1; dsimp [l, S]; linarith only [hh]
  have hA : 0 ≤ S ^ 38 := by positivity
  have hB : 0 ≤ S ^ 48 * p.σ ^ 2 := by positivity
  have hC : 0 ≤ S ^ 60 * p.σ / p.ε := div_nonneg (mul_nonneg (pow_nonneg hS0.le _) hσ) hε.le
  have hD : 0 ≤ S ^ 14 * p.σ ^ 2 * l := by positivity
  have hv := validation_samples_budget p hp
  have ht := training_samples_budget p hp
  have hr := restoration_samples_budget p hp
  have hh := add_le_add (add_le_add hv ht) hr
  have he : 10 ^ 18 * (S ^ 38 + S ^ 14 * p.σ ^ 2 * l) / p.ε ^ 2 +
      10 ^ 42 * (S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε) / p.ε ^ 2 +
      10 ^ 27 * (S ^ 38 + S ^ 48 * p.σ ^ 2) / p.ε ^ 2 =
      (10 ^ 18 * (S ^ 38 + S ^ 14 * p.σ ^ 2 * l) +
        10 ^ 42 * (S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε) +
        10 ^ 27 * (S ^ 38 + S ^ 48 * p.σ ^ 2)) / p.ε ^ 2 := by ring
  rw [he] at hh
  have hsum : (cfg.validationBatch : ℝ) * cfg.validationGroups +
      ((∑ k ∈ Finset.range cfg.steps, batchSize cfg k : ℕ) : ℝ) +
      (cfg.restoreBatch : ℝ) * cfg.restoreGroups * cfg.restoreSteps ≤
      3 * 10 ^ 42 * (S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε +
        S ^ 14 * p.σ ^ 2 * l) / p.ε ^ 2 := by
    apply hh.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg p.ε)
    nlinarith only [hA, hB, hC, hD]
  have hR := (repetition_cost_bounds p hp).2.2.1
  have hc : (calls cfg : ℝ) = 2 * (cfg.trials : ℝ) *
      ((cfg.validationBatch : ℝ) * cfg.validationGroups +
        ((∑ k ∈ Finset.range cfg.steps, batchSize cfg k : ℕ) : ℝ) +
        (cfg.restoreBatch : ℝ) * cfg.restoreGroups * cfg.restoreSteps) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (StochasticEqualityExecution.total_calls cfg)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hh
  rw [hc]
  have hbound := mul_le_mul (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2)) hsum
    (by positivity) (by positivity)
  have he' : (2 * (201 * l)) *
      (3 * 10 ^ 42 * (S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε + S ^ 14 * p.σ ^ 2 * l) / p.ε ^ 2) =
      (1206 * 10 ^ 42) * (((S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε) * l +
        S ^ 14 * p.σ ^ 2 * l ^ 2) / p.ε ^ 2) := by ring
  rw [he'] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right (by norm_num)
  exact div_nonneg (add_nonneg (mul_nonneg (add_nonneg (add_nonneg hA hB) hC) hl0)
    (by positivity)) (sq_nonneg p.ε)

lemma calls_le_ceiling (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let l := 1 + Real.log (S / p.ε)
    calls (tuning p.toPublic) ≤ ⌈10 ^ 47 * (((S ^ 38 + S ^ 48 * p.σ ^ 2 + S ^ 60 * p.σ / p.ε) * l +
      S ^ 14 * p.σ ^ 2 * l ^ 2) / p.ε ^ 2)⌉₊ := by
  have hh := (calls_budget_bound p hp).trans (Nat.le_ceil _)
  exact_mod_cast hh

end LongTails.Proofs.StochasticEqualityCost
