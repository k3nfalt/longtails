import LongTails.Proofs.StochasticMfcqSampling

namespace LongTails.Proofs.StochasticMfcqBudget
open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq
open LongTails.Algorithms.StochasticEnvelopeProgram

lemma reset_count_le (N q : ℕ) :
    ((Finset.range N).filter (fun k => k % q = 0)).card ≤ N / q + 1 := by
  classical
  rw [← Finset.card_range (N / q + 1)]
  apply Finset.card_le_card_of_injOn (f := fun k => k / q)
    (s := (Finset.range N).filter (fun k => k % q = 0)) (t := Finset.range (N / q + 1))
  · intro k hk
    apply Finset.mem_range.mpr
    have hkN := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hkN.le)
  · intro a ha b hb he
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    have ha' := Nat.mod_add_div a q
    have hb' := Nat.mod_add_div b q
    change a / q = b / q at he
    rw [ha0] at ha'
    rw [hb0, ← he] at hb'
    omega

lemma calls_sum (p : Params) :
    calls p = replicas p * ∑ k ∈ Finset.range (outerSteps p), batchSize p k := by
  unfold calls
  rw [StochasticEnvelopeExecution.slotCalls_sum]
  simp only [Nat.zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact Nat.mul_comm _ _

lemma batch_sum_upper (p : Params) :
    (∑ k ∈ Finset.range (outerSteps p), batchSize p k) ≤
      (outerSteps p / epochLength p + 1) * resetBatch p + outerSteps p * incrementBatch p := by
  classical
  have hb : ∀ k, batchSize p k ≤ (if k % epochLength p = 0 then resetBatch p else 0) + incrementBatch p := by
    intro k
    unfold batchSize
    split_ifs <;> omega
  calc
    _ ≤ ∑ k ∈ Finset.range (outerSteps p), ((if k % epochLength p = 0 then resetBatch p else 0) + incrementBatch p) :=
      Finset.sum_le_sum (fun k _ => hb k)
    _ = ((Finset.range (outerSteps p)).filter (fun k => k % epochLength p = 0)).card * resetBatch p +
        outerSteps p * incrementBatch p := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _
      (reset_count_le _ _)) _

lemma schedule_cost_bound (N a ell q : ℝ) (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hl : 0 ≤ ell) (hq : 1 ≤ q)
    (hqa : N * a ≤ q * (N * ell + a + 1))
    (hqb : q * (N * ell + a + 1) ≤ 2 * N * a) :
    (N / q + 1) * (2 + 1152 * a ^ 2) + N * (2 + 72 * q * ell ^ 2) ≤
      3500 * (a ^ 2 + N * (1 + a * ell)) := by
  have hq0 : 0 < q := by linarith
  have hN0 : 0 < N := by linarith
  have hratio : N * a ^ 2 / q ≤ N * a * ell + a ^ 2 + a := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hqa ha]
  have hinc : q * ell ^ 2 ≤ 2 * a * ell := by
    have hh : q * ell ≤ 2 * a := by
      have hnon : 0 ≤ q * (a + 1) := by positivity
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh hl]
  have hdiv : N / q ≤ N := (div_le_iff₀ hq0).mpr (by nlinarith)
  have he : (N / q + 1) * (2 + 1152 * a ^ 2) + N * (2 + 72 * q * ell ^ 2) =
      2 * (N / q) + 2 + 1152 * (N * a ^ 2 / q) + 1152 * a ^ 2 + 2 * N +
        72 * N * (q * ell ^ 2) := by ring
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left hinc hN0.le
  have hprod : 0 ≤ N * a * ell := by positivity
  nlinarith [sq_nonneg (a - 1)]

lemma single_epoch_cost_bound (N a ell : ℝ) (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hl : 0 ≤ ell) (ht : N * a ≤ N * ell + a + 1) :
    N * (2 + 1152 * a ^ 2) ≤ 3500 * (a ^ 2 + N * (1 + a * ell)) := by
  have hh := mul_le_mul_of_nonneg_right ht ha
  have hprod : 0 ≤ N * a * ell := by positivity
  nlinarith [sq_nonneg (a - 1)]


lemma epoch_ratio_eq (p : Params) (hp : spec.valid p) :
    (outerSteps p : ℝ) * p.σ * p.H /
        (outerSteps p * p.L * precision p + p.H * (p.σ + precision p)) =
      (outerSteps p : ℝ) * (p.σ / precision p) /
        (outerSteps p * (p.L / p.H) + p.σ / precision p + 1) := by
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  have hH : 0 < p.H := by linarith [hp.2.1]
  have hσ : 0 ≤ p.σ := hp.2.2.1
  have hL : 0 ≤ p.L := hp.2.2.2.1
  have hden : 0 < outerSteps p * p.L * precision p + p.H * (p.σ + precision p) := by positivity
  have hden' : 0 < outerSteps p * (p.L / p.H) + p.σ / precision p + 1 := by positivity
  apply (div_eq_div_iff hden.ne' hden'.ne').mpr
  field_simp
  ring

lemma batch_upper (p : Params) (hp : spec.valid p) :
    (resetBatch p : ℝ) ≤ 2 + 1152 * (p.σ / precision p) ^ 2 ∧
    (incrementBatch p : ℝ) ≤ 2 + 72 * epochLength p * (p.L / p.H) ^ 2 := by
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  have hH : 0 < p.H := by linarith [hp.2.1]
  constructor
  · have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 1152 * p.σ ^ 2 / precision p ^ 2)
    unfold resetBatch
    push_cast
    simp only [div_pow, ← mul_div_assoc]
    linarith
  · have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 72 * (epochLength p : ℝ) * p.L ^ 2 / p.H ^ 2)
    unfold incrementBatch
    push_cast
    simp only [div_pow, ← mul_div_assoc]
    linarith


lemma rounded_schedule (N a ell : ℝ) (hN : 0 ≤ N) (ha : 0 ≤ a) (hl : 0 ≤ ell) :
    let q := max 1 ⌈N * a / (N * ell + a + 1)⌉₊
    N * a ≤ (q : ℝ) * (N * ell + a + 1) ∧
      (q = 1 → N * a ≤ N * ell + a + 1) ∧
      (q ≠ 1 → (q : ℝ) * (N * ell + a + 1) ≤ 2 * N * a) := by
  let t := N * a / (N * ell + a + 1)
  let q := max 1 ⌈t⌉₊
  change N * a ≤ (q : ℝ) * (N * ell + a + 1) ∧
    (q = 1 → N * a ≤ N * ell + a + 1) ∧
    (q ≠ 1 → (q : ℝ) * (N * ell + a + 1) ≤ 2 * N * a)
  have hd : 0 < N * ell + a + 1 := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hq : 1 ≤ q := le_max_left _ _
  have hqt : t ≤ (q : ℝ) := (Nat.le_ceil t).trans (by exact_mod_cast (le_max_right 1 ⌈t⌉₊))
  have hlow : N * a ≤ (q : ℝ) * (N * ell + a + 1) := (div_le_iff₀ hd).mp hqt
  refine ⟨hlow, ?_, ?_⟩
  · intro he
    simpa only [he, Nat.cast_one, one_mul] using hlow
  · intro he
    have hqc : q = ⌈t⌉₊ := by dsimp [q] at *; omega
    have hc : (q : ℝ) < t + 1 := by rw [hqc]; exact Nat.ceil_lt_add_one ht
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hupper : (q : ℝ) ≤ 2 * t := by linarith
    dsimp [t] at hupper
    rw [← mul_div_assoc] at hupper
    simpa only [mul_assoc] using (le_div_iff₀ hd).mp hupper


lemma total_calls_bound (p : Params) (hp : spec.valid p) :
    (calls p : ℝ) ≤ (replicas p : ℝ) *
      (3500 * ((p.σ / precision p) ^ 2 + outerSteps p *
        (1 + (p.σ / precision p) * (p.L / p.H)))) := by
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  have hH : 0 < p.H := by linarith [hp.2.1]
  have ha : 0 ≤ p.σ / precision p := div_nonneg hp.2.2.1 hδ.le
  have hl : 0 ≤ p.L / p.H := div_nonneg hp.2.2.2.1 hH.le
  have hN : (1 : ℝ) ≤ outerSteps p := by exact_mod_cast StochasticMfcqTuning.outerSteps_positive p
  have hq : (1 : ℝ) ≤ epochLength p := by
    exact_mod_cast (Nat.succ_le_of_lt (StochasticMfcqTuning.batch_sizes_positive p).1)
  have hqeq : epochLength p = max 1 ⌈(outerSteps p : ℝ) * (p.σ / precision p) /
      (outerSteps p * (p.L / p.H) + p.σ / precision p + 1)⌉₊ := by
    unfold epochLength
    rw [epoch_ratio_eq p hp]
  have ht := rounded_schedule (outerSteps p : ℝ) (p.σ / precision p) (p.L / p.H)
    (Nat.cast_nonneg _) ha hl
  rw [← hqeq] at ht
  have hb := batch_upper p hp
  rw [calls_sum, Nat.cast_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  by_cases he : epochLength p = 1
  · have hs : (∑ k ∈ Finset.range (outerSteps p), batchSize p k) = outerSteps p * resetBatch p := by
      simp only [batchSize, he, Nat.mod_one, ite_true, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    rw [hs, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hb.1 (Nat.cast_nonneg _)).trans
      (single_epoch_cost_bound _ _ _ hN ha hl (ht.2.1 he))
  · have hs : ((∑ k ∈ Finset.range (outerSteps p), batchSize p k) : ℝ) ≤
        ((outerSteps p / epochLength p : ℕ) + 1 : ℕ) * (resetBatch p : ℝ) +
          (outerSteps p : ℝ) * incrementBatch p := by exact_mod_cast batch_sum_upper p
    have hdiv : ((outerSteps p / epochLength p : ℕ) : ℝ) ≤
        (outerSteps p : ℝ) / epochLength p := Nat.cast_div_le
    have hepoch : 0 ≤ (outerSteps p : ℝ) / epochLength p + 1 := by positivity
    have hcoef : (((outerSteps p / epochLength p + 1 : ℕ) : ℝ)) ≤
        (outerSteps p : ℝ) / epochLength p + 1 := by
      push_cast
      linarith
    have hfirst := mul_le_mul hcoef hb.1 (Nat.cast_nonneg (resetBatch p)) hepoch
    have hsecond := mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg (outerSteps p))
    simpa only [Nat.cast_sum] using (hs.trans (add_le_add hfirst hsecond)).trans
      (schedule_cost_bound _ _ _ _ hN ha hl hq ht.1 (ht.2.2 he))


lemma outerSteps_upper (p : Params) (hp : spec.valid p) :
    (outerSteps p : ℝ) ≤ 2 + 2 * p.H * p.Δ / precision p ^ 2 := by
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  have hH : 0 < p.H := by linarith [hp.2.1]
  have hΔ : 0 ≤ p.Δ := hp.2.2.2.2.2.2.2.1
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * p.H * p.Δ / precision p ^ 2)
  unfold outerSteps
  push_cast
  linarith

lemma replicas_upper (p : Params) (hp : spec.valid p) :
    replicas p ≤ 1 + ⌈Real.log ((2 + 2 * p.H * p.Δ / precision p ^ 2) / p.ρ) / Real.log 4⌉₊ := by
  have hρ : 0 < p.ρ := hp.2.2.2.2.2.2.2.2.2.1
  have hN : 0 < (outerSteps p : ℝ) := by unfold outerSteps; positivity
  unfold replicas
  apply Nat.add_le_add_left
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  apply Real.log_le_log (div_pos hN hρ)
  exact div_le_div_of_nonneg_right (outerSteps_upper p hp) hρ.le

lemma rounded_call_budget (p : Params) (hp : spec.valid p) :
    calls p ≤ ⌈3500 * ((p.σ / precision p) ^ 2 +
      (2 + 2 * p.H * p.Δ / precision p ^ 2) * (1 + (p.σ / precision p) * (p.L / p.H)))⌉₊ *
      (1 + ⌈Real.log ((2 + 2 * p.H * p.Δ / precision p ^ 2) / p.ρ) / Real.log 4⌉₊) := by
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  have hH : 0 < p.H := by linarith [hp.2.1]
  have ha : 0 ≤ p.σ / precision p := div_nonneg hp.2.2.1 hδ.le
  have hl : 0 ≤ p.L / p.H := div_nonneg hp.2.2.2.1 hH.le
  have hfactor : 0 ≤ 1 + (p.σ / precision p) * (p.L / p.H) := by positivity
  have hc := total_calls_bound p hp
  have hcost : 3500 * ((p.σ / precision p) ^ 2 + outerSteps p *
      (1 + (p.σ / precision p) * (p.L / p.H))) ≤
      3500 * ((p.σ / precision p) ^ 2 + (2 + 2 * p.H * p.Δ / precision p ^ 2) *
        (1 + (p.σ / precision p) * (p.L / p.H))) := by
    nlinarith [mul_le_mul_of_nonneg_right (outerSteps_upper p hp) hfactor]
  have hround := hcost.trans (Nat.le_ceil _)
  have hr : (replicas p : ℝ) ≤
      (1 + ⌈Real.log ((2 + 2 * p.H * p.Δ / precision p ^ 2) / p.ρ) / Real.log 4⌉₊ : ℕ) := by
    exact_mod_cast replicas_upper p hp
  have hmul := mul_le_mul hr hround (by positivity : 0 ≤
      3500 * ((p.σ / precision p) ^ 2 + outerSteps p * (1 + (p.σ / precision p) * (p.L / p.H))))
      (Nat.cast_nonneg _)
  have hfinal := hc.trans hmul
  rw [mul_comm] at hfinal
  exact_mod_cast hfinal


lemma explicit_call_budget (p : Params) (hp : spec.valid p) :
    calls p ≤ ⌈3500 * (1600 * p.H ^ 2 * p.σ ^ 2 / (p.μ ^ 2 * (min p.ε (min 1 p.τ)) ^ 2) +
      (2 + 3200 * p.H ^ 3 * p.Δ / (p.μ ^ 2 * (min p.ε (min 1 p.τ)) ^ 2)) *
        (1 + 40 * p.σ * p.L / (p.μ * min p.ε (min 1 p.τ))))⌉₊ *
      (1 + ⌈Real.log ((2 + 3200 * p.H ^ 3 * p.Δ / (p.μ ^ 2 * (min p.ε (min 1 p.τ)) ^ 2)) /
        p.ρ) / Real.log 4⌉₊) := by
  have hH : 0 < p.H := by linarith [hp.2.1]
  have hμ : 0 < p.μ := hp.2.2.2.2.1
  have hτ : 0 < p.τ := hp.2.2.2.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.1
  let e := min p.ε (min 1 p.τ)
  have he : 0 < e := lt_min hε (lt_min (by norm_num) hτ)
  have hd : precision p = p.μ * e / (40 * p.H) := rfl
  have hn : (p.σ / precision p) ^ 2 = 1600 * p.H ^ 2 * p.σ ^ 2 / (p.μ ^ 2 * e ^ 2) := by
    rw [hd]
    field_simp
    ring
  have hs : 2 * p.H * p.Δ / precision p ^ 2 = 3200 * p.H ^ 3 * p.Δ / (p.μ ^ 2 * e ^ 2) := by
    rw [hd]
    field_simp
    ring
  have hc : (p.σ / precision p) * (p.L / p.H) = 40 * p.σ * p.L / (p.μ * e) := by
    rw [hd]
    field_simp
  have hh := rounded_call_budget p hp
  rw [hn, hs, hc] at hh
  exact hh

end LongTails.Proofs.StochasticMfcqBudget
