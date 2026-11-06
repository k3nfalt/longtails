import LongTails.Proofs.CoupledCubicRun

namespace LongTails.Proofs.CoupledCubicBudget

open OracleTemplate MeasureTheory
open LongTails.Setups.StrongGrowthFiniteSumSecondOrder
open LongTails.Proofs.CoupledCubicExecution
open LongTails.Proofs.CoupledCubicRun
open LongTails.Algorithms.CoupledCubicTournament

lemma batchSize_positive (p : Params) (hκ : 1 ≤ p.κ) : 0 < batchSize p := by
  have hk : 0 < p.κ := lt_of_lt_of_le (by norm_num) hκ
  have hc := Nat.le_ceil (10 ^ 20 * p.κ * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ))
  have hp : 0 < 10 ^ 20 * p.κ * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) := by positivity
  exact Nat.cast_pos.mp (hp.trans_le hc)

lemma batchSize_suffices (p : Params) (hκ : 1 ≤ p.κ) :
    1024 * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) * p.κ ≤
      (batchSize p : ℝ) * (1 / 100000000 : ℝ) ^ 2 := by
  have hk : 0 ≤ p.κ := by linarith
  have hc := Nat.le_ceil (10 ^ 20 * p.κ * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ))
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (1 / 100000000 : ℝ))
  have hp : 0 ≤ p.κ * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) := by positivity
  change 1024 * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) * p.κ ≤
    (⌈10 ^ 20 * p.κ * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ)⌉₊ : ℝ) * (1 / 100000000 : ℝ) ^ 2
  norm_num at hm ⊢
  nlinarith

lemma roundCount_suffices (p : Params) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    p.Δ < (roundCount p : ℝ) * (p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ)) := by
  have hr := Real.sqrt_pos.mpr hρ
  have he := Real.sqrt_pos.mpr hε
  have hd : 0 < p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ) := by positivity
  have hc := Nat.le_ceil (16000 * Real.sqrt p.ρ * p.Δ / (p.ε * Real.sqrt p.ε))
  have hm := mul_le_mul_of_nonneg_right hc hd.le
  have hid : (16000 * Real.sqrt p.ρ * p.Δ / (p.ε * Real.sqrt p.ε)) *
      (p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ)) = p.Δ := by
    field_simp
  rw [hid] at hm
  simp only [roundCount, Nat.cast_add, Nat.cast_one]
  nlinarith

lemma modelsPerRound_failure (p : Params) :
    (roundCount p : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ modelsPerRound p) ≤
      ENNReal.ofReal (1 / 3 : ℝ) := by
  have hp : 3 * (roundCount p : ℝ) < (2 : ℝ) ^ modelsPerRound p := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) (3 * roundCount p)
  have hq : 0 < (1 / 2 : ℝ) ^ modelsPerRound p := by positivity
  have hid : (2 : ℝ) ^ modelsPerRound p * (1 / 2 : ℝ) ^ modelsPerRound p = 1 := by
    rw [← mul_pow]
    norm_num
  have hm := mul_lt_mul_of_pos_right hp hq
  rw [hid] at hm
  have hreal : (roundCount p : ℝ) * (1 / 2 : ℝ) ^ modelsPerRound p ≤ 1 / 3 := by nlinarith
  have hh := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at hh
  exact hh

lemma probability_success {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (s : Set Ω) (hs : MeasurableSet s)
    (hbad : P sᶜ ≤ ENNReal.ofReal (1 / 3 : ℝ)) : ENNReal.ofReal (2 / 3 : ℝ) ≤ P s := by
  have he := MeasureTheory.measure_compl hs.compl (MeasureTheory.measure_ne_top P sᶜ)
  simp only [compl_compl, MeasureTheory.measure_univ] at he
  rw [he]
  have hn : ENNReal.ofReal (2 / 3 : ℝ) = 1 - ENNReal.ofReal (1 / 3 : ℝ) := by
    rw [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num,
      ENNReal.ofReal_sub 1 (by norm_num), ENNReal.ofReal_one]
  rw [hn]
  exact tsub_le_tsub_left hbad 1

lemma tuned_output_success (p : Params) (f : Fin p.n → p.E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hκ : 1 ≤ p.κ) (hρ : 0 < p.ρ) (hε : 0 < p.ε)
    (hSGC : ∀ y, (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) y‖ ^ 2 ≤
      p.κ * ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) y‖ ^ 2)
    (hRMS : ∀ y z, (p.n : ℝ)⁻¹ * ∑ i,
      ‖fderiv ℝ (gradient (f i)) y - fderiv ℝ (gradient (f i)) z‖ ^ 2 ≤
        p.ρ ^ 2 * ‖y - z‖ ^ 2)
    (hgap : ∀ y, LongTails.Setups.FiniteSumSmoothAndConvex.objective f p.x0 -
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f y ≤ p.Δ) :
    let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let replies : Fin p.n × p.E → Model p := fun ix =>
      (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
    ENNReal.ofReal (2 / 3 : ℝ) ≤
      (PMF.uniformOfFintype (Seeds p (batchSize p) (modelsPerRound p) (roundCount p))).toMeasure
        {ξ | CoupledCubicRun.jointAccurate p F
          (output p (batchSize p) (modelsPerRound p) (roundCount p) replies ξ)} := by
  have hfails := CoupledCubicRun.objective_output_failure p f hf hκ hρ hε hSGC hRMS hgap
    (batchSize p) (modelsPerRound p) (roundCount p) (batchSize_positive p hκ)
    (batchSize_suffices p hκ) (roundCount_suffices p hρ hε)
  apply probability_success _ _ (Set.toFinite _).measurableSet
  exact hfails.trans (modelsPerRound_failure p)

lemma method_success (p : Params) (hv : spec.valid p) (f : Fin p.n → p.E → ℝ)
    (O : Oracle (Fin p.n × p.E) (Model p)) (hadm : spec.admissible p f O)
    (B : ℕ) (hB : ((1 * batchSize p) * modelsPerRound p) * roundCount p ≤ B) :
    let A := method p (batchSize p) (modelsPerRound p) (roundCount p)
    spec.successful p f
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => B) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  rcases hv with ⟨hκ, hρ, _, hε⟩
  rcases hadm with ⟨hf, hSGC, hRMS, hgap, hO⟩
  let replies : Fin p.n × p.E → Model p := fun ix =>
    (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  have hanswer : ∀ history q seed, O.answer history (0, q) seed = replies q := by
    rintro history ⟨i, x⟩ seed
    exact hO history seed i x
  change MeasurableSet {seed : Seeds p (batchSize p) (modelsPerRound p) (roundCount p) ×
      ((k : ℕ) → O.Seed k) | jointAccurate p F
        (execute O (method p (batchSize p) (modelsPerRound p) (roundCount p)) (fun _ => B) seed.1 seed.2)} ∧ _
  refine ⟨execute_event_measurable p (batchSize p) (modelsPerRound p) (roundCount p) B hB
    replies O hanswer (jointAccurate p F), ?_⟩
  have hset : {seed : Seeds p (batchSize p) (modelsPerRound p) (roundCount p) ×
      ((k : ℕ) → O.Seed k) | jointAccurate p F
        (execute O (method p (batchSize p) (modelsPerRound p) (roundCount p)) (fun _ => B) seed.1 seed.2)} =
      {ξ : Seeds p (batchSize p) (modelsPerRound p) (roundCount p) |
        jointAccurate p F (output p (batchSize p) (modelsPerRound p) (roundCount p) replies ξ)} ×ˢ Set.univ := by
    ext seed
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
    rw [execute_method p (batchSize p) (modelsPerRound p) (roundCount p) B hB replies O hanswer]
  change ENNReal.ofReal (2 / 3 : ℝ) ≤
    ((PMF.uniformOfFintype (Seeds p (batchSize p) (modelsPerRound p) (roundCount p))).toMeasure.prod
      (O.law : Measure ((k : ℕ) → O.Seed k)))
      {seed : Seeds p (batchSize p) (modelsPerRound p) (roundCount p) × ((k : ℕ) → O.Seed k) |
        jointAccurate p F (execute O (method p (batchSize p) (modelsPerRound p) (roundCount p))
          (fun _ => B) seed.1 seed.2)}
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  exact tuned_output_success p f hf hκ hρ hε hSGC hRMS hgap

end LongTails.Proofs.CoupledCubicBudget
