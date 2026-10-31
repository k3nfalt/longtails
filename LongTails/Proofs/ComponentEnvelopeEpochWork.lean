import LongTails.Proofs.ComponentEnvelopeEpochExecution
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Setups.InterpolatedGeneralizedFiniteSum

noncomputable def epochQueryLoss (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E) :
    (k : ℕ) → (Fin k → Fin p.n) → EpochState p.E → ℝ
  | 0, _, _ => 0
  | k + 1, samples, state =>
      let q := queryMix s snapshot state
      let v := Program.eval g (componentPlan p (samples 0) q) - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ i, cache i
      let next := epochUpdate p s snapshot v state
      F q + epochQueryLoss p g F s snapshot cache k (fun j => samples j.succ) next

lemma epoch_query_sum_bound (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (hR : 0 ≤ p.R) (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E) (C : ℝ)
    (hquery : ∀ state : EpochState p.E,
      state.y ∈ Metric.closedBall p.x0 p.R → state.z ∈ Metric.closedBall p.x0 p.R →
      F (queryMix s snapshot state) ≤ F snapshot + F state.y + C)
    (k : ℕ) (samples : Fin k → Fin p.n) (state : EpochState p.E)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R) :
    epochQueryLoss p g F s snapshot cache k samples state ≤
      k * (F snapshot + C) + epochLoss p g F s snapshot cache k samples state + F state.y -
        F (Program.eval g (epochPlan p s snapshot cache k samples state)).y := by
  induction k generalizing state with
  | zero => simp [epochQueryLoss, epochLoss, epochPlan, Program.eval]
  | succ k ih =>
      let next := epochUpdate p s snapshot
        (Program.eval g (componentPlan p (samples 0) (queryMix s snapshot state)) - cache (samples 0) + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
      let rest := fun j : Fin k => samples j.succ
      have hn : next.y ∈ Metric.closedBall p.x0 p.R ∧ next.z ∈ Metric.closedBall p.x0 p.R :=
        epochUpdate_mem p hR s snapshot _ state
      have ht := ih rest next hn.1 hn.2
      have hq := hquery state hy hz
      simp only [epochQueryLoss, epochLoss, epochPlan, Program.eval_bind, Nat.cast_add, Nat.cast_one]
      change F (queryMix s snapshot state) + epochQueryLoss p g F s snapshot cache k rest next ≤
        ((k : ℝ) + 1) * (F snapshot + C) +
          (F next.y + epochLoss p g F s snapshot cache k rest next) + F state.y -
          F (Program.eval g (epochPlan p s snapshot cache k rest next)).y
      linarith

lemma epoch_cost_expect (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (hR : 0 ≤ p.R) (s : ℕ) (snapshot : p.E) (cache : Fin p.n → p.E) (C β : ℝ)
    (hcost : ∀ state : EpochState p.E,
      state.y ∈ Metric.closedBall p.x0 p.R → state.z ∈ Metric.closedBall p.x0 p.R →
      (𝔼 i : Fin p.n, (Program.cost g (componentPlan p i (queryMix s snapshot state)) : ℝ)) ≤
        C * (1 + β * F (queryMix s snapshot state)))
    (k : ℕ) (state : EpochState p.E)
    (hy : state.y ∈ Metric.closedBall p.x0 p.R) (hz : state.z ∈ Metric.closedBall p.x0 p.R) :
    (𝔼 samples : Fin k → Fin p.n, (Program.cost g (epochPlan p s snapshot cache k samples state) : ℝ)) ≤
      C * (k + β * (𝔼 samples : Fin k → Fin p.n, epochQueryLoss p g F s snapshot cache k samples state)) := by
  induction k generalizing state with
  | zero => simp [epochPlan, Program.cost, epochQueryLoss]
  | succ k ih =>
      let next := fun i => epochUpdate p s snapshot
        (Program.eval g (componentPlan p i (queryMix s snapshot state)) - cache i + (p.n : ℝ)⁻¹ • ∑ j, cache j) state
      have hn (i : Fin p.n) : (next i).y ∈ Metric.closedBall p.x0 p.R ∧ (next i).z ∈ Metric.closedBall p.x0 p.R :=
        epochUpdate_mem p hR s snapshot _ state
      have ht (i : Fin p.n) := ih (next i) (hn i).1 (hn i).2
      rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ,
        OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
      simp only [epochPlan, Program.cost_bind, epochQueryLoss, Fin.cons_zero, Fin.cons_succ,
        Nat.cast_add, Nat.cast_one, Finset.expect_add_distrib, Fintype.expect_const]
      have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => ht i)
      have hc := hcost state hy hz
      simp only [mul_add, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hav
      change (𝔼 i : Fin p.n, (Program.cost g (componentPlan p i (queryMix s snapshot state)) : ℝ)) +
        (𝔼 i : Fin p.n, 𝔼 samples : Fin k → Fin p.n, (Program.cost g (epochPlan p s snapshot cache k samples (next i)) : ℝ)) ≤
        C * ((k : ℝ) + 1 + β * (F (queryMix s snapshot state) +
          (𝔼 i : Fin p.n, 𝔼 samples : Fin k → Fin p.n, epochQueryLoss p g F s snapshot cache k samples (next i))))
      nlinarith
lemma epoch_nominal_cost_from_work (p : Params) (g : Fin p.n × p.E → p.E)
    (F : p.E → ℝ) (hR : 0 ≤ p.R) (C β W : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hcost : ∀ x ∈ Metric.closedBall p.x0 p.R,
      (𝔼 i : Fin p.n, (Program.cost g (componentPlan p i x) : ℝ)) ≤ C * (1 + β * F x))
    (s : ℕ) (w : p.E) (cache : Fin p.n → p.E) (y z : p.E)
    (hw : w ∈ Metric.closedBall p.x0 p.R)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R)
    (hwork : (p.n : ℝ) * F w + (𝔼 samples : Fin p.n → Fin p.n,
      epochQueryLoss p g F s w cache p.n samples ⟨y, z, 0⟩) ≤ W) :
    (∑ i, (Program.cost g (componentPlan p i w) : ℝ)) +
      (𝔼 samples : Fin p.n → Fin p.n, (Program.cost g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩) : ℝ)) ≤
      C * (2 * p.n + β * W) := by
  have hc := epoch_cost_expect p g F hR s w cache C β
    (fun state hsy hsz => hcost _ (queryMix_mem p s w state hw hsy hsz)) p.n ⟨y, z, 0⟩ hy hz
  have hs := mul_le_mul_of_nonneg_left (hcost w hw) (Nat.cast_nonneg p.n : (0 : ℝ) ≤ p.n)
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin] at hs
  have hn : (p.n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.n)
  rw [mul_div_cancel₀ _ hn] at hs
  have hscaled := mul_le_mul_of_nonneg_left hwork (mul_nonneg hC hβ)
  nlinarith

lemma epoch_uniform_cost (p : Params) (g : Fin p.n × p.E → p.E)
    (hR : 0 ≤ p.R) (B : ℝ)
    (hcost : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      (Program.cost g (componentPlan p i x) : ℝ) ≤ B)
    (s : ℕ) (w : p.E) (cache : Fin p.n → p.E) (y z : p.E)
    (hw : w ∈ Metric.closedBall p.x0 p.R)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R) :
    (∑ i, (Program.cost g (componentPlan p i w) : ℝ)) +
      (𝔼 samples : Fin p.n → Fin p.n, (Program.cost g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩) : ℝ)) ≤
      2 * p.n * B := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcost i w hw)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hc := epoch_cost_expect p g (fun _ => 0) hR s w cache B 0
    (fun state hsy hsz => by
      have hh := Finset.expect_le_expect (s := Finset.univ)
        (fun i _ => hcost i _ (queryMix_mem p s w state hw hsy hsz))
      simpa only [Fintype.expect_const, mul_zero, add_zero, mul_one] using hh)
    p.n ⟨y, z, 0⟩ hy hz
  simp only [zero_mul, add_zero] at hc
  nlinarith

end OracleTemplate.ComponentEnvelope
