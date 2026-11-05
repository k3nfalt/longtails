import LongTails.Algorithms.SymmetricThirdOrder
import LongTails.Proofs.SampledQueryPlan

namespace LongTails.Proofs.SymmetricThirdOrderExecution

open OracleTemplate LongTails.Algorithms.SymmetricThirdOrder
open QueryPlan
open scoped BigOperators

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma samplePlan_eval (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (x : E) (k call : ℕ) :
    sampledEval oracle ξ (samplePlan x k) call = fun i => oracle x (ξ (call + i.val)) := by
  induction k generalizing call with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [samplePlan, sampledEval, sampledEval_map, ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cons_succ, Fin.val_succ]
      congr 2
      omega

lemma groupedPlan_eval (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (x : E) (m k call : ℕ) :
    sampledEval oracle ξ (groupedPlan x m k) call =
      fun i j => oracle x (ξ (call + m * i.val + j.val)) := by
  induction k generalizing call with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [groupedPlan, sampledEval_bind, sampledEval_map, samplePlan_eval, ih]
    funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · simp
    · simp only [Fin.cons_succ, Fin.val_succ]
      congr 2
      simp only [Nat.mul_add, Nat.mul_one]
      omega

lemma gradientPlan_eval (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (x : E) (call : ℕ) :
    sampledEval oracle ξ (gradientPlan cfg x) call =
      gradientPilot cfg.tolerance (fun (i : Fin cfg.groups) (j : Fin cfg.batch) => (oracle x (ξ (call + cfg.batch * i.val + j.val))).1) := by
  simp only [gradientPlan, sampledEval_map, groupedPlan_eval]

lemma hessianPlan_eval [CompleteSpace E] (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (x : E) (call : ℕ) :
    sampledEval oracle ξ (hessianPlan cfg x) call =
      hessianPilot cfg.σh (fun i : Fin cfg.groups => (oracle x (ξ (call + i.val))).2) := by
  simp only [hessianPlan, sampledEval_map, samplePlan_eval]

lemma meanPlan_eval (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (m : ℕ) (x : E) (call : ℕ) :
    sampledEval oracle ξ (meanPlan m x) call =
      (1 / (m : ℝ)) • ∑ i : Fin m, (oracle x (ξ (call + i.val))).1 := by
  simp only [meanPlan, sampledEval_map, samplePlan_eval]

lemma modelGradientPlan_eval (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (c y : E) (B : E →L[ℝ] E) (call : ℕ) :
    sampledEval oracle ξ (modelGradientPlan cfg c y B) call =
      (1 / 2 : ℝ) • (sampledEval oracle ξ (gradientPlan cfg y) call +
        sampledEval oracle ξ (gradientPlan cfg (c - (y - c))) (call + cfg.batch * cfg.groups)) +
      kernelGradient B cfg.L cfg.δ (y - c) := by
  simp only [modelGradientPlan, sampledEval_bind, sampledEval_map]

lemma sampledEval_cast (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    {U : Type} {k l : ℕ} (h : k = l) (plan : QueryPlan E (Reply E) U k) (call : ℕ) :
    sampledEval oracle ξ (h ▸ plan) call = sampledEval oracle ξ plan call := by
  subst l
  rfl

lemma cleanupPlan_eval [CompleteSpace E] (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (c y : E) (B : E →L[ℝ] E) (call : ℕ) :
    sampledEval oracle ξ (cleanupPlan cfg c y B) call =
      let qg := sampledEval oracle ξ (modelGradientPlan cfg c y B) call
      let Hp := sampledEval oracle ξ (hessianPlan cfg y)
        (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups))
      let Hm := sampledEval oracle ξ (hessianPlan cfg (c - (y - c)))
        (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) + cfg.groups)
      let Hq := shiftedHessian ((1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B cfg.L cfg.δ (y - c)) 0
      let z := cleanupPoint cfg.C cfg.x0 y Hq cfg.δ qg
      (z, -qg - Hq (z - y) - cfg.δ • (z - y)) := by
  simp only [cleanupPlan, sampledEval_bind, sampledEval_map]

lemma roundPlan_eval [CompleteSpace E] (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (s : OuterState E) (call : ℕ) :
    sampledEval oracle ξ (roundPlan cfg s) call =
      let c := outerCenter cfg.δ s
      let B := shiftedHessian (sampledEval oracle ξ (hessianPlan cfg c) call) (9 * cfg.σh)
      let y := sampledEval oracle ξ (innerPlan cfg c B cfg.innerRounds cfg.x0) (call + cfg.groups)
      let zn := sampledEval oracle ξ (cleanupPlan cfg c y B)
        (call + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds)
      let gm := sampledEval oracle ξ (meanPlan cfg.batch zn.1)
        (call + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
          ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)))
      outerAdvance cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop s zn.1 (gm + zn.2) := by
  simp only [roundPlan, sampledEval_cast, sampledEval_bind, sampledEval_map]

lemma innerPlan_follow (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (c : E) (B : E →L[ℝ] E) (J call : ℕ) (y : ℕ → E)
    (hrec : ∀ t < J, y (t + 1) = proxPoint cfg.C cfg.x0 c (y t) B cfg.L cfg.δ
      (sampledEval oracle ξ (modelGradientPlan cfg c (y t) B)
        (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * t))) :
    sampledEval oracle ξ (innerPlan cfg c B J (y 0)) call = y J := by
  induction J generalizing call y with
  | zero => rfl
  | succ J ih =>
    simp only [innerPlan, sampledEval_bind]
    have hzero := hrec 0 (Nat.zero_lt_succ J)
    simp only [Nat.mul_zero, Nat.add_zero] at hzero
    rw [← hzero]
    apply ih (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)) (fun t => y (t + 1))
    intro t ht
    have h := hrec (t + 1) (by omega)
    have he : call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) +
        (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * t =
        call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * (t + 1) := by ring
    simpa only [he] using h

lemma innerPlan_eval_iterate (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (c : E) (B : E →L[ℝ] E) (J call : ℕ) :
    sampledEval oracle ξ (innerPlan cfg c B J cfg.x0) call =
      innerIterate cfg.C cfg.x0 c B cfg.L cfg.δ
        (fun t y => sampledEval oracle ξ (modelGradientPlan cfg c y B)
          (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * t)) J := by
  exact innerPlan_follow oracle ξ cfg c B J call
    (innerIterate cfg.C cfg.x0 c B cfg.L cfg.δ
      (fun t y => sampledEval oracle ξ (modelGradientPlan cfg c y B)
        (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * t))) (fun _ _ => rfl)

lemma roundsPlan_follow [CompleteSpace E] (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (cfg : Config E) (T call : ℕ) (S : ℕ → OuterState E)
    (hrec : ∀ t < T, S (t + 1) = sampledEval oracle ξ (roundPlan cfg (S t))
      (call + (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) * t)) :
    sampledEval oracle ξ (roundsPlan cfg T (S 0)) call = S T := by
  induction T generalizing call S with
  | zero => rfl
  | succ T ih =>
    simp only [roundsPlan, sampledEval_bind]
    have hzero := hrec 0 (Nat.zero_lt_succ T)
    simp only [Nat.mul_zero, Nat.add_zero] at hzero
    rw [← hzero]
    apply ih (call + (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch))
      (fun t => S (t + 1))
    intro t ht
    have h := hrec (t + 1) (by omega)
    have he : call + (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) +
        (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) * t =
        call + (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) * (t + 1) := by ring
    simpa only [he] using h

lemma output_eq_sampledPlan [CompleteSpace E] [MeasurableSpace Ω]
    (cfg : Config E) (T K : ℕ) (oracle : E → Ω → Reply E)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω)
    (hK : (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) * T ≤ K) :
    LongTails.Algorithms.SymmetricThirdOrder.output cfg T K { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ =
      (sampledEval oracle ξ (roundsPlan cfg T (outerInitial cfg.x0 cfg.gridTop)) 0).point := by
  unfold LongTails.Algorithms.SymmetricThirdOrder.output
  erw [StochasticGradient.execute_advance]
  change QueryPlan.output cfg.x0 (StochasticGradient.advance
    (fun call s => QueryPlan.update s (oracle (QueryPlan.query cfg.x0 s) (ξ call))) K 0
    ⟨_, QueryPlan.map (fun s => s.point) (roundsPlan cfg T (outerInitial cfg.x0 cfg.gridTop))⟩) = _
  rw [advance_sampledPlan_of_le oracle ξ cfg.x0 _ hK]
  exact sampledEval_map oracle ξ _ _ 0

lemma sampledEval_congr_block {Q V U W : Type*} (oracle : Q → W → V)
    (ξ η : ℕ → W) {k : ℕ} (plan : QueryPlan Q V U k) (call : ℕ)
    (hξ : ∀ j, call ≤ j → j < call + k → ξ j = η j) :
    sampledEval oracle ξ plan call = sampledEval oracle η plan call := by
  induction plan generalizing call with
  | done value => rfl
  | @ask k q next ih =>
    simp only [sampledEval]
    rw [hξ call le_rfl (by omega)]
    apply ih
    intro j hj hj'
    exact hξ j (by omega) (by omega)

lemma sampledEval_adaptive_prefix {Q V U W : Type*} (oracle : Q → W → V)
    {k call : ℕ} (plan : (ℕ → W) → QueryPlan Q V U k)
    (hplan : ∀ ξ η, (∀ j < call, ξ j = η j) → plan ξ = plan η)
    (ξ η : ℕ → W) (hξ : ∀ j < call + k, ξ j = η j) :
    sampledEval oracle ξ (plan ξ) call = sampledEval oracle η (plan η) call := by
  rw [hplan ξ η (fun j hj => hξ j (by omega))]
  exact sampledEval_congr_block oracle ξ η (plan η) call (fun j _ hj => hξ j hj)

lemma roundsPlan_prefix [CompleteSpace E] (oracle : E → Ω → Reply E)
    (cfg : Config E) (T : ℕ) (s : OuterState E) (ξ η : ℕ → Ω)
    (hξ : ∀ j < (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) * T,
      ξ j = η j) :
    sampledEval oracle ξ (roundsPlan cfg T s) 0 = sampledEval oracle η (roundsPlan cfg T s) 0 := by
  exact sampledEval_congr_block oracle ξ η _ 0 (fun j _ hj => hξ j (by simpa using hj))

end LongTails.Proofs.SymmetricThirdOrderExecution
