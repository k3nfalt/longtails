import LongTails.Algorithms.MomentumDirection
import LongTails.Proofs.BatchedDirectionExecution

namespace LongTails.Proofs.MomentumDirectionExecution

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.MomentumDirection
open LongTails.Setups.MomentumSpectralSmooth
open LongTails.Proofs.BatchedDirectionExecution

noncomputable def sampledMomentum {m n : ℕ} {Ω : Type*} (direction : Space m n → Space m n)
    (β η : ℝ) (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) :
    ℕ → Space m n × Space m n
  | 0 => (x0, 0)
  | t + 1 =>
      let M := β • (sampledMomentum direction β η B x0 g ξ t).2 + (1 - β) • ((1 / (B : ℝ)) •
        ∑ j ∈ Finset.range B, g (sampledMomentum direction β η B x0 g ξ t).1 (ξ (B * t + j)))
      ((sampledMomentum direction β η B x0 g ξ t).1 - η • direction M, M)

noncomputable def savedMomentum {m n : ℕ} (direction : Space m n → Space m n) (β η : ℝ) (B : ℕ)
    (x0 : Space m n) (reply : ℕ → Space m n) (k t : ℕ) : Space m n :=
  if k ≤ t then (momentumIterate direction β η B x0 reply k).1 else x0

lemma momentum_state {m n : ℕ} (direction : Space m n → Space m n) (β η : ℝ) {B : ℕ}
    (hB : 0 < B) (T : ℕ) (x0 : Space m n) (k : Fin (T + 1)) (reply : ℕ → Space m n) (t : ℕ) :
    ∀ j < B, LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
        (momentumMethod direction β η B T x0) k reply (B * t + j) =
      (k, ⟨t, j, (momentumIterate direction β η B x0 reply t).1,
        (momentumIterate direction β η B x0 reply t).2,
        ∑ i ∈ Finset.range j, reply (B * t + i), savedMomentum direction β η B x0 reply k.val t⟩) := by
  induction t with
  | zero =>
      intro j hj
      induction j with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, Finset.range_zero, Finset.sum_empty]
          change (k, (⟨0, 0, x0, 0, 0, x0⟩ : MomentumProgress m n)) = _
          congr 2
          unfold savedMomentum
          split_ifs with h
          · rw [Nat.le_zero.mp h]
            rfl
          · rfl
      | succ j ih =>
          have hprev := ih (by omega)
          rw [show B * 0 + (j + 1) = (B * 0 + j) + 1 by omega]
          change (momentumMethod direction β η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (momentumMethod direction β η B T x0) k reply (B * 0 + j)) (reply (B * 0 + j)) = _
          rw [hprev]
          have hs : j + 1 < B := hj
          simp only [momentumMethod, advanceMomentum, hs, ↓reduceIte, Finset.sum_range_succ]
  | succ t ih =>
      intro j hj
      induction j with
      | zero =>
          have hprev := ih (B - 1) (by omega)
          rw [show B * (t + 1) + 0 = (B * t + (B - 1)) + 1 by
            rw [Nat.mul_succ]; omega]
          change (momentumMethod direction β η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (momentumMethod direction β η B T x0) k reply (B * t + (B - 1)))
              (reply (B * t + (B - 1))) = _
          rw [hprev]
          have hs : ¬ (B - 1 + 1 < B) := by omega
          have hsum : (∑ i ∈ Finset.range (B - 1), reply (B * t + i)) + reply (B * t + (B - 1)) =
              ∑ i ∈ Finset.range B, reply (B * t + i) := by
            have hB1 : B - 1 + 1 = B := Nat.sub_add_cancel hB
            rw [← Finset.sum_range_succ (fun i => reply (B * t + i)) (B - 1), hB1]
          simp only [momentumMethod, advanceMomentum, hs, ↓reduceIte, hsum, Finset.range_zero,
            Finset.sum_empty]
          congr 2
          unfold savedMomentum
          by_cases hk : k.val = t + 1
          · rw [ite_eq_left hk.symm, ite_eq_left (by omega), hk]
            rfl
          · rw [ite_eq_right (Ne.symm hk)]
            by_cases hkt : k.val ≤ t
            · rw [ite_eq_left hkt, ite_eq_left (by omega)]
            · rw [ite_eq_right hkt, ite_eq_right (by omega)]
      | succ j ih' =>
          have hprev := ih' (by omega)
          rw [show B * (t + 1) + (j + 1) = (B * (t + 1) + j) + 1 by omega]
          change (momentumMethod direction β η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (momentumMethod direction β η B T x0) k reply (B * (t + 1) + j))
              (reply (B * (t + 1) + j)) = _
          rw [hprev]
          have hs : j + 1 < B := hj
          simp only [momentumMethod, advanceMomentum, hs, ↓reduceIte, Finset.sum_range_succ]

lemma momentum_follows {m n : ℕ} (direction : Space m n → Space m n) (β η : ℝ) {B : ℕ}
    (hB : 0 < B) (T : ℕ) (x0 : Space m n) :
    FollowsMomentum direction β η B T x0 (momentumMethod direction β η B T x0) := by
  refine ⟨id, measurable_id, ?_, ?_⟩
  · exact Measure.map_id
  · intro seed reply
    refine ⟨?_, ?_⟩
    · intro t j _ hj
      rw [momentum_state direction β η hB T x0 seed reply t j hj]
      rfl
    · intro extra
      have hdiv : B * (T + 1) + extra = B * (T + 1 + extra / B) + extra % B := by
        rw [Nat.mul_add B (T + 1), add_assoc, Nat.div_add_mod]
      have h := momentum_state direction β η hB T x0 seed reply (T + 1 + extra / B) (extra % B)
        (Nat.mod_lt _ hB)
      rw [hdiv, h]
      have hle : (seed : Fin (T + 1)).val ≤ T + 1 + extra / B :=
        le_trans (Nat.le_succ_of_le (Nat.lt_succ_iff.mp (seed : Fin (T + 1)).isLt))
          (Nat.le_add_right _ _)
      show savedMomentum direction β η B x0 reply _ (T + 1 + extra / B) = _
      unfold savedMomentum
      split_ifs
      rfl

lemma execute_eq_sampledMomentum {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (law : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    {direction : Space m n → Space m n} {β η : ℝ} {B T : ℕ} {x0 : Space m n}
    {A : Algorithm (Space m n) (Space m n) (Space m n)} (draw : A.Seed → Fin (T + 1))
    (hA : ∀ seed reply,
      let state := LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = (momentumIterate direction β η B x0 reply t).1) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        (momentumIterate direction β η B x0 reply (draw seed)).1)
    (seed : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
        A (fun _ => B * (T + 1)) seed ξ =
      (sampledMomentum direction β η B x0 g ξ (draw seed)).1 := by
  rw [StochasticGradient.execute_advance]
  have hadv := advance_stateSeq A seed g ξ (B * (T + 1)) 0
  rw [Nat.zero_add] at hadv
  change A.output (StochasticGradient.advance _ _ 0 (stateSeq A seed g ξ 0)) = _
  rw [hadv]
  let reply := fun i => g (A.query (stateSeq A seed g ξ i)).2 (ξ i)
  have hrep : ∀ k, LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply k =
      stateSeq A seed g ξ k := replyState_stateSeq A seed g ξ
  obtain ⟨hq, hout⟩ := hA seed reply
  simp only [hrep] at hq hout
  have hout0 := hout 0
  rw [Nat.add_zero] at hout0
  rw [hout0]
  have hiter : ∀ t ≤ T + 1, momentumIterate direction β η B x0 reply t =
      sampledMomentum direction β η B x0 g ξ t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
        intro ht
        have ih' := ih (by omega)
        have hmean : LongTails.Setups.BatchedSpectralSmooth.batchMean B reply t =
            (1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
              g (sampledMomentum direction β η B x0 g ξ t).1 (ξ (B * t + j)) := by
          unfold LongTails.Setups.BatchedSpectralSmooth.batchMean
          refine congrArg _ (Finset.sum_congr rfl ?_)
          intro j hj
          change g (A.query (stateSeq A seed g ξ (B * t + j))).2 (ξ (B * t + j)) = _
          rw [hq t j (by omega) (Finset.mem_range.mp hj), ih']
        simp only [momentumIterate, sampledMomentum, ih', hmean]
  rw [hiter _ (by omega)]

end LongTails.Proofs.MomentumDirectionExecution
