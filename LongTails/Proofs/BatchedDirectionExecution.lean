import LongTails.Algorithms.BatchedDirection
import LongTails.Proofs.SgdExecution

namespace LongTails.Proofs.BatchedDirectionExecution

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.BatchedDirection
open LongTails.Setups.BatchedSpectralSmooth

noncomputable def sampledIterate {m n : ℕ} {Ω : Type*} (direction : Space m n → Space m n)
    (η : ℝ) (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) :
    ℕ → Space m n
  | 0 => x0
  | t + 1 => sampledIterate direction η B x0 g ξ t - η • direction ((1 / (B : ℝ)) •
      ∑ j ∈ Finset.range B, g (sampledIterate direction η B x0 g ξ t) (ξ (B * t + j)))

noncomputable def savedAt {m n : ℕ} (direction : Space m n → Space m n) (η : ℝ) (B : ℕ)
    (x0 : Space m n) (reply : ℕ → Space m n) (k t : ℕ) : Space m n :=
  if k ≤ t then batchedIterate direction η B x0 reply k else x0

lemma method_state {m n : ℕ} (direction : Space m n → Space m n) (η : ℝ) {B : ℕ} (hB : 0 < B)
    (T : ℕ) (x0 : Space m n) (k : Fin (T + 1)) (reply : ℕ → Space m n) (t : ℕ) :
    ∀ j < B, LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
        (method direction η B T x0) k reply (B * t + j) =
      (k, ⟨t, j, batchedIterate direction η B x0 reply t,
        ∑ i ∈ Finset.range j, reply (B * t + i), savedAt direction η B x0 reply k.val t⟩) := by
  induction t with
  | zero =>
      intro j hj
      induction j with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, Finset.range_zero, Finset.sum_empty]
          change (k, (⟨0, 0, x0, 0, x0⟩ : Progress m n)) = _
          congr 2
          unfold savedAt
          split_ifs with h
          · rw [Nat.le_zero.mp h]
            rfl
          · rfl
      | succ j ih =>
          have hprev := ih (by omega)
          rw [show B * 0 + (j + 1) = (B * 0 + j) + 1 by omega]
          change (method direction η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (method direction η B T x0) k reply (B * 0 + j)) (reply (B * 0 + j)) = _
          rw [hprev]
          have hs : j + 1 < B := hj
          simp only [method, advanceProgress, hs, ↓reduceIte, Finset.sum_range_succ]
  | succ t ih =>
      intro j hj
      induction j with
      | zero =>
          have hprev := ih (B - 1) (by omega)
          rw [show B * (t + 1) + 0 = (B * t + (B - 1)) + 1 by
            rw [Nat.mul_succ]; omega]
          change (method direction η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (method direction η B T x0) k reply (B * t + (B - 1))) (reply (B * t + (B - 1))) = _
          rw [hprev]
          have hs : ¬ (B - 1 + 1 < B) := by omega
          have hsum : (∑ i ∈ Finset.range (B - 1), reply (B * t + i)) + reply (B * t + (B - 1)) =
              ∑ i ∈ Finset.range B, reply (B * t + i) := by
            have hB1 : B - 1 + 1 = B := Nat.sub_add_cancel hB
            rw [← Finset.sum_range_succ (fun i => reply (B * t + i)) (B - 1), hB1]
          simp only [method, advanceProgress, hs, ↓reduceIte, hsum, Finset.range_zero,
            Finset.sum_empty]
          congr 2
          unfold savedAt
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
          change (method direction η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (method direction η B T x0) k reply (B * (t + 1) + j))
              (reply (B * (t + 1) + j)) = _
          rw [hprev]
          have hs : j + 1 < B := hj
          simp only [method, advanceProgress, hs, ↓reduceIte, Finset.sum_range_succ]

lemma method_follows {m n : ℕ} (direction : Space m n → Space m n) (η : ℝ) {B : ℕ} (hB : 0 < B)
    (T : ℕ) (x0 : Space m n) :
    FollowsBatched direction η B T x0 (method direction η B T x0) := by
  refine ⟨id, measurable_id, ?_, ?_⟩
  · exact Measure.map_id
  · intro seed reply
    refine ⟨?_, ?_⟩
    · intro t j _ hj
      rw [method_state direction η hB T x0 seed reply t j hj]
      rfl
    · intro extra
      have hdiv : B * (T + 1) + extra = B * (T + 1 + extra / B) + extra % B := by
        rw [Nat.mul_add B (T + 1), add_assoc, Nat.div_add_mod]
      have h := method_state direction η hB T x0 seed reply (T + 1 + extra / B) (extra % B)
        (Nat.mod_lt _ hB)
      rw [hdiv, h]
      have hle : (seed : Fin (T + 1)).val ≤ T + 1 + extra / B :=
        le_trans (Nat.le_succ_of_le (Nat.lt_succ_iff.mp (seed : Fin (T + 1)).isLt))
          (Nat.le_add_right _ _)
      show savedAt direction η B x0 reply _ (T + 1 + extra / B) = _
      unfold savedAt
      split_ifs
      rfl

noncomputable def stateSeq {Q R U : Type} {Ω : Type*} (A : Algorithm Q R U) (seed : A.Seed)
    (g : Q → Ω → R) (ξ : ℕ → Ω) : ℕ → A.State
  | 0 => A.initial seed
  | k + 1 => A.update (stateSeq A seed g ξ k) (g (A.query (stateSeq A seed g ξ k)).2 (ξ k))

lemma advance_stateSeq {Q R U : Type} {Ω : Type*} (A : Algorithm Q R U) (seed : A.Seed)
    (g : Q → Ω → R) (ξ : ℕ → Ω) (K c : ℕ) :
    StochasticGradient.advance (fun k state => A.update state (g (A.query state).2 (ξ k)))
      K c (stateSeq A seed g ξ c) = stateSeq A seed g ξ (c + K) := by
  induction K generalizing c with
  | zero => rfl
  | succ K ih =>
      change StochasticGradient.advance _ K (c + 1) (stateSeq A seed g ξ (c + 1)) = _
      rw [ih]
      congr 1
      omega

lemma replyState_stateSeq {Q R U : Type} {Ω : Type*} (A : Algorithm Q R U) (seed : A.Seed)
    (g : Q → Ω → R) (ξ : ℕ → Ω) (k : ℕ) :
    LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed
      (fun i => g (A.query (stateSeq A seed g ξ i)).2 (ξ i)) k = stateSeq A seed g ξ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change A.update _ _ = A.update _ _
      rw [ih]

lemma execute_eq_sampledIterate {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (law : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    {direction : Space m n → Space m n} {η : ℝ} {B T : ℕ} {x0 : Space m n}
    {A : Algorithm (Space m n) (Space m n) (Space m n)} (draw : A.Seed → Fin (T + 1))
    (hA : ∀ seed reply,
      let state := LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = batchedIterate direction η B x0 reply t) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        batchedIterate direction η B x0 reply (draw seed))
    (seed : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
        A (fun _ => B * (T + 1)) seed ξ =
      sampledIterate direction η B x0 g ξ (draw seed) := by
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
  have hiter : ∀ t ≤ T + 1, batchedIterate direction η B x0 reply t =
      sampledIterate direction η B x0 g ξ t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
        intro ht
        have ih' := ih (by omega)
        simp only [batchedIterate, sampledIterate, ih', batchMean]
        congr 3
        refine congrArg _ (Finset.sum_congr rfl ?_)
        intro j hj
        change g (A.query (stateSeq A seed g ξ (B * t + j))).2 (ξ (B * t + j)) = _
        rw [hq t j (by omega) (Finset.mem_range.mp hj), ih']
  exact hiter _ (by omega)

end LongTails.Proofs.BatchedDirectionExecution
