import LongTails.Proofs.SlidingLowerHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.SlidingLowerExecution

open LongTails.Proofs.SlidingLowerChain (Point)

open OracleTemplate SlidingLowerSim SlidingLowerRun SlidingLowerHiding

variable {d k : ℕ}

lemma trueSeq_stuck {S : Type*} (H : Run S d)
    (tr : (Fin (k + 1) ↪ Fin d) → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) (t : ℕ)
    (h : (trueSeq H tr π β budget t).2 (H.query (trueSeq H tr π β budget t).1).1 = 0) :
    ∀ m, trueSeq H tr π β budget (t + m) = trueSeq H tr π β budget t := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [← Nat.add_assoc]
      simp only [trueSeq]
      rw [ih]
      unfold trueStep
      rw [ite_eq_left h]

lemma brun_trueSeq (A : Algorithm (Point d) (Point d) (Point d) 2) (seed : A.Seed)
    (tr : (Fin (k + 1) ↪ Fin d) → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d) (β : ℕ → Bool) (budget : Fin 2 → ℕ) :
    ∀ f t, brun A (fun t q => tr π (β t) q) f (trueSeq (toRun A seed) tr π β budget t).2
      (trueSeq (toRun A seed) tr π β budget t).1 t =
        (trueSeq (toRun A seed) tr π β budget (t + f)).1 := by
  intro f
  induction f with
  | zero => intro t; rfl
  | succ f ih =>
      intro t
      simp only [brun]
      by_cases hz : (trueSeq (toRun A seed) tr π β budget t).2
          (A.query (trueSeq (toRun A seed) tr π β budget t).1).1 = 0
      · rw [ite_eq_left hz, trueSeq_stuck (toRun A seed) tr π β budget t hz]
      · rw [ite_eq_right hz]
        have hs : trueSeq (toRun A seed) tr π β budget (t + 1) =
            (A.update (trueSeq (toRun A seed) tr π β budget t).1
              (tr π (β t) (A.query (trueSeq (toRun A seed) tr π β budget t).1)),
            Function.update (trueSeq (toRun A seed) tr π β budget t).2
              (A.query (trueSeq (toRun A seed) tr π β budget t).1).1
              ((trueSeq (toRun A seed) tr π β budget t).2
                (A.query (trueSeq (toRun A seed) tr π β budget t).1).1 - 1)) := by
          simp only [trueSeq, trueStep, toRun]
          split_ifs with h
          · exact absurd h hz
          · rfl
        have := ih (t + 1)
        rw [hs] at this
        rw [this, show t + 1 + f = t + (f + 1) by omega]

lemma execute_trueSeq (O : Oracle (Point d) (Point d) 2)
    (A : Algorithm (Point d) (Point d) (Point d) 2) (budget : Fin 2 → ℕ) (seed : A.Seed)
    (ξ : (t : ℕ) → O.Seed t) (β : ℕ → Bool)
    (tr : (Fin (k + 1) ↪ Fin d) → Bool → Fin 2 × Point d → Point d)
    (π : Fin (k + 1) ↪ Fin d)
    (h : ∀ history q, O.answer history q (ξ history.length) = tr π (β history.length) q) :
    execute O A budget seed ξ =
      A.output (trueSeq (toRun A seed) tr π β budget (∑ i, budget i)).1 := by
  rw [execute_eq_brun O A budget seed ξ (fun t q => tr π (β t) q) h]
  have h0 := brun_trueSeq A seed tr π β budget (∑ i, budget i) 0
  rw [zero_add] at h0
  exact congrArg A.output h0

end LongTails.Proofs.SlidingLowerExecution
