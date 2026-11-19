import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationLocal

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminationQuery

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthTerminationRank
open DistributedJacobianStrongGrowthTerminationLocal

noncomputable def actionCost (p : Params) (action : Action (Point p) p.n) : ℕ := by
  classical
  exact if action = .advance 1 then 0 else 4

lemma query_progress (p : Params) (v : Fin p.n) (s : State p)
    (hbounds : PhaseBounds p s.phase) (hroute : RoutingShape p v s) :
    stagesRemaining p (query p v s).2.phase < stagesRemaining p s.phase ∨
      stagesRemaining p (query p v s).2.phase = stagesRemaining p s.phase ∧
        workerRank p (query p v s).2 + actionCost p (query p v s).1 ≤ workerRank p s := by
  classical
  cases hqueue : s.queue with
  | cons packet rest =>
      right
      refine ⟨by simp [query, hqueue], ?_⟩
      have he := workerRank_queue_tail p s packet rest hqueue
      simp only [query, hqueue, actionCost, reduceCtorEq, ↓reduceIte]
      omega
  | nil =>
      cases hw : s.work with
      | some work =>
          cases hb : s.busy with
          | true =>
              right
              simp [query, hqueue, hw, hb, actionCost]
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | some x =>
                  right
                  refine ⟨by simp [query, hqueue, hw, hb, hquery], ?_⟩
                  have he := workerRank_busy p s hb
                  simpa only [query, hqueue, hw, hb, Bool.false_eq_true, ↓reduceIte, hquery,
                    actionCost, reduceCtorEq] using le_of_eq he
              | none =>
                  by_cases hbase : s.phase = .baseline
                  · left
                    simp [query, hqueue, hw, hb, hquery, finishLocal, hbase, stagesRemaining]
                  · by_cases hwarm : s.phase = .warming
                    · left
                      have he := stagesRemaining_finishLocal_warming p s
                        (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) hwarm
                      simp only [query, hqueue, hw, hb, Bool.false_eq_true, ↓reduceIte, hquery]
                      omega
                    · right
                      constructor
                      · cases hs : s.phase <;> simp_all [query, finishLocal]
                      · have he := workerRank_finishLocal p s work hw hb hquery hbase hwarm
                        simp only [query, hqueue, hw, hb, Bool.false_eq_true, ↓reduceIte, hquery, actionCost]
                        simp only [Action.advance.injEq, ite_eq_right (show (0 : ClockReading) ≠ 1 by decide)]
                        omega
      | none =>
          by_cases hr : s.ready ∧ ¬ s.sent ∧ children p v ⊆ s.collector.seen
          · have ha := hroute.1.2.1 (Or.inl hr.1)
            by_cases hv : v = p.root
            · left
              have he := stagesRemaining_finishBroadcast p s
                (broadcastValues p s.phase (fun j => s.own j + s.collector.total j)) hbounds ha
              simp only [query, hqueue, hw, ite_eq_left hr, ite_eq_left hv]
              change stagesRemaining p (finishBroadcast p s _).phase < stagesRemaining p s.phase
              omega
            · right
              refine ⟨by simp only [query, hqueue, hw, ite_eq_left hr, ite_eq_right hv], ?_⟩
              have hsent : s.sent = false := by simpa using hr.2.1
              have he := workerRank_sent p s hsent
              simp only [hw, hqueue] at he
              simp only [query, hqueue, hw, ite_eq_left hr, ite_eq_right hv, actionCost,
                reduceCtorEq, ↓reduceIte]
              omega
          · right
            simp only [query, hqueue, hw, ite_eq_right hr]
            simp [actionCost]

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminationQuery
