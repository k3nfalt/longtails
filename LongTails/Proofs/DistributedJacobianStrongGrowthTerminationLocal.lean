import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationRank

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminationLocal

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthTerminationRank

noncomputable def workerRank (p : Params) (s : State p) : ℕ :=
  8 * workRemaining p s + 8 * s.work.isSome.toNat + 8 * s.queue.length +
    8 * ((p.n : ℕ) - s.collector.seen.card) + 8 * (!s.sent).toNat + 4 * (!s.busy).toNat

lemma workerRank_queue_tail (p : Params) (s : State p) (packet : Fin p.n × List Bool)
    (rest : List (Fin p.n × List Bool)) (hq : s.queue = packet :: rest) :
    workerRank p { s with queue := rest } + 8 = workerRank p s := by
  simp only [workerRank, workRemaining, hq, List.length_cons]
  omega

lemma workerRank_busy (p : Params) (s : State p) (hb : s.busy = false) :
    workerRank p { s with busy := true } + 4 = workerRank p s := by
  simp [workerRank, workRemaining, hb]

lemma workerRank_sent (p : Params) (s : State p) (hs : s.sent = false) :
    workerRank p { s with sent := true } + 8 = workerRank p s := by
  simp only [workerRank, workRemaining, hs, Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false]
  omega

lemma workerRank_computed (p : Params) (v : Fin p.n) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p) (x value : Point p)
    (hw : s.work = some work) (hb : s.busy = true)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some x) :
    workerRank p (update p v s (.computed value)) + 4 = workerRank p s := by
  have hr := DistributedJacobianStrongGrowthWorker.reply_decreases p work value x hq
  simp only [update, hw, hb, ↓reduceIte, workerRank, workRemaining,
    Option.isSome_some, Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false]
  omega

lemma workerRank_finishLocal (p : Params) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (hw : s.work = some work) (hb : s.busy = false)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = none)
    (hn : s.phase ≠ .baseline) (hnot : s.phase ≠ .warming) :
    workerRank p (finishLocal p s (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)) + 8 =
      workerRank p s := by
  have hr := (DistributedJacobianStrongGrowthWorker.query_none_iff p work).mp hq
  cases hs : s.phase <;>
    simp_all [finishLocal, workerRank, workRemaining]
  all_goals omega

lemma workerRank_accept (p : Params) (s : State p) (allowed : Finset (Fin p.n))
    (child : Fin p.n) (values : Fin p.d → ℕ) (hc : child ∈ allowed) (hf : child ∉ s.collector.seen) :
    workerRank p { s with collector := accept allowed s.collector child values } + 8 = workerRank p s := by
  classical
  have hcard : s.collector.seen.card < (p.n : ℕ) := by
    have hi := Finset.card_le_univ (insert child s.collector.seen)
    simp only [Finset.card_insert_of_notMem hf, Fintype.card_fin] at hi
    omega
  simp only [workerRank, workRemaining, accept, ite_eq_left (show child ∈ allowed ∧ child ∉ s.collector.seen from ⟨hc, hf⟩),
    Finset.card_insert_of_notMem hf]
  omega

lemma stagesRemaining_computed (p : Params) (v : Fin p.n) (s : State p) (value : Point p) :
    stagesRemaining p (update p v s (.computed value)).phase = stagesRemaining p s.phase := by
  cases hw : s.work <;> cases hb : s.busy <;> simp [update, hw, hb]

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminationLocal
