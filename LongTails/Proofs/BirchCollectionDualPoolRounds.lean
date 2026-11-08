import LongTails.Proofs.BirchCollectionDualPoolTrace
import LongTails.Proofs.BirchCollectionCycleTrace

namespace LongTails.Proofs.BirchCollectionDualPoolRounds

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools (Pool Worker publish selectedLabels age)
open LongTails.Algorithms.BirchCollectionDualPool
open LongTails.Algorithms.BirchCollectionDualProcess (Prefix)
open LongTails.Proofs.BirchCollectionDualPoolTrace
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionAsyncLocalTrace (prefixSet)
open LongTails.Proofs.BirchCollectionAsyncLocalPublish (prefixSet_all)
open LongTails.Proofs.BirchCollectionPoolMerge (discard_many)
open LongTails.Proofs.BirchCollectionPoolPublish (shape discard_many_shape data_publish)
open LongTails.Proofs.BirchCollectionPoolCounts (close_many_profile selected_count privateCount reset_workers)
open LongTails.Proofs.BirchCollectionCycleTrace (publish_cut)

local notation "PoolData" => LongTails.Proofs.BirchCollectionPoolTrace.Data
local notation "discardPacket" => LongTails.Algorithms.BirchCollectionWorkerPools.discard

lemma chain_prefix {s : TraceState} {w : Worker} {p : Prefix} {B : ℕ} {move : ℝ}
    (hc : Chain s w.base w.head w.privateLabels B move) (hp : AtPrefix s w p) :
    Chain s w.base p.point (w.privateLabels.take p.count) B move := by
  refine ⟨hc.baseBound, hp.bound, hc.nodup.sublist (List.take_sublist _ _),
    fun d hd => hc.bounded d (List.mem_of_mem_take hd), hp.history, ?_⟩
  intro n hn
  have hcount : n < p.count := by rwa [List.length_take_of_le hp.count] at hn
  have hlen : n < w.privateLabels.length := hcount.trans_le hp.count
  simp only [List.getElem_take, List.take_take, Nat.min_eq_left hcount.le]
  exact hc.direction n hlen

lemma discard_cuts {m : ℕ} (B : ℕ) (s : Pool m) (ws : List (Fin m)) :
    (ws.foldl (discardPacket B) s).cuts = s.cuts := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    refine (ih (discardPacket B s w)).trans ?_
    cases h : (s.worker w).pending <;>
      simp [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h,
        LongTails.Algorithms.BirchCollectionWorkerPools.Pool.put,
        LongTails.Algorithms.BirchCollectionWorkerPools.Pool.append]

structure AfterRound {m : ℕ} (s : Pool m) (K B Q : ℕ) (move : ℝ) : Prop where
  pool : PoolData s B Q Q (Q - 1) move
  base : ∀ w, (s.worker w).base = s.main
  frontier : ∀ w, (s.worker w).frontier = s.accepted.length
  cuts : s.cuts.length = K + 1

lemma finish_data {m B Q : ℕ} {move : ℝ} (s : Round m) (hs : Data s B Q move)
    (hQ : 0 < Q) (ha : acknowledged s = Q) :
    let out := finishRound B s
    PoolData out B Q Q (Q - 1) move ∧
      (∀ w, (out.worker w).base = out.main) ∧
      (∀ w, (out.worker w).frontier = out.accepted.length) ∧
      out.cuts.length = s.pool.cuts.length + 1 := by
  let ws := List.finRange m
  let closed := ws.foldl (discardPacket B) s.pool
  let clipped := clip s closed
  let out := publish B clipped ws
  obtain ⟨hc, he⟩ := discard_many s.pool ws hs.pool
  change PoolData closed B Q Q (Q - 1) move at hc
  have hsame (w : Fin m) := discard_many_shape B s.pool ws w
  have hbase (w : Fin m) : (closed.worker w).base = (s.pool.worker w).base := by
    simpa only [shape] using congrArg Worker.base (hsame w)
  have hlabels (w : Fin m) : (closed.worker w).privateLabels = (s.pool.worker w).privateLabels := by
    simpa only [shape] using congrArg Worker.privateLabels (hsame w)
  have hfront (w : Fin m) : (closed.worker w).frontier = (s.pool.worker w).frontier := by
    simpa only [shape] using congrArg Worker.frontier (hsame w)
  have hacc : closed.accepted = s.pool.accepted := (close_many_profile B s.pool ws).1
  have hcuts : clipped.cuts = s.pool.cuts := discard_cuts B s.pool ws
  have hcount (w : Fin m) : (s.record w).acknowledged.count ≤ (closed.worker w).privateLabels.length := by
    rw [hlabels]
    exact (hs.acknowledged w).count
  have hprefix (w : Fin m) : AtPrefix closed.trace (closed.worker w) (s.record w).acknowledged :=
    (hs.acknowledged w).extend he (hbase w) (hs.pool.branch w).chain.baseBound
      ⟨[], by simp [hlabels]⟩
  have hworker (w : Fin m) : (clipped.worker w).privateLabels =
      (closed.worker w).privateLabels.take (s.record w).acknowledged.count := rfl
  have hd : PoolData clipped B Q Q (Q - 1) move := by
    refine ⟨hc.represented, hc.legal, hc.retired, hc.main, ?_, ?_, ?_, ?_⟩
    · intro w
      have hh := hc.branch w
      refine ⟨hh.frontierBound, hh.baseHistory, chain_prefix hh.chain (hprefix w), ?_⟩
      apply disjoint_left.mpr
      intro d h₁ h₂
      exact disjoint_left.mp hh.separate ((prefixSet_all _ _) h₁) h₂
    · intro w v hne
      apply disjoint_left.mpr
      intro d h₁ h₂
      exact disjoint_left.mp (hc.disjoint w v hne) ((prefixSet_all _ _) h₁) ((prefixSet_all _ _) h₂)
    · simp [clipped, clip]
    · simp [clipped, clip]
  have hwork : (selectedLabels clipped ws).length = Q := by
    rw [selected_count clipped ws (List.nodup_finRange m)]
    have hfull : ws.toFinset = (univ : Finset (Fin m)) := by ext w; simp [ws]
    rw [hfull]
    have hsum : (∑ w : Fin m, privateCount clipped w) = acknowledged s := by
      apply sum_congr rfl
      intro w _
      rw [privateCount, hworker, List.length_take_of_le (hcount w)]
    rw [hsum, ha]
  have hage (w : Fin m) : age clipped w = 0 := by
    change closed.accepted.length - (closed.worker w).frontier = 0
    rw [hacc, hfront w, hs.frontier w, Nat.sub_self]
  have ho : PoolData out B Q Q (Q - 1) move :=
    data_publish clipped ws hd (List.nodup_finRange m)
      (fun _ => hwork.ge) hwork.le (fun w _ => by rw [hage w, hwork, zero_add])
  let before := LongTails.Algorithms.BirchCollectionWorkerPools.publishState B clipped ws
  let root : Worker := {base := before.main, head := before.main, frontier := before.accepted.length}
  have hp (w : Fin m) : out.worker w = root := by
    change ((ws.foldl (fun t w => t.put w root) before).worker w) = root
    rw [reset_workers, ite_eq_left (by simp [ws])]
  have hm : out.main = before.main := by
    have h (p : Pool m) (ys : List (Fin m)) : (ys.foldl (fun t w => t.put w root) p).main = p.main := by
      induction ys generalizing p with
      | nil => rfl
      | cons w ys ih => exact ih (p.put w root)
    exact h before ws
  have haccepted : out.accepted = before.accepted :=
    LongTails.Proofs.BirchCollectionPoolCounts.reset_accepted before ws root
  have hpub : out.cuts = clipped.cuts ++ [clipped.accepted.length + (selectedLabels clipped ws).length] :=
    publish_cut clipped ws (hwork.symm ▸ hQ)
  change PoolData out B Q Q (Q - 1) move ∧ _
  refine ⟨ho, ?_, ?_, ?_⟩
  · intro w
    change (out.worker w).base = out.main
    rw [hp w, hm]
  · intro w
    change (out.worker w).frontier = out.accepted.length
    rw [hp w, haccepted]
  · change out.cuts.length = _
    rw [hpub, hcuts, List.length_append, List.length_singleton]

lemma run_round {m K Q B : ℕ} {move : ℝ} (s : Pool m) (events : List (Action m))
    (hs : AfterRound s K B Q move) (hQ : 0 < Q) (hB : 0 < B)
    (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom Q B move (initial s) events)
    (ha : acknowledged (events.foldl (advance B move) (initial s)) = Q) :
    AfterRound (runRound B move s events) (K + 1) B Q move := by
  have h := data_fold (initial s) events (initial_data s hs.pool hs.base hs.frontier) hB hm0 hm1 he
  obtain ⟨hp, hb, hf, hcut⟩ := finish_data _ h hQ ha
  have hcuts (t : Round m) (es : List (Action m)) :
      ((es.foldl (advance B move) t).pool).cuts = t.pool.cuts := by
    induction es generalizing t with
    | nil => rfl
    | cons e es ih =>
      refine (ih (advance B move t e)).trans ?_
      cases e with
      | query w => rfl
      | compute w =>
        cases h : (t.pool.worker w).pending <;>
          simp [advance, LongTails.Algorithms.BirchCollectionWorkerPools.complete, h,
            LongTails.Algorithms.BirchCollectionWorkerPools.Pool.put,
            LongTails.Algorithms.BirchCollectionWorkerPools.Pool.append]
      | send w => rfl
      | acknowledge w => cases h : (t.record w).message <;> simp [advance, h,
          LongTails.Algorithms.BirchCollectionWorkerPools.Pool.append]
  exact ⟨hp, hb, hf, hcut.trans (congrArg (· + 1) ((congrArg List.length (hcuts (initial s) events)).trans hs.cuts))⟩

lemma run_rounds {m K Q B : ℕ} {move : ℝ} (s : Pool m) (events : List (List (Action m)))
    (hs : AfterRound s K B Q move) (hQ : 0 < Q) (hB : 0 < B)
    (hm0 : 0 ≤ move) (hm1 : move ≤ 1) (he : CompleteRounds Q B move s events) :
    AfterRound (events.foldl (runRound B move) s) (K + events.length) B Q move := by
  induction events generalizing s K with
  | nil => exact hs
  | cons e es ih =>
    obtain ⟨hv, ha, ht⟩ := he
    have h := ih _ (run_round s e hs hQ hB hm0 hm1 hv ha) ht
    simpa only [List.foldl_cons, List.length_cons, Nat.add_right_comm K 1 es.length, Nat.add_assoc] using h

end LongTails.Proofs.BirchCollectionDualPoolRounds
