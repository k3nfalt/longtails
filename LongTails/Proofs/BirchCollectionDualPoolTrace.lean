import LongTails.Algorithms.BirchCollectionDualPool
import LongTails.Proofs.BirchCollectionPoolCertificate

namespace LongTails.Proofs.BirchCollectionDualPoolTrace

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools (Pool Worker issue complete publish)
open LongTails.Algorithms.BirchCollectionDualPool
open LongTails.Algorithms.BirchCollectionDualProcess (Prefix)
open LongTails.Proofs.BirchCollectionPoolTrace (data_issue data_complete data_merge)
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionAsyncLocalTrace (prefixSet)
open LongTails.Proofs.BirchCollectionAsyncLocalPublish (prefixSet_mono)

local notation "PoolData" => LongTails.Proofs.BirchCollectionPoolTrace.Data

structure AtPrefix (s : TraceState) (w : Worker) (p : Prefix) : Prop where
  bound : p.point < s.nextState
  count : p.count ≤ w.privateLabels.length
  history : (s.states p.point).history = (s.states w.base).history ∪ prefixSet w.privateLabels p.count

structure Data {m : ℕ} (s : Round m) (B Q : ℕ) (move : ℝ) : Prop where
  pool : PoolData s.pool B Q Q (Q - 1) move
  base : ∀ w, (s.pool.worker w).base = s.pool.main
  frontier : ∀ w, (s.pool.worker w).frontier = s.pool.accepted.length
  acknowledged : ∀ w, AtPrefix s.pool.trace (s.pool.worker w) (s.record w).acknowledged
  message : ∀ w p, (s.record w).message = some p →
    AtPrefix s.pool.trace (s.pool.worker w) p ∧ (s.record w).acknowledged.count < p.count

lemma AtPrefix.extend {s t : TraceState} {w v : Worker} {p : Prefix}
    (h : AtPrefix s w p) (he : Extends s t) (hb : v.base = w.base) (hbase : w.base < s.nextState)
    (hl : ∃ suffix, v.privateLabels = w.privateLabels ++ suffix) : AtPrefix t v p := by
  obtain ⟨suffix, hl⟩ := hl
  refine ⟨h.bound.trans_le he.stateCount, ?_, ?_⟩
  · rw [hl, List.length_append]
    exact h.count.trans (Nat.le_add_right _ _)
  · rw [he.oldState _ h.bound, hb, he.oldState _ hbase, hl, h.history]
    simp [prefixSet, List.take_append_of_le_length h.count]

lemma initial_data {m B Q : ℕ} {move : ℝ} (s : Pool m)
    (hs : PoolData s B Q Q (Q - 1) move)
    (hb : ∀ w, (s.worker w).base = s.main)
    (hf : ∀ w, (s.worker w).frontier = s.accepted.length) :
    Data (initial s) B Q move := by
  refine ⟨hs, hb, hf, ?_, ?_⟩
  · intro w
    refine ⟨hs.main.headBound, Nat.zero_le _, ?_⟩
    change (s.trace.states s.main).history =
      (s.trace.states (s.worker w).base).history ∪ prefixSet (s.worker w).privateLabels 0
    simp [hb w, prefixSet]
  · simp [initial]

lemma preserve_records {m B Q : ℕ} {move : ℝ} (s : Round m) (p : Pool m)
    (hs : Data s B Q move) (hp : PoolData p B Q Q (Q - 1) move)
    (he : Extends s.pool.trace p.trace) (hm : p.main = s.pool.main) (ha : p.accepted = s.pool.accepted)
    (hb : ∀ w, (p.worker w).base = (s.pool.worker w).base)
    (hf : ∀ w, (p.worker w).frontier = (s.pool.worker w).frontier)
    (hl : ∀ w, ∃ suffix, (p.worker w).privateLabels = (s.pool.worker w).privateLabels ++ suffix) :
    Data {s with pool := p} B Q move := by
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  · intro w
    change (p.worker w).base = p.main
    rw [hb w, hm]
    exact hs.base w
  · intro w
    change (p.worker w).frontier = p.accepted.length
    rw [hf w, ha]
    exact hs.frontier w
  · intro w
    exact (hs.acknowledged w).extend he (hb w) (hs.pool.branch w).chain.baseBound (hl w)
  · intro w u hu
    obtain ⟨h, hcount⟩ := hs.message w u hu
    exact ⟨h.extend he (hb w) (hs.pool.branch w).chain.baseBound (hl w), hcount⟩

lemma query_data {m B Q : ℕ} {move : ℝ} (s : Round m) (w : Fin m)
    (hs : Data s B Q move) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    Data (advance B move s (.query w)) B Q move := by
  let p := issue B move s.pool w
  have hw (v : Fin m) : (p.worker v).base = (s.pool.worker v).base ∧
      (p.worker v).frontier = (s.pool.worker v).frontier ∧
      (p.worker v).privateLabels = (s.pool.worker v).privateLabels := by
    by_cases h : v = w
    · subst v
      simp [p, issue, Pool.put, Pool.append]
    · simp [p, issue, Pool.put, Pool.append, h]
  have he : Extends s.pool.trace p.trace := extends_fold _ _
  exact preserve_records s p hs (data_issue s.pool w hs.pool hB hm0 hm1) he rfl rfl
    (fun v => (hw v).1) (fun v => (hw v).2.1) (fun v => ⟨[], by simp [(hw v).2.2]⟩)

lemma compute_data {m B Q : ℕ} {move : ℝ} (s : Round m) (w : Fin m)
    (hs : Data s B Q move) (hw : (s.pool.worker w).pending.isSome) :
    Data (advance B move s (.compute w)) B Q move := by
  cases ht : (s.pool.worker w).pending with
  | none => simp [ht] at hw
  | some j =>
    let p := complete B s.pool w
    let es := LongTails.Algorithms.BirchCollectionLocal.localComplete B j
    have hout : p = (s.pool.append es).put w {(s.pool.worker w) with
        head := s.pool.trace.nextState
        privateLabels := (s.pool.worker w).privateLabels ++ [s.pool.trace.nextDirection]
        pending := none} := by simp [p, complete, ht, es]
    have he : Extends s.pool.trace p.trace := by rw [hout]; exact extends_fold _ es
    have ha : p.accepted = s.pool.accepted := by rw [hout]; rfl
    have hm : p.main = s.pool.main := by rw [hout]; rfl
    refine preserve_records s p hs (data_complete s.pool w hs.pool hw) he hm ha ?_ ?_ ?_
    · intro v
      by_cases hv : v = w
      · subst v
        simp [hout, Pool.put, Pool.append]
      · simp [hout, Pool.put, Pool.append, hv]
    · intro v
      by_cases hv : v = w
      · subst v
        simp [hout, Pool.put, Pool.append]
      · simp [hout, Pool.put, Pool.append, hv]
    · intro v
      by_cases hv : v = w
      · subst v
        exact ⟨[s.pool.trace.nextDirection], by simp [hout, Pool.put, Pool.append]⟩
      · exact ⟨[], by simp [hout, Pool.put, Pool.append, hv]⟩

lemma send_data {m B Q : ℕ} {move : ℝ} (s : Round m) (w : Fin m)
    (hs : Data s B Q move) (hw : Enabled Q s (.send w)) :
    Data (advance B move s (.send w)) B Q move := by
  let out := advance B move s (.send w)
  let msg : Prefix := ⟨(s.pool.worker w).head, (s.pool.worker w).privateLabels.length⟩
  have hrec (v : Fin m) : out.record v =
      Function.update s.record w {s.record w with message := some msg} v := rfl
  have hchain := (hs.pool.branch w).chain
  change Data out B Q move
  refine ⟨hs.pool, hs.base, hs.frontier, ?_, ?_⟩
  · intro v
    rw [hrec]
    by_cases h : v = w
    · subst v
      rw [Function.update_self]
      exact hs.acknowledged w
    · rw [Function.update_of_ne h]
      exact hs.acknowledged v
  · intro v p hp
    rw [hrec] at hp ⊢
    by_cases h : v = w
    · subst v
      rw [Function.update_self, Option.some.injEq] at hp
      subst p
      rw [Function.update_self]
      refine ⟨⟨hchain.headBound, le_rfl, ?_⟩, hw.2.2⟩
      change (s.pool.trace.states (s.pool.worker w).head).history =
        (s.pool.trace.states (s.pool.worker w).base).history ∪
          prefixSet (s.pool.worker w).privateLabels (s.pool.worker w).privateLabels.length
      simpa only [prefixSet, List.take_length] using hchain.history
    · rw [Function.update_of_ne h] at hp ⊢
      exact hs.message v p hp

lemma acknowledge_data {m B Q : ℕ} {move : ℝ} (s : Round m) (w : Fin m)
    (hs : Data s B Q move) (hw : Enabled Q s (.acknowledge w)) :
    Data (advance B move s (.acknowledge w)) B Q move := by
  cases h : (s.record w).message with
  | none =>
    have hbad : (s.record w).message.isSome := hw.2
    simp [h] at hbad
  | some sent =>
    let old := (s.record w).acknowledged
    let e := Event.merge 0 old.point sent.point old.point
    let p := s.pool.append [e]
    let out := advance B move s (.acknowledge w)
    let new : Record := {acknowledged := ⟨s.pool.trace.nextState, sent.count⟩}
    have hout : out = ⟨p, Function.update s.record w new⟩ := by
      simp [out, advance, h, p, e, old, new]
    have hold := hs.acknowledged w
    obtain ⟨hsent, horder⟩ := hs.message w sent h
    have hsub : (s.pool.trace.states old.point).history ⊆ (s.pool.trace.states sent.point).history := by
      rw [hold.history, hsent.history]
      exact union_subset_union le_rfl (prefixSet_mono _ horder.le)
    have he : e.Valid (m + 1) s.pool.trace := by
      refine ⟨Nat.zero_lt_succ _, hold.bound, hsent.bound, hold.bound, ?_⟩
      exact (inter_eq_left.mpr hsub).symm
    have hp : PoolData p B Q Q (Q - 1) move := data_merge s.pool 0 old.point sent.point old.point hs.pool he
    have hx : Extends s.pool.trace p.trace := extends_step _ e
    have hshape (v : Fin m) : (p.worker v) = s.pool.worker v := rfl
    have hBase : p.main = s.pool.main := rfl
    have hAccept : p.accepted = s.pool.accepted := rfl
    have hstable := preserve_records s p hs hp hx hBase hAccept (fun v => congrArg Worker.base (hshape v))
      (fun v => congrArg Worker.frontier (hshape v)) (fun v => ⟨[], by simp [hshape]⟩)
    have hnew : AtPrefix p.trace (p.worker w) new.acknowledged := by
      refine ⟨Nat.lt_succ_self _, hsent.count, ?_⟩
      change ((step s.pool.trace e).states s.pool.trace.nextState).history =
        (p.trace.states (p.worker w).base).history ∪ prefixSet (p.worker w).privateLabels sent.count
      rw [(merge_data s.pool.trace 0 old.point sent.point old.point).newState]
      change (s.pool.trace.states old.point).history ∪ (s.pool.trace.states sent.point).history = _
      rw [union_eq_right.mpr hsub, hshape, hx.oldState _ (hs.pool.branch w).chain.baseBound]
      exact hsent.history
    change Data out B Q move
    rw [hout]
    refine ⟨hp, hstable.base, hstable.frontier, ?_, ?_⟩
    · intro v
      change AtPrefix p.trace (p.worker v) (Function.update s.record w new v).acknowledged
      by_cases hv : v = w
      · subst v
        rw [Function.update_self]
        exact hnew
      · rw [Function.update_of_ne hv]
        exact hstable.acknowledged v
    · intro v packet hpacket
      change (Function.update s.record w new v).message = some packet at hpacket
      change AtPrefix p.trace (p.worker v) packet ∧ (Function.update s.record w new v).acknowledged.count < packet.count
      by_cases hv : v = w
      · subst v
        rw [Function.update_self] at hpacket
        simp [new] at hpacket
      · rw [Function.update_of_ne hv] at hpacket ⊢
        exact hstable.message v packet hpacket

lemma data_fold {m B Q : ℕ} {move : ℝ} (s : Round m) (events : List (Action m))
    (hs : Data s B Q move) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom Q B move s events) :
    Data (events.foldl (advance B move) s) B Q move := by
  induction events generalizing s with
  | nil => exact hs
  | cons e es ih =>
    apply ih _ _ he.2
    cases e with
    | query w => exact query_data s w hs hB hm0 hm1
    | compute w => exact compute_data s w hs he.1.2
    | send w => exact send_data s w hs he.1
    | acknowledge w => exact acknowledge_data s w hs he.1

end LongTails.Proofs.BirchCollectionDualPoolTrace
