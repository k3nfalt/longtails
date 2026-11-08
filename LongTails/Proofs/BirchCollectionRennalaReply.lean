import LongTails.Proofs.BirchCollectionRennalaTrace

namespace LongTails.Proofs.BirchCollectionRennalaReply

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionRennala
open LongTails.Proofs.BirchCollectionRennalaLedger
open LongTails.Proofs.BirchCollectionRennalaTrace
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchNonEuclideanRennalaScheduling (step_invariant)

local notation "Enabled" => LongTails.Algorithms.BirchNonEuclideanRennala.Event.Enabled
local notation "ostep" => LongTails.Algorithms.BirchNonEuclideanRennala.step

lemma main_same (s t : TraceState) (B r : ℕ) (hs : MainData s B r)
    (stateCount : t.nextState = s.nextState) (directionCount : t.nextDirection = s.nextDirection)
    (states : t.states = s.states) (directions : t.directions = s.directions)
    (markers : t.markers = s.markers) : MainData t B r :=
  ⟨stateCount.trans hs.states, directionCount.trans hs.directions, markers.trans hs.markers,
    fun k hk => by rw [states]; exact hs.history k hk,
    fun k hk => by rw [directions]; exact hs.direction k hk⟩

lemma main_finish (s : TraceState) (c B r : ℕ) (hs : MainData s B r)
    (ha : ActiveData s c B r B) :
    MainData (step (step s (.finish c)) (.mark s.nextState)) B (r + 1) := by
  let t := step s (.finish c)
  have hstates : t.nextState = r + 1 + 1 := congrArg (· + 1) hs.states
  have hdirs : t.nextDirection = r + 1 := congrArg (· + 1) hs.directions
  have hnew : (t.states (r + 1)).history = range (r + 1) := by
    simp only [t, step, hs.states, hs.directions, ha.source, Function.update_self]
    rw [hs.history r le_rfl, range_add_one]
  refine ⟨hstates, hdirs, ?_, ?_, ?_⟩
  · change s.markers ++ [s.nextState] = _
    rw [hs.markers, hs.states]
    exact List.range_succ.symm
  · intro k hk
    change (t.states k).history = _
    by_cases heq : k = r + 1
    · simpa only [heq] using hnew
    · have hlt : k < s.nextState := by rw [hs.states]; omega
      rw [step_old_state s (.finish c) k hlt]
      exact hs.history k (by omega)
  · intro k hk
    change (t.directions k).source = k ∧ (t.directions k).target = k + 1 ∧
      (t.directions k).history = range k ∧ (t.directions k).refresh = 1 ∧
      (t.directions k).movement = 1 ∧ (t.directions k).raw.length = B
    by_cases heq : k = r
    · subst k
      simp only [t, step, hs.states, hs.directions, ha.source, ha.refresh, ha.movement,
        ha.count, Function.update_self, hs.history r le_rfl, and_self]
    · have hlt : k < s.nextDirection := by rw [hs.directions]; omega
      rw [step_old_direction s (.finish c) k hlt]
      exact hs.direction k (by omega)

lemma mark_after_finish (workers : ℕ) (s : TraceState) (c B r : ℕ)
    (hs : MainData s B r) (ha : ActiveData s c B r B) :
    (Event.mark s.nextState).Valid workers (step s (.finish c)) := by
  have hlast : s.markers.getLast?.getD 0 = r := by
    rw [hs.markers, List.range_succ]
    simp
  have hlt : r < s.nextState := by rw [hs.states]; omega
  constructor
  · exact Nat.lt_succ_self _
  · change ((step s (.finish c)).states (s.markers.getLast?.getD 0)).history ⊆ _
    rw [hlast, step_old_state s (.finish c) r hlt]
    simp only [step, Function.update_self, ha.source]
    exact subset_insert _ _

structure ReplyEffect (s t : TraceState) (q : ℕ) : Prop where
  rawCount : t.nextRaw = s.nextRaw
  raw : t.raws = s.raws
  retired : t.retired = insert q s.retired
  collectionCount : s.nextCollection ≤ t.nextCollection
  source : ∀ c < s.nextCollection, (t.collections c).source = (s.collections c).source

lemma reply_effect {m K B : ℕ} (s : Translation m) (w : Fin m) (hs : Data K B s)
    (he : Enabled s.original (.reply w)) :
    let out := advance K B s (.reply w)
    ValidFrom (m + 1) s.trace (emissions K B s (.reply w)) ∧
      ReplyEffect s.trace out.trace (s.raw w) ∧
      MainData out.trace B out.original.round ∧
      (out.original.round < K →
        ActiveData out.trace out.active B out.original.round out.original.batch) ∧
      (out.original.round = s.original.round → out.active = s.active) := by
  let q := s.raw w
  let orig := s.original
  let st := s.trace
  let out := advance K B s (.reply w)
  change ValidFrom (m + 1) s.trace (emissions K B s (.reply w)) ∧
    ReplyEffect s.trace out.trace (s.raw w) ∧ MainData out.trace B out.original.round ∧
    (out.original.round < K → ActiveData out.trace out.active B out.original.round out.original.batch) ∧
    (out.original.round = s.original.round → out.active = s.active)
  have hp := hs.pending w he.2
  by_cases hf : orig.round < K ∧ orig.source w = orig.round
  · have ha := hs.active hf.1
    have hc := hs.fresh w he.2 hf.1 hf.2
    have hreceive : (Event.receive q).Valid (m + 1) st :=
      ⟨hp.existsRaw, hp.freshRaw, hc.symm ▸ ha.openCollection⟩
    let t := step st (.receive q)
    have ht : t.collections s.active = {st.collections s.active with
        delivered := (st.collections s.active).delivered ++ [q]} := by
      simp [t, step, show (st.raws q).collection = s.active from hc]
    have hcount : (t.collections s.active).delivered.length = orig.batch + 1 := by
      rw [ht]
      simp [show (st.collections s.active).delivered.length = orig.batch from ha.count]
    have hmain : MainData t B orig.round := main_same _ _ _ _ hs.main rfl rfl rfl rfl rfl
    have hactive : ActiveData t s.active B orig.round (orig.batch + 1) :=
      ⟨ha.existsCollection, by rw [ht]; exact ha.openCollection, by rw [ht]; exact ha.source,
        by rw [ht]; exact ha.size, hcount, by rw [ht]; exact ha.refresh,
        by rw [ht]; exact ha.movement⟩
    have hsource (c : ℕ) (hc' : c < st.nextCollection) :
        (t.collections c).source = (st.collections c).source :=
      step_old_collection_source st (.receive q) c hc'
    by_cases hB : orig.batch + 1 = B
    · have hcommit : LongTails.Algorithms.BirchNonEuclideanRennala.commits B orig w := ⟨hf.2, hB⟩
      have hround : out.original.round = orig.round + 1 := by
        simp [out, advance, LongTails.Algorithms.BirchNonEuclideanRennala.step, show
          s.original.round < K from hf.1, show
          LongTails.Algorithms.BirchNonEuclideanRennala.commits B s.original w from hcommit, orig]
      have hbatch : out.original.batch = 0 := by
        simp [out, advance, LongTails.Algorithms.BirchNonEuclideanRennala.step,
          show s.original.round < K from hf.1, show
          LongTails.Algorithms.BirchNonEuclideanRennala.fresh s.original w from hf.2,
          show LongTails.Algorithms.BirchNonEuclideanRennala.commits B s.original w from hcommit]
      have hfull : ActiveData t s.active B orig.round B := hB ▸ hactive
      have hfinish : (Event.finish s.active).Valid (m + 1) t :=
        ⟨hfull.existsCollection, hfull.openCollection, hfull.count.trans hfull.size.symm⟩
      have hmark := mark_after_finish (m + 1) t s.active B orig.round hmain hfull
      let u := step t (.finish s.active)
      let v := step u (.mark st.nextState)
      have hmv : MainData v B (orig.round + 1) := main_finish t s.active B orig.round hmain hfull
      have hsv (c : ℕ) (hc' : c < st.nextCollection) :
          (v.collections c).source = (st.collections c).source :=
        (step_old_collection_source t (.finish s.active) c hc').trans (hsource c hc')
      by_cases hn : orig.round + 1 < K
      · let e := Event.capture 0 st.nextState B 1 1
        have he' : e.Valid (m + 1) v := by
          refine ⟨Nat.zero_lt_succ _, ?_, ?_, zero_le_one, le_rfl, le_rfl⟩
          · exact Nat.lt_succ_self _
          · have h := hs.schedule.batch_lt
            omega
        have hev : emissions K B s (.reply w) = [.receive q, .finish s.active, .mark st.nextState, e] :=
          by simp [emissions, show s.original.round < K ∧ s.original.source w = s.original.round from hf,
            show s.original.batch + 1 = B from hB, show s.original.round + 1 < K from hn, q, e, st]
        have hout : out.trace = step v e := by rw [show out.trace = (emissions K B s (.reply w)).foldl step st from rfl, hev]; rfl
        have hact : out.active = st.nextCollection := by
          change (if s.original.round < out.original.round ∧ out.original.round < K then _ else _) = _
          rw [hround]
          simp [orig, st, show s.original.round + 1 < K from hn]
        rw [hev, hout, hround, hbatch, hact]
        refine ⟨⟨hreceive, hfinish, hmark, he', trivial⟩,
          ⟨rfl, rfl, rfl, Nat.le_succ _, ?_⟩,
          main_same _ _ _ _ hmv rfl rfl rfl rfl rfl, ?_, ?_⟩
        · intro c hc'
          exact (step_old_collection_source v e c hc').trans (hsv c hc')
        · intro _
          have hsrc : st.nextState = orig.round + 1 := hs.main.states
          constructor <;> simp [v, u, t, e, step, hsrc]
        · intro h
          exact (Nat.succ_ne_self orig.round h).elim
      · have hev : emissions K B s (.reply w) = [.receive q, .finish s.active, .mark st.nextState] :=
          by simp [emissions, show s.original.round < K ∧ s.original.source w = s.original.round from hf,
            show s.original.batch + 1 = B from hB, show ¬s.original.round + 1 < K from hn, q, st]
        have hout : out.trace = v := by rw [show out.trace = (emissions K B s (.reply w)).foldl step st from rfl, hev]; rfl
        rw [hev, hout, hround]
        exact ⟨⟨hreceive, hfinish, hmark, trivial⟩, ⟨rfl, rfl, rfl, le_rfl, hsv⟩, hmv,
          fun h => (hn h).elim, fun h => (Nat.succ_ne_self _ h).elim⟩
    · have hn : ¬LongTails.Algorithms.BirchNonEuclideanRennala.commits B orig w := fun h => hB h.2
      have hev : emissions K B s (.reply w) = [.receive q] := by
        simp [emissions, show s.original.round < K ∧ s.original.source w = s.original.round from hf,
          show s.original.batch + 1 ≠ B from hB, q]
      have hout : out.trace = t := by rw [show out.trace = (emissions K B s (.reply w)).foldl step st from rfl, hev]; rfl
      have hround : out.original.round = orig.round := by
        simp [out, advance, LongTails.Algorithms.BirchNonEuclideanRennala.step,
          show s.original.round < K from hf.1, show
          ¬LongTails.Algorithms.BirchNonEuclideanRennala.commits B s.original w from hn, orig]
      have hbatch : out.original.batch = orig.batch + 1 := by
        simp [out, advance, LongTails.Algorithms.BirchNonEuclideanRennala.step,
          show s.original.round < K from hf.1, show
          LongTails.Algorithms.BirchNonEuclideanRennala.fresh s.original w from hf.2,
          show ¬LongTails.Algorithms.BirchNonEuclideanRennala.commits B s.original w from hn, orig]
      have hact : out.active = s.active := by
        change (if s.original.round < out.original.round ∧ out.original.round < K then _ else _) = _
        rw [hround]
        simp [orig]
      rw [hev, hout, hround, hbatch, hact]
      exact ⟨⟨hreceive, trivial⟩, ⟨rfl, rfl, rfl, le_rfl, hsource⟩, hmain,
        fun _ => hactive, fun _ => rfl⟩
  · let t := step st (.discard q)
    have hev : emissions K B s (.reply w) = [.discard q] := by simpa [emissions, q] using
      (ite_eq_right (show ¬ (s.original.round < K ∧ s.original.source w = s.original.round) from hf) :
        (if s.original.round < K ∧ s.original.source w = s.original.round then
          if s.original.batch + 1 = B then
            [Event.receive (s.raw w), Event.finish s.active, Event.mark s.trace.nextState] ++
              if s.original.round + 1 < K then [Event.capture 0 s.trace.nextState B 1 1] else []
          else [Event.receive (s.raw w)] else [Event.discard (s.raw w)]) = [Event.discard (s.raw w)])
    have hout : out.trace = t := by rw [show out.trace = (emissions K B s (.reply w)).foldl step st from rfl, hev]; rfl
    have hroundbatch : out.original.round = orig.round ∧ out.original.batch = orig.batch := by
      by_cases hk : orig.round < K
      · have hn : ¬LongTails.Algorithms.BirchNonEuclideanRennala.fresh orig w := fun h => hf ⟨hk, h⟩
        have hnc : ¬LongTails.Algorithms.BirchNonEuclideanRennala.commits B orig w := fun h => hn h.1
        simp [out, advance, LongTails.Algorithms.BirchNonEuclideanRennala.step, show s.original.round < K from hk,
          show ¬LongTails.Algorithms.BirchNonEuclideanRennala.fresh s.original w from hn,
          show ¬LongTails.Algorithms.BirchNonEuclideanRennala.commits B s.original w from hnc, orig]
      · simp [out, advance, LongTails.Algorithms.BirchNonEuclideanRennala.step,
          show ¬s.original.round < K from hk, orig]
    have hact : out.active = s.active := by
      change (if s.original.round < out.original.round ∧ out.original.round < K then _ else _) = _
      rw [hroundbatch.1]
      simp [orig]
    rw [hev, hout, hroundbatch.1, hroundbatch.2, hact]
    refine ⟨⟨⟨hp.existsRaw, hp.freshRaw⟩, trivial⟩, ⟨rfl, rfl, rfl, le_rfl, fun _ _ => rfl⟩,
      main_same _ _ _ _ hs.main rfl rfl rfl rfl rfl, ?_, fun _ => rfl⟩
    intro hk
    have ha := hs.active hk
    exact ⟨ha.existsCollection, ha.openCollection, ha.source, ha.size, ha.count,
      ha.refresh, ha.movement⟩

lemma data_reply {m K B : ℕ} (s : Translation m) (w : Fin m) (hs : Data K B s)
    (he : Enabled s.original (.reply w)) : Data K B (advance K B s (.reply w)) := by
  let out := advance K B s (.reply w)
  obtain ⟨hv, hx, hm, ha, hactive⟩ := reply_effect s w hs he
  have hready : out.original.ready = s.original.ready.erase w := by
    change (ostep K B s.original (.reply w)).ready = _
    simp only [LongTails.Algorithms.BirchNonEuclideanRennala.step]
    split_ifs <;> rfl
  have hraw (v : Fin m) : out.raw v = s.raw v := rfl
  have hsource (v : Fin m) (hne : v ≠ w) : out.original.source v = s.original.source v := by
    change (ostep K B s.original (.reply w)).source v = _
    simp only [LongTails.Algorithms.BirchNonEuclideanRennala.step]
    split_ifs <;> simp [Function.update_of_ne hne]
  have hround : s.original.round ≤ out.original.round := by
    change s.original.round ≤ (ostep K B s.original (.reply w)).round
    simp only [LongTails.Algorithms.BirchNonEuclideanRennala.step]
    split_ifs <;> simp
  have hold (v : Fin m) (hv : v ∈ out.original.ready) : v ≠ w ∧ v ∈ s.original.ready := by
    rw [hready] at hv
    exact mem_erase.mp hv
  change Data K B out
  refine ⟨step_invariant K B _ _ hs.schedule he, advance_represented K B s _ hs.represented,
    legal_advance s _ hs hv, retired_past_fold _ _ _ hs.retired hv, hm, ha, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hne, hmem⟩ := hold v hv
    have hp := hs.pending v hmem
    have hd := hs.distinct v hmem w he.2 hne
    change ReplyEffect s.trace out.trace (s.raw w) at hx
    rw [hraw, hsource v hne]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hx.rawCount]
      exact hp.existsRaw
    · rw [hx.retired]
      exact fun h => (mem_insert.mp h).elim hd hp.freshRaw
    · rw [hx.raw]
      exact hp.existsCollection.trans_le hx.collectionCount
    · rw [hx.raw, hx.source _ hp.existsCollection]
      exact hp.source
    · rw [hx.raw]
      exact hp.worker
  · intro v hv hk hf
    obtain ⟨hne, hmem⟩ := hold v hv
    rw [hsource v hne] at hf
    have hle := hs.schedule.source_le v
    have heq : out.original.round = s.original.round := by omega
    change ReplyEffect s.trace out.trace (s.raw w) at hx
    rw [hraw, hx.raw, hactive heq]
    exact hs.fresh v hmem (heq ▸ hk) (hf.trans heq)
  · intro v hv u hu hne
    rw [hraw, hraw]
    exact hs.distinct v (hold v hv).2 u (hold u hu).2 hne

lemma data_fold {m K B : ℕ} (s : Translation m)
    (events : List (OriginalEvent m)) (hs : Data K B s)
    (he : LongTails.Algorithms.BirchNonEuclideanRennala.LegalFrom K B s.original events) :
    Data K B (events.foldl (advance K B) s) := by
  induction events generalizing s with
  | nil => exact hs
  | cons e events ih =>
    apply ih _ _ he.2
    cases e with
    | query w => exact data_query s w hs he.1
    | reply w => exact data_reply s w hs he.1

lemma data_translate {m K B : ℕ} (events : List (OriginalEvent m)) (hK : 0 < K) (hB : 0 < B)
    (he : LongTails.Algorithms.BirchNonEuclideanRennala.LegalFrom K B {} events) :
    Data K B (translate K B events) :=
  data_fold _ events (data_initial m K B hK hB) he

end LongTails.Proofs.BirchCollectionRennalaReply
