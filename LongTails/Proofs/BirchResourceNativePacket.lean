import LongTails.Algorithms.BirchResourceNative
import LongTails.Proofs.BirchCollectionBatches

namespace LongTails.Proofs.BirchResourceNativePacket

open Finset LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionBatches
open LongTails.Algorithms.BirchResourceNative
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution (step_old_state)

lemma discard_step (workers : ℕ) (s : TraceState) (c : ℕ) (hs : RetiredPast s)
    (hw : 0 < workers) (hc : c < s.nextCollection) (ho : (s.collections c).closed = false) :
    ValidFrom workers s [.issue c 0, .discard s.nextRaw] := by
  refine ⟨⟨hc, hw, ho⟩, ⟨?_, trivial⟩⟩
  have hf : s.nextRaw ∉ s.retired := fun h => (Nat.lt_irrefl _ (mem_range.mp (hs h))).elim
  simp [Event.Valid, step, hf]

lemma discard_replies (workers : ℕ) (s : TraceState) (c n : ℕ) (hs : RetiredPast s)
    (hw : 0 < workers) (hc : c < s.nextCollection) (ho : (s.collections c).closed = false) :
    let t := (discardReplies c s n).foldl step s
    ValidFrom workers s (discardReplies c s n) ∧
    t.nextRaw = s.nextRaw + n ∧ t.nextCollection = s.nextCollection ∧ t.collections = s.collections ∧
    t.nextState = s.nextState ∧ t.nextDirection = s.nextDirection ∧ t.states = s.states ∧
    t.directions = s.directions ∧ t.markers = s.markers := by
  induction n generalizing s with
  | zero => simp [discardReplies, ValidFrom]
  | succ n ih =>
    let t := step (step s (.issue c 0)) (.discard s.nextRaw)
    have hv := discard_step workers s c hs hw hc ho
    have ht : RetiredPast t := retired_past_fold workers s _ hs hv
    obtain ⟨hv', hr, hcc, hc', hsc, hdc, hss, hds, hm⟩ := ih t ht hc ho
    refine ⟨⟨hv.1, hv.2.1, hv'⟩, ?_, hcc, hc', hsc, hdc, hss, hds, hm⟩
    change ((discardReplies c t n).foldl step t).nextRaw = _
    rw [hr]
    change s.nextRaw + 1 + n = _
    omega

structure PacketEffect (s t : TraceState) (source b waste : ℕ) (β w : ℝ) : Prop where
  raw : t.nextRaw = s.nextRaw + b + waste
  stateCount : t.nextState = s.nextState + 2
  directionCount : t.nextDirection = s.nextDirection + 1
  markers : t.markers = s.markers
  oldState : ∀ j < s.nextState, t.states j = s.states j
  oldDirection : ∀ j < s.nextDirection, t.directions j = s.directions j
  privateHistory : (t.states s.nextState).history = insert s.nextDirection (s.states source).history
  publishedHistory : (t.states (s.nextState + 1)).history = range (s.nextDirection + 1)
  direction : t.directions s.nextDirection =
    { collection := s.nextCollection, source, target := s.nextState,
      history := (s.states source).history, refresh := β, movement := w,
      raw := List.range' s.nextRaw b }

lemma packet (workers : ℕ) (s : TraceState) (source b waste : ℕ) (β w : ℝ)
    (hs : RetiredPast s) (hw : 0 < workers) (hb : 0 < b)
    (hsr : source < s.nextState) (hsc : 0 < s.nextState)
    (hβ : β ≤ 1) (hm : 0 ≤ w) (hmβ : w ≤ β)
    (hprev : (s.states (s.nextState - 1)).history = range s.nextDirection)
    (hsource : (s.states source).history ⊆ range s.nextDirection) :
    ValidFrom workers s (packetCode s source b waste β w) ∧
      PacketEffect s ((packetCode s source b waste β w).foldl step s) source b waste β w := by
  let cap := Event.capture 0 source b β w
  let t := step s cap
  let accepted := batchReplies s.nextCollection t (List.replicate b 0)
  let u := accepted.foldl step t
  let extras := discardReplies s.nextCollection u waste
  let v := extras.foldl step u
  let f := step v (.finish s.nextCollection)
  let out := step f (.merge 0 (s.nextState - 1) s.nextState source)
  have hcap : cap.Valid workers s := ⟨hw, hsr, hb, hm, hmβ, hβ⟩
  have ht : RetiredPast t := retired_past_step workers s cap hs hcap
  obtain ⟨haccepted, ha⟩ := batch_replies workers t s.nextCollection (List.replicate b 0)
    ht (Nat.lt_succ_self _) (by simp [t, cap, step]) (fun w hw' => by have he : w = 0 := List.eq_of_mem_replicate hw'; simpa [he] using hw)
  have hu : RetiredPast u := retired_past_fold workers t accepted ht haccepted
  have huc : u.nextCollection = s.nextCollection + 1 := ha.collectionCount
  have hrec : u.collections s.nextCollection =
      { owner := 0, source, size := b, refresh := β, movement := w,
        delivered := List.range' s.nextRaw b } := by
    rw [ha.value]
    simp [t, cap, step]
  obtain ⟨hextras, hvraw, hvcc, hvcols, hvsc', hvdc', hvstates', hvdirs', hvm⟩ :=
    discard_replies workers u s.nextCollection waste hu hw (huc.symm ▸ Nat.lt_succ_self _)
      (by rw [hrec])
  have hvsc : v.nextState = s.nextState := hvsc'.trans ha.stateCount
  have hvdc : v.nextDirection = s.nextDirection := hvdc'.trans ha.directionCount
  have hvstates : v.states = s.states := hvstates'.trans ha.states
  have hvdirs : v.directions = s.directions := hvdirs'.trans ha.directions
  have hvrec : v.collections s.nextCollection =
      { owner := 0, source, size := b, refresh := β, movement := w,
        delivered := List.range' s.nextRaw b } := by rw [show v.collections = _ from hvcols, hrec]
  have hfinish : (Event.finish s.nextCollection).Valid workers v := by
    simp [Event.Valid, show v.nextCollection = u.nextCollection from hvcc, huc, hvrec]
  have hfstate : f.nextState = s.nextState + 1 := by
    change v.nextState + 1 = _
    rw [hvsc]
  have hfprev (j : ℕ) (hj : j < s.nextState) : f.states j = s.states j :=
    (step_old_state v _ j (hvsc.symm ▸ hj)).trans (congrFun hvstates j)
  have hnew : (f.states s.nextState).history =
      insert s.nextDirection (s.states source).history := by
    simp [f, step, hvsc, hvdc, hvrec, hvstates]
  have hmerge : (Event.merge 0 (s.nextState - 1) s.nextState source).Valid workers f := by
    change 0 < workers ∧ s.nextState - 1 < f.nextState ∧ s.nextState < f.nextState ∧
      source < f.nextState ∧ (f.states source).history =
        (f.states (s.nextState - 1)).history ∩ (f.states s.nextState).history
    refine ⟨hw, by omega, by omega, by omega, ?_⟩
    rw [hfprev _ hsr, hfprev _ (by omega), hnew, hprev]
    ext j
    simp only [mem_inter, mem_insert, mem_range]
    constructor
    · intro hj
      exact ⟨mem_range.mp (hsource hj), Or.inr hj⟩
    · rintro ⟨hj, he | hj'⟩
      · omega
      · exact hj'
  have hout (j : ℕ) (hj : j < s.nextState + 1) : out.states j = f.states j :=
    step_old_state f _ j (hfstate.symm ▸ hj)
  have hlegal : ValidFrom workers s (packetCode s source b waste β w) := by
    change cap.Valid workers s ∧ ValidFrom workers t
      (accepted ++ (extras ++ [.finish s.nextCollection, .merge 0 (s.nextState - 1) s.nextState source]))
    exact ⟨hcap, (valid_append _ _ _ _).2 ⟨haccepted,
      (valid_append _ _ _ _).2 ⟨hextras, hfinish, hmerge, trivial⟩⟩⟩
  have heq : (packetCode s source b waste β w).foldl step s = out := by
    simp only [packetCode, List.foldl_cons, List.foldl_append, List.foldl_nil]
    rfl
  rw [heq]
  refine ⟨hlegal, ⟨?_, ?_, ?_, hvm.trans ha.markers, ?_, ?_, ?_, ?_, ?_⟩⟩
  · change v.nextRaw = _
    rw [show v.nextRaw = u.nextRaw + waste from hvraw, ha.raw, List.length_replicate]
    rfl
  · change f.nextState + 1 = _
    rw [hfstate]
  · change v.nextDirection + 1 = _
    rw [hvdc]
  · intro j hj
    exact (hout j (by omega)).trans (hfprev j hj)
  · intro j hj
    change (Function.update v.directions v.nextDirection _) j = _
    rw [Function.update_of_ne (ne_of_lt (hvdc.symm ▸ hj)), hvdirs]
  · rw [hout _ (by omega), hnew]
  · change ((Function.update f.states f.nextState _) (s.nextState + 1)).history = _
    rw [hfstate, Function.update_self, hnew, hfprev _ (by omega), hprev]
    ext j
    simp only [mem_union, mem_range, mem_insert]
    constructor
    · rintro (hj | hj | hj)
      · omega
      · omega
      · have hh := mem_range.mp (hsource hj)
        omega
    · intro hj
      by_cases he : j = s.nextDirection
      · exact Or.inr (Or.inl he)
      · exact Or.inl (by omega)
  · change (Function.update v.directions v.nextDirection _) s.nextDirection = _
    simp [hvdc, hvsc, hvrec, hvstates]

end LongTails.Proofs.BirchResourceNativePacket
