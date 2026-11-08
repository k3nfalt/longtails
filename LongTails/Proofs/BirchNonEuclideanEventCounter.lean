import LongTails.Proofs.BirchNonEuclideanReplay
import LongTails.Proofs.BirchNonEuclideanEventLegality

namespace LongTails.Proofs.BirchNonEuclideanEventCounter

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanReplay

noncomputable def eventLoop {m : ℕ} (H K R : ℕ) (events : List (Event m))
    (state : EventState m × Registers m) : StateM CodeState (EventState m × Registers m) :=
  forIn events state (fun e state => ForInStep.yield <$> eventCode H K R e state)

lemma eventLoop_public {m : ℕ} (H K R : ℕ) (events : List (Event m))
    (state : EventState m × Registers m) (s : CodeState) :
    (eventLoop H K R events state s).1.1 = events.foldl (eventStep K R) state.1 := by
  induction events generalizing state s with
  | nil => rfl
  | cons e rest ih =>
      change ((forIn (e :: rest) state
        (fun e state => ForInStep.yield <$> eventCode H K R e state) :
          StateM CodeState (EventState m × Registers m)) s).1.1 = _
      rw [state_forIn_cons]
      change (eventLoop H K R rest (eventCode H K R e state s).1 (eventCode H K R e state s).2).1.1 = _
      rw [ih, eventCode_public]
      rfl

lemma initialCode_calls (m B : ℕ) (s : CodeState) :
    codeCalls (initialCode m B s).2 = codeCalls s + B := by
  simp only [initialCode, state_bind_apply, state_pure_apply]
  change codeCalls ((forIn (List.finRange m) () (fun w _ => ForInStep.yield <$>
    launchCode (w.val + 1) 0 (localBatch 0 0 B s).1) : StateM CodeState Unit)
      (localBatch 0 0 B s).2).2 = _
  rw [state_forIn_cost codeCalls _ 0 (fun w _ s => by simpa using launchCode_calls (w.val + 1) 0 _ s)]
  simpa only [StateT.run, Nat.mul_zero, Nat.add_zero] using localBatch_calls 0 0 B s

lemma eventsStateCode_run {m : ℕ} (H K B : ℕ) (events : List (Event m)) (s : CodeState) :
    eventsStateCode H K B events s =
      let start := initialCode m B s
      eventLoop H K (packetCutoff H B) events ({}, start.1) start.2 := rfl

lemma eventsStateCode_public {m : ℕ} (H K B : ℕ) (events : List (Event m)) (s : CodeState) :
    (eventsStateCode H K B events s).1.1 = eventRun K (packetCutoff H B) events := by
  rw [eventsStateCode_run]
  exact eventLoop_public H K (packetCutoff H B) events _ _

lemma eventsStateCode_calls {m : ℕ} (H K B : ℕ) (events : List (Event m)) (s : CodeState) :
    codeCalls (eventsStateCode H K B events s).2 = codeCalls s + B + (eventRun K (packetCutoff H B) events).queries.length := by
  rw [eventsStateCode_run]
  dsimp only [eventLoop]
  rw [state_forIn_weighted_cost codeCalls _ eventQueries (eventCode_calls H K (packetCutoff H B)),
    initialCode_calls]
  rw [eventRun, eventFold_query_length]
  simp

lemma eventsStateCode_append {m : ℕ} (H K B : ℕ) (pre rest : List (Event m)) (s : CodeState) :
    eventsStateCode H K B (pre ++ rest) s =
      let z := eventsStateCode H K B pre s
      eventLoop H K (packetCutoff H B) rest z.1 z.2 := by
  simp only [eventsStateCode_run, eventLoop, state_forIn_append]

lemma eventsStateCode_query_counter {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (H K B : ℕ) (pre : List (Event m)) :
    (codeMemory p lmo response t (eventsStateCode H K B pre {}).2).replies =
      B + (eventRun K (packetCutoff H B) pre).queries.length := by
  rw [codeMemory_replies, eventsStateCode_calls]
  simp [codeCalls]

lemma eventFold_queries_prefix {m : ℕ} (K R : ℕ) (events : List (Event m)) (s : EventState m) :
    s.queries.IsPrefix (events.foldl (eventStep K R) s).queries := by
  induction events generalizing s with
  | nil => exact List.prefix_refl _
  | cons e rest ih =>
      apply List.IsPrefix.trans (l₂ := (eventStep K R s e).queries) _ (ih _)
      cases e with
      | query w => exact List.prefix_append _ _
      | complete w => by_cases ha : s.schedule.accepted.length < K <;>
          simp only [eventStep, ha, ite_true, ite_false] <;> exact List.prefix_refl _

lemma queryLabels_next {m : ℕ} (H K B : ℕ) (pre rest : List (Event m)) (w : Fin m) :
    let s := eventRun K (packetCutoff H B) pre
    ∃ tail, queryLabels H K B (pre ++ .query w :: rest) =
      ((List.range B).map Sum.inl ++ s.queries) ++ [Sum.inr (w, s.schedule.serial w, s.progress w)] ++ tail := by
  let s := eventRun K (packetCutoff H B) pre
  obtain ⟨tail, htail⟩ := eventFold_queries_prefix K (packetCutoff H B) rest (eventStep K (packetCutoff H B) s (.query w))
  refine ⟨tail, ?_⟩
  simp only [queryLabels, eventRun, List.foldl_append, List.foldl_cons]
  change (List.range B).map Sum.inl ++ (rest.foldl (eventStep K (packetCutoff H B))
    (eventStep K (packetCutoff H B) s (.query w))).queries = _
  rw [← htail]
  simp only [eventStep, List.append_assoc]
  rfl

lemma queryLabels_getNext {m : ℕ} (H K B : ℕ) (pre rest : List (Event m)) (w : Fin m) :
    let s := eventRun K (packetCutoff H B) pre
    ∃ hi : B + s.queries.length < (queryLabels H K B (pre ++ .query w :: rest)).length,
      (queryLabels H K B (pre ++ .query w :: rest))[B + s.queries.length]'hi =
        Sum.inr (w, s.schedule.serial w, s.progress w) := by
  obtain ⟨tail, htail⟩ := queryLabels_next H K B pre rest w
  dsimp only at htail ⊢
  refine ⟨?_, ?_⟩
  · rw [htail]
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]
    omega
  · rw [List.getElem_of_eq htail]
    rw [List.getElem_append_left (by
      simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]
      omega)]
    rw [List.getElem_append_right (by
      simp only [List.length_append, List.length_map, List.length_range]
      omega)]
    simp only [List.length_append, List.length_map, List.length_range, Nat.sub_self, List.getElem_singleton]

def Labelled {d m : ℕ} (labels : List (QueryLabel m)) (response : ℕ → Point d → Point d)
    (labelled : QueryLabel m → Point d → Point d) : Prop :=
  ∀ i (hi : i < labels.length) x, response i x = labelled (labels[i]) x

lemma Labelled.prefix {d m : ℕ} {labels labels' : List (QueryLabel m)}
    {response : ℕ → Point d → Point d} {labelled : QueryLabel m → Point d → Point d}
    (h : Labelled labels' response labelled) (hp : labels.IsPrefix labels') :
    Labelled labels response labelled := by
  obtain ⟨tail, rfl⟩ := hp
  intro i hi x
  have hh := h i (by simp only [List.length_append]; omega) x
  simpa only [List.getElem_append_left hi] using hh

lemma queryLabels_prefix {m : ℕ} (H K B : ℕ) (pre rest : List (Event m)) :
    (queryLabels H K B pre).IsPrefix (queryLabels H K B (pre ++ rest)) := by
  obtain ⟨tail, htail⟩ := eventFold_queries_prefix K (packetCutoff H B) rest
    (eventRun K (packetCutoff H B) pre)
  refine ⟨tail, ?_⟩
  simp only [queryLabels, eventRun, List.foldl_append]
  dsimp only [eventRun] at htail
  rw [List.append_assoc, htail]

lemma next_reply {m : ℕ} (p : Params) (response : ℕ → Point p.d → Point p.d)
    (labelled : QueryLabel m → Point p.d → Point p.d) (H K B : ℕ)
    (pre rest : List (Event m)) (w : Fin m)
    (hr : Labelled (queryLabels H K B (pre ++ .query w :: rest)) response labelled) (x : Point p.d) :
    let z := eventsStateCode H K B pre {}
    response (codeCalls z.2) x = labelled (Sum.inr (w, z.1.1.schedule.serial w, z.1.1.progress w)) x := by
  obtain ⟨hi, hlabel⟩ := queryLabels_getNext H K B pre rest w
  dsimp only
  rw [eventsStateCode_calls, eventsStateCode_public]
  simp only [codeCalls, List.map_nil, List.sum_nil, zero_add]
  rw [hr _ hi x, hlabel]

end LongTails.Proofs.BirchNonEuclideanEventCounter
