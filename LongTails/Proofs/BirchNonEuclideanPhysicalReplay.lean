import LongTails.Proofs.BirchNonEuclideanPairedReplay

namespace LongTails.Proofs.BirchNonEuclideanPhysicalReplay

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Algorithms.BirchNonEuclideanTrajectories
open LongTails.Proofs.BirchNonEuclideanScheduling
open LongTails.Proofs.BirchNonEuclideanReplay
open LongTails.Proofs.BirchNonEuclideanEventCounter
open LongTails.Proofs.BirchNonEuclideanEventCosts
open LongTails.Proofs.BirchNonEuclideanEventLabels
open LongTails.Proofs.BirchNonEuclideanEventMeaning
open LongTails.Proofs.BirchNonEuclideanEventHistory
open LongTails.Proofs.BirchNonEuclideanPairedReplay
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta
open LongTails.Proofs.BirchNonEuclideanUnused

lemma eventsStateCode_history {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (events : List (Event m)) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid)
    (hr : Labelled (queryLabels H K B events) response labelled)
    (he : LegalFrom H K (packetCutoff H B) word {} events) :
    let t := canonicalTuning η B
    let init := localBatch 0 0 B {}
    let z := eventsStateCode H K B events {}
    let values := readValues (codeMemory p lmo response t z.2) z.1.2
    let jobs := (eventRun K (packetCutoff H B) events).schedule.accepted
    (values.points, values.momenta) =
      pairedValues p lmo (packetResponse labelled jobs) η B H (packetSource jobs)
        ((codeMemory p lmo response t init.2).vectors init.1) jobs.length := by
  let initial := (codeMemory p lmo response (canonicalTuning η B) (localBatch 0 0 B {}).2).vectors
    (localBatch 0 0 B {}).1
  have hi := replayInvariant_fold p lmo labelled η B H K (packetCutoff H B) initial
    ({}, initialValues p initial) events word he
    (replayInvariant_initial p lmo labelled η B H K (packetCutoff H B) initial)
  have hh := eventsStateCode_values p lmo response labelled η B H K events ht hr
  dsimp only at hh
  rw [initialCode_values] at hh
  change _ = events.foldl _ (({} : EventState m), initialValues p initial) at hh
  rw [← hh] at hi
  have hg := hi.2.2
  dsimp only [HistoryMatches] at hg
  rw [eventsStateCode_public] at hg
  dsimp only
  rw [hg.1, hg.2]
  exact packetHistory_pairedValues p lmo labelled η B H initial _

lemma completeTrace_history {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (events : List (Event m)) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid) (hK : 0 < K) (hm : 0 < m)
    (hr : Labelled (queryLabels H K B events) response labelled)
    (he : CompleteTrace H K B word events) :
    let t := canonicalTuning η B
    let init := localBatch 0 0 B {}
    let z := eventsStateCode H K B events {}
    let values := readValues (codeMemory p lmo response t z.2) z.1.2
    let jobs := (finalSchedule H K B word).accepted
    (values.points, values.momenta) =
      pairedValues p lmo (packetResponse labelled jobs) η B H (packetSource jobs)
        ((codeMemory p lmo response t init.2).vectors init.1) K := by
  have hh := eventsStateCode_history p lmo response labelled η B H K events word ht hr he.1
  rw [completeTrace_schedule H K B word events hK hm he] at hh
  have hl : (finalSchedule H K B word).accepted.length = K :=
    scheduleRun_stopped K (packetCutoff H B) word hK hm
  simpa only [hl] using hh

lemma Labelled.get {m : ℕ} {d : ℕ} {labels : List (QueryLabel m)}
    {response : ℕ → Point d → Point d} {labelled : QueryLabel m → Point d → Point d}
    (hr : Labelled labels response labelled) {i : ℕ} {lab : QueryLabel m}
    (hi : labels[i]? = some lab) : response i = labelled lab := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hi
  funext x
  simpa only [he] using hr i hi x

lemma packetsLabels_get {m : ℕ} (H : ℕ) (jobs : List (Packet m)) (k h : ℕ)
    (hk : k < jobs.length) (hh : h < H) :
    (jobs.flatMap (packetLabels H))[k * H + h]? =
      some (Sum.inr (jobs[k].worker, jobs[k].serial, h)) := by
  induction jobs generalizing k with
  | nil => simp at hk
  | cons job jobs ih =>
      cases k with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
          rw [List.getElem?_append_left (by simpa only [packetLabels_length] using hh)]
          simp [packetLabels, List.getElem?_eq_getElem (by simpa using hh : h < (List.range H).length)]
      | succ k =>
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem?_append_right (by simp only [packetLabels_length, Nat.add_mul]; omega)]
          rw [packetLabels_length]
          have hi : (k + 1) * H + h - H = k * H + h := by rw [Nat.add_mul]; omega
          rw [hi]
          exact ih k (by simpa using hk)

lemma normalLabels_packet_get {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (k h : ℕ)
    (hk : k < (finalSchedule H K B word).accepted.length) (hh : h < H) :
    (normalLabels H K B word)[B + k * H + h]? =
      some (Sum.inr ((finalSchedule H K B word).accepted[k].worker,
        (finalSchedule H K B word).accepted[k].serial, h)) := by
  unfold normalLabels
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
  simp only [List.length_map, List.length_range]
  have hi : B + k * H + h - B = k * H + h := by omega
  rw [hi, List.flatMap_append]
  rw [List.getElem?_append_left (by
    rw [packetsLabels_length, Nat.mul_comm H]
    have hn : (k + 1) * H ≤ (finalSchedule H K B word).accepted.length * H :=
      Nat.mul_le_mul_right H (by omega)
    rw [Nat.add_mul] at hn
    omega)]
  exact packetsLabels_get H _ k h hk hh

lemma Labelled.of_nodup {m d : ℕ} (labels : List (QueryLabel m))
    (response : ℕ → Point d → Point d) (hn : labels.Nodup) :
    Labelled labels response (fun lab => response (labels.idxOf lab)) := by
  intro i hi x
  dsimp only
  rw [hn.idxOf_getElem i hi]

lemma Labelled.reindex {m d : ℕ} {left right : List (QueryLabel m)}
    {response : ℕ → Point d → Point d} {labelled : QueryLabel m → Point d → Point d}
    (hr : Labelled left response labelled) (hp : left.Perm right) :
    Labelled right (fun i => response (labelIndex hp i)) labelled := by
  intro i hi x
  have hh := hr (labelIndex hp i) (labelIndex_mem hp i hi) x
  simpa only [labelIndex_get hp i hi] using hh

lemma Labelled.initial {m d : ℕ} (B : ℕ) {tail : List (QueryLabel m)}
    {response : ℕ → Point d → Point d} {labelled : QueryLabel m → Point d → Point d}
    (hr : Labelled ((List.range B).map Sum.inl ++ tail) response labelled)
    (b : ℕ) (hb : b < B) : response b = labelled (Sum.inl b) := by
  apply Labelled.get hr
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [List.getElem?_range hb]

lemma labelled_initial_mean {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (t : Tuning) (B : ℕ) (tail : List (QueryLabel m))
    (hr : Labelled ((List.range B).map Sum.inl ++ tail) response labelled) :
    let init := localBatch 0 0 B {}
    (codeMemory p lmo response t init.2).vectors init.1 =
      (1 / (B : ℝ)) • ∑ b ∈ Finset.range B, labelled (Sum.inl b) p.x0 := by
  dsimp only
  rw [localBatch_memory_mean p lmo response t 0 0 B {} rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  simpa only [LongTails.Proofs.BirchNonEuclideanFamilies.codeCalls, List.map_nil, List.sum_nil,
    zero_add, codeMemory, LongTails.Proofs.BirchNonEuclideanConstruction.codeInstructions,
    LongTails.Proofs.BirchNonEuclideanExecution.interpret, initialMemory]
    using congrFun (Labelled.initial B hr b (Finset.mem_range.mp hb)) p.x0

lemma pairedValues_congr_local (p : Params) (lmo : Point p.d → Point p.d)
    (response response' : ℕ → ℕ → Point p.d → Point p.d) (η : ℝ) (B H K : ℕ)
    (dispatch : ℕ → ℕ) (initial : Point p.d)
    (hr : ∀ k < K, ∀ h < H, ∀ x, response k h x = response' k h x) :
    pairedValues p lmo response η B H dispatch initial K =
      pairedValues p lmo response' η B H dispatch initial K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [pairedValues, pairedValues, ih (fun k hk => hr k (by omega))]
      rw [localValues_congr p lmo (response K) (response' K) η B H H _ (hr K (by omega))]

lemma canonical_labelled_history {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid) (hK : 0 < K) (hm : 0 < m)
    (hr : Labelled (normalLabels H K B word) response labelled) :
    let t := canonicalTuning η B
    let jobs := (finalSchedule H K B word).accepted
    let init := localBatch 0 0 B {}
    let z := LongTails.Proofs.BirchNonEuclideanDelta.deltaPrefix H (packetSource jobs) (packetWorker jobs) K B
    let mem := codeMemory p lmo response t z.2
    (fun j => mem.points (z.1.1 j), fun j => mem.vectors (z.1.2 j)) =
      pairedValues p lmo (packetResponse labelled jobs) η B H (packetSource jobs)
        ((codeMemory p lmo response t init.2).vectors init.1) K := by
  dsimp only
  rw [deltaPrefix_memory p lmo response (m + 1) H K B _ _ η ht (by omega) (packetWorker_bound _)]
  apply pairedValues_congr_local
  intro k hk h hh x
  have hl : (finalSchedule H K B word).accepted.length = K :=
    scheduleRun_stopped K (packetCutoff H B) word hK hm
  have hk' : k < (finalSchedule H K B word).accepted.length := by omega
  have he := congrFun (Labelled.get hr (normalLabels_packet_get H K B word k h hk' hh)) x
  simpa only [packetResponse, List.getElem?_eq_getElem hk'] using he

lemma physicalLocalCode_memory {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (H K B : ℕ)
    (word : ℕ → Fin m) (ht : t.Valid) :
    let jobs := (finalSchedule H K B word).accepted
    let z := deltaPrefix H (packetSource jobs) (packetWorker jobs) K B
    let r := physicalLocalCode H K B word {}
    (fun j => (codeMemory p lmo response t r.2).points (r.1 j)) =
      fun j => (codeMemory p lmo response t z.2).points (z.1.1 j) := by
  let jobs := (finalSchedule H K B word).accepted
  let z := deltaPrefix H (packetSource jobs) (packetWorker jobs) K B
  have hv := deltaPrefix_valid (m + 1) H K B (packetSource jobs) (packetWorker jobs) t ht
    (by omega) (packetWorker_bound jobs)
  have hb := codeValid_register_bound (m + 1) t z.2 hv.1
  have hn : z.2.next = (codeMemory p lmo response t z.2).next := by
    rw [codeMemory_next, ← codeLayout_next t z.2]
    exact hv.1.1
  have he := state_forIn_extends (fun job (_ : Unit) =>
      unusedPacket (job.worker.val + 1) (z.1.1 job.source) (z.1.2 job.source) H 0)
    (ignored (finalSchedule H K B word)) () z.2
    (fun job _ _ => unusedPacket_extends _ _ _ _ _)
  dsimp only
  change (fun j => (codeMemory p lmo response t ((physicalLocalCode H K B word).run {}).2).points
    (((physicalLocalCode H K B word).run {}).1 j)) = _
  rw [physicalLocalCode_run]
  funext j
  exact (codeMemory_old p lmo response t z.2 _ he _ (hn ▸ hb.1 0 _ (hv.2.1 j))).1

lemma completeTrace_labelled_output {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response normal : ℕ → Point p.d → Point p.d)
    (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (events : List (Event m)) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid) (hK : 0 < K) (hm : 0 < m)
    (hr : Labelled (queryLabels H K B events) response labelled)
    (hn : Labelled (normalLabels H K B word) normal labelled)
    (he : CompleteTrace H K B word events) :
    let t := canonicalTuning η B
    let z := eventsCode H K B events {}
    let r := physicalLocalCode H K B word {}
    (fun j => (codeMemory p lmo response t z.2).points (z.1 j)) =
      fun j => (codeMemory p lmo normal t r.2).points (r.1 j) := by
  have hp := completeTrace_history p lmo response labelled η B H K events word ht hK hm hr he
  have hc := canonical_labelled_history p lmo normal labelled η B H K word ht hK hm hn
  have hi := labelled_initial_mean p lmo response labelled (canonicalTuning η B) B _ hr
  have hi' := labelled_initial_mean p lmo normal labelled (canonicalTuning η B) B _ hn
  dsimp only at hp hc hi hi'
  rw [hi] at hp
  rw [hi'] at hc
  have hg := congrArg Prod.fst (hp.trans hc.symm)
  dsimp only at hg ⊢
  rw [physicalLocalCode_memory p lmo normal (canonicalTuning η B) H K B word ht]
  exact hg

lemma completeTrace_replay {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (events : List (Event m)) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid) (hK : 0 < K) (hm : 0 < m)
    (he : CompleteTrace H K B word events) :
    let t := canonicalTuning η B
    let perm := completeTrace_labels_perm H K B word events hK hm he
    let z := eventsCode H K B events {}
    let r := physicalLocalCode H K B word {}
    (fun j => (codeMemory p lmo response t z.2).points (z.1 j)) =
      fun j => (codeMemory p lmo (fun i => response (labelIndex perm i)) t r.2).points (r.1 j) := by
  let labels := queryLabels H K B events
  have hr := Labelled.of_nodup labels response
    (LongTails.Proofs.BirchNonEuclideanEvents.queryLabels_nodup H K B word events he.1)
  exact completeTrace_labelled_output p lmo response _ _ η B H K events word ht hK hm hr
    (Labelled.reindex hr (completeTrace_labels_perm H K B word events hK hm he)) he

lemma eventsStateCode_captured {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (events : List (Event m)) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid)
    (hr : Labelled (queryLabels H K B events) response labelled)
    (he : LegalFrom H K (packetCutoff H B) word {} events) :
    let z := eventsStateCode H K B events {}
    Captured p lmo labelled η B H
      (z.1.1, readValues (codeMemory p lmo response (canonicalTuning η B) z.2) z.1.2) := by
  let initial := (codeMemory p lmo response (canonicalTuning η B) (localBatch 0 0 B {}).2).vectors
    (localBatch 0 0 B {}).1
  have hi := replayInvariant_fold p lmo labelled η B H K (packetCutoff H B) initial
    ({}, initialValues p initial) events word he
    (replayInvariant_initial p lmo labelled η B H K (packetCutoff H B) initial)
  have hh := eventsStateCode_values p lmo response labelled η B H K events ht hr
  dsimp only at hh
  rw [initialCode_values] at hh
  change _ = events.foldl _ (({} : EventState m), initialValues p initial) at hh
  rw [← hh] at hi
  exact hi.2.1

lemma physical_query_point {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (pre : List (Event m)) (word : ℕ → Fin m) (w : Fin m)
    (ht : (canonicalTuning η B).Valid)
    (hr : Labelled (queryLabels H K B (pre ++ [.query w])) response labelled)
    (he : LegalFrom H K (packetCutoff H B) word {} pre)
    (hw : w ∈ (eventRun K (packetCutoff H B) pre).live) :
    let z := eventsStateCode H K B pre {}
    let mem := codeMemory p lmo response (canonicalTuning η B) z.2
    let src := z.1.1.schedule.source w
    mem.points (z.1.2.point w) =
      (localValues p lmo (fun h => labelled (Sum.inr (w, z.1.1.schedule.serial w, h))) η B H
        (mem.points (z.1.2.points src), mem.vectors (z.1.2.momenta src)) (z.1.1.progress w)).1 := by
  have hc := eventsStateCode_captured p lmo response labelled η B H K pre word ht
    (LongTails.Proofs.BirchNonEuclideanEventCounter.Labelled.prefix hr (queryLabels_prefix H K B pre [.query w])) he
  have hh := hc w (by simpa only [eventsStateCode_public] using hw)
  rw [hh.1, hh.2.1] at hh
  exact congrArg Prod.fst hh.2.2

end LongTails.Proofs.BirchNonEuclideanPhysicalReplay
