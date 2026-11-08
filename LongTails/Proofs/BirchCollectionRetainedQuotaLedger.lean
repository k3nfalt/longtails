import LongTails.Proofs.BirchCollectionRetainedQuotaStructure

namespace LongTails.Proofs.BirchCollectionRetainedQuotaLedger

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round localAbort localComplete abortPending joinHeads publish)
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Algorithms.BirchCollectionRetainedQuota
open LongTails.Algorithms.BirchCollectionBatches (batchAndMarkWithMove)
open LongTails.Algorithms.BirchCollectionRetune (trace)
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution (fold_raw)
open LongTails.Proofs.BirchCollectionNestedRun (Data start_data advance_data)
open LongTails.Proofs.BirchCollectionNestedRounds (arrival_fold)
open LongTails.Proofs.BirchCollectionRetainedQuotaHistory
open LongTails.Proofs.BirchCollectionRetainedQuotaStructure
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering

local notation "groupStep" => LongTails.Algorithms.BirchCollectionLocalAsync.advance
local notation "groupCapture" => LongTails.Algorithms.BirchCollectionLocalAsync.capture
local notation "groupComplete" => LongTails.Algorithms.BirchCollectionLocalAsync.complete

lemma query_raw {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (g : ℝ) (s : Round m) (w : Fin m) :
    (groupStep group B g s (.query w)).trace.nextRaw = s.trace.nextRaw + B := by
  change ((groupCapture group B g s w).foldl step s.trace).nextRaw = _
  rw [fold_raw]
  simp [LongTails.Algorithms.BirchCollectionLocalAsync.capture, calls, Event.calls]

lemma reply_raw {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (g : ℝ) (s : Round m) (w : Fin m) :
    (groupStep group B g s (.reply w)).trace.nextRaw = s.trace.nextRaw := by
  cases ht : s.pending w with
  | none => simp [LongTails.Algorithms.BirchCollectionLocalAsync.advance, ht]
  | some t =>
    simp only [LongTails.Algorithms.BirchCollectionLocalAsync.advance, ht]
    change ((groupComplete group B s w t).foldl step s.trace).nextRaw = _
    rw [fold_raw]
    simp [LongTails.Algorithms.BirchCollectionLocalAsync.complete, localComplete, calls, Event.calls, List.map_map, Function.comp_def]

lemma query_fold_raw {m : ℕ} (group : Fin m → Fin m) (B : ℕ) (g : ℝ) (s : Round m)
    (ws : List (Fin m)) :
    (ws.foldl (fun t w => groupStep group B g t (.query w)) s).trace.nextRaw =
      s.trace.nextRaw + B * ws.length := by
  induction ws generalizing s with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons, ih, query_raw, List.length_cons, Nat.mul_succ]
    omega

lemma abort_fold_raw {m : ℕ} (B : ℕ) (s : Round m) (ws : List (Fin m)) :
    (ws.foldl (fun t w =>
      match t.pending w with
      | none => t
      | some j => {t.append (localAbort B j) with pending := Function.update t.pending w none})
      s).trace.nextRaw = s.trace.nextRaw := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons, ih]
    cases h : s.pending w with
    | none => rfl
    | some t =>
      change ((localAbort B t).foldl step s.trace).nextRaw = _
      rw [fold_raw]
      simp [localAbort, calls, Event.calls, List.map_map, Function.comp_def]

lemma collect_cluster_raw {m : ℕ} (layout : Layout m) (s : Round m) (i : Fin m) (base : ℕ) :
    (collectCluster layout s i base).1.trace.nextRaw = s.trace.nextRaw := by
  unfold collectCluster
  generalize (groups layout i) = groups'
  have aux (t : Round m × ℕ) :
      (groups'.foldl (fun (r, l) g =>
        (r.append [.merge (i.val + 1) l (s.head g) base], r.trace.nextState)) t).1.trace.nextRaw =
        t.1.trace.nextRaw := by
    induction groups' generalizing t with
    | nil => rfl
    | cons g gs ih => rw [List.foldl_cons, ih]; rfl
  exact aux (s, base)

lemma collect_all_raw {m : ℕ} (layout : Layout m) (s : State m) (outer : Round m) :
    (collectAll layout s outer).trace.nextRaw = outer.trace.nextRaw := by
  have aux (cs : List (Fin m)) (t : Round m × (Fin m → ℕ)) :
      (cs.foldl (fun (r, heads) i =>
        let (r', head) := collectCluster layout r i (s.cluster i).point
        (r', Function.update heads i head)) t).1.trace.nextRaw = t.1.trace.nextRaw := by
    induction cs generalizing t with
    | nil => rfl
    | cons i cs ih =>
      rw [List.foldl_cons, ih]
      exact collect_cluster_raw layout t.1 i (s.cluster i).point
  exact aux (List.finRange m) (outer, fun i => (s.cluster i).point)

lemma join_heads_raw {m : ℕ} (s : Round m) : (joinHeads s).trace.nextRaw = s.trace.nextRaw := by
  have aux (ws : List (Fin m)) (t : Round m × ℕ) :
      (ws.foldl (fun (r, l) w =>
        (r.append [.merge 0 l (s.head w) s.base], r.trace.nextState)) t).1.trace.nextRaw =
        t.1.trace.nextRaw := by
    induction ws generalizing t with
    | nil => rfl
    | cons w ws ih => rw [List.foldl_cons, ih]; rfl
  exact aux (List.finRange m) (s, s.base)

lemma publish_raw {m : ℕ} (B : ℕ) (s : Round m) : (publish B s).trace.nextRaw = s.trace.nextRaw := by
  rw [publish, join_heads_raw]
  exact abort_fold_raw B s (List.finRange m)

lemma sync_raw {m : ℕ} (layout : Layout m) (B : ℕ) (g : ℝ) (s : State m) (i : Fin m) :
    (synchronize layout B g s i).outer.trace.nextRaw =
      s.outer.trace.nextRaw + B * (workers layout i).length := by
  unfold synchronize
  rw [query_fold_raw]
  change (collectCluster layout (abortCluster layout B s.outer i) i (s.cluster i).point).1.trace.nextRaw +
    B * (workers layout i).length = _
  rw [collect_cluster_raw]
  have h := abort_fold_raw B s.outer (workers layout i)
  change (abortCluster layout B s.outer i).trace.nextRaw = s.outer.trace.nextRaw at h
  rw [h]

lemma start_raw {m : ℕ} (layout : Layout m) (B : ℕ) (g : ℝ) (s : Round m) :
    (start layout B g s.trace s.events).outer.trace.nextRaw = s.trace.nextRaw + B * m := by
  unfold start
  rw [query_fold_raw, List.length_finRange]
  rfl

lemma advance_raw {m B Q : ℕ} (layout : Layout m) (g : ℝ) (s : State m) (w : Fin m)
    (hp : (s.outer.pending w).isSome) :
    (advance layout Q B g s w).outer.trace.nextRaw =
      s.outer.trace.nextRaw + B * ((if s.outer.completed + 1 = Q then 0 else 1) + extra layout Q s w) := by
  let i := layout.cluster (layout.group w)
  let t := groupStep layout.group B g s.outer (.reply w)
  let completed := (s.cluster i).completed + 1
  let u : State m := {outer := t, cluster := Function.update s.cluster i {(s.cluster i) with completed}}
  have ht : t.completed = s.outer.completed + 1 := by
    cases h : s.outer.pending w with
    | none => simp [h] at hp
    | some j => simp [t, LongTails.Algorithms.BirchCollectionLocalAsync.advance, h]
  have hr : u.outer.trace.nextRaw = s.outer.trace.nextRaw := reply_raw layout.group B g s.outer w
  have hw : 0 < (workers layout i).length := by
    apply List.length_pos_of_mem
    exact (LongTails.Proofs.BirchCollectionNestedReset.worker_member layout i w).2 rfl
  change (if t.completed = Q then u else if layout.quota i = some completed then
    synchronize layout B g u i else {u with outer := groupStep layout.group B g t (.query w)}).outer.trace.nextRaw = _
  have he : extra layout Q s w = if s.outer.completed + 1 = Q then 0
      else if layout.quota i = some completed then (workers layout i).length - 1 else 0 := rfl
  rw [ht, he]
  by_cases h : s.outer.completed + 1 = Q
  · simp [h, hr]
  · by_cases hq : layout.quota i = some completed
    · simp only [ite_eq_right h, ite_eq_left hq]
      rw [sync_raw, hr, show 1 + ((workers layout i).length - 1) = (workers layout i).length by omega]
    · simp only [ite_eq_right h, ite_eq_right hq, Nat.add_zero, Nat.mul_one]
      exact (query_raw _ _ _ _ _).trans (congrArg (· + B) hr)

lemma arrival_raw {m S Q B : ℕ} {g : ℝ} (layout : Layout m) (s : State m)
    (order : List (Fin m)) (hs : Data layout s S B g)
    (hQ : s.outer.completed + order.length = Q)
    (hp : s.outer.completed < Q → ∀ w, (s.outer.pending w).isSome)
    (hB : 0 < B) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (order.foldl (advance layout Q B g) s).outer.trace.nextRaw =
      s.outer.trace.nextRaw + B * (order.length - 1 + restartTally layout Q B g s order) := by
  induction order generalizing s with
  | nil => simp [restartTally]
  | cons w order ih =>
    have hlt : s.outer.completed < Q := by simp only [List.length_cons] at hQ; omega
    obtain ⟨hd, _, hcount, _, hp'⟩ := advance_data layout s w hs hlt (hp hlt) hB hg0 hg1
    have he : (advance layout Q B g s w).outer.completed + order.length = Q := by
      rw [hcount]
      simp only [List.length_cons] at hQ
      omega
    rw [List.foldl_cons, ih _ hd he hp', advance_raw layout g s w (hp hlt w)]
    simp only [List.length_cons, restartTally]
    rw [Nat.add_assoc, ← Nat.mul_add]
    have hh : (if s.outer.completed + 1 = Q then 0 else 1) + (order.length - 1) = order.length := by
      simp only [List.length_cons] at hQ
      split <;> omega
    exact congrArg (fun x => s.outer.trace.nextRaw + B * x) (by omega)

lemma phase_raw {m B K : ℕ} (layout : Layout m) {schedule : ℕ → Phase m} {s : Round m}
    (hs : History s schedule B K) (phase : Phase m) (hB : 0 < B) (hp : phase.Valid B) :
    (runRound layout phase.arrivals.length phase.batch (leafGain B phase.batch) s phase.arrivals).trace.nextRaw =
      s.trace.nextRaw + phase.work + phaseWaste layout B s phase := by
  let Q := phase.arrivals.length
  let b := phase.batch
  let g := leafGain B b
  let root := start layout b g s.trace s.events
  let out := phase.arrivals.foldl (advance layout Q b g) root
  have hg := leaf_bounds hB hp
  have hh := hs.last.2
  rw [← hs.count] at hh
  obtain ⟨hd, _, hzero, _, hpend⟩ := start_data layout s.trace s.events hs.represented hs.legal hs.retired
    rfl hs.last.1 hh hp.1 hg.1 (hg.2.trans (by norm_num))
  have hcount : root.outer.completed + phase.arrivals.length = Q := by
    change root.outer.completed = 0 at hzero
    simp [hzero, Q]
  have hraw := arrival_raw layout root phase.arrivals hd hcount (fun _ => hpend)
    hp.1 hg.1 (hg.2.trans (by norm_num))
  have hQ : 0 < Q := hp.2.1
  have hm : 0 < m := Nat.zero_lt_of_lt (phase.arrivals[0]'hp.2.1).isLt
  change (publish b (collectAll layout out (abortPending b out.outer))).trace.nextRaw = _
  rw [publish_raw, collect_all_raw]
  have ha := abort_fold_raw b out.outer (List.finRange m)
  change (abortPending b out.outer).trace.nextRaw = out.outer.trace.nextRaw at ha
  rw [ha]
  change (phase.arrivals.foldl (advance layout Q b g) root).outer.trace.nextRaw =
    s.trace.nextRaw + b * Q + b * (m - 1 + restartTally layout Q b g root phase.arrivals)
  rw [hraw]
  have hroot : root.outer.trace.nextRaw = s.trace.nextRaw + b * m := start_raw _ _ _ _
  rw [hroot]
  let r := restartTally layout Q b g root phase.arrivals
  change s.trace.nextRaw + b * m + b * (Q - 1 + r) = s.trace.nextRaw + b * Q + b * (m - 1 + r)
  rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_assoc, ← Nat.mul_add]
  exact congrArg (fun n => s.trace.nextRaw + b * n) (by omega)


lemma batch_replies_calls (collection : ℕ) (s : TraceState) (ws : List ℕ) :
    calls (LongTails.Algorithms.BirchCollectionBatches.batchReplies collection s ws) = ws.length := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [LongTails.Algorithms.BirchCollectionBatches.batchReplies, calls, List.map_cons,
      List.sum_cons, Event.calls, List.length_cons]
    have h := ih (LongTails.Algorithms.BirchCollectionBatches.receiveNow s collection w)
    change _ = _ at h
    unfold calls at h
    rw [h]
    omega

lemma reset_raw {m B : ℕ} (s : Round m) :
    (s.append (batchAndMarkWithMove s.trace 0 (s.trace.markers.getLast?.getD 0)
      (List.replicate B 0) (1 / 2))).trace.nextRaw = s.trace.nextRaw + B := by
  rw [show (s.append _).trace.nextRaw =
    ((batchAndMarkWithMove s.trace 0 (s.trace.markers.getLast?.getD 0)
      (List.replicate B 0) (1 / 2)).foldl step s.trace).nextRaw from rfl, fold_raw]
  congr 1
  unfold batchAndMarkWithMove
  simp only [calls, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
    Event.calls, zero_add]
  exact (batch_replies_calls _ _ _).trans List.length_replicate

lemma rounds_raw {m B : ℕ} (layout : Layout m) (schedule : ℕ → Phase m) (K : ℕ)
    (hB : 0 < B) (hc : Complete schedule B K) :
    (rounds layout B schedule K).trace.nextRaw =
      (∑ k ∈ range K, volume schedule B k) + waste layout B schedule K := by
  induction K with
  | zero => simp [rounds, Round.initial, waste]
  | succ k ih =>
    let s := rounds layout B schedule k
    have hc' : Complete schedule B k := fun j hj hj' => hc j hj (by omega)
    have hs : History s schedule B k := rounds_history layout schedule hB k hc'
    have hr : (stepRound layout B s k (schedule k)).trace.nextRaw =
        s.trace.nextRaw + volume schedule B k + if k = 0 then 0 else phaseWaste layout B s (schedule k) := by
      by_cases h : k = 0
      · simpa only [stepRound, volume, h, ite_true, Nat.add_zero] using (reset_raw (B := B) s)
      · simpa only [stepRound, volume, h, ite_false] using phase_raw layout hs (schedule k) hB
          (hc k (Nat.pos_of_ne_zero h) (Nat.lt_succ_self _))
    change (stepRound layout B s k (schedule k)).trace.nextRaw = _
    have hi : s.trace.nextRaw = (∑ j ∈ range k, volume schedule B j) + waste layout B schedule k := ih hc'
    rw [hr, hi]
    unfold waste
    rw [sum_range_succ, sum_range_succ]
    dsimp only [s]
    omega

lemma raw_sum {m B K : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hB : 0 < B) :
    (∑ n ∈ range (cut schedule K), ((ordering schedule K).raw (trace gain s.trace) n).card) =
      ∑ k ∈ range K, volume schedule B k := by
  let f := fun n => ((ordering schedule K).raw (trace gain s.trace) n).card
  change (∑ n ∈ range (cut schedule K), f n) = _
  suffices h : ∀ k ≤ K, (∑ n ∈ range (cut schedule k), f n) = ∑ i ∈ range k, volume schedule B i
    from h K le_rfl
  intro k hk
  induction k with
  | zero => simp [cut]
  | succ k ih =>
    have hle := cut_le hc (show k ≤ k + 1 by omega) (show k + 1 ≤ K from hk)
    have hu : range (cut schedule (k + 1)) =
        range (cut schedule k) ∪ Ico (cut schedule k) (cut schedule (k + 1)) := by
      ext n
      simp only [mem_range, mem_union, mem_Ico]
      omega
    have hd : Disjoint (range (cut schedule k)) (Ico (cut schedule k) (cut schedule (k + 1))) := by
      apply disjoint_left.mpr
      intro n h₁ h₂
      exact (not_lt_of_ge (mem_Ico.mp h₂).1) (mem_range.mp h₁)
    rw [hu, sum_union hd, ih (by omega), (block_sums hs hc hB (show k < K by omega)).2, sum_range_succ]

lemma waste_exact {m B K : ℕ} (layout : Layout m) (schedule : ℕ → Phase m)
    (hB : 0 < B) (hK : 0 < K) (hc : Complete schedule B K) :
    let s := rounds layout B schedule K
    let o := ordering schedule K
    let t := trace gain s.trace
    s.trace.nextRaw - ((range o.labels.length).biUnion (o.raw t)).card = waste layout B schedule K := by
  let s := rounds layout B schedule K
  let o := ordering schedule K
  let t := trace gain s.trace
  have hs : History s schedule B K := rounds_history layout schedule hB K hc
  have hr := rawLedger_run _ _ (mapped_legal hs)
  have hd := completedLedger_run _ _ (mapped_legal hs)
  rw [mapped_run hs] at hr hd
  have he := card_biUnion (ordering_raw_disjoint t o K hr hd (ordering_valid hs hc hK))
  have hn : o.labels.length = cut schedule K := by simp [o, ordering]
  change s.trace.nextRaw - ((range o.labels.length).biUnion (o.raw t)).card = _
  rw [he, hn, raw_sum hs hc hB, rounds_raw layout schedule K hB hc]
  omega

lemma volume_upper {m B K : ℕ} {schedule : ℕ → Phase m} (hc : Complete schedule B K) :
    (∑ k ∈ range K, volume schedule B k) ≤ B * K := by
  calc
    _ ≤ ∑ _k ∈ range K, B := by
      apply sum_le_sum
      intro k hk
      by_cases h : k = 0
      · simp [volume, h]
      · rw [volume, ite_eq_right h]
        exact (hc k (Nat.pos_of_ne_zero h) (mem_range.mp hk)).2.2.2
    _ = _ := by simp [Nat.mul_comm]

end LongTails.Proofs.BirchCollectionRetainedQuotaLedger
