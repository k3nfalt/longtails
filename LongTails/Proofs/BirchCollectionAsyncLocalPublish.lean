import LongTails.Proofs.BirchCollectionAsyncLocalTrace

namespace LongTails.Proofs.BirchCollectionAsyncLocalPublish

open Finset
open LongTails.Setups.BirchCollections (TraceState StateRecord run step ValidFrom)
open LongTails.Algorithms.BirchCollectionAsyncLocal
open LongTails.Proofs.BirchCollectionAsyncLocalTrace
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionBatches (RetiredPast)

lemma prefixSet_mono (labels : List ℕ) : Monotone (prefixSet labels) := by
  intro i j hij x hx
  have hh : (labels.take j).take i = labels.take i := by
    rw [List.take_take, Nat.min_eq_left hij]
  exact List.mem_toFinset.mpr (List.mem_of_mem_take (hh.symm ▸ List.mem_toFinset.mp hx))

lemma prefixSet_all (labels : List ℕ) (n : ℕ) :
    prefixSet labels n ⊆ labels.toFinset := by
  intro x hx
  exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx))

lemma prefixSet_append_before (xs ys : List ℕ) (i : ℕ) (hi : i ≤ xs.length) :
    prefixSet (xs ++ ys) i = prefixSet xs i := by
  simp [prefixSet, List.take_append_of_le_length hi]

lemma prefixSet_append_inside (xs ys : List ℕ) (n : ℕ) (hn : xs.length ≤ n) :
    prefixSet (xs ++ ys) n = xs.toFinset ∪ (ys.take (n - xs.length)).toFinset := by
  simp [prefixSet, List.take_append, List.take_of_length_le hn, List.toFinset_append]

lemma savedIndex_append_before (xs ys : List ℕ) (i : ℕ) (hi : i < xs.length) :
    savedIndex (xs ++ ys) i = savedIndex xs i := by
  simp [savedIndex, List.getElem?_append_left hi]

lemma savedIndex_append_repeat (xs : List ℕ) (i a size : ℕ)
    (hl : xs.length ≤ i) (hh : i < xs.length + size) :
    savedIndex (xs ++ List.replicate size a) i = a := by
  have hi : i - xs.length < size := by omega
  simp [savedIndex, List.getElem?_append_right hl, hi]

lemma publish_main {s t : TraceState} {head target rounds G M B : ℕ} {move : ℝ}
    {accepted frontiers : List ℕ} {worker : Worker}
    (hm : Main s head rounds accepted frontiers G M B move)
    (hb : Branch s rounds accepted M B move worker)
    (hM : 0 < M) (hG : 0 < G) (hlen : worker.directions.length = M)
    (hage : (rounds - worker.round) * M < G)
    (he : Extends s t) (hbound : ∀ i ∈ s.markers, i < s.nextState)
    (htarget : target < t.nextState) (hmarks : t.markers = s.markers ++ [target])
    (hh : (t.states target).history = (accepted ++ worker.directions).toFinset) :
    Main t target (rounds + 1) (accepted ++ worker.directions)
      (frontiers ++ List.replicate M (M * worker.round)) G M B move := by
  let ws := worker.directions
  have hx : accepted.length + M = (rounds + 1) * M := by
    rw [hm.count, Nat.add_mul, Nat.one_mul]
  have hlen' : (accepted ++ ws).length = (rounds + 1) * M := by
    rw [List.length_append, show ws.length = M from hlen, hx]
  have hbase : worker.round * M ≤ accepted.length := by
    rw [hm.count]
    exact Nat.mul_le_mul_right M hb.age
  have hsummed : worker.round * M + (rounds - worker.round) * M = accepted.length := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hb.age, hm.count]
  have hsep := disjoint_left.mp hb.separate
  refine ⟨hlen', by simp [hm.frontierCount, hlen], ?_, ?_,
    by simp [hmarks, hm.markerCount], by simp [hmarks], htarget, hh, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hm.unique, hb.chain.nodup, fun d hd q hq h => hsep (List.mem_toFinset.mpr hq)
      (List.mem_toFinset.mpr (h ▸ hd))⟩
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact (hm.labels d hd).trans_le he.directionCount
    · exact (hb.chain.bounded d hd).trans_le he.directionCount
  · intro k hk
    by_cases ho : k ≤ rounds
    · have hidx : k < s.markers.length := by rw [hm.markerCount]; omega
      have hmem : s.markers[k]?.getD 0 ∈ s.markers := by simp [hidx]
      have hle : k * M ≤ accepted.length := by rw [hm.count]; exact Nat.mul_le_mul_right M ho
      rw [hmarks, List.getElem?_append_left hidx, he.oldState _ (hbound _ hmem),
        hm.markers k ho, prefixSet_append_before _ _ _ hle]
    · have heq : k = rounds + 1 := by omega
      have hg : (s.markers ++ [target])[k]?.getD 0 = target := by
        have hi : k = s.markers.length := heq.trans hm.markerCount.symm
        simp [hi]
      rw [hmarks, hg, heq, hh, ← hlen']
      change (accepted ++ ws).toFinset = prefixSet (accepted ++ ws) (accepted ++ ws).length
      unfold prefixSet
      rw [List.take_length]
  · intro n hn
    let label := (accepted ++ ws)[n]'hn
    let fs := frontiers ++ List.replicate M (M * worker.round)
    change AcceptedDirection t (accepted ++ ws) fs B (delayWindow G M) move n label
    by_cases hbefore : n < accepted.length
    · have hd := hm.directions n hbefore
      have hget : label = accepted[n] := List.getElem_append_left hbefore
      have hf : savedIndex fs n = savedIndex frontiers n := by
        apply savedIndex_append_before
        rwa [hm.frontierCount]
      have hdir : t.directions label = s.directions accepted[n] := by
        rw [hget, he.oldDirection _ (hm.labels _ (List.getElem_mem hbefore))]
      have hprior : prefixSet (accepted ++ ws) n = prefixSet accepted n :=
        prefixSet_append_before _ _ _ hbefore.le
      have hincludes : prefixSet (accepted ++ ws) (savedIndex fs n) =
          prefixSet accepted (savedIndex frontiers n) := by
        rw [hf]
        exact prefixSet_append_before _ _ _ (hd.frontierBound.trans hbefore.le)
      refine ⟨hf.symm ▸ hd.frontierBound, hf.symm ▸ hd.delayBound, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hincludes, hdir]
        exact hd.includes
      · rw [hprior, hdir]
        exact hd.prior
      · rw [hdir]
        exact hd.refresh
      · rw [hdir]
        exact hd.movement
      · rw [hdir]
        exact hd.raw
    · have hnl : accepted.length ≤ n := Nat.le_of_not_gt hbefore
      let j := n - accepted.length
      have hj : j < ws.length := by
        change n < (accepted ++ ws).length at hn
        rw [List.length_append] at hn
        omega
      have hget : label = ws[j] := List.getElem_append_right hnl
      have hf : savedIndex fs n = worker.round * M := by
        rw [Nat.mul_comm worker.round M]
        apply savedIndex_append_repeat
        · rwa [hm.frontierCount]
        · rw [hm.frontierCount, hx]
          exact hlen' ▸ hn
      have hdir : t.directions label = s.directions ws[j] := by
        rw [hget, he.oldDirection _ (hb.chain.bounded _ (List.getElem_mem hj))]
      obtain ⟨hd, hr, hm', hraw⟩ := hb.chain.direction j hj
      have hscale : (rounds - worker.round) ≤ (G - 1) / M :=
        (Nat.le_div_iff_mul_le hM).2 (by omega)
      have hscaled := Nat.mul_le_mul_right M hscale
      have hj' : j < M := by simpa only [ws, hlen] using hj
      have hdelay : n - worker.round * M ≤ delayWindow G M := by
        unfold delayWindow
        dsimp only [j] at hj'
        omega
      refine ⟨by rw [hf]; exact hbase.trans hnl, hf.symm ▸ hdelay, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hf, prefixSet_append_before _ _ _ hbase, hdir, hd, hb.baseHistory]
        exact subset_union_left
      · rw [hdir, hd, hb.baseHistory, prefixSet_append_inside _ _ _ hnl]
        exact union_subset_union (prefixSet_all _ _) le_rfl
      · rw [hdir]
        exact hr
      · rw [hdir]
        exact hm'
      · rw [hdir]
        exact hraw

lemma restart_worker {m G M B : ℕ} {move : ℝ} (s t : Controller m) (w : Fin m)
    (hs : Data s G M B move)
    (hm : Main t.trace t.main t.rounds t.accepted t.frontiers G M B move)
    (he : Extends s.trace t.trace) (hround : s.rounds ≤ t.rounds)
    (haccepted : ∃ added, t.accepted = s.accepted ++ added ∧
      (added = [] ∨ added = (s.worker w).directions))
    (hcollectionCount : t.trace.nextCollection = s.trace.nextCollection)
    (hcollections : t.trace.collections = s.trace.collections)
    (hrawCount : t.trace.nextRaw = s.trace.nextRaw) (hraw : t.trace.raws = s.trace.raws)
    (hretired : t.trace.retired = s.trace.retired)
    (hr : run t.events = t.trace) (hl : ValidFrom (m + 1) {} t.events) (hret : RetiredPast t.trace) :
    Data (restart s t w) G M B move := by
  let reset : Worker := {base := t.main, head := t.main, round := t.rounds}
  let out := restart s t w
  change Data out G M B move
  have hs' (v : Fin m) (hv : v ≠ w) : out.worker v = s.worker v := Function.update_of_ne hv _ _
  have hw' : out.worker w = reset := Function.update_self ..
  have hpending (v : Fin m) (j : LongTails.Algorithms.BirchCollectionDelayed.Ticket)
      (hj : (out.worker v).pending = some j) : v ≠ w ∧ (s.worker v).pending = some j := by
    by_cases h : v = w
    · subst v
      rw [hw'] at hj
      simp [reset] at hj
    · rw [hs' v h] at hj
      exact ⟨h, hj⟩
  obtain ⟨added, ha, hadd⟩ := haccepted
  refine ⟨hr, hl, hret, hm, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v = w
    · subst v
      rw [hw']
      refine ⟨le_rfl, ?_, chain_initial _ _ _ _ hm.headBound, by simp [reset]⟩
      change (t.trace.states t.main).history = prefixSet t.accepted (t.rounds * M)
      rw [hm.headHistory, ← hm.count]
      simp [prefixSet]
    · rw [hs' v hv]
      have hb := hs.branch v
      refine ⟨hb.age.trans hround, ?_, hb.chain.extend he, ?_⟩
      · change (t.trace.states (s.worker v).base).history = prefixSet t.accepted ((s.worker v).round * M)
        rw [he.oldState _ hb.chain.baseBound, ha, prefixSet_append_before]
        · exact hb.baseHistory
        · rw [hs.main.count]
          exact Nat.mul_le_mul_right M hb.age
      · change Disjoint (s.worker v).directions.toFinset t.accepted.toFinset
        rw [ha, List.toFinset_append, disjoint_union_right]
        refine ⟨hb.separate, ?_⟩
        rcases hadd with rfl | rfl
        · simp
        · exact hs.disjoint v w hv
  · intro v u hne
    by_cases hv : v = w
    · subst v
      rw [hw']
      simp [reset]
    · rw [hs' v hv]
      by_cases hu : u = w
      · subst u
        rw [hw']
        simp [reset]
      · rw [hs' u hu]
        exact hs.disjoint v u hne
  · intro v j hj
    obtain ⟨hv, hp⟩ := hpending v j hj
    have ht := hs.ticket v j hp
    rw [hs' v hv]
    refine ⟨?_, ?_, ?_⟩
    · change j.collection < t.trace.nextCollection
      rw [hcollectionCount]
      exact ht.collection
    · change t.trace.collections j.collection = _
      rw [hcollections]
      exact ht.header
    · intro q hq
      change q < t.trace.nextRaw ∧ q ∉ t.trace.retired ∧ t.trace.raws q = _
      rw [hrawCount, hretired, hraw]
      exact ht.raw q hq
  · intro v u j k hv hu hne
    exact hs.distinct v u j k (hpending v j hv).2 (hpending u k hu).2 hne

lemma data_submit {m K G M B : ℕ} {move : ℝ} (s : Controller m) (w : Fin m)
    (hs : Data s G M B move) (hM : 0 < M) (hG : 0 < G) (hw : Enabled K M s (.submit w)) :
    Data (advance B G M move s (.submit w)) G M B move := by
  let worker := s.worker w
  by_cases ha : accepts G M s w
  · let merge := LongTails.Setups.BirchCollections.Event.merge 0 s.main worker.head worker.base
    let mark := LongTails.Setups.BirchCollections.Event.mark s.trace.nextState
    let es := [merge, mark]
    let t : Controller m := {s.append es with
      main := s.trace.nextState
      rounds := s.rounds + 1
      accepted := s.accepted ++ worker.directions
      frontiers := s.frontiers ++ List.replicate M (M * worker.round)}
    have hb := hs.branch w
    have hsub : (s.trace.states worker.base).history ⊆ (s.trace.states s.main).history := by
      rw [hb.baseHistory, hs.main.headHistory]
      exact prefixSet_all _ _
    have hsep : Disjoint worker.directions.toFinset (s.trace.states s.main).history := by
      rw [hs.main.headHistory]
      exact hb.separate
    obtain ⟨hi, hu⟩ := hb.chain.merge_history hsub hsep
    have he : merge.Valid (m + 1) s.trace :=
      ⟨Nat.zero_lt_succ _, hs.main.headBound, hb.chain.headBound, hb.chain.baseBound, hi⟩
    have hv : ValidFrom (m + 1) s.trace es :=
      merge_mark_valid _ _ _ _ _ _ he hs.main.headMarker
    have hext : Extends s.trace t.trace := extends_fold _ es
    obtain ⟨hr, hl, hret⟩ := append_legal hs es hv
    have hd : MergeData s.trace (step s.trace merge) 0 s.main worker.head := merge_data _ _ _ _ _
    have hnew : (t.trace.states s.trace.nextState).history = (s.accepted ++ worker.directions).toFinset := by
      change ((step s.trace merge).states s.trace.nextState).history = _
      rw [hd.newState]
      change (s.trace.states s.main).history ∪ (s.trace.states worker.head).history = _
      rw [hu, hs.main.headHistory, List.toFinset_append]
    have hm := publish_main hs.main hb hM hG hw.2.1 ha hext (marker_bounds hs)
      (Nat.lt_succ_self _) (show t.trace.markers = s.trace.markers ++ [s.trace.nextState] from rfl) hnew
    have h := restart_worker s t w hs hm hext (Nat.le_succ _)
      ⟨worker.directions, rfl, Or.inr rfl⟩ rfl rfl rfl rfl rfl hr hl hret
    simpa only [advance, ite_eq_left ha, worker, t, es, merge, mark] using h
  · have h := restart_worker s s w hs hs.main (extends_refl _) le_rfl
      ⟨[], by simp, Or.inl rfl⟩ rfl rfl rfl rfl rfl hs.represented hs.legal hs.retired
    simpa only [advance, ite_eq_right ha] using h

lemma data_run {m K G M B : ℕ} (move : ℝ) (events : List (Event m))
    (hG : 0 < G) (hM : 0 < M) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom K B G M move {} events) :
    Data (controller B G M move events) G M B move := by
  have aux (s : Controller m) (es : List (Event m)) (hs : Data s G M B move)
      (he : LegalFrom K B G M move s es) :
      Data (es.foldl (advance B G M move) s) G M B move := by
    induction es generalizing s with
    | nil => exact hs
    | cons e es ih =>
      apply ih _ _ he.2
      cases e with
      | query w => exact data_query s w hs hB hm0 hm1
      | localReply w => exact data_localReply s w hs he.1
      | submit w => exact data_submit s w hs hM hG he.1
  exact aux {} events (initial_data m G M B move) he

end LongTails.Proofs.BirchCollectionAsyncLocalPublish
