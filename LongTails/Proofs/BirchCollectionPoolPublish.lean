import LongTails.Proofs.BirchCollectionPoolOrder
import LongTails.Proofs.BirchCollectionLocalRounds

namespace LongTails.Proofs.BirchCollectionPoolPublish

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Proofs.BirchCollectionPoolTrace
open LongTails.Proofs.BirchCollectionPoolMerge
open LongTails.Proofs.BirchCollectionPoolOrder
open LongTails.Proofs.BirchCollectionPoolCounts (reset_workers)
open LongTails.Proofs.BirchCollectionAsyncLocalTrace (prefixSet)
open LongTails.Proofs.BirchCollectionAsyncLocalPublish (prefixSet_append_before)
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionBatches (RetiredPast)

local notation "discardPacket" => LongTails.Algorithms.BirchCollectionWorkerPools.discard

def shape (w : Worker) : Worker := {w with pending := none}

lemma discard_shape {m : ℕ} (B : ℕ) (s : Pool m) (w v : Fin m) :
    shape ((discardPacket B s w).worker v) = shape (s.worker v) := by
  cases h : (s.worker w).pending with
  | none => simp [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h]
  | some j =>
    by_cases hv : v = w
    · subst v
      simp [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h, Pool.put, Pool.append, shape]
    · simp [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h, Pool.put, Pool.append, hv]

lemma discard_many_shape {m : ℕ} (B : ℕ) (s : Pool m) (ws : List (Fin m)) (v : Fin m) :
    shape (((ws.foldl (discardPacket B) s).worker v)) = shape (s.worker v) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih (discardPacket B s w)).trans (discard_shape B s w v)

lemma discard_and_merge_frame {m : ℕ} (B : ℕ) (s : Pool m) (ws : List (Fin m)) :
    let closed := ws.foldl (discardPacket B) s
    let joined := ws.foldl (joinOne s) (closed, s.main)
    joined.1.trace.markers = s.trace.markers ∧
      ∀ w, shape (joined.1.worker w) = shape (s.worker w) := by
  let closed := ws.foldl (discardPacket B) s
  let joined := ws.foldl (joinOne s) (closed, s.main)
  have hclose (s : Pool m) (ls : List (Fin m)) :
      (ls.foldl (discardPacket B) s).trace.markers = s.trace.markers := by
    induction ls generalizing s with
    | nil => rfl
    | cons w ls ih =>
      refine (ih (discardPacket B s w)).trans ?_
      cases h : (s.worker w).pending with
      | none => simp [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h]
      | some t =>
        simp only [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h, Pool.put, Pool.append]
        rw [LongTails.Proofs.BirchCollectionLocalRounds.fold_marks]
        simp [LongTails.Proofs.BirchCollectionLocalRounds.marks,
          LongTails.Algorithms.BirchCollectionLocal.localAbort, List.filterMap_map]
  have hmerge (t : Pool m × ℕ) (ls : List (Fin m)) :
      (ls.foldl (joinOne s) t).1.trace.markers = t.1.trace.markers := by
    induction ls generalizing t with
    | nil => rfl
    | cons w ls ih => exact ih (joinOne s t w)
  change joined.1.trace.markers = _ ∧ _
  refine ⟨(hmerge (closed, s.main) ws).trans (hclose s ws), ?_⟩
  intro w
  have hworker : joined.1.worker = closed.worker :=
    LongTails.Proofs.BirchCollectionPoolCounts.merge_fold_worker s (closed, s.main) ws
  change shape (joined.1.worker w) = _
  rw [hworker]
  exact discard_many_shape B s ws w

lemma reset_data {m B lower upper window : ℕ} {move : ℝ}
    (s before out : Pool m) (ws : List (Fin m))
    (hs : Data s B lower upper window move)
    (hb : Data before B lower upper window move)
    (hl : Log out.trace out.main out.accepted out.cuts out.frontiers B lower upper window move)
    (he : Extends s.trace out.trace)
    (hbefore : ∀ w, shape (before.worker w) = shape (s.worker w))
    (hw : out.worker = before.worker)
    (ha : ∃ extra, out.accepted = s.accepted ++ extra ∧
      extra.toFinset ⊆ (selectedLabels s ws).toFinset)
    (hcollectionCount : out.trace.nextCollection = before.trace.nextCollection)
    (hcollections : out.trace.collections = before.trace.collections)
    (hrawCount : out.trace.nextRaw = before.trace.nextRaw)
    (hraw : out.trace.raws = before.trace.raws) (hretired : out.trace.retired = before.trace.retired)
    (hrun : run out.events = out.trace) (hvalid : ValidFrom (m + 1) {} out.events)
    (hret : RetiredPast out.trace) :
    let root : Worker := {base := out.main, head := out.main, frontier := out.accepted.length}
    Data (ws.foldl (fun t w => t.put w root) out) B lower upper window move := by
  let root : Worker := {base := out.main, head := out.main, frontier := out.accepted.length}
  let t := ws.foldl (fun t w => t.put w root) out
  have hframe (u : Pool m) (xs : List (Fin m)) :
      let t := xs.foldl (fun t w => t.put w root) u
      t.trace = u.trace ∧ t.events = u.events ∧ t.main = u.main ∧
        t.accepted = u.accepted ∧ t.cuts = u.cuts ∧ t.frontiers = u.frontiers := by
    induction xs generalizing u with
    | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | cons w xs ih => exact ih (u.put w root)
  obtain ⟨hf₁, hf₂, hf₃, hf₄, hf₅, hf₆⟩ := hframe out ws
  have hs' (w : Fin m) (h : w ∉ ws) : t.worker w = before.worker w := by
    change ((ws.foldl (fun t w => t.put w root) out).worker w) = _
    rw [reset_workers, ite_eq_right h, hw]
  have hr' (w : Fin m) (h : w ∈ ws) : t.worker w = root := by
    change ((ws.foldl (fun t w => t.put w root) out).worker w) = _
    rw [reset_workers, ite_eq_left h]
  have hh (w : Fin m) (h : w ∉ ws) :
      (t.worker w).base = (s.worker w).base ∧
      (t.worker w).head = (s.worker w).head ∧
      (t.worker w).frontier = (s.worker w).frontier ∧
      (t.worker w).privateLabels = (s.worker w).privateLabels := by
    rw [hs' w h]
    exact ⟨by simpa only [shape] using congrArg Worker.base (hbefore w),
      by simpa only [shape] using congrArg Worker.head (hbefore w),
      by simpa only [shape] using congrArg Worker.frontier (hbefore w),
      by simpa only [shape] using congrArg Worker.privateLabels (hbefore w)⟩
  obtain ⟨extra, ha', hextra⟩ := ha
  change Data t B lower upper window move
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf₁, hf₂]
    exact hrun
  · rw [hf₂]
    exact hvalid
  · rw [hf₁]
    exact hret
  · rw [hf₁, hf₃, hf₄, hf₅, hf₆]
    exact hl
  · intro w
    rw [hf₁, hf₄]
    by_cases hm : w ∈ ws
    · rw [hr' w hm]
      refine ⟨le_rfl, ?_, chain_initial _ _ _ _ hl.headBound, by simp [root]⟩
      change (out.trace.states out.main).history = prefixSet out.accepted out.accepted.length
      rw [hl.headHistory]
      simp [prefixSet]
    · obtain ⟨hbase, hhead, hfront, hlabel⟩ := hh w hm
      have hp := hs.branch w
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfront, ha', List.length_append]
        exact hp.frontierBound.trans (Nat.le_add_right _ _)
      · rw [hbase, hfront, he.oldState _ hp.chain.baseBound, ha',
          prefixSet_append_before _ _ _ hp.frontierBound]
        exact hp.baseHistory
      · rw [hbase, hhead, hlabel]
        exact hp.chain.extend he
      · rw [hlabel, ha', List.toFinset_append, disjoint_union_right]
        refine ⟨hp.separate, disjoint_left.mpr ?_⟩
        intro d hd hnew
        obtain ⟨v, hv, hvd⟩ := (mem_selected s ws d).1 (hextra hnew)
        exact disjoint_left.mp (hs.disjoint w v (fun eq => hm (eq.symm ▸ hv))) hd hvd
  · intro w v hne
    by_cases hw' : w ∈ ws
    · rw [hr' w hw']
      simp [root]
    · rw [(hh w hw').2.2.2]
      by_cases hv : v ∈ ws
      · rw [hr' v hv]
        simp [root]
      · rw [(hh v hv).2.2.2]
        exact hs.disjoint w v hne
  · intro w j hj
    have hw' : w ∉ ws := by
      intro h
      rw [hr' w h] at hj
      simp [root] at hj
    rw [hf₁, hs' w hw']
    rw [hs' w hw'] at hj
    have h := hb.ticket w j hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hcollectionCount]
      exact h.collection
    · rw [hcollections]
      exact h.header
    · intro q hq
      rw [hrawCount, hraw, hretired]
      exact h.raw q hq
  · intro w v j k hw' hv hne
    have hn (u : Fin m) (a : Ticket) (h : (t.worker u).pending = some a) : u ∉ ws := by
      intro hu
      rw [hr' u hu] at h
      simp [root] at h
    exact hb.distinct w v j k ((hs' w (hn w j hw')) ▸ hw') ((hs' v (hn v k hv)) ▸ hv) hne

lemma data_publish {m B lower upper window : ℕ} {move : ℝ}
    (s : Pool m) (ws : List (Fin m)) (hs : Data s B lower upper window move)
    (hn : ws.Nodup)
    (hlo : 0 < (selectedLabels s ws).length → lower ≤ (selectedLabels s ws).length)
    (hhi : (selectedLabels s ws).length ≤ upper)
    (hwindow : ∀ w ∈ ws, age s w + (selectedLabels s ws).length - 1 ≤ window) :
    Data (publish B s ws) B lower upper window move := by
  let closed := ws.foldl (discardPacket B) s
  obtain ⟨hc, hx⟩ := discard_many s ws hs
  change Data closed B lower upper window move at hc
  change Extends s.trace closed.trace at hx
  by_cases hz : (selectedLabels s ws).isEmpty
  · have hacc : closed.accepted = s.accepted :=
      (LongTails.Proofs.BirchCollectionPoolCounts.close_many_profile B s ws).1
    have hp : publishState B s ws = closed := by simp only [publishState, ite_eq_left hz, closed]
    unfold publish
    rw [hp]
    exact reset_data s closed closed ws hs hc hc.main hx (discard_many_shape B s ws) rfl
      ⟨[], by simpa using hacc, by simp⟩
      rfl rfl rfl rfl rfl hc.represented hc.legal hc.retired
  · let pair := ws.foldl (joinOne s) (closed, s.main)
    let t := pair.1
    let target := pair.2
    let e := Event.mark target
    let out : Pool m := { t.append [e] with
      main := target
      accepted := s.accepted ++ selectedLabels s ws
      cuts := s.cuts ++ [s.accepted.length + (selectedLabels s ws).length]
      frontiers := s.frontiers ++ selectedFrontiers s ws}
    have hstate : publishState B s ws = out := by
      simp only [publishState, ite_eq_right hz, out, t, target, pair, closed, e]
      rfl
    have hi : Joined s (closed, s.main) [] B lower upper window move := by
      refine ⟨hc, hx, hs.main.headBound.trans_le hx.stateCount, ?_⟩
      change (closed.trace.states s.main).history = _
      rw [hx.oldState _ hs.main.headBound, hs.main.headHistory]
      simp [selectedLabels]
    have hjoin : Joined s pair ws B lower upper window move := by
      simpa only [List.nil_append] using join_fold s (closed, s.main) [] ws hs hi hn (by simp)
    obtain ⟨hmarks, hshape⟩ := discard_and_merge_frame B s ws
    have hmark : e.Valid (m + 1) t.trace := by
      refine ⟨hjoin.head, ?_⟩
      change t.trace.markers = s.trace.markers at hmarks
      rw [hmarks, hs.main.headMarker, hjoin.extendsTrace.oldState _ hs.main.headBound,
        hs.main.headHistory, show (t.trace.states target).history = _ from hjoin.history]
      exact subset_union_left
    obtain ⟨hr, hv, hret⟩ := append_legal hjoin.data [e] ⟨hmark, trivial⟩
    have hpos : 0 < (selectedLabels s ws).length := by
      cases h : selectedLabels s ws with
      | nil => simp [h] at hz
      | cons d ds => simp
    have hx' : Extends s.trace out.trace := hjoin.extendsTrace.trans (extends_step t.trace e)
    have hmarkOut : out.trace.markers = s.trace.markers ++ [target] := by
      change t.trace.markers ++ [target] = _
      rw [hmarks]
    have hhistory : (out.trace.states target).history = out.accepted.toFinset := by
      change (t.trace.states target).history = (s.accepted ++ selectedLabels s ws).toFinset
      rw [show (t.trace.states target).history = _ from hjoin.history, List.toFinset_append]
    have hlog : Log out.trace out.main out.accepted out.cuts out.frontiers B lower upper window move :=
      log_append s ws hs hn hpos (hlo hpos) hhi hwindow _ _ hx' hjoin.head hmarkOut hhistory
    unfold publish
    rw [hstate]
    exact reset_data s t out ws hs hjoin.data hlog hx' hshape rfl
      ⟨selectedLabels s ws, rfl, le_rfl⟩ rfl rfl rfl rfl rfl hr hv hret

end LongTails.Proofs.BirchCollectionPoolPublish
