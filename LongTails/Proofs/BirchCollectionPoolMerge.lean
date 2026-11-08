import LongTails.Proofs.BirchCollectionPoolTrace
import LongTails.Proofs.BirchCollectionPoolCounts

namespace LongTails.Proofs.BirchCollectionPoolMerge

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Proofs.BirchCollectionPoolTrace
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionAsyncLocalPublish (prefixSet_all)

local notation "discardPacket" => LongTails.Algorithms.BirchCollectionWorkerPools.discard

lemma discard_extends {m : ℕ} (B : ℕ) (s : Pool m) (w : Fin m) :
    Extends s.trace (discardPacket B s w).trace := by
  cases h : (s.worker w).pending with
  | none => simpa only [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h] using extends_refl s.trace
  | some t =>
    simp only [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h]
    exact extends_fold _ _

lemma discard_many {m B lower upper window : ℕ} {move : ℝ}
    (s : Pool m) (ws : List (Fin m)) (hs : Data s B lower upper window move) :
    let t := ws.foldl (discardPacket B) s
    Data t B lower upper window move ∧ Extends s.trace t.trace := by
  induction ws generalizing s with
  | nil => exact ⟨hs, extends_refl _⟩
  | cons w ws ih =>
    obtain ⟨ht, he⟩ := ih _ (data_discard s w hs)
    exact ⟨ht, (discard_extends B s w).trans he⟩

lemma mem_selected {m : ℕ} (s : Pool m) (seen : List (Fin m)) (d : ℕ) :
    d ∈ (selectedLabels s seen).toFinset ↔
      ∃ w ∈ seen, d ∈ (s.worker w).privateLabels.toFinset := by
  simp [selectedLabels, List.mem_flatMap]

def joinOne {m : ℕ} (s : Pool m) (t : Pool m × ℕ) (w : Fin m) : Pool m × ℕ :=
  (t.1.append [.merge 0 t.2 (s.worker w).head (s.worker w).base], t.1.trace.nextState)

structure Joined {m : ℕ} (s : Pool m) (t : Pool m × ℕ) (seen : List (Fin m))
    (B lower upper window : ℕ) (move : ℝ) : Prop where
  data : Data t.1 B lower upper window move
  extendsTrace : Extends s.trace t.1.trace
  head : t.2 < t.1.trace.nextState
  history : (t.1.trace.states t.2).history =
    s.accepted.toFinset ∪ (selectedLabels s seen).toFinset

lemma join_one {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (t : Pool m × ℕ)
    (seen : List (Fin m)) (w : Fin m) (hs : Data s B lower upper window move)
    (ht : Joined s t seen B lower upper window move) (hw : w ∉ seen) :
    Joined s (joinOne s t w) (seen ++ [w]) B lower upper window move := by
  let e := Event.merge 0 t.2 (s.worker w).head (s.worker w).base
  let out := joinOne s t w
  have hb := hs.branch w
  have hc := hb.chain.extend ht.extendsTrace
  have hbase : (t.1.trace.states (s.worker w).base).history ⊆ (t.1.trace.states t.2).history := by
    rw [ht.extendsTrace.oldState _ hb.chain.baseBound, hb.baseHistory, ht.history]
    exact (prefixSet_all _ _).trans subset_union_left
  have hsep : Disjoint (s.worker w).privateLabels.toFinset (t.1.trace.states t.2).history := by
    rw [ht.history, disjoint_union_right]
    refine ⟨hb.separate, disjoint_left.mpr ?_⟩
    intro d hd h
    obtain ⟨v, hv, hdv⟩ := (mem_selected s seen d).1 h
    have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
    exact disjoint_left.mp (hs.disjoint w v hne) hd hdv
  obtain ⟨hi, hu⟩ := hc.merge_history hbase hsep
  have he : e.Valid (m + 1) t.1.trace := ⟨Nat.zero_lt_succ _, ht.head, hc.headBound, hc.baseBound, hi⟩
  change Joined s out (seen ++ [w]) B lower upper window move
  refine ⟨data_merge t.1 _ _ _ _ ht.data he, ht.extendsTrace.trans (extends_step _ e),
    Nat.lt_succ_self _, ?_⟩
  change ((step t.1.trace e).states t.1.trace.nextState).history = _
  rw [(merge_data t.1.trace 0 t.2 (s.worker w).head (s.worker w).base).newState]
  change (t.1.trace.states t.2).history ∪ (t.1.trace.states (s.worker w).head).history = _
  have hselected : selectedLabels s (seen ++ [w]) = selectedLabels s seen ++ (s.worker w).privateLabels := by
    simp [selectedLabels]
  rw [hu, ht.history, hselected, List.toFinset_append, union_assoc]

lemma join_fold {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (t : Pool m × ℕ)
    (seen ws : List (Fin m)) (hs : Data s B lower upper window move)
    (ht : Joined s t seen B lower upper window move)
    (hn : ws.Nodup) (hsep : ∀ w ∈ ws, w ∉ seen) :
    Joined s (ws.foldl (joinOne s) t) (seen ++ ws) B lower upper window move := by
  induction ws generalizing t seen with
  | nil => simpa only [List.append_nil, List.foldl_nil] using ht
  | cons w ws ih =>
    have ht' := join_one s t seen w hs ht (hsep w (by simp))
    have he (v : Fin m) (hv : v ∈ ws) : v ∉ seen ++ [w] := by
      intro h
      rcases List.mem_append.mp h with h | h
      · exact hsep v (List.mem_cons_of_mem _ hv) h
      · have he : v = w := by simpa using h
        exact (List.nodup_cons.mp hn).1 (he ▸ hv)
    have h := ih (joinOne s t w) (seen ++ [w]) ht' (List.nodup_cons.mp hn).2 he
    simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using h

lemma selected_disjoint {m B lower upper window : ℕ} {move : ℝ}
    (s : Pool m) (ws : List (Fin m)) (hs : Data s B lower upper window move) :
    Disjoint (selectedLabels s ws).toFinset s.accepted.toFinset := by
  apply disjoint_left.mpr
  intro d hd ha
  obtain ⟨w, _, hdw⟩ := (mem_selected s ws d).1 hd
  exact disjoint_left.mp (hs.branch w).separate hdw ha

lemma selected_nodup {m B lower upper window : ℕ} {move : ℝ}
    (s : Pool m) (ws : List (Fin m)) (hs : Data s B lower upper window move) (hn : ws.Nodup) :
    (selectedLabels s ws).Nodup := by
  induction ws with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    change ((s.worker w).privateLabels ++ selectedLabels s ws).Nodup
    rw [List.nodup_append]
    refine ⟨(hs.branch w).chain.nodup, ih (List.nodup_cons.mp hn).2, ?_⟩
    intro d hd q hq he
    subst q
    obtain ⟨v, hv, hdv⟩ := (mem_selected s ws d).1 (List.mem_toFinset.mpr hq)
    have hne : w ≠ v := fun h => (List.nodup_cons.mp hn).1 (h.symm ▸ hv)
    exact disjoint_left.mp (hs.disjoint w v hne) (List.mem_toFinset.mpr hd) hdv

end LongTails.Proofs.BirchCollectionPoolMerge
