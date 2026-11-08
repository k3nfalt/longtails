import LongTails.Proofs.BirchCollectionPoolMerge

namespace LongTails.Proofs.BirchCollectionPoolOrder

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Proofs.BirchCollectionPoolTrace
open LongTails.Proofs.BirchCollectionPoolMerge
open LongTails.Proofs.BirchCollectionAsyncLocalTrace (AcceptedDirection prefixSet savedIndex)
open LongTails.Proofs.BirchCollectionAsyncLocalPublish
  (prefixSet_append_before prefixSet_append_inside prefixSet_all savedIndex_append_before)
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionPublication

lemma frontier_length {m : ℕ} (s : Pool m) (ws : List (Fin m)) :
    (selectedFrontiers s ws).length = (selectedLabels s ws).length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change (List.replicate (s.worker w).privateLabels.length (s.worker w).frontier ++
      selectedFrontiers s ws).length = ((s.worker w).privateLabels ++ selectedLabels s ws).length
    simp only [List.length_append, List.length_replicate, ih]

lemma selected_entry {m : ℕ} (s : Pool m) (ws : List (Fin m)) (n : ℕ)
    (hn : n < (selectedLabels s ws).length) :
    ∃ w ∈ ws, ∃ j, ∃ hj : j < (s.worker w).privateLabels.length,
      (selectedLabels s ws)[n] = (s.worker w).privateLabels[j] ∧
      savedIndex (selectedFrontiers s ws) n = (s.worker w).frontier ∧
      prefixSet (s.worker w).privateLabels j ⊆ prefixSet (selectedLabels s ws) n := by
  induction ws generalizing n with
  | nil => simp [selectedLabels] at hn
  | cons w ws ih =>
    let x := (s.worker w).privateLabels
    let xs := selectedLabels s ws
    let f := List.replicate x.length (s.worker w).frontier
    let fs := selectedFrontiers s ws
    change n < (x ++ xs).length at hn
    change ∃ v ∈ w :: ws, ∃ j, ∃ hj : j < (s.worker v).privateLabels.length,
      (x ++ xs)[n] = (s.worker v).privateLabels[j] ∧
      savedIndex (f ++ fs) n = (s.worker v).frontier ∧
      prefixSet (s.worker v).privateLabels j ⊆ prefixSet (x ++ xs) n
    by_cases h : n < x.length
    · refine ⟨w, by simp, n, h, List.getElem_append_left h, ?_, ?_⟩
      · have hf : n < f.length := by simp [f, h]
        rw [savedIndex_append_before _ _ _ hf]
        simp [savedIndex, f, h]
      · rw [prefixSet_append_before _ _ _ h.le]
    · have hx := Nat.le_of_not_gt h
      let j := n - x.length
      have hj : j < xs.length := by rw [List.length_append] at hn; omega
      obtain ⟨v, hv, k, hk, hget, hf, hp⟩ := ih j hj
      have he : n - f.length = j := by simp [f, j]
      have hfront : f.length ≤ n := by simpa [f] using hx
      refine ⟨v, List.mem_cons_of_mem _ hv, k, hk, ?_, ?_, ?_⟩
      · exact (List.getElem_append_right hx).trans hget
      · unfold savedIndex at *
        rw [List.getElem?_append_right hfront, he]
        exact hf
      · rw [prefixSet_append_inside _ _ _ hx]
        exact hp.trans subset_union_right

lemma new_directions {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (ws : List (Fin m))
    (hs : Data s B lower upper window move)
    (hwindow : ∀ w ∈ ws, age s w + (selectedLabels s ws).length - 1 ≤ window)
    (t : TraceState) (he : Extends s.trace t) :
    ∀ n (hn : n < (s.accepted ++ selectedLabels s ws).length), s.accepted.length ≤ n →
      AcceptedDirection t (s.accepted ++ selectedLabels s ws)
        (s.frontiers ++ selectedFrontiers s ws) B window move n
        ((s.accepted ++ selectedLabels s ws)[n]'hn) := by
  intro n hn ha
  let j := n - s.accepted.length
  have hj : j < (selectedLabels s ws).length := by
    rw [List.length_append] at hn
    omega
  obtain ⟨w, hw, k, hk, hget, hfront, hp⟩ := selected_entry s ws j hj
  have hb := hs.branch w
  have hlabel : (s.accepted ++ selectedLabels s ws)[n]'hn = (s.worker w).privateLabels[k] :=
    (List.getElem_append_right ha).trans hget
  have hfront' : savedIndex (s.frontiers ++ selectedFrontiers s ws) n = (s.worker w).frontier := by
    unfold savedIndex at *
    rw [List.getElem?_append_right (hs.main.frontierCount.symm ▸ ha), hs.main.frontierCount]
    exact hfront
  have hdir : t.directions (s.worker w).privateLabels[k] =
      s.trace.directions (s.worker w).privateLabels[k] :=
    he.oldDirection _ (hb.chain.bounded _ (List.getElem_mem hk))
  obtain ⟨hd, hr, hm, hB⟩ := hb.chain.direction k hk
  have hw' := hwindow w hw
  unfold age at hw'
  have hb' := hb.frontierBound
  refine ⟨by rw [hfront']; exact hb'.trans ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfront']
    dsimp only [j] at hj
    omega
  · rw [hlabel, hfront', prefixSet_append_before _ _ _ hb', hdir, hd, hb.baseHistory]
    exact subset_union_left
  · rw [hlabel, hdir, hd, hb.baseHistory, prefixSet_append_inside _ _ _ ha]
    exact union_subset_union (prefixSet_all _ _) hp
  · rwa [hlabel, hdir]
  · rwa [hlabel, hdir]
  · rwa [hlabel, hdir]

lemma old_directions {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (ws : List (Fin m))
    (hs : Data s B lower upper window move) (t : TraceState) (he : Extends s.trace t) :
    ∀ n (hn : n < (s.accepted ++ selectedLabels s ws).length), n < s.accepted.length →
      AcceptedDirection t (s.accepted ++ selectedLabels s ws)
        (s.frontiers ++ selectedFrontiers s ws) B window move n
        ((s.accepted ++ selectedLabels s ws)[n]'hn) := by
  intro n hn h
  have hd := hs.main.directions n h
  have hget : (s.accepted ++ selectedLabels s ws)[n]'hn = s.accepted[n] :=
    List.getElem_append_left h
  have hf : savedIndex (s.frontiers ++ selectedFrontiers s ws) n = savedIndex s.frontiers n := by
    apply savedIndex_append_before
    rwa [hs.main.frontierCount]
  have hdir : t.directions s.accepted[n] = s.trace.directions s.accepted[n] :=
    he.oldDirection _ (hs.main.labels _ (List.getElem_mem h))
  have hincludes : prefixSet (s.accepted ++ selectedLabels s ws)
      (savedIndex (s.frontiers ++ selectedFrontiers s ws) n) =
        prefixSet s.accepted (savedIndex s.frontiers n) := by
    rw [hf, prefixSet_append_before _ _ _ (hd.frontierBound.trans h.le)]
  refine ⟨hf.symm ▸ hd.frontierBound, hf.symm ▸ hd.delayBound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hincludes, hget, hdir]
    exact hd.includes
  · rw [prefixSet_append_before _ _ _ h.le, hget, hdir]
    exact hd.prior
  · rw [hget, hdir]
    exact hd.refresh
  · rw [hget, hdir]
    exact hd.movement
  · rw [hget, hdir]
    exact hd.raw

lemma log_append {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (ws : List (Fin m))
    (hs : Data s B lower upper window move) (hn : ws.Nodup)
    (hc : 0 < (selectedLabels s ws).length)
    (hlo : lower ≤ (selectedLabels s ws).length) (hhi : (selectedLabels s ws).length ≤ upper)
    (hwindow : ∀ w ∈ ws, age s w + (selectedLabels s ws).length - 1 ≤ window)
    (t : TraceState) (target : ℕ) (he : Extends s.trace t) (ht : target < t.nextState)
    (hmarks : t.markers = s.trace.markers ++ [target])
    (hh : (t.states target).history = (s.accepted ++ selectedLabels s ws).toFinset) :
    Log t target (s.accepted ++ selectedLabels s ws)
      (s.cuts ++ [s.accepted.length + (selectedLabels s ws).length])
      (s.frontiers ++ selectedFrontiers s ws) B lower upper window move := by
  let labels := s.accepted ++ selectedLabels s ws
  let top := s.accepted.length + (selectedLabels s ws).length
  let cuts := s.cuts ++ [top]
  have hcount : labels.length = top := List.length_append
  have hlen : cuts.length = s.cuts.length + 1 := by simp [cuts]
  have hold (k : ℕ) (hk : k < s.cuts.length) : cutIndex cuts k = cutIndex s.cuts k := by
    simp [cutIndex, cuts, List.getElem?_append_left hk]
  have hnew : cutIndex cuts s.cuts.length = top := by simp [cutIndex, cuts]
  have hlast : cutIndex s.cuts (s.cuts.length - 1) = s.accepted.length := by
    unfold cutIndex
    rw [← List.getLast?_eq_getElem?]
    exact hs.main.cutLast
  have hcut (k : ℕ) (hk : k + 1 = s.cuts.length) :
      cutIndex cuts k = s.accepted.length ∧ cutIndex cuts (k + 1) = top := by
    rw [hold k (by omega), hk, hnew]
    have heq : k = s.cuts.length - 1 := by omega
    exact ⟨heq.symm ▸ hlast, rfl⟩
  have hlenM : s.trace.markers.length = s.cuts.length := hs.main.markerCount
  change Log t target labels cuts (s.frontiers ++ selectedFrontiers s ws) B lower upper window move
  refine ⟨by rw [hlen]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ht, hh, ?_, ?_⟩
  · rw [List.length_append, hs.main.frontierCount, frontier_length, hcount]
  · unfold labels
    rw [List.nodup_append]
    refine ⟨hs.main.unique, selected_nodup s ws hs hn, ?_⟩
    intro d hd j hj heq
    subst j
    exact disjoint_left.mp (selected_disjoint s ws hs) (List.mem_toFinset.mpr hj) (List.mem_toFinset.mpr hd)
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact (hs.main.labels d hd).trans_le he.directionCount
    · obtain ⟨w, _, hw⟩ := (mem_selected s ws d).1 (List.mem_toFinset.mpr hd)
      exact ((hs.branch w).chain.bounded d (List.mem_toFinset.mp hw)).trans_le he.directionCount
  · rw [hold 0 hs.main.nonempty, hs.main.cutStart]
  · simp [cuts, hcount]
  · intro k hk
    rw [hlen] at hk
    by_cases hk' : k < s.cuts.length
    · rw [hold k hk', hcount]
      exact (hs.main.cutBound k hk').trans (Nat.le_add_right _ _)
    · have heq : k = s.cuts.length := by omega
      rw [heq, hnew, hcount]
  · intro k hk
    rw [hlen] at hk
    by_cases hk' : k + 1 < s.cuts.length
    · rw [hold k (by omega), hold (k + 1) hk']
      exact hs.main.positive k hk'
    · obtain ⟨ha, hb⟩ := hcut k (by omega)
      rw [ha, hb]
      unfold top
      omega
  · intro k hk
    rw [hlen] at hk
    by_cases hk' : k + 1 < s.cuts.length
    · rw [hold k (by omega), hold (k + 1) hk']
      exact hs.main.mass k hk'
    · obtain ⟨ha, hb⟩ := hcut k (by omega)
      rw [ha, hb]
      simp only [top, Nat.add_sub_cancel_left]
      exact ⟨hlo, hhi⟩
  · rw [hmarks, hlen, List.length_append, List.length_singleton, hlenM]
  · simp [hmarks]
  · intro k hk
    rw [hlen] at hk
    by_cases hk' : k < s.cuts.length
    · have hi : k < s.trace.markers.length := by rwa [hlenM]
      have hm : s.trace.markers[k]?.getD 0 ∈ s.trace.markers := by simp [hi]
      rw [hmarks, List.getElem?_append_left hi, he.oldState _ (marker_bounds hs _ hm),
        hs.main.markers k hk', hold k hk']
      exact (prefixSet_append_before _ _ _ (hs.main.cutBound k hk')).symm
    · have hk' : k = s.cuts.length := by omega
      have hi : k = s.trace.markers.length := hk'.trans hlenM.symm
      have hmark : (s.trace.markers ++ [target])[k]?.getD 0 = target := by simp [hi]
      rw [hmarks, hmark, hh, hk', hnew, ← hcount]
      unfold prefixSet
      rw [List.take_length]
  · intro n hn'
    by_cases h : n < s.accepted.length
    · exact old_directions s ws hs t he n hn' h
    · exact new_directions s ws hs hwindow t he n hn' (Nat.le_of_not_gt h)

end LongTails.Proofs.BirchCollectionPoolOrder
