import LongTails.Algorithms.BirchCollectionWorkerPools

namespace LongTails.Proofs.BirchCollectionPoolCounts

open Finset
open LongTails.Algorithms.BirchCollectionWorkerPools

def privateCount {m : ℕ} (s : Pool m) (w : Fin m) : ℕ := (s.worker w).privateLabels.length

lemma selected_count {m : ℕ} (s : Pool m) (ws : List (Fin m)) (hn : ws.Nodup) :
    (selectedLabels s ws).length = ∑ w ∈ ws.toFinset, privateCount s w := by
  induction ws with
  | nil => simp [selectedLabels]
  | cons w ws ih =>
    have hnot : w ∉ ws.toFinset := by simpa using (List.nodup_cons.mp hn).1
    have ht := ih (List.nodup_cons.mp hn).2
    change ((s.worker w).privateLabels ++ selectedLabels s ws).length = _
    rw [List.length_append, ht, List.toFinset_cons, sum_insert hnot]
    rfl

lemma close_profile {m : ℕ} (B : ℕ) (s : Pool m) (w u : Fin m) :
    (discard B s w).accepted = s.accepted ∧
      privateCount (discard B s w) u = privateCount s u ∧
      ((discard B s w).worker u).frontier = (s.worker u).frontier := by
  cases ht : (s.worker w).pending with
  | none => simp [LongTails.Algorithms.BirchCollectionWorkerPools.discard, ht]
  | some ticket =>
    simp only [LongTails.Algorithms.BirchCollectionWorkerPools.discard, ht]
    constructor
    · rfl
    · by_cases h : u = w
      · subst u
        simp [Pool.put, Pool.append, privateCount]
      · simp [Pool.put, Pool.append, privateCount, Function.update_of_ne h]

lemma close_many_profile {m : ℕ} (B : ℕ) (s : Pool m) (ws : List (Fin m)) :
    let out := ws.foldl (discard B) s
    out.accepted = s.accepted ∧
      ∀ u, privateCount out u = privateCount s u ∧ (out.worker u).frontier = (s.worker u).frontier := by
  induction ws generalizing s with
  | nil => exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | cons w ws ih =>
    obtain ⟨ha, hp⟩ := ih (discard B s w)
    exact ⟨ha.trans (close_profile B s w w).1, fun u =>
      ⟨(hp u).1.trans (close_profile B s w u).2.1, (hp u).2.trans (close_profile B s w u).2.2⟩⟩

lemma merge_fold_worker {m : ℕ} (s : Pool m) (t : Pool m × ℕ) (ws : List (Fin m)) :
    ((ws.foldl (fun (t, left) w =>
      (t.append [.merge 0 left (s.worker w).head (s.worker w).base], t.trace.nextState)) t).1.worker) =
      t.1.worker := by
  induction ws generalizing t with
  | nil => rfl
  | cons w ws ih => exact ih _

lemma reset_workers {m : ℕ} (s : Pool m) (ws : List (Fin m)) (root : Worker) (w : Fin m) :
    ((ws.foldl (fun t u => t.put u root) s).worker w) =
      if w ∈ ws then root else s.worker w := by
  induction ws generalizing s with
  | nil => simp
  | cons u ws ih =>
    rw [List.foldl_cons, ih]
    by_cases hm : w ∈ ws
    · simp [hm]
    · by_cases he : w = u
      · subst w
        simp [hm, Pool.put]
      · simp [hm, he, Pool.put]

lemma reset_accepted {m : ℕ} (s : Pool m) (ws : List (Fin m)) (root : Worker) :
    (ws.foldl (fun t w => t.put w root) s).accepted = s.accepted := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact ih (s.put w root)

lemma publish_profile {m : ℕ} (B : ℕ) (s : Pool m) (ws : List (Fin m)) :
    let out := publish B s ws
    let c := (selectedLabels s ws).length
    out.accepted.length = s.accepted.length + c ∧
      (∀ w, privateCount out w = if w ∈ ws then 0 else privateCount s w) ∧
      (∀ w, (out.worker w).frontier = if w ∈ ws then out.accepted.length else (s.worker w).frontier) := by
  let closed := ws.foldl (discard B) s
  let out := publishState B s ws
  let root : Worker := {base := out.main, head := out.main, frontier := out.accepted.length}
  let t := ws.foldl (fun s w => s.put w root) out
  let c := (selectedLabels s ws).length
  have hc := close_many_profile B s ws
  have hp : out.accepted.length = s.accepted.length + c ∧
      ∀ w, privateCount out w = privateCount s w ∧ (out.worker w).frontier = (s.worker w).frontier := by
    by_cases h : (selectedLabels s ws).isEmpty
    · have hlist : selectedLabels s ws = [] := List.isEmpty_iff.mp h
      have ho : out = closed := by simp only [out, publishState, ite_eq_left h, closed]
      rw [ho]
      exact ⟨by simpa only [c, hlist, List.length_nil, Nat.add_zero] using congrArg List.length hc.1, hc.2⟩
    · let merged := ws.foldl (fun (t, left) w =>
        (t.append [.merge 0 left (s.worker w).head (s.worker w).base], t.trace.nextState))
        (closed, s.main)
      have ho : out =
          { merged.1.append [.mark merged.2] with
            main := merged.2
            accepted := s.accepted ++ selectedLabels s ws
            cuts := s.cuts ++ [s.accepted.length + c]
            frontiers := s.frontiers ++ selectedFrontiers s ws } := by
        simp only [out, publishState, ite_eq_right h, closed, merged, c]
      have hworkers : out.worker = closed.worker := by
        rw [ho]
        exact merge_fold_worker s (closed, s.main) ws
      refine ⟨?_, ?_⟩
      · rw [ho]
        exact List.length_append
      · intro w
        unfold privateCount
        rw [hworkers]
        exact hc.2 w
  have hacc : t.accepted = out.accepted := reset_accepted out ws root
  change t.accepted.length = _ ∧ _ ∧ _
  refine ⟨(congrArg List.length hacc).trans hp.1, ?_, ?_⟩
  · intro w
    change ((ws.foldl (fun s w => s.put w root) out).worker w).privateLabels.length = _
    rw [reset_workers]
    by_cases hm : w ∈ ws
    · simp [hm, root]
    · rw [ite_eq_right hm, ite_eq_right hm]
      exact (hp.2 w).1
  · intro w
    change ((ws.foldl (fun s w => s.put w root) out).worker w).frontier =
      if w ∈ ws then t.accepted.length else (s.worker w).frontier
    rw [reset_workers, hacc]
    by_cases hm : w ∈ ws
    · simp [hm, root]
    · simpa only [ite_eq_right hm] using (hp.2 w).2

lemma remaining_publish {m : ℕ} (B : ℕ) (s : Pool m) (ws : List (Fin m)) (hn : ws.Nodup) :
    remaining (publish B s ws) + (selectedLabels s ws).length = remaining s := by
  have hp := (publish_profile B s ws).2.1
  rw [selected_count s ws hn]
  unfold remaining
  change (∑ w : Fin m, privateCount (publish B s ws) w) + _ = _
  have he : (∑ w ∈ ws.toFinset, privateCount s w) =
      ∑ w : Fin m, if w ∈ ws then privateCount s w else 0 := by
    rw [← sum_filter]
    congr 1
    ext w
    simp
  rw [he, ← sum_add_distrib]
  apply sum_congr rfl
  intro w _
  rw [hp w]
  by_cases hm : w ∈ ws
  · simp [hm, privateCount]
  · simp [hm, privateCount]

lemma accepted_count_window {m : ℕ} (s : Pool m) (ws : List (Fin m)) (Q : ℕ)
    (hn : ws.Nodup) (hcap : maxAge s + remaining s ≤ Q) :
    (selectedLabels s ws).length ≤ Q ∧
      ∀ w ∈ ws, age s w + (selectedLabels s ws).length ≤ Q := by
  have hcount : (selectedLabels s ws).length ≤ remaining s := by
    have he := remaining_publish 1 s ws hn
    omega
  refine ⟨by omega, ?_⟩
  intro w _
  have hage : age s w ≤ maxAge s := le_sup (f := age s) (mem_univ w)
  omega

end LongTails.Proofs.BirchCollectionPoolCounts
