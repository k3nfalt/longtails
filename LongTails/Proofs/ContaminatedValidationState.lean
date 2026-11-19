import LongTails.Proofs.ContaminatedTrainingHistory
import LongTails.Proofs.ContaminatedValidationCalendar

namespace LongTails.Proofs.ContaminatedValidationState

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonCalendar (levels)
open LongTails.Algorithms.LeonTuning (resolution height iterations)
open ContaminatedParallelHistory ContaminatedParallelFailures ContaminatedTrainingGeometry
open ContaminatedTrainingDescent ContaminatedTrainingHistory ContaminatedValidationCalendar
open scoped Classical
variable {p : Params}

noncomputable abbrev ops (p : Params) (z : Seed p) := atOp (operations p z)
noncomputable abbrev run (D : Data p) (s : Samples p) (z : Seed p) (t : ℕ) := state p D.g (ops p z) s t

lemma congr_state (D : Data p) (s : Samples p) {o a : ℕ → Operation} (k : ℕ)
    (h : ∀ j < k, o j = a j) :
    state p D.g o s k = state p D.g a s k ∧ used p o k = used p a k := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨hs,hu⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    simp only [state,used,hs,hu,h k (Nat.lt_succ_self _),and_self]

lemma after_training (D : Data p) (s : Samples p) (z : Seed p) :
    run D s z (count p) = snapshot D s := by
  apply (congr_state D s _ ?_).1
  intro j hj
  have h : j < ((levels (height (network p))).map Operation.train).length := by simpa using hj
  simp [ops,atOp,operations,List.getElem?_append_left h,trainOp,List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem h]

lemma untouched (D : Data p) (s : Samples p) (t : ℕ) :
    (model D s t).anchor = 0 ∧ (model D s t).best = (p.x0,-1) := by
  induction t with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih => exact ih

lemma saved_get (D : Data p) (s : Samples p) (j : Fin (iterations (network p))) :
    point D s j = ((hist D s (count p))[j.val]'(by rw [length D s]; exact j.isLt)).1 := by
  simp [point,saved,List.getElem?_eq_getElem (show j.val < (hist D s (count p)).length by
    rw [length D s]; exact j.isLt)]

lemma initial_scale (D : Data p) (s : Samples p) (j : Fin (iterations (network p))) :
    ‖D.G (point D s j)‖ ≤ 2*(4:ℝ)^height (network p)*resolution (network p) := by
  have h := (path D s (count p)).2
  have hj : D.G (point D s j) ∈ ((hist D s (count p)).map (fun z => D.G z.1)) := by
    rw [saved_get D s j]
    exact List.mem_map_of_mem (f := fun z : Point p × ℝ => D.G z.1) (List.getElem_mem _)
  have hh := h _ (List.mem_cons_of_mem _ hj)
  rw [length D s] at hh
  simp only [iterations,Nat.cast_pow,Nat.cast_ofNat] at hh
  linarith only [hh,D.start_bound]

lemma gap_scale (D : Data p) (s : Samples p) (i j : Fin (iterations (network p))) (hij : i ≤ j) :
    ‖D.G (point D s i)-D.G (point D s j)‖ ≤ (j.val-i.val:ℕ)*resolution (network p) := by
  have hj : j.val < (hist D s (count p)).length := by rw [length D s]; exact j.isLt
  have hi : i.val < (hist D s (count p)).length := by rw [length D s]; exact i.isLt
  have h := (path D s (count p)).1 (i.val+1) (j.val+1) (Nat.succ_le_succ hij)
    (by simp only [List.length_cons,List.length_map]; omega)
  simp only [List.getElem?_cons_succ,List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some,Nat.succ_sub_succ_eq_sub] at h
  simpa only [saved_get] using h

lemma suffix (p : Params) (z : Seed p) :
    ∀ i < (candidateIndices p z).length, ops p z (count p+i) =
      atOp (validationOps (height (network p)) none (candidateIndices p z)) i := by
  intro i _
  unfold ops atOp operations
  rw [List.getElem?_append_right (by simp [count])]
  simp only [List.length_map,count,Nat.add_sub_cancel_left]

end LongTails.Proofs.ContaminatedValidationState
