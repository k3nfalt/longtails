import LongTails.Algorithms.BirchCollectionRetune

namespace LongTails.Proofs.BirchCollectionRetune

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionRetune

lemma map_update {α β γ : Type*} [DecidableEq α] (f : β → γ) (s : α → β) (i : α) (v : β) :
    (fun j => f (Function.update s i v j)) = Function.update (fun j => f (s j)) i (f v) := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h]

lemma retune_step (g : ℝ → ℝ × ℝ) (s : TraceState) (e : Event) :
    step (trace g s) (retune g e) = trace g (step s e) := by
  cases e with
  | capture w x b r m => simp only [step, trace, retune, map_update]; rfl
  | receive q => simp only [step, trace, retune, map_update]; rfl
  | finish c => simp only [step, trace, retune, map_update]; rfl
  | cancel c => simp only [step, trace, retune, map_update]; rfl
  | issue c w => rfl
  | merge w l r a => rfl
  | mark x => rfl
  | discard q => rfl

lemma retune_valid (g : ℝ → ℝ × ℝ) (workers : ℕ) (s : TraceState) (e : Event)
    (hg : ∀ w, 0 ≤ w → w ≤ 1 → 0 ≤ (g w).2 ∧ (g w).2 ≤ (g w).1 ∧ (g w).1 ≤ 1)
    (he : e.Valid workers s) : (retune g e).Valid workers (trace g s) := by
  cases e with
  | capture w x b r m =>
    obtain ⟨hw, hx, hb, hm, hmr, hr⟩ := he
    exact ⟨hw, hx, hb, hg m hm (hmr.trans hr)⟩
  | _ => exact he

lemma retune_fold (g : ℝ → ℝ × ℝ) (s : TraceState) (events : List Event) :
    ((events.map (retune g)).foldl step (trace g s)) = trace g (events.foldl step s) := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.foldl_cons, retune_step]
    exact ih _

lemma retune_legal (g : ℝ → ℝ × ℝ) (workers : ℕ) (s : TraceState) (events : List Event)
    (hg : ∀ w, 0 ≤ w → w ≤ 1 → 0 ≤ (g w).2 ∧ (g w).2 ≤ (g w).1 ∧ (g w).1 ≤ 1)
    (he : ValidFrom workers s events) :
    ValidFrom workers (trace g s) (events.map (retune g)) := by
  induction events generalizing s with
  | nil => trivial
  | cons e es ih =>
    refine ⟨retune_valid g workers s e hg he.1, ?_⟩
    rw [retune_step]
    exact ih _ he.2

lemma trace_initial (g : ℝ → ℝ × ℝ) (h : g 1 = (1, 1)) : trace g {} = {} := by
  simp [trace, collection, direction, h]

lemma retune_run (g : ℝ → ℝ × ℝ) (events : List Event) (h : g 1 = (1, 1)) :
    run (events.map (retune g)) = trace g (run events) := by
  simpa only [trace_initial g h, run] using retune_fold g {} events

end LongTails.Proofs.BirchCollectionRetune
