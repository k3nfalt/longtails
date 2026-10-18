import LongTails.Algorithms.QuarticMetricStage
import LongTails.Proofs.EnergyHessianExecution

namespace LongTails.Proofs.QuarticStageExecution

open OracleTemplate OracleTemplate.QueryPlan LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.EnergyHessianExecution

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma readPoint_faithful (f : E → ℝ) (x : E) :
    readPoint x (.inl (f x, gradient f x)) = ⟨x, f x, gradient f x⟩ := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma better_value (x y : Point E) : (better x y).value = min x.value y.value := by
  unfold better
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma better_member (x y : Point E) : better x y = x ∨ better x y = y := by
  unfold better
  split_ifs <;> simp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma fold_value_le_initial (points : List (Point E)) (x : Point E) :
    (points.foldl better x).value ≤ x.value := by
  induction points generalizing x with
  | nil => exact le_rfl
  | cons y ys ih =>
    exact (ih (better x y)).trans (by rw [better_value]; exact min_le_left _ _)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma fold_value_le_member (points : List (Point E)) (x y : Point E) (hy : y ∈ points) :
    (points.foldl better x).value ≤ y.value := by
  induction points generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
    rcases List.mem_cons.mp hy with h | h
    · subst z
      exact (fold_value_le_initial zs (better x y)).trans (by rw [better_value]; exact min_le_right _ _)
    · exact ih (better x z) h

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma fold_member (points : List (Point E)) (x : Point E) :
    points.foldl better x = x ∨ points.foldl better x ∈ points := by
  induction points generalizing x with
  | nil => simp
  | cons y ys ih =>
    rcases ih (better x y) with h | h
    · rcases better_member x y with hx | hy
      · left
        simpa only [List.foldl_cons, hx] using h
      · right
        simp only [hy] at h
        rw [List.foldl_cons, hy, h]
        exact List.mem_cons_self
    · right
      exact List.mem_cons_of_mem _ h

omit [FiniteDimensional ℝ E] in
lemma stop_counts (p : Parameters E) (g : Fin 2 × E → Reply E) (status : Status E) (i : Fin 2) :
    counts g (stopAfter p status) i = if i = 0 then 1 else 0 := by
  simp [stopAfter, counts]

lemma step_counts (p : Parameters E) (g : Fin 2 × E → Reply E) (status : Status E) (i : Fin 2) :
    counts g (step p status) i = if i = 0 then 2 else 0 := by
  classical
  cases status with
  | finished x => simp [step, counts, stopAfter]; split_ifs <;> omega
  | witness w => simp [step, counts, stopAfter]; split_ifs <;> omega
  | running st =>
    simp only [step, counts]
    split_ifs <;> simp_all [stopAfter, counts] <;> (try split_ifs) <;> simp_all [counts]

lemma loop_counts (p : Parameters E) (g : Fin 2 × E → Reply E) (status : Status E)
    (n : ℕ) (i : Fin 2) : counts g (loop p n status) i = if i = 0 then 2 * n else 0 := by
  induction n generalizing status with
  | zero => simp [loop, counts]
  | succ n ih =>
    simp only [loop, id_eq, counts_bind, step_counts, ih]
    split_ifs <;> omega

lemma certificate_counts (p : Parameters E) (g : Fin 2 × E → Reply E)
    (status : Status E) (i : Fin 2) :
    counts g (certificate p status) i = if i = 0 then 1 else 0 := by
  classical
  cases status with
  | finished x => exact stop_counts p g _ i
  | witness w => exact stop_counts p g _ i
  | running st =>
    simp only [certificate, counts]
    split_ifs
    all_goals (try split) <;> simp [counts]

omit [FiniteDimensional ℝ E] in
lemma traverse_counts {U : Type} (g : Fin 2 × E → Reply E) {k c d : ℕ}
    (plans : Fin k → Plan E U c) (i : Fin 2)
    (hc : ∀ j, counts g (plans j) i = d) :
    counts g (QueryPlan.traverse k plans) i = d * k := by
  induction k with
  | zero => simp [QueryPlan.traverse, counts]
  | succ k ih =>
    rw [QueryPlan.traverse, counts_bind, counts_map, hc, ih _ (fun j => hc j.succ)]
    ring

omit [FiniteDimensional ℝ E] in
lemma finish_counts (p : Parameters E) (g : Fin 2 × E → Reply E)
    (status : Status E) (i : Fin 2) :
    counts g (finish p status) i = if i = 0 then 6 else 0 := by
  cases status <;> simp only [finish, counts_map]
  all_goals
    rw [traverse_counts g _ i (d := if i = 0 then 1 else 0) (by intro j; simp [counts])]
    split_ifs <;> simp

omit [FiniteDimensional ℝ E] in
lemma counts_cast {U : Type} (g : Fin 2 × E → Reply E) {k m : ℕ}
    (h : k = m) (q : Plan E U k) (i : Fin 2) :
    counts g (h ▸ q) i = counts g q i := by
  subst m
  rfl

lemma plan_counts (p : Parameters E) (g : Fin 2 × E → Reply E) (n : ℕ) (i : Fin 2) :
    counts g (plan p n) i = if i = 0 then 2 * n + 7 else 0 := by
  simp only [plan, counts_cast, counts_bind, loop_counts, certificate_counts, finish_counts]
  split_ifs <;> omega

end LongTails.Proofs.QuarticStageExecution
