import LongTails.Algorithms.StrongGrowthRestartedAgd
import LongTails.Proofs.Execution

namespace LongTails.Proofs.StrongGrowthAgdProcess

open OracleTemplate LongTails.Algorithms.StrongGrowthRestartedAgd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
variable (cfg : Config) (x0 : E) (g : E → Ω → E)

noncomputable def bmean (q : E) (ω : Fin cfg.b → Ω) : E := (1 / (cfg.b : ℝ)) • ∑ i, g q (ω i)

noncomputable def blockStep (s : State E) (ω : Fin cfg.b → Ω) : State E :=
  if s.done then s else batchUpdate cfg x0 s (bmean cfg g (queryPoint cfg s) ω)

noncomputable def traj (ξ : ℕ → Ω) : ℕ → State E
  | 0 => initState x0
  | t + 1 => blockStep cfg x0 g (traj ξ t) (fun i => ξ (t * cfg.b + i))

lemma traj_zero (ξ : ℕ → Ω) : traj cfg x0 g ξ 0 = initState x0 := rfl

lemma traj_succ (ξ : ℕ → Ω) (t : ℕ) :
    traj cfg x0 g ξ (t + 1) = blockStep cfg x0 g (traj cfg x0 g ξ t) (fun i => ξ (t * cfg.b + i)) := rfl

lemma batchUpdate_i (s : State E) (v : E) : (batchUpdate cfg x0 s v).i = s.i := by
  unfold batchUpdate restart
  dsimp only
  split_ifs <;> rfl

lemma batchUpdate_acc (s : State E) (v : E) : (batchUpdate cfg x0 s v).acc = s.acc := by
  unfold batchUpdate restart
  dsimp only
  split_ifs <;> rfl

lemma blockStep_i (s : State E) (ω : Fin cfg.b → Ω) : (blockStep cfg x0 g s ω).i = s.i := by
  unfold blockStep; split_ifs
  · rfl
  · exact batchUpdate_i cfg x0 _ _

lemma blockStep_acc (s : State E) (ω : Fin cfg.b → Ω) : (blockStep cfg x0 g s ω).acc = s.acc := by
  unfold blockStep; split_ifs
  · rfl
  · exact batchUpdate_acc cfg x0 _ _

lemma traj_i (ξ : ℕ → Ω) (t : ℕ) : (traj cfg x0 g ξ t).i = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [traj_succ, blockStep_i]; exact ih

lemma traj_acc (ξ : ℕ → Ω) (t : ℕ) : (traj cfg x0 g ξ t).acc = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [traj_succ, blockStep_acc]; exact ih

lemma traj_congr {ξ ξ' : ℕ → Ω} : ∀ t, (∀ n, n < t * cfg.b → ξ n = ξ' n) →
    traj cfg x0 g ξ t = traj cfg x0 g ξ' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    rw [traj_succ, traj_succ, ih (fun n hn => h n (by
      calc n < t * cfg.b := hn
        _ ≤ (t + 1) * cfg.b := Nat.mul_le_mul_right _ (Nat.le_succ t)))]
    congr 1
    funext i
    exact h _ (by
      have := i.isLt
      calc t * cfg.b + (i : ℕ) < t * cfg.b + cfg.b := by omega
        _ = (t + 1) * cfg.b := by ring)

lemma queryPoint_partial (s : State E) (j : ℕ) (a : E) :
    queryPoint cfg { s with i := j, acc := a } = queryPoint cfg s := rfl

variable (ξ : ℕ → Ω)

noncomputable def F (sc : State E × ℕ) : State E × ℕ :=
  (update cfg x0 sc.1 (g (queryPoint cfg sc.1) (ξ sc.2)), sc.2 + 1)

lemma F_partial (s : State E) (hi : s.i = 0) (hacc : s.acc = 0) (hd : s.done = false) (n0 : ℕ) :
    ∀ j, j < cfg.b →
      (F cfg x0 g ξ)^[j] (s, n0) =
        ({ s with i := j, acc := ∑ l ∈ Finset.range j, g (queryPoint cfg s) (ξ (n0 + l)) }, n0 + j) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Function.iterate_zero, id_eq, Finset.range_zero, Finset.sum_empty, Nat.add_zero]
    cases s
    simp_all
  | succ j ih =>
    intro hj
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [F, queryPoint_partial]
    unfold update
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    have hlt : j + 1 < cfg.b := hj
    simp only [hlt, ↓reduceIte, Finset.sum_range_succ]
    rfl

lemma F_block (s : State E) (hi : s.i = 0) (hacc : s.acc = 0) (hd : s.done = false)
    (hb : 0 < cfg.b) (n0 : ℕ) :
    (F cfg x0 g ξ)^[cfg.b] (s, n0) =
      (batchUpdate cfg x0 s (bmean cfg g (queryPoint cfg s) (fun i => ξ (n0 + i))), n0 + cfg.b) := by
  obtain ⟨b', hb'⟩ : ∃ b', cfg.b = b' + 1 := ⟨cfg.b - 1, by omega⟩
  have hpart := F_partial cfg x0 g ξ s hi hacc hd n0 b' (by omega)
  have hit : (F cfg x0 g ξ)^[cfg.b] (s, n0) = F cfg x0 g ξ ((F cfg x0 g ξ)^[b'] (s, n0)) := by
    conv_lhs => rw [hb']
    exact Function.iterate_succ_apply' _ _ _
  rw [hit, hpart]
  simp only [F, queryPoint_partial]
  unfold update
  have hnlt : ¬ (b' + 1 < cfg.b) := by omega
  simp only [hd, Bool.false_eq_true, ↓reduceIte, hnlt]
  have hs : ({ s with i := 0, acc := 0, done := false } : State E) = s := by
    cases s; simp_all
  rw [hs]
  have hsum : ∑ i : Fin cfg.b, g (queryPoint cfg s) (ξ (n0 + i)) =
      ∑ l ∈ Finset.range b', g (queryPoint cfg s) (ξ (n0 + l)) + g (queryPoint cfg s) (ξ (n0 + b')) := by
    rw [Fin.sum_univ_eq_sum_range (fun l => g (queryPoint cfg s) (ξ (n0 + l))) cfg.b, hb',
      Finset.sum_range_succ]
  unfold bmean
  rw [hsum]
  refine Prod.ext rfl ?_
  simp only
  omega

lemma F_done (s : State E) (hd : s.done = true) (n : ℕ) :
    ∀ j, (F cfg x0 g ξ)^[j] (s, n) = (s, n + j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [F, update, hd, ↓reduceIte]
    rfl

lemma F_blockStep (s : State E) (hi : s.i = 0) (hacc : s.acc = 0) (hb : 0 < cfg.b) (n0 : ℕ) :
    (F cfg x0 g ξ)^[cfg.b] (s, n0) = (blockStep cfg x0 g s (fun i => ξ (n0 + i)), n0 + cfg.b) := by
  unfold blockStep
  by_cases hd : s.done
  · rw [F_done cfg x0 g ξ s hd n0]; simp [hd]
  · have hd' : s.done = false := by simpa using hd
    rw [F_block cfg x0 g ξ s hi hacc hd' hb n0]
    simp [hd']

lemma F_traj (hb : 0 < cfg.b) : ∀ N,
    (F cfg x0 g ξ)^[N * cfg.b] (initState x0, 0) = (traj cfg x0 g ξ N, N * cfg.b) := by
  intro N
  induction N with
  | zero => simp [traj_zero]
  | succ N ih =>
    rw [show (N + 1) * cfg.b = cfg.b + N * cfg.b by ring, Function.iterate_add_apply, ih,
      F_blockStep cfg x0 g ξ _ (traj_i cfg x0 g ξ N) (traj_acc cfg x0 g ξ N) hb, traj_succ]
    congr 1
    ring

theorem execute_method [MeasurableSpace Ω] (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (hb : 0 < cfg.b) (N : ℕ) :
    execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle E E)
      (method cfg x0) (fun _ => N * cfg.b) () ξ = (traj cfg x0 g ξ N).out := by
  refine (execute_indexed_of_answer
    ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle E E)
    (method cfg x0) (N * cfg.b) () ξ (fun n q => g q.2 (ξ n)) (fun _ _ => rfl)).trans ?_
  change ((F cfg x0 g ξ)^[N * cfg.b] (initState x0, 0)).1.out = _
  rw [F_traj cfg x0 g ξ hb N]

end LongTails.Proofs.StrongGrowthAgdProcess
