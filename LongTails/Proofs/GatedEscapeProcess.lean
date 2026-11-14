import LongTails.Algorithms.GatedPerturbedEscape
import LongTails.Proofs.Execution
import LongTails.Proofs.StrongGrowthAgdBlocks

namespace LongTails.Proofs.GatedEscapeProcess

open OracleTemplate LongTails.Algorithms.GatedPerturbedEscape LongTails.Proofs.StrongGrowthAgdBlocks

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
variable (cfg : Config) (d : ℕ) (x0 : E) (g : E → Ω → E)

noncomputable def bmean (q : E) (ω : Fin cfg.b → Ω) : E := (1 / (cfg.b : ℝ)) • ∑ i, g q (ω i)

noncomputable def blockStep (s : State E) (ω : Fin cfg.b → Ω) : State E :=
  if s.done then s else stepBlock cfg d s (bmean cfg g (queryPoint cfg s) ω) (s.zs s.t)

noncomputable def astep (s : State E) (X : (Fin cfg.b → Ω) × E) : State E :=
  if s.done then s else stepBlock cfg d s (bmean cfg g (queryPoint cfg s) X.1) X.2

noncomputable def traj (zs : ℕ → E) (ξ : ℕ → Ω) : ℕ → State E
  | 0 => initState x0 zs
  | t + 1 => blockStep cfg d g (traj zs ξ t) (fun i => ξ (t * cfg.b + i))

lemma traj_succ (zs : ℕ → E) (ξ : ℕ → Ω) (t : ℕ) :
    traj cfg d x0 g zs ξ (t + 1) = blockStep cfg d g (traj cfg d x0 g zs ξ t) (fun i => ξ (t * cfg.b + i)) :=
  rfl

omit [InnerProductSpace ℝ E] in
lemma endAttempt_fields (s : State E) :
    (endAttempt cfg s).i = s.i ∧ (endAttempt cfg s).acc = s.acc ∧ (endAttempt cfg s).zs = s.zs ∧
      (endAttempt cfg s).t = s.t := by
  unfold endAttempt; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

lemma blockUpdate_fields (s : State E) (gb z : E) :
    (blockUpdate cfg d s gb z).i = s.i ∧ (blockUpdate cfg d s gb z).acc = s.acc ∧
      (blockUpdate cfg d s gb z).zs = s.zs := by
  unfold blockUpdate endAttempt
  cases s.ph <;> dsimp only <;> (try split_ifs) <;>
    exact ⟨rfl, rfl, rfl⟩

lemma stepBlock_fields (s : State E) (gb z : E) :
    (stepBlock cfg d s gb z).i = s.i ∧ (stepBlock cfg d s gb z).acc = s.acc ∧
      (stepBlock cfg d s gb z).zs = s.zs ∧ (stepBlock cfg d s gb z).t = s.t + 1 := by
  obtain ⟨h1, h2, h3⟩ := blockUpdate_fields cfg d s gb z
  exact ⟨h1, h2, h3, rfl⟩

lemma traj_fields (zs : ℕ → E) (ξ : ℕ → Ω) (t : ℕ) :
    (traj cfg d x0 g zs ξ t).i = 0 ∧ (traj cfg d x0 g zs ξ t).acc = 0 ∧
      (traj cfg d x0 g zs ξ t).zs = zs ∧
      ((traj cfg d x0 g zs ξ t).done = false → (traj cfg d x0 g zs ξ t).t = t) := by
  induction t with
  | zero => exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨hi, hacc, hzs, ht⟩ := ih
    rw [traj_succ]
    unfold blockStep
    by_cases hd : (traj cfg d x0 g zs ξ t).done = true
    · simp only [hd, ↓reduceIte]
      exact ⟨hi, hacc, hzs, fun h => by simp at h⟩
    · have hd' : (traj cfg d x0 g zs ξ t).done = false := by simpa using hd
      simp only [hd', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := stepBlock_fields cfg d (traj cfg d x0 g zs ξ t)
        (bmean cfg g (queryPoint cfg (traj cfg d x0 g zs ξ t)) fun i => ξ (t * cfg.b + i))
        ((traj cfg d x0 g zs ξ t).zs (traj cfg d x0 g zs ξ t).t)
      exact ⟨h1.trans hi, h2.trans hacc, h3.trans hzs, fun _ => by rw [h4, ht hd']⟩

def blocks (ξ : ℕ → Ω) : ℕ → (Fin cfg.b → Ω) := fun t i => ξ (t * cfg.b + i)

lemma traj_eq_run (zs : ℕ → E) (ξ : ℕ → Ω) : ∀ N,
    traj cfg d x0 g zs ξ N = run (astep cfg d g) (initState x0 zs) (fun n => (blocks cfg ξ n, zs n)) N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [traj_succ, run_succ, ← ih]
    unfold blockStep astep
    by_cases hd : (traj cfg d x0 g zs ξ N).done = true
    · simp [hd]
    · have hd' : (traj cfg d x0 g zs ξ N).done = false := by simpa using hd
      obtain ⟨_, _, hzs, ht⟩ := traj_fields cfg d x0 g zs ξ N
      simp only [hd', Bool.false_eq_true, ↓reduceIte, hzs, ht hd']
      rfl

lemma queryPoint_partial (s : State E) (j : ℕ) (a : E) :
    queryPoint cfg { s with i := j, acc := a } = queryPoint cfg s := rfl

variable (ξ : ℕ → Ω)

noncomputable def F (sc : State E × ℕ) : State E × ℕ :=
  (update cfg d sc.1 (g (queryPoint cfg sc.1) (ξ sc.2)), sc.2 + 1)

lemma F_partial (s : State E) (hi : s.i = 0) (hacc : s.acc = 0) (hd : s.done = false) (n0 : ℕ) :
    ∀ j, j < cfg.b →
      (F cfg d g ξ)^[j] (s, n0) =
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
    (F cfg d g ξ)^[cfg.b] (s, n0) =
      (stepBlock cfg d s (bmean cfg g (queryPoint cfg s) (fun i => ξ (n0 + i))) (s.zs s.t),
        n0 + cfg.b) := by
  obtain ⟨b', hb'⟩ : ∃ b', cfg.b = b' + 1 := ⟨cfg.b - 1, by omega⟩
  have hpart := F_partial cfg d g ξ s hi hacc hd n0 b' (by omega)
  have hit : (F cfg d g ξ)^[cfg.b] (s, n0) = F cfg d g ξ ((F cfg d g ξ)^[b'] (s, n0)) := by
    conv_lhs => rw [hb']
    exact Function.iterate_succ_apply' _ _ _
  rw [hit, hpart]
  simp only [F, queryPoint_partial]
  unfold update
  have hnlt : ¬ (b' + 1 < cfg.b) := by omega
  simp only [hd, Bool.false_eq_true, ↓reduceIte, hnlt]
  have hs : ({ s with i := 0, acc := 0 } : State E) = s := by
    cases s; simp_all
  have hsum : ∑ i : Fin cfg.b, g (queryPoint cfg s) (ξ (n0 + i)) =
      ∑ l ∈ Finset.range b', g (queryPoint cfg s) (ξ (n0 + l)) + g (queryPoint cfg s) (ξ (n0 + b')) := by
    rw [Fin.sum_univ_eq_sum_range (fun l => g (queryPoint cfg s) (ξ (n0 + l))) cfg.b, hb',
      Finset.sum_range_succ]
  unfold bmean
  refine Prod.ext ?_ (by simp only; omega)
  simp only
  congr 1
  · cases s; simp_all
  · rw [hsum]

lemma F_done (s : State E) (hd : s.done = true) (n : ℕ) :
    ∀ j, (F cfg d g ξ)^[j] (s, n) = (s, n + j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [F, update, hd, ↓reduceIte]
    rfl

lemma F_blockStep (s : State E) (hi : s.i = 0) (hacc : s.acc = 0) (hb : 0 < cfg.b) (n0 : ℕ) :
    (F cfg d g ξ)^[cfg.b] (s, n0) = (blockStep cfg d g s (fun i => ξ (n0 + i)), n0 + cfg.b) := by
  unfold blockStep
  by_cases hd : s.done
  · rw [F_done cfg d g ξ s hd n0]; simp [hd]
  · have hd' : s.done = false := by simpa using hd
    rw [F_block cfg d g ξ s hi hacc hd' hb n0]
    simp [hd']

lemma F_traj (zs : ℕ → E) (hb : 0 < cfg.b) : ∀ N,
    (F cfg d g ξ)^[N * cfg.b] (initState x0 zs, 0) = (traj cfg d x0 g zs ξ N, N * cfg.b) := by
  intro N
  induction N with
  | zero => simp; rfl
  | succ N ih =>
    obtain ⟨hi, hacc, _, _⟩ := traj_fields cfg d x0 g zs ξ N
    rw [show (N + 1) * cfg.b = cfg.b + N * cfg.b by ring, Function.iterate_add_apply, ih,
      F_blockStep cfg d g ξ _ hi hacc hb, traj_succ]
    congr 1
    ring

theorem execute_method [FiniteDimensional ℝ E] [MeasurableSpace E] [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (hb : 0 < cfg.b) (N : ℕ) (zs : ℕ → E) :
    execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle E E)
      (method cfg x0) (fun _ => N * cfg.b) zs ξ =
        (traj cfg (Module.finrank ℝ E) x0 g zs ξ N).x := by
  refine (execute_indexed_of_answer
    ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle E E)
    (method cfg x0) (N * cfg.b) zs ξ (fun n q => g q.2 (ξ n)) (fun _ _ => rfl)).trans ?_
  change ((F cfg (Module.finrank ℝ E) g ξ)^[N * cfg.b] (initState x0 zs, 0)).1.x = _
  rw [F_traj cfg (Module.finrank ℝ E) x0 g ξ zs hb N]

end LongTails.Proofs.GatedEscapeProcess
