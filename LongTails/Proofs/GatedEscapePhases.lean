import LongTails.Proofs.GatedEscapeProcess

namespace LongTails.Proofs.GatedEscapePhases

open LongTails.Algorithms.GatedPerturbedEscape LongTails.Proofs.GatedEscapeProcess
  LongTails.Proofs.StrongGrowthAgdBlocks
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
variable (cfg : Config) (d : ℕ) (g : E → Ω → E)

lemma astep_live (s : State E) (hd : s.done = false) (X : (Fin cfg.b → Ω) × E) :
    astep cfg d g s X = { blockUpdate cfg d s (bmean cfg g (queryPoint cfg s) X.1) X.2 with t := s.t + 1 } := by
  simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock]

lemma astep_done (s : State E) (hd : s.done = true) (X : (Fin cfg.b → Ω) × E) : astep cfg d g s X = s := by
  simp only [astep, hd, ↓reduceIte]

lemma run_done (s : State E) (hd : s.done = true) (tail : ℕ → (Fin cfg.b → Ω) × E) :
    ∀ n, run (astep cfg d g) s tail n = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, astep_done cfg d g s hd]

noncomputable def fill (base : ℕ → E) (q : E) (tail : ℕ → (Fin cfg.b → Ω) × E) (j : ℕ) : ℕ → E :=
  fun i => if i < j then bmean cfg g q (tail i).1 else base i

lemma fill_succ (base : ℕ → E) (q : E) (tail : ℕ → (Fin cfg.b → Ω) × E) (j : ℕ) :
    Function.update (fill cfg g base q tail j) j (bmean cfg g q (tail j).1) = fill cfg g base q tail (j + 1) := by
  funext i
  unfold fill
  by_cases h : i = j
  · subst h; simp
  · rw [Function.update_of_ne h]
    by_cases h2 : i < j
    · simp [h2, show i < j + 1 by omega]
    · simp [h2, show ¬ i < j + 1 by omega]

theorem run_test (s : State E) (hd : s.done = false) (hph : s.ph = .test) (hj : s.j = 0)
    (tail : ℕ → (Fin cfg.b → Ω) × E) :
    ∀ j, j < cfg.M → run (astep cfg d g) s tail j =
      { s with store := fill cfg g s.store s.x tail j, j := j, t := s.t + j } := by
  intro j
  induction j with
  | zero =>
    intro _
    have hf : ∀ q, fill cfg g s.store q tail 0 = s.store := fun q => funext fun i => by simp [fill]
    rw [hf]
    cases s
    simp only at hj
    subst hj
    rfl
  | succ j ih =>
    intro hjM
    rw [run_succ, ih (by omega)]
    simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show j + 1 < cfg.M from hjM, ↓reduceIte, fill_succ]
    rfl

theorem run_grad0 (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0)
    (tail : ℕ → (Fin cfg.b → Ω) × E) :
    ∀ j, j < cfg.M → run (astep cfg d g) s tail j =
      { s with store := fill cfg g s.store s.x tail j, j := j, t := s.t + j } := by
  intro j
  induction j with
  | zero =>
    intro _
    have hf : ∀ q, fill cfg g s.store q tail 0 = s.store := fun q => funext fun i => by simp [fill]
    rw [hf]
    cases s
    simp only at hj
    subst hj
    rfl
  | succ j ih =>
    intro hjM
    rw [run_succ, ih (by omega)]
    simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show j + 1 < cfg.M from hjM, ↓reduceIte, fill_succ]
    rfl

theorem run_grad0_end (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0)
    (hM : 0 < cfg.M) (tail : ℕ → (Fin cfg.b → Ω) × E) :
    run (astep cfg d g) s tail cfg.M =
      { s with
        store := fill cfg g s.store s.x tail cfg.M
        j := 0
        ph := .init
        g0 := select cfg.M cfg.τ0 (fill cfg g s.store s.x tail cfg.M)
        t := s.t + cfg.M } := by
  obtain ⟨m, hm⟩ : ∃ m, cfg.M = m + 1 := ⟨cfg.M - 1, by omega⟩
  have hpre := run_grad0 cfg d g s hd hph hj tail m (by omega)
  rw [hm, run_succ, hpre]
  simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show ¬ (m + 1 < cfg.M) by omega, ↓reduceIte, fill_succ]
  rw [Nat.add_assoc, ← hm]

theorem run_test_end (s : State E) (hd : s.done = false) (hph : s.ph = .test) (hj : s.j = 0)
    (hM : 0 < cfg.M) (tail : ℕ → (Fin cfg.b → Ω) × E) :
    run (astep cfg d g) s tail cfg.M =
      if cfg.gth < ‖select cfg.M cfg.τg (fill cfg g s.store s.x tail cfg.M)‖ then
        { s with
          store := fill cfg g s.store s.x tail cfg.M
          j := 0
          x := s.x - cfg.η • select cfg.M cfg.τg (fill cfg g s.store s.x tail cfg.M)
          t := s.t + cfg.M }
      else
        { s with
          store := fill cfg g s.store s.x tail cfg.M
          j := 0
          ph := .grad0
          att := 0
          found := false
          t := s.t + cfg.M } := by
  obtain ⟨m, hm⟩ : ∃ m, cfg.M = m + 1 := ⟨cfg.M - 1, by omega⟩
  have hpre := run_test cfg d g s hd hph hj tail m (by omega)
  rw [hm, run_succ, hpre]
  simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show ¬ (m + 1 < cfg.M) by omega, ↓reduceIte, fill_succ]
  rw [Nat.add_assoc, ← hm]
  split_ifs <;> rfl

theorem run_init (s : State E) (hd : s.done = false) (hph : s.ph = .init) (X : (Fin cfg.b → Ω) × E) :
    astep cfg d g s X = { s with ph := .traj, v := clip cfg.r ((cfg.s0 / Real.sqrt d) • X.2), t := s.t + 1 } := by
  rw [astep_live cfg d g _ hd]
  simp only [blockUpdate, hph]

noncomputable def vstep (x g0 : E) (v : E) (B : Fin cfg.b → Ω) : E :=
  clip cfg.r (v - cfg.η • (bmean cfg g (x + v) B - g0))

noncomputable def vrun (x g0 v0 : E) (blocks : ℕ → (Fin cfg.b → Ω)) : ℕ → E
  | 0 => v0
  | n + 1 => vstep cfg g x g0 (vrun x g0 v0 blocks n) (blocks n)

theorem run_traj (s : State E) (hd : s.done = false) (hph : s.ph = .traj) (hj : s.j = 0)
    (tail : ℕ → (Fin cfg.b → Ω) × E) :
    ∀ j, j < cfg.T → run (astep cfg d g) s tail j =
      { s with v := vrun cfg g s.x s.g0 s.v (fun n => (tail n).1) j, j := j, t := s.t + j } := by
  intro j
  induction j with
  | zero =>
    intro _
    cases s
    simp only at hj
    subst hj
    rfl
  | succ j ih =>
    intro hjT
    rw [run_succ, ih (by omega)]
    simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show j + 1 < cfg.T from hjT, ↓reduceIte]
    rfl

theorem run_traj_end (s : State E) (hd : s.done = false) (hph : s.ph = .traj) (hj : s.j = 0)
    (hT : 0 < cfg.T) (tail : ℕ → (Fin cfg.b → Ω) × E) :
    run (astep cfg d g) s tail cfg.T =
      { s with
        v := vrun cfg g s.x s.g0 s.v (fun n => (tail n).1) cfg.T
        j := 0
        ph := .ray
        w := (1 / ‖vrun cfg g s.x s.g0 s.v (fun n => (tail n).1) cfg.T‖) •
          vrun cfg g s.x s.g0 s.v (fun n => (tail n).1) cfg.T
        t := s.t + cfg.T } := by
  obtain ⟨m, hm⟩ : ∃ m, cfg.T = m + 1 := ⟨cfg.T - 1, by omega⟩
  have hpre := run_traj cfg d g s hd hph hj tail m (by omega)
  rw [hm, run_succ, hpre]
  simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show ¬ (m + 1 < cfg.T) by omega, ↓reduceIte]
  rw [Nat.add_assoc]
  rfl

theorem run_ray (s : State E) (hd : s.done = false) (hph : s.ph = .ray) (hj : s.j = 0)
    (tail : ℕ → (Fin cfg.b → Ω) × E) :
    ∀ j, j < cfg.M → run (astep cfg d g) s tail j =
      { s with store := fill cfg g s.store (s.x + cfg.r • s.w) tail j, j := j, t := s.t + j } := by
  intro j
  induction j with
  | zero =>
    intro _
    have hf : ∀ q, fill cfg g s.store q tail 0 = s.store := fun q => funext fun i => by simp [fill]
    rw [hf]
    cases s
    simp only at hj
    subst hj
    rfl
  | succ j ih =>
    intro hjM
    rw [run_succ, ih (by omega)]
    simp only [astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show j + 1 < cfg.M from hjM, ↓reduceIte, fill_succ]
    rfl

noncomputable def qhat (s : State E) (tail : ℕ → (Fin cfg.b → Ω) × E) : ℝ :=
  select cfg.M cfg.τq (fun c => ⟪s.w, fill cfg g s.store (s.x + cfg.r • s.w) tail cfg.M c - s.g0⟫ / cfg.r)

theorem run_ray_end (s : State E) (hd : s.done = false) (hph : s.ph = .ray) (hj : s.j = 0)
    (hM : 0 < cfg.M) (tail : ℕ → (Fin cfg.b → Ω) × E) :
    run (astep cfg d g) s tail cfg.M =
      if s.found = false ∧ cfg.r / 2 ≤ ‖s.v‖ ∧ qhat cfg g s tail ≤ -2 * cfg.θ then
        endAttempt cfg
          { s with
            store := fill cfg g s.store (s.x + cfg.r • s.w) tail cfg.M
            j := 0
            found := true
            dx := -(((if 0 ≤ ⟪s.g0, s.w⟫ then (1 : ℝ) else -1) * cfg.r) • s.w)
            t := s.t + cfg.M }
      else endAttempt cfg
          { s with
            store := fill cfg g s.store (s.x + cfg.r • s.w) tail cfg.M
            j := 0
            t := s.t + cfg.M } := by
  obtain ⟨m, hm⟩ : ∃ m, cfg.M = m + 1 := ⟨cfg.M - 1, by omega⟩
  have hpre := run_ray cfg d g s hd hph hj tail m (by omega)
  rw [hm, run_succ, hpre]
  simp only [qhat, astep, hd, Bool.false_eq_true, ↓reduceIte, stepBlock, blockUpdate, queryPoint, hph, show ¬ (m + 1 < cfg.M) by omega, ↓reduceIte, fill_succ]
  rw [Nat.add_assoc, ← hm]
  split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl

end LongTails.Proofs.GatedEscapePhases
