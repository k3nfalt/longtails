import LongTails.Algorithms.GuardedHessianTransport
import LongTails.Proofs.ExecutionHistory
import LongTails.Proofs.HeavyTailedTapeExecution
import LongTails.Proofs.HeavyTailedSospEpochIntegration
import Mathlib.Tactic

namespace LongTails.Proofs.GuardedHessianExecution

open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Setups.GeneralizedAffineHessianVector

def cycleCalls (c : Config) : ℕ := 1 + (c.groups + 1) * (c.guardBatch + 1)

def futureCalls (c : Config) (i : ℕ) : ℕ :=
  (c.steps - i) * cycleCalls c +
    (c.steps / (c.epoch + 1) - i / (c.epoch + 1)) * (c.resetBatch + 1)

def remainingCalls (p : Params) (c : Config) (s : State p c) : ℕ :=
  match s.phase with
  | .reset i _ => c.resetBatch + 1 - i + cycleCalls c + futureCalls c s.index
  | .transport => cycleCalls c + futureCalls c s.index
  | .guard j i _ _ =>
      (c.groups - j.val) * (c.guardBatch + 1) + c.guardBatch + 1 - i +
        futureCalls c s.index
  | .done => 0

def Valid (p : Params) (c : Config) (s : State p c) : Prop :=
  s.index ≤ c.steps ∧ match s.phase with
  | .reset i _ => i ≤ c.resetBatch
  | .guard _ i _ _ => i ≤ c.guardBatch
  | _ => True

lemma futureCalls_step (c : Config) {i : ℕ} (hi : i < c.steps) :
    futureCalls c i = cycleCalls c + futureCalls c (i + 1) +
      (if (i + 1) % (c.epoch + 1) = 0 then c.resetBatch + 1 else 0) := by
  have hdiv : (i + 1) / (c.epoch + 1) = i / (c.epoch + 1) +
      if (i + 1) % (c.epoch + 1) = 0 then 1 else 0 := by
    simpa only [Nat.dvd_iff_mod_eq_zero, Nat.succ_eq_add_one, Nat.add_comm] using
      (Nat.succ_div (a := i) (b := c.epoch + 1))
  have hiC := Nat.mul_le_mul_right (cycleCalls c) (show i + 1 ≤ c.steps by omega)
  have hiB := Nat.mul_le_mul_right (c.resetBatch + 1)
    (Nat.div_le_div_right (show i + 1 ≤ c.steps by omega) :
      (i + 1) / (c.epoch + 1) ≤ c.steps / (c.epoch + 1))
  unfold futureCalls
  simp only [Nat.sub_mul, Nat.add_mul, one_mul] at *
  split_ifs at hdiv ⊢ <;> simp_all [Nat.add_mul] <;> omega

lemma beginStep_remaining (p : Params) (c : Config) (s : State p c) :
    remainingCalls p c (beginStep p c s) = cycleCalls c + futureCalls c s.index := by
  rfl

lemma nextStep_remaining (p : Params) (c : Config) (s : State p c)
    (hi : s.index ≤ c.steps) :
    remainingCalls p c (nextStep p c s) = futureCalls c s.index := by
  unfold nextStep
  dsimp only
  split_ifs with hnext hreset
  · simp only [remainingCalls, Nat.sub_zero]
    have h := futureCalls_step c hnext
    rw [ite_eq_left hreset] at h
    omega
  · rw [beginStep_remaining]
    have h := futureCalls_step c hnext
    rw [ite_eq_right hreset] at h
    simpa using h.symm
  · have he : s.index = c.steps := by omega
    simp [remainingCalls, futureCalls, he]

lemma beginStep_valid (p : Params) (c : Config) (s : State p c)
    (hi : s.index ≤ c.steps) : Valid p c (beginStep p c s) := by
  exact ⟨hi, trivial⟩

lemma nextStep_valid (p : Params) (c : Config) (s : State p c)
    (hi : s.index ≤ c.steps) : Valid p c (nextStep p c s) := by
  unfold nextStep
  dsimp only
  split_ifs with hn hr
  · exact ⟨by dsimp; omega, Nat.zero_le _⟩
  · apply beginStep_valid
    dsimp
    omega
  · exact ⟨hi, trivial⟩


lemma update_valid (p : Params) (c : Config) (s : State p c) (u : ℝ) (r : Space p)
    (hs : Valid p c s) : Valid p c (update p c s u r) := by
  rcases hs with ⟨hi, hs⟩
  cases hp : s.phase with
  | reset i sum =>
      by_cases h : i < c.resetBatch
      · simp only [update, hp, ite_eq_left h, Valid]
        exact ⟨hi, by omega⟩
      · simp only [update, hp, ite_eq_right h]
        exact beginStep_valid p c _ hi
  | transport =>
      simp only [update, hp, Valid]
      exact ⟨hi, Nat.zero_le _⟩
  | guard j i sum values =>
      by_cases h : i < c.guardBatch
      · simp only [update, hp, ite_eq_left h, Valid]
        exact ⟨hi, by omega⟩
      · by_cases hj : j.val + 1 < c.groups + 1
        · simp only [update, hp, ite_eq_right h, dite_eq_left hj, Valid]
          exact ⟨hi, Nat.zero_le _⟩
        · simp only [update, hp, ite_eq_right h, dite_eq_right hj]
          exact nextStep_valid p c _ hi
  | done => simpa only [update, hp, Valid] using And.intro hi (by simp [hp] :
      match s.phase with
      | .reset i _ => i ≤ c.resetBatch
      | .guard _ i _ _ => i ≤ c.guardBatch
      | _ => True)

lemma update_remaining (p : Params) (c : Config) (s : State p c) (u : ℝ) (r : Space p)
    (hs : Valid p c s) :
    remainingCalls p c (update p c s u r) = remainingCalls p c s - 1 := by
  rcases hs with ⟨hi, hs⟩
  cases hp : s.phase with
  | reset i sum =>
      simp only [hp] at hs
      by_cases h : i < c.resetBatch
      · simp only [update, hp, ite_eq_left h, remainingCalls]
        omega
      · simp only [update, hp, ite_eq_right h, beginStep_remaining]
        simp only [remainingCalls, hp]
        omega
  | transport =>
      simp only [update, hp, remainingCalls, Fin.val_zero, Nat.sub_zero, cycleCalls, Nat.add_mul, one_mul]
      omega
  | guard j i sum values =>
      simp only [hp] at hs
      by_cases h : i < c.guardBatch
      · simp only [update, hp, ite_eq_left h, remainingCalls]
        omega
      · by_cases hj : j.val + 1 < c.groups + 1
        · simp only [update, hp, ite_eq_right h, dite_eq_left hj, remainingCalls, Nat.sub_zero]
          have hjle : j.val + 1 ≤ c.groups := by omega
          have hc := Nat.mul_le_mul_right (c.guardBatch + 1) hjle
          simp only [Nat.sub_mul, Nat.add_mul, one_mul] at *
          omega
        · simp only [update, hp, ite_eq_right h, dite_eq_right hj]
          rw [nextStep_remaining p c _]
          swap
          · exact hi
          simp only [remainingCalls, hp]
          have hjval : j.val = c.groups := by have := j.isLt; omega
          simp only [hjval, Nat.sub_self, zero_mul, zero_add]
          omega
  | done => simp [update, hp, remainingCalls]

lemma initial_remaining (p : Params) (c : Config) (seed : (trial p c).Seed) :
    remainingCalls p c ((trial p c).initial seed).value = trialCalls c := by
  simp only [trial, LongTails.Algorithms.HeavyTailedFreshTape.algorithm, remainingCalls, futureCalls,
    Nat.sub_zero, Nat.zero_div, cycleCalls, trialCalls, Nat.add_mul, one_mul]
  omega

lemma indexed_valid (p : Params) (c : Config)
    (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (seed : (trial p c).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    Valid p c (OracleTemplate.executeIndexedState O (trial p c) seed ξ n).1.value := by
  induction n with
  | zero => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ n ih => exact update_valid p c _ 0 _ ih

lemma indexed_remaining (p : Params) (c : Config)
    (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (seed : (trial p c).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    remainingCalls p c (OracleTemplate.executeIndexedState O (trial p c) seed ξ n).1.value =
      trialCalls c - n := by
  induction n with
  | zero => exact initial_remaining p c seed
  | succ n ih =>
      change remainingCalls p c (update p c _ 0 _) = _
      rw [update_remaining p c _ 0 _ (indexed_valid p c O seed ξ n), ih]
      omega

lemma remaining_zero_iff (p : Params) (c : Config) (s : State p c)
    (hs : Valid p c s) : remainingCalls p c s = 0 ↔ s.phase = .done := by
  rcases hs with ⟨_, hs⟩
  cases hp : s.phase <;> simp only [hp] at hs
  · simp [remainingCalls, hp, cycleCalls]
  · simp [remainingCalls, hp, cycleCalls]
  · simp [remainingCalls, hp]
    omega
  · simp [remainingCalls, hp]

lemma trial_finishes (p : Params) (c : Config)
    (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (seed : (trial p c).Seed) (ξ : (k : ℕ) → O.Seed k) :
    (OracleTemplate.executeIndexedState O (trial p c) seed ξ (trialCalls c)).1.value.phase =
      .done := by
  apply (remaining_zero_iff p c _ (indexed_valid p c O seed ξ _)).mp
  rw [indexed_remaining, Nat.sub_self]

lemma trial_trace_length (p : Params) (c : Config)
    (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (seed : (trial p c).Seed) (ξ : (k : ℕ) → O.Seed k) :
    (OracleTemplate.executeWithTrace O (trial p c) (fun _ => trialCalls c) seed ξ).2.length =
      trialCalls c := by
  rw [OracleTemplate.executeWithTrace_eq_executeIndexedState]
  exact OracleTemplate.executeIndexedState_length O (trial p c) seed ξ _

lemma trial_output_eq (p : Params) (c : Config)
    (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (seed : (trial p c).Seed) (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (trial p c) (fun _ => trialCalls c) seed ξ =
      let s := (OracleTemplate.executeIndexedState O (trial p c) seed ξ (trialCalls c)).1.value
      if s.alive then s.selected else p.x0 := by
  unfold OracleTemplate.execute
  rw [OracleTemplate.executeWithTrace_eq_executeIndexedState]
  rfl

def SameDynamics (p : Params) (c : Config) (s t : State p c) : Prop :=
  s.point = t.point ∧ s.estimate = t.estimate ∧ s.index = t.index ∧
    s.alive = t.alive ∧ s.phase = t.phase

lemma sameDynamics_query (p : Params) (c : Config) {s t : State p c}
    (h : SameDynamics p c s t) (u : ℝ) : query p c s u = query p c t u := by
  rcases s with ⟨x, e, i, target, selected, alive, phase⟩
  rcases t with ⟨x', e', i', target', selected', alive', phase'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

lemma sameDynamics_beginStep (p : Params) (c : Config) {s t : State p c}
    (h : SameDynamics p c s t) : SameDynamics p c (beginStep p c s) (beginStep p c t) := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

lemma sameDynamics_nextStep (p : Params) (c : Config) {s t : State p c}
    (h : SameDynamics p c s t) : SameDynamics p c (nextStep p c s) (nextStep p c t) := by
  rcases s with ⟨x, e, i, target, selected, alive, phase⟩
  rcases t with ⟨x', e', i', target', selected', alive', phase'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold nextStep
  dsimp only
  split_ifs <;> simp [SameDynamics, beginStep]

lemma sameDynamics_update (p : Params) (c : Config) {s t : State p c}
    (h : SameDynamics p c s t) (u : ℝ) (r : Space p) :
    SameDynamics p c (update p c s u r) (update p c t u r) := by
  rcases s with ⟨x, e, i, target, selected, alive, phase⟩
  rcases t with ⟨x', e', i', target', selected', alive', phase'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  cases phase <;> simp only [update]
  · split_ifs <;> simp [SameDynamics, beginStep]
  · simp [SameDynamics, displacement]
  · split_ifs <;> first
    | exact sameDynamics_nextStep p c (by simp [SameDynamics])
    | simp [SameDynamics]
  · simp [SameDynamics]

lemma sameDynamics_trajectory (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    {s t : State p c} (h : SameDynamics p c s t) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    SameDynamics p c
      (HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ)
      (HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n t ξ) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last,
        HeavyTailedProductProcess.trajectory_succ_last]
      rw [sameDynamics_query p c ih]
      exact sameDynamics_update p c ih _ _

lemma trial_execute_trajectory (p : Params) (c : Config)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → p.Ω))
    (answer : (Space p × Option (Space p)) → p.Ω → Space p)
    (target : Fin (c.steps + 1)) (tape : ℕ → ℝ) (ξ : ℕ → p.Ω) (K : ℕ) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ q ω => answer q.2 ω }
    OracleTemplate.execute O (trial p c) (fun _ => K) (target, tape) ξ =
      let s := HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × p.Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
        K (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c)
        (fun k => (tape k, ξ k))
      if s.alive then s.selected else p.x0 := by
  exact HeavyTailedTapeExecution.execute_fresh_tape _ _ _ _ _ _ _ _ _ _ _

lemma reset_prefix (p : Params) (c : Config) (s : State p c)
    (ξ : ℕ → Space p) (n : ℕ) (hn : n ≤ c.resetBatch) :
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      n { s with phase := .reset 0 0 } ξ =
      { s with phase := .reset n (∑ k ∈ Finset.range n, ξ k) } := by
  induction n with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last, ih (by omega)]
      simp only [update, show n < c.resetBatch by omega, ite_true, Finset.sum_range_succ]

lemma reset_block (p : Params) (c : Config) (s : State p c) (ξ : ℕ → Space p) :
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      (c.resetBatch + 1) { s with phase := .reset 0 0 } ξ =
      beginStep p c { s with
        phase := .reset c.resetBatch (∑ k ∈ Finset.range c.resetBatch, ξ k)
        estimate := if s.alive then ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ •
          ∑ k ∈ Finset.range (c.resetBatch + 1), ξ k else 0 } := by
  rw [HeavyTailedProductProcess.trajectory_succ_last, reset_prefix p c s ξ _ le_rfl]
  simp only [update, lt_self_iff_false, ite_false, Finset.sum_range_succ]

lemma guard_prefix (p : Params) (c : Config) (s : State p c)
    (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p)
    (ξ : ℕ → Space p) (n : ℕ) (hn : n ≤ c.guardBatch) :
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      n { s with phase := .guard j 0 0 values } ξ =
      { s with phase := .guard j n (∑ k ∈ Finset.range n, ξ k) values } := by
  induction n with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last, ih (by omega)]
      simp only [update, show n < c.guardBatch by omega, ite_true, Finset.sum_range_succ]

lemma guard_block (p : Params) (c : Config) (s : State p c)
    (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p) (ξ : ℕ → Space p) :
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      (c.guardBatch + 1) { s with phase := .guard j 0 0 values } ξ =
      let values' := Function.update values j
        (((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (c.guardBatch + 1), ξ k)
      if hj : j.val + 1 < c.groups + 1 then
        { s with phase := .guard ⟨j.val + 1, hj⟩ 0 0 values' }
      else
        let accepted := s.alive && decide
          (‖OracleTemplate.MultiplicativeRobustEstimator.medoid values'‖ ≤ c.threshold)
        nextStep p c { s with
          phase := .guard j c.guardBatch (∑ k ∈ Finset.range c.guardBatch, ξ k) values
          alive := accepted
          point := if accepted then s.point else p.x0
          selected := if accepted then s.selected else p.x0 } := by
  rw [HeavyTailedProductProcess.trajectory_succ_last, guard_prefix p c s j values ξ _ le_rfl]
  simp only [update, lt_self_iff_false, ite_false, Finset.sum_range_succ]

lemma prefix_values_update {E : Type*} [Zero E] {N j : ℕ} (hj : j < N) (V : Fin N → E) :
    Function.update (fun k : Fin N => if k.val < j then V k else 0) ⟨j, hj⟩ (V ⟨j, hj⟩) =
      (fun k : Fin N => if k.val < j + 1 then V k else 0) := by
  classical
  funext k
  by_cases he : k = ⟨j, hj⟩
  · subst k
    simp
  · have hv : k.val ≠ j := by intro h; apply he; exact Fin.ext h
    rw [Function.update_of_ne he]
    by_cases hk : k.val < j <;> simp [hk, show (k.val < j + 1) ↔ k.val < j by omega]

lemma guard_groups_prefix (p : Params) (c : Config) (s : State p c)
    (ξ : ℕ → Space p) (j : ℕ) (hj : j ≤ c.groups) :
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      (j * (c.guardBatch + 1)) { s with phase := .guard 0 0 0 (fun _ => 0) } ξ =
      { s with
        phase := .guard ⟨j, by omega⟩ 0 0
          (fun k => if k.val < j then ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ •
            ∑ l ∈ Finset.range (c.guardBatch + 1), ξ (k.val * (c.guardBatch + 1) + l) else 0) } := by
  induction j with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ j ih =>
      rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add, ih (by omega), guard_block]
      simp only [show j + 1 < c.groups + 1 by omega, dite_true]
      rw [prefix_values_update]

lemma nextStep_phase (p : Params) (c : Config) (s : State p c) (ph : Phase p c) :
    nextStep p c { s with phase := ph } = nextStep p c s := by
  unfold nextStep
  dsimp only
  split_ifs <;> rfl

lemma guard_pass (p : Params) (c : Config) (s : State p c) (ξ : ℕ → Space p) :
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } ξ =
      let values := fun j : Fin (c.groups + 1) => ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ l ∈ Finset.range (c.guardBatch + 1), ξ (j.val * (c.guardBatch + 1) + l)
      let accepted := s.alive && decide
        (‖OracleTemplate.MultiplicativeRobustEstimator.medoid values‖ ≤ c.threshold)
      nextStep p c { s with
        alive := accepted
        point := if accepted then s.point else p.x0
        selected := if accepted then s.selected else p.x0 } := by
  rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
    guard_groups_prefix p c s ξ c.groups le_rfl, guard_block]
  simp only [lt_self_iff_false, dite_false]
  rw [prefix_values_update]
  simp only [Fin.is_lt, ite_true]
  unfold nextStep
  dsimp only
  split_ifs <;> rfl

lemma fresh_guard_prefix (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) (hn : n ≤ c.guardBatch) :
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      n { s with phase := .guard j 0 0 values } ξ =
      { s with
        phase := .guard j n (∑ k ∈ Finset.range n, answer (s.point, none) (ξ k).2) values } := by
  induction n with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last, ih (by omega)]
      simp only [query, update, show n < c.guardBatch by omega, ite_true,
        Finset.sum_range_succ]

lemma fresh_guard_block (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p)
    (ξ : ℕ → ℝ × Ω) :
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (c.guardBatch + 1) { s with phase := .guard j 0 0 values } ξ =
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      (c.guardBatch + 1) { s with phase := .guard j 0 0 values }
      (fun k => answer (s.point, none) (ξ k).2) := by
  rw [HeavyTailedProductProcess.trajectory_succ_last,
    HeavyTailedProductProcess.trajectory_succ_last,
    fresh_guard_prefix p c s answer j values ξ _ le_rfl,
    guard_prefix p c s j values _ _ le_rfl]
  rfl

lemma fresh_guard_groups_prefix (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (j : ℕ) (hj : j ≤ c.groups) :
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (j * (c.guardBatch + 1)) { s with phase := .guard 0 0 0 (fun _ => 0) } ξ =
      { s with
        phase := .guard ⟨j, by omega⟩ 0 0
          (fun k => if k.val < j then ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ •
            ∑ l ∈ Finset.range (c.guardBatch + 1),
              answer (s.point, none) (ξ (k.val * (c.guardBatch + 1) + l)).2 else 0) } := by
  induction j with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ j ih =>
      rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
        ih (by omega), fresh_guard_block, guard_block]
      simp only [show j + 1 < c.groups + 1 by omega, dite_true]
      rw [prefix_values_update]

lemma fresh_guard_pass (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) :
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } ξ =
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) }
      (fun k => answer (s.point, none) (ξ k).2) := by
  rw [Nat.succ_mul]
  conv_lhs => rw [HeavyTailedSospEpochIntegration.trajectory_add]
  conv_rhs => rw [HeavyTailedSospEpochIntegration.trajectory_add]
  rw [fresh_guard_groups_prefix p c s answer ξ c.groups le_rfl,
    guard_groups_prefix p c s _ c.groups le_rfl, fresh_guard_block]

lemma nextStep_point (p : Params) (c : Config) (s : State p c) :
    (nextStep p c s).point = s.point := by
  unfold nextStep
  dsimp only
  split_ifs <;> rfl

lemma nextStep_alive (p : Params) (c : Config) (s : State p c) :
    (nextStep p c s).alive = s.alive := by
  unfold nextStep
  dsimp only
  split_ifs <;> rfl

lemma guard_pass_killed_gradient (p : Params) (c : Config) (s : State p c)
    (g : Space p → Space p) (ξ : ℕ → Space p) :
    let result := HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } ξ
    (if result.alive then ‖g result.point‖ ^ 2 else 0) =
      let values := fun j : Fin (c.groups + 1) => ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ l ∈ Finset.range (c.guardBatch + 1), ξ (j.val * (c.guardBatch + 1) + l)
      if s.alive && decide
          (‖OracleTemplate.MultiplicativeRobustEstimator.medoid values‖ ≤ c.threshold)
      then ‖g s.point‖ ^ 2 else 0 := by
  dsimp only
  rw [guard_pass]
  dsimp only
  rw [nextStep_point, nextStep_alive]
  dsimp only
  split_ifs <;> rfl

lemma fresh_reset_prefix (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) (hn : n ≤ c.resetBatch) :
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      n { s with phase := .reset 0 0 } ξ =
      { s with
        phase := .reset n (∑ k ∈ Finset.range n, answer (s.point, none) (ξ k).2) } := by
  induction n with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last, ih (by omega)]
      simp only [query, update, show n < c.resetBatch by omega, ite_true,
        Finset.sum_range_succ]

lemma fresh_reset_block (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) :
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (c.resetBatch + 1) { s with phase := .reset 0 0 } ξ =
    HeavyTailedProductProcess.trajectory (fun s r => update p c s 0 r)
      (c.resetBatch + 1) { s with phase := .reset 0 0 }
      (fun k => answer (s.point, none) (ξ k).2) := by
  rw [HeavyTailedProductProcess.trajectory_succ_last,
    HeavyTailedProductProcess.trajectory_succ_last,
    fresh_reset_prefix p c s answer ξ _ le_rfl,
    reset_prefix p c s _ _ le_rfl]
  rfl

lemma fresh_guard_pass_killed_gradient (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ξ : ℕ → ℝ × Ω) :
    let result := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } ξ
    (if result.alive then ‖g result.point‖ ^ 2 else 0) =
      let values := fun j : Fin (c.groups + 1) => ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ l ∈ Finset.range (c.guardBatch + 1),
          answer (s.point, none) (ξ (j.val * (c.guardBatch + 1) + l)).2
      if s.alive && decide
          (‖OracleTemplate.MultiplicativeRobustEstimator.medoid values‖ ≤ c.threshold)
      then ‖g s.point‖ ^ 2 else 0 := by
  dsimp only
  rw [fresh_guard_pass]
  exact guard_pass_killed_gradient p c s g _

lemma fresh_cycle_shape (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hs : s.phase = .transport) :
    let result := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (cycleCalls c) s ξ
    result.index = (if s.index < c.steps then s.index + 1 else s.index) ∧
      result.phase = if s.index < c.steps then
        if (s.index + 1) % (c.epoch + 1) = 0 then .reset 0 0 else .transport
        else .done := by
  dsimp only
  rw [cycleCalls, Nat.add_comm, HeavyTailedProductProcess.trajectory]
  have hu (u : ℝ) (r : Space p) : update p c s u r =
      { s with
        point := if s.alive then s.point + displacement p c s else p.x0
        estimate := if s.alive then s.estimate + r else 0
        phase := .guard 0 0 0 (fun _ => 0) } := by simp [update, hs]
  rw [hu]
  have hpass := fresh_guard_pass p c
    { s with
      point := if s.alive then s.point + displacement p c s else p.x0
      estimate := if s.alive then s.estimate + answer (query p c s (ξ 0).1) (ξ 0).2 else 0 }
    answer (fun k => ξ (k + 1))
  rw [guard_pass] at hpass
  rw [hpass]
  simp only [nextStep]
  split_ifs <;> simp [beginStep]

def transportTime (c : Config) (t : ℕ) : ℕ :=
  t * cycleCalls c + (t / (c.epoch + 1) + 1) * (c.resetBatch + 1)

lemma transportTime_zero (c : Config) : transportTime c 0 = c.resetBatch + 1 := by
  simp [transportTime]

lemma transportTime_succ (c : Config) (t : ℕ) :
    transportTime c (t + 1) = transportTime c t + cycleCalls c +
      (if (t + 1) % (c.epoch + 1) = 0 then c.resetBatch + 1 else 0) := by
  have hdiv : (t + 1) / (c.epoch + 1) = t / (c.epoch + 1) +
      if (t + 1) % (c.epoch + 1) = 0 then 1 else 0 := by
    simpa only [Nat.dvd_iff_mod_eq_zero, Nat.succ_eq_add_one, Nat.add_comm] using
      (Nat.succ_div (a := t) (b := c.epoch + 1))
  unfold transportTime
  rw [hdiv]
  split_ifs <;> simp [Nat.add_mul] <;> omega

lemma transportTime_final (c : Config) :
    transportTime c c.steps + cycleCalls c = trialCalls c := by
  simp only [transportTime, trialCalls, cycleCalls]
  ring

lemma fresh_reset_shape (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hs : s.phase = .reset 0 0) :
    let result := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (c.resetBatch + 1) s ξ
    result.index = s.index ∧ result.phase = .transport := by
  have he : { s with phase := .reset 0 0 } = s := by
    cases s
    simp_all
  have hh := fresh_reset_block p c s answer ξ
  rw [reset_block, he] at hh
  dsimp only
  rw [hh]
  exact ⟨rfl, rfl⟩

lemma transport_shape (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ) (ht : t ≤ c.steps) :
    let result := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (transportTime c t) (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    result.index = t ∧ result.phase = .transport := by
  let advance := fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)
  let initial : State p c := ⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩
  change (HeavyTailedProductProcess.trajectory advance (transportTime c t) initial ξ).index = t ∧
    (HeavyTailedProductProcess.trajectory advance (transportTime c t) initial ξ).phase = .transport
  induction t with
  | zero =>
      rw [transportTime_zero]
      exact fresh_reset_shape p c initial answer ξ rfl
  | succ t ih =>
      have hi := ih (by omega)
      let s := HeavyTailedProductProcess.trajectory advance (transportTime c t) initial ξ
      have hsi : s.index = t := hi.1
      have hc := fresh_cycle_shape p c s answer (fun k => ξ (transportTime c t + k)) hi.2
      have hcyc :
          (HeavyTailedProductProcess.trajectory advance
            (transportTime c t + cycleCalls c) initial ξ).index = t + 1 ∧
          (HeavyTailedProductProcess.trajectory advance
            (transportTime c t + cycleCalls c) initial ξ).phase =
              if (t + 1) % (c.epoch + 1) = 0 then .reset 0 0 else .transport := by
        rw [HeavyTailedSospEpochIntegration.trajectory_add]
        simpa only [hsi, show t < c.steps by omega, ite_true] using hc
      rw [transportTime_succ]
      by_cases hr : (t + 1) % (c.epoch + 1) = 0
      · rw [ite_eq_left hr, HeavyTailedSospEpochIntegration.trajectory_add]
        have hh := fresh_reset_shape p c
          (HeavyTailedProductProcess.trajectory advance
            (transportTime c t + cycleCalls c) initial ξ)
          answer (fun k => ξ (transportTime c t + cycleCalls c + k))
          (by simpa only [hr, ite_true] using hcyc.2)
        exact ⟨hh.1.trans hcyc.1, hh.2⟩
      · rw [ite_eq_right hr, Nat.add_zero]
        exact ⟨hcyc.1, by simpa only [hr, ite_false] using hcyc.2⟩

lemma fresh_reset_point_alive (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hs : s.phase = .reset 0 0) :
    let result := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (c.resetBatch + 1) s ξ
    (result.point, result.alive) = (s.point, s.alive) := by
  have he : { s with phase := .reset 0 0 } = s := by
    cases s
    simp_all
  have hh := fresh_reset_block p c s answer ξ
  rw [reset_block, he] at hh
  dsimp only
  rw [hh]
  rfl

lemma transport_next_point_alive (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ) (ht : t < c.steps) :
    let X := fun n => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      n (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    ((X (transportTime c (t + 1))).point, (X (transportTime c (t + 1))).alive) =
      ((X (transportTime c t + cycleCalls c)).point,
        (X (transportTime c t + cycleCalls c)).alive) := by
  dsimp only
  rw [transportTime_succ]
  by_cases hr : (t + 1) % (c.epoch + 1) = 0
  · rw [ite_eq_left hr, HeavyTailedSospEpochIntegration.trajectory_add]
    apply fresh_reset_point_alive
    rw [HeavyTailedSospEpochIntegration.trajectory_add]
    have hi := transport_shape p c answer target ξ t ht.le
    have hh := fresh_cycle_shape p c _ answer (fun k => ξ (transportTime c t + k)) hi.2
    simpa only [hi.1, ht, hr, ite_true] using hh.2
  · rw [ite_eq_right hr, Nat.add_zero]

lemma trajectory_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (hs : Valid p c s) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    Valid p c (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last]
      exact update_valid p c _ _ _ ih

lemma trajectory_remaining (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (hs : Valid p c s) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    remainingCalls p c (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ) =
      remainingCalls p c s - n := by
  induction n with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last,
        update_remaining p c _ _ _ (trajectory_valid p c answer s hs ξ n), ih]
      omega

lemma transportTime_remaining (c : Config) {i : ℕ} (hi : i ≤ c.steps) :
    transportTime c i + cycleCalls c + futureCalls c i = trialCalls c := by
  have hc := Nat.mul_le_mul_right (cycleCalls c) hi
  have hr := Nat.mul_le_mul_right (c.resetBatch + 1)
    (Nat.div_le_div_right hi : i / (c.epoch + 1) ≤ c.steps / (c.epoch + 1))
  change _ = (c.steps / (c.epoch + 1) + 1) * (c.resetBatch + 1) +
    (c.steps + 1) * cycleCalls c
  simp only [transportTime, futureCalls, Nat.sub_mul, Nat.add_mul, one_mul]
  omega

lemma trajectory_transport_time (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    let X := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      n (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    X.phase = .transport → n = transportTime c X.index := by
  let initial : State p c := ⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩
  let X := HeavyTailedProductProcess.trajectory
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n initial ξ
  change X.phase = .transport → n = transportTime c X.index
  intro hphase
  have hvalid : Valid p c initial := ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hv : Valid p c X := trajectory_valid p c answer initial hvalid ξ n
  have hr := trajectory_remaining p c answer initial hvalid ξ n
  have hinit : remainingCalls p c initial = trialCalls c :=
    initial_remaining p c (target, fun _ => 0)
  change remainingCalls p c X = remainingCalls p c initial - n at hr
  rw [hinit, remainingCalls, hphase] at hr
  have ht := transportTime_remaining c hv.1
  have hpos : 0 < cycleCalls c := by simp [cycleCalls]
  change n = transportTime c X.index
  dsimp only at hr
  omega

lemma transportTime_strictMono (c : Config) : StrictMono (transportTime c) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [transportTime_succ]
  have hc : 0 < cycleCalls c := by simp [cycleCalls]
  omega

lemma transport_calls_card (c : Config) (a b : ℕ) :
    ((Finset.Ico a b).image (transportTime c)).card = b - a := by
  rw [Finset.card_image_of_injective _ (transportTime_strictMono c).injective,
    Nat.card_Ico]

lemma sum_supported_transport_calls (c : Config) (a b n : ℕ) {F : ℕ → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hb : ∀ k ∈ (Finset.Ico a b).image (transportTime c), F k ≤ κ)
    (hz : ∀ k ∉ (Finset.Ico a b).image (transportTime c), F k = 0) :
    (∑ k ∈ Finset.range n, F k) ≤ (b - a : ℕ) * κ := by
  classical
  let S := (Finset.Ico a b).image (transportTime c)
  have heq : (∑ k ∈ Finset.range n, F k) =
      ∑ k ∈ (Finset.range n).filter (fun k => k ∈ S), F k := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    exact hz k (by simpa only [Finset.mem_filter, hk, true_and] using hnot)
  rw [heq]
  calc
    _ ≤ ∑ _k ∈ (Finset.range n).filter (fun k => k ∈ S), κ :=
      Finset.sum_le_sum (fun k hk => hb k (Finset.mem_filter.mp hk).2)
    _ ≤ ∑ _k ∈ S, κ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => (Finset.mem_filter.mp hk).2) (fun _ _ _ => hκ)
    _ = (b - a : ℕ) * κ := by simp [S, transport_calls_card]

lemma nextStep_estimate (p : Params) (c : Config) (s : State p c) :
    (nextStep p c s).estimate = s.estimate := by
  unfold nextStep
  dsimp only
  split_ifs <;> rfl

lemma update_alive (p : Params) (c : Config) (s : State p c) (u : ℝ) (r : Space p) :
    (update p c s u r).alive = true → s.alive = true := by
  cases hs : s.phase with
  | reset i sum => simp only [update, hs]; split_ifs <;> simp [beginStep]
  | transport => simp [update, hs]
  | guard j i sum values =>
      simp only [update, hs]
      split_ifs <;> simp [nextStep_alive, Bool.and_eq_true] <;> aesop
  | done => simp [update, hs]

lemma trajectory_alive_previous (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      n s ξ).alive = true → s.alive = true := by
  induction n generalizing s ξ with
  | zero => exact id
  | succ n ih =>
      exact fun h => update_alive p c s _ _ (ih _ _ h)

lemma update_transport (p : Params) (c : Config) (s : State p c)
    (hs : s.phase = .transport) (u : ℝ) (r : Space p) :
    update p c s u r = { s with
      point := if s.alive then s.point + displacement p c s else p.x0
      estimate := if s.alive then s.estimate + r else 0
      phase := .guard 0 0 0 (fun _ => 0) } := by simp [update, hs]

lemma fresh_cycle_estimate (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hs : s.phase = .transport) :
    (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (cycleCalls c) s ξ).estimate =
    if s.alive then s.estimate + answer (query p c s (ξ 0).1) (ξ 0).2 else 0 := by
  rw [cycleCalls, Nat.add_comm 1, HeavyTailedProductProcess.trajectory]
  rw [update_transport p c s hs]
  have hpass := fresh_guard_pass p c
    { s with
      point := if s.alive then s.point + displacement p c s else p.x0
      estimate := if s.alive then s.estimate + answer (query p c s (ξ 0).1) (ξ 0).2 else 0 }
    answer (fun k => ξ (k + 1))
  rw [guard_pass] at hpass
  rw [hpass, nextStep_estimate]

lemma fresh_cycle_alive_point (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hs : s.phase = .transport) :
    let result := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (cycleCalls c) s ξ
    result.alive = true → result.point = s.point + displacement p c s := by
  intro result ha
  have hsa := trajectory_alive_previous p c answer s ξ (cycleCalls c) ha
  dsimp only [result] at ha ⊢
  rw [cycleCalls, Nat.add_comm 1, HeavyTailedProductProcess.trajectory] at ha ⊢
  rw [update_transport p c s hs] at ha ⊢
  have hpass := fresh_guard_pass p c
    { s with
      point := if s.alive then s.point + displacement p c s else p.x0
      estimate := if s.alive then s.estimate + answer (query p c s (ξ 0).1) (ξ 0).2 else 0 }
    answer (fun k => ξ (k + 1))
  rw [guard_pass] at hpass
  rw [hpass, nextStep_point]
  rw [hpass, nextStep_alive] at ha
  dsimp only at ha ⊢
  rw [ite_eq_left ha, ite_eq_left hsa]

def resetTime (c : Config) (t : ℕ) : ℕ :=
  t * cycleCalls c + (t / (c.epoch + 1)) * (c.resetBatch + 1)

lemma resetTime_add_batch (c : Config) (t : ℕ) :
    resetTime c t + (c.resetBatch + 1) = transportTime c t := by
  simp only [resetTime, transportTime]
  ring

lemma resetTime_succ (c : Config) (t : ℕ) (hr : (t + 1) % (c.epoch + 1) = 0) :
    resetTime c (t + 1) = transportTime c t + cycleCalls c := by
  have h1 := resetTime_add_batch c (t + 1)
  have h2 := transportTime_succ c t
  rw [ite_eq_left hr] at h2
  omega

lemma reset_shape (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ)
    (ht : t ≤ c.steps) (hr : t % (c.epoch + 1) = 0) :
    let X := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (resetTime c t) (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    X.index = t ∧ X.phase = .reset 0 0 := by
  cases t with
  | zero => simp [resetTime, HeavyTailedProductProcess.trajectory]
  | succ t =>
      dsimp only
      rw [resetTime_succ c t hr, HeavyTailedSospEpochIntegration.trajectory_add]
      have hi := transport_shape p c answer target ξ t (by omega)
      have hh := fresh_cycle_shape p c _ answer (fun k => ξ (transportTime c t + k)) hi.2
      simpa only [hi.1, show t < c.steps by omega, hr, ↓reduceIte] using hh

lemma fresh_reset_estimate (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hs : s.phase = .reset 0 0) :
    (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (c.resetBatch + 1) s ξ).estimate =
      if s.alive then ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (c.resetBatch + 1), answer (s.point, none) (ξ k).2 else 0 := by
  have he : { s with phase := .reset 0 0 } = s := by cases s; simp_all
  have hh := fresh_reset_block p c s answer ξ
  rw [reset_block, he] at hh
  rw [hh]
  rfl

def TransportSelected (p : Params) (c : Config) (s : State p c) : Prop :=
  s.phase = .transport → s.index = s.target.val → s.selected = s.point

lemma beginStep_transportSelected (p : Params) (c : Config) (s : State p c) :
    TransportSelected p c (beginStep p c s) := by
  intro _ hi
  change s.index = s.target.val at hi
  simp only [beginStep, hi, ↓reduceIte]

lemma nextStep_transportSelected (p : Params) (c : Config) (s : State p c) :
    TransportSelected p c (nextStep p c s) := by
  unfold nextStep
  dsimp only
  split_ifs
  · intro hp
    contradiction
  · exact beginStep_transportSelected p c _
  · intro hp
    contradiction

lemma update_transportSelected (p : Params) (c : Config) (s : State p c) (u : ℝ) (r : Space p) :
    TransportSelected p c (update p c s u r) := by
  cases hp : s.phase <;> simp only [update, hp]
  · split_ifs <;> first
    | exact beginStep_transportSelected p c _
    | (intro h; contradiction)
  · intro h
    contradiction
  · split_ifs <;> first
    | exact nextStep_transportSelected p c _
    | (intro h; contradiction)
  · intro h
    simp only [hp] at h
    contradiction

lemma trajectory_transportSelected (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (s : State p c)
    (hs : TransportSelected p c s) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    TransportSelected p c (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ) := by
  cases n with
  | zero => exact hs
  | succ n =>
      rw [HeavyTailedProductProcess.trajectory_succ_last]
      exact update_transportSelected p c _ _ _

def Captured (p : Params) (c : Config) (s : State p c) : Prop :=
  match s.phase with
  | .reset _ _ => s.target.val < s.index
  | _ => s.target.val ≤ s.index

lemma nextStep_captured (p : Params) (c : Config) (s : State p c)
    (hs : s.target.val ≤ s.index) :
    Captured p c (nextStep p c s) ∧ (nextStep p c s).selected = s.selected := by
  have hi : s.index + 1 ≠ s.target.val := by omega
  unfold nextStep
  dsimp only
  split_ifs <;> simp [Captured, beginStep, hi] <;> omega

lemma update_captured (p : Params) (c : Config) (s : State p c) (u : ℝ) (r : Space p)
    (hs : Captured p c s) (ha : (update p c s u r).alive = true) :
    Captured p c (update p c s u r) ∧ (update p c s u r).selected = s.selected := by
  cases hp : s.phase with
  | reset i total =>
      have hlt : s.target.val < s.index := by simpa only [Captured, hp] using hs
      have hi : s.index ≠ s.target.val := by omega
      simp only [update, hp]
      split_ifs <;> simp [Captured, beginStep, hi] <;> omega
  | transport =>
      have hle : s.target.val ≤ s.index := by simpa only [Captured, hp] using hs
      simpa only [update, hp, Captured, and_true] using hle
  | guard j i total values =>
      have hle : s.target.val ≤ s.index := by simpa only [Captured, hp] using hs
      by_cases hi : i < c.guardBatch
      · simp only [update, hp, hi, ↓reduceIte, Captured]
        exact ⟨hle, trivial⟩
      by_cases hj : j.val + 1 < c.groups + 1
      · simp only [update, hp, hi, hj, ↓reduceIte, ↓reduceDIte, Captured]
        exact ⟨hle, trivial⟩
      simp only [update, hp, hi, hj, ↓reduceIte, ↓reduceDIte] at ha ⊢
      rw [nextStep_alive] at ha
      dsimp only at ha
      simp only [ha, ↓reduceIte]
      exact nextStep_captured p c _ hle
  | done => simpa only [update, hp] using And.intro hs (rfl : s.selected = s.selected)

lemma trajectory_captured (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (s : State p c)
    (hs : Captured p c s) (ξ : ℕ → ℝ × Ω) (n : ℕ)
    (ha : (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ).alive = true) :
    Captured p c (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ) ∧
    (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ).selected = s.selected := by
  induction n generalizing s ξ with
  | zero => exact ⟨hs, rfl⟩
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory] at ha ⊢
      have hu := trajectory_alive_previous p c answer _ (fun k => ξ (k + 1)) n ha
      have hc := update_captured p c s _ _ hs hu
      have hh := ih _ hc.1 _ ha
      exact ⟨hh.1, hh.2.trans hc.2⟩

lemma nextStep_target (p : Params) (c : Config) (s : State p c) :
    (nextStep p c s).target = s.target := by
  unfold nextStep
  dsimp only
  split_ifs <;> rfl

lemma update_target (p : Params) (c : Config) (s : State p c) (u : ℝ) (r : Space p) :
    (update p c s u r).target = s.target := by
  cases hp : s.phase <;> simp only [update, hp]
  all_goals first
    | rfl
    | (split_ifs <;> first | rfl | exact nextStep_target p c _)

lemma trajectory_target (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ).target = s.target := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last, update_target, ih]

lemma trial_selected_on_survival (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) :
    let X := fun n => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n
      (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    (X (trialCalls c)).alive = true →
      (X (trialCalls c)).selected = (X (transportTime c target.val)).point := by
  intro X ha
  have hshape := transport_shape p c answer target ξ target.val (by omega)
  have ht := trajectory_target p c answer
    (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ (transportTime c target.val)
  have hc : Captured p c (X (transportTime c target.val)) := by
    unfold Captured
    rw [hshape.2]
    exact le_of_eq (congrArg Fin.val ht |>.trans hshape.1.symm)
  have hselected := trajectory_transportSelected p c answer
    (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c)
    (by intro h; contradiction) ξ (transportTime c target.val)
  have hsel : (X (transportTime c target.val)).selected = (X (transportTime c target.val)).point :=
    hselected hshape.2 (hshape.1.trans (congrArg Fin.val ht).symm)
  have htime : transportTime c target.val ≤ trialCalls c := by
    have hh := transportTime_remaining c (show target.val ≤ c.steps by omega)
    omega
  have he : X (trialCalls c) = HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (trialCalls c - transportTime c target.val) (X (transportTime c target.val))
      (fun k => ξ (transportTime c target.val + k)) := by
    dsimp only [X]
    rw [← HeavyTailedSospEpochIntegration.trajectory_add, Nat.add_sub_of_le htime]
  rw [he] at ha ⊢
  exact (trajectory_captured p c answer _ hc _ _ ha).2.trans hsel

end LongTails.Proofs.GuardedHessianExecution
