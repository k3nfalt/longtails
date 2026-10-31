import LongTails.Algorithms.ValidatedHessianTransport
import LongTails.Proofs.GuardedHessianExecution

namespace LongTails.Proofs.ValidatedHessianExecution

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport (Config trialCalls)
open LongTails.Algorithms.ValidatedHessianTransport
open HeavyTailedProductProcess

lemma trialCalls_pos (c : Config) : 0 < trialCalls c := by
  unfold trialCalls
  positivity

noncomputable def step (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (z : ℝ × Ω) : State p c K :=
  update p c K B s z.1 (answer (query p c K B s z.1) z.2)

lemma update_count (p : Params) (c : Config) (K B : ℕ)
    (s : State p c K) (u : ℝ) (r : Space p) :
    (update p c K B s u r).count = s.count + 1 := by
  unfold update
  split_ifs <;> rfl

lemma trajectory_count (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    (trajectory (step p c K B answer) n s ξ).count = s.count + n := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih => rw [trajectory_succ_last]; simp only [step, update_count, ih]; omega

lemma block_index (c : Config) {j i : ℕ} (hi : i < trialCalls c) :
    (j * trialCalls c + i) / trialCalls c = j := by
  rw [Nat.mul_comm j, Nat.mul_add_div (trialCalls_pos c), Nat.div_eq_of_lt hi, add_zero]

lemma training_step (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (z : ℝ × Ω) (j : Fin K) {i : ℕ}
    (hi : i < trialCalls c) (hc : s.count = j.val * trialCalls c + i) :
    step p c K B answer s z =
      let next := LongTails.Algorithms.GuardedHessianTransport.update p c (s.trials j) z.1
        (answer (LongTails.Algorithms.GuardedHessianTransport.query p c (s.trials j) z.1) z.2)
      { s with trials := Function.update s.trials j next
               candidates := Function.update s.candidates j.succ
                 (if next.alive then next.selected else p.x0)
               count := s.count + 1 } := by
  have hd : s.count / trialCalls c = j.val := by rw [hc, block_index c hi]
  simp only [step, query, update, hd, j.isLt, ↓reduceDIte]

lemma training_trial (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j : Fin K)
    (hc : s.count = j.val * trialCalls c) (n : ℕ) (hn : n ≤ trialCalls c) :
    (trajectory (step p c K B answer) n s ξ).trials j =
      trajectory (fun t (z : ℝ × Ω) => LongTails.Algorithms.GuardedHessianTransport.update p c t z.1
        (answer (LongTails.Algorithms.GuardedHessianTransport.query p c t z.1) z.2)) n (s.trials j) ξ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ_last, training_step p c K B answer _ _ j (i := n) (by omega)
        (by rw [trajectory_count, hc])]
      simp only [Function.update_self]
      rw [trajectory_succ_last, ih (by omega)]

lemma training_other_trial (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j k : Fin K) (hjk : k ≠ j)
    (hc : s.count = j.val * trialCalls c) (n : ℕ) (hn : n ≤ trialCalls c) :
    (trajectory (step p c K B answer) n s ξ).trials k = s.trials k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ_last, training_step p c K B answer _ _ j (i := n) (by omega)
        (by rw [trajectory_count, hc])]
      simp only [Function.update_of_ne hjk]
      exact ih (by omega)

lemma training_candidate (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j : Fin K)
    (hc : s.count = j.val * trialCalls c) (n : ℕ) (hn : n < trialCalls c) :
    let t := trajectory (step p c K B answer) (n + 1) s ξ
    t.candidates j.succ = if (t.trials j).alive then (t.trials j).selected else p.x0 := by
  intro t
  dsimp only [t]
  have hh := training_step p c K B answer
    (trajectory (step p c K B answer) n s ξ) (ξ n) j (i := n) hn
    (by rw [trajectory_count, hc])
  simp only [trajectory_succ_last, hh, Function.update_self]

lemma training_other_candidate (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j : Fin K) (k : Fin (K + 1)) (hjk : k ≠ j.succ)
    (hc : s.count = j.val * trialCalls c) (n : ℕ) (hn : n ≤ trialCalls c) :
    (trajectory (step p c K B answer) n s ξ).candidates k = s.candidates k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ_last, training_step p c K B answer _ _ j (i := n) (by omega)
        (by rw [trajectory_count, hc])]
      simp only [Function.update_of_ne hjk]
      exact ih (by omega)

lemma training_sums (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j : Fin K)
    (hc : s.count = j.val * trialCalls c) (n : ℕ) (hn : n ≤ trialCalls c) :
    (trajectory (step p c K B answer) n s ξ).sums = s.sums := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ_last, training_step p c K B answer _ _ j (i := n) (by omega)
        (by rw [trajectory_count, hc])]
      exact ih (by omega)

lemma validation_step (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (z : ℝ × Ω) (j : Fin (K + 1)) {i : ℕ}
    (hB : 0 < B) (hi : i < B) (hc : s.count = K * trialCalls c + j.val * B + i) :
    step p c K B answer s z =
      { s with sums := Function.update s.sums j (s.sums j + answer (s.candidates j, none) z.2)
               count := s.count + 1 } := by
  have hnt : ¬ s.count / trialCalls c < K := by
    have hh : K * trialCalls c ≤ s.count := by rw [hc]; omega
    have hd := (Nat.le_div_iff_mul_le (trialCalls_pos c)).mpr hh
    omega
  have hd : (s.count - K * trialCalls c) / B = j.val := by
    rw [hc]
    have hh : K * trialCalls c + j.val * B + i - K * trialCalls c = j.val * B + i := by omega
    rw [hh, Nat.mul_comm j.val, Nat.mul_add_div hB, Nat.div_eq_of_lt hi, add_zero]
  simp only [step, query, update, hnt, ↓reduceDIte, hd, j.isLt]

lemma validation_candidates (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j : Fin (K + 1))
    (hB : 0 < B) (hc : s.count = K * trialCalls c + j.val * B)
    (n : ℕ) (hn : n ≤ B) :
    (trajectory (step p c K B answer) n s ξ).candidates = s.candidates := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ_last, validation_step p c K B answer _ _ j (i := n) hB (by omega)
        (by rw [trajectory_count, hc])]
      exact ih (by omega)

lemma validation_sum (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j : Fin (K + 1))
    (hB : 0 < B) (hc : s.count = K * trialCalls c + j.val * B)
    (n : ℕ) (hn : n ≤ B) :
    (trajectory (step p c K B answer) n s ξ).sums j = s.sums j +
      ∑ i ∈ Finset.range n, answer (s.candidates j, none) (ξ i).2 := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
      rw [trajectory_succ_last, validation_step p c K B answer _ _ j (i := n) hB (by omega)
        (by rw [trajectory_count, hc])]
      simp only [Function.update_self]
      rw [ih (by omega), validation_candidates p c K B answer s ξ j hB hc n (by omega),
        Finset.sum_range_succ, add_assoc]

lemma validation_other_sum (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (j k : Fin (K + 1)) (hjk : k ≠ j)
    (hB : 0 < B) (hc : s.count = K * trialCalls c + j.val * B)
    (n : ℕ) (hn : n ≤ B) :
    (trajectory (step p c K B answer) n s ξ).sums k = s.sums k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ_last, validation_step p c K B answer _ _ j (i := n) hB (by omega)
        (by rw [trajectory_count, hc])]
      simp only [Function.update_of_ne hjk]
      exact ih (by omega)

lemma future_trials (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (n : ℕ) (hn : n ≤ K) (k : Fin K) (hk : n ≤ k.val) :
    (trajectory (step p c K B answer) (n * trialCalls c) (initial p c K targets) ξ).trials k =
      (initial p c K targets).trials k := by
  induction n with
  | zero => simp [trajectory, initial]
  | succ n ih =>
      let j : Fin K := ⟨n, by omega⟩
      rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
        training_other_trial p c K B answer _ _ j k (by
          intro he
          have hh := congrArg Fin.val he
          dsimp [j] at hh
          omega) (by simp only [trajectory_count, initial, zero_add]; rfl) _ (le_refl _)]
      exact ih (by omega) (by omega)

lemma training_all_sums (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (n : ℕ) (hn : n ≤ K) :
    (trajectory (step p c K B answer) (n * trialCalls c) (initial p c K targets) ξ).sums =
      fun _ => 0 := by
  induction n with
  | zero => simp [trajectory, initial]
  | succ n ih =>
      let j : Fin K := ⟨n, by omega⟩
      rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
        training_sums p c K B answer _ _ j (by simp only [trajectory_count, initial, zero_add]; rfl) _ (le_refl _)]
      exact ih (by omega)

lemma training_fallback (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (n : ℕ) (hn : n ≤ K) :
    (trajectory (step p c K B answer) (n * trialCalls c) (initial p c K targets) ξ).candidates 0 =
      p.x0 := by
  induction n with
  | zero => simp [trajectory, initial]
  | succ n ih =>
      let j : Fin K := ⟨n, by omega⟩
      rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
        training_other_candidate p c K B answer _ _ j 0 (Ne.symm (Fin.succ_ne_zero j))
          (by simp only [trajectory_count, initial, zero_add]; rfl) _ (le_refl _)]
      exact ih (by omega)

lemma padding_step (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (z : ℝ × Ω) (hB : 0 < B) (hc : calls c K B ≤ s.count) :
    step p c K B answer s z = { s with count := s.count + 1 } := by
  have hnt : ¬ s.count / trialCalls c < K := by
    have hh : K * trialCalls c ≤ s.count := by unfold calls at hc; omega
    have hd := (Nat.le_div_iff_mul_le (trialCalls_pos c)).mpr hh
    omega
  have hnv : ¬ (s.count - K * trialCalls c) / B < K + 1 := by
    have hh : (K + 1) * B ≤ s.count - K * trialCalls c := by unfold calls at hc; omega
    have hd := (Nat.le_div_iff_mul_le hB).mpr hh
    omega
  simp only [step, update, hnt, hnv, ↓reduceDIte]

lemma padding_output (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (hB : 0 < B) (hc : calls c K B ≤ s.count)
    (n : ℕ) :
    output p c K B (trajectory (step p c K B answer) n s ξ) = output p c K B s := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
      rw [trajectory_succ_last, padding_step p c K B answer _ _ hB
        (by rw [trajectory_count]; omega)]
      exact ih

noncomputable def trialPoint (p : Params) (c : Config) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) : Space p :=
  let t := trajectory (fun t (z : ℝ × Ω) => LongTails.Algorithms.GuardedHessianTransport.update p c t z.1
    (answer (LongTails.Algorithms.GuardedHessianTransport.query p c t z.1) z.2))
    (trialCalls c) ⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ ξ
  if t.alive then t.selected else p.x0

lemma trial_endpoint (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (j : Fin K) :
    (trajectory (step p c K B answer) ((j.val + 1) * trialCalls c)
      (initial p c K targets) ξ).candidates j.succ =
    trialPoint p c answer (targets j) (fun i => ξ (j.val * trialCalls c + i)) := by
  let s := trajectory (step p c K B answer) (j.val * trialCalls c) (initial p c K targets) ξ
  let ζ := fun i => ξ (j.val * trialCalls c + i)
  have hc : s.count = j.val * trialCalls c := by simp [s, trajectory_count, initial]
  have hC := trialCalls_pos c
  have hh := training_candidate p c K B answer s ζ j hc (trialCalls c - 1) (by omega)
  have he : trialCalls c - 1 + 1 = trialCalls c := by omega
  simp only [he] at hh
  have ht := training_trial p c K B answer s ζ j hc (trialCalls c) (le_refl _)
  have hi : s.trials j = (initial p c K targets).trials j :=
    future_trials p c K B answer targets ξ j.val j.isLt.le j (le_refl _)
  rw [hi] at ht
  simp only [ht] at hh
  rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add]
  exact hh

lemma completed_candidate (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (n : ℕ) (hn : n ≤ K) (j : Fin K) (hj : j.val < n) :
    (trajectory (step p c K B answer) (n * trialCalls c) (initial p c K targets) ξ).candidates j.succ =
      trialPoint p c answer (targets j) (fun i => ξ (j.val * trialCalls c + i)) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases he : j.val = n
      · rw [← he]
        exact trial_endpoint p c K B answer targets ξ j
      · let k : Fin K := ⟨n, by omega⟩
        rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
          training_other_candidate p c K B answer _ _ k j.succ (by
            intro hh
            have hv := congrArg Fin.val hh
            dsimp [k] at hv
            omega) (by simp only [trajectory_count, initial, zero_add]; rfl) _ (le_refl _)]
        exact ih (by omega) (by omega)

lemma validation_all_candidates (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (hB : 0 < B) (hc : s.count = K * trialCalls c)
    (n : ℕ) (hn : n ≤ K + 1) :
    (trajectory (step p c K B answer) (n * B) s ξ).candidates = s.candidates := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
      let j : Fin (K + 1) := ⟨n, by omega⟩
      rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
        validation_candidates p c K B answer _ _ j hB
          (by rw [trajectory_count, hc]) _ (le_refl _)]
      exact ih (by omega)

lemma validation_future_sum (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (hB : 0 < B) (hc : s.count = K * trialCalls c)
    (n : ℕ) (hn : n ≤ K + 1) (k : Fin (K + 1)) (hk : n ≤ k.val) :
    (trajectory (step p c K B answer) (n * B) s ξ).sums k = s.sums k := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
      let j : Fin (K + 1) := ⟨n, by omega⟩
      rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
        validation_other_sum p c K B answer _ _ j k (by
          intro he
          have hh := congrArg Fin.val he
          dsimp [j] at hh
          omega) hB (by rw [trajectory_count, hc]) _ (le_refl _)]
      exact ih (by omega) (by omega)

lemma validation_endpoint (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (hB : 0 < B) (hc : s.count = K * trialCalls c)
    (j : Fin (K + 1)) :
    (trajectory (step p c K B answer) ((j.val + 1) * B) s ξ).sums j = s.sums j +
      ∑ i ∈ Finset.range B, answer (s.candidates j, none) (ξ (j.val * B + i)).2 := by
  rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
    validation_sum p c K B answer _ _ j hB (by rw [trajectory_count, hc]) _ (le_refl _),
    validation_future_sum p c K B answer s ξ hB hc j.val j.isLt.le j (le_refl _),
    validation_all_candidates p c K B answer s ξ hB hc j.val j.isLt.le]

lemma validation_completed_sum (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (hB : 0 < B) (hc : s.count = K * trialCalls c)
    (n : ℕ) (hn : n ≤ K + 1) (j : Fin (K + 1)) (hj : j.val < n) :
    (trajectory (step p c K B answer) (n * B) s ξ).sums j = s.sums j +
      ∑ i ∈ Finset.range B, answer (s.candidates j, none) (ξ (j.val * B + i)).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases he : j.val = n
      · rw [← he]
        exact validation_endpoint p c K B answer s ξ hB hc j
      · let k : Fin (K + 1) := ⟨n, by omega⟩
        rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add,
          validation_other_sum p c K B answer _ _ k j (by
            intro hh
            have hv := congrArg Fin.val hh
            dsimp [k] at hv
            omega) hB (by rw [trajectory_count, hc]) _ (le_refl _)]
        exact ih (by omega) (by omega)

lemma output_after_validation (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c K) (ξ : ℕ → ℝ × Ω) (hB : 0 < B) (hc : s.count = K * trialCalls c)
    (hs : s.sums = fun _ => 0) :
    output p c K B (trajectory (step p c K B answer) ((K + 1) * B) s ξ) =
      s.candidates (LongTails.Algorithms.GuardedHessianTransport.bestEstimate
        (fun j => (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
          answer (s.candidates j, none) (ξ (j.val * B + i)).2)) := by
  have hh : (trajectory (step p c K B answer) ((K + 1) * B) s ξ).sums =
      fun j => ∑ i ∈ Finset.range B, answer (s.candidates j, none) (ξ (j.val * B + i)).2 := by
    funext j
    simpa only [hs, zero_add] using
      validation_completed_sum p c K B answer s ξ hB hc (K + 1) (le_refl _) j j.isLt
  simp only [output, hh, validation_all_candidates p c K B answer s ξ hB hc (K + 1) (le_refl _)]

noncomputable def blockCandidates (p : Params) (c : Config) (K : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) : Fin (K + 1) → Space p :=
  Fin.cases p.x0 (fun j => trialPoint p c answer (targets j)
    (fun i => ξ (j.val * trialCalls c + i)))

lemma training_candidates (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) :
    (trajectory (step p c K B answer) (K * trialCalls c) (initial p c K targets) ξ).candidates =
      blockCandidates p c K answer targets ξ := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact training_fallback p c K B answer targets ξ K (le_refl _)
  · exact completed_candidate p c K B answer targets ξ K (le_refl _) k k.isLt

lemma output_representation (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (hB : 0 < B) :
    output p c K B (trajectory (step p c K B answer) (calls c K B) (initial p c K targets) ξ) =
      let candidates := blockCandidates p c K answer targets ξ
      candidates (LongTails.Algorithms.GuardedHessianTransport.bestEstimate
        (fun j => (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
          answer (candidates j, none) (ξ (K * trialCalls c + (j.val * B + i))).2)) := by
  rw [calls, HeavyTailedSospEpochIntegration.trajectory_add,
    output_after_validation p c K B answer _ _ hB
      (by simp [trajectory_count, initial]) (training_all_sums p c K B answer targets ξ K (le_refl _)),
    training_candidates]

lemma output_of_le (p : Params) (c : Config) (K B : ℕ) {Ω : Type*}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (hB : 0 < B) (N : ℕ) (hN : calls c K B ≤ N) :
    output p c K B (trajectory (step p c K B answer) N (initial p c K targets) ξ) =
      output p c K B (trajectory (step p c K B answer) (calls c K B) (initial p c K targets) ξ) := by
  have he : N = calls c K B + (N - calls c K B) := by omega
  conv_lhs => rw [he, HeavyTailedSospEpochIntegration.trajectory_add]
  exact padding_output p c K B answer _ _ hB (by simp [trajectory_count, initial]) _

lemma execute_wrapper (p : Params) (c : Config) (K B : ℕ) {Ω : Type}
    [MeasurableSpace Ω] (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (seed : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ)) (ξ : ℕ → Ω)
    (hB : 0 < B) (N : ℕ) (hN : calls c K B ≤ N) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ q ω => answer q.2 ω }
    OracleTemplate.execute O (algorithm p c K B) (fun _ => N) seed ξ =
      let ζ := fun k => (seed.2 k, ξ k)
      let candidates := blockCandidates p c K answer seed.1 ζ
      candidates (LongTails.Algorithms.GuardedHessianTransport.bestEstimate
        (fun j => (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
          answer (candidates j, none) (ξ (K * trialCalls c + (j.val * B + i))))) := by
  intro O
  have hh := HeavyTailedTapeExecution.execute_fresh_tape
    ⟨MeasureTheory.Measure.pi (fun _ : Fin K => (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure),
      inferInstance⟩ LongTails.Algorithms.GuardedHessianTransport.uniformLaw P
    (initial p c K) (query p c K B) (update p c K B) (output p c K B) answer seed ξ N
  change OracleTemplate.execute O (algorithm p c K B) (fun _ => N) seed ξ =
    output p c K B (trajectory (step p c K B answer) N
      (initial p c K seed.1) (fun k => (seed.2 k, ξ k))) at hh
  exact hh.trans ((output_of_le p c K B answer _ _ hB N hN).trans
    (output_representation p c K B answer _ _ hB))

end LongTails.Proofs.ValidatedHessianExecution
