import LongTails.Proofs.NoisyTwoSamplePerceptronDynamics
import LongTails.Proofs.Execution

open MeasureTheory OracleTemplate
open LongTails.Setups.FiniteLogisticTwoTap (Weights Reply signedInput answer Separates)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Algorithms.NoisyTwoSamplePerceptron

namespace LongTails.Proofs.NoisyTwoSamplePerceptronExecution

noncomputable def choice {d : ℕ} (μ : ℝ) (i : Fin d) (w : Weights d) : Option Bool := by
  classical
  exact if (answer (signedInput μ i false) w).margin ≤ 0 then some false else
    if (answer (signedInput μ i true) w).margin ≤ 0 then some true else none

noncomputable def move {d : ℕ} (μ η σ : ℝ) (i : Fin d) (w g : Weights d) (b : Bool) :=
  w + η • (answer (signedInput μ i b) w).direction + σ • g

noncomputable def point {d : ℕ} (μ η σ : ℝ) (i : Fin d) (x : Weights d) (g : ℕ → Weights d) :
    ℕ → Weights d
  | 0 => x
  | n+1 =>
    let w := point μ η σ i x g n
    match choice μ i w with
    | none => w
    | some b => move μ η σ i w (g n) b

lemma execute_pairs (p : Params) (η σ : ℝ) (i : Fin p.d)
    (O : Oracle (Bool × Weights p.d) (Reply p.d)) (hO : spec.admissible p i O)
    (g : ℕ → Weights p.d) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    execute O (algorithm p η σ) (fun _ => 2*n) g ξ = point p.μ η σ i p.x₀ g n := by
  let reply := fun q : Bool × Weights p.d => answer (signedInput p.μ i q.1) q.2
  erw [execute_eq_of_answer_eq O reply (fun k q s => hO.2 k (0,q) s),execute_iterate]
  let f := fun s : State p.d => update η σ s (reply (s.first.isSome,s.point))
  let X := point p.μ η σ i p.x₀ g
  have H : f^[2*n] ⟨p.x₀,none,0,g⟩ = ⟨X n,none,n,g⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ,Nat.add_comm (2*n) 2,Function.iterate_add_apply,ih]
      change f (f ⟨X n,none,n,g⟩) = _
      by_cases h₁ : (answer (signedInput p.μ i false) (X n)).margin ≤ 0
      · simp [f,reply,update,X,point,choice,move] at h₁ ⊢
        grind
      · by_cases h₂ : (answer (signedInput p.μ i true) (X n)).margin ≤ 0
        · simp [f,reply,update,X,point,choice,move] at h₁ h₂ ⊢
          grind
        · simp [f,reply,update,X,point,choice,move] at h₁ h₂ ⊢
          grind
  exact congrArg output H

lemma choice_none {d : ℕ} (μ : ℝ) (i : Fin d) (w : Weights d) :
    choice μ i w = none ↔ Separates μ i w := by
  simp [choice,Separates]
  grind

lemma choice_violated {d : ℕ} (μ : ℝ) (i : Fin d) (w : Weights d) (b : Bool)
    (h : choice μ i w = some b) : (answer (signedInput μ i b) w).margin ≤ 0 := by
  unfold choice at h
  split at h
  · cases h
    assumption
  · split at h
    · cases h
      assumption
    · contradiction

lemma remains_separated {d : ℕ} (μ η σ : ℝ) (i : Fin d) (x : Weights d) (g : ℕ → Weights d)
    (m n : ℕ) (hm : Separates μ i (point μ η σ i x g m)) :
    point μ η σ i x g (m+n) = point μ η σ i x g m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc,point,ih,(choice_none ..).mpr hm]

lemma point_congr {d : ℕ} (μ η σ : ℝ) (i : Fin d) (x : Weights d) (g g' : ℕ → Weights d)
    (n : ℕ) (h : ∀ k < n, g k = g' k) : point μ η σ i x g n = point μ η σ i x g' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [point,ih (fun k hk => h k (by omega)),h n (by omega)]

lemma point_measurable {d : ℕ} (μ η σ : ℝ) (i : Fin d) (x : Weights d) (n : ℕ) :
    Measurable (fun g => point μ η σ i x g n) := by
  classical
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let X := fun g => point μ η σ i x g n
    have hm (b : Bool) : Measurable (fun g => (answer (signedInput μ i b) (X g)).margin) := by
      dsimp [answer,X]
      fun_prop
    have hmove (b : Bool) : Measurable (fun g => move μ η σ i (X g) (g n) b) := by
      dsimp [move,answer,X]
      fun_prop
    let E := fun b : Bool => {g | (answer (signedInput μ i b) (X g)).margin ≤ 0}
    have hE (b : Bool) : MeasurableSet (E b) := measurableSet_le (hm b) measurable_const
    convert (hmove false).ite (hE false) ((hmove true).ite (hE true) ih) using 1
    ext1 g
    simp [point,choice,X]
    split_ifs <;> rfl
    all_goals infer_instance

end LongTails.Proofs.NoisyTwoSamplePerceptronExecution
