import LongTails.Setups.CyclicFullWidthPerceptron

open OracleTemplate

namespace LongTails.Algorithms.CyclicFullWidthPerceptron

open LongTails.Setups.CyclicFullWidthPerceptron

structure State (d n : ℕ) where
  point : Space d
  cursor : Fin (n + 1)

noncomputable def stepSize (p : Params) : ℝ := p.κ ^ 6 / 2 ^ 28

noncomputable def update {d n : ℕ} (η : ℝ) (s : State d n) (r : Reply d) : State d n :=
  ⟨if r.value ≤ 0 then move s.point η r.direction else s.point, finRotate (n + 1) s.cursor⟩

noncomputable def algorithm (p : Params) :
    Algorithm (Fin (p.count + 1) × Space p.dimension) (Reply p.dimension) (Space p.dimension) where
  State := State p.dimension p.count
  initial _ := ⟨initial p.dimension, 0⟩
  query s := (0, (s.cursor, s.point))
  update := update (stepSize p)
  output s := s.point

noncomputable def output (p : Params)
    (oracle : Oracle (Fin (p.count + 1) × Space p.dimension) (Reply p.dimension))
    (budget : ℕ) (seed : (k : ℕ) → oracle.Seed k) : Space p.dimension :=
  execute oracle (algorithm p) (fun _ => budget) () seed

lemma family_algorithm (p : Params) (hκ : 0 < p.κ) : family p (algorithm p) := by
  refine ⟨State.point, State.cursor, stepSize p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos (pow_pos hκ _) (by norm_num)
  · intro seed; exact ⟨rfl, rfl⟩
  · intro s; rfl
  · intro s r; rfl
  · intro s r; rfl
  · intro s; rfl

end LongTails.Algorithms.CyclicFullWidthPerceptron
