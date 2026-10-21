import LongTails.Proofs.Execution
import LongTails.Algorithms.Sgd
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

namespace OracleTemplate.StochasticGradient

def advance {State : Type*} (step : ℕ → State → State) : ℕ → ℕ → State → State
  | 0, _, state => state
  | K + 1, call, state => advance step K (call + 1) (step call state)

lemma execute_advance_of_answer {Query Reply Output : Type*} (O : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (response : ℕ → (Fin 1 × Query) → Reply)
    (h : ∀ history query, O.answer history query (ξ history.length) = response history.length query) :
    execute O A (fun _ => K) seed ξ =
      A.output (advance (fun k state => A.update state (response k (A.query state)))
        K 0 (A.initial seed)) := by
  rw [execute_indexed_of_answer O A K seed ξ response h]
  congr 1
  generalize A.initial seed = state
  generalize (0 : ℕ) = call
  induction K generalizing state call with
  | zero => rfl
  | succ K ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ _

lemma execute_advance_indexed {Query Reply Output : Type*}
    {Seed : ℕ → Type} [∀ k, MeasurableSpace (Seed k)]
    (law : MeasureTheory.ProbabilityMeasure ((k : ℕ) → Seed k))
    (answer : (k : ℕ) → (Fin 1 × Query) → Seed k → Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed) (ξ : (k : ℕ) → Seed k) :
    execute { Seed := Seed, law := law, answer := fun history query seed => answer history.length query seed }
      A (fun _ => K) seed ξ =
      A.output (advance (fun k state => A.update state (answer k (A.query state) (ξ k)))
        K 0 (A.initial seed)) := by
  rw [execute_indexed_of_answer _ _ _ _ _ (fun k query => answer k query (ξ k)) (fun _ _ => rfl)]
  congr 1
  generalize A.initial seed = state
  generalize (0 : ℕ) = call
  induction K generalizing state call with
  | zero => rfl
  | succ K ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ _

lemma execute_advance {Query Reply Output : Type*} {Ω : Type} [MeasurableSpace Ω]
    (law : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : Query → Ω → Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) seed => g x seed }
      A (fun _ => K) seed ξ =
      A.output (advance (fun k state => A.update state (g (A.query state).2 (ξ k)))
        K 0 (A.initial seed)) :=
  execute_advance_indexed law (fun _ query seed => g query.2 seed) A K seed ξ

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma advance_sgd (g : E → Ω → E) (η : ℝ) (x0 : E) (ξ : ℕ → Ω)
    (K call count : ℕ) (x sum : E) :
    advance (fun k state => (sgd η x0).update state (g ((sgd η x0).query state).2 (ξ k)))
      K call (count, x, sum) =
      (count + K, (run g η K x (fun i => ξ (call + i))).1,
        sum + (run g η K x (fun i => ξ (call + i))).2) := by
  dsimp only [sgd]
  induction K generalizing call count x sum with
  | zero => simp [advance, run]
  | succ K ih =>
    rw [advance]
    change advance _ K (call + 1) (count + 1, x - η • g x (ξ call), sum + x) = _
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc] using
      ih (call + 1) (count + 1) (x - η • g x (ξ call)) (sum + x)

lemma execute_sgd [MeasurableSpace Ω] (p : MeasureTheory.ProbabilityMeasure Ω)
    (g : E → Ω → E) (η : ℝ) (x0 : E) (K : ℕ) (hK : 0 < K) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := ⟨MeasureTheory.Measure.infinitePi (fun _ : ℕ =>
                (p : MeasureTheory.Measure Ω)), inferInstance⟩
              answer := fun _ (_, x) seed => g x seed } (sgd η x0) (fun _ => K) () ξ =
      (K : ℝ)⁻¹ • (run g η K x0 (fun i => ξ i)).2 := by
  erw [execute_advance]
  change (sgd η x0).output (advance _ K 0 (0, x0, 0)) = _
  erw [advance_sgd]
  simp [sgd, hK.ne']

end OracleTemplate.StochasticGradient
