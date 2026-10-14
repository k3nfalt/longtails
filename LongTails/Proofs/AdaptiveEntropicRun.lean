import LongTails.Proofs.AdaptiveEntropicMacro

open MeasureTheory

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma macroState_eq_advance (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (T : ℕ) :
    macroState q g ξ T =
      StochasticGradient.advance (fun k s => updateState q s (g (queryPoint q s) (ξ k)))
        (preload q + 2 * T) 0 (initialState q) := by
  have h := blockTrace_eq_advance q g (analysisCost q) (initialState q) ξ (preload q + T)
  rw [blockCalls_preload_pairs] at h
  exact h

lemma odd_call_output (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (T : ℕ) :
    (StochasticGradient.advance (fun k s => updateState q s (g (queryPoint q s) (ξ k)))
      (preload q + 2 * T + 1) 0 (initialState q)).y = (macroState q g ξ T).y := by
  rw [advance_add, Nat.zero_add, ← macroState_eq_advance]
  simp only [StochasticGradient.advance]
  exact primary_output q (macroState q g ξ T) _ (macroState_structure q g ξ T).2.1
    (macroState_structure q g ξ T).1

lemma remaining_calls_output (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (N : ℕ) (hN : preload q ≤ N) :
    (StochasticGradient.advance (fun k s => updateState q s (g (queryPoint q s) (ξ k)))
      N 0 (initialState q)).y = (macroState q g ξ ((N - preload q) / 2)).y := by
  have hr : (N - preload q) % 2 < 2 := Nat.mod_lt _ (by decide)
  have he : N = preload q + 2 * ((N - preload q) / 2) + (N - preload q) % 2 := by omega
  set T := (N - preload q) / 2 with hT
  have heT : N = preload q + 2 * T + (N - preload q) % 2 := by
    rw [hT]
    exact he
  by_cases hz : (N - preload q) % 2 = 0
  · rw [heT, hz, Nat.add_zero, ← macroState_eq_advance]
  · have ho : (N - preload q) % 2 = 1 := by omega
    rw [heT, ho]
    exact odd_call_output q g ξ _

lemma measurable_macro_output (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g)) (T : ℕ) :
    Measurable (fun ξ : ℕ → Ω => (macroState q g ξ T).y) := by
  have hm := (measurable_y q).comp ((measurable_advance q hg (preload q + 2 * T) 0).comp
    ((measurable_const : Measurable (fun _ : ℕ → Ω => initialState q)).prodMk measurable_id))
  convert hm using 1
  funext ξ
  rw [macroState_eq_advance]
  rfl

lemma execute_macro_output (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (P : ProbabilityMeasure (ℕ → Ω))
    (N : ℕ) (hN : preload q ≤ N) (ξ : ℕ → Ω) :
    (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed }
      (algorithm q) (fun _ => N) () ξ) = (macroState q g ξ ((N - preload q) / 2)).y := by
  erw [StochasticGradient.execute_advance]
  exact remaining_calls_output q g ξ N hN

end OracleTemplate.AdaptiveHeavyTailSimplex
