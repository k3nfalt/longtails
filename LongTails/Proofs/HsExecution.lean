import LongTails.Template
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Proofs.HsExecution

open OracleTemplate

variable {Query Reply Output : Type*}

def stepTwo (A : Algorithm Query Reply Output 2) (ans : Fin 2 × Query → Reply)
    (c : A.State × (Fin 2 → ℕ) × Bool) : A.State × (Fin 2 → ℕ) × Bool :=
  if c.2.2 = true ∨ c.2.1 (A.query c.1).1 = 0 then (c.1, c.2.1, true)
  else (A.update c.1 (ans (A.query c.1)),
    Function.update c.2.1 (A.query c.1).1 (c.2.1 (A.query c.1).1 - 1), false)

lemma stepTwo_stopped (A : Algorithm Query Reply Output 2) (ans : Fin 2 × Query → Reply)
    (s : A.State) (r : Fin 2 → ℕ) (n : ℕ) :
    (stepTwo A ans)^[n] (s, r, true) = (s, r, true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have h : stepTwo A ans (s, r, true) = (s, r, true) := by
      simp [stepTwo]
    rw [h, ih]

lemma execute_two (O : Oracle Query Reply 2) (A : Algorithm Query Reply Output 2)
    (b : Fin 2 → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k) (ans : Fin 2 × Query → Reply)
    (h : ∀ history q, O.answer history q (ξ history.length) = ans q) (N : ℕ)
    (hN : b 0 + b 1 ≤ N) :
    execute O A b seed ξ =
      A.output ((stepTwo A ans)^[N] (A.initial seed, b, false)).1 := by
  unfold execute executeWithTrace
  rw [Fin.sum_univ_two]
  generalize hF : b 0 + b 1 = fuel
  rw [hF] at hN
  generalize A.initial seed = state
  generalize hc : ([] : List ((Fin 2 × Query) × Reply)) = history
  clear hc
  induction fuel generalizing state history b N with
  | zero =>
    have hb0 : ∀ i, b i = 0 := by
      intro i; fin_cases i <;> simp <;> omega
    rcases N with _ | N
    · rfl
    · rw [Function.iterate_succ_apply]
      have hs : stepTwo A ans (state, b, false) = (state, b, true) := by
        simp [stepTwo, hb0]
      rw [hs, stepTwo_stopped]
      rfl
  | succ fuel ih =>
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    by_cases hz : b (A.query state).1 = 0
    · have hs : stepTwo A ans (state, b, false) = (state, b, true) := by
        simp [stepTwo, hz]
      rw [hs, stepTwo_stopped]
      change (if b (A.query state).1 = 0 then (A.output state, history) else _).1 = _
      rw [ite_eq_left hz]
    · have hs : stepTwo A ans (state, b, false) =
          (A.update state (ans (A.query state)),
            Function.update b (A.query state).1 (b (A.query state).1 - 1), false) := by
        simp [stepTwo, hz]
      rw [hs]
      change (if b (A.query state).1 = 0 then (A.output state, history) else _).1 = _
      rw [ite_eq_right hz]
      dsimp only
      rw [h history (A.query state)]
      have hsum : Function.update b (A.query state).1 (b (A.query state).1 - 1) 0 +
          Function.update b (A.query state).1 (b (A.query state).1 - 1) 1 = fuel := by
        rcases Fin.exists_fin_two.mp ⟨(A.query state).1, rfl⟩ with hq | hq <;>
          simp only [hq, Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
            Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)] at hz ⊢ <;> omega
      apply ih
      all_goals first | exact hsum | omega

lemma const_success {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
    (g : Ω → ℝ) (c ε : ℝ) (hg : ∀ ω, g ω = c) (hc : c ≤ ε) :
    MeasureTheory.Integrable g (μ : MeasureTheory.Measure Ω) ∧
      ∫ ω, g ω ∂(μ : MeasureTheory.Measure Ω) ≤ ε := by
  have e : g = fun _ => c := funext hg
  subst e
  refine ⟨MeasureTheory.integrable_const c, ?_⟩
  rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  exact hc

lemma not_success_congr {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f g : Ω → ℝ) (ε : ℝ) (h : ∀ ω, f ω = g ω)
    (hg : ¬ (MeasureTheory.Integrable g μ ∧ ∫ ω, g ω ∂μ ≤ ε)) :
    ¬ (MeasureTheory.Integrable f μ ∧ ∫ ω, f ω ∂μ ≤ ε) := by
  have e : f = g := funext h
  subst e
  exact hg

end LongTails.Proofs.HsExecution
