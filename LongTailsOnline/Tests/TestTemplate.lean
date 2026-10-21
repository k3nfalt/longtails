import LongTailsOnline.Template
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace OnlineTemplate.Tests

abbrev counterAlgorithm : Algorithm ℕ ℕ ℕ where
  State := ℕ
  initial := ⟨Measure.dirac 0, inferInstance⟩
  choose _ := Kernel.deterministic (fun s => (s.1 + s.2, s.1 + 100)) (by fun_prop)
  update _ := Kernel.deterministic (fun s => s.1 + s.2.2.2) (by fun_prop)

abbrev counterEnvironment : Environment ℕ ℕ ℕ ℕ where
  State := ℕ
  initial := ⟨Measure.dirac 1, inferInstance⟩
  observe _ := Kernel.deterministic (fun s => (s, s + 10)) (by fun_prop)
  respond _ := Kernel.deterministic
    (fun s => (s.2.2 + 1, s.1 + s.2.2, s.1 + 1)) (by fun_prop)

lemma counter_step (t : ℕ) (s : RunState counterAlgorithm counterEnvironment t) :
    step counterAlgorithm counterEnvironment t s =
      Measure.dirac (s.1 + 100 + (s.1 + s.2.1 + 1), s.2.1 + 11,
        Trace.append s.2.2 (s.2.1, s.1 + s.2.1,
          s.1 + s.2.1 + 1, s.2.1 + 10 + (s.1 + s.2.1))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_step _ _ _ _ _ hf]
  simp [counterAlgorithm, counterEnvironment, Kernel.deterministic_apply,
    lintegral_dirac' _ hf]

def counterHistory : Trace ℕ ℕ ℕ ℕ 2 :=
  ![(1, 1, 2, 12), (12, 114, 115, 136)]

lemma counter_two_rounds :
    (execute counterAlgorithm counterEnvironment 2).toMeasure =
      Measure.dirac counterHistory := by
  rw [execute_toMeasure]
  simp only [executionKernel_succ_apply, executionKernel_zero_apply]
  have hzero : ((counterAlgorithm.initial : Measure ℕ).prod
      (counterEnvironment.initial : Measure ℕ)).map
        (fun s => (s.1, s.2, fun i : Fin 0 => (Fin.elim0 i : Round ℕ ℕ ℕ ℕ))) =
      Measure.dirac (0, 1, fun i : Fin 0 => (Fin.elim0 i : Round ℕ ℕ ℕ ℕ)) := by
    change ((Measure.dirac (0 : ℕ)).prod (Measure.dirac (1 : ℕ))).map _ = _
    rw [Measure.dirac_prod_dirac, Measure.map_dirac' (by fun_prop)]
  rw [hzero]
  rw [Measure.dirac_bind (step _ _ _).measurable, counter_step,
    Measure.dirac_bind (step _ _ _).measurable, counter_step,
    Measure.map_dirac' (by fun_prop)]
  congr 1
  funext i
  fin_cases i <;> rfl

def fairCoin : ProbabilityMeasure Bool :=
  ⟨(1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true,
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩⟩

abbrev randomAlgorithm : Algorithm Unit Bool Unit where
  State := Unit
  initial := ⟨Measure.dirac (), inferInstance⟩
  choose _ := Kernel.const _ ((fairCoin : Measure Bool).map (fun b => (b, ())))
  update _ := Kernel.deterministic (fun _ => ()) measurable_const

abbrev hiddenEnvironment (hidden : Bool) : Environment Unit Bool Unit Bool where
  State := Unit
  initial := ⟨Measure.dirac (), inferInstance⟩
  observe _ := Kernel.deterministic (fun _ => ((), ())) measurable_const
  respond _ := Kernel.deterministic (fun _ => ((), hidden, ())) measurable_const

lemma random_action_unaffected_by_hidden_outcome (hidden : Bool)
    (s : RunState randomAlgorithm (hiddenEnvironment hidden) 0)
    (f : Bool → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f (z.2.2 0).2.1 ∂step randomAlgorithm (hiddenEnvironment hidden) 0 s =
      ∫⁻ b, f b ∂(fairCoin : Measure Bool) := by
  rw [lintegral_step _ _ _ _ _ (by fun_prop)]
  simp only [randomAlgorithm, hiddenEnvironment, Kernel.deterministic_apply,
    Kernel.const_apply]
  simp only [lintegral_dirac]
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  rfl

abbrev counterSpec : Setup where
  Params := Unit
  Public := Unit
  Instance _ := Unit
  Observation _ := ℕ
  Action _ := ℕ
  Feedback _ := ℕ
  Outcome _ := ℕ
  Bound _ := ℕ
  publicInput := id
  horizon _ := 2
  valid _ := True
  admissible _ _ E := E = counterEnvironment
  successful _ _ bound law := bound = 2 ∧ law.toMeasure = Measure.dirac counterHistory
  allowedAction _ observation action := observation ≤ action
  allowedAlgorithm _ A := A = counterAlgorithm

lemma counter_guarantee : Guarantee counterSpec (fun _ => counterAlgorithm) (fun _ => 2) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  rintro _ _ _ _ rfl
  refine ⟨?_, rfl, counter_two_rounds⟩
  change ∀ᵐ history ∂(execute counterAlgorithm counterEnvironment 2).toMeasure,
    ∀ t, (history t).1 ≤ (history t).2.1
  rw [counter_two_rounds]
  simp only [ae_dirac_eq, Filter.eventually_pure]
  intro t
  fin_cases t <;> decide

lemma counter_achievable : Achievable counterSpec (fun _ => 2) :=
  ⟨fun _ => counterAlgorithm, counter_guarantee⟩

lemma forbidden_algorithm_not_achievable :
    ¬ Achievable { counterSpec with allowedAlgorithm := fun _ _ => False } (fun _ => 2) := by
  rintro ⟨makeAlgorithm, h⟩
  exact h.1 () trivial

lemma forbidden_actions_not_achievable :
    ¬ Achievable { counterSpec with allowedAction := fun _ _ _ => False } (fun _ => 2) := by
  rintro ⟨makeAlgorithm, h⟩
  have ha := (h.2 () trivial () counterEnvironment rfl).1
  obtain ⟨history, hh⟩ := ha.exists
  exact hh 0

end OnlineTemplate.Tests
