import LongTailsOnline.Template
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LongTailsOnline.Setups.StochasticBandit

abbrev Arm (k : ℕ) := Fin (k + 1)

abbrev Sample (k : ℕ) := Arm k × ℕ → ℝ

abbrev Counts (k : ℕ) := Arm k → ℕ

abbrev Statistics (k : ℕ) := Counts k × (Arm k → ℝ)

noncomputable def empirical {k : ℕ} (w : Sample k) (i : Arm k) (n : ℕ) : ℝ :=
  (∑ s ∈ Finset.range n, w (i, s)) / n

@[fun_prop]
lemma measurable_empirical {k : ℕ} (i : Arm k) (n : ℕ) :
    Measurable (fun w : Sample k => empirical w i n) := by
  unfold empirical
  fun_prop

def increment {k : ℕ} (c : Counts k) (a : Arm k) : Counts k :=
  fun i => c i + if i = a then 1 else 0

def record {k : ℕ} (s : Statistics k) (a : Arm k) (r : ℝ) : Statistics k :=
  (increment s.1 a, fun i => s.2 i + if i = a then r else 0)

@[fun_prop]
lemma measurable_increment (k : ℕ) :
    Measurable (fun p : Counts k × Arm k => increment p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i |>.comp measurable_fst).add
    (measurable_const.ite (measurableSet_eq_fun measurable_const measurable_snd)
      measurable_const)

@[fun_prop]
lemma measurable_record (k : ℕ) :
    Measurable (fun p : Statistics k × Arm k × ℝ => record p.1 p.2.1 p.2.2) := by
  apply Measurable.prodMk
  · exact (measurable_increment k).comp
      (show Measurable (fun p : Statistics k × Arm k × ℝ => (p.1.1, p.2.1)) by fun_prop)
  · apply Measurable.of_eval
    intro i
    exact (show Measurable (fun p : Statistics k × Arm k × ℝ => p.1.2 i) by fun_prop).add
      (measurable_snd.snd.ite
        (measurableSet_eq_fun measurable_const
          (show Measurable (fun p : Statistics k × Arm k × ℝ => p.2.1) by fun_prop))
        measurable_const)

lemma measurable_eval_countable {α ι β : Type*} [MeasurableSpace α]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] [MeasurableSpace β]
    {f : α → ι → β} {i : α → ι} (hf : Measurable f) (hi : Measurable i) :
    Measurable (fun x => f x (i x)) := by
  have he : Measurable (fun p : (ι → β) × ι => p.1 p.2) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
  exact he.comp (hf.prodMk hi)

noncomputable abbrev environment {k : ℕ} (P : ProbabilityMeasure (Sample k)) :
    OnlineTemplate.Environment Unit (Arm k) ℝ Unit where
  State := Sample k × Counts k
  initial := ⟨(P : Measure (Sample k)).map (fun w => (w, fun _ => 0)),
    inferInstance⟩
  observe _ := Kernel.deterministic (fun s => ((), s)) (by fun_prop)
  respond _ := Kernel.deterministic
    (fun s => (s.1.1 (s.2.2, s.1.2 s.2.2), (),
      s.1.1, increment s.1.2 s.2.2)) (by
        apply Measurable.prodMk
        · apply measurable_eval_countable
          · fun_prop
          · apply Measurable.prodMk
            · fun_prop
            · apply measurable_eval_countable <;> fun_prop
        · fun_prop)

structure Params where
  k : ℕ
  T : ℕ
  μ : Arm k → ℝ
  best : Arm k

structure Sampling (p : Params) (P : ProbabilityMeasure (Sample p.k)) : Prop where
  independent : iIndepFun (fun q : Arm p.k × ℕ => fun w : Sample p.k => w q) P.toMeasure
  stationary : ∀ i n,
    P.toMeasure.map (fun w => w (i, n)) = P.toMeasure.map (fun w => w (i, 0))
  bounded : ∀ i n, ∀ᵐ w ∂P.toMeasure, w (i, n) ∈ Set.Icc (0 : ℝ) 1
  mean : ∀ i n, (∫ w, w (i, n) ∂P.toMeasure) = p.μ i

def gap (p : Params) (i : Arm p.k) : ℝ := p.μ p.best - p.μ i

def regret (p : Params)
    (h : OnlineTemplate.Trace Unit (Arm p.k) ℝ Unit p.T) : ℝ :=
  ∑ t, (p.μ p.best - p.μ (h t).2.1)

abbrev spec : OnlineTemplate.Setup where
  Params := Params
  Public := ℕ
  Instance k := ProbabilityMeasure (Sample k)
  Observation _ := Unit
  Action k := Arm k
  Feedback _ := ℝ
  Outcome _ := Unit
  Bound _ := ℝ
  publicInput := Params.k
  horizon := Params.T
  valid p := 0 < p.T ∧ (∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ i, p.μ i ≤ p.μ p.best
  admissible p P E := Sampling p P ∧ E = environment P
  successful p _ b law :=
    Integrable (regret p) law.toMeasure ∧
      (∫ h, regret p h ∂law.toMeasure) / p.T ≤ b

end LongTailsOnline.Setups.StochasticBandit
