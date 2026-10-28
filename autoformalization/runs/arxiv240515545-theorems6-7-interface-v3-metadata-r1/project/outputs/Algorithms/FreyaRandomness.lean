import LongTails.Template
import outputs.Algorithms.FreyaInputs
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

namespace outputs.Algorithms.FreyaRandomness

abbrev ChoiceRow := (j : ℕ) → Fin (j + 1)

noncomputable def rowLaw : ProbabilityMeasure ChoiceRow :=
  ⟨Measure.infinitePi (fun j : ℕ => (PMF.uniformOfFintype (Fin (j + 1))).toMeasure),
    inferInstance⟩

noncomputable def choiceTapeLaw : ProbabilityMeasure (ℕ → ℕ → ChoiceRow) :=
  ⟨Measure.infinitePi (fun _ : ℕ =>
    Measure.infinitePi (fun _ : ℕ => (rowLaw : Measure ChoiceRow))), inferInstance⟩

noncomputable def refreshLaw (ρ : ℝ) : ProbabilityMeasure (ℕ → Bool) :=
  let p : unitInterval := Set.projIcc 0 1 zero_le_one ρ
  ⟨Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p), inferInstance⟩

abbrev Seed (K : ℕ) := (ℕ → ℕ → ChoiceRow) × (ℕ → Bool) × Fin (max 1 K)

noncomputable def seedLaw (ρ : ℝ) (K : ℕ) : ProbabilityMeasure (Seed K) := by
  haveI : NeZero (max 1 K) := ⟨by omega⟩
  exact ⟨(choiceTapeLaw : Measure _).prod
    ((refreshLaw ρ : Measure _).prod (PMF.uniformOfFintype (Fin (max 1 K))).toMeasure),
    inferInstance⟩

def chooseRemaining {α : Type*} (row : ChoiceRow) (remaining : List α) : Option α :=
  if h : remaining.length = 0 then none
  else
    let index := row (remaining.length - 1)
    some (remaining.get ⟨index.val, by have hi := index.isLt; omega⟩)

def labelAt (row : ChoiceRow) (m : ℕ) : Option (Fin m) :=
  if h : 0 < m then
    let index := row (m - 1)
    some ⟨index.val, by have hi := index.isLt; omega⟩
  else none

def refreshAt {K : ℕ} (seed : Seed K) (batch : ℕ) : Bool := seed.2.1 batch

def outputIndex {K : ℕ} (seed : Seed K) : Fin (max 1 K) := seed.2.2

end outputs.Algorithms.FreyaRandomness
