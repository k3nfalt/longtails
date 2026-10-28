import LongTails.Template
import outputs.Algorithms.FreyaRandomness

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators

namespace outputs.Algorithms.FreyaSerial

open outputs.Proofs.FreyaModel outputs.Algorithms.FreyaInputs
open outputs.Algorithms.FreyaRandomness

inductive Phase where
  | full
  | firstDifference
  | secondDifference
  | halted

structure State (q : SerialRaw) where
  seed : Seed q.K
  iteration : ℕ
  x : Space q.d
  previous : Space q.d
  g : Space q.d
  selected : Space q.d
  sum : Space q.d
  first : Space q.d
  component : ℕ
  sample : ℕ
  phase : Phase

noncomputable def initial (q : SerialRaw) (seed : Seed q.K) : State q where
  seed := seed
  iteration := 0
  x := q.x0
  previous := q.x0
  g := 0
  selected := q.x0
  sum := 0
  first := 0
  component := 0
  sample := 0
  phase := if q.m = 0 ∨ q.K = 0 then .halted else .full

noncomputable def advance (q : SerialRaw) (s : State q) : State q :=
  if q.K ≤ s.iteration then { s with phase := .halted } else
    let x := s.x - q.η • s.g
    let batch := s.iteration + 1
    { s with
      iteration := batch
      x := x
      previous := s.x
      selected := if (outputIndex s.seed).val = batch then x else s.selected
      sum := 0
      first := 0
      component := 0
      sample := 0
      phase := if refreshAt s.seed s.iteration then .full else .firstDifference }

def query (q : SerialRaw) (s : State q) : Fin 1 × Option (Fin q.m × Space q.d) :=
  (0, match s.phase with
    | .halted => none
    | .full => if h : s.component < q.m then some (⟨s.component, h⟩, s.x) else none
    | .firstDifference =>
      (labelAt (s.seed.1 s.iteration s.sample) q.m).map fun i => (i, s.x)
    | .secondDifference =>
      (labelAt (s.seed.1 s.iteration s.sample) q.m).map fun i => (i, s.previous))

noncomputable def update (q : SerialRaw) (s : State q) (reply : Space q.d) : State q :=
  match s.phase with
  | .halted => s
  | .full =>
    let total := s.sum + reply
    if s.component + 1 < q.m then { s with sum := total, component := s.component + 1 }
    else advance q { s with g := (q.m : ℝ)⁻¹ • total }
  | .firstDifference => { s with first := reply, phase := .secondDifference }
  | .secondDifference =>
    let total := s.sum + (s.first - reply)
    if s.sample + 1 < q.S then
      { s with sum := total, sample := s.sample + 1, phase := .firstDifference }
    else advance q { s with g := s.g + (q.S : ℝ)⁻¹ • total }

def output (q : SerialRaw) (s : State q) : Space q.d := s.selected

noncomputable def algorithm (q : SerialRaw) :
    Algorithm (Option (Fin q.m × Space q.d)) (Space q.d) (Space q.d) 1 where
  Seed := Seed q.K
  law := seedLaw q.ρ q.K
  State := State q
  initial := initial q
  query := query q
  update := update q
  output := output q

abbrev CanonicalSeed (q : SerialRaw) :=
  (Fin q.K → Bool) × (Fin q.K → Fin q.S → Option (Fin q.m)) × Fin (max 1 q.K)

noncomputable def componentLaw (m : ℕ) : ProbabilityMeasure (Option (Fin m)) := by
  classical
  by_cases h : 0 < m
  · haveI : NeZero m := ⟨by omega⟩
    exact ⟨((PMF.uniformOfFintype (Fin m)).map some).toMeasure, inferInstance⟩
  · exact ⟨Measure.dirac none, inferInstance⟩

noncomputable def canonicalLaw (q : SerialRaw) : ProbabilityMeasure (CanonicalSeed q) := by
  haveI : NeZero (max 1 q.K) := ⟨by omega⟩
  let p : unitInterval := Set.projIcc 0 1 zero_le_one q.ρ
  exact ⟨(Measure.pi (fun _ : Fin q.K => bernoulliMeasure true false p)).prod
    ((Measure.pi (fun _ : Fin q.K =>
      Measure.pi (fun _ : Fin q.S => (componentLaw q.m : Measure (Option (Fin q.m)))))).prod
      (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure), inferInstance⟩

noncomputable def idealTrace (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
    (z : CanonicalSeed q) : ℕ → Space q.d × Space q.d
  | 0 => (q.x0, gradient (objective f) q.x0)
  | k + 1 =>
    let previous := idealTrace q f z k
    if h : k < q.K then
      let x := previous.1 - q.η • previous.2
      let g := if z.1 ⟨k, h⟩ then gradient (objective f) x else
        previous.2 + (q.S : ℝ)⁻¹ • ∑ j : Fin q.S,
          match z.2.1 ⟨k, h⟩ j with
          | none => 0
          | some i => gradient (f i) x - gradient (f i) previous.1
      (x, g)
    else previous

noncomputable def idealOutput (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
    (z : CanonicalSeed q) : Space q.d :=
  (idealTrace q f z z.2.2.val).1

end outputs.Algorithms.FreyaSerial
