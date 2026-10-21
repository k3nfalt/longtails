import LongTails.Template
import Mathlib.Tactic

open MeasureTheory

noncomputable section

namespace OracleTemplate.MultiOracleTests

def algorithm : Algorithm ℕ ℕ ℕ 2 where
  State := ℕ × ℕ
  initial _ := (0, 0)
  query s := if s.1 = 0 then (0, 7) else (1, s.2)
  update _ reply := (if reply = 0 then 0 else 1, reply)
  output := Prod.snd

def oracle : Oracle ℕ ℕ 2 where
  answer _ q _ := if q.1 = 0 then 2 * q.2 else q.2 + 1

theorem separate_budgets_output :
    execute oracle algorithm ![1, 1] () (fun _ => ()) = 15 := by decide

theorem zero_calls : execute oracle algorithm ![0, 0] () (fun _ => ()) = 0 := rfl

theorem exhausted_requested_oracle :
    execute oracle algorithm ![0, 3] () (fun _ => ()) = 0 := by decide

theorem other_oracle_continues :
    execute oracle algorithm ![1, 3] () (fun _ => ()) = 17 := by decide

def zeroOracle : Oracle ℕ ℕ 2 where
  answer _ _ _ := 0

theorem adaptive_calls :
    execute zeroOracle algorithm ![2, 3] () (fun _ => ()) = 0 := by decide

theorem ordered_trace :
    executeWithTrace oracle algorithm ![1, 1] () (fun _ => ()) =
      (15, [((0, 7), 14), ((1, 14), 15)]) := by decide

theorem empty_trace :
    executeWithTrace oracle algorithm ![0, 0] () (fun _ => ()) = (0, []) := rfl

theorem trace_stops_at_exhausted_oracle :
    executeWithTrace zeroOracle algorithm ![2, 3] () (fun _ => ()) =
      (0, [((0, 7), 0), ((0, 7), 0)]) := by decide

def stochasticOracle (P : ProbabilityMeasure (ℕ → Bool)) : Oracle ℕ ℕ 2 where
  Seed := fun _ => Bool
  law := P
  answer _ q seed := if q.1 = 0 then 2 * q.2 else if seed then q.2 + 1 else 0

theorem preserves_seed_index (P : ProbabilityMeasure (ℕ → Bool)) (ξ : ℕ → Bool) :
    execute (stochasticOracle P) algorithm ![1, 1] () ξ =
      if ξ 1 then 15 else 0 := rfl

abbrev spec : Setup where
  numOracles := 2
  Params := Unit
  Public := Unit
  Instance _ := Unit
  Query _ := ℕ
  Reply _ := ℕ
  Output _ := ℕ
  publicInput := id
  valid _ := True
  admissible _ _ O := O = oracle
  successful _ _ output _ := ∀ ω, output ω = 15
  allowedAlgorithm _ A := A = algorithm

theorem separate_budgets : Convergence spec (fun _ => ![1, 1]) := by
  refine ⟨fun _ => algorithm, ?_, fun _ _ => rfl⟩
  intro p _ I O hO
  change O = oracle at hO
  subst O
  change ∀ seed : Unit × (ℕ → Unit), execute oracle algorithm ![1, 1] seed.1 seed.2 = 15
  intro seed
  have hseed : seed = ((), fun _ => ()) := Subsingleton.elim _ _
  rw [hseed]
  exact separate_budgets_output

theorem insufficient_budget : ¬ Convergence spec (fun _ => ![0, 2]) := by
  rintro ⟨makeAlgorithm, hCorrect, hAllowed⟩
  have hA : makeAlgorithm = fun _ => algorithm := funext (fun p => hAllowed p True.intro)
  subst makeAlgorithm
  have h := hCorrect () True.intro () oracle rfl ((), fun _ => ())
  change (0 : ℕ) = 15 at h
  omega

abbrev traceSpec : Setup :=
  { spec with
    successful := fun _ _ _ _ => False
    successfulWithTrace := fun _ _ result _ =>
      ∀ ω, result ω = (15, [((0, 7), 14), ((1, 14), 15)]) }

theorem trace_success : Convergence traceSpec (fun _ => ![1, 1]) := by
  refine ⟨fun _ => algorithm, ?_, fun _ _ => rfl⟩
  intro p _ I O hO
  change O = oracle at hO
  subst O
  change ∀ seed : Unit × (ℕ → Unit),
    executeWithTrace oracle algorithm ![1, 1] seed.1 seed.2 =
      (15, [((0, 7), 14), ((1, 14), 15)])
  intro seed
  have hseed : seed = ((), fun _ => ()) := Subsingleton.elim _ _
  rw [hseed]
  exact ordered_trace

#print axioms separate_budgets
#print axioms insufficient_budget
#print axioms trace_success

end OracleTemplate.MultiOracleTests
