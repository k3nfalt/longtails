import LongTails.Proofs.Execution
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

noncomputable section

namespace OracleTemplate.TemplateTests

theorem execute_zero_steps {Q : Type u} {R : Type v} {O : Type w}
    (oracle : Oracle Q R) (A : Algorithm Q R O) (seed : A.Seed) (oracleSeed : (k : ℕ) → oracle.Seed k) :
    execute oracle A (fun _ => 0) seed oracleSeed = A.output (A.initial seed) := rfl

def constant (n : Nat) : Algorithm Unit Nat Nat where
  State := Unit
  initial _ := ()
  query _ := (0, ())
  update _ _ := ()
  output _ := n

def readOracle : Algorithm Unit Nat Nat where
  State := Nat
  initial _ := 0
  query _ := (0, ())
  update _ response := response
  output state := state

theorem read_oracle_zero_steps : execute { answer := fun _ (_, _) _ => 99 } readOracle (fun _ => 0) = 0 := rfl
theorem read_oracle_one_step : execute { answer := fun _ (_, _) _ => 99 } readOracle (fun _ => 1) = 99 := by
  rfl
theorem read_oracle_multiple_steps : execute { answer := fun _ (_, _) _ => 99 } readOracle (fun _ => 3) = 99 := by
  rfl
theorem constant_ignores_replies : execute { answer := fun _ (_, _) _ => 99 } (constant 7) (fun _ => 3) = 7 := by
  rfl

def adaptive : Algorithm Nat Bool (List Nat) where
  State := Nat × List Nat
  initial _ := (2, [])
  query state := (0, state.1 + 1)
  update state reply :=
    (if reply then 2 * state.1 else state.1 + 1, state.1 :: state.2)
  output state := state.1 :: state.2

theorem adaptive_zero_steps : execute { answer := fun _ (_, q) _ => decide (q < 5) } adaptive (fun _ => 0) = [2] := rfl
theorem adaptive_one_step : execute { answer := fun _ (_, q) _ => decide (q < 5) } adaptive (fun _ => 1) = [4, 2] := by
  rfl
theorem adaptive_mixed_replies :
    execute { answer := fun _ (_, q) _ => decide (q < 5) } adaptive (fun _ => 3) = [6, 5, 4, 2] := by
  rfl
theorem adaptive_false_replies : execute { answer := fun _ (_, _) _ => false } adaptive (fun _ => 3) = [5, 4, 3, 2] := by
  rfl

@[reducible] def spec : Setup where
  Params := Unit
  Public := Unit
  Instance := (fun _ => Nat)
  Query := (fun _ => Unit)
  Reply := (fun _ => Nat)
  Output := (fun _ => Nat)
  publicInput _ := ()
  valid _ := True
  admissible _ hidden oracle := ∀ k seed, oracle.answer k (0, ()) seed = hidden
  successful _ hidden output P := ∀ᵐ ω ∂(P : Measure _), output ω = hidden

theorem one_query_solves : Convergence spec (fun _ _ => 1) := by
  refine ⟨fun _ => readOracle, ?_, fun _ _ => trivial⟩
  intro p hp hidden oracle h
  exact Filter.Eventually.of_forall (fun seed => h 0 (seed.2 0))

theorem restriction_applies_to_successful_algorithm :
    ¬ Convergence { spec with allowedAlgorithm := fun _ A => A = constant 0 } (fun _ _ => 1) := by
  rintro ⟨makeAlgorithm, hCorrect, hAllowed⟩
  have hA : makeAlgorithm = fun _ => constant 0 := funext (fun p => hAllowed p True.intro)
  subst makeAlgorithm
  have h := (hCorrect () trivial
    1 { answer := fun _ _ _ => 1 } (fun _ _ => rfl))
  change ∀ᵐ seed : Unit × (ℕ → Unit)
      ∂((Measure.dirac ()).prod (Measure.dirac (fun _ : ℕ => ()))),
    (execute { answer := fun _ _ _ => (1 : ℕ) } (constant 0)
      (fun _ => 1) seed.1 seed.2) = 1 at h
  obtain ⟨seed, hseed⟩ := h.exists
  have hz : (execute { answer := fun _ _ _ => (1 : ℕ) } (constant 0)
      (fun _ => 1) seed.1 seed.2) = 0 := by
    have hs : seed = ((), fun _ => ()) := Subsingleton.elim _ _
    rw [hs]
    erw [execute_iterate (fun _ : Unit => (1 : ℕ))]
    rfl
  exact Nat.zero_ne_one (hz.symm.trans hseed)

theorem no_uniform_zero_query : ¬ Convergence spec (fun _ _ => 0) := by
  rintro ⟨makeAlgorithm, hCorrect, _⟩
  have h0 := hCorrect () trivial
    0 { answer := fun _ _ _ => 0 } (fun _ _ => rfl)
  have h1 := hCorrect () trivial
    1 { answer := fun _ _ _ => 1 } (fun _ _ => rfl)
  simp only [ProbabilityMeasure.coe_mk] at h0 h1
  obtain ⟨seed, hs0, hs1⟩ := (h0.and h1).exists
  exact Nat.zero_ne_one (hs0.symm.trans hs1)

theorem reversed_quantifiers :
    ∀ hidden : Nat, ∃ A : Algorithm Unit Nat Nat,
      ∀ oracle, spec.admissible () hidden oracle →
        let result := fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) => execute oracle A (fun _ => 0) seed.1 seed.2
        spec.successful () hidden (fun seed => (result seed))
            ⟨(A.law : Measure _).prod (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩ := by
  intro hidden
  refine ⟨constant hidden, ?_⟩
  intro oracle _
  exact Filter.Eventually.of_forall (fun _ => rfl)

@[reducible] def publicParamSpec : Setup where
  Params := Nat
  Public := Nat
  Instance := (fun _ => Unit)
  Query := (fun _ => Unit)
  Reply := (fun _ => Nat)
  Output := (fun _ => Nat)
  publicInput p := p
  valid _ := True
  admissible _ _ oracle := ∀ k seed, oracle.answer k (0, ()) seed = 0
  successful p _ output P := ∀ᵐ ω ∂(P : Measure _), output ω = p

theorem can_read_public_parameter :
    Convergence publicParamSpec (fun _ _ => 0) := by
  refine ⟨constant, ?_, fun _ _ => trivial⟩
  intro p hp I oracle hI
  exact Filter.Eventually.of_forall (fun _ => rfl)

@[reducible] def dependentSpec : Setup where
  Params := Nat
  Public := Nat
  Instance := (fun _ => Unit)
  Query := (fun n => Fin (n + 1))
  Reply := (fun n => Fin (n + 1))
  Output := (fun n => Fin (n + 1))
  publicInput := id
  valid _ := True
  admissible _ _ _ := True
  successful p _ output P := ∀ᵐ ω ∂(P : Measure _), (output ω).val = p

theorem can_use_parameter_dependent_types : Convergence dependentSpec (fun _ _ => 0) := by
  refine ⟨fun n => {
    State := Fin (n + 1)
    initial _ := ⟨n, Nat.lt_succ_self n⟩
    query := fun state => (0, state)
    update _ reply := reply
    output := id }, ?_, fun _ _ => trivial⟩
  intro p hp I oracle hI
  exact Filter.Eventually.of_forall (fun _ => rfl)

@[reducible] def hiddenParamSpec : Setup where
  Params := Nat
  Public := Unit
  Instance := (fun _ => Unit)
  Query := (fun _ => Unit)
  Reply := (fun _ => Nat)
  Output := (fun _ => Nat)
  publicInput _ := ()
  valid _ := True
  admissible _ _ oracle := ∀ k seed, oracle.answer k (0, ()) seed = 0
  successful p _ output P := ∀ᵐ ω ∂(P : Measure _), output ω = p

theorem cannot_read_hidden_parameter (budget : Nat → Fin 1 → Nat)
    (hbudget : budget 0 = budget 1) : ¬ Convergence hiddenParamSpec budget := by
  rintro ⟨makeAlgorithm, hCorrect, _⟩
  have h0 := hCorrect 0 trivial () { answer := fun _ _ _ => 0 } (fun _ _ => rfl)
  have h1 := hCorrect 1 trivial () { answer := fun _ _ _ => 0 } (fun _ _ => rfl)
  simp only [hiddenParamSpec, hbudget, ProbabilityMeasure.coe_mk] at h0 h1
  obtain ⟨seed, h0, h1⟩ := (h0.and h1).exists
  exact Nat.zero_ne_one (h0.symm.trans h1)

theorem valid_restricts_parameters :
    Convergence { hiddenParamSpec with valid := fun p => p = 0 } (fun _ _ => 0) := by
  refine ⟨fun _ => constant 0, ?_, fun _ _ => trivial⟩
  intro p hp I oracle hI
  exact Filter.Eventually.of_forall (fun _ => hp.symm)

def fairCoin : ProbabilityMeasure Bool :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac false + (1 / 2 : ENNReal) • Measure.dirac true,
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩⟩

def guess : Algorithm Unit Bool Bool where
  Seed := Bool
  law := fairCoin
  State := Bool
  initial seed := seed
  query _ := (0, ())
  update state _ := state
  output state := state

@[reducible] def guessingSpec : Setup where
  Params := Unit
  Public := Unit
  Instance := (fun _ => Bool)
  Query := (fun _ => Unit)
  Reply := (fun _ => Bool)
  Output := (fun _ => Bool)
  publicInput _ := ()
  valid _ := True
  admissible _ _ _ := True
  successful _ hidden output P :=
    Measurable output ∧ (1 / 2 : ENNReal) ≤ (P : Measure _) {ω | output ω = hidden}

theorem randomized_zero_query_guess : Convergence guessingSpec (fun _ _ => 0) := by
  refine ⟨fun _ => guess, ?_, fun _ _ => trivial⟩
  intro p hp hidden oracle h
  refine ⟨measurable_fst, ?_⟩
  change (1 / 2 : ENNReal) ≤
    ((fairCoin : Measure Bool).prod (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) {ω | ω.1 = hidden}
  have hs : {ω : Bool × ((k : ℕ) → oracle.Seed k) | ω.1 = hidden} = {hidden} ×ˢ Set.univ := by
    ext ω
    simp
  rw [hs, Measure.prod_prod]
  cases hidden <;> simp [fairCoin]

@[reducible] def expectedSpec : Setup where
  Params := Unit
  Public := Unit
  Instance := (fun _ => Bool)
  Query := (fun _ => Unit)
  Reply := (fun _ => Bool)
  Output := (fun _ => Bool)
  publicInput _ := ()
  valid _ := True
  admissible _ _ _ := True
  successful _ _ output P :=
    Integrable (fun ω => if output ω then (1 : ℝ) else 0) (P : Measure _) ∧
      (∫ ω, if output ω then (1 : ℝ) else 0 ∂(P : Measure _)) = 1 / 2

theorem randomized_expected_output : Convergence expectedSpec (fun _ _ => 0) := by
  refine ⟨fun _ => guess, ?_, fun _ _ => trivial⟩
  intro p hp hidden oracle h
  refine ⟨?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun ω : Bool => if ω then (1 : ℝ) else 0)
        (μ := (fairCoin : Measure Bool)))
  change (∫ ω : Bool × ((k : ℕ) → oracle.Seed k), if ω.1 then (1 : ℝ) else 0
    ∂(fairCoin : Measure Bool).prod (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) = 1 / 2
  rw [integral_fun_fst (fun ω : Bool => if ω then (1 : ℝ) else 0)]
  simp only [probReal_univ, one_smul, fairCoin, ProbabilityMeasure.coe_mk]
  rw [integral_add_measure
    (Integrable.of_finite.smul_measure (by norm_num))
    (Integrable.of_finite.smul_measure (by norm_num))]
  norm_num [integral_smul_measure, integral_dirac]

def alternatingCoin : Oracle Unit Bool where
  Seed := fun _ => Bool
  law := ⟨(1 / 2 : ENNReal) • Measure.dirac (fun _ => false) +
    (1 / 2 : ENNReal) • Measure.dirac (fun _ => true),
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩⟩
  answer := fun k (_, _) seed => if k % 2 = 0 then seed else !seed

def readCoin : Algorithm Unit Bool Bool where
  State := Bool
  initial _ := false
  query _ := (0, ())
  update _ reply := reply
  output state := state

theorem random_oracle_first_call :
    execute alternatingCoin readCoin (fun _ => 1) () (fun _ => true) = true := by
  rfl

theorem random_oracle_next_call :
    execute alternatingCoin readCoin (fun _ => 2) () (fun _ => true) = false := by
  rfl

theorem oracle_samples_can_be_dependent :
    (alternatingCoin.law : Measure ((k : ℕ) → alternatingCoin.Seed k)) {ξ | ξ 0 = ξ 1} = 1 := by
  unfold alternatingCoin
  simp [ProbabilityMeasure.coe_mk, ENNReal.inv_two_add_inv_two]

def indexedOracle : Oracle Unit Nat where
  Seed := fun k => Fin (k + 1)
  law := ⟨Measure.dirac (fun k => (0 : Fin (k + 1))), inferInstance⟩
  answer := fun _ (_, _) seed => seed.val

theorem execution_consumes_indexed_seeds :
    execute indexedOracle readOracle (fun _ => 3) () (fun k => ⟨k, Nat.lt_succ_self k⟩) = 2 := by
  rfl

def xorGuess : Algorithm Unit Bool Bool :=
  { guess with update := fun state reply => Bool.xor state reply }

@[reducible] def independentSpec : Setup where
  Params := Unit
  Public := Unit
  Instance := (fun _ => Unit)
  Query := (fun _ => Unit)
  Reply := (fun _ => Bool)
  Output := (fun _ => Bool)
  publicInput _ := ()
  valid _ := True
  admissible _ _ oracle := oracle = alternatingCoin
  successful _ _ output P :=
    Measurable output ∧ (P : Measure _) {ω | output ω = true} = 1 / 2

theorem algorithm_and_oracle_randomness_are_independent :
    Convergence independentSpec (fun _ _ => 1) := by
  refine ⟨fun _ => xorGuess, ?_, fun _ _ => trivial⟩
  intro p hp I oracle h
  cases h
  refine ⟨?_, ?_⟩
  · change Measurable (fun ω : Bool × (ℕ → Bool) => Bool.xor ω.1 (ω.2 0))
    exact (measurable_of_finite (fun ω : Bool × Bool => Bool.xor ω.1 ω.2)).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  change ((fairCoin : Measure Bool).prod (alternatingCoin.law : Measure ((k : ℕ) → alternatingCoin.Seed k)))
    {ω : Bool × (ℕ → Bool) | Bool.xor ω.1 (ω.2 0) = true} = 1 / 2
  unfold alternatingCoin
  norm_num [fairCoin, ProbabilityMeasure.coe_mk, Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.dirac_prod_dirac]
  rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

#print axioms execute_zero_steps
#print axioms read_oracle_zero_steps
#print axioms read_oracle_one_step
#print axioms read_oracle_multiple_steps
#print axioms constant_ignores_replies
#print axioms adaptive_zero_steps
#print axioms adaptive_one_step
#print axioms adaptive_mixed_replies
#print axioms adaptive_false_replies
#print axioms one_query_solves
#print axioms no_uniform_zero_query
#print axioms reversed_quantifiers
#print axioms can_read_public_parameter
#print axioms cannot_read_hidden_parameter
#print axioms valid_restricts_parameters

#print axioms randomized_zero_query_guess
#print axioms randomized_expected_output

end OracleTemplate.TemplateTests
