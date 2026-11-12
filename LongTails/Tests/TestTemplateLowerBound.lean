import LongTails.TemplateLowerBound
import LongTails.Setups.SmoothAndConvexExpected

namespace OracleTemplate.TemplateLowerBoundTests

lemma convergence_budget_not_le (S : Setup)
    (upper lower : S.Params → Fin S.numOracles → ℕ)
    (hc : Convergence S upper) (hn : NonConvergence S lower)
    (p : S.Params) (hp : S.valid p) : ¬ ∀ i, upper p i ≤ lower p i := by
  intro hb
  obtain ⟨make, hs, ha⟩ := hc
  obtain ⟨I, O, had, hbad⟩ := hn p hp (make (S.publicInput p)) (ha p hp) (upper p) hb
  exact hbad (hs p hp I O had)

lemma exists_oracle_lower_lt_upper (S : Setup)
    (upper lower : S.Params → Fin S.numOracles → ℕ)
    (hc : Convergence S upper) (hn : NonConvergence S lower)
    (p : S.Params) (hp : S.valid p) : ∃ i, lower p i < upper p i := by
  classical
  simpa only [not_forall, not_le] using convergence_budget_not_le S upper lower hc hn p hp

lemma lower_lt_upper_single_oracle (S : Setup) (hone : S.numOracles = 1)
    (upper lower : S.Params → Fin S.numOracles → ℕ)
    (hc : Convergence S upper) (hn : NonConvergence S lower)
    (p : S.Params) (hp : S.valid p) (i : Fin S.numOracles) : lower p i < upper p i := by
  by_contra h
  apply convergence_budget_not_le S upper lower hc hn p hp
  intro j
  have heq : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
  simpa only [heq] using Nat.le_of_not_gt h

lemma nonconvergence_mono (S : Setup)
    (lower smaller : S.Params → Fin S.numOracles → ℕ)
    (hn : NonConvergence S lower)
    (hle : ∀ p, S.valid p → ∀ i, smaller p i ≤ lower p i) :
    NonConvergence S smaller := by
  intro p hp A ha b hb
  exact hn p hp A ha b (fun i => (hb i).trans (hle p hp i))

noncomputable def countingAlgorithm : Algorithm Unit Unit ℕ where
  State := ℕ
  initial _ := 0
  query _ := (0, ())
  update n _ := n + 1
  output := id

abbrev countingSpec : Setup where
  Params := Unit
  Public := Unit
  Instance _ := Unit
  Query _ := Unit
  Reply _ := Unit
  Output _ := ℕ
  publicInput := id
  valid _ := True
  admissible _ _ _ := True
  successful _ _ output _ := ∀ seed, output seed = 0
  allowedAlgorithm _ A := A = countingAlgorithm

lemma counting_converges_zero : Convergence countingSpec (fun _ _ => 0) := by
  refine ⟨fun _ => countingAlgorithm, ?_, fun _ _ => rfl⟩
  intro p hp I O hO
  dsimp only
  intro seed
  rfl

lemma counting_fails_after_one :
    execute ({ answer := fun _ _ _ => () } : Oracle Unit Unit)
      countingAlgorithm (fun _ => 1) () (fun _ => ()) = 1 := by
  rfl

lemma counting_not_nonconvergence_one : ¬ NonConvergence countingSpec (fun _ _ => 1) := by
  intro h
  have hlt := lower_lt_upper_single_oracle countingSpec rfl
    (fun _ _ => 0) (fun _ _ => 1) counting_converges_zero h () trivial 0
  exact (by norm_num : ¬ ((1 : ℕ) < 0)) hlt

abbrev mixedSpec : Setup where
  Params := Bool
  Public := Bool
  Instance _ := Unit
  Query _ := Unit
  Reply _ := Unit
  Output _ := Unit
  publicInput := id
  valid _ := True
  admissible _ _ _ := True
  successful p _ _ _ := p = true

noncomputable def unitAlgorithm : Algorithm Unit Unit Unit where
  State := Unit
  initial _ := ()
  query _ := (0, ())
  update _ _ := ()
  output _ := ()

theorem mixed_not_convergence : ¬ Convergence mixedSpec (fun _ _ => 0) := by
  rintro ⟨make, h, _⟩
  have hf := h false trivial () { answer := fun _ _ _ => () } trivial
  exact Bool.false_ne_true hf

theorem mixed_not_nonconvergence : ¬ NonConvergence mixedSpec (fun _ _ => 0) := by
  intro h
  obtain ⟨I, O, _, hf⟩ := h true trivial unitAlgorithm trivial (fun _ => 0) (fun _ => le_rfl)
  exact hf rfl

theorem every_valid_parameter_is_hard :
    NonConvergence { mixedSpec with valid := fun p => p = false } (fun _ _ => 0) := by
  intro p hp A _ b hb
  subst p
  exact ⟨(), { answer := fun _ _ _ => () }, trivial, Bool.false_ne_true⟩

theorem euclidean_parameters_valid (d : ℕ) (L R ε : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hregime : 262144 * ε ≤ L * R ^ 2)
    (hd : 65536 * (⌊Real.sqrt (L * R ^ 2 / ε) / 512⌋₊ + 1) ^ 5 ≤ d) :
    LongTails.Setups.SmoothAndConvexExpected.spec.valid
      { d := d, L := L, x0 := 0, R := R, ε := ε } :=
  ⟨hL, hR, hε, hregime, hd⟩

theorem expected_setup_has_valid_parameters :
    ∃ d : ℕ, LongTails.Setups.SmoothAndConvexExpected.spec.valid
      { d := d, L := 1, x0 := 0, R := 1, ε := 1 / 262144 } := by
  refine ⟨65536 * (⌊Real.sqrt (1 * 1 ^ 2 / (1 / 262144)) / 512⌋₊ + 1) ^ 5, ?_⟩
  apply euclidean_parameters_valid <;> norm_num

end OracleTemplate.TemplateLowerBoundTests
