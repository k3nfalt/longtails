import LongTails.TemplateLowerBound
import LongTails.Setups.SmoothAndConvexExpected

namespace OracleTemplate.TemplateLowerBoundTests

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
  obtain ⟨I, O, _, hf⟩ := h true trivial unitAlgorithm trivial
  exact hf rfl

theorem every_valid_parameter_is_hard :
    NonConvergence { mixedSpec with valid := fun p => p = false } (fun _ _ => 0) := by
  intro p hp A _
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
