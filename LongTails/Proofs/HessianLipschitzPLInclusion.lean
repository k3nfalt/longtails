import LongTails.Setups.HighDimensionalHessianLipschitzPL
import LongTails.Includes
import LongTails.Theorems.HessianLipschitzPLCubicNewton

namespace LongTails.Proofs.HessianLipschitzPLInclusion

open OracleTemplate LongTails.Setups

noncomputable def inclusion :
    Inclusion HessianLipschitzPL.spec HighDimensionalHessianLipschitzPL.spec where
  numOracles_eq := rfl
  mapParams q := HighDimensionalHessianLipschitzPL.toGeneral q
  mapPublic q := (HighDimensionalHessianLipschitzPL.toGeneral q).toPublic
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid q hq := by
    have h1 : 0 < q.ε := hq.2.2.1
    have h2 : 32 * q.ε ≤ q.Δ := hq.2.2.2.1
    have h3 : (0 : ℝ) ≤ q.Δ := by linarith
    exact ⟨hq.1, hq.2.1, h3, h1⟩
  admissible _ _ _ _ h := h
  successful _ _ _ _ _ _ _ _ _ h := h
  allowedAlgorithm _ _ _ := trivial

lemma includes : Includes HessianLipschitzPL.spec HighDimensionalHessianLipschitzPL.spec :=
  ⟨inclusion⟩

lemma transfer : Convergence HighDimensionalHessianLipschitzPL.spec (fun q _ =>
    ⌈53 * (q.H ^ 2 * q.Δ / q.μ ^ 3) ^ (1 / 4 : ℝ) +
      5 * Real.log (1 + Real.log (1 + q.μ ^ 3 / (q.H ^ 2 * q.ε))) + 4⌉₊) := by
  obtain ⟨make, correct, _⟩ := LongTails.Theorems.HessianLipschitzPLCubicNewton.result
  refine ⟨fun q => make (HighDimensionalHessianLipschitzPL.toGeneral q).toPublic, ?_,
    fun _ _ => trivial⟩
  intro q hq f O h
  exact correct (HighDimensionalHessianLipschitzPL.toGeneral q) (inclusion.valid q hq) f O
    (inclusion.admissible q hq f O h)

end LongTails.Proofs.HessianLipschitzPLInclusion
