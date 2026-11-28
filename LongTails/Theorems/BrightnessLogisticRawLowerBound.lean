import LongTails.Setups.BrightnessLogisticRaw
import LongTails.Proofs.BrightnessLogisticRawExecution
import LongTails.TemplateLowerBound

open OracleTemplate MeasureTheory
open LongTails.Setups.BrightnessLogisticRaw
open LongTails.Proofs.BrightnessLogisticRawExecution

namespace LongTails.Theorems.BrightnessLogisticRawLowerBound

noncomputable def budget :
    (let S := LongTails.Setups.BrightnessLogisticRaw.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun p _ =>
    let B := 1 + max p.t (-p.t) * p.D + p.H * ‖p.w‖
    ⌊p.R^2*p.m*p.δ/(8*p.H^2) * min 1 (p.debt/(2*B*Real.log p.R))⌋₊

theorem result : NonConvergence LongTails.Setups.BrightnessLogisticRaw.spec budget := by
  intro p hp A hA b hb
  change Fin 1 → ℕ at b
  change ∀ i : Fin 1, b i ≤ budget p i at hb
  let o : Oracle _ _ := { answer := fun _ q _ => answer p.rows q.2 }
  refine ⟨p.rows,o,⟨rfl,fun _ _ _ => rfl⟩,?_⟩
  dsimp only
  intro hs
  obtain ⟨seed⟩ := nonempty_of_isProbabilityMeasure (A.law : Measure A.Seed)
  have hbudget := hb 0
  simp only [budget, ← abs_eq_max_neg] at hbudget
  obtain ⟨hk,ht⟩ := budget_limits p hp (b 0) hbudget
  have hfail := execute_fails p hp A hA (b 0) hk ht seed
  have hh : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  have hfit := hs (seed,fun _ => ())
  rw [hh] at hfit
  exact hfail hfit

end LongTails.Theorems.BrightnessLogisticRawLowerBound
