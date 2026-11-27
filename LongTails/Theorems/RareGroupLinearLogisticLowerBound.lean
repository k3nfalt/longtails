import LongTails.Setups.RareGroupLinearLogistic
import LongTails.Proofs.RareGroupLinearLogistic
import LongTails.TemplateLowerBound
import Mathlib.Tactic

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.RareGroupLinearLogistic

namespace LongTails.Theorems.RareGroupLinearLogisticLowerBound

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  ⌊1 - p.g / (p.p * p.C)⌋₊

theorem result : NonConvergence LongTails.Setups.RareGroupLinearLogistic.spec budget := by
  intro p hp A ha b hb
  obtain ⟨_, _, hpos, hone, hC, _, hV⟩ := hp
  let O := LongTails.Proofs.RareGroupLinearLogistic.oracle p.data
  refine ⟨p.data, O, ⟨rfl, fun _ _ _ => rfl⟩, ?_⟩
  have htime (h : b (0 : Fin 1) ≠ 0) :
      ((b (0 : Fin 1) : ℝ)-1) * (p.p*capacity p) ≤ -⟪p.v, vote p.data p.start⟫ := by
    let t := 1 - ⟪p.v, vote p.data p.start⟫ / (p.p*capacity p)
    have hle : b (0 : Fin 1) ≤ ⌊t⌋₊ := by
      simpa only [budget, p.g_eq, p.C_eq, t, capacity] using hb (0 : Fin 1)
    have ht : 0 ≤ t := by
      by_contra! hn
      rw [Nat.floor_of_nonpos hn.le] at hle
      omega
    have hfloor : (b (0 : Fin 1) : ℝ) ≤ t := (Nat.cast_le.mpr hle).trans (Nat.floor_le ht)
    dsimp [t] at hfloor
    have hpos' := mul_pos hpos hC
    have hdiv : ⟪p.v, vote p.data p.start⟫ / (p.p*capacity p) ≤ 1 - b (0 : Fin 1) := by linarith
    linarith [(div_le_iff₀ hpos').mp hdiv]
  obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure (A.law : Measure A.Seed)
  change ¬ ∀ z : A.Seed × (ℕ → Unit), Fits p.data (execute O A b z.1 z.2)
  intro hfit
  exact LongTails.Proofs.RareGroupLinearLogistic.fails_within hV hpos hone hC A ha b
    htime z (fun _ => ()) (hfit (z, fun _ => ()))

end LongTails.Theorems.RareGroupLinearLogisticLowerBound
