import LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
import LongTails.Algorithms.KnownGapSelection
import LongTails.Proofs.KnownGapUpperTransfer

open MeasureTheory

namespace LongTails.Theorems.KnownGapGeneralizedSmoothUpperBound

open OracleTemplate OracleTemplate.KnownGapSelection LongTails.Proofs.KnownGapUpperTransfer
open LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => min (2 * ⌈4096 * (1 + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + (⌈(p.L1 * p.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * p.Δ / p.ε))⌉₊) ⌈64 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + 32768 * (1 + p.L1 * p.R) * Real.log (2 + p.L1 * p.R)⌉₊

theorem result : Convergence spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  obtain ⟨hL0, hL1, hR, hε, _, _, hΔ, _, _⟩ := hp
  have hΔpos : 0 < p.Δ := by
    have : 0 < p.ε * (2 + p.L1 * p.R) ^ 2 := by positivity
    linarith
  obtain ⟨hc, hg, hgd, hH, u, hmin, hdist, hgap⟩ := hadm
  let seed0 := (Classical.choice O.law.nonempty) 0
  let g := fun x => O.answer [] (0, x) seed0
  have hans : ∀ k x sample, O.answer k (0, x) sample = g x :=
    fun k x sample => (hg k sample x).unique (hg [] seed0 x)
  refine ⟨u, hmin, ?_⟩
  by_cases hcase : 2 * gapTrials p ≤ radiusSteps p
  · have hb : budget p = fun _ => 2 * gapTrials p := by
      funext i
      exact min_eq_left hcase
    obtain ⟨u', hmin', hall⟩ := GeneralizedAccelerated.accelerated_gap p.toGeneralized
      ⟨hL0, hL1.le, hR, hΔpos, hε⟩ (gapTrials p) (Nat.le_ceil _) f O
      ⟨hc, hg, hgd, hH, u, hmin, hdist, hgap⟩
    have huu : f u' = f u := le_antisymm (hmin' (Set.mem_univ u)) (hmin (Set.mem_univ u'))
    let A := GeneralizedAccelerated.algorithm p.toGeneralized.toPublic
    let sA := Classical.choice A.law.nonempty
    let v := execute O A (fun _ => 2 * gapTrials p) sA (Classical.choice O.law.nonempty)
    have hex : ∀ (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k),
        execute O (algorithm p) (fun _ => 2 * gapTrials p) seed ξ =
          execute { answer := fun _ query _ => g query.2 } (algorithm p) (fun _ => 2 * gapTrials p) seed :=
      fun seed ξ => execute_eq_of_answer_eq O g hans _ _ seed ξ
    have hexA : ∀ (ξ : (k : ℕ) → O.Seed k),
        execute O A (fun _ => 2 * gapTrials p) sA ξ =
          execute { answer := fun _ query _ => g query.2 } A (fun _ => 2 * gapTrials p) sA :=
      fun ξ => execute_eq_of_answer_eq O g hans _ _ sA ξ
    have hconst : ∀ ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k),
        execute O (algorithm p) (budget p) ω.1 ω.2 = v := by
      intro ω
      rw [hb, hex]
      unfold algorithm
      rw [combine_execute_left _ hcase]
      dsimp only [v]
      rw [hexA]
    have hv : f v - f u ≤ p.ε := by
      rw [← huu]
      exact hall sA _
    exact constant_success _ f _ u p.ε v hconst hv
  · have hb : budget p = fun _ => radiusSteps p := by
      funext i
      exact min_eq_right (le_of_not_ge hcase)
    obtain ⟨u', hmin', hall⟩ := RadiusFreeSherpa.sherpa_gap (toRadiusOnly p) ⟨hL0, hL1, hR, hε⟩
      (radiusSteps p) le_rfl f O ⟨hc, hg, hgd, hH, u, hmin, hdist⟩
    have huu : f u' = f u := le_antisymm (hmin' (Set.mem_univ u)) (hmin (Set.mem_univ u'))
    let B := RadiusFreeSherpa.algorithm (toRadiusOnly p).toPublic
    let sB := Classical.choice B.law.nonempty
    let v := execute O B (fun _ => radiusSteps p) sB (Classical.choice O.law.nonempty)
    have hex : ∀ (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k),
        execute O (algorithm p) (fun _ => radiusSteps p) seed ξ =
          execute { answer := fun _ query _ => g query.2 } (algorithm p) (fun _ => radiusSteps p) seed :=
      fun seed ξ => execute_eq_of_answer_eq O g hans _ _ seed ξ
    have hexB : ∀ (ξ : (k : ℕ) → O.Seed k),
        execute O B (fun _ => radiusSteps p) sB ξ =
          execute { answer := fun _ query _ => g query.2 } B (fun _ => radiusSteps p) sB :=
      fun ξ => execute_eq_of_answer_eq O g hans _ _ sB ξ
    have hconst : ∀ ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k),
        execute O (algorithm p) (budget p) ω.1 ω.2 = v := by
      intro ω
      rw [hb, hex]
      unfold algorithm
      rw [combine_execute_right _ hcase]
      dsimp only [v]
      rw [hexB]
    have hv : f v - f u ≤ p.ε := by
      rw [← huu]
      exact hall sB _
    exact constant_success _ f _ u p.ε v hconst hv

end LongTails.Theorems.KnownGapGeneralizedSmoothUpperBound
