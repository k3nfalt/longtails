import LongTails.Proofs.TailEntropyHardOracle
import LongTails.Proofs.FinitePrefixExpectation
import LongTails.TemplateLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.TailEntropyChainLowerBound

open LongTails.Setups.GeneralizedSmoothConvexFull
open TailEntropyHardOracle TailEntropyParameters TailEntropyLocalizedChain

lemma exists_failure (p : Params) (hp : Valid p) (N : ℕ)
    (hN : N + 1 ≤ links p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  have hm : 0 < N + 1 := by omega
  let B := radius p
  let θ := thresh p
  let D := 2 * ((N + 1 : ℕ) : ℝ) ^ 2 * (B ^ 2 / θ ^ 2)
  have hB : 0 < B := radius_pos p hp
  have hθ : 0 < θ := thresh_pos p hp
  have hD : 0 < D := by dsimp [D]; positivity
  have hDs : D + (N + 1 : ℕ) ≤ (p.d : ℝ) := by
    have hh := dimension_ok p hp (N + 1) hm hN
    change (N + 1 : ℕ) + D ≤ (p.d : ℝ) at hh
    linarith
  let reply := fun π : Fin (N + 1) ↪ Fin p.d => field p hp (N + 1) hm hN π
  let loss := fun π : Fin (N + 1) ↪ Fin p.d => objective p hp (N + 1) hm hN π
  let partialFn := partialReply p hp (N + 1) hm
  let query := fun s => (A.query s).2 - p.x0
  let output := fun s => A.output s - p.x0
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  have hε := ε_pos p hp
  obtain ⟨π, hbad⟩ := FinitePrefixExpectation.exists_failure B θ D (3 * p.ε) p.ε hB.le hθ hD
    (by positivity) hDs le_rfl (by linarith)
    partialFn reply loss (partialReply_prefix p hp (N + 1) hm)
    (fun π r x hr hs => partialReply_eq p hp (N + 1) hm hN π ⟨r, by omega⟩ x hs)
    (objective_nonneg p hp (N + 1) hm hN)
    (fun π x hx => objective_near_gap p hp (N + 1) hm hN π (Fin.last N) x hx)
    (objective_far_gap p hp (N + 1) hm hN)
    query output A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let f := loss π
  let g := reply π
  let z := (seed p hp (N + 1) hm hN π).z
  let O := SmoothConvexFiniteLowerBound.oracle p.x0 g
  refine ⟨fun x : EuclideanSpace ℝ (Fin p.d) => f (x - p.x0), O,
    admissible p hp (N + 1) hm hN π, ?_⟩
  rintro ⟨xstar, hmin, hi, he⟩
  change EuclideanSpace ℝ (Fin p.d) at xstar
  have hz : f (xstar - p.x0) = 0 := by
    apply le_antisymm
    · have hh := hmin (Set.mem_univ (p.x0 + z))
      change f (xstar - p.x0) ≤ f (p.x0 + z - p.x0) at hh
      rw [add_sub_cancel_left] at hh
      exact hh.trans_eq (objective_zero p hp (N + 1) hm hN π)
    · exact objective_nonneg p hp (N + 1) hm hN π _
  have hout :
      (fun w : A.Seed × (ℕ → Unit) => f (execute O A (fun _ => N) w.1 w.2 - p.x0) - f (xstar - p.x0)) =
      fun w => f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) := by
    funext w
    rw [hz, sub_zero, SmoothConvexFiniteLowerBound.execute_translated p.x0 g A N w.1 w.2]
  apply hbad
  constructor
  · change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1)))) (P : Measure _)
    rw [← hout]
    exact hi
  · change (∫ w : A.Seed × (ℕ → Unit),
      f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) ∂(P : Measure _)) ≤ p.ε
    rw [← hout]
    exact he

end LongTails.Proofs.TailEntropyChainLowerBound
