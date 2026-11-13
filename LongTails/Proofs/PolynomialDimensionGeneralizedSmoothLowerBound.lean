import LongTails.Proofs.AdaptiveGeneralizedSmoothHardOracle
import LongTails.Proofs.FinitePrefixExpectation
import LongTails.TemplateLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.PolynomialDimensionGeneralizedSmoothLowerBound

open LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension
open AdaptiveGeneralizedSmoothHardOracle

lemma valid_nonempty : ∃ p : Params, spec.valid p := by
  let d := ⌈17592186044416 * (1 + (1048576 : ℝ)) ^ 5⌉₊
  refine ⟨{ d := d, L0 := 1, L1 := 1, x0 := 0, R := 1048576, ε := 1 }, ?_⟩
  norm_num [spec, d]

lemma exists_failure (p : Params) (hp : spec.valid p) (N : ℕ)
    (hN : N ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  have hm : 0 < N + 1 := by omega
  have hmB : N + 1 ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1 := by omega
  let B := radius p (N + 1)
  let θ := threshold p (N + 1)
  let D := 2 * ((N + 1 : ℕ) : ℝ) ^ 2 * (B ^ 2 / θ ^ 2)
  have hB : 0 < B := radius_pos p hp (N + 1)
  have hθ : 0 < θ := threshold_pos p hp (N + 1) hm
  have hD : 0 < D := by dsimp [D]; positivity
  have hDs : D + (N + 1 : ℕ) ≤ (p.d : ℝ) := by
    have hh := dimension_sufficient p hp (N + 1) hm hmB
    change (N + 1 : ℕ) + D ≤ (p.d : ℝ) at hh
    linarith
  let reply := fun π : Fin (N + 1) ↪ Fin p.d => AdaptiveGeneralizedSmoothLocalizedChain.field p hp (N + 1) hm hmB π
  let loss := fun π : Fin (N + 1) ↪ Fin p.d => AdaptiveGeneralizedSmoothLocalizedChain.objective p hp (N + 1) hm hmB π
  let partialFn := partialReply p hp (N + 1) hm
  let query := fun s => (A.query s).2 - p.x0
  let output := fun s => A.output s - p.x0
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨π, hbad⟩ := FinitePrefixExpectation.exists_failure B θ D (3 * p.ε) p.ε hB.le hθ hD
    (by have := hp.2.2.2.1; positivity) hDs le_rfl (by have := hp.2.2.2.1; linarith)
    partialFn reply loss (partialReply_prefix p hp (N + 1) hm)
    (fun π r x hr hs => partialReply_eq p hp (N + 1) hm hmB π ⟨r, by omega⟩ x hs)
    (objective_nonnegative p hp (N + 1) hm hmB)
    (fun π x hx => objective_near_gap p hp (N + 1) hm hmB π (Fin.last N) x hx)
    (objective_far_gap p hp (N + 1) hm hmB)
    query output A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let f := loss π
  let g := reply π
  let z := (AdaptiveGeneralizedSmoothLocalizedChain.seed p hp (N + 1) hm hmB π).z
  let O := SmoothConvexFiniteLowerBound.oracle p.x0 g
  refine ⟨fun x : EuclideanSpace ℝ (Fin p.d) => f (x - p.x0), O,
    AdaptiveGeneralizedSmoothLocalizedChain.admissible p hp (N + 1) hm hmB π, ?_⟩
  rintro ⟨xstar, hmin, hi, he⟩
  change EuclideanSpace ℝ (Fin p.d) at xstar
  have hz : f (xstar - p.x0) = 0 := by
    apply le_antisymm
    · have hh := hmin (Set.mem_univ (p.x0 + z))
      change f (xstar - p.x0) ≤ f (p.x0 + z - p.x0) at hh
      rw [add_sub_cancel_left] at hh
      exact hh.trans_eq (AdaptiveGeneralizedSmoothLocalizedChain.objective_zero p hp (N + 1) hm hmB π)
    · exact objective_nonnegative p hp (N + 1) hm hmB π _
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

end LongTails.Proofs.PolynomialDimensionGeneralizedSmoothLowerBound
