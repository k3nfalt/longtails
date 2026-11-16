import LongTails.Setups.GapGeneralizedSmoothConvex
import LongTails.Proofs.FinitePrefixExpectation
import LongTails.Proofs.SmoothConvexFiniteLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.GapChainLowerBound

open LongTails.Setups.GapGeneralizedSmoothConvex

lemma exists_failure (p : Params) (hε : 0 < p.ε) (N : ℕ) (B θ : ℝ) (hB : 0 < B) (hθ : 0 < θ)
    (hd : 2 * ((N + 1 : ℕ) : ℝ) ^ 2 * (B ^ 2 / θ ^ 2) + (N + 1 : ℕ) ≤ (p.d : ℝ))
    (loss : (Fin (N + 1) ↪ Fin p.d) → EuclideanSpace ℝ (Fin p.d) → ℝ)
    (reply : (Fin (N + 1) ↪ Fin p.d) → EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (partialFn : (Fin (N + 1) ↪ Fin p.d) → ℕ → EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (center : (Fin (N + 1) ↪ Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (hadm : ∀ π, spec.admissible p (fun x : EuclideanSpace ℝ (Fin p.d) => loss π (x - p.x0))
      (SmoothConvexFiniteLowerBound.oracle p.x0 (reply π)))
    (hp : ∀ π ρ r x, (∀ i, i.val ≤ r → π i = ρ i) → partialFn π r x = partialFn ρ r x)
    (heq : ∀ π r x, r < N → (‖x‖ < B → ∀ i, r ≤ i.val → |x (π i)| ≤ θ) → partialFn π r x = reply π x)
    (hn : ∀ π x, 0 ≤ loss π x)
    (hz : ∀ π, loss π (center π) = 0)
    (hnear : ∀ π x, |x (π (Fin.last N))| ≤ θ → 3 * p.ε ≤ loss π x)
    (hfar : ∀ π x, B ≤ ‖x‖ → 3 * p.ε ≤ loss π x)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let D := 2 * ((N + 1 : ℕ) : ℝ) ^ 2 * (B ^ 2 / θ ^ 2)
  have hD : 0 < D := by dsimp [D]; positivity
  let query := fun s => (A.query s).2 - p.x0
  let output := fun s => A.output s - p.x0
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨π, hbad⟩ := FinitePrefixExpectation.exists_failure B θ D (3 * p.ε) p.ε hB.le hθ hD
    (by positivity) hd le_rfl (by linarith) partialFn reply loss hp heq hn hnear hfar
    query output A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let f := loss π
  let g := reply π
  let O := SmoothConvexFiniteLowerBound.oracle p.x0 g
  refine ⟨fun x : EuclideanSpace ℝ (Fin p.d) => f (x - p.x0), O, hadm π, ?_⟩
  rintro ⟨xstar, hmin, hi, he⟩
  change EuclideanSpace ℝ (Fin p.d) at xstar
  have hzero : f (xstar - p.x0) = 0 := by
    apply le_antisymm
    · have hh := hmin (Set.mem_univ (p.x0 + center π))
      change f (xstar - p.x0) ≤ f (p.x0 + center π - p.x0) at hh
      rw [add_sub_cancel_left] at hh
      exact hh.trans_eq (hz π)
    · exact hn π _
  have hout :
      (fun w : A.Seed × (ℕ → Unit) => f (execute O A (fun _ => N) w.1 w.2 - p.x0) - f (xstar - p.x0)) =
      fun w => f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) := by
    funext w
    rw [hzero, sub_zero, SmoothConvexFiniteLowerBound.execute_translated p.x0 g A N w.1 w.2]
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

end LongTails.Proofs.GapChainLowerBound
