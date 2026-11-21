import LongTails.Setups.EllSmoothNonconvex
import LongTails.Proofs.EllSmoothGd

open MeasureTheory

namespace OracleTemplate.EllSmoothNonconvexUpperBound

open LongTails.Setups.EllSmoothNonconvex LongTails.Algorithms.EllSmoothGd
open LongTails.Proofs.EllSmoothGd

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊16 * p.Δ * p.ℓ p.ε / p.ε ^ 2⌋₊ + 1

theorem result :
    Convergence LongTails.Setups.EllSmoothNonconvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => ellGd p.ℓ p.ε p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨-, hρ2, hreg, -, hε⟩ f oracle ⟨hg, hd, hH, hΔ, hanswer⟩
  let K := ⌊16 * p.Δ * p.ℓ p.ε / p.ε ^ 2⌋₊ + 1
  let out := (fun y => gdStep p.ℓ p.ε y (gradient f y))^[K] p.x0
  have hK : 16 * p.Δ * p.ℓ p.ε / p.ε ^ 2 < (K : ℝ) := by
    simp only [K]
    push_cast
    exact Nat.lt_floor_add_one _
  have ha := iterate_accuracy f p.ℓ p.ρ p.Δ p.ε p.x0 hρ2 hreg hε hg hd hH hΔ K hK
  have he : ∀ seed : (ellGd p.ℓ p.ε p.x0).Seed × ((k : ℕ) → oracle.Seed k),
      execute oracle (ellGd p.ℓ p.ε p.x0) (fun _ => K) seed.1 seed.2 = out := by
    rintro ⟨s, ξ⟩
    rw [execute_eq_of_answer_eq oracle (fun x => (f x, gradient f x))
      (fun k x seed => hanswer k seed x)]
    exact execute_iterate (fun x => (f x, gradient f x)) (ellGd p.ℓ p.ε p.x0) K s
  change spec.successful p f (fun seed : (ellGd p.ℓ p.ε p.x0).Seed × ((k : ℕ) → oracle.Seed k) =>
    (execute oracle (ellGd p.ℓ p.ε p.x0) (fun _ => K) seed.1 seed.2)) _
  rw [funext he]
  dsimp only [spec, ProbabilityMeasure.coe_mk]
  exact ⟨measurable_const, integrable_const _,
    by simpa only [integral_const, probReal_univ, one_smul] using ha⟩

end OracleTemplate.EllSmoothNonconvexUpperBound
