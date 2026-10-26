import LongTails.Setups.SmoothWeaklyConvex
import LongTails.Algorithms.WeaklyConvexSilver
import LongTails.Proofs.Execution
import LongTails.Proofs.WeaklyConvexSilverExecution
import LongTails.Proofs.WeaklyConvexSilverBudget

open MeasureTheory

namespace OracleTemplate.WeaklyConvexSilverGd

open LongTails.Setups.SmoothWeaklyConvex
open LongTails.Algorithms.SilverSchedule
open LongTails.Algorithms.WeaklyConvexSilver
open LongTails.Proofs.WeaklyConvexSilverExecution
open LongTails.Proofs.WeaklyConvexSilverBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2⌉₊ + ⌈13 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ)⌉₊ + 3

theorem result :
    Convergence LongTails.Setups.SmoothWeaklyConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => method p, ?_, fun p hp => allowed p hp.1⟩
  rintro p ⟨hL, hρ, hΔ, hε⟩ f oracle ⟨ho, hg, hlip, hc, lower, hlower, hgap⟩
  have hanswer : ∀ k x seed, oracle.answer k (0, x) seed = gradient f x :=
    fun k x seed => (ho k seed x).unique (hg x)
  set B := budget p 0 with hBdef
  have hacc : ‖gradient f (traj p f B).best‖ ^ 2 ≤ p.ε ^ 2 := by
    rcases (show level p = 1 ∨ 2 ≤ level p by
      have : 1 ≤ level p := le_max_left _ _
      omega) with h1 | h2
    · have hT := budget_single p hL hρ hΔ hε h1
      apply accuracy_single hL hg hlip lower hlower hgap h1 (⌈ratio * p.L * p.Δ / p.ε ^ 2⌉₊ + 1)
        (by omega) _ B hT
      have hc' := Nat.le_ceil (ratio * p.L * p.Δ / p.ε ^ 2)
      have hε2 : 0 < p.ε ^ 2 := by positivity
      push_cast
      rw [div_le_iff₀ hε2] at hc'
      nlinarith
    · have hJ := budget_blocks p hL hρ hΔ hε h2
      obtain ⟨hsmall, -⟩ := level_spec p h2
      apply accuracy_blocks hL hρ hg hlip hc lower hlower hgap h2 hsmall
        (max 1 ⌈4 * p.L * p.Δ / (ratio ^ level p * p.ε ^ 2)⌉₊) (le_max_left _ _) _ B hJ
      have hc' := Nat.le_ceil (4 * p.L * p.Δ / (ratio ^ level p * p.ε ^ 2))
      have hpos : 0 < ratio ^ level p * p.ε ^ 2 := by
        have := ratio_pos'
        positivity
      rw [div_le_iff₀ hpos] at hc'
      have hm : (⌈4 * p.L * p.Δ / (ratio ^ level p * p.ε ^ 2)⌉₊ : ℝ) ≤
          ((max 1 ⌈4 * p.L * p.Δ / (ratio ^ level p * p.ε ^ 2)⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast le_max_right _ _
      nlinarith
  let result := execute { answer := fun _ query _ => gradient f query.2 } (method p) (fun _ => B)
  have hres : result = (traj p f B).best := execute_iterate (gradient f) (method p) B ()
  have he : ∀ seed : (method p).Seed × ((k : ℕ) → oracle.Seed k),
      execute oracle (method p) (fun _ => B) seed.1 seed.2 = result := by
    rintro ⟨⟨⟩, ξ⟩
    exact execute_eq_of_answer_eq oracle (gradient f) hanswer _ _ _ _
  have hout : (fun seed : (method p).Seed × ((k : ℕ) → oracle.Seed k) =>
      (execute oracle (method p) (fun _ => B) seed.1 seed.2)) = (fun _ => result) :=
    funext (fun seed => he seed)
  change spec.successful p f (fun seed : (method p).Seed × ((k : ℕ) → oracle.Seed k) =>
    (execute oracle (method p) (fun _ => B) seed.1 seed.2)) _
  rw [hout]
  dsimp only [spec, ProbabilityMeasure.coe_mk]
  refine ⟨measurable_const, integrable_const _, ?_⟩
  simpa only [integral_const, probReal_univ, one_smul, hres] using hacc

end OracleTemplate.WeaklyConvexSilverGd
