import LongTails.Setups.AdditiveCubeFixedPoint
import LongTails.Proofs.AdditiveCubeAnchoringAccuracy

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.AdditiveCubeFixedPoint

open LongTails.Setups.AdditiveCubeFixedPoint LongTails.Algorithms.AdditiveCubeAnchoring
open LongTails.Proofs.AdditiveCubeAnchoringExecution LongTails.Proofs.AdditiveCubeAnchoringAccuracy

noncomputable def budget : (let S := LongTails.Setups.AdditiveCubeFixedPoint.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => if p.R ≤ p.ε then 0 else ⌈4096 * (p.R / p.ε) * (1 + 2097152 * Real.log (2 * p.d) * (p.σ / p.ε)^2)⌉₊

theorem result : Convergence LongTails.Setups.AdditiveCubeFixedPoint.spec budget := by
  refine ⟨algorithm, ?_, fun p _ => policy p⟩
  rintro p ⟨hd, _, _, he⟩ T O ⟨hT, μ, P, hP, hi, hz, hi2, hσ, rfl⟩
  let O : Oracle (Cube p) (Point p) :=
    { Seed := fun _ => Point p, law := P, answer := fun _ (_,x) z => (T x).val+z }
  let z := output p O (budget p)
  have hacc : spec.successful p T z P := by
    by_cases hr : (p.R : ℝ) ≤ p.ε
    · have hb : budget p = fun _ => 0 := by funext i; simp [budget,hr]
      let x : Cube p := ⟨0, by simp⟩
      have hx : project p 0 = x := project_fix x
      have hout (ξ) : z ξ = x := by
        change execute O (algorithm p) (budget p) () ξ = x
        rw [hb]
        exact (show project p 0 = x from hx)
      have hres : dist (T x) x ≤ p.ε := by
        rw [Subtype.dist_eq, dist_eq_norm]
        change ‖(T x).val-0‖ ≤ p.ε
        rw [sub_zero]
        exact (T x).property.trans hr
      change Measurable z ∧ Integrable _ _ ∧ _ ≤ _
      rw [show z = fun _ => x from funext hout]
      simpa [integrable_const, measurable_const] using hres
    · let B := ⌈4096 * (p.R / p.ε) * (1 + 2097152 * Real.log (2 * p.d) * (p.σ / p.ε)^2)⌉₊
      have hb : budget p = fun _ => B := funext fun _ => ite_eq_right hr
      change spec.successful p T (output p O (budget p)) P
      rw [hb]
      exact execution_accuracy hT μ P hP hd he hi hz hi2 hσ B (budget_suffices he (lt_of_not_ge hr))
  have hex (s : Unit × (ℕ → Point p)) : execute O (algorithm p) (budget p) s.1 s.2 = z s.2 := by
    rcases s with ⟨⟨⟩,ξ⟩
    rfl
  change Measurable (fun s : Unit × (ℕ → Point p) => execute O (algorithm p) (budget p) s.1 s.2) ∧
    Integrable (fun s : Unit × (ℕ → Point p) => dist (T (execute O (algorithm p) (budget p) s.1 s.2))
      (execute O (algorithm p) (budget p) s.1 s.2)) ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ s : Unit × (ℕ → Point p), dist (T (execute O (algorithm p) (budget p) s.1 s.2))
      (execute O (algorithm p) (budget p) s.1 s.2) ∂(Measure.dirac ()).prod (P : Measure _)) ≤ p.ε
  simp_rw [hex]
  refine ⟨hacc.1.comp measurable_snd, measurePreserving_snd.integrable_comp_of_integrable hacc.2.1, ?_⟩
  rw [integral_fun_snd (fun ξ => dist (T (z ξ)) (z ξ))]
  simpa using hacc.2.2

end LongTails.Theorems.AdditiveCubeFixedPoint
