import LongTails.Setups.SmoothHessianLipschitzGd
import LongTails.Algorithms.AdaptiveSilverGd
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveSilverExecution
import LongTails.Proofs.AdaptiveSilverBudget

open MeasureTheory

namespace OracleTemplate.AdaptiveSilverHessianLipschitz

open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.AdaptiveSilverGd
open LongTails.Proofs.AdaptiveSilverExecution
open LongTails.Proofs.AdaptiveSilverBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈90 * p.L * p.Δ * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 22 : ℝ) / p.ε ^ 2⌉₊ + ⌈400 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ)⌉₊ + 8

theorem result :
    Convergence LongTails.Setups.SmoothHessianLipschitzGd.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => method p, ?_, fun p hp => allowed p hp.1⟩
  rintro p ⟨hL, hρ, hΔ, hε⟩ f oracle ⟨hf, hlip, hA, hgap, ho⟩
  set B := budget p 0 with hBdef
  have hadm : Adm p f := ⟨hL, hρ, hε, hf, hlip, hA⟩
  have hB : B = budgetFormula p := rfl
  obtain ⟨t, htB, ht⟩ := reach hadm hgap B (by rw [hB]; exact budget_suffices p hL hρ hΔ hε)
  have hacc : ‖gradient f (traj p f B).best‖ ≤ p.ε := by
    obtain ⟨h1, h2⟩ := traj_best p f B (by omega)
    have h3 := h2 t htB
    rw [← h1] at h3
    have hsq : ‖gradient f (traj p f B).best‖ ^ 2 ≤ p.ε ^ 2 :=
      h3.trans (pow_le_pow_left₀ (norm_nonneg _) ht 2)
    exact (sq_le_sq₀ (norm_nonneg _) hε.le).mp hsq
  let res := execute { answer := fun _ query _ => gradient f query.2 } (method p) (fun _ => B)
  have hres : res = (traj p f B).best := execute_iterate (gradient f) (method p) B ()
  have he : ∀ seed : (method p).Seed × ((k : ℕ) → oracle.Seed k),
      execute oracle (method p) (fun _ => B) seed.1 seed.2 = res := by
    rintro ⟨⟨⟩, ξ⟩
    exact execute_eq_of_answer_eq oracle (gradient f) ho _ _ _ _
  change spec.successful p f (fun seed : (method p).Seed × ((k : ℕ) → oracle.Seed k) =>
    (execute oracle (method p) (fun _ => B) seed.1 seed.2)) _
  refine ae_of_all _ (fun seed => ?_)
  simp only
  rw [he seed, hres]
  exact hacc

end OracleTemplate.AdaptiveSilverHessianLipschitz
