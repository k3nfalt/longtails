import LongTails.Setups.CompositeGeneralizedParameterFree
import LongTails.Proofs.Execution
import LongTails.Proofs.BacktrackingCompositeBudget
import LongTails.Proofs.BacktrackingCompositeExecution

open Set
open OracleTemplate.CompositeGeneralized

namespace OracleTemplate.CompositeParameterFree

open LongTails.Setups.CompositeGeneralizedParameterFree

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 3 * ⌈4 + 61 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (35 + 1067 * q.L1 * q.R) * Real.log (1 + (12 + 400 * q.L1 * q.R) * (1 + 1 / Real.sqrt ((q.L0 + q.L1 * q.G) * q.h0) + q.L1 * Real.sqrt (q.Δ / (q.L0 + q.L1 * q.G)))) + 4 * Real.log (5 / 2 + 1 / (16 * (q.L0 + q.L1 * q.G) * q.h0) + 22 * q.L1 ^ 2 * q.Δ / (q.L0 + q.L1 * q.G)) + 2 * Real.log (2 * ((1 + q.h0 * (40 * (q.L0 + q.L1 * q.G) + 400 * q.L1 ^ 2 * q.Δ)) * (8 * (1 + 32 * q.L1 * q.R) ^ 2 + 200 * q.L1 ^ 2 * q.R ^ 2)))⌉₊

theorem result : Convergence LongTails.Setups.CompositeGeneralizedParameterFree.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => ⌈4 + 61 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (35 + 1067 * q.L1 * q.R) * Real.log (1 + (12 + 400 * q.L1 * q.R) * (1 + 1 / Real.sqrt ((q.L0 + q.L1 * q.G) * q.h0) + q.L1 * Real.sqrt (q.Δ / (q.L0 + q.L1 * q.G)))) + 4 * Real.log (5 / 2 + 1 / (16 * (q.L0 + q.L1 * q.G) * q.h0) + 22 * q.L1 ^ 2 * q.Δ / (q.L0 + q.L1 * q.G)) + 2 * Real.log (2 * ((1 + q.h0 * (40 * (q.L0 + q.L1 * q.G) + 400 * q.L1 ^ 2 * q.Δ)) * (8 * (1 + 32 * q.L1 * q.R) ^ 2 + 200 * q.L1 ^ 2 * q.R ^ 2)))⌉₊)
    (fun _ => 3)
  refine ⟨fun p => backtrackingComposite p, ?_, fun _ _ => trivial⟩
  rintro q ⟨hh0, hL0, hL1, hR, hΔ, hG0, hε⟩
  intro n hcap
  rintro I oracle
    ⟨hgradAns, hproxAns, hc, hgrad, hcont, hsmooth, hQ, hψ, hprox, hx0, xs, hxs, hmin,
      hdist, hgap, hGx⟩
  have hyp : Hyp I.f I.ψ I.grad I.Q I.prox q.L0 q.L1 :=
    ⟨hL0, hL1, hc, hgrad, hcont, hsmooth, hQ, hψ, hprox⟩
  have b : Base I.f I.ψ I.grad I.Q I.prox q.L0 q.L1 q.R q.G q.Δ xs q.x0 q.h0 :=
    ⟨hyp, hR, hGx, hΔ, hh0, hxs, hmin, hx0, hdist, hgap⟩
  have hbudget : 3 * n = 3 * n := rfl
  have hLs : 0 < q.L0 + q.L1 * q.G := by positivity
  have hsuff := trials_sufficient (ε := q.ε) hLs hL1 hR hΔ hh0
  have hn := Nat.le_ceil (4 + 61 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (35 + 1067 * q.L1 * q.R) * Real.log (1 + (12 + 400 * q.L1 * q.R) * (1 + 1 / Real.sqrt ((q.L0 + q.L1 * q.G) * q.h0) + q.L1 * Real.sqrt (q.Δ / (q.L0 + q.L1 * q.G)))) + 4 * Real.log (5 / 2 + 1 / (16 * (q.L0 + q.L1 * q.G) * q.h0) + 22 * q.L1 ^ 2 * q.Δ / (q.L0 + q.L1 * q.G)) + 2 * Real.log (2 * ((1 + q.h0 * (40 * (q.L0 + q.L1 * q.G) + 400 * q.L1 ^ 2 * q.Δ)) * (8 * (1 + 32 * q.L1 * q.R) ^ 2 + 200 * q.L1 ^ 2 * q.R ^ 2))))
  have hcast : ((⌈4 + 61 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (35 + 1067 * q.L1 * q.R) * Real.log (1 + (12 + 400 * q.L1 * q.R) * (1 + 1 / Real.sqrt ((q.L0 + q.L1 * q.G) * q.h0) + q.L1 * Real.sqrt (q.Δ / (q.L0 + q.L1 * q.G)))) + 4 * Real.log (5 / 2 + 1 / (16 * (q.L0 + q.L1 * q.G) * q.h0) + 22 * q.L1 ^ 2 * q.Δ / (q.L0 + q.L1 * q.G)) + 2 * Real.log (2 * ((1 + q.h0 * (40 * (q.L0 + q.L1 * q.G) + 400 * q.L1 ^ 2 * q.Δ)) * (8 * (1 + 32 * q.L1 * q.R) ^ 2 + 200 * q.L1 ^ 2 * q.R ^ 2)))⌉₊) : ℝ) ≤ n := Nat.cast_le.mpr hcap
  have hrej := rej_bound b n
  have hacc : 1 + L0c (q.L0 + q.L1 * q.G) (Amin (q.L0 + q.L1 * q.G) q.L1 q.Δ q.h0) +
      4 / 3 * (4 * Real.sqrt 32 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) +
        (1 + ρc q.L1 q.R) / ρc q.L1 q.R *
          Real.log (1 + δc (q.L0 + q.L1 * q.G) / ρc q.L1 q.R /
            Real.sqrt (Amin (q.L0 + q.L1 * q.G) q.L1 q.Δ q.h0))) ≤
      (acc I.grad I.prox q.x0 q.h0 n : ℝ) := by
    linarith
  have hA := run_accuracy b hε le_rfl n hacc
  have hinv := run_inv b n
  obtain ⟨hA0, hxQ, -, hΦ, -, -, -⟩ := hinv
  have hans : ∀ k query seed, oracle.answer k (0, query) seed =
      answerOf q.toPublic I.grad I.prox query := by
    intro k query seed
    cases query with
    | gradient x => exact hgradAns k seed x
    | prox a z v => exact hproxAns k seed a z v
  have hexec : ∀ ξ : (k : ℕ) → oracle.Seed k,
      execute oracle (backtrackingComposite q.toPublic) (fun _ => (3 * n)) () ξ =
        (run I.grad I.prox q.x0 q.h0 n).x := fun ξ =>
    (execute_eq_of_answer_eq oracle _ hans (backtrackingComposite q.toPublic) (3 * n) () ξ).trans
      (execute_backtracking q.toPublic I.grad I.prox n)
  have hApos : 0 < (run I.grad I.prox q.x0 q.h0 n).A := by
    have : 0 < q.R ^ 2 / q.ε := by positivity
    linarith
  have hgap0 : 0 ≤ I.f (run I.grad I.prox q.x0 q.h0 n).x + I.ψ (run I.grad I.prox q.x0 q.h0 n).x -
      (I.f xs + I.ψ xs) := by
    have := hmin hxQ
    simp only [mem_ofPred_eq] at this
    change I.f xs + I.ψ xs ≤ I.f _ + I.ψ _ at this
    linarith
  have haccuracy : I.f (run I.grad I.prox q.x0 q.h0 n).x + I.ψ (run I.grad I.prox q.x0 q.h0 n).x -
      (I.f xs + I.ψ xs) ≤ q.ε := by
    have h1 : (run I.grad I.prox q.x0 q.h0 n).A *
        (I.f (run I.grad I.prox q.x0 q.h0 n).x + I.ψ (run I.grad I.prox q.x0 q.h0 n).x -
          (I.f xs + I.ψ xs)) ≤ q.R ^ 2 := by
      nlinarith [sq_nonneg ‖(run I.grad I.prox q.x0 q.h0 n).z - xs‖]
    have h2 : q.R ^ 2 / q.ε * (I.f (run I.grad I.prox q.x0 q.h0 n).x +
        I.ψ (run I.grad I.prox q.x0 q.h0 n).x - (I.f xs + I.ψ xs)) ≤ q.R ^ 2 :=
      (mul_le_mul_of_nonneg_right hA hgap0).trans h1
    rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h2
    have hR2 : 0 < q.R ^ 2 := by positivity
    nlinarith
  refine ⟨xs, hxs, hmin, Filter.Eventually.of_forall fun seed => ?_⟩
  · obtain ⟨⟨⟩, ξ⟩ := seed
    rw [hbudget]
    change (execute oracle (backtrackingComposite q.toPublic) (fun _ => (3 * n)) () ξ) ∈ I.Q ∧
      objective I (execute oracle (backtrackingComposite q.toPublic) (fun _ => (3 * n)) () ξ) -
        objective I xs ≤ q.ε
    have e : (execute oracle (backtrackingComposite q.toPublic) (fun _ => (3 * n)) () ξ) =
        (run I.grad I.prox q.x0 q.h0 n).x := (hexec ξ)
    rw [e]
    exact ⟨hxQ, haccuracy⟩

end OracleTemplate.CompositeParameterFree
