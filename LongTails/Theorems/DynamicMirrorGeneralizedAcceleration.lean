import LongTails.Setups.MirrorGeneralizedSmooth
import LongTails.Proofs.MirrorGeneralizedBudget
import LongTails.Proofs.MirrorGeneralizedExecution

namespace LongTails.Theorems.DynamicMirrorGeneralizedAcceleration

open OracleTemplate LongTails.Setups.MirrorGeneralizedSmooth
open LongTails.Algorithms.MirrorGeneralizedAcceleration
open LongTails.Proofs

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 3 * ⌈24576 * (1 + Real.sqrt (2 * p.L0 * p.D / p.ε) + (1 + 2 * p.L1 * Real.sqrt p.D) * Real.log (2 + 2 * p.Δ / p.ε))⌉₊

theorem result : Convergence LongTails.Setups.MirrorGeneralizedSmooth.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp I oracle ho
    obtain ⟨hL0, hL1, hD, hΔ, hε⟩ := hp
    obtain ⟨hg, hprox, hc, hf, hcont, hs, hm, hstrong, hminprox, xs, hmin, hb, hgap⟩ := ho
    have h : MirrorGeneralizedStep.Hyp I := ⟨hc, hf, hcont, hs, hm, hstrong, hminprox⟩
    let N := ⌈24576 * (1 + Real.sqrt (2 * p.L0 * p.D / p.ε) + (1 + 2 * p.L1 * Real.sqrt p.D) * Real.log (2 + 2 * p.Δ / p.ε))⌉₊
    have hacc := MirrorGeneralizedBudget.run_accuracy h hL0 hL1 hD hΔ
      (fun u => hmin (Set.mem_univ u)) hb hgap hε (N := N) (by
        simpa [N, radius, mul_assoc, mul_left_comm, mul_comm] using
          (Nat.le_ceil (24576 * (1 + Real.sqrt (2 * p.L0 * p.D / p.ε) +
            (1 + 2 * p.L1 * Real.sqrt p.D) * Real.log (2 + 2 * p.Δ / p.ε)))))
    refine ⟨xs, hmin, Filter.Eventually.of_forall ?_⟩
    intro ω
    change I.f (execute oracle (algorithm p.toPublic) (fun _ => 3 * N) ω.1 ω.2) - I.f xs ≤ p.ε
    rw [MirrorGeneralizedExecution.execute_oracle I oracle hg hprox N ω.1 ω.2]
    exact hacc
  · intro p hp
    trivial

end LongTails.Theorems.DynamicMirrorGeneralizedAcceleration
