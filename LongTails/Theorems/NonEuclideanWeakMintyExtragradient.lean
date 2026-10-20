import LongTails.Setups.NonEuclideanWeakMinty
import LongTails.Proofs.NonEuclideanExtragradientRun

namespace LongTails.Theorems.NonEuclideanWeakMintyExtragradient

open OracleTemplate LongTails.Setups.NonEuclideanWeakMinty
open LongTails.Algorithms.NonEuclideanExtragradient
open LongTails.Proofs.NonEuclideanExtragradientRun

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 + 2 * ⌈400 * p.data.L ^ 2 * p.D / (p.data.μ * p.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.NonEuclideanWeakMinty.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨hd, hD, hε⟩ F O ⟨hO, hlip, u, hroot, hinit, hminty⟩
  apply Filter.Eventually.of_forall
  rintro ⟨seed, ξ⟩
  let K : ℕ := 1 + ⌈400 * p.data.L ^ 2 * p.D / (p.data.μ * p.ε ^ 2)⌉₊
  have hK : 0 < K := by dsimp [K]; omega
  have hbudget : 400 * p.data.L ^ 2 * p.D / (p.data.μ * p.ε ^ 2) ≤ (K : ℝ) := by
    have hh := Nat.le_ceil (400 * p.data.L ^ 2 * p.D / (p.data.μ * p.ε ^ 2))
    dsimp [K]
    push_cast
    linarith
  have heq : budget p = fun _ => 2 * K := by
    funext i
    dsimp [budget, K]
    omega
  change ‖F (execute O (algorithm p.data) (budget p) seed ξ)‖ ≤ p.ε
  rw [heq]
  exact execute_accuracy p.data hd F hlip u hminty hinit hε K hK hbudget O hO seed ξ

end LongTails.Theorems.NonEuclideanWeakMintyExtragradient
