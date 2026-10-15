import LongTails.Algorithms.FullGradientAccelerated
import LongTails.Proofs.FullGradientQuadraticModel
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.InexactAcceleratedConvergence

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FullGradientAccelerated

open LongTails.Setups.QuadraticFiniteSum

lemma execute_algorithm (p : Params) (f : Instance p) (O : Oracle (Fin p.n × p.E) p.E)
    (hanswer : ∀ k seed i x, O.answer k (0, (i, x)) seed = f.A i x + f.b i)
    (K : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => p.n * K) seed ξ = output p (averageGradient f) K := by
  erw [execute_eq_of_answer_eq O (fun q => f.A q.1 q.2 + f.b q.1)
    (fun k q s => hanswer k s q.1 q.2)]
  erw [StochasticGradient.execute_advance]
  unfold output
  erw [StochasticGradient.execute_advance]
  have h := advance_batched (NeZero.pos p.n) (core p)
    (fun s i => (i, InexactGradient.query (InexactGradient.momentum p.L p.μ 0) s))
    (fun _ replies => (p.n : ℝ)⁻¹ • ∑ i, replies i) (0 : p.E)
    (fun q (_ : Unit) => f.A q.1 q.2 + f.b q.1) (fun _ => ()) K 0 (p.x0, p.x0)
  simp only [Nat.zero_mul] at h
  change (StochasticGradient.advance _ (p.n * K) 0 (0, (p.x0, p.x0), fun _ => (0 : p.E))).2.1.1 = _
  erw [Nat.mul_comm p.n K, h]
  rfl

lemma output_accuracy (p : Params) (hp : spec.valid p) (f : Instance p)
    (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖f.A i‖ ≤ p.L)
    (hc : ∀ x, p.μ * ‖x‖ ^ 2 ≤ (p.n : ℝ)⁻¹ * ∑ i, ⟪x, f.A i x⟫)
    (u : p.E) (hu : (∑ i, (f.A i u + f.b i)) = 0) (hR : ‖p.x0 - u‖ ≤ p.R)
    (K : ℕ) (hK : ⌈8 * Real.sqrt (p.L / p.μ) * Real.log (1 + 2 * p.L * p.R ^ 2 / p.ε)⌉₊ ≤ K) :
    objective f (output p (averageGradient f) K) - objective f u ≤ p.ε := by
  have hg : ∀ x, HasGradientAt (objective f) (gradient (objective f) x) x := by
    intro x
    rw [objective_gradient f hs]
    exact objective_hasGradientAt f hs x
  apply InexactGradient.execute_accuracy (α := 0) (δ := 0) hp.2.1 hp.2.2.1
    (by norm_num) (by norm_num) hp.2.2.2.2.2
    (by nlinarith [hp.2.1, hp.2.2.2.2.2]) hg
    (objective_smooth f hs hA) (objective_strong f hs hc)
    (QuadraticFiniteSum.stationary_minimizer f hp.2.1.le hs hc hu) hR
    { answer := fun _ q _ => averageGradient f q.2 }
    (fun k x seed => by simp [objective_gradient f hs]) () (fun _ => ()) K
  simpa using hK

end OracleTemplate.FullGradientAccelerated
