import LongTails.Proofs.RobustGeneralizedExecution
import LongTails.Proofs.RobustGeneralizedFailures
import LongTails.Proofs.RobustGeneralizedBudget

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight energy)
open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex hiding Params spec

lemma rawAdvance_proofNext (p : Params) (f : p.E → ℝ) (u : p.E)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (s : Iterate p.E) (call : ℕ)
    (hgood : proofFailure p f u g (proofCost p f u s) s (fun i => ξ (call+i)) = 0) :
    rawAdvance p g ξ (proofCost p f u s) call (resume p s) =
      resume p (proofNext p f u g (proofCost p f u s) s (fun i => ξ (call+i))) := by
  classical
  by_cases hs : proofActive p f u s
  · have hA : ¬target p.R p.ε ≤ s.A := not_le.mpr hs.2.2.1
    have hbadSize (n : ℕ) (hn : n = 2*estimatorCost p (tentativeWeight s))
        (hgood : proofFailure p f u g n s (fun i => ξ (call+i)) = 0) :
        ¬batchBad p f g s
          (firstHalf (fun i : Fin (2*estimatorCost p (tentativeWeight s)) => ξ (call+i)))
          (secondHalf (fun i : Fin (2*estimatorCost p (tentativeWeight s)) => ξ (call+i))) := by
      subst n
      simpa only [proofFailure, hs, true_and, ite_eq_right_iff, one_ne_zero, imp_false] using hgood
    have hbad := hbadSize (proofCost p f u s) (by simp only [proofCost, ite_eq_left hs]) hgood
    simp only [proofCost, ite_eq_left hs, proofNext]
    rw [ite_eq_left hs, resume, ite_eq_right hA, guardedStep_eq_sampleStep p f g s _ hbad]
    exact rawAdvance_sampleStep p g ξ s call
  · simp only [proofCost, ite_eq_right hs, proofNext, rawAdvance, StochasticGradient.advance]

lemma rawAdvance_proofTrace (p : Params) (f : p.E → ℝ) (u : p.E)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (s : Iterate p.E) (n : ℕ)
    (hgood : ∀ i < n, let q := blockTrace (proofCost p f u) (proofNext p f u g) s ξ i
      proofFailure p f u g (proofCost p f u q.1) q.1 (fun j => q.2 j) = 0) :
    rawAdvance p g ξ (blockCalls (proofCost p f u) (proofNext p f u g) s ξ n) 0 (resume p s) =
      resume p (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blockCalls_succ, rawAdvance_add, ih (fun i hi => hgood i (by omega)), Nat.zero_add]
    have hg := hgood n (by omega)
    have hg' : proofFailure p f u g
        (proofCost p f u (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1)
        (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1
        (fun i => ξ (blockCalls (proofCost p f u) (proofNext p f u g) s ξ n+i)) = 0 := by
      simpa only [blockTrace_tail] using hg
    rw [rawAdvance_proofNext p f u g ξ _ _ hg', blockTrace_succ]
    congr 2
    funext i
    exact (blockTrace_tail (proofCost p f u) (proofNext p f u g) s ξ n i).symm

lemma rawAdvance_after_target (p : Params) (f : p.E → ℝ) (u : p.E)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (s : Iterate p.E) (n K : ℕ)
    (hgood : ∀ i < n, let q := blockTrace (proofCost p f u) (proofNext p f u g) s ξ i
      proofFailure p f u g (proofCost p f u q.1) q.1 (fun j => q.2 j) = 0)
    (hK : blockCalls (proofCost p f u) (proofNext p f u g) s ξ n ≤ K)
    (hT : target p.R p.ε ≤ (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1.A) :
    rawAdvance p g ξ K 0 (resume p s) =
      .done (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1 := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [rawAdvance_add, rawAdvance_proofTrace p f u g ξ s n hgood]
  rw [resume, ite_eq_left hT]
  exact rawAdvance_done p g ξ _ _ _

lemma execute_after_target (p : Params) (P : MeasureTheory.ProbabilityMeasure (ℕ → p.Ω))
    (f : p.E → ℝ) (u : p.E) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (hεΔ : p.ε < p.Δ) (n K : ℕ)
    (hgood : ∀ i < n, let q := blockTrace (proofCost p f u) (proofNext p f u g) (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ i
      proofFailure p f u g (proofCost p f u q.1) q.1 (fun j => q.2 j) = 0)
    (hK : blockCalls (proofCost p f u) (proofNext p f u g)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ n ≤ K)
    (hT : target p.R p.ε ≤ (blockTrace (proofCost p f u) (proofNext p f u g)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ n).1.A) :
    execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm p) (fun _ => K) () ξ =
      (blockTrace (proofCost p f u) (proofNext p f u g)
        (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ n).1.x := by
  classical
  erw [StochasticGradient.execute_advance]
  change (algorithm p).output (rawAdvance p g ξ K 0 ((algorithm p).initial ())) = _
  have hi : (algorithm p).initial () = resume p (initialIterate p.L0 p.R p.Δ p.ε p.x0) := by
    simp only [algorithm, ite_eq_right (not_le.mpr hεΔ)]
  rw [hi, rawAdvance_after_target p f u g ξ _ n K hgood hK hT]
  rfl

end OracleTemplate.RobustGeneralized
