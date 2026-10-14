import LongTails.Proofs.StochasticGeneralizedExecution
import LongTails.Proofs.StochasticGeneralizedBudget

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight energy)

lemma rawAdvance_proofNext (p : Params) (f : p.E → ℝ) (u : p.E)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (s : Iterate p.E) (call : ℕ) :
    rawAdvance p g ξ (proofCost p f u s) call (resume p s) =
      resume p (proofNext p f u g (proofCost p f u s) s (fun i => ξ (call+i))) := by
  classical
  by_cases hs : proofActive p f u s
  · have hA : ¬target p.R p.ε ≤ s.A := not_le.mpr hs.2.2.1
    simp only [proofCost, ite_eq_left hs, proofNext]
    rw [ite_eq_left hs, resume, ite_eq_right hA]
    exact rawAdvance_prefixStep p g ξ s _ call (batchSize_pos p.σ p.ε p.δ s)
  · simp only [proofCost, ite_eq_right hs, proofNext, rawAdvance, StochasticGradient.advance]

lemma rawAdvance_proofTrace (p : Params) (f : p.E → ℝ) (u : p.E)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (s : Iterate p.E) (n : ℕ) :
    rawAdvance p g ξ (blockCalls (proofCost p f u) (proofNext p f u g) s ξ n) 0 (resume p s) =
      resume p (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blockCalls_succ, rawAdvance_add, ih, Nat.zero_add, rawAdvance_proofNext, blockTrace_succ]
    congr 2
    funext i
    exact (blockTrace_tail (proofCost p f u) (proofNext p f u g) s ξ n i).symm

lemma rawAdvance_after_target (p : Params) (f : p.E → ℝ) (u : p.E)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (s : Iterate p.E) (n K : ℕ)
    (hK : blockCalls (proofCost p f u) (proofNext p f u g) s ξ n ≤ K)
    (hT : target p.R p.ε ≤ (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1.A) :
    rawAdvance p g ξ K 0 (resume p s) =
      .done (blockTrace (proofCost p f u) (proofNext p f u g) s ξ n).1 := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [rawAdvance_add, rawAdvance_proofTrace]
  rw [resume, ite_eq_left hT]
  exact rawAdvance_done p g ξ _ _ _

lemma execute_after_target (p : Params) (P : MeasureTheory.ProbabilityMeasure (ℕ → p.Ω))
    (f : p.E → ℝ) (u : p.E) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (hεΔ : p.ε < p.Δ) (n K : ℕ)
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
  rw [hi, rawAdvance_after_target p f u g ξ _ n K hK hT]
  rfl

end OracleTemplate.StochasticGeneralized
