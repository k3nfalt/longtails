import LongTails.Algorithms.SublevelWeightedGradient
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.SymmetricThirdOrderSampling

namespace OracleTemplate.SublevelWeighted

open MeasureTheory
variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def mean (g : E → Ω → E) (x : E) (n start : ℕ) (ξ : ℕ → Ω) : E :=
  (1 / (n : ℝ)) • ∑ i : Fin n, g x (ξ (start + i))

noncomputable def point (L : ℝ) (x0 : E) (b : ℕ → ℕ) (g : E → Ω → E) (ξ : ℕ → Ω) : ℕ → E
  | 0 => x0
  | k + 1 =>
    let x := point L x0 b g ξ k
    x - (1 / L) • mean g x (b k) (calls b k) ξ

omit [InnerProductSpace ℝ E] in
lemma eval_collect (x : E) (g : E → Ω → E) (ξ : ℕ → Ω) (n start : ℕ) :
    (collect x n).sampledEval g ξ start = ∑ i : Fin n, g x (ξ (start + i)) := by
  induction n generalizing start with
  | zero => simp [collect, QueryPlan.sampledEval]
  | succ n ih =>
    simp only [collect, QueryPlan.sampledEval, QueryPlan.sampledEval_map, ih, Fin.sum_univ_succ,
      Fin.val_zero, Nat.add_zero, Fin.val_succ]
    simp [Nat.add_comm, Nat.add_left_comm]

lemma eval_output (L : ℝ) (x0 : E) (b : ℕ → ℕ) (g : E → Ω → E) (ξ : ℕ → Ω) (K : ℕ) :
    (outputPlan L x0 b K).sampledEval g ξ 0 = point L x0 b g ξ K := by
  induction K with
  | zero => rfl
  | succ k ih =>
    unfold outputPlan
    erw [QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
    rw [ih, eval_collect]
    simp [point, mean]

lemma point_congr (L : ℝ) (x0 : E) (b : ℕ → ℕ) (g : E → Ω → E) {ξ ζ : ℕ → Ω} (k : ℕ)
    (h : ∀ i < calls b k, ξ i = ζ i) : point L x0 b g ξ k = point L x0 b g ζ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h₁ := ih (fun i hi => h i (by simp [calls]; omega))
    simp only [point, h₁, mean]
    congr 3
    apply Finset.sum_congr rfl
    intro i _
    rw [h (calls b k + i.val) (by simp only [calls]; omega)]

variable [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma measurable_point (L : ℝ) (x0 : E) (b : ℕ → ℕ) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (k : ℕ) : Measurable (fun ξ => point L x0 b g ξ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact ih.sub ((Finset.measurable_sum _ fun i _ => hg.comp
      (ih.prodMk (measurable_pi_apply (calls b k + i.val)))).const_smul _ |>.const_smul _)

end OracleTemplate.SublevelWeighted
