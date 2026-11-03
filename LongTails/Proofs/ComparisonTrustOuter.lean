import LongTails.Proofs.ComparisonTrustEpoch

namespace LongTails.Proofs.ComparisonTrustOuter

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion
  LongTails.Proofs.ComparisonTrustPlans LongTails.Proofs.ComparisonTrustTaylor
  LongTails.Proofs.ComparisonTrustGuess LongTails.Proofs.ComparisonTrustEpoch

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def outerPure (f : E → ℝ) (t : Tuning) (k : ℕ) (x0 : E) : E × List E :=
  loopPure (fun _ st => (selectPure f (epochCands f t st.1) (4 * t.J + 1) st.1,
    st.2 ++ selectPure f (epochCands f t st.1) (4 * t.J + 1) st.1 :: epochCands f t st.1))
    k 0 (x0, [x0])

lemma eval_outerPlan (f : E → ℝ) (t : Tuning) (x0 : E) :
    QueryPlan.eval (cmpOf f) (outerPlan t x0) = outerPure f t t.T x0 := by
  simp only [outerPlan, eval_loop, outerStep, QueryPlan.eval_map, eval_epochPlan, outerPure]

theorem outer_visits {f : E → ℝ} {L ρ : ℝ} (h : Smooth f L ρ) {t : Tuning}
    {ε G δ K θ Δ : ℝ} (hR : Rel E t L ρ ε G δ K θ) {x0 : E}
    (hgap : ∀ z, f x0 - f z ≤ Δ) (hG : 2 * L * Δ ≤ G ^ 2) (hT : Δ < t.T * θ) :
    ∃ y ∈ (outerPure f t t.T x0).2, ‖gradient f y‖ ≤ ε := by
  have hG0 := hR.hG
  have key := loopPure_induction
    (fun _ st => (selectPure f (epochCands f t st.1) (4 * t.J + 1) st.1,
      st.2 ++ selectPure f (epochCands f t st.1) (4 * t.J + 1) st.1 :: epochCands f t st.1))
    (fun k st => st.1 ∈ st.2 ∧ f st.1 ≤ f x0 ∧
      ((∃ y ∈ st.2, ‖gradient f y‖ ≤ ε) ∨ f st.1 ≤ f x0 - k * θ))
    (x0, [x0]) ⟨List.mem_singleton_self _, le_rfl, Or.inr (by simp)⟩
    (fun k st ⟨hmem, hle, hor⟩ => by
      have hbest := (select_spec f (epochCands f t st.1) (4 * t.J + 1) st.1).1
      have hlen := length_epochCands f t st.1
      refine ⟨List.mem_append_right _ (by simp), hbest.trans hle, ?_⟩
      rcases hor with ⟨y, hy, hyg⟩ | hdec
      · exact Or.inl ⟨y, List.mem_append_left _ hy, hyg⟩
      by_cases hst : ‖gradient f st.1‖ ≤ ε
      · exact Or.inl ⟨st.1, List.mem_append_left _ hmem, hst⟩
      push Not at hst
      have hgs := h.grad_sq_bound hR.hL hgap hle
      have hcG : ‖gradient f st.1‖ ≤ G := by
        have : ‖gradient f st.1‖ ^ 2 ≤ G ^ 2 := hgs.trans hG
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) hG0 (by norm_num)).mp this
      rcases epoch_progress h hR st.1 hst hcG with ⟨y, hy, hyg⟩ | ⟨y, hy, hyf⟩
      · exact Or.inl ⟨y, List.mem_append_right _ (List.mem_cons_of_mem _ hy), hyg⟩
      · right
        have := select_le_mem f (le_of_eq hlen) st.1 hy
        push_cast
        linarith) t.T
  obtain ⟨_, _, hor⟩ := key
  rcases hor with hvis | hdec
  · exact hvis
  · exfalso
    have := hgap (outerPure f t t.T x0).1
    have : f (outerPure f t t.T x0).1 ≤ f x0 - t.T * θ := hdec
    linarith

end

end LongTails.Proofs.ComparisonTrustOuter
