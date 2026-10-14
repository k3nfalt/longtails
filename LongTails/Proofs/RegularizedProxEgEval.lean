import LongTails.Algorithms.RegularizedProxExtragradient
import LongTails.Proofs.SampledQueryPlan
import LongTails.Setups.StochasticCohypomonotoneInclusion

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

open QueryPlan

section General

variable {Q R U V Ω : Type*}

def evalP (g : Q → Ω → R) {k : ℕ} (plan : QueryPlan Q R U k) (ξ : ℕ → Ω) : U :=
  sampledEval g ξ plan 0

lemma sampledEval_shift (g : Q → Ω → R) {k : ℕ} (plan : QueryPlan Q R U k) :
    ∀ (ξ : ℕ → Ω) (call : ℕ), sampledEval g ξ plan call = sampledEval g (fun i => ξ (call + i)) plan 0 := by
  induction plan with
  | done value => intro ξ call; rfl
  | ask q next ih =>
      intro ξ call
      simp only [sampledEval]
      rw [ih _ ξ (call + 1), ih _ (fun i => ξ (call + i)) 1]
      simp only [Nat.add_zero]
      congr 1
      funext i
      congr 1
      omega

lemma evalP_bind (g : Q → Ω → R) {k m : ℕ} (plan : QueryPlan Q R U k)
    (next : U → QueryPlan Q R V m) (ξ : ℕ → Ω) :
    evalP g (plan.bind next) ξ = evalP g (next (evalP g plan ξ)) (fun i => ξ (k + i)) := by
  unfold evalP
  rw [sampledEval_bind, Nat.zero_add, sampledEval_shift]

lemma evalP_map (g : Q → Ω → R) (f : U → V) {k : ℕ} (plan : QueryPlan Q R U k) (ξ : ℕ → Ω) :
    evalP g (plan.map f) ξ = f (evalP g plan ξ) := sampledEval_map g ξ f plan 0

lemma evalP_ask (g : Q → Ω → R) {k : ℕ} (q : Q) (next : R → QueryPlan Q R U k) (ξ : ℕ → Ω) :
    evalP g (QueryPlan.ask q next) ξ = evalP g (next (g q (ξ 0))) (fun i => ξ (1 + i)) := by
  unfold evalP
  simp only [sampledEval]
  rw [sampledEval_shift]

end General

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma evalP_batchSum (g : E → Ω → E) (J : ℝ → E → E) (x : E) :
    ∀ (b : ℕ) (ξ : ℕ → Ω), evalP (reply g J) (batchSum x b) ξ = ∑ i : Fin b, g x (ξ i)
  | 0, ξ => by simp [evalP, batchSum, sampledEval]
  | b + 1, ξ => by
      rw [batchSum, evalP_ask, evalP_map, evalP_batchSum g J x b, Fin.sum_univ_succ]
      simp only [reply, Sum.elim_inl, Fin.val_zero, Fin.val_succ]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_comm]

omit [InnerProductSpace ℝ E] in
omit [NormedAddCommGroup E] in
lemma evalP_resolvent (g : E → Ω → E) (J : ℝ → E → E) (γ : ℝ) (y : E) (ξ : ℕ → Ω) :
    evalP (reply g J) (resolventQuery γ y) ξ = J γ y := by
  rw [resolventQuery, evalP_ask]
  try rfl

noncomputable def egOut (g : E → Ω → E) (J : ℝ → E → E) (γ α Λ : ℝ) (b : ℕ) (c x : E)
    (u : Fin b → Ω) (t : ℕ → Ω) : E :=
  x - (α * γ) • (γ⁻¹ • (x - J γ (x - γ • ((1 / (b : ℝ)) • ∑ i, g x (u i) + Λ • (x - c)))) -
      ((1 / (b : ℝ)) • ∑ i, g x (u i) + Λ • (x - c)) +
    ((1 / (b : ℝ)) • ∑ i : Fin b, g (J γ (x - γ • ((1 / (b : ℝ)) • ∑ i, g x (u i) + Λ • (x - c))))
        (t (1 + i)) +
      Λ • (J γ (x - γ • ((1 / (b : ℝ)) • ∑ i, g x (u i) + Λ • (x - c))) - c)))

lemma evalP_egStep (g : E → Ω → E) (J : ℝ → E → E) (γ α Λ : ℝ) (b : ℕ) (c x : E) (ξ : ℕ → Ω) :
    evalP (reply g J) (egStep γ α Λ b c x) ξ =
      egOut g J γ α Λ b c x (fun i => ξ i) (fun i => ξ (b + i)) := by
  rw [egStep, evalP_bind, evalP_batchSum, evalP_bind, evalP_resolvent, evalP_map, evalP_batchSum]
  simp only [egOut]

omit [InnerProductSpace ℝ E] in
omit [NormedAddCommGroup E] in
lemma evalP_repeat {c : ℕ} (g : (E ⊕ (ℝ × E)) → Ω → E)
    (step : E → QueryPlan (E ⊕ (ℝ × E)) E E c) (n : ℕ) (x : E) (ξ : ℕ → Ω) :
    evalP g (repeatPlan step (n + 1) x) ξ =
      evalP g (repeatPlan step n (evalP g (step x) ξ)) (fun i => ξ (c + i)) := by
  rw [repeatPlan, evalP_bind]

end OracleTemplate.StochasticCohypomonotone
