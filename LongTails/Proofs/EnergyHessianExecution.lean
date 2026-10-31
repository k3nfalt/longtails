import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Proofs.QueryPlan
import LongTails.Proofs.EnergyHessianParameters

namespace LongTails.Proofs.EnergyHessianExecution

open OracleTemplate OracleTemplate.QueryPlan LongTails.Algorithms.EnergyHessianReuse

variable {Q R U : Type} {n : ℕ}

def counts (g : Fin n × Q → R) : {k : ℕ} → QueryPlan (Fin n × Q) R U k → Fin n → ℕ
  | _, .done _ => fun _ => 0
  | _, .ask q rest => fun i => (if i = q.1 then 1 else 0) + counts g (rest (g q)) i

lemma counts_sum (g : Fin n × Q → R) {k : ℕ} (plan : QueryPlan (Fin n × Q) R U k) :
    ∑ i, counts g plan i = k := by
  induction plan with
  | done value => simp [counts]
  | @ask k q rest ih => simp [counts, Finset.sum_add_distrib, ih, Nat.add_comm]

lemma counts_positive (g : Fin n × Q → R) (q0 : Fin n × Q)
    (s : Σ k, QueryPlan (Fin n × Q) R U k) (hs : 0 < s.1) :
    0 < counts g s.2 (query q0 s).1 := by
  obtain ⟨k, plan⟩ := s
  cases plan with
  | done value => simp at hs
  | ask q rest => simp [query, counts]

lemma counts_update (g : Fin n × Q → R) (q0 : Fin n × Q)
    (s : Σ k, QueryPlan (Fin n × Q) R U k) (b : Fin n → ℕ)
    (hb : ∀ i, counts g s.2 i ≤ b i) :
    ∀ i, counts g (update s (g (query q0 s))).2 i ≤
      Function.update b (query q0 s).1 (b (query q0 s).1 - 1) i := by
  obtain ⟨k, plan⟩ := s
  cases plan with
  | done value => intro i; simp [update, counts]
  | ask q rest =>
    intro i
    have h := hb i
    by_cases hi : i = q.1
    · subst i
      simp only [counts, ite_true] at h
      simp only [update, query, Function.update_self]
      omega
    · simpa [update, query, counts, hi] using h

lemma length_update (g : Fin n × Q → R) (q0 : Fin n × Q)
    (s : Σ k, QueryPlan (Fin n × Q) R U k) :
    (update s (g (query q0 s))).1 = s.1 - 1 := by
  obtain ⟨k, plan⟩ := s
  cases plan <;> rfl

lemma eval_update (g : Fin n × Q → R) (q0 : Fin n × Q)
    (s : Σ k, QueryPlan (Fin n × Q) R U k) :
    eval g (update s (g (query q0 s))).2 = eval g s.2 := by
  obtain ⟨k, plan⟩ := s
  cases plan <;> rfl

lemma output_of_length_zero (g : Fin n × Q → R) (u0 : U)
    (s : Σ k, QueryPlan (Fin n × Q) R U k) (hs : s.1 = 0) :
    output u0 s = eval g s.2 := by
  obtain ⟨k, plan⟩ := s
  cases plan with
  | done value => rfl
  | ask q rest => simp at hs

lemma execute_of_counts (g : Fin n × Q → R) (q0 : Fin n × Q) (u0 : U)
    {K : ℕ} (plan : QueryPlan (Fin n × Q) R U K)
    (O : Oracle Q R n) (budget : Fin n → ℕ)
    (hO : ∀ k q seed, O.answer k q seed = g q)
    (hb : ∀ i, counts g plan i ≤ budget i)
    (seed : (channelAlgorithm q0 u0 plan).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (channelAlgorithm q0 u0 plan) budget seed ξ = eval g plan := by
  let state : ℕ → (Σ k, QueryPlan (Fin n × Q) R U k) :=
    fun k => (fun s => update s (g (query q0 s)))^[k] ⟨K, plan⟩
  have hstate0 : state 0 = ⟨K, plan⟩ := rfl
  have hstep (k : ℕ) : state (k + 1) = update (state k) (g (query q0 (state k))) :=
    Function.iterate_succ_apply' _ _ _
  let remaining : ℕ → Fin n → ℕ := fun k =>
    Nat.rec budget (fun j b => Function.update b (query q0 (state j)).1
      (b (query q0 (state j)).1 - 1)) k
  have hremaining0 : remaining 0 = budget := rfl
  have hremaining (k : ℕ) : remaining (k + 1) =
      Function.update (remaining k) (query q0 (state k)).1
        (remaining k (query q0 (state k)).1 - 1) := rfl
  have hcover (k : ℕ) : ∀ i, counts g (state k).2 i ≤ remaining k i := by
    induction k with
    | zero => exact hb
    | succ k ih => rw [hstep, hremaining]; exact counts_update g q0 (state k) _ ih
  have hlength (k : ℕ) : (state k).1 = K - k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, length_update, ih]; omega
  have heval (k : ℕ) : eval g (state k).2 = eval g plan := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, eval_update, ih]
  apply execute_eq_of_safe_prefix O (channelAlgorithm q0 u0 plan) budget seed ξ
    state remaining K (eval g plan)
  · rfl
  · intro k
    change state (k.length + 1) = update (state k.length)
      (O.answer k (query q0 (state k.length)) (ξ k.length))
    rw [hO, hstep]
  · rfl
  · exact hremaining
  · intro k hk
    exact (counts_positive g q0 (state k) (by rw [hlength]; omega)).trans_le
      (hcover k _)
  · intro k hk
    change output u0 (state k) = _
    rw [output_of_length_zero g u0 (state k) (by rw [hlength]; omega), heval]
  · rw [← counts_sum g plan]
    exact Finset.sum_le_sum (fun i _ => hb i)

lemma counts_bind {V : Type} (g : Fin n × Q → R) {k m : ℕ}
    (plan : QueryPlan (Fin n × Q) R U k) (next : U → QueryPlan (Fin n × Q) R V m)
    (i : Fin n) :
    counts g (bind plan next) i = counts g plan i + counts g (next (eval g plan)) i := by
  induction plan with
  | done value => simp [QueryPlan.bind, counts, eval]
  | ask q rest ih => simp only [QueryPlan.bind, counts, eval, ih]; omega

lemma counts_map {V : Type} (g : Fin n × Q → R) (f : U → V) {k : ℕ}
    (plan : QueryPlan (Fin n × Q) R U k) (i : Fin n) :
    counts g (map f plan) i = counts g plan i := by
  induction plan with
  | done value => rfl
  | ask q rest ih => simp only [map, counts, ih]

lemma counts_iterate {p : LongTails.Setups.GradientDependentHessian.Params} {c : ℕ}
    (g : Fin 2 × p.E → Reply p) (step : Point p → Plan p (Point p) c)
    (i : Fin 2) (d : ℕ) (h : ∀ a, counts g (step a) i = d) (N : ℕ) (a : Point p) :
    counts g (iteratePlans step N a) i = d * N := by
  induction N generalizing a with
  | zero => simp [iteratePlans, counts]
  | succ N ih => rw [iteratePlans, counts_bind, h, ih]; ring

lemma counts_lazy (p : LongTails.Setups.GradientDependentHessian.Params)
    (g : Fin 2 × p.E → Reply p) (B : p.E →L[ℝ] p.E) (N : ℕ)
    (a : Point p) (energy path : ℝ) (i : Fin 2) :
    counts g (lazySteps p B N a energy path) i = if i = 0 then N else 0 := by
  induction N generalizing a energy path with
  | zero => simp [lazySteps, counts]
  | succ N ih => simp only [lazySteps, counts, ih]; split_ifs <;> omega

lemma counts_fresh (p : LongTails.Setups.GradientDependentHessian.Params)
    (g : Fin 2 × p.E → Reply p) (a : Point p) (i : Fin 2) :
    counts g (fresh p a) i = 1 := by
  fin_cases i <;> simp [fresh, counts]

lemma counts_block (p : LongTails.Setups.GradientDependentHessian.Params)
    (g : Fin 2 × p.E → Reply p) (a : Point p) (i : Fin 2) :
    counts g (block p a) i = if i = 0 then p.m + 1 else 2 := by
  fin_cases i <;> simp [block, counts, counts_lazy, Nat.add_comm]

lemma counts_plan (p : LongTails.Setups.GradientDependentHessian.Params)
    (g : Fin 2 × p.E → Reply p) (i : Fin 2) :
    counts g (plan p) i =
      if i = 0 then burnCount p + blockCount p * (p.m + 1) + 1
      else burnCount p + 2 * blockCount p := by
  simp only [plan, counts, counts_bind, counts_map,
    counts_iterate g (fresh p) i 1 (fun a => counts_fresh p g a i),
    counts_iterate g (block p) i (if i = 0 then p.m + 1 else 2)
      (fun a => counts_block p g a i)]
  split_ifs <;> ring

noncomputable def replies (p : LongTails.Setups.GradientDependentHessian.Params) (f : p.E → ℝ)
    (q : Fin 2 × p.E) : Reply p :=
  if q.1 = 0 then Sum.inl (gradient f q.2) else Sum.inr (fderiv ℝ (gradient f) q.2)

structure Correct (p : LongTails.Setups.GradientDependentHessian.Params) (f : p.E → ℝ)
    (a : Point p) : Prop where
  gradient_eq : a.g = gradient f a.x
  best_eq : ‖gradient f a.best‖ = a.bestNorm
  best_le : a.bestNorm ≤ ‖a.g‖

lemma correct_initial (p : LongTails.Setups.GradientDependentHessian.Params) (f : p.E → ℝ) :
    Correct p f (initial p (gradient f p.x0)) := ⟨rfl, rfl, le_rfl⟩

lemma correct_move (p : LongTails.Setups.GradientDependentHessian.Params) (f : p.E → ℝ)
    (a : Point p) (s : p.E) (h : Correct p f a) :
    Correct p f (move p a s (gradient f (a.x + s))) := by
  exact ⟨rfl, EnergyHessianParameters.move_best_gradient p (gradient f) a s h.best_eq,
    min_le_left _ _⟩

lemma eval_lazy_correct (p : LongTails.Setups.GradientDependentHessian.Params) (f : p.E → ℝ)
    (B : p.E →L[ℝ] p.E) (N : ℕ) (a : Point p) (energy path : ℝ) (h : Correct p f a) :
    Correct p f (eval (replies p f) (lazySteps p B N a energy path)) ∧
      (eval (replies p f) (lazySteps p B N a energy path)).bestNorm ≤ a.bestNorm := by
  induction N generalizing a energy path with
  | zero => exact ⟨h, le_rfl⟩
  | succ N ih =>
    simp only [lazySteps, eval, replies, ite_true, readGradient]
    obtain ⟨hc, hb⟩ := ih _ _ _ (correct_move p f a _ h)
    exact ⟨hc, hb.trans (min_le_right _ _)⟩

lemma eval_fresh_correct (p : LongTails.Setups.GradientDependentHessian.Params) (f : p.E → ℝ)
    (a : Point p) (h : Correct p f a) :
    Correct p f (eval (replies p f) (fresh p a)) ∧
      (eval (replies p f) (fresh p a)).bestNorm ≤ a.bestNorm := by
  simpa [fresh, eval, replies, readGradient, readHessian] using
    (show Correct p f (move p a
      (selectedStep p a.g (fderiv ℝ (gradient f) a.x) 0 (coefficient p a)).1
      (gradient f (a.x + (selectedStep p a.g (fderiv ℝ (gradient f) a.x) 0 (coefficient p a)).1))) ∧
      (move p a (selectedStep p a.g (fderiv ℝ (gradient f) a.x) 0 (coefficient p a)).1
      (gradient f (a.x + (selectedStep p a.g (fderiv ℝ (gradient f) a.x) 0 (coefficient p a)).1))).bestNorm ≤ a.bestNorm
      from ⟨correct_move p f a _ h, min_le_right _ _⟩)

lemma eval_block_correct (p : LongTails.Setups.GradientDependentHessian.Params) (f : p.E → ℝ)
    (a : Point p) (h : Correct p f a) :
    Correct p f (eval (replies p f) (block p a)) ∧
      (eval (replies p f) (block p a)).bestNorm ≤ a.bestNorm := by
  simp only [block, eval, replies, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    ite_true, readHessian, readGradient]
  obtain ⟨hc, hb⟩ := eval_lazy_correct p f _ _ _ _ _ (correct_move p f a _ h)
  exact ⟨hc, hb.trans (min_le_right _ _)⟩

lemma eval_iterate_correct {p : LongTails.Setups.GradientDependentHessian.Params} {c : ℕ}
    (f : p.E → ℝ) (step : Point p → Plan p (Point p) c)
    (hs : ∀ a, Correct p f a → Correct p f (eval (replies p f) (step a)) ∧
      (eval (replies p f) (step a)).bestNorm ≤ a.bestNorm)
    (N : ℕ) (a : Point p) (h : Correct p f a) :
    Correct p f (eval (replies p f) (iteratePlans step N a)) ∧
      (eval (replies p f) (iteratePlans step N a)).bestNorm ≤ a.bestNorm := by
  induction N generalizing a with
  | zero => exact ⟨h, le_rfl⟩
  | succ N ih =>
    rw [iteratePlans, eval_bind]
    obtain ⟨hnext, hbest⟩ := hs a h
    obtain ⟨hc, hb⟩ := ih _ hnext
    exact ⟨hc, hb.trans hbest⟩

end LongTails.Proofs.EnergyHessianExecution
