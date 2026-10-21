import LongTails.Algorithms.CompositeLazyCubic
import LongTails.Proofs.EnergyHessianExecution
import LongTails.Proofs.CompositeModel
import LongTails.Proofs.CompositeLocalObjective

set_option maxRecDepth 4096

namespace LongTails.Proofs.CompositeLazyCubicExecution

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Algorithms.CompositeLazyCubic
open LongTails.Proofs.EnergyHessianExecution

def queriesSatisfy {Q R U : Type} (g : Q → R) (P : Q → Prop) :
    {k : ℕ} → QueryPlan Q R U k → Prop
  | _, .done _ => True
  | _, .ask q rest => P q ∧ queriesSatisfy g P (rest (g q))

lemma queriesSatisfy_map {Q R U V : Type} (g : Q → R) (P : Q → Prop) (f : U → V)
    {k : ℕ} (plan : QueryPlan Q R U k) :
    queriesSatisfy g P (plan.map f) ↔ queriesSatisfy g P plan := by
  induction plan with
  | done value => rfl
  | ask q rest ih => simp only [QueryPlan.map, queriesSatisfy, ih]

lemma queriesSatisfy_bind {Q R U V : Type} (g : Q → R) (P : Q → Prop)
    {k m : ℕ} (plan : QueryPlan Q R U k) (next : U → QueryPlan Q R V m) :
    queriesSatisfy g P (plan.bind next) ↔
      queriesSatisfy g P plan ∧ queriesSatisfy g P (next (eval g plan)) := by
  induction plan with
  | done value => simp [QueryPlan.bind, queriesSatisfy, eval]
  | ask q rest ih => simp only [QueryPlan.bind, queriesSatisfy, eval, ih, and_assoc]

lemma queriesSatisfy_update {Q R U : Type} {n : ℕ} (g : Fin n × Q → R)
    (P : Fin n × Q → Prop) (q0 : Fin n × Q)
    (state : Σ k, QueryPlan (Fin n × Q) R U k) (h : queriesSatisfy g P state.2) :
    queriesSatisfy g P (update state (g (query q0 state))).2 := by
  obtain ⟨k, plan⟩ := state
  cases plan with
  | done value => trivial
  | ask q rest => exact h.2

lemma update_agrees {Q R U : Type} {n : ℕ} (g : Fin n × Q → R)
    (P : Fin n × Q → Prop) (q0 : Fin n × Q) (O : Oracle Q R n)
    (hO : ∀ k q seed, P q → O.answer k q seed = g q)
    (state : Σ k, QueryPlan (Fin n × Q) R U k) (h : queriesSatisfy g P state.2)
    (call : List ((Fin n × Q) × R)) (ξ : O.Seed call.length) :
    update state (O.answer call (query q0 state) ξ) = update state (g (query q0 state)) := by
  obtain ⟨k, plan⟩ := state
  cases plan with
  | done value => rfl
  | ask q rest => simp only [query]; rw [hO call q ξ h.1]

lemma execute_of_valid_counts {Q R U : Type} {n : ℕ} (g : Fin n × Q → R)
    (P : Fin n × Q → Prop) (q0 : Fin n × Q) (u0 : U)
    {K : ℕ} (plan : QueryPlan (Fin n × Q) R U K)
    (O : Oracle Q R n) (budget : Fin n → ℕ)
    (hO : ∀ k q seed, P q → O.answer k q seed = g q)
    (hv : queriesSatisfy g P plan) (hb : ∀ i, counts g plan i ≤ budget i)
    (seed : (LongTails.Algorithms.EnergyHessianReuse.channelAlgorithm q0 u0 plan).Seed)
    (ξ : (k : ℕ) → O.Seed k) :
    execute O (LongTails.Algorithms.EnergyHessianReuse.channelAlgorithm q0 u0 plan) budget seed ξ = eval g plan := by
  let state : ℕ → (Σ k, QueryPlan (Fin n × Q) R U k) :=
    fun k => (fun s => update s (g (query q0 s)))^[k] ⟨K, plan⟩
  have hstep (k : ℕ) : state (k + 1) = update (state k) (g (query q0 (state k))) :=
    Function.iterate_succ_apply' _ _ _
  have hvalid (k : ℕ) : queriesSatisfy g P (state k).2 := by
    induction k with
    | zero => exact hv
    | succ k ih => rw [hstep]; exact queriesSatisfy_update g P q0 _ ih
  let remaining : ℕ → Fin n → ℕ := fun k =>
    Nat.rec budget (fun j b => Function.update b (query q0 (state j)).1
      (b (query q0 (state j)).1 - 1)) k
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
  apply execute_eq_of_safe_prefix O _ budget seed ξ state remaining K (eval g plan)
  · rfl
  · intro k
    change state (k.length + 1) = update (state k.length)
      (O.answer k (query q0 (state k.length)) (ξ k.length))
    rw [update_agrees g P q0 O hO _ (hvalid k.length), hstep]
  · rfl
  · exact hremaining
  · intro k hk
    exact (counts_positive g q0 (state k) (by rw [hlength]; omega)).trans_le (hcover k _)
  · intro k hk
    change output u0 (state k) = _
    rw [output_of_length_zero g u0 (state k) (by rw [hlength]; omega), heval]
  · rw [← counts_sum g plan]
    exact Finset.sum_le_sum (fun i _ => hb i)

noncomputable def modelAnswer {p : Params} (F : Problem p) (q : Model p) : p.E := by
  classical
  exact if h : ∃ z, q.solution F z then Classical.choose h else p.x0

noncomputable def canonicalReply {p : Params} (F : Problem p) (q : Fin 3 × (p.E ⊕ Model p)) : Reply p :=
  match q.2 with
  | .inl x => if q.1 = 0 then .inl (gradient F.f x) else .inr (fderiv ℝ (gradient F.f) x)
  | .inr model => .inl (modelAnswer F model)

def QueryValid {p : Params} (q : Fin 3 × (p.E ⊕ Model p)) : Prop :=
  match q.2 with
  | .inl _ => q.1 = 0 ∨ q.1 = 1
  | .inr model => q.1 = 2 ∧ model.valid

lemma modelAnswer_solution {p : Params} (F : Problem p) (q : Model p) (hq : q.valid)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) : q.solution F (modelAnswer F q) := by
  have he := CompositeModel.solution_exists q F hq hψ hclosed hx0
  simpa only [modelAnswer, dite_eq_left he] using Classical.choose_spec he

lemma oracle_agreement {p : Params} (F : Problem p) (O : Oracle (p.E ⊕ Model p) (Reply p) 3)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain)
    (hg : ∀ k x seed, O.answer k (0, Sum.inl x) seed = Sum.inl (gradient F.f x))
    (hH : ∀ k x seed, O.answer k (1, Sum.inl x) seed = Sum.inr (fderiv ℝ (gradient F.f) x))
    (hm : ∀ k q seed, q.valid → ∃ z, O.answer k (2, Sum.inr q) seed = Sum.inl z ∧ q.solution F z)
    (k : List ((Fin 3 × (p.E ⊕ Model p)) × Reply p))
    (q : Fin 3 × (p.E ⊕ Model p)) (seed : O.Seed k.length) (hv : QueryValid q) :
    O.answer k q seed = canonicalReply F q := by
  obtain ⟨i, x | q⟩ := q
  · change i = 0 ∨ i = 1 at hv
    rcases hv with hi | hi
    · subst i
      simpa [canonicalReply] using hg k x seed
    · subst i
      simpa [canonicalReply] using hH k x seed
  · change i = 2 ∧ q.valid at hv
    obtain ⟨hi, hq⟩ := hv
    subst i
    obtain ⟨z, hz, hs⟩ := hm k q seed hq
    have he := CompositeModel.solution_unique q F hq hs (modelAnswer_solution F q hq hψ hclosed hx0)
    simpa [canonicalReply, he] using hz

lemma extrapolated_queries_valid (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot point : p.E) (n i : ℕ) :
    queriesSatisfy g QueryValid (extrapolatedGradient p center snapshot point n i) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih =>
      simp only [extrapolatedGradient, queriesSatisfy, queriesSatisfy_map, QueryValid]
      exact ⟨Or.inl trivial, ih _⟩

lemma trial_queries_valid (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot point : p.E) (B : p.E →L[ℝ] p.E)
    (hB : ∀ y gy, (⟨y, gy, B, 0, regularizerScale p⟩ : Model p).valid) :
    queriesSatisfy g QueryValid (searchTrial p center snapshot point B) := by
  unfold searchTrial trialCalls
  rw [queriesSatisfy_bind]
  refine ⟨extrapolated_queries_valid p g _ _ _ _ _, ?_⟩
  simp only [queriesSatisfy, QueryValid, queriesSatisfy_map]
  exact ⟨⟨trivial, hB _ _⟩, extrapolated_queries_valid p g _ _ _ _ _⟩

lemma search_rounds_queries_valid (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E)
    (hB : ∀ y gy, (⟨y, gy, B, 0, regularizerScale p⟩ : Model p).valid)
    (n : ℕ) (state : SearchState p) :
    queriesSatisfy g QueryValid (searchRounds p center snapshot x v B n state) := by
  induction n generalizing state with
  | zero => trivial
  | succ n ih =>
      simp only [searchRounds, queriesSatisfy_bind]
      exact ⟨trial_queries_valid p g _ _ _ B hB, ih _⟩

lemma search_queries_valid (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E)
    (hB : ∀ y gy, (⟨y, gy, B, 0, regularizerScale p⟩ : Model p).valid) :
    queriesSatisfy g QueryValid (guardedSearch p center snapshot x v B) := by
  simp only [guardedSearch, queriesSatisfy_bind, queriesSatisfy_map]
  exact ⟨trial_queries_valid p g _ _ _ B hB, trial_queries_valid p g _ _ _ B hB,
    search_rounds_queries_valid p g _ _ _ _ B hB _ _⟩

lemma accelerated_queries_valid (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot : p.E) (B : p.E →L[ℝ] p.E)
    (hB : ∀ y gy, (⟨y, gy, B, 0, regularizerScale p⟩ : Model p).valid)
    (n k : ℕ) (state : LongTails.Algorithms.CompositeGuardedSearch.AccelerationState p.E) :
    queriesSatisfy g QueryValid (acceleratedRounds p center snapshot B n k state) := by
  induction n generalizing k state with
  | zero => trivial
  | succ n ih =>
      simp only [acceleratedRounds, queriesSatisfy_bind]
      exact ⟨search_queries_valid p g _ _ _ _ B hB, ih _ _⟩

lemma epoch_queries_valid {p : Params} (F : Problem p) (center snapshot : p.E) {Δ : ℝ}
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hΔ : 0 < Δ) :
    queriesSatisfy (canonicalReply F) QueryValid (gapEpoch p center snapshot Δ) := by
  simp only [gapEpoch, queriesSatisfy, QueryValid, queriesSatisfy_map]
  refine ⟨Or.inr trivial, ?_⟩
  simp only [canonicalReply, show (1 : Fin 3) ≠ 0 by decide, ite_false, readHessian]
  exact accelerated_queries_valid p _ center snapshot _
    (fun y gy => CompositeLocalObjective.snapshot_model_valid F center snapshot y gy hf hconv hH hm hΔ) _ _ _

lemma gap_queries_valid {p : Params} (F : Problem p) (center point : p.E) {Δ : ℝ}
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hΔ : 0 < Δ) (n : ℕ) :
    queriesSatisfy (canonicalReply F) QueryValid (gapRounds p center n point Δ) := by
  induction n generalizing point Δ with
  | zero => trivial
  | succ n ih =>
      simp only [gapRounds, queriesSatisfy_bind]
      exact ⟨epoch_queries_valid F center point hf hconv hH hm hΔ, ih _ (by positivity)⟩

lemma cubic_step_queries_valid {p : Params} (F : Problem p) (center point : p.E)
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) :
    queriesSatisfy (canonicalReply F) QueryValid (cubicStep p center point) := by
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hH0 := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hvalid : (⟨point, localGradient p center point (gradient F.f point),
      localHessian p center point (fderiv ℝ (gradient F.f) point), localHessianLip p, 1⟩ : Model p).valid :=
    ⟨by norm_num, hH0.le, CompositeLocalObjective.localHessian_symmetric F center point hf,
      CompositeLocalObjective.localHessian_nonneg F center point hf hconv hγ.le, Or.inl hH0⟩
  simp [cubicStep, queriesSatisfy, QueryValid, canonicalReply, readVector, readHessian, hvalid]

lemma padding_queries_valid (p : Params) {U : Type}
    (g : Fin 3 × (p.E ⊕ Model p) → Reply p) (value : U) (n : ℕ) :
    queriesSatisfy g QueryValid (padGradients p value n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨Or.inl rfl, ih⟩

lemma cubic_solve_queries_valid {p : Params} (F : Problem p) (center : p.E)
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) :
    queriesSatisfy (canonicalReply F) QueryValid (cubicSolve p center) := by
  unfold cubicSolve cubicSolveCalls
  rw [queriesSatisfy_bind, queriesSatisfy_bind]
  refine ⟨cubic_step_queries_valid F center center hf hconv hH hm,
    cubic_step_queries_valid F center _ hf hconv hH hm, ?_⟩
  split
  · exact padding_queries_valid p _ _ _
  · rename_i hn
    rw [queriesSatisfy_bind]
    refine ⟨gap_queries_valid F center _ hf hconv hH hm ?_ _,
      cubic_step_queries_valid F center _ hf hconv hH hm⟩
    have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
    have hr := norm_pos_iff.mpr hn
    positivity

lemma outer_queries_valid {p : Params} (F : Problem p)
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (n : ℕ)
    (state : LongTails.Algorithms.CompositeCubicAcceleration.State p.E) :
    queriesSatisfy (canonicalReply F) QueryValid (outerRounds p n state) := by
  induction n generalizing state with
  | zero => trivial
  | succ n ih =>
      simp only [outerRounds, queriesSatisfy_bind]
      refine ⟨cubic_solve_queries_valid F _ hf hconv hH hm, ?_⟩
      split
      · exact padding_queries_valid p _ _ _
      · exact ih _

lemma plan_queries_valid {p : Params} (F : Problem p)
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) :
    queriesSatisfy (canonicalReply F) QueryValid (plan p) :=
  outer_queries_valid F hf hconv hH hm _ _

lemma extrapolated_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot point : p.E) (n i : ℕ) :
    counts g (extrapolatedGradient p center snapshot point n i) 1 = 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [extrapolatedGradient, counts, counts_map, ih]

lemma trial_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot point : p.E) (B : p.E →L[ℝ] p.E) :
    counts g (searchTrial p center snapshot point B) 1 = 0 := by
  unfold searchTrial trialCalls
  rw [counts_bind]
  simp [counts, counts_map, extrapolated_hessian_count]

lemma search_rounds_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E) (n : ℕ) (state : SearchState p) :
    counts g (searchRounds p center snapshot x v B n state) 1 = 0 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [searchRounds, counts_bind, trial_hessian_count, ih]

lemma search_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E) :
    counts g (guardedSearch p center snapshot x v B) 1 = 0 := by
  simp [guardedSearch, counts_bind, counts_map, trial_hessian_count, search_rounds_hessian_count]

lemma accelerated_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot : p.E) (B : p.E →L[ℝ] p.E) (n k : ℕ)
    (state : LongTails.Algorithms.CompositeGuardedSearch.AccelerationState p.E) :
    counts g (acceleratedRounds p center snapshot B n k state) 1 = 0 := by
  induction n generalizing k state with
  | zero => rfl
  | succ n ih => simp [acceleratedRounds, counts_bind, search_hessian_count, ih]

lemma epoch_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot : p.E) (Δ : ℝ) : counts g (gapEpoch p center snapshot Δ) 1 = 1 := by
  simp [gapEpoch, counts, counts_map, accelerated_hessian_count]

lemma gap_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center point : p.E) (Δ : ℝ) (n : ℕ) : counts g (gapRounds p center n point Δ) 1 = n := by
  induction n generalizing point Δ with
  | zero => rfl
  | succ n ih => simp [gapRounds, counts_bind, epoch_hessian_count, ih, Nat.add_comm]

lemma cubic_step_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center point : p.E) : counts g (cubicStep p center point) 1 = 1 := by
  simp [cubicStep, counts]

lemma padding_hessian_count (p : Params) {U : Type} (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (value : U) (n : ℕ) : counts g (padGradients p value n) 1 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [padGradients, counts, ih]

lemma cubic_solve_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center : p.E) : counts g (cubicSolve p center) 1 ≤ gapIterations p + 3 := by
  unfold cubicSolve cubicSolveCalls
  rw [counts_bind, counts_bind]
  simp only [cubic_step_hessian_count]
  split
  · simp [padding_hessian_count]
  · simp only [counts_bind, gap_hessian_count, cubic_step_hessian_count]
    omega

lemma outer_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (n : ℕ) (state : LongTails.Algorithms.CompositeCubicAcceleration.State p.E) :
    counts g (outerRounds p n state) 1 ≤ (gapIterations p + 3) * n := by
  induction n generalizing state with
  | zero => simp [outerRounds, counts]
  | succ n ih =>
      simp only [outerRounds, counts_bind]
      have hc := cubic_solve_hessian_count p g
        (LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) state)
      split
      · have hp := padding_hessian_count p g
          (eval g (cubicSolve p (LongTails.Algorithms.CompositeCubicAcceleration.center p.E
            (outerCoefficient p) state))).point (cubicSolveCalls p * n)
        nlinarith only [hc, hp]
      · calc
          _ ≤ (gapIterations p + 3) + (gapIterations p + 3) * n := Nat.add_le_add hc (ih _)
          _ ≤ _ := by nlinarith

lemma plan_hessian_count (p : Params) (g : Fin 3 × (p.E ⊕ Model p) → Reply p) :
    counts g (plan p) 1 ≤ (gapIterations p + 3) * outerIterations p :=
  outer_hessian_count p g _ _

lemma channel_count_le_length {p : Params} {U : Type} {k : ℕ}
    (g : Fin 3 × (p.E ⊕ Model p) → Reply p) (plan : Plan p U k) (i : Fin 3) :
    counts g plan i ≤ k := by
  have h := Finset.single_le_sum (fun j _ => Nat.zero_le (counts g plan j)) (Finset.mem_univ i)
  exact h.trans_eq (counts_sum g plan)

lemma execute_eq_canonical (p : Params) (hp : spec.valid p) (F : Problem p)
    (O : Oracle (p.E ⊕ Model p) (Reply p) 3) (hF : spec.admissible p F O)
    (budget : Fin 3 → ℕ)
    (hHess : (gapIterations p + 3) * outerIterations p ≤ budget 1)
    (hOther : ∀ i, i ≠ 1 → cubicSolveCalls p * outerIterations p ≤ budget i)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) budget seed ξ = eval (canonicalReply F) (plan p) := by
  obtain ⟨hf, hconv, hLip, hψ, hclosed, hx0, hxstar, hdist, hmin, hg, hH, hm⟩ := hF
  apply execute_of_valid_counts (canonicalReply F) QueryValid (0, .inl p.x0) p.x0 (plan p) O budget
  · exact oracle_agreement F O hψ hclosed hx0 hg hH hm
  · exact plan_queries_valid F hf hconv hp.1 hp.2.2.2
  · intro i
    by_cases hi : i = 1
    · subst i
      exact (plan_hessian_count p _).trans hHess
    · exact (channel_count_le_length _ (plan p) i).trans (hOther i hi)

end LongTails.Proofs.CompositeLazyCubicExecution
