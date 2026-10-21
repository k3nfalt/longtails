import LongTails.Proofs.QueryPlan
import LongTails.Algorithms.NearZeroSumFoam

open private _run from LongTails.Template

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

variable {Q R U V : Type*}

def safeQueries (valid : Q → Prop) (g : Q → R) : {k : ℕ} → QueryPlan Q R U k → Prop
  | _, .done _ => True
  | _, .ask q next => valid q ∧ safeQueries valid g (next (g q))

lemma safe_queries_bind {valid : Q → Prop} {g : Q → R} {k m : ℕ}
    (plan : QueryPlan Q R U k) (next : U → QueryPlan Q R V m)
    (hp : safeQueries valid g plan)
    (hn : safeQueries valid g (next (QueryPlan.eval g plan))) :
    safeQueries valid g (plan.bind next) := by
  induction plan with
  | done value => exact hn
  | ask q rest ih => exact ⟨hp.1, ih (g q) hp.2 hn⟩

lemma safe_queries_map {valid : Q → Prop} {g : Q → R} {k : ℕ}
    (plan : QueryPlan Q R U k) (f : U → V) (hp : safeQueries valid g plan) :
    safeQueries valid g (plan.map f) := by
  induction plan with
  | done value => trivial
  | ask q rest ih => exact ⟨hp.1, ih (g q) hp.2⟩

lemma advance_safe_plan {valid : Q → Prop} {g : Q → R} (q0 : Q)
    (answer : ℕ → Q → R) (ha : ∀ k q, valid q → answer k q = g q)
    {k K : ℕ} (plan : QueryPlan Q R U k) (hp : safeQueries valid g plan)
    (hK : k ≤ K) (call : ℕ) :
    StochasticGradient.advance (fun k s => QueryPlan.update s (answer k (QueryPlan.query q0 s)))
      K call ⟨k, plan⟩ = ⟨0, QueryPlan.done (QueryPlan.eval g plan)⟩ := by
  induction plan generalizing K call with
  | done value =>
      induction K generalizing call with
      | zero => rfl
      | succ K ih => exact ih (Nat.zero_le K) (call + 1)
  | @ask k q rest ih =>
      cases K with
      | zero => omega
      | succ K =>
          change StochasticGradient.advance
            (fun i s => QueryPlan.update s (answer i (QueryPlan.query q0 s)))
            K (call + 1) (⟨k, rest (answer call q)⟩ : Σ n, QueryPlan Q R U n) = _
          rw [ha call q hp.1]
          exact ih (g q) hp.2 (by omega) (call + 1)

lemma execute_safe_plan {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (k K : ℕ) (plan : S → QueryPlan Q R U k) (g : Q → R) (valid : Q → Prop)
    (oracle : Oracle Q R) (seed : S) (ω : (i : ℕ) → oracle.Seed i)
    (ha : ∀ history q, valid q → oracle.answer history (0, q) (ω history.length) = g q)
    (hp : safeQueries valid g (plan seed)) (hK : k ≤ K) :
    execute oracle (QueryPlan.algorithm law q0 u0 k plan) (fun _ => K) seed ω =
      QueryPlan.eval g (plan seed) := by
  let answer : List ((Fin 1 × Q) × R) → (Fin 1 × Q) → R := fun history query =>
    oracle.answer history query (ω history.length)
  let A := QueryPlan.algorithm law q0 u0 k plan
  have hrun : ∀ (fuel : ℕ) (history : List ((Fin 1 × Q) × R))
      (remaining : Fin 1 → ℕ) (j : ℕ) (p : QueryPlan Q R U j),
      safeQueries valid g p → j ≤ fuel → j ≤ remaining 0 →
      (_run answer A fuel history remaining ⟨j, p⟩).1 = QueryPlan.eval g p := by
    intro fuel
    induction fuel with
    | zero =>
        intro history remaining j p hp hf hr
        have hj : j = 0 := by omega
        subst j
        cases p with
        | done value => rfl
    | succ fuel ih =>
        intro history remaining j p hp hf hr
        cases p with
        | done value =>
            let st : A.State := ⟨0, .done value⟩
            have hquery : A.query st = (0, q0) := rfl
            have hupdate : A.update st (answer history (0, q0)) = st := rfl
            have houtput : A.output st = value := rfl
            by_cases hz : remaining 0 = 0
            · simp only [_run, st, hquery, hz, ite_true, houtput, QueryPlan.eval]
            · have hnextRemaining : 0 ≤ (Function.update remaining 0 (remaining 0 - 1)) 0 := by
                simp only [Function.update_self]
                omega
              let r := answer history (0, q0)
              have hnext := ih (history ++ [((0, q0), r)])
                (Function.update remaining 0 (remaining 0 - 1)) 0
                (.done value) trivial (by omega) hnextRemaining
              simpa only [_run, st, hquery, hz, ite_false, hupdate, r, QueryPlan.eval] using hnext
        | @ask j q next =>
            have hpositive : 0 < remaining 0 := by omega
            have hnextFuel : j ≤ fuel := by omega
            have hnextRemaining : j ≤ (Function.update remaining 0 (remaining 0 - 1)) 0 := by
              simp only [Function.update_self]
              omega
            have hanswer := ha history q hp.1
            let st : A.State := ⟨j + 1, .ask q next⟩
            have hquery : A.query st = (0, q) := rfl
            have hupdate : A.update st (g q) = ⟨j, next (g q)⟩ := rfl
            have hanswer' : answer history (0, q) = g q := by
              simpa [answer] using hanswer
            have hnext := ih (history ++ [((0, q), g q)])
              (Function.update remaining 0 (remaining 0 - 1)) j (next (g q)) hp.2
              hnextFuel hnextRemaining
            have hnotzero : remaining 0 ≠ 0 := by omega
            simp only [_run, st, hquery, hnotzero, ite_false, hanswer', hupdate, QueryPlan.eval]
            exact hnext
  unfold execute executeWithTrace
  change (_run answer A K [] (fun _ => K) (A.initial seed)).1 = _
  exact hrun K [] (fun _ => K) k (plan seed) hp hK hK

lemma eval_repeatQueries {S : Type*} {c : ℕ} (g : Q → R)
    (step : S → QueryPlan Q R S c) (n : ℕ) (s : S) :
    QueryPlan.eval g (repeatQueries step n s) =
      (fun t => QueryPlan.eval g (step t))^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [repeatQueries, QueryPlan.eval_bind, ih, Function.iterate_succ_apply]

lemma safe_repeatQueries {S : Type*} {c : ℕ} {g : Q → R} {valid : Q → Prop}
    (step : S → QueryPlan Q R S c) (good : S → Prop)
    (hstep : ∀ s, good s → safeQueries valid g (step s) ∧ good (QueryPlan.eval g (step s)))
    (n : ℕ) (s : S) (hs : good s) :
    safeQueries valid g (repeatQueries step n s) ∧ good (QueryPlan.eval g (repeatQueries step n s)) := by
  induction n generalizing s with
  | zero => exact ⟨trivial, hs⟩
  | succ n ih =>
      obtain ⟨hp, hv⟩ := hstep s hs
      obtain ⟨hr, ho⟩ := ih _ hv
      exact ⟨safe_queries_bind _ _ hp hr, by simpa only [repeatQueries, QueryPlan.eval_bind] using ho⟩

section Feasible

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def feasibleQuery (C : Set (Joint E F)) : Joint E F ⊕ Joint E F → Prop
  | .inl u => u ∈ C
  | .inr _ => True

lemma eval_fieldQuery (B P : Joint E F → Joint E F) (β : ℝ) (center u : Joint E F) :
    QueryPlan.eval (Sum.elim B P) (fieldQuery β center u) = B u + β • (u - center) := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma eval_projectionQuery (B P : Joint E F → Joint E F) (u : Joint E F) :
    QueryPlan.eval (Sum.elim B P) (projectionQuery u) = P u := rfl

lemma eval_innerFieldQuery (B P : Joint E F → Joint E F) (cfg : FoamConfig) (β : ℝ)
    (center : Joint E F) (zg : E) (yg : F) (u : Joint E F) :
    QueryPlan.eval (Sum.elim B P) (innerFieldQuery cfg β center zg yg u) =
      pair ((B u + β • (u - center)).fst - (cfg.a / 2) • u.fst - (1 / 2 : ℝ) • zg)
        ((B u + β • (u - center)).snd + (cfg.a / 8) • (u.snd - yg)) := rfl

lemma safe_fieldQuery {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (β : ℝ) (center u : Joint E F) (hu : u ∈ C) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (fieldQuery β center u) := ⟨hu, trivial⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma safe_projectionQuery {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (u : Joint E F) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (projectionQuery u) := ⟨trivial, trivial⟩

lemma safe_innerFieldQuery {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (cfg : FoamConfig) (β : ℝ) (center : Joint E F) (zg : E) (yg : F)
    (u : Joint E F) (hu : u ∈ C) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (innerFieldQuery cfg β center zg yg u) :=
  safe_queries_map _ _ (safe_fieldQuery B P β center u hu)

lemma safe_innerEagStep {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (hP : ∀ u, P u ∈ C) (cfg : FoamConfig) (β : ℝ) (center : Joint E F) (zg : E) (yg : F)
    (u0 : Joint E F) (st : InnerState E F) (hst : st.point ∈ C) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (innerEagStep cfg β center zg yg u0 st) ∧
      (QueryPlan.eval (Sum.elim B P) (innerEagStep cfg β center zg yg u0 st)).point ∈ C := by
  constructor
  · apply safe_queries_bind _ _ (safe_innerFieldQuery B P cfg β center zg yg _ hst)
    apply safe_queries_bind _ _ (safe_projectionQuery B P _)
    apply safe_queries_bind _ _ (safe_innerFieldQuery B P cfg β center zg yg _ (hP _))
    exact safe_queries_map _ _ (safe_projectionQuery B P _)
  · simp only [innerEagStep, QueryPlan.eval_bind, QueryPlan.eval_map, eval_projectionQuery]
    exact hP _

lemma safe_foamStep {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (hP : ∀ u, P u ∈ C) (cfg : FoamConfig) (β : ℝ) (center : Joint E F) (s : FoamState E F) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (foamStep cfg β center s) ∧
      pair (QueryPlan.eval (Sum.elim B P) (foamStep cfg β center s)).xf
        (QueryPlan.eval (Sum.elim B P) (foamStep cfg β center s)).yf ∈ C := by
  dsimp only [foamStep]
  have hr := safe_repeatQueries (g := Sum.elim B P) (valid := feasibleQuery C)
    (innerEagStep cfg β center (cfg.α • s.z + (1 - cfg.α) • s.zf)
      (cfg.α • s.y + (1 - cfg.α) • s.yf)
      (P (pair ((-1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        (cfg.α • s.y + (1 - cfg.α) • s.yf))))
    (fun st => st.point ∈ C) (fun st hst => safe_innerEagStep B P hP cfg β center _ _ _ st hst)
    cfg.innerSteps ⟨0, P (pair ((-1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        (cfg.α • s.y + (1 - cfg.α) • s.yf)), 0⟩ (hP _)
  constructor
  · apply safe_queries_bind _ _ (safe_projectionQuery B P _)
    apply safe_queries_bind _ _ hr.1
    exact safe_queries_map _ _ (safe_fieldQuery B P β center _ hr.2)
  · erw [QueryPlan.eval_bind, eval_projectionQuery, QueryPlan.eval_bind, QueryPlan.eval_map]
    exact hr.2


lemma safe_foamInitial {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (hP : ∀ u, P u ∈ C) (cfg : FoamConfig) (β : ℝ) (center u0 : Joint E F) (hu0 : u0 ∈ C) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (foamInitial cfg β center u0) := by
  apply safe_queries_bind _ _ (safe_fieldQuery B P β center u0 hu0)
  apply safe_queries_bind _ _ (safe_projectionQuery B P _)
  exact safe_queries_map _ _ (safe_fieldQuery B P β center _ (hP _))

lemma safe_foamPlan {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (hP : ∀ u, P u ∈ C) (cfg : FoamConfig) (β : ℝ) (center u0 : Joint E F) (hu0 : u0 ∈ C) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (foamPlan cfg β center u0) ∧
      QueryPlan.eval (Sum.elim B P) (foamPlan cfg β center u0) ∈ C := by
  have hr := safe_repeatQueries (g := Sum.elim B P) (valid := feasibleQuery C)
    (foamStep cfg β center) (fun _ => True)
    (fun s _ => ⟨(safe_foamStep B P hP cfg β center s).1, trivial⟩)
    cfg.outerSteps (QueryPlan.eval (Sum.elim B P) (foamInitial cfg β center u0)) trivial
  constructor
  · apply safe_queries_bind _ _ (safe_foamInitial B P hP cfg β center u0 hu0)
    apply safe_queries_bind _ _ hr.1
    exact safe_projectionQuery B P _
  · unfold foamPlan
    erw [QueryPlan.eval_bind, QueryPlan.eval_bind, eval_projectionQuery]
    exact hP _

lemma safe_proximalFoamPlan {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (hP : ∀ u, P u ∈ C) (cfg : FoamConfig) (β : ℝ) (N : ℕ) (u0 : Joint E F) (hu0 : u0 ∈ C) :
    safeQueries (feasibleQuery C) (Sum.elim B P) (proximalFoamPlan cfg β N u0) ∧
      QueryPlan.eval (Sum.elim B P) (proximalFoamPlan cfg β N u0) ∈ C :=
  safe_repeatQueries _ (fun u => u ∈ C) (fun u hu => safe_foamPlan B P hP cfg β u u hu) N u0 hu0

lemma execute_proximalFoam {C : Set (Joint E F)} (B P : Joint E F → Joint E F)
    (hP : ∀ u, P u ∈ C) (cfg : FoamConfig) (β : ℝ) (N K : ℕ) (u0 : Joint E F) (hu0 : u0 ∈ C)
    (oracle : Oracle (Joint E F ⊕ Joint E F) (Joint E F))
    (hf : ∀ history seed u, u ∈ C →
      oracle.answer history (0, Sum.inl u) seed = B u)
    (hp : ∀ history seed u,
      oracle.answer history (0, Sum.inr u) seed = P u)
    (ω : (i : ℕ) → oracle.Seed i) (hK : foamCalls cfg * N ≤ K) :
    execute oracle (proximalFoam cfg β N u0) (fun _ => K) () ω =
      QueryPlan.eval (Sum.elim B P) (proximalFoamPlan cfg β N u0) := by
  apply execute_safe_plan _ _ _ _ _ _ (Sum.elim B P) (feasibleQuery C) oracle () ω
  · intro history q hq
    cases q with
    | inl u => exact hf history (ω history.length) u hq
    | inr u => exact hp history (ω history.length) u
  · exact (safe_proximalFoamPlan B P hP cfg β N u0 hu0).1
  · exact hK


lemma eag_anchor_eq (u0 u : Joint E F) (k : ℕ) :
    eagAnchor u0 u k = (1 / (k + 1 : ℝ)) • u0 + (1 - 1 / (k + 1 : ℝ)) • u := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have he : (k : ℝ) / (k + 1) = 1 - 1 / (k + 1) := by field_simp; ring
  rw [eagAnchor, he]
  module

lemma inner_eag_execution (B P : Joint E F → Joint E F) (cfg : FoamConfig) (hη : cfg.η ≠ 0)
    (β : ℝ) (center : Joint E F) (zg : E) (yg : F) (u0 : Joint E F) (n : ℕ) :
    let A := fun u => cfg.η • QueryPlan.eval (Sum.elim B P) (innerFieldQuery cfg β center zg yg u)
    let st := QueryPlan.eval (Sum.elim B P)
      (repeatQueries (innerEagStep cfg β center zg yg u0) n ⟨0, u0, 0⟩)
    st.index = n ∧ st.point = eagIterate P A u0 n ∧ st.normal = (1 / cfg.η) • eagNormal P A u0 n := by
  let A := fun u => cfg.η • QueryPlan.eval (Sum.elim B P) (innerFieldQuery cfg β center zg yg u)
  let step := fun st => QueryPlan.eval (Sum.elim B P) (innerEagStep cfg β center zg yg u0 st)
  rw [eval_repeatQueries]
  change (step^[n] ⟨0, u0, 0⟩).index = n ∧
    (step^[n] ⟨0, u0, 0⟩).point = eagIterate P A u0 n ∧
    (step^[n] ⟨0, u0, 0⟩).normal = (1 / cfg.η) • eagNormal P A u0 n
  induction n with
  | zero => simp [eagIterate, eagNormal]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      generalize he : step^[n] ⟨0, u0, 0⟩ = st at ih ⊢
      simp only [step, innerEagStep, QueryPlan.eval_bind, QueryPlan.eval_map,
        eval_projectionQuery, ih.1, ih.2.1]
      refine ⟨trivial, ?_, ?_⟩
      · simp only [eagIterate, eag_anchor_eq, A]
      · simp only [eagNormal, eagIterate, eag_anchor_eq, A]
        simp only [smul_sub, smul_smul, one_div_mul_cancel hη, one_smul]
        module

end Feasible

end OracleTemplate.NearZeroSum
