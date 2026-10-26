import LongTails.Proofs.FairExecution

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory

variable {E : Type} [MeasurableSpace E]

abbrev StateCode (cfg : Config) (E : Type) := Fin (max 1 cfg.T) × ℕ × ℕ × ℕ × Bool × E × (ℕ → E) × (ℕ → E) × E × E × E × E × E

def stateEquiv (cfg : Config) : State cfg E ≃ StateCode cfg E where
  toFun s := (s.outputIndex, s.t, s.blockIndex, s.sampleIndex, s.second, s.secondPoint, s.left, s.right, s.accumulator, s.point, s.previous, s.estimate, s.selected)
  invFun w := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by rcases w with ⟨outputIndex, t, blockIndex, sampleIndex, second, secondPoint, left, right, accumulator, point, previous, estimate, selected⟩; rfl

instance (cfg : Config) : MeasurableSpace (State cfg E) :=
  MeasurableSpace.comap (stateEquiv cfg) inferInstance

lemma measurable_stateCode (cfg : Config) : Measurable (stateEquiv (E := E) cfg) := comap_measurable _

@[fun_prop]
lemma measurable_state_outputIndex (cfg : Config) : Measurable (fun s : State cfg E => s.outputIndex) :=
  (measurable_stateCode cfg).fst

@[fun_prop]
lemma measurable_state_t (cfg : Config) : Measurable (fun s : State cfg E => s.t) :=
  (measurable_stateCode cfg).snd.fst

@[fun_prop]
lemma measurable_state_blockIndex (cfg : Config) : Measurable (fun s : State cfg E => s.blockIndex) :=
  (measurable_stateCode cfg).snd.snd.fst

@[fun_prop]
lemma measurable_state_sampleIndex (cfg : Config) : Measurable (fun s : State cfg E => s.sampleIndex) :=
  (measurable_stateCode cfg).snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_second (cfg : Config) : Measurable (fun s : State cfg E => s.second) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_secondPoint (cfg : Config) : Measurable (fun s : State cfg E => s.secondPoint) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_left (cfg : Config) : Measurable (fun s : State cfg E => s.left) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_right (cfg : Config) : Measurable (fun s : State cfg E => s.right) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_accumulator (cfg : Config) : Measurable (fun s : State cfg E => s.accumulator) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_point (cfg : Config) : Measurable (fun s : State cfg E => s.point) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_previous (cfg : Config) : Measurable (fun s : State cfg E => s.previous) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_estimate (cfg : Config) : Measurable (fun s : State cfg E => s.estimate) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop]
lemma measurable_state_selected (cfg : Config) : Measurable (fun s : State cfg E => s.selected) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd

lemma measurable_state_mk {Ξ : Type} [MeasurableSpace Ξ] (cfg : Config)
    {outputIndex : Ξ → Fin (max 1 cfg.T)} (h_outputIndex : Measurable outputIndex)
    {t : Ξ → ℕ} (h_t : Measurable t)
    {blockIndex : Ξ → ℕ} (h_blockIndex : Measurable blockIndex)
    {sampleIndex : Ξ → ℕ} (h_sampleIndex : Measurable sampleIndex)
    {second : Ξ → Bool} (h_second : Measurable second)
    {secondPoint : Ξ → E} (h_secondPoint : Measurable secondPoint)
    {left : Ξ → (ℕ → E)} (h_left : Measurable left)
    {right : Ξ → (ℕ → E)} (h_right : Measurable right)
    {accumulator : Ξ → E} (h_accumulator : Measurable accumulator)
    {point : Ξ → E} (h_point : Measurable point)
    {previous : Ξ → E} (h_previous : Measurable previous)
    {estimate : Ξ → E} (h_estimate : Measurable estimate)
    {selected : Ξ → E} (h_selected : Measurable selected)
    : Measurable (fun z => (⟨outputIndex z, t z, blockIndex z, sampleIndex z, second z, secondPoint z, left z, right z, accumulator z, point z, previous z, estimate z, selected z⟩ : State cfg E)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z => (outputIndex z, t z, blockIndex z, sampleIndex z, second z, secondPoint z, left z, right z, accumulator z, point z, previous z, estimate z, selected z))
  fun_prop

@[fun_prop]
lemma measurable_refreshFlag (cfg : Config) : Measurable cfg.isRefresh := measurable_of_countable _

@[fun_prop]
lemma measurable_batchSize (cfg : Config) : Measurable cfg.batch := measurable_of_countable _

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] in
lemma measurable_query (cfg : Config) : Measurable (query (E := E) cfg) := by
  exact Measurable.ite (measurableSet_eq_fun (measurable_state_second cfg) measurable_const)
    (measurable_state_secondPoint cfg) (measurable_state_point cfg)

omit [CompleteSpace E] in
lemma measurable_commitObservation (cfg : Config) :
    Measurable (fun z : State cfg E × E => commitObservation cfg z.1 z.2) := by
  have hcast : Measurable (fun z : State cfg E × E => (cfg.batch z.1.t : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (cfg.batch n : ℝ))).comp (by fun_prop)
  have he : Measurable (fun z : State cfg E × E =>
      (cfg.batch z.1.t : ℝ)⁻¹ • (z.1.accumulator + z.2) +
        if cfg.isRefresh z.1.t then 0 else z.1.estimate) := by
    apply Measurable.add (by fun_prop)
    exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) measurable_const (by fun_prop)
  have hsel : Measurable (fun z : State cfg E × E =>
      if z.1.t = z.1.outputIndex.val then z.1.point else z.1.selected) := by
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop)) <;> fun_prop
  unfold commitObservation
  apply Measurable.ite
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · apply measurable_state_mk
    all_goals fun_prop
  · apply measurable_state_mk
    all_goals try dsimp only [NormalizedStorm.stormStep]
    all_goals fun_prop

omit [CompleteSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma measurable_arrayUpdate {Ξ : Type} [MeasurableSpace Ξ]
    {a : Ξ → ℕ → E} {i : Ξ → ℕ} {v : Ξ → E}
    (ha : Measurable a) (hi : Measurable i) (hv : Measurable v) :
    Measurable (fun z => Function.update (a z) (i z) (v z)) := by
  apply Measurable.of_eval
  intro j
  simp only [Function.update_apply]
  exact Measurable.ite (measurableSet_eq_fun measurable_const hi) hv ((measurable_pi_apply j).comp ha)

lemma measurable_finishBlock (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R) :
    Measurable (fun z : State cfg E × (ℕ → E) => finishBlock cfg z.1 z.2) := by
  have hl : Measurable (fun z : State cfg E × (ℕ → E) => fun i : Fin cfg.m => z.1.left i) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply (i : ℕ)).comp ((measurable_state_left cfg).comp measurable_fst)
  have hr : Measurable (fun z : State cfg E × (ℕ → E) => fun i : Fin cfg.m => z.2 i) := by fun_prop
  have hv : Measurable (fun z : State cfg E × (ℕ → E) =>
      if cfg.isRefresh z.1.t then refresh cfg.R cfg.G (fun i : Fin cfg.m => z.1.left i)
      else increment cfg.R cfg.B (fun i : Fin cfg.m => z.1.left i) (fun i : Fin cfg.m => z.2 i)) := by
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    · simpa only [Function.comp_def] using (measurable_refresh hm hR cfg.G).comp hl
    · simpa only [Function.comp_def] using (measurable_increment hm hR cfg.B).comp (hl.prodMk hr)
  simpa only [Function.comp_def, finishBlock] using
    (measurable_commitObservation cfg).comp (measurable_fst.prodMk hv)

lemma measurable_update (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R) :
    Measurable (fun z : State cfg E × E => update cfg z.1 z.2) := by
  have hl : Measurable (fun z : State cfg E × E => Function.update z.1.left z.1.sampleIndex z.2) :=
    measurable_arrayUpdate (by fun_prop) (by fun_prop) measurable_snd
  have hr : Measurable (fun z : State cfg E × E => Function.update z.1.right z.1.sampleIndex z.2) :=
    measurable_arrayUpdate (by fun_prop) (by fun_prop) measurable_snd
  have hp : Measurable (fun z : State cfg E × E => (points cfg z.1).2) :=
    Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)
  unfold update
  apply Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_fst
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  · apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · apply measurable_state_mk
      all_goals fun_prop
    · exact (measurable_finishBlock cfg hm hR).comp (measurable_fst.prodMk hr)
  · apply measurable_state_mk
    all_goals fun_prop

variable {Ω : Type} [MeasurableSpace Ω]

noncomputable def rawState (cfg : Config) (g : E → Ω → E) (x0 : E)
    (τ : Fin (max 1 cfg.T)) (ξ : ℕ → Ω) : ℕ → State cfg E
  | 0 => (algorithm cfg x0).initial τ
  | n + 1 => update cfg (rawState cfg g x0 τ ξ n)
      (g (query cfg (rawState cfg g x0 τ ξ n)) (ξ n))

lemma measurable_rawState (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E) :
    ∀ n, Measurable (fun z : Fin (max 1 cfg.T) × (ℕ → Ω) => rawState cfg g x0 z.1 z.2 n)
  | 0 => by
      dsimp only [rawState, algorithm]
      apply measurable_state_mk
      all_goals fun_prop
  | n + 1 => by
      have hi := measurable_rawState cfg hm hR hg x0 n
      have hq := (measurable_query cfg).comp hi
      have hr := hg.comp (hq.prodMk ((measurable_pi_apply n).comp measurable_snd))
      simpa only [rawState, Function.comp_def, Function.uncurry_apply_pair] using
        (measurable_update cfg hm hR).comp (hi.prodMk hr)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω] in
lemma execute_rawState (cfg : Config) (g : E → Ω → E) (x0 : E)
    (O : Oracle E E) (τ : Fin (max 1 cfg.T)) (ξ : (k : ℕ) → O.Seed k) (ζ : ℕ → Ω)
    (hanswer : ∀ history x, O.answer history (0, x) (ξ history.length) = g x (ζ history.length))
    (K : ℕ) : execute O (algorithm cfg x0) (fun _ => K) τ ξ =
      (rawState cfg g x0 τ ζ K).selected := by
  have hans : ∀ history query, O.answer history query (ξ history.length) = g query.2 (ζ history.length) := by
    intro history query
    have hi : query.1 = 0 := Subsingleton.elim _ _
    simpa only [← hi] using hanswer history query.2
  erw [execute_indexed_of_answer O _ _ _ ξ (fun k query => g query.2 (ζ k)) hans]
  let step : State cfg E × ℕ → State cfg E × ℕ := fun z =>
    (update cfg z.1 (g (query cfg z.1) (ζ z.2)), z.2 + 1)
  have he : ∀ n, step^[n] ((algorithm cfg x0).initial τ, 0) = (rawState cfg g x0 τ ζ n, n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl
  change output cfg (step^[K] ((algorithm cfg x0).initial τ, 0)).1 = _
  rw [he]
  rfl

lemma measurable_execute (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E)
    (P : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    Measurable (fun z : Fin (max 1 cfg.T) × (ℕ → Ω) =>
      execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } : Oracle E E)
        (algorithm cfg x0) (fun _ => K) z.1 z.2) := by
  have he : (fun z : Fin (max 1 cfg.T) × (ℕ → Ω) =>
      execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } : Oracle E E)
        (algorithm cfg x0) (fun _ => K) z.1 z.2) =
      fun z => (rawState cfg g x0 z.1 z.2 K).selected := by
    funext z
    exact execute_rawState cfg g x0
      ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } : Oracle E E)
      z.1 z.2 z.2 (fun _ _ => rfl) K
  rw [he]
  exact (measurable_state_selected cfg).comp (measurable_rawState cfg hm hR hg x0 K)

end OracleTemplate.FairVarianceReduction
