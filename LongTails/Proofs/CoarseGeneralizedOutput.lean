import LongTails.Proofs.CoarseGeneralizedOracle
import LongTails.Proofs.CoarseGeneralizedBatchExecution

open MeasureTheory

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

abbrev CombinedCode (E : Type*) :=
  (Search E × ℕ × ℕ × (ℕ → E)) ⊕ (E × RobustGeneralized.State E)

def combinedCode {E : Type*} : CombinedState E → CombinedCode E
  | .warm s b r v => .inl (s, b, r, v)
  | .final x s => .inr (x, s)

def codeCombined {E : Type*} : CombinedCode E → CombinedState E
  | .inl (s, b, r, v) => .warm s b r v
  | .inr (x, s) => .final x s

instance measurableSpaceCombined {E : Type*} [MeasurableSpace E] : MeasurableSpace (CombinedState E) :=
  MeasurableSpace.comap combinedCode inferInstance

instance measurableSpaceAlgorithmState (p : Params) : MeasurableSpace (algorithm p).State :=
  inferInstanceAs (MeasurableSpace (CombinedState p.E))

lemma measurable_combinedCode {E : Type*} [MeasurableSpace E] : Measurable (@combinedCode E) :=
  comap_measurable _

lemma measurable_combined_uncurry {E α β : Type*} [MeasurableSpace E]
    [MeasurableSpace α] [MeasurableSpace β] {F : CombinedState E → α → β}
    (hw : Measurable (fun w : (Search E × ℕ × ℕ × (ℕ → E)) × α =>
      F (.warm w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2) w.2))
    (hf : Measurable (fun w : (E × RobustGeneralized.State E) × α => F (.final w.1.1 w.1.2) w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : CombinedCode E × α => F (codeCombined w.1) w.2) := by
    apply (MeasurableEquiv.sumProdDistrib (Search E × ℕ × ℕ × (ℕ → E))
      (E × RobustGeneralized.State E) α).symm.measurable_comp_iff.mp
    exact measurable_fun_sum hw hf
  have hh := hm.comp ((measurable_combinedCode.comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  rcases w with ⟨s, a⟩
  cases s <;> rfl

@[fun_prop] lemma measurable_combined_warm {E α : Type*} [MeasurableSpace E] [MeasurableSpace α]
    {s : α → Search E} {b r : α → ℕ} {v : α → ℕ → E}
    (hs : Measurable s) (hb : Measurable b) (hr : Measurable r) (hv : Measurable v) :
    Measurable (fun a => CombinedState.warm (s a) (b a) (r a) (v a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl.comp (hs.prodMk (hb.prodMk (hr.prodMk hv)))

@[fun_prop] lemma measurable_combined_final {E α : Type*} [MeasurableSpace E] [MeasurableSpace α]
    {x : α → E} {s : α → RobustGeneralized.State E} (hx : Measurable x) (hs : Measurable s) :
    Measurable (fun a => CombinedState.final (x a) (s a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (hx.prodMk hs)

lemma restart_query (p : Params) (x : p.E) (s : RobustGeneralized.State p.E) :
    ((RobustGeneralized.algorithm (restartParams p x)).query s).2 =
      ((RobustGeneralized.algorithm (restartParams p p.x0)).query s).2 := by cases s <;> rfl

lemma restart_update (p : Params) (x : p.E) (s : RobustGeneralized.State p.E) (h : p.E) :
    (RobustGeneralized.algorithm (restartParams p x)).update s h =
      (RobustGeneralized.algorithm (restartParams p p.x0)).update s h := by cases s <;> rfl

lemma restart_output (p : Params) (x : p.E) (s : RobustGeneralized.State p.E) :
    (RobustGeneralized.algorithm (restartParams p x)).output s =
      (RobustGeneralized.algorithm (restartParams p p.x0)).output s := by cases s <;> rfl

lemma measurable_restart_initial (p : Params) :
    Measurable (fun x : p.E => (show RobustGeneralized.State p.E from by exact (RobustGeneralized.algorithm (restartParams p x)).initial ())) := by
  dsimp only [RobustGeneralized.algorithm, restartParams, RobustGeneralized.resume,
    StochasticGeneralized.initialIterate]
  split_ifs
  all_goals first
    | exact RobustGeneralized.measurable_state_done
        (StochasticGeneralized.measurable_iterate_mk measurable_const measurable_id measurable_id measurable_const)
    | exact RobustGeneralized.measurable_state_first
        (StochasticGeneralized.measurable_iterate_mk measurable_const measurable_id measurable_id measurable_const)
        measurable_const (by
          change Measurable (fun _ : p.E => (fun _ : ℕ => (0 : p.E)))
          exact measurable_const)

@[fun_prop] lemma measurable_startFinal (p : Params) : Measurable (startFinal p) := by
  exact measurable_combined_final measurable_id (measurable_restart_initial p)

lemma measurable_algorithm_query (p : Params) :
    Measurable (fun s : CombinedState p.E => ((algorithm p).query s).2) := by
  have hh : Measurable (fun w : CombinedState p.E × Unit => ((algorithm p).query w.1).2) := by
    apply measurable_combined_uncurry (F := fun (s : CombinedState p.E) (_ : Unit) => ((algorithm p).query s).2)
    · dsimp [algorithm]
      fun_prop
    · dsimp only [algorithm]
      simp_rw [restart_query]
      exact (RobustGeneralized.measurable_algorithm_query (restartParams p p.x0)).comp (by fun_prop)
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_algorithm_output (p : Params) : Measurable (algorithm p).output := by
  have hh : Measurable (fun w : CombinedState p.E × Unit => (algorithm p).output w.1) := by
    apply measurable_combined_uncurry (F := fun (s : CombinedState p.E) (_ : Unit) => (algorithm p).output s)
    · dsimp [algorithm]
      fun_prop
    · dsimp only [algorithm]
      simp_rw [restart_output]
      exact (RobustGeneralized.measurable_algorithm_output (restartParams p p.x0)).comp (by fun_prop)
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_algorithm_update (p : Params) :
    Measurable (fun w : CombinedState p.E × p.E => (algorithm p).update w.1 w.2) := by
  apply measurable_combined_uncurry
  · dsimp [algorithm]
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · fun_prop
    · apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      · fun_prop
      · fun_prop
  · dsimp only [algorithm]
    simp_rw [restart_update]
    apply measurable_combined_final (by fun_prop)
    exact (RobustGeneralized.measurable_algorithm_update (restartParams p p.x0)).comp
      (measurable_fst.snd.prodMk measurable_snd)

lemma measurable_rawAdvance (p : Params) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) (n call : ℕ) :
    Measurable (fun w : CombinedState p.E × (ℕ → p.Ω) => rawAdvance p g w.2 n call w.1) := by
  induction n generalizing call with
  | zero => exact measurable_fst
  | succ n ih =>
      have hq : Measurable (fun w : CombinedState p.E × (ℕ → p.Ω) => ((algorithm p).query w.1).2) :=
        (measurable_algorithm_query p).comp measurable_fst
      have hr := hg.comp (hq.prodMk ((measurable_pi_apply call).comp measurable_snd))
      have hu := (measurable_algorithm_update p).comp (measurable_fst.prodMk hr)
      exact (ih (call + 1)).comp (hu.prodMk measurable_snd)

lemma measurable_execute_output (p : Params) (P : ProbabilityMeasure (ℕ → p.Ω))
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g)) (K : ℕ) :
    Measurable (fun w : Unit × (ℕ → p.Ω) =>
      execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm p) (fun _ => K) w.1 w.2) := by
  have hi : Measurable (fun _ : Unit => ((algorithm p).initial () : CombinedState p.E)) := measurable_const
  have hh := (measurable_algorithm_output p).comp
    ((measurable_rawAdvance p hg K 0).comp ((hi.comp measurable_fst).prodMk measurable_snd))
  convert hh using 1
  funext w
  rcases w with ⟨⟨⟩, ξ⟩
  erw [StochasticGradient.execute_advance]
  rfl

lemma measurable_warmPoint (p : Params) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) : Measurable (warmPoint p g) := by
  have hh := (measurable_algorithm_output p).comp
    ((measurable_rawAdvance p hg (warmCost p) 0).comp
      ((measurable_const (a := ((algorithm p).initial () : CombinedState p.E))).prodMk measurable_id))
  convert hh using 1
  funext ξ
  exact warmPoint_eq_output p g ξ

end OracleTemplate.CoarseGeneralized
