import LongTails.Proofs.AdaptiveRobustGeneralizedExecution
import LongTails.Proofs.AdaptiveRobustGeneralizedMeasurability
import LongTails.Proofs.StochasticGeneralizedMeasurability

open MeasureTheory

namespace OracleTemplate.AdaptiveRobustGeneralized

open GeneralizedAccelerated (Iterate Pending coupling)
open StochasticGeneralized (measurable_iterate_A)

abbrev StateCode (E : Type*) :=
  (Iterate E × ℕ × (ℕ → E)) ⊕ ((Pending E × ℕ × (ℕ → E)) ⊕ Iterate E)

def stateCode {E : Type*} : State E → StateCode E
  | .first s n total => .inl (s, n, total)
  | .second s n total => .inr (.inl (s, n, total))
  | .done s => .inr (.inr s)

def codeState {E : Type*} : StateCode E → State E
  | .inl (s, n, total) => .first s n total
  | .inr (.inl (s, n, total)) => .second s n total
  | .inr (.inr s) => .done s

instance measurableSpaceState {E : Type*} [MeasurableSpace E] : MeasurableSpace (State E) :=
  MeasurableSpace.comap stateCode inferInstance

instance measurableSpaceAlgorithmState (p : Params) : MeasurableSpace (algorithm p).State :=
  inferInstanceAs (MeasurableSpace (State p.E))

lemma measurable_stateCode {E : Type*} [MeasurableSpace E] : Measurable (@stateCode E) :=
  comap_measurable _

lemma measurable_state_uncurry {E α β : Type*} [MeasurableSpace E] [MeasurableSpace α] [MeasurableSpace β]
    {F : State E → α → β}
    (hfirst : Measurable (fun w : (Iterate E × ℕ × (ℕ → E)) × α =>
      F (.first w.1.1 w.1.2.1 w.1.2.2) w.2))
    (hsecond : Measurable (fun w : (Pending E × ℕ × (ℕ → E)) × α =>
      F (.second w.1.1 w.1.2.1 w.1.2.2) w.2))
    (hdone : Measurable (fun w : Iterate E × α => F (.done w.1) w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : StateCode E × α => F (codeState w.1) w.2) := by
    apply (MeasurableEquiv.sumProdDistrib (Iterate E × ℕ × (ℕ → E))
      ((Pending E × ℕ × (ℕ → E)) ⊕ Iterate E) α).symm.measurable_comp_iff.mp
    apply measurable_fun_sum
    · exact hfirst
    · apply (MeasurableEquiv.sumProdDistrib (Pending E × ℕ × (ℕ → E)) (Iterate E) α).symm.measurable_comp_iff.mp
      exact measurable_fun_sum hsecond hdone
  have hh := hm.comp ((measurable_stateCode.comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  rcases w with ⟨s, a⟩
  cases s <;> rfl

@[fun_prop] lemma measurable_state_first {E α : Type*} [MeasurableSpace E] [MeasurableSpace α]
    {s : α → Iterate E} {n : α → ℕ} {total : α → (ℕ → E)}
    (hs : Measurable s) (hn : Measurable n) (ht : Measurable total) :
    Measurable (fun a => State.first (s a) (n a) (total a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl.comp (hs.prodMk (hn.prodMk ht))

@[fun_prop] lemma measurable_state_second {E α : Type*} [MeasurableSpace E] [MeasurableSpace α]
    {s : α → Pending E} {n : α → ℕ} {total : α → (ℕ → E)}
    (hs : Measurable s) (hn : Measurable n) (ht : Measurable total) :
    Measurable (fun a => State.second (s a) (n a) (total a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inl.comp (hs.prodMk (hn.prodMk ht)))

@[fun_prop] lemma measurable_state_done {E α : Type*} [MeasurableSpace E] [MeasurableSpace α]
    {s : α → Iterate E} (hs : Measurable s) : Measurable (fun a => State.done (s a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inr.comp hs)

@[fun_prop] lemma measurable_resume (p : Params) : Measurable (resume p) := by
  unfold resume
  apply Measurable.ite (measurableSet_le measurable_const measurable_iterate_A)
  · fun_prop
  · fun_prop

lemma measurable_algorithm_query (p : Params) :
    Measurable (fun s => ((algorithm p).query s).2) := by
  have hh : Measurable (fun w : State p.E × Unit => ((algorithm p).query w.1).2) := by
    apply measurable_state_uncurry (F := fun (s : State p.E) (_ : Unit) => ((algorithm p).query s).2)
    all_goals dsimp [algorithm]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_algorithm_output (p : Params) : Measurable (algorithm p).output := by
  have hh : Measurable (fun w : State p.E × Unit => (algorithm p).output w.1) := by
    apply measurable_state_uncurry (F := fun (s : State p.E) (_ : Unit) => (algorithm p).output s)
    all_goals dsimp [algorithm]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))


@[fun_prop] lemma measurable_reply_update {E α : Type*} [MeasurableSpace E] [MeasurableSpace α]
    {v : α → ℕ → E} {n : α → ℕ} {r : α → E}
    (hv : Measurable v) (hn : Measurable n) (hr : Measurable r) :
    Measurable (fun a => Function.update (v a) (n a) (r a)) := by
  apply Measurable.of_eval
  intro i
  have he : (fun a => Function.update (v a) (n a) (r a) i) =
      fun a => if i = n a then r a else v a i := by
    ext a
    by_cases h : i = n a
    · simp [h]
    · simp [h]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun measurable_const hn) hr ((measurable_pi_apply i).comp hv)

lemma measurable_algorithm_update (p : Params) : Measurable (Function.uncurry (algorithm p).update) := by
  have hcost := measurable_estimatorCost p
  have hest := measurable_estimate p
  apply measurable_state_uncurry
  · dsimp [algorithm]
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
    · fun_prop
    · fun_prop
  · dsimp [algorithm]
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
    · fun_prop
    · fun_prop
  · dsimp [algorithm]
    fun_prop

lemma measurable_rawAdvance (p : Params) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) (n call : ℕ) :
    Measurable (fun w : State p.E × (ℕ → p.Ω) => rawAdvance p g w.2 n call w.1) := by
  induction n generalizing call with
  | zero => exact measurable_fst
  | succ n ih =>
    have hquery : Measurable (fun w : State p.E × (ℕ → p.Ω) => ((algorithm p).query w.1).2) :=
      (measurable_algorithm_query p).comp measurable_fst
    have hreply := hg.comp (hquery.prodMk ((measurable_pi_apply call).comp measurable_snd))
    have hupdate := (measurable_algorithm_update p).comp (measurable_fst.prodMk hreply)
    exact (ih (call+1)).comp (hupdate.prodMk measurable_snd)

lemma measurable_execute_output (p : Params) (P : ProbabilityMeasure (ℕ → p.Ω))
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g)) (K : ℕ) :
    Measurable (fun w : (algorithm p).Seed × (ℕ → p.Ω) =>
      (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm p) (fun _ => K) w.1 w.2)) := by
  have hi : Measurable (algorithm p).initial := measurable_const
  have hh := (measurable_algorithm_output p).comp
    ((measurable_rawAdvance p hg K 0).comp ((hi.comp measurable_fst).prodMk measurable_snd))
  convert hh using 1
  funext w
  rw [StochasticGradient.execute_advance]
  rfl

end OracleTemplate.AdaptiveRobustGeneralized
