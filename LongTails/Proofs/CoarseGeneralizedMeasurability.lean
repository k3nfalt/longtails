import LongTails.Proofs.RobustGeneralizedOutput
import LongTails.Algorithms.CoarseGeneralizedAccelerated

open MeasureTheory

namespace OracleTemplate.CoarseGeneralized

variable {E : Type*} [MeasurableSpace E]

instance measurableSpaceIterate : MeasurableSpace (Iterate E) :=
  MeasurableSpace.comap (fun s => (s.x, s.v, s.A, s.index)) inferInstance

@[fun_prop] lemma measurable_iterate_x : Measurable (fun s : Iterate E => s.x) :=
  measurable_fst.comp (comap_measurable _)

@[fun_prop] lemma measurable_iterate_v : Measurable (fun s : Iterate E => s.v) :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable _))

@[fun_prop] lemma measurable_iterate_A : Measurable (fun s : Iterate E => s.A) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _)))

@[fun_prop] lemma measurable_iterate_index : Measurable (fun s : Iterate E => s.index) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _)))

@[fun_prop] lemma measurable_iterate_mk {α : Type*} [MeasurableSpace α]
    {x v : α → E} {A : α → ℝ} {i : α → ℕ}
    (hx : Measurable x) (hv : Measurable v) (hA : Measurable A) (hi : Measurable i) :
    Measurable (fun a => (⟨x a, v a, A a, i a⟩ : Iterate E)) := by
  apply measurable_comap_iff.mpr
  exact hx.prodMk (hv.prodMk (hA.prodMk hi))

abbrev SearchCode (E : Type*) :=
  Iterate E ⊕ (Iterate E ⊕ ((Iterate E × ℝ × ℝ × E × ℕ) ⊕ E))

def searchCode : Search E → SearchCode E
  | .left s => .inl s
  | .right s => .inr (.inl s)
  | .bracket s lo hi upper r => .inr (.inr (.inl (s, lo, hi, upper, r)))
  | .done x => .inr (.inr (.inr x))

def codeSearch : SearchCode E → Search E
  | .inl s => .left s
  | .inr (.inl s) => .right s
  | .inr (.inr (.inl (s, lo, hi, upper, r))) => .bracket s lo hi upper r
  | .inr (.inr (.inr x)) => .done x

instance measurableSpaceSearch : MeasurableSpace (Search E) :=
  MeasurableSpace.comap searchCode inferInstance

lemma measurable_searchCode : Measurable (@searchCode E) := comap_measurable _

lemma measurable_search_uncurry {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {F : Search E → α → β}
    (hl : Measurable (fun w : Iterate E × α => F (.left w.1) w.2))
    (hr : Measurable (fun w : Iterate E × α => F (.right w.1) w.2))
    (hb : Measurable (fun w : (Iterate E × ℝ × ℝ × E × ℕ) × α =>
      F (.bracket w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1 w.1.2.2.2.2) w.2))
    (hd : Measurable (fun w : E × α => F (.done w.1) w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : SearchCode E × α => F (codeSearch w.1) w.2) := by
    apply (MeasurableEquiv.sumProdDistrib (Iterate E)
      (Iterate E ⊕ ((Iterate E × ℝ × ℝ × E × ℕ) ⊕ E)) α).symm.measurable_comp_iff.mp
    apply measurable_fun_sum hl
    apply (MeasurableEquiv.sumProdDistrib (Iterate E)
      ((Iterate E × ℝ × ℝ × E × ℕ) ⊕ E) α).symm.measurable_comp_iff.mp
    apply measurable_fun_sum hr
    apply (MeasurableEquiv.sumProdDistrib (Iterate E × ℝ × ℝ × E × ℕ) E α).symm.measurable_comp_iff.mp
    exact measurable_fun_sum hb hd
  have hh := hm.comp ((measurable_searchCode.comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  rcases w with ⟨s, a⟩
  cases s <;> rfl

@[fun_prop] lemma measurable_search_left {α : Type*} [MeasurableSpace α]
    {s : α → Iterate E} (hs : Measurable s) : Measurable (fun a => Search.left (s a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl.comp hs

@[fun_prop] lemma measurable_search_right {α : Type*} [MeasurableSpace α]
    {s : α → Iterate E} (hs : Measurable s) : Measurable (fun a => Search.right (s a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inl.comp hs)

@[fun_prop] lemma measurable_search_bracket {α : Type*} [MeasurableSpace α]
    {s : α → Iterate E} {lo hi : α → ℝ} {upper : α → E} {r : α → ℕ}
    (hs : Measurable s) (hlo : Measurable lo) (hhi : Measurable hi)
    (hu : Measurable upper) (hr : Measurable r) :
    Measurable (fun a => Search.bracket (s a) (lo a) (hi a) (upper a) (r a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inr.comp
    (measurable_inl.comp (hs.prodMk (hlo.prodMk (hhi.prodMk (hu.prodMk hr))))))

@[fun_prop] lemma measurable_search_done {α : Type*} [MeasurableSpace α]
    {x : α → E} (hx : Measurable x) : Measurable (fun a => Search.done (x a)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inr.comp (measurable_inr.comp hx))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_decrement (t : Tuning) : Measurable (decrement (E := E) t) := by
  unfold decrement
  fun_prop

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_surplus (t : Tuning) : Measurable (surplus (E := E) t) := by
  unfold surplus
  fun_prop

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_weight (t : Tuning) :
    Measurable (fun w : ℝ × E => weight t w.1 w.2) := by
  unfold weight
  fun_prop

@[fun_prop] lemma measurable_advance (t : Tuning) :
    Measurable (fun w : Iterate E × E × E => advance t w.1 w.2.1 w.2.2) := by
  unfold advance
  dsimp only
  apply measurable_iterate_mk <;> fun_prop

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_resume (t : Tuning) : Measurable (resume (E := E) t) := by
  unfold resume
  apply Measurable.ite (measurableSet_le measurable_const measurable_iterate_index)
  · fun_prop
  · fun_prop

@[fun_prop] lemma measurable_finish (t : Tuning) :
    Measurable (fun w : Iterate E × E × E => finish t w.1 w.2.1 w.2.2) := by
  unfold finish
  fun_prop

@[fun_prop] lemma measurable_searchPoint : Measurable (searchPoint (E := E)) := by
  have hh : Measurable (fun w : Search E × Unit => searchPoint w.1) := by
    apply measurable_search_uncurry (F := fun (s : Search E) (_ : Unit) => searchPoint s)
    all_goals dsimp [searchPoint]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_warmOutput : Measurable (warmOutput (E := E)) := by
  have hh : Measurable (fun w : Search E × Unit => warmOutput w.1) := by
    apply measurable_search_uncurry (F := fun (s : Search E) (_ : Unit) => warmOutput s)
    all_goals dsimp [warmOutput]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

@[fun_prop] lemma measurable_assess (t : Tuning) :
    Measurable (fun w : Iterate E × E × E × Search E => assess t w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  unfold assess
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
  · fun_prop
  · apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
    · fun_prop
    · fun_prop

@[fun_prop] lemma measurable_assess_map (t : Tuning) {α : Type*} [MeasurableSpace α]
    {s : α → Iterate E} {y h : α → E} {next : α → Search E}
    (hs : Measurable s) (hy : Measurable y) (hh : Measurable h) (hn : Measurable next) :
    Measurable (fun a => assess t (s a) (y a) (h a) (next a)) :=
  (measurable_assess t).comp (hs.prodMk (hy.prodMk (hh.prodMk hn)))

@[fun_prop] lemma measurable_searchUpdate (t : Tuning) :
    Measurable (Function.uncurry (searchUpdate (E := E) t)) := by
  apply measurable_search_uncurry
  · dsimp [searchUpdate]
    apply measurable_assess_map t (by fun_prop) (by fun_prop) (by fun_prop)
    apply Measurable.ite (measurableSet_le measurable_const (by fun_prop)) <;> fun_prop
  · dsimp [searchUpdate]
    apply measurable_assess_map t (by fun_prop) (by fun_prop) (by fun_prop)
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    · fun_prop
    · split_ifs <;> fun_prop
  · dsimp [searchUpdate]
    apply measurable_assess_map t (by fun_prop) (by fun_prop) (by fun_prop)
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) <;> fun_prop
    · apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) <;> fun_prop
  · dsimp [searchUpdate]
    fun_prop

end OracleTemplate.CoarseGeneralized
