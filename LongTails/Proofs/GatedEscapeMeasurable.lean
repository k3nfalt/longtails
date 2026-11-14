import LongTails.Proofs.GatedEscapePhases
import LongTails.Proofs.GatedEscapeMoments

namespace LongTails.Proofs.GatedEscapeMeasurable

open MeasureTheory LongTails.Algorithms.GatedPerturbedEscape LongTails.Proofs.GatedEscapeProcess
  LongTails.Proofs.GatedEscapeMoments
open scoped RealInnerProductSpace

instance : MeasurableSpace Phase := ⊤

instance : MeasurableSingletonClass Phase := ⟨fun _ => trivial⟩

instance : DiscreteMeasurableSpace Phase := ⟨fun _ => trivial⟩

def phaseCode : Phase → ℕ
  | .test => 0
  | .grad0 => 1
  | .init => 2
  | .traj => 3
  | .ray => 4

instance : Countable Phase := by
  refine ⟨⟨phaseCode, fun a b h => ?_⟩⟩
  cases a <;> cases b <;> simp_all [phaseCode]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

abbrev Enc (E : Type) :=
  ℕ × E × ℕ × Phase × ℕ × E × (ℕ → E) × E × E × E × ℕ × Bool × E × Bool × (ℕ → E)

def enc (s : State E) : Enc E :=
  (s.i, s.acc, s.t, s.ph, s.j, s.x, s.store, s.g0, s.v, s.w, s.att, s.found, s.dx, s.done, s.zs)

noncomputable instance : MeasurableSpace (State E) := MeasurableSpace.comap enc inferInstance

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_enc : Measurable (enc : State E → Enc E) := comap_measurable enc

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_to_state {α : Type*} [MeasurableSpace α] (f : α → State E)
    (h : Measurable (enc ∘ f)) : Measurable f := by
  rw [measurable_iff_comap_le]
  change (MeasurableSpace.comap enc inferInstance).comap f ≤ _
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 h

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_i : Measurable (fun s : State E => s.i) :=
  measurable_enc.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_acc : Measurable (fun s : State E => s.acc) :=
  measurable_enc.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_t : Measurable (fun s : State E => s.t) :=
  measurable_enc.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_ph : Measurable (fun s : State E => s.ph) :=
  measurable_enc.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_j : Measurable (fun s : State E => s.j) :=
  measurable_enc.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_x : Measurable (fun s : State E => s.x) :=
  measurable_enc.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_store : Measurable (fun s : State E => s.store) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_g0 : Measurable (fun s : State E => s.g0) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_v : Measurable (fun s : State E => s.v) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_w : Measurable (fun s : State E => s.w) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_att : Measurable (fun s : State E => s.att) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_found : Measurable (fun s : State E => s.found) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_dx : Measurable (fun s : State E => s.dx) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_done : Measurable (fun s : State E => s.done) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[fun_prop]
lemma measurable_zs : Measurable (fun s : State E => s.zs) :=
  measurable_enc.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_mk {α : Type*} [MeasurableSpace α]
    {f0 : α → ℕ} {f1 : α → E} {f2 : α → ℕ} {f3 : α → Phase} {f4 : α → ℕ} {f5 : α → E}
    {f6 : α → (ℕ → E)} {f7 : α → E} {f8 : α → E} {f9 : α → E} {f10 : α → ℕ} {f11 : α → Bool}
    {f12 : α → E} {f13 : α → Bool} {f14 : α → (ℕ → E)}
    (h0 : Measurable f0) (h1 : Measurable f1) (h2 : Measurable f2) (h3 : Measurable f3)
    (h4 : Measurable f4) (h5 : Measurable f5) (h6 : Measurable f6) (h7 : Measurable f7)
    (h8 : Measurable f8) (h9 : Measurable f9) (h10 : Measurable f10) (h11 : Measurable f11)
    (h12 : Measurable f12) (h13 : Measurable f13) (h14 : Measurable f14) :
    Measurable (fun a =>
      State.mk (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) (f9 a) (f10 a)
      (f11 a) (f12 a) (f13 a) (f14 a) : α → State E) := by
  refine measurable_to_state _ ?_
  exact h0.prodMk (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk (h6.prodMk (h7.prodMk
    (h8.prodMk (h9.prodMk (h10.prodMk (h11.prodMk (h12.prodMk (h13.prodMk (h14))))))))))))))

section ops

variable {α : Type*} [MeasurableSpace α]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_phase_split {β : Type*} [MeasurableSpace β] (F : State E → β)
    (h : ∀ c : Phase, Measurable (fun s : State E => F { s with ph := c })) : Measurable F := by
  have h2 : Measurable (fun q : Phase × State E => F { q.2 with ph := q.1 }) :=
    measurable_from_prod_countable_right (fun c => h c)
  exact h2.comp (measurable_ph.prodMk measurable_id)

lemma measurable_eval_nat {β : Type*} [MeasurableSpace β] {F : α → ℕ → β} {I : α → ℕ}
    (hF : Measurable F) (hI : Measurable I) : Measurable (fun a => F a (I a)) := by
  have h2 : Measurable (fun q : (ℕ → β) × ℕ => q.1 q.2) :=
    measurable_from_prod_countable_left (fun n => by exact measurable_pi_apply n)
  exact h2.comp (hF.prodMk hI)

@[fun_prop]
lemma measurable_update_nat {β : Type*} [MeasurableSpace β] {F : α → ℕ → β} {I : α → ℕ} {V : α → β}
    (hF : Measurable F) (hI : Measurable I) (hV : Measurable V) :
    Measurable (fun a => Function.update (F a) (I a) (V a)) := by
  refine measurable_pi_iff.mpr fun n => ?_
  have : (fun a => Function.update (F a) (I a) (V a) n) = fun a => if n = I a then V a else F a n := by
    funext a; by_cases h : n = I a
    · subst h; simp
    · rw [Function.update_of_ne h]; simp [h]
  rw [this]
  exact Measurable.ite (measurableSet_eq_fun measurable_const hI) hV
    ((measurable_pi_apply n).comp hF)

lemma measurable_votes {β : Type} [NormedAddCommGroup β] [MeasurableSpace β] [BorelSpace β]
    [SecondCountableTopology β] (M : ℕ) (τ : ℝ) (a : ℕ) :
    Measurable (fun s : ℕ → β => votes M τ s a) := by
  unfold votes
  simp_rw [Finset.card_filter]
  refine Finset.measurable_sum _ (fun c _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le ((measurable_pi_apply a).sub (measurable_pi_apply c)).norm measurable_const

@[fun_prop]
lemma measurable_select {β : Type} [NormedAddCommGroup β] [MeasurableSpace β] [BorelSpace β]
    [SecondCountableTopology β] (M : ℕ) (τ : ℝ) : Measurable (fun s : ℕ → β => select M τ s) := by
  have hp : Measurable (fun s : ℕ → β => pick M τ s) := by
    unfold pick
    refine measurable_find _ (fun k => ?_)
    rw [Set.ofPred_or, Set.ofPred_and]
    refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) ?_
    · exact MeasurableSet.const _
    · exact measurableSet_lt measurable_const ((measurable_votes M τ k).const_mul 2)
    · exact MeasurableSet.const _
  exact measurable_eval_nat measurable_id hp

@[fun_prop]
lemma measurable_clip (r : ℝ) : Measurable (fun u : E => clip r u) := by
  unfold clip
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    ((measurable_const.div measurable_norm).smul measurable_id)

end ops

section machine

variable {Ω : Type} [MeasurableSpace Ω] (cfg : Config) (d : ℕ) (g : E → Ω → E)
variable {α : Type*} [MeasurableSpace α]

lemma measurable_queryPoint : Measurable (fun s : State E => queryPoint cfg s) := by
  refine measurable_phase_split _ (fun c => ?_)
  cases c <;> simp only [queryPoint] <;> fun_prop

lemma measurable_blockUpdate {S : α → State E} {G Z : α → E} (hS : Measurable S) (hG : Measurable G)
    (hZ : Measurable Z) : Measurable (fun a => blockUpdate cfg d (S a) (G a) (Z a)) := by
  have key : ∀ c : Phase, Measurable (fun a => blockUpdate cfg d { S a with ph := c } (G a) (Z a)) := by
    intro c
    cases c <;> unfold blockUpdate endAttempt <;> dsimp only <;>
      repeat' (first
      | (apply Measurable.ite)
      | (apply measurable_mk)
      | (rw [Set.ofPred_and])
      | (apply MeasurableSet.inter)
      | exact measurableSet_lt (by fun_prop) (by fun_prop)
      | exact measurableSet_le (by fun_prop) (by fun_prop)
      | exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
      | fun_prop
      | (apply Measurable.add)
      | (apply Measurable.neg)
      | (apply Measurable.smul)
      | (apply Measurable.mul))
  have h2 : Measurable (fun q : Phase × α => blockUpdate cfg d { S q.2 with ph := q.1 } (G q.2) (Z q.2)) :=
    measurable_from_prod_countable_right (fun c => key c)
  exact h2.comp ((measurable_ph.comp hS).prodMk measurable_id)

lemma measurable_stepBlock {S : α → State E} {G Z : α → E} (hS : Measurable S) (hG : Measurable G)
    (hZ : Measurable Z) : Measurable (fun a => stepBlock cfg d (S a) (G a) (Z a)) := by
  have hB := measurable_blockUpdate cfg d hS hG hZ
  simp only [stepBlock]
  refine measurable_mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> fun_prop

lemma measurable_astep (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (astep cfg d g)) := by
  have hG : Measurable (fun p : State E × ((Fin cfg.b → Ω) × E) => bmean cfg g (queryPoint cfg p.1) p.2.1) :=
    (bmean_measurable_joint cfg hg (q := fun s : State E => queryPoint cfg s) (measurable_queryPoint cfg)).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hst := measurable_stepBlock cfg d (S := fun p : State E × ((Fin cfg.b → Ω) × E) => p.1)
    measurable_fst hG (measurable_snd.comp measurable_snd)
  have : Function.uncurry (astep cfg d g) = fun p : State E × ((Fin cfg.b → Ω) × E) =>
      if p.1.done = true then p.1
      else stepBlock cfg d p.1 (bmean cfg g (queryPoint cfg p.1) p.2.1) p.2.2 := by
    funext p; rfl
  rw [this]
  exact Measurable.ite (measurableSet_eq_fun (measurable_done.comp measurable_fst) measurable_const)
    measurable_fst hst

end machine

end LongTails.Proofs.GatedEscapeMeasurable
