import LongTails.Algorithms.SparseGroupSampling
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

namespace LongTails.Proofs.SparseGroupChoices

open LongTails.Algorithms.SparseGroupSampling

lemma fold_min_le_initial {α : Type*} (score : α → ℝ) (l : List α) (a : α) :
    score (l.foldl (fun best i => if score i < score best then i else best) a) ≤ score a := by
  classical
  induction l generalizing a with
  | nil => exact le_rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply (ih _).trans
    split_ifs with h
    · exact h.le
    · exact le_rfl

lemma fold_min_le_member {α : Type*} (score : α → ℝ) (l : List α) (a i : α)
    (hi : i ∈ l) :
    score (l.foldl (fun best j => if score j < score best then j else best) a) ≤ score i := by
  classical
  induction l generalizing a with
  | nil => simp at hi
  | cons j l ih =>
    simp only [List.mem_cons] at hi
    simp only [List.foldl_cons]
    rcases hi with rfl | hi
    · apply (fold_min_le_initial score l _).trans
      split_ifs with h
      · exact le_rfl
      · exact le_of_not_gt h
    · exact ih _ hi

lemma finiteMinimizer_le {α : Type*} [Fintype α] [Nonempty α]
    (score : α → ℝ) (i : α) : score (finiteMinimizer score) ≤ score i := by
  classical
  exact fold_min_le_member score _ _ i (by simp)

lemma le_finiteMaximizer {α : Type*} [Fintype α] [Nonempty α]
    (score : α → ℝ) (i : α) : score i ≤ score (finiteMaximizer score) := by
  have h := finiteMinimizer_le (fun i => -score i) i
  simpa only [finiteMaximizer, neg_le_neg_iff] using h

lemma measurable_selected_score {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α] (score : α → Ω → β)
    (hs : ∀ i, Measurable (score i)) {a : Ω → α} (ha : Measurable a) :
    Measurable (fun ω => score (a ω) ω) := by
  have h : Measurable (fun p : Ω × α => score p.2 p.1) :=
    measurable_from_prod_countable_left hs
  exact h.comp (measurable_id.prodMk ha)

lemma measurable_fold_min {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α] (score : α → Ω → ℝ)
    (hs : ∀ i, Measurable (score i)) (l : List α) {a : Ω → α} (ha : Measurable a) :
    Measurable (fun ω => l.foldl
      (fun best i => if score i ω < score best ω then i else best) (a ω)) := by
  classical
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih
    exact Measurable.ite (measurableSet_lt (hs i) (measurable_selected_score score hs ha))
      measurable_const ha

lemma measurable_finiteMinimizer {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Fintype α] [Nonempty α] [MeasurableSingletonClass α] (score : α → Ω → ℝ)
    (hs : ∀ i, Measurable (score i)) :
    Measurable (fun ω => finiteMinimizer (fun i => score i ω)) := by
  classical
  exact measurable_fold_min score hs Finset.univ.toList measurable_const

lemma measurable_finiteMaximizer {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Fintype α] [Nonempty α] [MeasurableSingletonClass α] (score : α → Ω → ℝ)
    (hs : ∀ i, Measurable (score i)) :
    Measurable (fun ω => finiteMaximizer (fun i => score i ω)) :=
  measurable_finiteMinimizer (fun i ω => -score i ω) (fun i => (hs i).neg)

open LongTails.Setups.OptimumGapGroupDro

instance (q : Public) : MeasurableSpace (Option (PrimalIndex q)) := ⊤

instance (q : Public) : MeasurableSingletonClass (Option (PrimalIndex q)) :=
  ⟨fun _ => trivial⟩

lemma measurable_upper (q : Public) (i : Fin q.K) (h : PrimalIndex q) :
    Measurable (fun s : State q => upper q s i h) := by
  have hn : Measurable (fun s : State q => s.1 i) := by fun_prop
  have ht : Measurable (fun s : State q => s.2.1 i h) := by fun_prop
  exact (ht.div ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn)).add
    ((measurable_of_countable (radius q)).comp hn)

lemma measurable_primalChoice (q : Public) : Measurable (primalChoice q) := by
  apply measurable_finiteMinimizer
  intro h
  apply measurable_selected_score (fun i s => upper q s i h)
    (fun i => measurable_upper q i h)
  exact measurable_finiteMaximizer _ (fun i => measurable_upper q i h)

lemma measurable_weighted_upper (q : Public) (w : Fin q.K → ℝ) (h : PrimalIndex q) :
    Measurable (fun s : State q => ∑ i, w i * upper q s i h) := by
  exact Finset.measurable_sum _ (fun i _ => (measurable_upper q i h).const_mul (w i))

lemma measurable_dualChoice (q : Public) : Measurable (dualChoice q) := by
  apply measurable_finiteMaximizer
  intro w
  apply measurable_selected_score (fun h s => ∑ i, w.val i * upper q s i h)
    (fun h => measurable_weighted_upper q w.val h)
  exact measurable_finiteMinimizer _ (fun h => measurable_weighted_upper q w.val h)

lemma measurable_uncertainty (q : Public) (i : Fin q.K) :
    Measurable (fun s : State q => uncertainty q s i) := by
  unfold uncertainty
  apply Measurable.mul
  · exact (measurable_pi_apply i).comp (measurable_subtype_coe.comp (measurable_dualChoice q))
  · exact (measurable_of_countable (radius q)).comp
      ((measurable_pi_apply i).comp measurable_fst)

lemma measurable_selectedGroup (q : Public) : Measurable (selectedGroup q) :=
  measurable_finiteMaximizer _ (measurable_uncertainty q)

lemma measurableSet_certified (q : Public) : MeasurableSet {s | certified q s} := by
  apply measurableSet_le _ measurable_const
  exact measurable_selected_score _ (measurable_uncertainty q) (measurable_selectedGroup q)

lemma measurable_output (q : Public) : Measurable (output q) := by
  have hm : Measurable (fun p : State q × Option (PrimalIndex q) =>
      match p.2 with
      | some h => h.val
      | none => (primalChoice q p.1).val) := by
    apply measurable_from_prod_countable_left
    intro o
    cases o with
    | none => exact measurable_subtype_coe.comp (measurable_primalChoice q)
    | some h => exact measurable_const
  exact hm.comp (measurable_id.prodMk (measurable_snd.comp measurable_snd))

lemma measurable_step (q : Public) (hloss : Measurable (Function.uncurry q.loss)) :
    Measurable (Function.uncurry (step q)) := by
  classical
  let next : Fin q.K → State q × q.Z → State q := fun i p =>
    (Function.update p.1.1 i (p.1.1 i + 1),
      Function.update p.1.2.1 i (fun h => p.1.2.1 i h + q.loss h.val p.2), none)
  have hn (i : Fin q.K) : Measurable (next i) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro j
      by_cases hij : j = i
      · subst j
        simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hij]
        fun_prop
    · apply Measurable.prodMk
      · apply Measurable.of_eval
        intro j
        by_cases hij : j = i
        · subst j
          simp only [Function.update_self]
          apply Measurable.of_eval
          intro h
          apply Measurable.add (by fun_prop)
          exact hloss.comp (measurable_const.prodMk measurable_snd)
        · simp only [Function.update_of_ne hij]
          fun_prop
      · exact measurable_const
  let finish : State q → State q := fun s =>
    if certified q s then (s.1, s.2.1, some (primalChoice q s)) else s
  have hf : Measurable finish := by
    apply Measurable.ite (measurableSet_certified q)
    · apply Measurable.prodMk measurable_fst
      apply Measurable.prodMk (measurable_fst.comp measurable_snd)
      exact (measurable_of_countable (fun h : PrimalIndex q => some h)).comp
        (measurable_primalChoice q)
    · exact measurable_id
  have hnext : Measurable (fun p : State q × q.Z => next (selectedGroup q p.1) p) :=
    measurable_selected_score next hn ((measurable_selectedGroup q).comp measurable_fst)
  have hcase : Measurable (fun p : (State q × q.Z) × Option (PrimalIndex q) =>
      match p.2 with
      | some _ => p.1.1
      | none => finish (next (selectedGroup q p.1.1) p.1)) := by
    apply measurable_from_prod_countable_left
    intro o
    cases o with
    | none => exact hf.comp hnext
    | some _ => exact measurable_fst
  exact hcase.comp (measurable_id.prodMk (by fun_prop))

end LongTails.Proofs.SparseGroupChoices
