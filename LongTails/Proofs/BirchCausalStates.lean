import LongTails.Proofs.BirchCausalCoefficients
import LongTails.Proofs.BirchCausalMerges

namespace LongTails.Proofs.BirchCausalStates

open Finset
open LongTails.Proofs.BirchCausalCoefficients
open LongTails.Proofs.BirchCausalMerges
open LongTails.Algorithms.BirchCausalPackets

noncomputable def causalState {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw : ℕ → E) (n : ℕ) : E :=
  initial + α • ∑ j : history n,
    (raw j.val - causalState history hpast α initial raw j.val)
termination_by n
decreasing_by exact mem_range.mp (hpast n j.property)

lemma causalState_rec {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw : ℕ → E) (n : ℕ) :
    causalState history hpast α initial raw n =
      initial + α • ∑ j ∈ history n, (raw j - causalState history hpast α initial raw j) := by
  rw [causalState]
  simp [sum_attach]

lemma causalState_unique {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw value : ℕ → E)
    (hrec : ∀ n, value n = initial + α • ∑ j ∈ history n, (raw j - value j)) :
    ∀ n, value n = causalState history hpast α initial raw n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [hrec, causalState_rec]
      congr 2
      apply sum_congr rfl
      intro j hj
      rw [ih j (mem_range.mp (hpast n hj))]

lemma causalState_map {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α : ℝ) (initial : E)
    (raw : ℕ → E) (map : E →ₗ[ℝ] F) (n : ℕ) :
    map (causalState history hpast α initial raw n) =
      causalState history hpast α (map initial) (fun q => map (raw q)) n := by
  refine causalState_unique history hpast α (map initial) (fun q => map (raw q))
    (fun k => map (causalState history hpast α initial raw k)) ?_ n
  intro k
  rw [causalState_rec, map_add, map_smul, map_sum]
  simp only [map_sub]

lemma causalState_initial (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α : ℝ) (n : ℕ) :
    causalState history hpast α (1 : ℝ) (fun _ => 0) n =
      initialCoefficient history hpast α n := by
  symm
  apply causalState_unique history hpast α 1 (fun _ => 0)
  intro k
  rw [initialCoefficient_rec]
  simp [sum_neg_distrib, sub_eq_add_neg]

lemma causalState_source (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α : ℝ) (q n : ℕ) :
    causalState history hpast α (0 : ℝ) (fun j => if j = q then 1 else 0) n =
      sourceCoefficient history hpast α q n := by
  symm
  apply causalState_unique history hpast α 0 (fun j => if j = q then 1 else 0)
  intro k
  rw [sourceCoefficient_rec, sum_sub_distrib]
  simp only [sum_ite_eq', smul_eq_mul, zero_add]
  split_ifs <;> ring

noncomputable def stateAggregate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw : ℕ → E) (s : Finset ℕ) : E :=
  initial + α • ∑ j ∈ s, (raw j - causalState history hpast α initial raw j)

lemma stateAggregate_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw : ℕ → E) (n : ℕ) :
    stateAggregate history hpast α initial raw (history n) =
      causalState history hpast α initial raw n := (causalState_rec _ _ _ _ _ _).symm

lemma stateAggregate_union {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw : ℕ → E) (s t : Finset ℕ) :
    stateAggregate history hpast α initial raw (s ∪ t) =
      stateAggregate history hpast α initial raw s +
        stateAggregate history hpast α initial raw t -
          stateAggregate history hpast α initial raw (s ∩ t) := by
  simpa only [stateAggregate, Finset.smul_sum] using
    aggregate_union s t initial (fun j => α • (raw j - causalState history hpast α initial raw j))

lemma stateAggregate_atom {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw : ℕ → E) (n : ℕ) :
    stateAggregate history hpast α initial raw (insert n (history n)) =
      α • raw n + (1 - α) • causalState history hpast α initial raw n := by
  have hn : n ∉ history n := by
    intro hn
    exact (Nat.lt_irrefl _) (mem_range.mp (hpast n hn))
  rw [stateAggregate, sum_insert hn, smul_add]
  rw [show initial + (α • (raw n - causalState history hpast α initial raw n) +
      α • ∑ j ∈ history n, (raw j - causalState history hpast α initial raw j)) =
      α • (raw n - causalState history hpast α initial raw n) +
        causalState history hpast α initial raw n by rw [causalState_rec]; module]
  module

lemma causalState_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α c : ℝ) (initial : E) (raw : ℕ → E) (n : ℕ) :
    causalState history hpast α (c • initial) (fun q => c • raw q) n =
      c • causalState history hpast α initial raw n := by
  symm
  refine causalState_unique history hpast α (c • initial) (fun q => c • raw q)
    (fun k => c • causalState history hpast α initial raw k) ?_ n
  intro k
  rw [causalState_rec, smul_add, smul_comm c α, smul_sum]
  simp only [smul_sub]

lemma causalState_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (n : ℕ) : causalState history hpast α (0 : E) (fun _ => 0) n = 0 := by
  symm
  refine causalState_unique history hpast α 0 (fun _ => 0) (fun _ => 0) ?_ n
  intro k
  simp

lemma causalState_congr {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw raw' : ℕ → E) (n : ℕ)
    (hraw : ∀ q, q < n → raw q = raw' q) :
    causalState history hpast α initial raw n = causalState history hpast α initial raw' n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [causalState_rec, causalState_rec]
      congr 2
      apply sum_congr rfl
      intro j hj
      have hjn := mem_range.mp (hpast n hj)
      rw [hraw j hjn, ih j hjn (fun q hq => hraw q (hq.trans hjn))]

lemma causalState_constant (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α c : ℝ) (n : ℕ) :
    causalState history hpast α c (fun _ => 0) n =
      c * initialCoefficient history hpast α n := by
  have h := causalState_smul history hpast α c (1 : ℝ) (fun _ => 0) n
  simpa [causalState_initial] using h

lemma innovation_update_outside {E : Type*} [AddCommGroup E]
    (s : Finset ℕ) (raw value : ℕ → E) (n : ℕ) (v : E) (hn : n ∉ s) :
    (∑ j ∈ s, (raw j - Function.update value n v j)) = ∑ j ∈ s, (raw j - value j) := by
  apply sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (show j ≠ n by intro he; subst j; exact hn hj)]

structure ModelInvariant {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : HistoryState) (values : GraphValues E) (point momentum : E)
    (α γ : ℝ) (raw direction : ℕ → E) : Prop where
  next : values.next = history.next
  atoms : values.atoms = history.atoms
  points : ∀ s, values.points s = point + γ • ∑ j ∈ history.states s, direction j
  momenta : ∀ s, values.momenta s = momentum +
    α • ∑ j ∈ history.states s, (raw j - values.queryMomenta j)
  queryPoints : ∀ j, j < history.atoms → values.queryPoints j =
    point + γ • ∑ i ∈ history.queryHistory j, direction i
  queries : ∀ j, j < history.atoms → values.queryMomenta j = momentum +
    α • ∑ i ∈ history.queryHistory j, (raw i - values.queryMomenta i)

lemma modelInvariant_initial {E : Type*} [AddCommGroup E] [Module ℝ E]
    (point momentum : E) (α γ : ℝ) (raw direction : ℕ → E) :
    ModelInvariant {} (initialValues point momentum) point momentum α γ raw direction := by
  constructor <;> simp [initialValues]

lemma modelInvariant_query {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : HistoryState) (values : GraphValues E) (point momentum : E)
    (α γ : ℝ) (raw direction : ℕ → E) (worker source : ℕ)
    (hh : HistoryInvariant history) (h : ModelInvariant history values point momentum α γ raw direction) :
    ModelInvariant (historyStep (.query worker source) history)
      (valueStep α γ raw direction (.query worker source) values) point momentum α γ raw direction := by
  have hn (s : ℕ) : history.atoms ∉ history.states s := by
    intro hj
    exact (Nat.lt_irrefl _) (mem_range.mp (hh.states_past s hj))
  have hs (s : ℕ) := innovation_update_outside (history.states s) raw values.queryMomenta
    history.atoms (values.momenta source) (hn s)
  constructor
  · simpa [historyStep, valueStep] using h.next
  · simpa [historyStep, valueStep] using h.atoms
  · intro s
    simp only [historyStep, valueStep, h.next, h.atoms]
    by_cases he : s = history.next
    · subst s
      rw [Function.update_self, Function.update_self, sum_insert (hn source), h.points source, smul_add]
      module
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      exact h.points s
  · intro s
    simp only [historyStep, valueStep, h.next, h.atoms]
    by_cases he : s = history.next
    · subst s
      rw [Function.update_self, Function.update_self, sum_insert (hn source), Function.update_self, hs source]
      rw [h.momenta source]
      module
    · rw [Function.update_of_ne he, Function.update_of_ne he, hs s]
      exact h.momenta s
  · intro j hj
    simp only [historyStep] at hj
    simp only [historyStep, valueStep, h.next, h.atoms]
    by_cases he : j = history.atoms
    · subst j
      rw [Function.update_self, Function.update_self]
      exact h.points source
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      exact h.queryPoints j (by omega)
  · intro j hj
    simp only [historyStep] at hj
    simp only [historyStep, valueStep, h.next, h.atoms]
    by_cases he : j = history.atoms
    · subst j
      rw [Function.update_self, Function.update_self, hs source]
      exact h.momenta source
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      have hj0 : j < history.atoms := by omega
      have hnq : history.atoms ∉ history.queryHistory j := by
        intro hi
        have := mem_range.mp (hh.query_past j hj0 hi)
        omega
      rw [innovation_update_outside _ _ _ _ _ hnq]
      exact h.queries j hj0

lemma modelInvariant_merge {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : HistoryState) (values : GraphValues E) (point momentum : E)
    (α γ : ℝ) (raw direction : ℕ → E) (worker left right common : ℕ)
    (hcommon : history.states common = history.states left ∩ history.states right)
    (h : ModelInvariant history values point momentum α γ raw direction) :
    ModelInvariant (historyStep (.merge worker left right common) history)
      (valueStep α γ raw direction (.merge worker left right common) values)
        point momentum α γ raw direction := by
  constructor
  · simpa [historyStep, valueStep] using h.next
  · exact h.atoms
  · intro s
    simp only [historyStep, valueStep, h.next]
    by_cases he : s = history.next
    · subst s
      rw [Function.update_self, Function.update_self, h.points left, h.points right, h.points common, hcommon]
      simpa only [smul_sum] using (aggregate_union (history.states left) (history.states right)
        point (fun j => γ • direction j)).symm
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      exact h.points s
  · intro s
    simp only [historyStep, valueStep, h.next]
    by_cases he : s = history.next
    · subst s
      rw [Function.update_self, Function.update_self, h.momenta left, h.momenta right, h.momenta common, hcommon]
      simpa only [smul_sum] using (aggregate_union (history.states left) (history.states right)
        momentum (fun j => α • (raw j - values.queryMomenta j))).symm
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      exact h.momenta s
  · exact h.queryPoints
  · exact h.queries

lemma modelInvariant_fold {E : Type*} [AddCommGroup E] [Module ℝ E]
    (workers : ℕ) (nodes : List GraphNode) (history : HistoryState) (values : GraphValues E)
    (point momentum : E) (α γ : ℝ) (raw direction : ℕ → E)
    (hvalid : GraphValidFrom workers history nodes) (hh : HistoryInvariant history)
    (h : ModelInvariant history values point momentum α γ raw direction) :
    ModelInvariant (nodes.foldl (flip historyStep) history)
      (nodes.foldl (flip (valueStep α γ raw direction)) values) point momentum α γ raw direction := by
  induction nodes generalizing history values with
  | nil => exact h
  | cons node rest ih =>
      apply ih _ _ hvalid.2 (historyInvariant_step history node hh)
      cases node with
      | query worker source => exact modelInvariant_query history values point momentum α γ raw direction worker source hh h
      | merge worker left right common =>
          exact modelInvariant_merge history values point momentum α γ raw direction worker left right common
            hvalid.1.2.2.2.2 h

lemma causalState_unique_below {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (α : ℝ) (initial : E) (raw value : ℕ → E) (N : ℕ)
    (hrec : ∀ n, n < N → value n = initial + α • ∑ j ∈ history n, (raw j - value j)) :
    ∀ n, n < N → value n = causalState history hpast α initial raw n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rw [hrec n hn, causalState_rec]
      congr 2
      apply sum_congr rfl
      intro j hj
      have hjn := mem_range.mp (hpast n hj)
      rw [ih j hjn (hjn.trans hn)]

def completeHistory (history : HistoryState) (n : ℕ) : Finset ℕ :=
  if n < history.atoms then history.queryHistory n else range n

lemma completeHistory_past (history : HistoryState) (h : HistoryInvariant history) :
    ∀ n, completeHistory history n ⊆ range n := by
  intro n
  unfold completeHistory
  split_ifs with hn
  · exact h.query_past n hn
  · exact Subset.rfl

lemma completeHistory_closed (history : HistoryState) (h : HistoryInvariant history) :
    ∀ n j, j ∈ completeHistory history n →
      completeHistory history j ⊆ completeHistory history n := by
  intro n j hj
  by_cases hn : n < history.atoms
  · have he : completeHistory history n = history.queryHistory n := by simp [completeHistory, hn]
    rw [he] at hj ⊢
    have hjn := mem_range.mp (h.query_past n hn hj)
    simpa [completeHistory, hjn.trans hn] using h.query_closed n hn j hj
  · have he : completeHistory history n = range n := by simp [completeHistory, hn]
    rw [he] at hj ⊢
    exact (completeHistory_past history h j).trans (range_mono (mem_range.mp hj).le)

lemma model_query_coefficients {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : HistoryState) (values : GraphValues E) (point momentum : E)
    (α γ : ℝ) (raw direction : ℕ → E)
    (hh : HistoryInvariant history) (h : ModelInvariant history values point momentum α γ raw direction)
    (n : ℕ) (hn : n < history.atoms) :
    values.queryMomenta n = causalState (completeHistory history)
      (completeHistory_past history hh) α momentum raw n := by
  apply causalState_unique_below (completeHistory history) (completeHistory_past history hh)
    α momentum raw values.queryMomenta history.atoms _ n hn
  intro j hj
  simpa [completeHistory, hj] using h.queries j hj

lemma model_state_coefficients {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : HistoryState) (values : GraphValues E) (point momentum : E)
    (α γ : ℝ) (raw direction : ℕ → E)
    (hh : HistoryInvariant history) (h : ModelInvariant history values point momentum α γ raw direction)
    (s : ℕ) :
    values.momenta s = stateAggregate (completeHistory history)
      (completeHistory_past history hh) α momentum raw (history.states s) := by
  rw [h.momenta s, stateAggregate]
  congr 2
  apply sum_congr rfl
  intro j hj
  rw [model_query_coefficients history values point momentum α γ raw direction hh h j
    (mem_range.mp (hh.states_past s hj))]

end LongTails.Proofs.BirchCausalStates
