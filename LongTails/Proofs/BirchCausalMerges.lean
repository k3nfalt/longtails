import LongTails.Algorithms.BirchCausalPackets
import LongTails.Proofs.BirchNonEuclideanFamilies

namespace LongTails.Proofs.BirchCausalMerges

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchNonEuclideanFamilies

lemma aggregate_union {ι G : Type*} [DecidableEq ι] [AddCommGroup G]
    (s t : Finset ι) (base : G) (delta : ι → G) :
    base + ∑ j ∈ s ∪ t, delta j =
      (base + ∑ j ∈ s, delta j) + (base + ∑ j ∈ t, delta j) -
        (base + ∑ j ∈ s ∩ t, delta j) := by
  have h : (∑ j ∈ s ∪ t, delta j) + (∑ j ∈ s ∩ t, delta j) =
      (∑ j ∈ s, delta j) + ∑ j ∈ t, delta j := sum_union_inter
  have he := eq_sub_of_add_eq h
  rw [he]
  abel

lemma closed_union (history : ℕ → Finset ℕ) (s t : Finset ℕ)
    (hs : ∀ j ∈ s, history j ⊆ s) (ht : ∀ j ∈ t, history j ⊆ t) :
    ∀ j ∈ s ∪ t, history j ⊆ s ∪ t := by
  intro j hj
  rcases mem_union.mp hj with hj | hj
  · exact (hs j hj).trans subset_union_left
  · exact (ht j hj).trans subset_union_right

lemma closed_inter (history : ℕ → Finset ℕ) (s t : Finset ℕ)
    (hs : ∀ j ∈ s, history j ⊆ s) (ht : ∀ j ∈ t, history j ⊆ t) :
    ∀ j ∈ s ∩ t, history j ⊆ s ∩ t := by
  intro j hj q hq
  exact mem_inter.mpr ⟨hs j (mem_inter.mp hj).1 hq, ht j (mem_inter.mp hj).2 hq⟩

lemma closed_insert (history : ℕ → Finset ℕ) (s : Finset ℕ) (n : ℕ)
    (hs : ∀ j ∈ s, history j ⊆ s) (hn : history n ⊆ s) :
    ∀ j ∈ insert n s, history j ⊆ insert n s := by
  intro j hj
  rcases mem_insert.mp hj with rfl | hj
  · exact hn.trans (subset_insert _ _)
  · exact (hs j hj).trans (subset_insert _ _)

lemma packet_recent_prefix (history : ℕ → Finset ℕ) (dispatch : ℕ → ℕ) (H R : ℕ)
    (hH : 0 < H) (hdelay : ∀ k, k - dispatch k ≤ R)
    (hroot : ∀ n, range (dispatch (n / H) * H) ⊆ history n) :
    ∀ n, range (n - H * (R + 1)) ⊆ history n := by
  intro n
  apply (range_mono ?_).trans (hroot n)
  have hd := hdelay (n / H)
  have hq : n / H ≤ dispatch (n / H) + R := by omega
  have hm := Nat.mul_le_mul_right H hq
  have hn : n < n / H * H + H := by
    have hr := Nat.mod_lt n hH
    have he := Nat.mod_add_div n H
    rw [Nat.mul_comm H (n / H)] at he
    omega
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at hm ⊢
  rw [Nat.mul_comm R H] at hm
  omega

lemma atom_calls (H round index worker x m : ℕ) (s : CodeState) :
    codeCalls (atom H round index worker x m s).2 = codeCalls s + 1 := by
  simp only [atom, state_bind_apply, emit_apply, state_pure_apply]
  simp [codeCalls, InstructionTemplate.instantiate, Instruction.oracleCost]

lemma sequence_calls (left right : PacketCode) (L R : ℕ)
    (hl : ∀ w x m s, codeCalls (left w x m s).2 = codeCalls s + L)
    (hr : ∀ w x m s, codeCalls (right w x m s).2 = codeCalls s + R)
    (w x m : ℕ) (s : CodeState) :
    codeCalls (sequence left right w x m s).2 = codeCalls s + (L + R) := by
  simp only [LongTails.Algorithms.BirchCausalPackets.sequence, state_bind_apply, hr, hl]
  omega

lemma join_calls (w x m : ℕ) (left right : ℕ × ℕ) (s : CodeState) :
    codeCalls (join w x m left right s).2 = codeCalls s := by
  simp only [join, state_bind_apply, emit_apply, state_pure_apply]
  simp [codeCalls, InstructionTemplate.instantiate, Instruction.oracleCost]

lemma fork_calls (leftWorker rightWorker : ℕ) (left right : PacketCode) (L R : ℕ)
    (hl : ∀ w x m s, codeCalls (left w x m s).2 = codeCalls s + L)
    (hr : ∀ w x m s, codeCalls (right w x m s).2 = codeCalls s + R)
    (w x m : ℕ) (s : CodeState) :
    codeCalls (fork leftWorker rightWorker left right w x m s).2 = codeCalls s + (L + R) := by
  have he (i : InstructionTemplate) (s : CodeState) :
      codeCalls (emit i s).2 = codeCalls s +
        (i.instantiate (canonicalTuning 0 1)).oracleCost := emit_calls i s
  simp only [LongTails.Algorithms.BirchCausalPackets.fork, sendState, state_bind_apply,
    state_pure_apply]
  rw [join_calls]
  simp only [he, InstructionTemplate.instantiate, Instruction.oracleCost, Nat.add_zero]
  rw [hr]
  simp only [he, InstructionTemplate.instantiate, Instruction.oracleCost, Nat.add_zero]
  rw [hl]
  simp only [he, InstructionTemplate.instantiate, Instruction.oracleCost, Nat.add_zero]
  omega

lemma nestedPacket_calls (H round leftWorker rightWorker w x m : ℕ) (s : CodeState) :
    codeCalls (nestedPacket H round leftWorker rightWorker w x m s).2 = codeCalls s + 6 := by
  have ha (i : ℕ) := atom_calls H round i
  have hl := sequence_calls (atom H round 1) (atom H round 2) 1 1 (ha 1) (ha 2)
  have hr := sequence_calls (atom H round 3) (atom H round 4) 1 1 (ha 3) (ha 4)
  have hf := fork_calls leftWorker rightWorker _ _ 2 2 hl hr
  have hs := sequence_calls _ (atom H round 5) 4 1 hf (ha 5)
  exact sequence_calls (atom H round 0) _ 1 5 (ha 0) hs w x m s

lemma nestedHistories_value : nestedHistories =
    [∅, {0}, {0, 1}, {0}, {0, 3}, {0, 1, 2, 3, 4}] := by decide

lemma nestedHistories_incomparable :
    ¬({0, 1} : Finset ℕ) ⊆ {0, 3} ∧ ¬({0, 3} : Finset ℕ) ⊆ {0, 1} := by decide

lemma incomparable_not_prefixes (s t : Finset ℕ) (hs : ¬s ⊆ t) (ht : ¬t ⊆ s)
    (order : ℕ → ℕ) (hsorder : ∃ a, s = (range a).image order)
    (htorder : ∃ b, t = (range b).image order) : False := by
  obtain ⟨a, rfl⟩ := hsorder
  obtain ⟨b, rfl⟩ := htorder
  rcases le_total a b with hab | hba
  · exact hs (image_subset_image (range_mono hab))
  · exact ht (image_subset_image (range_mono hba))

def extendedHistory (histories : List (Finset ℕ)) (n : ℕ) : Finset ℕ :=
  if n < histories.length then histories.getD n ∅ else range n

lemma extendedHistory_past (histories : List (Finset ℕ))
    (hpast : ∀ n, n < histories.length → histories.getD n ∅ ⊆ range n) :
    ∀ n, extendedHistory histories n ⊆ range n := by
  intro n
  unfold extendedHistory
  split_ifs with hn
  · exact hpast n hn
  · exact Subset.rfl

lemma extendedHistory_recent (histories : List (Finset ℕ)) (r : ℕ)
    (hrecent : ∀ n, n < histories.length → range (n - r) ⊆ histories.getD n ∅) :
    ∀ n, range (n - r) ⊆ extendedHistory histories n := by
  intro n
  unfold extendedHistory
  split_ifs with hn
  · exact hrecent n hn
  · exact range_mono (Nat.sub_le n r)

lemma extendedHistory_closed (histories : List (Finset ℕ))
    (hpast : ∀ n, n < histories.length → histories.getD n ∅ ⊆ range n)
    (hclosed : ∀ n, n < histories.length → ∀ j ∈ histories.getD n ∅,
      histories.getD j ∅ ⊆ histories.getD n ∅) :
    ∀ n j, j ∈ extendedHistory histories n →
      extendedHistory histories j ⊆ extendedHistory histories n := by
  intro n j hj
  by_cases hn : n < histories.length
  · have hj' : j ∈ histories.getD n ∅ := by simpa [extendedHistory, hn] using hj
    have hjn := mem_range.mp (hpast n hn hj')
    have hjlen : j < histories.length := by omega
    simpa [extendedHistory, hn, hjlen] using hclosed n hn j hj'
  · have hjn : j < n := by simpa [extendedHistory, hn] using hj
    simpa [extendedHistory, hn] using
      (extendedHistory_past histories hpast j).trans (range_mono hjn.le)

lemma nestedHistories_past :
    ∀ n, n < nestedHistories.length → nestedHistories.getD n ∅ ⊆ range n := by
  intro n hn
  rw [nestedHistories_value] at hn ⊢
  simp only [List.length_cons, List.length_nil] at hn
  interval_cases n <;> decide

lemma nestedHistories_recent :
    ∀ n, n < nestedHistories.length → range (n - 3) ⊆ nestedHistories.getD n ∅ := by
  intro n hn
  rw [nestedHistories_value] at hn ⊢
  simp only [List.length_cons, List.length_nil] at hn
  interval_cases n <;> decide

lemma nestedHistories_closed :
    ∀ n, n < nestedHistories.length → ∀ j ∈ nestedHistories.getD n ∅,
      nestedHistories.getD j ∅ ⊆ nestedHistories.getD n ∅ := by
  intro n hn j hj
  have hjn := mem_range.mp (nestedHistories_past n hn hj)
  rw [nestedHistories_value] at hn hj ⊢
  simp only [List.length_cons, List.length_nil] at hn
  interval_cases n <;> interval_cases j <;> simp_all

structure HistoryInvariant (state : HistoryState) : Prop where
  states_past : ∀ s, state.states s ⊆ range state.atoms
  states_closed : ∀ s j, j ∈ state.states s → state.queryHistory j ⊆ state.states s
  query_past : ∀ j, j < state.atoms → state.queryHistory j ⊆ range j
  query_closed : ∀ j, j < state.atoms → ∀ i ∈ state.queryHistory j,
    state.queryHistory i ⊆ state.queryHistory j

lemma historyInvariant_initial : HistoryInvariant {} := by
  constructor <;> simp

lemma historyInvariant_query (state : HistoryState) (worker source : ℕ)
    (h : HistoryInvariant state) : HistoryInvariant (historyStep (.query worker source) state) := by
  have hnot (s : ℕ) : state.atoms ∉ state.states s := by
    intro ha
    exact (Nat.lt_irrefl _) (mem_range.mp (h.states_past s ha))
  constructor
  · intro s
    simp only [historyStep, Function.update_apply]
    split_ifs with hs
    · exact insert_subset (mem_range.mpr (by omega))
        ((h.states_past source).trans (range_mono (by omega)))
    · exact (h.states_past s).trans (range_mono (by omega))
  · intro s j hj
    by_cases hs : s = state.next
    · subst s
      simp only [historyStep, Function.update_self] at hj ⊢
      by_cases hjnew : j = state.atoms
      · subst j
        rw [Function.update_self]
        exact subset_insert _ _
      · rw [Function.update_of_ne hjnew]
        exact (h.states_closed source j ((mem_insert.mp hj).resolve_left hjnew)).trans
          (subset_insert _ _)
    · simp only [historyStep, Function.update_of_ne hs] at hj ⊢
      have hjnew : j ≠ state.atoms := by intro he; subst j; exact hnot s hj
      rw [Function.update_of_ne hjnew]
      exact h.states_closed s j hj
  · intro j hj
    simp only [historyStep] at hj ⊢
    by_cases he : j = state.atoms
    · subst j
      simpa using h.states_past source
    · rw [Function.update_of_ne he]
      exact h.query_past j (by omega)
  · intro j hj i hi
    simp only [historyStep] at hj hi ⊢
    by_cases he : j = state.atoms
    · subst j
      rw [Function.update_self] at hi ⊢
      have hi0 : i ≠ state.atoms := by
        have := mem_range.mp (h.states_past source hi)
        omega
      rw [Function.update_of_ne hi0]
      exact h.states_closed source i hi
    · rw [Function.update_of_ne he] at hi ⊢
      have hj0 : j < state.atoms := by omega
      have hi0 : i ≠ state.atoms := by
        have := mem_range.mp (h.query_past j hj0 hi)
        omega
      rw [Function.update_of_ne hi0]
      exact h.query_closed j hj0 i hi

lemma historyInvariant_merge (state : HistoryState) (worker left right common : ℕ)
    (h : HistoryInvariant state) : HistoryInvariant (historyStep (.merge worker left right common) state) := by
  constructor
  · intro s
    simp only [historyStep, Function.update_apply]
    split_ifs
    · exact union_subset (h.states_past left) (h.states_past right)
    · exact h.states_past s
  · intro s
    simp only [historyStep, Function.update_apply]
    split_ifs
    · exact closed_union state.queryHistory _ _ (h.states_closed left) (h.states_closed right)
    · exact h.states_closed s
  · exact h.query_past
  · exact h.query_closed

lemma historyInvariant_step (state : HistoryState) (node : GraphNode)
    (h : HistoryInvariant state) : HistoryInvariant (historyStep node state) := by
  cases node with
  | query worker source => exact historyInvariant_query state worker source h
  | merge worker left right common => exact historyInvariant_merge state worker left right common h

lemma historyInvariant_fold (nodes : List GraphNode) (state : HistoryState)
    (h : HistoryInvariant state) : HistoryInvariant (nodes.foldl (flip historyStep) state) := by
  induction nodes generalizing state with
  | nil => exact h
  | cons node rest ih => exact ih _ (historyInvariant_step state node h)

lemma graphHistory_invariant (nodes : List GraphNode) : HistoryInvariant (graphHistory nodes) :=
  historyInvariant_fold nodes {} historyInvariant_initial

def packetHistory (H : ℕ) (dispatch : ℕ → ℕ) (privateHistory : ℕ → ℕ → Finset ℕ)
    (n : ℕ) : Finset ℕ :=
  range (dispatch (n / H) * H) ∪ (privateHistory (n / H) (n % H)).image (fun j => n / H * H + j)

lemma packetHistory_past (H : ℕ) (dispatch : ℕ → ℕ) (privateHistory : ℕ → ℕ → Finset ℕ)
    (hH : 0 < H) (hd : ∀ k, dispatch k ≤ k)
    (hpast : ∀ k i, i < H → privateHistory k i ⊆ range i) :
    ∀ n, packetHistory H dispatch privateHistory n ⊆ range n := by
  intro n j hj
  rcases mem_union.mp hj with hj | hj
  · exact range_mono ((Nat.mul_le_mul_right H (hd (n / H))).trans
      (Nat.div_mul_le_self n H)) hj
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    have hi0 := mem_range.mp (hpast (n / H) (n % H) (Nat.mod_lt n hH) hi)
    apply mem_range.mpr
    have he := Nat.mod_add_div n H
    rw [Nat.mul_comm H (n / H)] at he
    omega

lemma packetHistory_closed (H : ℕ) (dispatch : ℕ → ℕ) (privateHistory : ℕ → ℕ → Finset ℕ)
    (hH : 0 < H) (hd : ∀ k, dispatch k ≤ k)
    (hpast : ∀ k i, i < H → privateHistory k i ⊆ range i)
    (hclosed : ∀ k i, i < H → ∀ j ∈ privateHistory k i, privateHistory k j ⊆ privateHistory k i) :
    ∀ n j, j ∈ packetHistory H dispatch privateHistory n →
      packetHistory H dispatch privateHistory j ⊆ packetHistory H dispatch privateHistory n := by
  intro n j hj
  rcases mem_union.mp hj with hj | hj
  · exact (packetHistory_past H dispatch privateHistory hH hd hpast j).trans
      ((range_mono (mem_range.mp hj).le).trans subset_union_left)
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    have hi0 := mem_range.mp (hpast (n / H) (n % H) (Nat.mod_lt n hH) hi)
    have hiH : i < H := hi0.trans (Nat.mod_lt n hH)
    have hdiv : (n / H * H + i) / H = n / H := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hH, Nat.div_eq_of_lt hiH]
      omega
    have hmod : (n / H * H + i) % H = i := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hiH]
    simp only [packetHistory, hdiv, hmod]
    apply union_subset_union Subset.rfl
    exact image_subset_image (hclosed (n / H) (n % H) (Nat.mod_lt n hH) i hi)

lemma packetHistory_recent (H R : ℕ) (dispatch : ℕ → ℕ) (privateHistory : ℕ → ℕ → Finset ℕ)
    (hH : 0 < H) (hdelay : ∀ k, k - dispatch k ≤ R) :
    ∀ n, range (n - H * (R + 1)) ⊆ packetHistory H dispatch privateHistory n := by
  apply packet_recent_prefix _ dispatch H R hH hdelay
  exact fun _ => subset_union_left

lemma sendState_calls (sender receiver x m : ℕ) (s : CodeState) :
    codeCalls (sendState sender receiver x m s).2 = codeCalls s := by
  simp only [sendState, state_bind_apply, state_pure_apply, emit_apply]
  simp [codeCalls, InstructionTemplate.instantiate, Instruction.oracleCost]

lemma graphNodeCode_calls (H round : ℕ) (node : GraphNode) (state : GraphState) (s : CodeState) :
    codeCalls (graphNodeCode H round node state s).2 = codeCalls s + node.calls := by
  cases node <;> simp only [graphNodeCode, state_bind_apply, state_pure_apply,
    atom_calls, join_calls, sendState_calls, GraphNode.calls, Nat.add_zero]

lemma graphStep_calls (H round : ℕ) (node : GraphNode) (state : GraphState) (s : CodeState) :
    codeCalls (graphStep H round node state s).2 = codeCalls s + node.calls :=
  graphNodeCode_calls H round node state s

lemma state_forIn_variable_cost {σ α β : Type} (cost : σ → ℕ)
    (step : α → β → StateM σ β) (increment : α → ℕ)
    (hc : ∀ i b s, cost (step i b s).2 = cost s + increment i)
    (xs : List α) (b : β) (s : σ) :
    cost ((forIn xs b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s).2 =
      cost s + (xs.map increment).sum := by
  induction xs generalizing b s with
  | nil => rfl
  | cons x xs ih =>
      rw [state_forIn_cons, ih, hc]
      simp [Nat.add_assoc]

lemma graphCode_calls (H round output worker x m : ℕ) (nodes : List GraphNode) (s : CodeState) :
    codeCalls (graphCode H round nodes output worker x m s).2 =
      codeCalls s + (nodes.map GraphNode.calls).sum := by
  simp only [graphCode, state_bind_apply, state_pure_apply, sendState_calls]
  exact state_forIn_variable_cost codeCalls (graphStep H round) GraphNode.calls
    (graphStep_calls H round) nodes _ s

lemma historyStep_atoms (node : GraphNode) (state : HistoryState) :
    (historyStep node state).atoms = state.atoms + node.calls := by
  cases node <;> rfl

lemma history_fold_atoms (nodes : List GraphNode) (state : HistoryState) :
    (nodes.foldl (flip historyStep) state).atoms = state.atoms + (nodes.map GraphNode.calls).sum := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      rw [List.foldl_cons, ih]
      dsimp only [flip]
      rw [historyStep_atoms]
      simp [Nat.add_assoc]

lemma graphHistory_atoms (nodes : List GraphNode) :
    (graphHistory nodes).atoms = (nodes.map GraphNode.calls).sum := by
  simpa [graphHistory] using history_fold_atoms nodes {}

lemma graphCode_history_calls (H round output worker x m : ℕ) (nodes : List GraphNode) (s : CodeState) :
    codeCalls (graphCode H round nodes output worker x m s).2 =
      codeCalls s + (graphHistory nodes).atoms := by
  rw [graphCode_calls, graphHistory_atoms]

lemma nestedHybrid_valid (workers outer left innerA innerFirst innerSecond innerB right : ℕ)
    (ho : outer < workers) (hl : left < workers) (ha : innerA < workers)
    (hf : innerFirst < workers) (hs : innerSecond < workers)
    (hb : innerB < workers) (hr : right < workers) :
    GraphValidFrom workers {} (nestedHybridNodes outer left innerA innerFirst innerSecond innerB right) := by
  simp [nestedHybridNodes, GraphValidFrom, GraphNode.Valid, historyStep, ho, hl, ha, hf, hs, hb, hr]

lemma nestedHybrid_history (outer left innerA innerFirst innerSecond innerB right : ℕ) :
    let h := graphHistory (nestedHybridNodes outer left innerA innerFirst innerSecond innerB right)
    h.atoms = 8 ∧ h.states 12 = range 8 ∧
      (List.range 8).map h.queryHistory =
        [∅, {0}, {0, 1}, {0, 1}, {0, 1, 2}, {0, 1}, {0}, {0, 6}] := by
  norm_num [graphHistory, nestedHybridNodes, historyStep, List.range_succ, flip]
  decide

end LongTails.Proofs.BirchCausalMerges
