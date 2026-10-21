import LongTails.Proofs.MixedNoiseSchedule
import LongTails.Proofs.MixedNoiseSelectors
import LongTails.Proofs.MixedNoiseAllocation
import LongTails.Proofs.Execution

namespace OracleTemplate.MixedNoise

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma query_after_first (cfg : Config) (s : RepresentativeState cfg E) (reply : E)
    (hs : s.second = false) (hj : s.taskIndex < cfg.tasks.length) :
    representativeQuery cfg (representativeUpdate cfg s reply) = (taskPoints cfg s).2 := by
  simp [representativeUpdate, representativeQuery, hs, Nat.not_le.mpr hj]

lemma commit_first_fields (cfg : Config) (s : RepresentativeState cfg E) (r z acc : E) :
    representativeCommit cfg { s with second := true, firstReply := r, secondPoint := z } acc =
      representativeCommit cfg s acc := by
  rfl

lemma paired_update (cfg : Config) (s : RepresentativeState cfg E) (r z : E)
    (hs : s.second = false) (hj : s.taskIndex < cfg.tasks.length) :
    representativeUpdate cfg (representativeUpdate cfg s r) z =
      let task := cfg.tasks[s.taskIndex]!
      let acc := s.accumulator + (if task.level = cfg.m then r else r - z)
      if s.sampleIndex + 1 < task.size then
        { s with
          sampleIndex := s.sampleIndex + 1
          second := false
          accumulator := acc
          firstReply := 0
          secondPoint := 0 }
      else representativeCommit cfg s acc := by
  simp only [representativeUpdate, Nat.not_le.mpr hj, hs, Bool.false_eq_true,
    ↓reduceIte]
  split_ifs <;> rfl

lemma frozen_update (cfg : Config) (s : RepresentativeState cfg E) (reply : E)
    (hj : cfg.tasks.length ≤ s.taskIndex) : representativeUpdate cfg s reply = s := by
  simp [representativeUpdate, hj]

variable {Ω : Type}

noncomputable def batchContribution (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (ω : Ω) : E :=
  if (cfg.tasks[s.taskIndex]!).level = cfg.m then g (taskPoints cfg s).1 ω
  else g (taskPoints cfg s).1 ω - g (taskPoints cfg s).2 ω

def sampleOffset (cfg : Config) : ℕ → ℕ
  | 0 => 0
  | j + 1 => sampleOffset cfg j + (cfg.tasks[j]!).size

noncomputable def batchAccumulator (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (ξ : ℕ → Ω) (offset n : ℕ) : E :=
  ∑ i ∈ Finset.range n, batchContribution cfg g s (ξ (offset + i))

noncomputable def batchState (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) : ℕ → RepresentativeState cfg E
  | 0 => (multiscaleRepresentatives cfg x0).initial seed
  | j + 1 =>
      let s := batchState cfg g x0 seed ξ j
      representativeCommit cfg s
        (batchAccumulator cfg g s ξ (sampleOffset cfg j) (cfg.tasks[j]!).size)

noncomputable def sampledPair (cfg : Config) (g : E → Ω → E)
    (ω : Ω) (s : RepresentativeState cfg E) : RepresentativeState cfg E :=
  let s' := representativeUpdate cfg s (g (representativeQuery cfg s) ω)
  representativeUpdate cfg s' (g (representativeQuery cfg s') ω)

lemma sampledPair_eq (cfg : Config) (g : E → Ω → E)
    (ω : Ω) (s : RepresentativeState cfg E) (hs : s.second = false)
    (hj : s.taskIndex < cfg.tasks.length) :
    sampledPair cfg g ω s =
      let acc := s.accumulator + batchContribution cfg g s ω
      if s.sampleIndex + 1 < (cfg.tasks[s.taskIndex]!).size then
        { s with
          sampleIndex := s.sampleIndex + 1
          second := false
          accumulator := acc
          firstReply := 0
          secondPoint := 0 }
      else representativeCommit cfg s acc := by
  dsimp only [sampledPair]
  rw [query_after_first cfg s _ hs hj, paired_update cfg s _ _ hs hj]
  simp only [representativeQuery, hs, Bool.false_eq_true, ↓reduceIte, batchContribution]

noncomputable def partialBatchState (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (ξ : ℕ → Ω) (offset n : ℕ) :
    RepresentativeState cfg E :=
  { s with
    sampleIndex := n
    second := false
    firstReply := 0
    secondPoint := 0
    accumulator := batchAccumulator cfg g s ξ offset n }

omit [InnerProductSpace ℝ E] in
lemma partialBatchState_zero (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (ξ : ℕ → Ω) (offset : ℕ)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (ha : s.accumulator = 0)
    (hr : s.firstReply = 0) (hp : s.secondPoint = 0) :
    partialBatchState cfg g s ξ offset 0 = s := by
  cases s
  simp_all [partialBatchState, batchAccumulator]

lemma partialBatchState_step (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (ξ : ℕ → Ω) (offset n : ℕ)
    (hj : s.taskIndex < cfg.tasks.length) :
    sampledPair cfg g (ξ (offset + n)) (partialBatchState cfg g s ξ offset n) =
      if n + 1 < (cfg.tasks[s.taskIndex]!).size then
        partialBatchState cfg g s ξ offset (n + 1)
      else representativeCommit cfg s (batchAccumulator cfg g s ξ offset (n + 1)) := by
  rw [sampledPair_eq cfg g (ξ (offset + n))
    (partialBatchState cfg g s ξ offset n) rfl (show
      (partialBatchState cfg g s ξ offset n).taskIndex < cfg.tasks.length from hj)]
  simp only [partialBatchState, batchAccumulator, Finset.sum_range_succ,
    batchContribution, taskPoints, representativeCommit]
  rfl

noncomputable def sampledPairs (cfg : Config) (g : E → Ω → E)
    (ξ : ℕ → Ω) (offset : ℕ) (s : RepresentativeState cfg E) :
    ℕ → RepresentativeState cfg E
  | 0 => s
  | n + 1 => sampledPair cfg g (ξ (offset + n)) (sampledPairs cfg g ξ offset s n)

lemma sampledPairs_partial (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (ξ : ℕ → Ω) (offset n : ℕ)
    (hj : s.taskIndex < cfg.tasks.length)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (ha : s.accumulator = 0)
    (hr : s.firstReply = 0) (hp : s.secondPoint = 0)
    (hsize : n < (cfg.tasks[s.taskIndex]!).size) :
    sampledPairs cfg g ξ offset s n = partialBatchState cfg g s ξ offset n := by
  induction n with
  | zero => exact (partialBatchState_zero cfg g s ξ offset hn hs ha hr hp).symm
  | succ n ih =>
    rw [sampledPairs, ih (by omega), partialBatchState_step cfg g s ξ offset n hj]
    exact ite_eq_left hsize

lemma sampledPairs_batch (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (ξ : ℕ → Ω) (offset : ℕ)
    (hj : s.taskIndex < cfg.tasks.length)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (ha : s.accumulator = 0)
    (hr : s.firstReply = 0) (hp : s.secondPoint = 0) :
    sampledPairs cfg g ξ offset s (cfg.tasks[s.taskIndex]!).size =
      representativeCommit cfg s
        (batchAccumulator cfg g s ξ offset (cfg.tasks[s.taskIndex]!).size) := by
  have hpos : 0 < (cfg.tasks[s.taskIndex]!).size := by
    rw [getElem!_pos cfg.tasks s.taskIndex hj]
    exact task_size_pos cfg (List.getElem_mem hj)
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [he, sampledPairs,
    sampledPairs_partial cfg g s ξ offset n hj hn hs ha hr hp (by omega),
    partialBatchState_step cfg g s ξ offset n hj]
  simp only [he, lt_self_iff_false, ↓reduceIte]

noncomputable def indexedStep (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (sc : RepresentativeState cfg E × ℕ) : RepresentativeState cfg E × ℕ :=
  (representativeUpdate cfg sc.1 (g (representativeQuery cfg sc.1) (ξ (sc.2 / 2))),
    sc.2 + 1)

lemma indexedStep_pair (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (s : RepresentativeState cfg E) (offset : ℕ) :
    (indexedStep cfg g ξ)^[2] (s, 2 * offset) =
      (sampledPair cfg g (ξ offset) s, 2 * (offset + 1)) := by
  have h0 : 2 * offset / 2 = offset := by omega
  have h1 : (2 * offset + 1) / 2 = offset := by omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    indexedStep, h0, h1, sampledPair]
  congr 1

lemma indexedStep_pairs (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (s : RepresentativeState cfg E) (offset n : ℕ) :
    (indexedStep cfg g ξ)^[2 * n] (s, 2 * offset) =
      (sampledPairs cfg g ξ offset s n, 2 * (offset + n)) := by
  induction n with
  | zero => simp [sampledPairs]
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2 * n) 2, Function.iterate_add_apply, ih,
      indexedStep_pair]
    simp only [sampledPairs, Nat.add_assoc]

lemma batchState_index (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).taskIndex = j := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [batchState, representativeCommit] using congrArg Nat.succ ih

lemma batchState_sample (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).sampleIndex = 0 := by
  cases j <;> rfl

lemma batchState_second (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).second = false := by
  cases j <;> rfl

lemma batchState_accumulator (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).accumulator = 0 := by
  cases j <;> rfl

lemma batchState_firstReply (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).firstReply = 0 := by
  cases j <;> rfl

lemma batchState_secondPoint (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).secondPoint = 0 := by
  cases j <;> rfl

lemma indexedStep_batchState (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) (hj : j ≤ cfg.tasks.length) :
    (indexedStep cfg g ξ)^[2 * sampleOffset cfg j]
        ((multiscaleRepresentatives cfg x0).initial seed, 0) =
      (batchState cfg g x0 seed ξ j, 2 * sampleOffset cfg j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j < cfg.tasks.length := by omega
    rw [sampleOffset, Nat.mul_add, Nat.add_comm (2 * sampleOffset cfg j),
      Function.iterate_add_apply, ih (by omega), indexedStep_pairs]
    have he := sampledPairs_batch cfg g (batchState cfg g x0 seed ξ j) ξ
      (sampleOffset cfg j) (by simpa only [batchState_index] using hj')
      (batchState_sample cfg g x0 seed ξ j) (batchState_second cfg g x0 seed ξ j)
      (batchState_accumulator cfg g x0 seed ξ j) (batchState_firstReply cfg g x0 seed ξ j)
      (batchState_secondPoint cfg g x0 seed ξ j)
    simp only [batchState_index] at he
    rw [he]
    simp only [batchState, Nat.mul_add, Nat.add_comm]

lemma sampleOffset_le_succ (cfg : Config) (j : ℕ) :
    sampleOffset cfg j ≤ sampleOffset cfg (j + 1) := Nat.le_add_right _ _

lemma sampleOffset_mono (cfg : Config) : Monotone (sampleOffset cfg) :=
  monotone_nat_of_le_succ (sampleOffset_le_succ cfg)

lemma sampleOffset_eq_sum_take (cfg : Config) (j : ℕ) (hj : j ≤ cfg.tasks.length) :
    sampleOffset cfg j = ((cfg.tasks.take j).map BatchTask.size).sum := by
  induction j with
  | zero => simp [sampleOffset]
  | succ j ih =>
    have hj' : j < cfg.tasks.length := by omega
    rw [sampleOffset, ih (by omega), List.take_succ_eq_append_getElem hj',
      List.map_append, List.sum_append, getElem!_pos cfg.tasks j hj']
    simp

lemma calls_eq_sampleOffset (cfg : Config) :
    cfg.calls = 2 * sampleOffset cfg cfg.tasks.length := by
  rw [sampleOffset_eq_sum_take cfg _ le_rfl, List.take_length]
  rfl

lemma execute_batchState (cfg : Config) (g : E → Ω → E) (x0 : E)
    (O : Oracle E E) (seed : RepresentativeSeed cfg)
    (ξ : (k : ℕ) → O.Seed k) (ζ : ℕ → Ω)
    (hanswer : ∀ k x, O.answer k (0, x) (ξ k.length) = g x (ζ (k.length / 2))) :
    execute O (multiscaleRepresentatives cfg x0) (fun _ => cfg.calls) seed ξ =
      representativeOutput (batchState cfg g x0 seed ζ cfg.tasks.length) := by
  have hans : ∀ history query, O.answer history query (ξ history.length) =
      g query.2 (ζ (history.length / 2)) := by
    intro history query
    have hi : query.1 = 0 := Subsingleton.elim _ _
    simpa only [← hi] using hanswer history query.2
  erw [execute_indexed_of_answer O _ _ _ ξ (fun k query => g query.2 (ζ (k / 2))) hans]
  change representativeOutput ((indexedStep cfg g ζ)^[cfg.calls]
    ((multiscaleRepresentatives cfg x0).initial seed, 0)).1 = _
  rw [calls_eq_sampleOffset, indexedStep_batchState cfg g x0 seed ζ _ le_rfl]

lemma indexedStep_frozen (cfg : Config) (g : E → Ω → E) (ζ : ℕ → Ω)
    (s : RepresentativeState cfg E) (hs : cfg.tasks.length ≤ s.taskIndex) (c n : ℕ) :
    ((indexedStep cfg g ζ)^[n] (s, c)).1 = s := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [indexedStep, frozen_update cfg s _ hs]
    exact ih (c + 1)

lemma execute_batchState_of_le (cfg : Config) (g : E → Ω → E) (x0 : E)
    (O : Oracle E E) (seed : RepresentativeSeed cfg)
    (ξ : (k : ℕ) → O.Seed k) (ζ : ℕ → Ω)
    (hanswer : ∀ k x, O.answer k (0, x) (ξ k.length) = g x (ζ (k.length / 2)))
    (K : ℕ) (hK : cfg.calls ≤ K) :
    execute O (multiscaleRepresentatives cfg x0) (fun _ => K) seed ξ =
      representativeOutput (batchState cfg g x0 seed ζ cfg.tasks.length) := by
  have hans : ∀ history query, O.answer history query (ξ history.length) =
      g query.2 (ζ (history.length / 2)) := by
    intro history query
    have hi : query.1 = 0 := Subsingleton.elim _ _
    simpa only [← hi] using hanswer history query.2
  erw [execute_indexed_of_answer O _ _ _ ξ (fun k query => g query.2 (ζ (k / 2))) hans]
  change representativeOutput ((indexedStep cfg g ζ)^[K]
    ((multiscaleRepresentatives cfg x0).initial seed, 0)).1 = _
  rw [show K = (K - cfg.calls) + cfg.calls by omega,
    Function.iterate_add_apply, calls_eq_sampleOffset,
    indexedStep_batchState cfg g x0 seed ζ _ le_rfl,
    indexedStep_frozen cfg g ζ _ (by simp [batchState_index])]

lemma batchState_dep (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (j : ℕ) (ξ ξ' : ℕ → Ω)
    (h : ∀ i, i < sampleOffset cfg j → ξ i = ξ' i) :
    batchState cfg g x0 seed ξ j = batchState cfg g x0 seed ξ' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hprev : batchState cfg g x0 seed ξ j = batchState cfg g x0 seed ξ' j :=
      ih (fun i hi => h i (hi.trans_le (sampleOffset_le_succ cfg j)))
    simp only [batchState, hprev]
    congr 1
    unfold batchAccumulator
    apply Finset.sum_congr rfl
    intro i hi
    rw [h (sampleOffset cfg j + i) (by
      have hi := Finset.mem_range.mp hi
      simp only [sampleOffset]
      omega)]

lemma batchState_seed (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).seed = seed := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma taskPoints_outputIndex (cfg : Config) (s : RepresentativeState cfg E)
    (τ : Fin (max 1 cfg.T)) :
    taskPoints cfg { s with seed := { s.seed with outputIndex := τ } } = taskPoints cfg s := by
  rfl

omit [InnerProductSpace ℝ E] in
lemma batchContribution_outputIndex (cfg : Config) (g : E → Ω → E)
    (s : RepresentativeState cfg E) (τ : Fin (max 1 cfg.T)) (ω : Ω) :
    batchContribution cfg g { s with seed := { s.seed with outputIndex := τ } } ω =
      batchContribution cfg g s ω := by
  rfl

lemma batchState_outputIndex (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (τ : Fin (max 1 cfg.T)) (j : ℕ) :
    batchState cfg g x0 { seed with outputIndex := τ } ξ j =
      { batchState cfg g x0 seed ξ j with seed := { seed with outputIndex := τ } } := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [batchState, ih, batchState]
    generalize hB : batchState cfg g x0 seed ξ j = B
    have hseed : B.seed = seed := hB ▸ batchState_seed cfg g x0 seed ξ j
    rw [← hseed]
    rfl

lemma batchState_seed_dep (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed seed' : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j cutoff : ℕ)
    (hrep : ∀ i : Fin (cfg.m + 1) × Fin (cfg.T + 1), i.2.val < cutoff →
      seed.representatives i = seed'.representatives i)
    (htime : ∀ k < j, (cfg.tasks[k]!).t < cutoff) :
    (batchState cfg g x0 seed ξ j).xs = (batchState cfg g x0 seed' ξ j).xs ∧
      (batchState cfg g x0 seed ξ j).estimates =
        (batchState cfg g x0 seed' ξ j).estimates := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hx, hd⟩ := ih (fun k hk => htime k (by omega))
    have hp : taskPoints cfg (batchState cfg g x0 seed ξ j) =
        taskPoints cfg (batchState cfg g x0 seed' ξ j) := by
      simp only [taskPoints, batchState_index, batchState_seed]
      rw [hx, anchorIndex_dep cfg seed seed' (htime j (by omega)) hrep,
        anchorIndex_dep cfg seed seed' (htime j (by omega)) hrep]
    have ha : batchAccumulator cfg g (batchState cfg g x0 seed ξ j) ξ
        (sampleOffset cfg j) (cfg.tasks[j]!).size =
        batchAccumulator cfg g (batchState cfg g x0 seed' ξ j) ξ
        (sampleOffset cfg j) (cfg.tasks[j]!).size := by
      unfold batchAccumulator
      apply Finset.sum_congr rfl
      intro i hi
      simp only [batchContribution, batchState_index, hp]
    simp only [batchState, representativeCommit, batchState_index]
    rw [ha, hx, hd]
    exact ⟨rfl, rfl⟩

lemma commit_preserves_past (cfg : Config) (s : RepresentativeState cfg E)
    (acc : E) {n : ℕ} (hn : n ≤ (cfg.tasks[s.taskIndex]!).t) :
    (representativeCommit cfg s acc).xs n = s.xs n := by
  simp only [representativeCommit]
  split_ifs
  · exact Function.update_of_ne (by omega) _ _
  · rfl

lemma batchState_preserves_past (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {j k n : ℕ} (hjk : j ≤ k)
    (htime : ∀ i, j ≤ i → i < k → n ≤ (cfg.tasks[i]!).t) :
    (batchState cfg g x0 seed ξ k).xs n = (batchState cfg g x0 seed ξ j).xs n := by
  induction k with
  | zero =>
    have hj : j = 0 := by omega
    subst j
    rfl
  | succ k ih =>
    by_cases he : j = k + 1
    · rw [he]
    have hjk' : j ≤ k := by omega
    rw [batchState, commit_preserves_past cfg _ _ (by
      simpa only [batchState_index] using htime k hjk' (by omega))]
    exact ih hjk' (fun i hji hik => htime i hji (by omega))

lemma batchState_initial_point (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    (batchState cfg g x0 seed ξ j).xs 0 = x0 := by
  have h := batchState_preserves_past cfg g x0 seed ξ (Nat.zero_le j)
    (fun _ _ _ => Nat.zero_le _)
  exact h

lemma boundary_path_stable (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {t k n : ℕ}
    (ht : t ≤ cfg.T) (hk : cfg.eventOffset t ≤ k) (hkT : k ≤ cfg.tasks.length)
    (hn : n ≤ t) :
    (batchState cfg g x0 seed ξ k).xs n =
      (batchState cfg g x0 seed ξ (cfg.eventOffset t)).xs n := by
  apply batchState_preserves_past cfg g x0 seed ξ hk
  intro i hi hik
  exact hn.trans (tasks_after_time cfg ht hi (hik.trans_le hkT))

lemma event_path_final (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {j n : ℕ}
    (hj : j < cfg.tasks.length) (hn : n ≤ (cfg.tasks[j]!).t) :
    (batchState cfg g x0 seed ξ j).xs n =
      (batchState cfg g x0 seed ξ cfg.tasks.length).xs n := by
  have hmem : cfg.tasks[j]! ∈ cfg.tasks := by
    rw [getElem!_pos cfg.tasks j hj]
    exact List.getElem_mem hj
  have ht := task_time_lt cfg hmem
  have hoff : cfg.eventOffset (cfg.tasks[j]!).t ≤ j := by
    by_contra hh
    have hb := tasks_before_time cfg ht.le (by omega : j < cfg.eventOffset (cfg.tasks[j]!).t)
    omega
  symm
  apply batchState_preserves_past cfg g x0 seed ξ hj.le
  intro i hji hi
  exact hn.trans (tasks_after_time cfg ht.le (hoff.trans hji) hi)

lemma taskPoints_final (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {j : ℕ} (hj : j < cfg.tasks.length) :
    let task := cfg.tasks[j]!
    let X := (batchState cfg g x0 seed ξ cfg.tasks.length).xs
    taskPoints cfg (batchState cfg g x0 seed ξ j) =
      if task.level = cfg.m then
        (X (anchorIndex cfg seed task.t task.level), X (anchorIndex cfg seed task.t task.level))
      else (X (anchorIndex cfg seed task.t task.level),
        X (anchorIndex cfg seed task.t (task.level + 1))) := by
  dsimp only
  have hmem : cfg.tasks[j]! ∈ cfg.tasks := by
    rw [getElem!_pos cfg.tasks j hj]
    exact List.getElem_mem hj
  have ht := (task_time_lt cfg hmem).le
  have hl : (cfg.tasks[j]!).level ≤ cfg.m := by
    have h := task_level_mem cfg hmem
    by_cases hz : (cfg.tasks[j]!).t = 0
    · simp only [Config.levels, hz, ↓reduceIte, List.mem_singleton] at h
      exact h.le
    · exact ((levels_mem cfg hz).mp h).1
  simp only [taskPoints, batchState_index, batchState_seed]
  rw [event_path_final cfg g x0 seed ξ hj (anchorIndex_le cfg seed hl ht)]
  split_ifs with he
  · rfl
  · rw [event_path_final cfg g x0 seed ξ hj (anchorIndex_le cfg seed (by omega) ht)]

lemma iteration_path_step (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {t : ℕ} (ht : t < cfg.T) :
    (batchState cfg g x0 seed ξ cfg.tasks.length).xs (t + 1) =
      (batchState cfg g x0 seed ξ cfg.tasks.length).xs t - cfg.η •
        ∑ l ∈ Finset.range (cfg.m + 1),
          (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l := by
  have hlen := levels_length_pos cfg t
  let i := (cfg.levels t).length - 1
  have hi : i < (cfg.levels t).length := by dsimp [i]; omega
  have hilast : i + 1 = (cfg.levels t).length := by dsimp [i]; omega
  let j := cfg.eventOffset t + i
  have hjnext : j + 1 = cfg.eventOffset (t + 1) := by
    rw [eventOffset_succ]
    dsimp [j]
    omega
  have hjT : j < cfg.tasks.length := by
    have h := (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
    change cfg.eventOffset (t + 1) ≤ cfg.tasks.length at h
    omega
  have htask := tasks_iteration_at cfg ht hi
  rw [iterationTask_at cfg t i hi] at htask
  have htime : (cfg.tasks[j]!).t = t := congrArg BatchTask.t htask
  have hfinish : (cfg.tasks[j]!).finish = true := by
    have h := congrArg BatchTask.finish htask
    simpa only [hilast, decide_true] using h
  have hleft := boundary_path_stable cfg g x0 seed ξ (show t + 1 ≤ cfg.T by omega)
    (show cfg.eventOffset (t + 1) ≤ cfg.tasks.length by omega) le_rfl le_rfl
  rw [hleft, ← hjnext]
  have hright : (batchState cfg g x0 seed ξ cfg.tasks.length).xs t =
      (batchState cfg g x0 seed ξ j).xs t := by
    apply batchState_preserves_past cfg g x0 seed ξ (Nat.le_of_lt hjT)
    intro k hjk hkT
    exact tasks_after_time cfg (Nat.le_of_lt ht)
      (show cfg.eventOffset t ≤ k by dsimp [j] at hjk; omega) hkT
  rw [hright]
  simp only [batchState, representativeCommit, batchState_index, htime, hfinish,
    ↓reduceIte, Function.update_self]

lemma boundary_history_dep (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed seed' : RepresentativeSeed cfg) (ξ : ℕ → Ω) {t : ℕ} (ht : t ≤ cfg.T)
    (hrep : ∀ i : Fin (cfg.m + 1) × Fin (cfg.T + 1), i.2.val < t →
      seed.representatives i = seed'.representatives i) :
    (batchState cfg g x0 seed ξ (cfg.eventOffset t)).xs =
      (batchState cfg g x0 seed' ξ (cfg.eventOffset t)).xs :=
  (batchState_seed_dep cfg g x0 seed seed' ξ (cfg.eventOffset t) t hrep
    (fun _k hk => tasks_before_time cfg ht hk)).1

lemma boundary_history_fresh (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed seed' : RepresentativeSeed cfg) (ξ : ℕ → Ω)
    (i : Fin (cfg.m + 1) × Fin (cfg.T + 1))
    (he : (representativeSplit cfg i seed).2 = (representativeSplit cfg i seed').2) :
    (batchState cfg g x0 seed ξ (cfg.eventOffset i.2.val)).xs =
      (batchState cfg g x0 seed' ξ (cfg.eventOffset i.2.val)).xs := by
  apply boundary_history_dep cfg g x0 seed seed' ξ (by have := i.2.isLt; omega)
  intro j hj
  have hne : j ≠ i := by
    intro hji
    rw [hji] at hj
    exact Nat.lt_irrefl _ hj
  simp only [representativeSplit_snd, Prod.mk.injEq] at he
  exact congrFun he.2 ⟨j, hne⟩

open MeasureTheory ProbabilityTheory in
lemma boundary_selected_energy (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Ω) (i : Fin (cfg.m + 1) × Fin (cfg.T + 1)) (φ : E → ℝ) :
    (∫ seed, φ ((batchState cfg g x0 seed ξ (cfg.eventOffset i.2.val)).xs
      (i.2.val - 4 ^ i.1.val + (seed.representatives i).val))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) =
    ∫ seed, (4 ^ i.1.val : ℝ)⁻¹ *
      ∑ a : Fin (4 ^ i.1.val), φ ((batchState cfg g x0 seed ξ
        (cfg.eventOffset i.2.val)).xs (i.2.val - 4 ^ i.1.val + a.val))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
  let : Nonempty (Fin (4 ^ i.1.val)) := ⟨⟨0, by positivity⟩⟩
  let : Nonempty (Fin (max 1 cfg.T) ×
      ((j : {j : Fin (cfg.m + 1) × Fin (cfg.T + 1) // j ≠ i}) →
        Fin (4 ^ j.val.1.val))) :=
    ⟨(representativeSplit cfg i (Classical.choice inferInstance)).2⟩
  have h := uniform_choice_energy (representativeSplit cfg i)
    (fun seed a => φ ((batchState cfg g x0 seed ξ (cfg.eventOffset i.2.val)).xs
      (i.2.val - 4 ^ i.1.val + a.val))) (by
        intro seed seed' he
        funext a
        rw [boundary_history_fresh cfg g x0 seed seed' ξ i he])
  simpa only [representativeSplit_fst, integral_uniform_finite, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using h

open MeasureTheory ProbabilityTheory in
lemma final_selected_energy (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Ω) (i : Fin (cfg.m + 1) × Fin (cfg.T + 1)) (φ : E → ℝ)
    (hb : 4 ^ i.1.val ≤ i.2.val) :
    (∫ seed, φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs
      (i.2.val - 4 ^ i.1.val + (seed.representatives i).val))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) =
    ∫ seed, (4 ^ i.1.val : ℝ)⁻¹ *
      ∑ a : Fin (4 ^ i.1.val), φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs
        (i.2.val - 4 ^ i.1.val + a.val))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
  have ht : i.2.val ≤ cfg.T := by have := i.2.isLt; omega
  have hk : cfg.eventOffset i.2.val ≤ cfg.tasks.length :=
    (prefixTasks_prefix cfg ht).length_le
  have he (seed : RepresentativeSeed cfg) (a : Fin (4 ^ i.1.val)) :
      (batchState cfg g x0 seed ξ cfg.tasks.length).xs (i.2.val - 4 ^ i.1.val + a.val) =
      (batchState cfg g x0 seed ξ (cfg.eventOffset i.2.val)).xs
        (i.2.val - 4 ^ i.1.val + a.val) :=
    boundary_path_stable cfg g x0 seed ξ ht hk le_rfl (by have := a.isLt; omega)
  simp_rw [he]
  exact boundary_selected_energy cfg g x0 ξ i φ

open MeasureTheory ProbabilityTheory in
lemma anchor_selected_energy (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Ω) (φ : E → ℝ) {t l : ℕ} (hl0 : 0 < l) (hl : l ≤ cfg.m)
    (ht : t ≤ cfg.T) (hstart : 4 ^ l ≤ t) :
    (∫ seed, φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) =
    ∫ seed, (4 ^ l : ℝ)⁻¹ *
      ∑ a : Fin (4 ^ l), φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs
        (t / 4 ^ l * 4 ^ l - 4 ^ l + a.val))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
  have hp : 0 < 4 ^ l := by positivity
  have hb : t / 4 ^ l * 4 ^ l ≤ cfg.T := (Nat.div_mul_le_self t (4 ^ l)).trans ht
  have hd : 1 ≤ t / 4 ^ l := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hstart)
  have hs : 4 ^ l ≤ t / 4 ^ l * 4 ^ l := by
    simpa only [one_mul] using Nat.mul_le_mul_right (4 ^ l) hd
  have hb0 : t / 4 ^ l * 4 ^ l ≠ 0 := by omega
  let i : Fin (cfg.m + 1) × Fin (cfg.T + 1) :=
    (⟨l, by omega⟩, ⟨t / 4 ^ l * 4 ^ l, by omega⟩)
  have h := final_selected_energy cfg g x0 ξ i φ hs
  simpa only [anchorIndex, hl0.ne', hb0, hl, hb, ↓reduceIte, ↓reduceDIte, i] using h

open MeasureTheory ProbabilityTheory in
lemma regular_anchor_energy (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Ω) (φ : E → ℝ) (hφ : ∀ x, 0 ≤ φ x) {l n : ℕ}
    (hl : l ≤ cfg.m) (hT : cfg.T = n * 4 ^ l) :
    (∑ t ∈ Finset.range cfg.T, if t < 4 ^ l then 0 else
      ∫ seed, φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l))
        ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) ≤
      ∫ seed, ∑ t ∈ Finset.range cfg.T,
        φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)
        ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
  by_cases hlzero : l = 0
  · subst l
    simp only [anchorIndex_zero, pow_zero]
    calc
      _ ≤ ∑ t ∈ Finset.range cfg.T,
          ∫ seed, φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)
            ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs
        · exact integral_nonneg (fun seed => hφ _)
        · exact le_rfl
      _ = _ := (integral_finsetSum _ (fun _ _ => Integrable.of_finite)).symm
  have hl0 : 0 < l := Nat.pos_of_ne_zero hlzero
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let X := fun seed => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  have he (t : ℕ) (ht : t < cfg.T) :
      (if t < 4 ^ l then 0 else ∫ seed, φ (X seed (anchorIndex cfg seed t l)) ∂Q) =
        ∫ seed, (if t < 4 ^ l then 0 else
          (∑ k ∈ Finset.range (4 ^ l), φ (X seed ((t / 4 ^ l - 1) * 4 ^ l + k))) / (4 ^ l : ℕ)) ∂Q := by
    by_cases hs : t < 4 ^ l
    · simp [hs]
    · simp only [hs, ↓reduceIte]
      rw [anchor_selected_energy cfg g x0 ξ φ hl0 hl ht.le (by omega)]
      congr 1
      funext seed
      rw [Fin.sum_univ_eq_sum_range (fun k => φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs
        (t / 4 ^ l * 4 ^ l - 4 ^ l + k))) (4 ^ l)]
      simp only [Nat.sub_mul, one_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [div_eq_mul_inv, mul_comm]
  change (∑ t ∈ Finset.range cfg.T, if t < 4 ^ l then 0 else
    ∫ seed, φ (X seed (anchorIndex cfg seed t l)) ∂Q) ≤ _
  rw [Finset.sum_congr rfl (fun t ht => he t (Finset.mem_range.mp ht))]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro seed
  change (∑ t ∈ Finset.range cfg.T, if t < 4 ^ l then 0 else
    (∑ k ∈ Finset.range (4 ^ l), φ (X seed ((t / 4 ^ l - 1) * 4 ^ l + k))) / (4 ^ l : ℕ)) ≤ _
  rw [hT]
  exact held_previous_block_energy (fun k => φ (X seed k)) (fun k => hφ _) n (4 ^ l) (by positivity)

open MeasureTheory ProbabilityTheory in
lemma uniform_output_energy (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Ω) (j : ℕ) (φ : E → ℝ) :
    (∫ seed, φ (representativeOutput (batchState cfg g x0 seed ξ j))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) =
    ∫ seed, (max 1 cfg.T : ℝ)⁻¹ *
      ∑ a : Fin (max 1 cfg.T), φ ((batchState cfg g x0 seed ξ j).xs a.val)
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure := by
  let : Nonempty (Fin (max 1 cfg.T)) := ⟨⟨0, by omega⟩⟩
  let : Nonempty ((i : Fin (cfg.m + 1) × Fin (cfg.T + 1)) → Fin (4 ^ i.1.val)) :=
    ⟨fun _ => ⟨0, by positivity⟩⟩
  have h := uniform_choice_energy (representativeSeedEquiv cfg)
    (fun seed a => φ ((batchState cfg g x0 seed ξ j).xs a.val)) (by
      intro seed seed' he
      have hs : seed' = { seed with outputIndex := seed'.outputIndex } := by
        cases seed
        cases seed'
        simp only [representativeSeedEquiv, Equiv.coe_fn_mk] at he
        cases he
        rfl
      have hx : (batchState cfg g x0 seed' ξ j).xs =
          (batchState cfg g x0 seed ξ j).xs := by
        rw [hs]
        have hxx := congrArg (fun s : RepresentativeState cfg E => s.xs)
          (batchState_outputIndex cfg g x0 seed ξ seed'.outputIndex j)
        exact hxx
      exact congrArg (fun xs => fun a : Fin (max 1 cfg.T) => φ (xs a.val)) hx.symm)
  simpa only [representativeOutput, batchState_seed, representativeSeedEquiv,
    Equiv.coe_fn_mk, integral_uniform_finite, Fintype.card_fin, Nat.cast_max,
    Nat.cast_one] using h

section Measurability

open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma batchState_measurable (cfg : Config) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (x0 : E) (seed : RepresentativeSeed cfg) (j : ℕ) :
    (∀ k, Measurable (fun ξ => (batchState cfg g x0 seed ξ j).xs k)) ∧
    (∀ l, Measurable (fun ξ => (batchState cfg g x0 seed ξ j).estimates l)) := by
  classical
  induction j with
  | zero => exact ⟨fun _ => measurable_const, fun _ => measurable_const⟩
  | succ j ih =>
    have hleft : Measurable (fun ξ => (taskPoints cfg (batchState cfg g x0 seed ξ j)).1) := by
      simp only [taskPoints, batchState_index, batchState_seed]
      split_ifs <;> exact ih.1 _
    have hright : Measurable (fun ξ => (taskPoints cfg (batchState cfg g x0 seed ξ j)).2) := by
      simp only [taskPoints, batchState_index, batchState_seed]
      split_ifs <;> exact ih.1 _
    have hc (n : ℕ) : Measurable (fun ξ =>
        batchContribution cfg g (batchState cfg g x0 seed ξ j) (ξ n)) := by
      simp only [batchContribution, batchState_index]
      split_ifs
      · exact hg.comp (hleft.prodMk (measurable_pi_apply n))
      · exact (hg.comp (hleft.prodMk (measurable_pi_apply n))).sub
          (hg.comp (hright.prodMk (measurable_pi_apply n)))
    have ha : Measurable (fun ξ => batchAccumulator cfg g (batchState cfg g x0 seed ξ j)
        ξ (sampleOffset cfg j) (cfg.tasks[j]!).size) :=
      Finset.measurable_sum _ fun n _ => hc _
    have he (l : ℕ) : Measurable (fun ξ =>
        (batchState cfg g x0 seed ξ (j + 1)).estimates l) := by
      simp only [batchState, representativeCommit, batchState_index, Function.update_apply]
      split_ifs
      · exact ha.const_smul _
      · exact ih.2 l
    refine ⟨fun k => ?_, he⟩
    have hv : Measurable (fun ξ => ∑ l ∈ Finset.range (cfg.m + 1),
        (batchState cfg g x0 seed ξ (j + 1)).estimates l) :=
      Finset.measurable_sum _ fun l _ => he l
    have hx := (ih.1 (cfg.tasks[j]!).t).sub (hv.const_smul cfg.η)
    simp only [batchState, representativeCommit, batchState_index] at hx ⊢
    split_ifs
    · simp only [Function.update_apply]
      split_ifs
      · convert hx using 1
        funext ξ
        simp only [Pi.sub_apply, Pi.smul_apply, Function.update_apply]
      · exact ih.1 k
    · exact ih.1 k

lemma batchOutput_measurable (cfg : Config) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (x0 : E) (j : ℕ) :
    Measurable (fun z : RepresentativeSeed cfg × (ℕ → Ω) =>
      representativeOutput (batchState cfg g x0 z.1 z.2 j)) := by
  apply measurable_from_prod_countable_right
  intro seed
  simp only [representativeOutput, batchState_seed]
  exact (batchState_measurable cfg g hg x0 seed j).1 _

end Measurability

end OracleTemplate.MixedNoise
