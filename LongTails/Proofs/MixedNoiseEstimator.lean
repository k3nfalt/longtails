import LongTails.Proofs.MixedNoiseIntegrability

namespace OracleTemplate.MixedNoise

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

def lastTask (cfg : Config) (level : ℕ) : ℕ → Option ℕ
  | 0 => none
  | j + 1 => if (cfg.tasks[j]!).level = level then some j else lastTask cfg level j

noncomputable def eventValue (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) : E :=
  ((cfg.tasks[j]!).size : ℝ)⁻¹ • batchAccumulator cfg g (batchState cfg g x0 seed ξ j)
    ξ (sampleOffset cfg j) (cfg.tasks[j]!).size

lemma estimate_lastTask (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j level : ℕ) :
    (batchState cfg g x0 seed ξ j).estimates level =
      match lastTask cfg level j with
      | none => 0
      | some k => eventValue cfg g x0 seed ξ k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [batchState, representativeCommit, batchState_index, lastTask, Function.update_apply]
    by_cases he : (cfg.tasks[j]!).level = level
    · simp only [he, ↓reduceIte, eventValue]
    · simp only [he, Ne.symm he, ↓reduceIte]
      exact ih

lemma lastTask_lt (cfg : Config) {level j k : ℕ} (h : lastTask cfg level j = some k) : k < j := by
  induction j with
  | zero => simp [lastTask] at h
  | succ j ih =>
    simp only [lastTask] at h
    split_ifs at h with he
    · cases h
      omega
    · exact (ih h).trans (Nat.lt_succ_self j)

lemma lastTask_level (cfg : Config) {level j k : ℕ}
    (h : lastTask cfg level j = some k) : (cfg.tasks[k]!).level = level := by
  induction j with
  | zero => simp [lastTask] at h
  | succ j ih =>
    simp only [lastTask] at h
    split_ifs at h with he
    · cases h
      exact he
    · exact ih h

lemma lastTask_stable (cfg : Config) (level : ℕ) {j k : ℕ} (hjk : j ≤ k)
    (hnone : ∀ i, j ≤ i → i < k → (cfg.tasks[i]!).level ≠ level) :
    lastTask cfg level k = lastTask cfg level j := by
  induction k with
  | zero =>
    have hj : j = 0 := by omega
    subst j
    rfl
  | succ k ih =>
    by_cases he : j = k + 1
    · rw [he]
    have hjk' : j ≤ k := by omega
    rw [lastTask, ite_eq_right (hnone k hjk' (by omega))]
    exact ih hjk' (fun i hji hik => hnone i hji (by omega))

lemma lastTask_after_event (cfg : Config) {level j n : ℕ}
    (hj : j < n) (he : (cfg.tasks[j]!).level = level)
    (hnone : ∀ i, j < i → i < n → (cfg.tasks[i]!).level ≠ level) :
    lastTask cfg level n = some j := by
  rw [lastTask_stable cfg level (show j + 1 ≤ n by omega)
    (fun i hji hin => hnone i (by omega) hin), lastTask, ite_eq_left he]

lemma lastTask_latest (cfg : Config) {level j n : ℕ}
    (he : lastTask cfg level n = some j) :
    ∀ i, j < i → i < n → (cfg.tasks[i]!).level ≠ level := by
  induction n with
  | zero => simp [lastTask] at he
  | succ n ih =>
    intro i hji hin
    simp only [lastTask] at he
    split_ifs at he with hn
    · cases he
      omega
    · by_cases hi : i = n
      · simpa [hi] using hn
      · exact ih he i hji (by omega)

lemma lastTask_none (cfg : Config) {level n : ℕ}
    (he : lastTask cfg level n = none) :
    ∀ i, i < n → (cfg.tasks[i]!).level ≠ level := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [lastTask] at he
    split_ifs at he with hn
    intro i hi
    by_cases hin : i = n
    · simpa only [hin] using hn
    · exact ih he i (by omega)

lemma lastTask_no_refresh (cfg : Config) {t l j : ℕ} (ht : t < cfg.T)
    (hl : l ≤ cfg.m) (he : lastTask cfg l (cfg.eventOffset (t + 1)) = some j) :
    ∀ u, (cfg.tasks[j]!).t < u → u ≤ t → u % 4 ^ l ≠ 0 := by
  have hj := lastTask_lt cfg he
  have hjT : j < cfg.tasks.length := hj.trans_le
    (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
  intro u hju hut hu
  have hu0 : u ≠ 0 := by omega
  obtain ⟨k, hk, hk', hkT, hkt, hkl⟩ := event_at_level cfg (by omega : u < cfg.T)
    ((levels_mem cfg hu0).mpr ⟨hl, hu⟩)
  have hju' : j < cfg.eventOffset u := by
    by_contra hh
    have htime := tasks_after_time cfg (show u ≤ cfg.T by omega) (by omega) hjT
    omega
  have hkbound : k < cfg.eventOffset (t + 1) := by
    by_contra hh
    have htime := tasks_after_time cfg (show t + 1 ≤ cfg.T by omega) (by omega) hkT
    omega
  exact lastTask_latest cfg he k (by omega) hkbound hkl

lemma lastTask_time (cfg : Config) {t l j : ℕ} (ht : t < cfg.T)
    (hl : l ≤ cfg.m) (he : lastTask cfg l (cfg.eventOffset (t + 1)) = some j) :
    (cfg.tasks[j]!).t = t / 4 ^ l * 4 ^ l := by
  have hj := lastTask_lt cfg he
  have hjT : j < cfg.tasks.length := hj.trans_le
    (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
  have hmem : cfg.tasks[j]! ∈ cfg.tasks := by
    rw [getElem!_pos cfg.tasks j hjT]
    exact List.getElem_mem hjT
  have hlevel := lastTask_level cfg he
  have htime := tasks_before_time cfg (show t + 1 ≤ cfg.T by omega) hj
  let a := (cfg.tasks[j]!).t
  have ha : a % 4 ^ l = 0 := by
    by_cases hz : a = 0
    · simp [hz]
    · have hm := task_level_mem cfg hmem
      rw [hlevel] at hm
      exact ((levels_mem cfg hz).mp hm).2
  have hab : a / 4 ^ l * 4 ^ l = a := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ha)
  have hnext : t < a + 4 ^ l := by
    by_contra hh
    have hp : 0 < 4 ^ l := by positivity
    have hm := lastTask_no_refresh cfg ht hl he (a + 4 ^ l) (by dsimp [a]; omega) (by omega)
    apply hm
    simp only [Nat.add_mod, ha, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
  have hdiv : t / 4 ^ l = a / 4 ^ l := by
    apply Nat.div_eq_of_lt_le
    · rw [hab]
      exact Nat.le_of_lt_succ htime
    · rw [Nat.add_mul, hab, one_mul]
      exact hnext
  rw [hdiv, hab]

lemma lastTask_anchor (cfg : Config) (seed : RepresentativeSeed cfg) {t l j : ℕ}
    (ht : t < cfg.T) (hl : l ≤ cfg.m)
    (he : lastTask cfg l (cfg.eventOffset (t + 1)) = some j) :
    anchorIndex cfg seed t l = anchorIndex cfg seed (cfg.tasks[j]!).t l ∧
    anchorIndex cfg seed t (l + 1) = anchorIndex cfg seed (cfg.tasks[j]!).t (l + 1) := by
  have hj := lastTask_lt cfg he
  have htime := tasks_before_time cfg (show t + 1 ≤ cfg.T by omega) hj
  have hmod := lastTask_no_refresh cfg ht hl he
  exact ⟨anchorIndex_held cfg seed (by omega) hmod,
    anchorIndex_held cfg seed (by omega) (fun u hju hut => parent_not_refresh (hmod u hju hut))⟩

lemma missingTask_anchors (cfg : Config) (seed : RepresentativeSeed cfg) {t l : ℕ}
    (ht : t < cfg.T) (hl : l ≤ cfg.m)
    (he : lastTask cfg l (cfg.eventOffset (t + 1)) = none) :
    l ≠ cfg.m ∧ anchorIndex cfg seed t l = 0 ∧ anchorIndex cfg seed t (l + 1) = 0 := by
  have hmissing := lastTask_none cfg he
  have hbefore {u j : ℕ} (hu : u ≤ t) (hj : j < cfg.tasks.length)
      (hjt : (cfg.tasks[j]!).t = u) : j < cfg.eventOffset (t + 1) := by
    by_contra hh
    have htime := tasks_after_time cfg (show t + 1 ≤ cfg.T by omega) (by omega) hj
    omega
  have hroot : l ≠ cfg.m := by
    intro hm
    obtain ⟨j, hj, hj', hjT, hjt, hjl⟩ := event_at_level cfg (by omega : 0 < cfg.T)
      (show cfg.m ∈ cfg.levels 0 by simp [Config.levels])
    exact hmissing j (hbefore (by omega) hjT hjt) (hjl.trans hm.symm)
  have hmod : ∀ u, 0 < u → u ≤ t → u % 4 ^ l ≠ 0 := by
    intro u hu hut hm
    obtain ⟨j, hj, hj', hjT, hjt, hjl⟩ := event_at_level cfg (by omega : u < cfg.T)
      ((levels_mem cfg hu.ne').mpr ⟨hl, hm⟩)
    exact hmissing j (hbefore hut hjT hjt) hjl
  refine ⟨hroot, ?_, ?_⟩
  · rw [anchorIndex_held cfg seed (Nat.zero_le t) hmod, anchorIndex_at_zero]
  · rw [anchorIndex_held cfg seed (Nat.zero_le t)
      (fun u hu hut => parent_not_refresh (hmod u hu hut)), anchorIndex_at_zero]

lemma centered_batch_identity (b : ℕ) (hb : 0 < b) (v : ℕ → E) (μ : E) :
    (b : ℝ)⁻¹ • (∑ i ∈ Finset.range b, v i) - μ =
      (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b, (v i - μ) := by
  rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hb.ne'), one_smul]

noncomputable def taskMean (cfg : Config) (G : E → E) (s : RepresentativeState cfg E) : E :=
  if (cfg.tasks[s.taskIndex]!).level = cfg.m then G (taskPoints cfg s).1
  else G (taskPoints cfg s).1 - G (taskPoints cfg s).2

lemma lastTask_mean_current (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {t l j : ℕ}
    (ht : t < cfg.T) (hl : l ≤ cfg.m)
    (he : lastTask cfg l (cfg.eventOffset (t + 1)) = some j) :
    let X := (batchState cfg g x0 seed ξ cfg.tasks.length).xs
    taskMean cfg G (batchState cfg g x0 seed ξ j) =
      if l = cfg.m then G (X (anchorIndex cfg seed t l))
      else G (X (anchorIndex cfg seed t l)) - G (X (anchorIndex cfg seed t (l + 1))) := by
  dsimp only
  have hj := lastTask_lt cfg he
  have hjT : j < cfg.tasks.length := hj.trans_le
    (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
  have hlevel := lastTask_level cfg he
  have ha := lastTask_anchor cfg seed ht hl he
  simp only [taskMean, batchState_index, taskPoints_final cfg g x0 seed ξ hjT, hlevel]
  split_ifs <;> simp only [ha.1, ha.2]

omit [InnerProductSpace ℝ E] in
lemma centered_contribution (cfg : Config) (g : E → Ω → E) (G : E → E)
    (s : RepresentativeState cfg E) (ω : Ω) :
    batchContribution cfg g s ω - taskMean cfg G s =
      if (cfg.tasks[s.taskIndex]!).level = cfg.m then
        g (taskPoints cfg s).1 ω - G (taskPoints cfg s).1
      else (g (taskPoints cfg s).1 ω - G (taskPoints cfg s).1) -
        (g (taskPoints cfg s).2 ω - G (taskPoints cfg s).2) := by
  unfold batchContribution taskMean
  split_ifs <;> abel

omit [InnerProductSpace ℝ E] in
lemma hierarchy_telescopes (m : ℕ) (v : ℕ → E) :
    (∑ l ∈ Finset.range (m + 1), if l = m then v l else v l - v (l + 1)) = v 0 := by
  rw [Finset.sum_range_succ]
  simp only [↓reduceIte]
  have he : (∑ l ∈ Finset.range m, if l = m then v l else v l - v (l + 1)) =
      ∑ l ∈ Finset.range m, (v l - v (l + 1)) := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Nat.ne_of_lt (Finset.mem_range.mp hl), ↓reduceIte]
  rw [he, Finset.sum_range_sub']
  abel

omit [InnerProductSpace ℝ E] in
lemma hierarchy_error_decomposition (m : ℕ) (v d : ℕ → E) :
    (∑ l ∈ Finset.range (m + 1), d l) - v 0 =
      ∑ l ∈ Finset.range (m + 1), (d l - (if l = m then v l else v l - v (l + 1))) := by
  rw [Finset.sum_sub_distrib, hierarchy_telescopes]

noncomputable def centeredKernel (root : Bool) (g : E → Ω → E) (G : E → E)
    (y : E × E) (ω : Ω) : E :=
  if root then g y.1 ω - G y.1
  else (g y.1 ω - G y.1) - (g y.2 ω - G y.2)

noncomputable def kernelVariance (root : Bool) (G : E → E) (r M σ : ℝ) (y : E × E) : ℝ :=
  if root then r * ‖G y.1‖ ^ 2 + σ ^ 2
  else r * (‖G y.1‖ ^ 2 + ‖G y.2‖ ^ 2) + M ^ 2 * ‖y.1 - y.2‖ ^ 2

noncomputable def componentWeight (cfg : Config) (t l : ℕ) : ℝ :=
  match lastTask cfg l (cfg.eventOffset (t + 1)) with
  | none => 0
  | some j => ((cfg.tasks[j]!).size : ℝ)⁻¹

lemma componentWeight_nonneg (cfg : Config) (t l : ℕ) : 0 ≤ componentWeight cfg t l := by
  unfold componentWeight
  split <;> positivity

lemma componentWeight_le_inv_batch (cfg : Config) {t l : ℕ}
    (ht : t < cfg.T) (hl : l ≤ cfg.m) :
    componentWeight cfg t l ≤ ((max 1 (cfg.batch (t / 4 ^ l * 4 ^ l) l) : ℕ) : ℝ)⁻¹ := by
  unfold componentWeight
  cases he : lastTask cfg l (cfg.eventOffset (t + 1)) with
  | none => positivity
  | some j =>
    have hj := lastTask_lt cfg he
    have hjT : j < cfg.tasks.length := hj.trans_le
      (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
    have hmem : cfg.tasks[j]! ∈ cfg.tasks := by
      rw [getElem!_pos cfg.tasks j hjT]
      exact List.getElem_mem hjT
    dsimp only
    rw [task_size_eq cfg hmem, lastTask_time cfg ht hl he, lastTask_level cfg he]

lemma event_kernel_current (cfg : Config) (g : E → Ω → E) (G : E → E) (r M σ : ℝ)
    (x0 : E) (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {t l j : ℕ}
    (ht : t < cfg.T) (hl : l ≤ cfg.m)
    (he : lastTask cfg l (cfg.eventOffset (t + 1)) = some j) :
    let X := (batchState cfg g x0 seed ξ cfg.tasks.length).xs
    kernelVariance (decide ((cfg.tasks[j]!).level = cfg.m)) G r M σ
      (taskPoints cfg (batchState cfg g x0 seed ξ j)) =
    kernelVariance (decide (l = cfg.m)) G r M σ
      (X (anchorIndex cfg seed t l), X (anchorIndex cfg seed t (l + 1))) := by
  dsimp only
  have hj := lastTask_lt cfg he
  have hjT : j < cfg.tasks.length := hj.trans_le
    (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
  have hlevel := lastTask_level cfg he
  have ha := lastTask_anchor cfg seed ht hl he
  rw [taskPoints_final cfg g x0 seed ξ hjT, hlevel]
  simp only [kernelVariance, decide_eq_true_eq]
  split_ifs <;> simp only [ha.1, ha.2]

noncomputable def eventError (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) : E :=
  eventValue cfg g x0 seed ξ j - taskMean cfg G (batchState cfg g x0 seed ξ j)

lemma eventValue_eq_estimate (cfg : Config) (g : E → Ω → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) :
    eventValue cfg g x0 seed ξ j =
      (batchState cfg g x0 seed ξ (j + 1)).estimates (cfg.tasks[j]!).level := by
  simp only [batchState, representativeCommit, batchState_index, Function.update_self, eventValue]

lemma eventError_dep (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (j : ℕ) (ξ ξ' : ℕ → Ω)
    (h : ∀ i, i < sampleOffset cfg (j + 1) → ξ i = ξ' i) :
    eventError cfg g G x0 seed ξ j = eventError cfg g G x0 seed ξ' j := by
  have hs := batchState_dep cfg g x0 seed (j + 1) ξ ξ' h
  have hp := batchState_dep cfg g x0 seed j ξ ξ'
    (fun i hi => h i (hi.trans_le (sampleOffset_le_succ cfg j)))
  simp only [eventError, eventValue_eq_estimate, hs, hp]

lemma eventError_eq_kernel (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (j : ℕ) (hj : j < cfg.tasks.length) :
    eventError cfg g G x0 seed ξ j =
      ((cfg.tasks[j]!).size : ℝ)⁻¹ • ∑ i ∈ Finset.range (cfg.tasks[j]!).size,
        centeredKernel (decide ((cfg.tasks[j]!).level = cfg.m)) g G
          (taskPoints cfg (batchState cfg g x0 seed ξ j)) (ξ (sampleOffset cfg j + i)) := by
  have hb : 0 < (cfg.tasks[j]!).size := by
    rw [getElem!_pos cfg.tasks j hj]
    exact task_size_pos cfg (List.getElem_mem hj)
  unfold eventError eventValue batchAccumulator
  rw [centered_batch_identity _ hb]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [centered_contribution]
  simp only [centeredKernel, batchState_index, decide_eq_true_eq]

noncomputable def selectedErrors (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (active : ℕ → Bool) (ξ : ℕ → Ω) (n : ℕ) : E :=
  ∑ j ∈ Finset.range n, if active j then eventError cfg g G x0 seed ξ j else 0

lemma selectedErrors_dep (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (active : ℕ → Bool) (n : ℕ) (ξ ξ' : ℕ → Ω)
    (h : ∀ i, i < sampleOffset cfg n → ξ i = ξ' i) :
    selectedErrors cfg g G x0 seed active ξ n = selectedErrors cfg g G x0 seed active ξ' n := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [eventError_dep cfg g G x0 seed j ξ ξ' (fun i hi => h i
    (hi.trans_le (sampleOffset_mono cfg (by have := Finset.mem_range.mp hj; omega))))]

def activeEvent (cfg : Config) (n j : ℕ) : Bool :=
  decide ((cfg.tasks[j]!).level ≤ cfg.m ∧
    lastTask cfg (cfg.tasks[j]!).level n = some j)

omit [InnerProductSpace ℝ E] in
lemma active_event_sum (cfg : Config) (n : ℕ) (v : ℕ → E) :
    (∑ j ∈ Finset.range n, if activeEvent cfg n j then v j else 0) =
      ∑ l ∈ Finset.range (cfg.m + 1),
        match lastTask cfg l n with | none => 0 | some j => v j := by
  classical
  have hinner (l : ℕ) :
      (∑ j ∈ Finset.range n, if lastTask cfg l n = some j then v j else 0) =
        match lastTask cfg l n with | none => 0 | some j => v j := by
    cases he : lastTask cfg l n with
    | none => simp
    | some k =>
      have hk := lastTask_lt cfg he
      simp [hk]
  rw [← Finset.sum_congr rfl (fun l _ => hinner l), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases ha : activeEvent cfg n j = true
  · have h := (of_decide_eq_true ha)
    simp [ha]
    symm
    rw [Finset.sum_eq_single (cfg.tasks[j]!).level]
    · simp only [h.2, ↓reduceIte]
    · intro l hl hne
      have hn : lastTask cfg l n ≠ some j := by
        intro he
        exact hne (lastTask_level cfg he).symm
      simp [hn]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · have hz (l : ℕ) (hl : l ∈ Finset.range (cfg.m + 1)) : lastTask cfg l n ≠ some j := by
      intro he
      apply ha
      apply decide_eq_true
      have hlevel := lastTask_level cfg he
      exact ⟨by have := Finset.mem_range.mp hl; omega, by rw [hlevel]; exact he⟩
    simp [ha]
    symm
    exact Finset.sum_eq_zero (fun l hl => by simp [hz l hl])

lemma stored_error_sum (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) (n : ℕ) :
    selectedErrors cfg g G x0 seed (activeEvent cfg n) ξ n =
      ∑ l ∈ Finset.range (cfg.m + 1),
        match lastTask cfg l n with
        | none => 0
        | some j => (batchState cfg g x0 seed ξ n).estimates l -
            taskMean cfg G (batchState cfg g x0 seed ξ j) := by
  rw [selectedErrors, active_event_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [estimate_lastTask]
  cases lastTask cfg l n <;> rfl

lemma actual_estimator_error (cfg : Config) (g : E → Ω → E) (G : E → E) (x0 : E)
    (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) {t : ℕ} (ht : t < cfg.T) :
    (∑ l ∈ Finset.range (cfg.m + 1),
      (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l) -
        G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t) =
      selectedErrors cfg g G x0 seed (activeEvent cfg (cfg.eventOffset (t + 1))) ξ
        (cfg.eventOffset (t + 1)) := by
  let X := (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  let v := fun l => G (X (anchorIndex cfg seed t l))
  have hv0 : v 0 = G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t) := by
    simp [v, X, anchorIndex_zero]
  rw [← hv0, hierarchy_error_decomposition, stored_error_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hlm : l ≤ cfg.m := by have := Finset.mem_range.mp hl; omega
  cases he : lastTask cfg l (cfg.eventOffset (t + 1)) with
  | none =>
    have hm := missingTask_anchors cfg seed ht hlm he
    rw [estimate_lastTask, he]
    simp [v, hm.1, hm.2.1, hm.2.2]
  | some j =>
    dsimp only
    rw [lastTask_mean_current cfg g G x0 seed ξ ht hlm he]

open MeasureTheory ProbabilityTheory

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma centeredKernel_measurable (root : Bool) (g : E → Ω → E) (G : E → E)
    (hg : Measurable (Function.uncurry g)) (hG : Measurable G) :
    Measurable (Function.uncurry (centeredKernel root g G)) := by
  have h1 : Measurable (fun z : (E × E) × Ω => g z.1.1 z.2 - G z.1.1) :=
    (hg.comp (measurable_fst.fst.prodMk measurable_snd)).sub (hG.comp measurable_fst.fst)
  have h2 : Measurable (fun z : (E × E) × Ω => g z.1.2 z.2 - G z.1.2) :=
    (hg.comp (measurable_fst.snd.prodMk measurable_snd)).sub (hG.comp measurable_fst.snd)
  cases root
  · exact h1.sub h2
  · exact h1

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma centeredKernel_integral (p : Measure Ω) [IsProbabilityMeasure p]
    (root : Bool) (g : E → Ω → E) (G : E → E)
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x) (y : E × E) :
    Integrable (centeredKernel root g G y) p ∧ ∫ ω, centeredKernel root g G y ω ∂p = 0 := by
  have hi (x : E) : Integrable (fun ω => g x ω - G x) p := (hgi x).sub (integrable_const _)
  have hz (x : E) : ∫ ω, g x ω - G x ∂p = 0 := by
    rw [integral_sub (hgi x) (integrable_const _), hmean]
    simp
  cases root
  · refine ⟨(hi y.1).sub (hi y.2), ?_⟩
    change (∫ ω, (g y.1 ω - G y.1) - (g y.2 ω - G y.2) ∂p) = 0
    rw [integral_sub (hi y.1) (hi y.2), hz, hz, sub_self]
  · exact ⟨hi y.1, hz y.1⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma centeredKernel_variance (p : Measure Ω) (root : Bool) (g : E → Ω → E) (G : E → E)
    (r M σ : ℝ)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2 ∂p ≤
      r * (‖G x‖ ^ 2 + ‖G y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2) (y : E × E) :
    Integrable (fun ω => ‖centeredKernel root g G y ω‖ ^ 2) p ∧
      ∫ ω, ‖centeredKernel root g G y ω‖ ^ 2 ∂p ≤ kernelVariance root G r M σ y := by
  cases root
  · exact ⟨hdiff y.1 y.2, hmixed y.1 y.2⟩
  · exact ⟨hnoise y.1, hbound y.1⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma kernelVariance_integrable {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsFiniteMeasure P] (root : Bool) (G : E → E) {L : NNReal} (hG : LipschitzWith L G)
    (r M σ : ℝ) (S : α → E × E)
    (h1 : MemLp (fun a => (S a).1) 2 P) (h2 : MemLp (fun a => (S a).2) 2 P) :
    Integrable (fun a => kernelVariance root G r M σ (S a)) P := by
  have hg1 := lipschitz_comp_memLp hG h1
  have hg2 := lipschitz_comp_memLp hG h2
  have hi1 := (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hg1.aestronglyMeasurable).mp hg1
  have hi2 := (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hg2.aestronglyMeasurable).mp hg2
  have hd := h1.sub h2
  have hid := (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hd.aestronglyMeasurable).mp hd
  cases root
  · exact ((hi1.add hi2).const_mul r).add (hid.const_mul (M ^ 2))
  · exact (hi1.const_mul r).add (integrable_const _)

omit [CompleteSpace E] in
lemma eventError_measurable (cfg : Config) (g : E → Ω → E) (G : E → E)
    (hg : Measurable (Function.uncurry g)) (hG : Measurable G)
    (x0 : E) (seed : RepresentativeSeed cfg) (j : ℕ) :
    Measurable (fun ξ => eventError cfg g G x0 seed ξ j) := by
  have hp := batchPoints_measurable cfg g hg x0 seed j
  have hmean : Measurable (fun ξ => taskMean cfg G (batchState cfg g x0 seed ξ j)) := by
    simp only [taskMean, batchState_index]
    split_ifs
    · exact hG.comp hp.fst
    · exact (hG.comp hp.fst).sub (hG.comp hp.snd)
  simp only [eventError, eventValue_eq_estimate]
  exact ((batchState_measurable cfg g hg x0 seed (j + 1)).2 _).sub hmean

omit [CompleteSpace E] in
lemma selectedErrors_measurable (cfg : Config) (g : E → Ω → E) (G : E → E)
    (hg : Measurable (Function.uncurry g)) (hG : Measurable G)
    (x0 : E) (seed : RepresentativeSeed cfg) (active : ℕ → Bool) (n : ℕ) :
    Measurable (fun ξ => selectedErrors cfg g G x0 seed active ξ n) := by
  apply Finset.measurable_sum
  intro j hj
  by_cases ha : active j = true
  · simpa only [ha, ↓reduceIte] using eventError_measurable cfg g G hg hG x0 seed j
  · simp [ha]

lemma event_error_add_bound (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {L : NNReal} (hG : LipschitzWith L G) (r M σ : ℝ)
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2 ∂p ≤
      r * (‖G x‖ ^ 2 + ‖G y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) (seed : RepresentativeSeed cfg) (j : ℕ) (hj : j < cfg.tasks.length)
    (B : (ℕ → Ω) → E) (hB : Measurable B)
    (hdB : ∀ ξ ξ', (∀ i, i < sampleOffset cfg j → ξ i = ξ' i) → B ξ = B ξ')
    (hB2 : Integrable (fun ξ => ‖B ξ‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p)) :
    let P := Measure.infinitePi fun _ : ℕ => p
    let S := fun ξ => taskPoints cfg (batchState cfg g x0 seed ξ j)
    Integrable (fun ξ => ‖B ξ + eventError cfg g G x0 seed ξ j‖ ^ 2) P ∧
    (∫ ξ, ‖B ξ + eventError cfg g G x0 seed ξ j‖ ^ 2 ∂P) ≤
      (∫ ξ, ‖B ξ‖ ^ 2 ∂P) + (∫ ξ,
        kernelVariance (decide ((cfg.tasks[j]!).level = cfg.m)) G r M σ (S ξ) ∂P) /
        (cfg.tasks[j]!).size := by
  dsimp only
  simp_rw [eventError_eq_kernel cfg g G x0 seed _ j hj]
  let root := decide ((cfg.tasks[j]!).level = cfg.m)
  have hpoints := batchPoints_memLp p cfg g hg G hG r σ hnoise hbound x0 seed j
  have hi := centeredKernel_integral p root g G hgi hmean
  have hv := centeredKernel_variance p root g G r M σ hnoise hbound hdiff hmixed
  apply batch_average_variable_variance p (sampleOffset cfg j)
    (fun ξ => taskPoints cfg (batchState cfg g x0 seed ξ j))
    (batchPoints_measurable cfg g hg x0 seed j) _ B hB hdB hB2
    (centeredKernel root g G) (centeredKernel_measurable root g G hg hG.continuous.measurable)
    (fun y => (hi y).1) (fun y => (hi y).2) (fun y => (hv y).1)
    (kernelVariance root G r M σ) (fun y => (hv y).2)
    (kernelVariance_integrable root G hG r M σ _ hpoints.1 hpoints.2)
    (cfg.tasks[j]!).size
  · rw [getElem!_pos cfg.tasks j hj]
    exact task_size_pos cfg (List.getElem_mem hj)
  · intro ξ ξ' he
    rw [batchState_dep cfg g x0 seed j ξ ξ' he]

lemma selectedErrors_moment_bound (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {L : NNReal} (hG : LipschitzWith L G) (r M σ : ℝ)
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2 ∂p ≤
      r * (‖G x‖ ^ 2 + ‖G y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) (seed : RepresentativeSeed cfg) (active : ℕ → Bool)
    (n : ℕ) (hn : n ≤ cfg.tasks.length) :
    let P := Measure.infinitePi fun _ : ℕ => p
    Integrable (fun ξ => ‖selectedErrors cfg g G x0 seed active ξ n‖ ^ 2) P ∧
      (∫ ξ, ‖selectedErrors cfg g G x0 seed active ξ n‖ ^ 2 ∂P) ≤
        ∑ j ∈ Finset.range n, if active j then
          (∫ ξ, kernelVariance (decide ((cfg.tasks[j]!).level = cfg.m)) G r M σ
            (taskPoints cfg (batchState cfg g x0 seed ξ j)) ∂P) / (cfg.tasks[j]!).size else 0 := by
  dsimp only
  induction n with
  | zero => simp [selectedErrors]
  | succ n ih =>
    obtain ⟨hI, hboundSum⟩ := ih (by omega)
    by_cases ha : active n = true
    · have h := event_error_add_bound p cfg g hg G hG r M σ hgi hmean hnoise hbound hdiff hmixed
        x0 seed n (by omega) (fun ξ => selectedErrors cfg g G x0 seed active ξ n)
        (selectedErrors_measurable cfg g G hg hG.continuous.measurable x0 seed active n)
        (selectedErrors_dep cfg g G x0 seed active n) hI
      dsimp only at h
      have he (ξ : ℕ → Ω) : selectedErrors cfg g G x0 seed active ξ (n + 1) =
          selectedErrors cfg g G x0 seed active ξ n + eventError cfg g G x0 seed ξ n := by
        simp only [selectedErrors, Finset.sum_range_succ, ha, ↓reduceIte]
      simp_rw [he]
      refine ⟨h.1, ?_⟩
      rw [Finset.sum_range_succ]
      simp only [ha, ↓reduceIte]
      exact h.2.trans (add_le_add hboundSum le_rfl)
    · have he (ξ : ℕ → Ω) : selectedErrors cfg g G x0 seed active ξ (n + 1) =
          selectedErrors cfg g G x0 seed active ξ n := by
        simp [selectedErrors, Finset.sum_range_succ, ha]
      simp_rw [he]
      refine ⟨hI, ?_⟩
      simpa [Finset.sum_range_succ, ha] using hboundSum

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma active_variance_sum_eq (p : Measure Ω) (cfg : Config) (g : E → Ω → E)
    (G : E → E) (r M σ : ℝ) (x0 : E) (seed : RepresentativeSeed cfg)
    (t : ℕ) (ht : t < cfg.T) :
    (∑ l ∈ Finset.range (cfg.m + 1),
      match lastTask cfg l (cfg.eventOffset (t + 1)) with
      | none => 0
      | some j => (∫ ξ,
          kernelVariance (decide ((cfg.tasks[j]!).level = cfg.m)) G r M σ
            (taskPoints cfg (batchState cfg g x0 seed ξ j))
          ∂(Measure.infinitePi fun _ : ℕ => p)) / (cfg.tasks[j]!).size) =
    ∑ l ∈ Finset.range (cfg.m + 1), componentWeight cfg t l *
      (∫ ξ, kernelVariance (decide (l = cfg.m)) G r M σ
        ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l),
          (batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1)))
        ∂(Measure.infinitePi fun _ : ℕ => p)) := by
  apply Finset.sum_congr rfl
  intro l hl
  have hlm : l ≤ cfg.m := by have := Finset.mem_range.mp hl; omega
  cases he : lastTask cfg l (cfg.eventOffset (t + 1)) with
  | none => simp only [componentWeight, he, zero_mul]
  | some j =>
    simp only [componentWeight, he]
    simp_rw [event_kernel_current cfg g G r M σ x0 seed _ ht hlm he]
    rw [div_eq_mul_inv, mul_comm]

lemma actual_estimator_moment_bound (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {L : NNReal} (hG : LipschitzWith L G) (r M σ : ℝ)
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2 ∂p ≤
      r * (‖G x‖ ^ 2 + ‖G y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) (seed : RepresentativeSeed cfg) (t : ℕ) (ht : t < cfg.T) :
    let P := Measure.infinitePi fun _ : ℕ => p
    let error := fun ξ => (∑ l ∈ Finset.range (cfg.m + 1),
      (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l) -
      G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)
    Integrable (fun ξ => ‖error ξ‖ ^ 2) P ∧
      (∫ ξ, ‖error ξ‖ ^ 2 ∂P) ≤
        ∑ l ∈ Finset.range (cfg.m + 1), componentWeight cfg t l *
          (∫ ξ, kernelVariance (decide (l = cfg.m)) G r M σ
            ((batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t l),
              (batchState cfg g x0 seed ξ cfg.tasks.length).xs (anchorIndex cfg seed t (l + 1))) ∂P) := by
  dsimp only
  simp_rw [actual_estimator_error cfg g G x0 seed _ ht]
  have h := selectedErrors_moment_bound p cfg g hg G hG r M σ hgi hmean hnoise hbound hdiff hmixed
    x0 seed (activeEvent cfg (cfg.eventOffset (t + 1))) (cfg.eventOffset (t + 1))
    (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
  dsimp only at h
  rw [active_event_sum, active_variance_sum_eq p cfg g G r M σ x0 seed t ht] at h
  exact h

end OracleTemplate.MixedNoise
