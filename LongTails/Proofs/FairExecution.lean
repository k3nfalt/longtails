import LongTails.Algorithms.FairVarianceReduction
import LongTails.Proofs.Execution
import LongTails.Proofs.FairTrajectory

namespace OracleTemplate.FairVarianceReduction

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma query_after_first (cfg : Config) (s : State cfg E) (reply : E)
    (hs : s.second = false) (ht : s.t < cfg.T) :
    query cfg (update cfg s reply) = (points cfg s).2 := by
  simp [update, query, hs, Nat.not_le.mpr ht]

lemma frozen_update (cfg : Config) (s : State cfg E) (reply : E)
    (ht : cfg.T ≤ s.t) : update cfg s reply = s := by
  simp [update, ht]

lemma finishBlock_buffers (cfg : Config) (s : State cfg E) (second : Bool) (point : E)
    (right : ℕ → E) :
    finishBlock cfg { s with second := second, secondPoint := point } right = finishBlock cfg s right := by
  unfold finishBlock commitObservation
  split_ifs <;> rfl

lemma paired_update (cfg : Config) (s : State cfg E) (a b : E)
    (hs : s.second = false) (ht : s.t < cfg.T) :
    update cfg (update cfg s a) b =
      if s.sampleIndex + 1 < cfg.m then
        { s with
          sampleIndex := s.sampleIndex + 1
          second := false
          secondPoint := 0
          left := Function.update s.left s.sampleIndex a
          right := Function.update s.right s.sampleIndex b }
      else finishBlock cfg { s with left := Function.update s.left s.sampleIndex a }
        (Function.update s.right s.sampleIndex b) := by
  simp only [update, Nat.not_le.mpr ht, hs, Bool.false_eq_true, ↓reduceIte]
  split_ifs
  · rfl
  · exact finishBlock_buffers cfg { s with left := Function.update s.left s.sampleIndex a }
      true (points cfg s).2 _

def prefixValues (a : ℕ → E) (n : ℕ) : ℕ → E := fun i => if i < n then a i else 0

omit [InnerProductSpace ℝ E] in
lemma prefixValues_zero (a : ℕ → E) : prefixValues a 0 = fun _ => 0 := by
  funext i
  simp [prefixValues]

omit [InnerProductSpace ℝ E] in
lemma prefixValues_update (a : ℕ → E) (n : ℕ) :
    Function.update (prefixValues a n) n (a n) = prefixValues a (n + 1) := by
  funext i
  by_cases hi : i = n
  · subst i
    simp [prefixValues]
  · rw [Function.update_of_ne hi]
    simp only [prefixValues]
    by_cases hn : i < n
    · rw [ite_eq_left hn, ite_eq_left (by omega)]
    · rw [ite_eq_right hn, ite_eq_right (by omega)]

lemma commitObservation_buffers (cfg : Config) (s : State cfg E) (n : ℕ) (second : Bool)
    (point : E) (left right : ℕ → E) (v : E) :
    commitObservation cfg { s with
      sampleIndex := n
      second := second
      secondPoint := point
      left := left
      right := right } v = commitObservation cfg s v := by
  unfold commitObservation
  split_ifs <;> rfl

variable {Ω : Type}

noncomputable def sampledPair (cfg : Config) (g : E → Ω → E) (ω : Ω) (s : State cfg E) : State cfg E :=
  let s' := update cfg s (g (query cfg s) ω)
  update cfg s' (g (query cfg s') ω)

lemma sampledPair_eq (cfg : Config) (g : E → Ω → E) (ω : Ω) (s : State cfg E)
    (hs : s.second = false) (ht : s.t < cfg.T) :
    sampledPair cfg g ω s =
      if s.sampleIndex + 1 < cfg.m then
        { s with
          sampleIndex := s.sampleIndex + 1
          second := false
          secondPoint := 0
          left := Function.update s.left s.sampleIndex (g (points cfg s).1 ω)
          right := Function.update s.right s.sampleIndex (g (points cfg s).2 ω) }
      else finishBlock cfg { s with left := Function.update s.left s.sampleIndex (g (points cfg s).1 ω) }
        (Function.update s.right s.sampleIndex (g (points cfg s).2 ω)) := by
  dsimp only [sampledPair]
  rw [query_after_first cfg s _ hs ht, paired_update cfg s _ _ hs ht]
  simp only [query, hs, Bool.false_eq_true, ↓reduceIte]

noncomputable def partialBlockState (cfg : Config) (g : E → Ω → E) (s : State cfg E)
    (ξ : ℕ → Ω) (offset n : ℕ) : State cfg E :=
  { s with
    sampleIndex := n
    second := false
    secondPoint := 0
    left := prefixValues (fun i => g (points cfg s).1 (ξ (offset + i))) n
    right := prefixValues (fun i => g (points cfg s).2 (ξ (offset + i))) n }

omit [InnerProductSpace ℝ E] in
lemma partialBlockState_zero (cfg : Config) (g : E → Ω → E) (s : State cfg E)
    (ξ : ℕ → Ω) (offset : ℕ) (hn : s.sampleIndex = 0) (hs : s.second = false)
    (hp : s.secondPoint = 0) (hl : s.left = fun _ => 0) (hr : s.right = fun _ => 0) :
    partialBlockState cfg g s ξ offset 0 = s := by
  cases s
  simp_all [partialBlockState, prefixValues_zero]

lemma partialBlockState_step (cfg : Config) (g : E → Ω → E) (s : State cfg E)
    (ξ : ℕ → Ω) (offset n : ℕ) (ht : s.t < cfg.T) (hn : n + 1 ≤ cfg.m) :
    sampledPair cfg g (ξ (offset + n)) (partialBlockState cfg g s ξ offset n) =
      if n + 1 < cfg.m then partialBlockState cfg g s ξ offset (n + 1)
      else commitObservation cfg s
        (blockObservation cfg g s.t s.point s.previous (fun i => ξ (offset + i))) := by
  rw [sampledPair_eq cfg g (ξ (offset + n)) (partialBlockState cfg g s ξ offset n) rfl
    (show (partialBlockState cfg g s ξ offset n).t < cfg.T from ht)]
  dsimp only [partialBlockState, points]
  simp only [prefixValues_update]
  by_cases h : n + 1 < cfg.m
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    have he : n + 1 = cfg.m := by omega
    have hl : (fun i : Fin cfg.m => prefixValues (fun j => g s.point (ξ (offset + j))) (n + 1) i) =
        fun i : Fin cfg.m => g s.point (ξ (offset + i)) := by
      funext i
      simp only [prefixValues, he, i.isLt, ite_true]
    have hr : (fun i : Fin cfg.m => prefixValues
        (fun j => g (if cfg.isRefresh s.t then s.point else s.previous) (ξ (offset + j))) (n + 1) i) =
        fun i : Fin cfg.m => g (if cfg.isRefresh s.t then s.point else s.previous) (ξ (offset + i)) := by
      funext i
      simp only [prefixValues, he, i.isLt, ite_true]
    simp only [finishBlock, hl, hr]
    rw [commitObservation_buffers]
    congr 1
    unfold blockObservation
    split_ifs <;> rfl

noncomputable def sampledPairs (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (offset : ℕ) (s : State cfg E) : ℕ → State cfg E
  | 0 => s
  | n + 1 => sampledPair cfg g (ξ (offset + n)) (sampledPairs cfg g ξ offset s n)

lemma sampledPairs_partial (cfg : Config) (g : E → Ω → E) (s : State cfg E)
    (ξ : ℕ → Ω) (offset n : ℕ) (ht : s.t < cfg.T)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (hp : s.secondPoint = 0)
    (hl : s.left = fun _ => 0) (hr : s.right = fun _ => 0) (hsize : n < cfg.m) :
    sampledPairs cfg g ξ offset s n = partialBlockState cfg g s ξ offset n := by
  induction n with
  | zero => exact (partialBlockState_zero cfg g s ξ offset hn hs hp hl hr).symm
  | succ n ih =>
    rw [sampledPairs, ih (by omega), partialBlockState_step cfg g s ξ offset n ht (by omega)]
    exact ite_eq_left hsize

lemma sampledPairs_block (cfg : Config) (hm : 0 < cfg.m) (g : E → Ω → E) (s : State cfg E)
    (ξ : ℕ → Ω) (offset : ℕ) (ht : s.t < cfg.T)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (hp : s.secondPoint = 0)
    (hl : s.left = fun _ => 0) (hr : s.right = fun _ => 0) :
    sampledPairs cfg g ξ offset s cfg.m = commitObservation cfg s
      (blockObservation cfg g s.t s.point s.previous (fun i => ξ (offset + i))) := by
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  conv_lhs => rw [he]
  rw [sampledPairs, sampledPairs_partial cfg g s ξ offset n ht hn hs hp hl hr (by omega),
    partialBlockState_step cfg g s ξ offset n ht (by omega)]
  simp only [he, lt_self_iff_false, ite_false]

noncomputable def indexedStep (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (sc : State cfg E × ℕ) : State cfg E × ℕ :=
  (update cfg sc.1 (g (query cfg sc.1) (ξ (sc.2 / 2))), sc.2 + 1)

lemma indexedStep_pair (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (s : State cfg E) (offset : ℕ) :
    (indexedStep cfg g ξ)^[2] (s, 2 * offset) =
      (sampledPair cfg g (ξ offset) s, 2 * (offset + 1)) := by
  have h0 : 2 * offset / 2 = offset := by omega
  have h1 : (2 * offset + 1) / 2 = offset := by omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, indexedStep, h0, h1, sampledPair]
  congr 1

lemma indexedStep_pairs (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (s : State cfg E) (offset n : ℕ) :
    (indexedStep cfg g ξ)^[2 * n] (s, 2 * offset) =
      (sampledPairs cfg g ξ offset s n, 2 * (offset + n)) := by
  induction n with
  | zero => simp [sampledPairs]
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2 * n) 2, Function.iterate_add_apply, ih, indexedStep_pair]
    simp only [sampledPairs, Nat.add_assoc]

lemma indexedStep_block (cfg : Config) (hm : 0 < cfg.m) (g : E → Ω → E) (s : State cfg E)
    (ξ : ℕ → Ω) (offset : ℕ) (ht : s.t < cfg.T)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (hp : s.secondPoint = 0)
    (hl : s.left = fun _ => 0) (hr : s.right = fun _ => 0) :
    (indexedStep cfg g ξ)^[2 * cfg.m] (s, 2 * offset) =
      (commitObservation cfg s (blockObservation cfg g s.t s.point s.previous
        (fun i => ξ (offset + i))), 2 * (offset + cfg.m)) := by
  rw [indexedStep_pairs, sampledPairs_block cfg hm g s ξ offset ht hn hs hp hl hr]

noncomputable def partialBatchState (cfg : Config) (s : State cfg E) (v : ℕ → E)
    (j : ℕ) : State cfg E :=
  { s with
    blockIndex := j
    accumulator := ∑ i ∈ Finset.range j, v i }

omit [InnerProductSpace ℝ E] in
lemma partialBatchState_zero (cfg : Config) (s : State cfg E) (v : ℕ → E)
    (hj : s.blockIndex = 0) (ha : s.accumulator = 0) :
    partialBatchState cfg s v 0 = s := by
  cases s
  simp_all [partialBatchState]

noncomputable def completedBatchState (cfg : Config) (s : State cfg E) (v : ℕ → E) : State cfg E :=
  let est := (cfg.batch s.t : ℝ)⁻¹ • (∑ i ∈ Finset.range (cfg.batch s.t), v i) +
    if cfg.isRefresh s.t then 0 else s.estimate
  { s with
    t := s.t + 1
    blockIndex := 0
    sampleIndex := 0
    second := false
    secondPoint := 0
    left := fun _ => 0
    right := fun _ => 0
    accumulator := 0
    point := NormalizedStorm.stormStep cfg.η s.point est
    previous := s.point
    estimate := est
    selected := if s.t = s.outputIndex.val then s.point else s.selected }

lemma partialBatchState_step (cfg : Config) (s : State cfg E) (v : ℕ → E) (j : ℕ)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (hp : s.secondPoint = 0)
    (hl : s.left = fun _ => 0) (hr : s.right = fun _ => 0)
    (hj : j + 1 ≤ cfg.batch s.t) :
    commitObservation cfg (partialBatchState cfg s v j) (v j) =
      if j + 1 < cfg.batch s.t then partialBatchState cfg s v (j + 1)
      else completedBatchState cfg s v := by
  by_cases h : j + 1 < cfg.batch s.t
  · simp [commitObservation, partialBatchState, h, Finset.sum_range_succ, hn, hs, hp, hl, hr]
  · have he : j + 1 = cfg.batch s.t := by omega
    simp only [commitObservation, partialBatchState, completedBatchState]
    simp only [← he, Finset.sum_range_succ, lt_self_iff_false, ite_false]
    rfl

lemma indexedStep_partial_batch (cfg : Config) (hm : 0 < cfg.m) (g : E → Ω → E)
    (s : State cfg E) (ξ : ℕ → Ω) (offset j : ℕ) (ht : s.t < cfg.T)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (hp : s.secondPoint = 0)
    (hl : s.left = fun _ => 0) (hr : s.right = fun _ => 0)
    (hj : s.blockIndex = 0) (ha : s.accumulator = 0) (hsize : j < cfg.batch s.t) :
    (indexedStep cfg g ξ)^[2 * cfg.m * j] (s, 2 * offset) =
      (partialBatchState cfg s (fun i => blockObservation cfg g s.t s.point s.previous
        (fun l => ξ (offset + cfg.m * i + l))) j, 2 * (offset + cfg.m * j)) := by
  induction j with
  | zero => simp [partialBatchState_zero cfg s _ hj ha]
  | succ j ih =>
    rw [Nat.mul_succ, Nat.add_comm (2 * cfg.m * j) (2 * cfg.m), Function.iterate_add_apply,
      ih (by omega)]
    rw [indexedStep_block cfg hm g (partialBatchState cfg s
      (fun i => blockObservation cfg g s.t s.point s.previous
        (fun l => ξ (offset + cfg.m * i + l))) j) ξ (offset + cfg.m * j)
      (show (partialBatchState cfg s _ j).t < cfg.T from ht)
      (show (partialBatchState cfg s _ j).sampleIndex = 0 from hn)
      (show (partialBatchState cfg s _ j).second = false from hs)
      (show (partialBatchState cfg s _ j).secondPoint = 0 from hp)
      (show (partialBatchState cfg s _ j).left = _ from hl)
      (show (partialBatchState cfg s _ j).right = _ from hr)]
    have hstep := partialBatchState_step cfg s
      (fun i => blockObservation cfg g s.t s.point s.previous
        (fun l => ξ (offset + cfg.m * i + l))) j hn hs hp hl hr (by omega)
    dsimp only [partialBatchState] at hstep ⊢
    rw [hstep]
    simp only [hsize, ite_true, Nat.mul_succ, Nat.add_assoc]

lemma indexedStep_batch (cfg : Config) (hm : 0 < cfg.m) (g : E → Ω → E)
    (s : State cfg E) (ξ : ℕ → Ω) (offset : ℕ) (ht : s.t < cfg.T)
    (hn : s.sampleIndex = 0) (hs : s.second = false) (hp : s.secondPoint = 0)
    (hl : s.left = fun _ => 0) (hr : s.right = fun _ => 0)
    (hj : s.blockIndex = 0) (ha : s.accumulator = 0) (hb : 0 < cfg.batch s.t) :
    (indexedStep cfg g ξ)^[2 * cfg.m * cfg.batch s.t] (s, 2 * offset) =
      (completedBatchState cfg s (fun i => blockObservation cfg g s.t s.point s.previous
        (fun l => ξ (offset + cfg.m * i + l))), 2 * (offset + cfg.m * cfg.batch s.t)) := by
  obtain ⟨j, he⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  conv_lhs => rw [he]
  rw [Nat.mul_succ, Nat.add_comm (2 * cfg.m * j) (2 * cfg.m), Function.iterate_add_apply,
    indexedStep_partial_batch cfg hm g s ξ offset j ht hn hs hp hl hr hj ha (by omega)]
  rw [indexedStep_block cfg hm g (partialBatchState cfg s
      (fun i => blockObservation cfg g s.t s.point s.previous
        (fun l => ξ (offset + cfg.m * i + l))) j) ξ (offset + cfg.m * j)
      (show (partialBatchState cfg s _ j).t < cfg.T from ht)
      (show (partialBatchState cfg s _ j).sampleIndex = 0 from hn)
      (show (partialBatchState cfg s _ j).second = false from hs)
      (show (partialBatchState cfg s _ j).secondPoint = 0 from hp)
      (show (partialBatchState cfg s _ j).left = _ from hl)
      (show (partialBatchState cfg s _ j).right = _ from hr)]
  have hstep := partialBatchState_step cfg s
      (fun i => blockObservation cfg g s.t s.point s.previous
        (fun l => ξ (offset + cfg.m * i + l))) j hn hs hp hl hr (by omega)
  dsimp only [partialBatchState] at hstep ⊢
  rw [hstep]
  simp only [he, lt_self_iff_false, ite_false, Nat.mul_succ, Nat.add_assoc]

noncomputable def iterationState (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Fin cfg.m → Ω) (τ : Fin (max 1 cfg.T)) (t : ℕ) : State cfg E :=
  { outputIndex := τ
    t := t
    blockIndex := 0
    sampleIndex := 0
    second := false
    secondPoint := 0
    left := fun _ => 0
    right := fun _ => 0
    accumulator := 0
    point := (trajectory cfg g x0 ξ t).1
    previous := (trajectory cfg g x0 ξ t).2.1
    estimate := (trajectory cfg g x0 ξ t).2.2
    selected := if τ.val < t then (trajectory cfg g x0 ξ τ.val).1 else x0 }

lemma iterationState_zero (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Fin cfg.m → Ω) (τ : Fin (max 1 cfg.T)) :
    iterationState cfg g x0 ξ τ 0 = (algorithm cfg x0).initial τ := by
  simp [iterationState, trajectory, algorithm]

lemma completedBatchState_iteration (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Fin cfg.m → Ω) (τ : Fin (max 1 cfg.T)) (t : ℕ) :
    completedBatchState cfg (iterationState cfg g x0 ξ τ t)
      (fun i => blockObservation cfg g t (trajectory cfg g x0 ξ t).1
        (trajectory cfg g x0 ξ t).2.1 (ξ (cfg.blockOffset t + i))) =
      iterationState cfg g x0 ξ τ (t + 1) := by
  have he : (if t = τ.val then (trajectory cfg g x0 ξ t).1
      else if τ.val < t then (trajectory cfg g x0 ξ τ.val).1 else x0) =
      if τ.val < t + 1 then (trajectory cfg g x0 ξ τ.val).1 else x0 := by
    split_ifs with h h' h'' <;> first | subst t; rfl | omega | rfl
  dsimp only [completedBatchState, iterationState, trajectory, batchObservation]
  congr 1

lemma indexedStep_iterations (cfg : Config) (hm : 0 < cfg.m)
    (hb : ∀ t, 0 < cfg.batch t) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω)
    (τ : Fin (max 1 cfg.T)) : ∀ t, t ≤ cfg.T →
    (indexedStep cfg g ξ)^[2 * cfg.m * cfg.blockOffset t] ((algorithm cfg x0).initial τ, 0) =
      (iterationState cfg g x0 (fun j i => ξ (cfg.m * j + i)) τ t,
        2 * (cfg.m * cfg.blockOffset t))
  | 0, _ => by simp [blockOffset_zero, iterationState_zero]
  | t + 1, ht => by
      rw [blockOffset_succ, Nat.mul_add, Nat.add_comm, Function.iterate_add_apply,
        indexedStep_iterations cfg hm hb g x0 ξ τ t (by omega)]
      have hbatch := indexedStep_batch cfg hm g
        (iterationState cfg g x0 (fun j i => ξ (cfg.m * j + i)) τ t) ξ
        (cfg.m * cfg.blockOffset t) (show t < cfg.T from by omega)
        rfl rfl rfl rfl rfl rfl rfl (hb t)
      change (indexedStep cfg g ξ)^[2 * cfg.m * cfg.batch t]
        (iterationState cfg g x0 (fun j i => ξ (cfg.m * j + i)) τ t,
          2 * (cfg.m * cfg.blockOffset t)) = _ at hbatch
      rw [hbatch]
      have he : (fun j => blockObservation cfg g t
          (trajectory cfg g x0 (fun j i => ξ (cfg.m * j + i)) t).1
          (trajectory cfg g x0 (fun j i => ξ (cfg.m * j + i)) t).2.1
          (fun i => ξ (cfg.m * cfg.blockOffset t + cfg.m * j + i))) =
          (fun j => blockObservation cfg g t
          (trajectory cfg g x0 (fun j i => ξ (cfg.m * j + i)) t).1
          (trajectory cfg g x0 (fun j i => ξ (cfg.m * j + i)) t).2.1
          (fun i => ξ (cfg.m * (cfg.blockOffset t + j) + i))) := by
        simp only [Nat.mul_add]
      change (completedBatchState cfg
        (iterationState cfg g x0 (fun j i => ξ (cfg.m * j + i)) τ t)
        (fun j => blockObservation cfg g t
          (trajectory cfg g x0 (fun j i => ξ (cfg.m * j + i)) t).1
          (trajectory cfg g x0 (fun j i => ξ (cfg.m * j + i)) t).2.1
          (fun i => ξ (cfg.m * cfg.blockOffset t + cfg.m * j + i))),
          2 * (cfg.m * cfg.blockOffset t + cfg.m * cfg.batch t)) = _
      rw [he, completedBatchState_iteration]
      simp only [Nat.mul_add]

lemma calls_eq (cfg : Config) : cfg.calls = 2 * cfg.m * cfg.blockOffset cfg.T := by
  simp only [Config.calls, Config.blockOffset, Finset.mul_sum]

lemma indexedStep_finished (cfg : Config) (hm : 0 < cfg.m) (hT : 0 < cfg.T)
    (hb : ∀ t, 0 < cfg.batch t) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω)
    (τ : Fin (max 1 cfg.T)) :
    output cfg ((indexedStep cfg g ξ)^[cfg.calls] ((algorithm cfg x0).initial τ, 0)).1 =
      (trajectory cfg g x0 (fun j i => ξ (cfg.m * j + i)) τ.val).1 := by
  rw [calls_eq, indexedStep_iterations cfg hm hb g x0 ξ τ cfg.T le_rfl]
  have hτ : τ.val < cfg.T := by have := τ.isLt; omega
  simp only [output, iterationState, hτ, ite_true]

lemma indexedStep_frozen (cfg : Config) (g : E → Ω → E) (ξ : ℕ → Ω)
    (s : State cfg E) (hs : cfg.T ≤ s.t) (c n : ℕ) :
    ((indexedStep cfg g ξ)^[n] (s, c)).1 = s := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [indexedStep, frozen_update cfg s _ hs]
    exact ih (c + 1)

lemma execute_trajectory (cfg : Config) (hm : 0 < cfg.m) (hT : 0 < cfg.T)
    (hb : ∀ t, 0 < cfg.batch t) (g : E → Ω → E) (x0 : E)
    (O : Oracle E E) (τ : Fin (max 1 cfg.T))
    (ξ : (k : ℕ) → O.Seed k) (ζ : ℕ → Ω)
    (hanswer : ∀ history x, O.answer history (0, x) (ξ history.length) =
      g x (ζ (history.length / 2))) (K : ℕ) (hK : cfg.calls ≤ K) :
    execute O (algorithm cfg x0) (fun _ => K) τ ξ =
      (trajectory cfg g x0 (fun j i => ζ (cfg.m * j + i)) τ.val).1 := by
  have hans : ∀ history query, O.answer history query (ξ history.length) =
      g query.2 (ζ (history.length / 2)) := by
    intro history query
    have hi : query.1 = 0 := Subsingleton.elim _ _
    simpa only [← hi] using hanswer history query.2
  erw [execute_indexed_of_answer O _ _ _ ξ (fun k query => g query.2 (ζ (k / 2))) hans]
  change output cfg ((indexedStep cfg g ζ)^[K] ((algorithm cfg x0).initial τ, 0)).1 = _
  rw [show K = (K - cfg.calls) + cfg.calls by omega, Function.iterate_add_apply,
    calls_eq, indexedStep_iterations cfg hm hb g x0 ζ τ cfg.T le_rfl,
    indexedStep_frozen cfg g ζ _ (by rfl)]
  have hτ : τ.val < cfg.T := by have := τ.isLt; omega
  simp only [output, iterationState, hτ, ite_true]

end OracleTemplate.FairVarianceReduction
