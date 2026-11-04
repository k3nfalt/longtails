import LongTails.Proofs.HystereticHessianPhases
import LongTails.Proofs.HystereticHessianMoments
import LongTails.Proofs.HeavyTailedSospEpochIntegration
import LongTails.Proofs.GuardedHessianExecution

namespace LongTails.Proofs.HystereticHessianBlocks

open OracleTemplate.StochasticGeneralized
open HeavyTailedProductProcess

def finiteRun {S Ω : Type*} (step : S → Ω → S) : (n : ℕ) → S → (Fin n → Ω) → S
  | 0, s, _ => s
  | n + 1, s, ξ => finiteRun step n (step s (ξ 0)) (fun i => ξ i.succ)

lemma finiteRun_eq_trajectory {S Ω : Type*} (step : S → Ω → S)
    (n : ℕ) (s : S) (ξ : ℕ → Ω) :
    finiteRun step n s (fun i => ξ i) = trajectory step n s ξ := by
  induction n generalizing s ξ with
  | zero => rfl
  | succ n ih =>
    simpa only [finiteRun, trajectory, Fin.val_zero, Fin.val_succ] using
      ih (step s (ξ 0)) (fun k => ξ (k + 1))

lemma blockTrace_eq_trajectory {S Ω : Type*} (step : S → Ω → S) (cost : S → ℕ)
    (s : S) (ξ : ℕ → Ω) (k : ℕ) :
    (blockTrace cost (finiteRun step) s ξ k).1 =
      trajectory step (blockCalls cost (finiteRun step) s ξ k) s ξ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [blockTrace_succ, blockCalls_succ]
    change finiteRun step (cost (blockTrace cost (finiteRun step) s ξ k).1)
      (blockTrace cost (finiteRun step) s ξ k).1
      (fun i => (blockTrace cost (finiteRun step) s ξ k).2 i) = _
    simp_rw [blockTrace_tail]
    rw [finiteRun_eq_trajectory step _ _ (fun i => ξ (blockCalls cost (finiteRun step) s ξ k + i)),
      HeavyTailedSospEpochIntegration.trajectory_add, ih]

lemma finiteRun_map {S T Ω : Type*} (step : S → Ω → S) (step' : T → Ω → T)
    (F : S → T) (hF : ∀ s z, F (step s z) = step' (F s) z)
    (n : ℕ) (s : S) (ξ : Fin n → Ω) :
    F (finiteRun step n s ξ) = finiteRun step' n (F s) ξ := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [finiteRun, ih, hF]

lemma blockTrace_map {S T Ω : Type*} (step : S → Ω → S) (step' : T → Ω → T)
    (F : S → T) (hF : ∀ s z, F (step s z) = step' (F s) z) (cost : T → ℕ)
    (s : S) (ξ : ℕ → Ω) (k : ℕ) :
    let t := blockTrace (fun s => cost (F s)) (finiteRun step) s ξ k
    (F t.1, t.2) = blockTrace cost (finiteRun step') (F s) ξ k := by
  dsimp only
  induction k generalizing s ξ with
  | zero => rfl
  | succ k ih =>
    rw [blockTrace_start_succ, blockTrace_start_succ, ih, finiteRun_map step step' F hF]

lemma finiteRun_measurable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (step : S → Ω → S) (hs : Measurable (Function.uncurry step)) (n : ℕ) :
    Measurable (Function.uncurry (finiteRun step n)) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact ih.comp ((hs.comp (measurable_fst.prodMk
      ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (measurable_pi_iff.mpr (fun i : Fin n =>
          (measurable_pi_apply i.succ).comp measurable_snd)))

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianPhases HystereticHessianMoments

def phaseCalls (p : Params) (c : Config) (s : State p c) : ℕ :=
  if s.active then
    match s.phase with
    | .gradient refresh j i _ _ =>
        batchRemaining (if refresh then c.resetBatch else c.pilotBatch) c.groups j.val i
    | .transport i _ => c.transportBatch + 1 - i
    | .padding => macroCalls c - s.slot
  else macroCalls c - s.slot

lemma phaseCalls_pos (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) : 0 < phaseCalls p c s := by
  have hslot := hf.1
  cases ha : s.active with
  | false => simp only [phaseCalls, ha, Bool.false_eq_true, ite_false]; omega
  | true =>
    cases he : s.phase with
    | padding => simp only [phaseCalls, ha, ite_true, he]; omega
    | transport i sum =>
      have hh : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [he] using hc.2
      simp only [phaseCalls, ha, ite_true, he]
      omega
    | gradient refresh j i sum values =>
      have hh : s.inner ≤ c.epoch ∧ i ≤ if refresh then c.resetBatch else c.pilotBatch := by
        simpa [he] using hc.2
      simp only [phaseCalls, ha, ite_true, he, batchRemaining]
      omega

lemma phaseCalls_le_work (p : Params) (c : Config) (s : State p c)
    (ha : s.active = true) (hp : s.phase ≠ .padding) :
    phaseCalls p c s ≤ remainingWork p c s := by
  cases he : s.phase with
  | padding => exact (hp he).elim
  | transport i sum => simp [phaseCalls, remainingWork, ha, he]
  | gradient refresh j i sum values => simp [phaseCalls, remainingWork, ha, he]; omega

lemma phaseCalls_fit (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) :
    s.slot + phaseCalls p c s ≤ macroCalls c := by
  have hslot := hf.1
  by_cases ha : s.active = true
  · by_cases hp : s.phase = .padding
    · simp only [phaseCalls, ha, ite_true, hp]
      omega
    · have hw := work_pos p c s hc ha hp
      have hr := hf.2 hw
      have hh := phaseCalls_le_work p c s ha hp
      omega
  · have haf : s.active = false := Bool.eq_false_iff.mpr ha
    simp only [phaseCalls, haf, Bool.false_eq_true, ite_false]
    omega

noncomputable def finishGradient (p : Params) (c : Config) (refresh : Bool)
    (s : State p c) (values : Fin (c.groups + 1) → Space p) : State p c :=
  if refresh then beginFineStep p c
    { s with estimate := OracleTemplate.MultiplicativeRobustEstimator.medoid values }
  else finishPilot p c s (OracleTemplate.MultiplicativeRobustEstimator.medoid values)

lemma finishGradient_phase (p : Params) (c : Config) (refresh : Bool)
    (s : State p c) (values : Fin (c.groups + 1) → Space p) (ph : Phase p c) :
    finishGradient p c refresh { s with phase := ph } values =
      finishGradient p c refresh s values := by
  unfold finishGradient finishPilot beginFineStep
  split_ifs <;> rfl

lemma finishGradient_slot (p : Params) (c : Config) (refresh : Bool)
    (s : State p c) (values : Fin (c.groups + 1) → Space p) (slot : ℕ) :
    { finishGradient p c refresh s values with slot := slot } =
      finishGradient p c refresh { s with slot := slot } values := by
  unfold finishGradient finishPilot beginFineStep
  split_ifs <;> rfl

lemma gradient_prefix (p : Params) (c : Config) (s : State p c)
    (refresh : Bool) (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) (ha : s.active = true)
    (hn : n ≤ if refresh then c.resetBatch else c.pilotBatch)
    (ht : s.slot + n < macroCalls c) :
    path p c answer { s with phase := .gradient refresh j 0 0 values } ξ n =
      { s with
        slot := s.slot + n
        phase := .gradient refresh j n
          (∑ k ∈ Finset.range n, answer (s.point, none) (ξ k).2) values } := by
  induction n with
  | zero => simp [path, trajectory]
  | succ n ih =>
    have hi : n < if refresh then c.resetBatch else c.pilotBatch := by omega
    have hclock : s.slot + n + 1 < macroCalls c := by omega
    rw [path, trajectory_succ_last]
    change update p c (path p c answer _ ξ n) (ξ n).1
      (answer (query p c (path p c answer _ ξ n) (ξ n).1) (ξ n).2) = _
    simp only [ih (by omega) (by omega)]
    simp only [update, rawUpdate, query, ha, ite_true, hi, hclock, Finset.sum_range_succ]
    rfl

lemma gradient_group (p : Params) (c : Config) (s : State p c)
    (refresh : Bool) (j : Fin (c.groups + 1)) (values : Fin (c.groups + 1) → Space p)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + ((if refresh then c.resetBatch else c.pilotBatch) + 1) < macroCalls c) :
    path p c answer { s with phase := .gradient refresh j 0 0 values } ξ
      ((if refresh then c.resetBatch else c.pilotBatch) + 1) =
      let b := if refresh then c.resetBatch else c.pilotBatch
      let values' := Function.update values j
        (((b + 1 : ℕ) : ℝ)⁻¹ •
          ∑ k ∈ Finset.range (b + 1), answer (s.point, none) (ξ k).2)
      if hj : j.val + 1 < c.groups + 1 then
        { s with
          slot := s.slot + (b + 1)
          phase := .gradient refresh ⟨j.val + 1, hj⟩ 0 0 values' }
      else finishGradient p c refresh { s with slot := s.slot + (b + 1) } values' := by
  let b := if refresh then c.resetBatch else c.pilotBatch
  have hclock : s.slot + b + 1 < macroCalls c := by simpa [Nat.add_assoc] using ht
  rw [path, trajectory_succ_last]
  change update p c (path p c answer _ ξ b) (ξ b).1
    (answer (query p c (path p c answer _ ξ b) (ξ b).1) (ξ b).2) = _
  simp only [gradient_prefix p c s refresh j values answer ξ b ha le_rfl (by omega)]
  simp only [update, rawUpdate, query, ha, ite_true, b, lt_self_iff_false, ite_false,
    hclock, Finset.sum_range_succ]
  by_cases hj : j.val + 1 < c.groups + 1
  · simp only [hj, dite_true]
    rfl
  · simp only [hj, dite_false]
    unfold finishGradient finishPilot beginFineStep
    split_ifs <;> simp_all [b, fineDisplacement, Nat.add_assoc]


lemma path_add (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (m n : ℕ) :
    path p c answer s ξ (m + n) =
      path p c answer (path p c answer s ξ m) (fun k => ξ (m + k)) n :=
  HeavyTailedSospEpochIntegration.trajectory_add _ _ _ _ _

lemma gradient_groups_prefix (p : Params) (c : Config) (s : State p c)
    (refresh : Bool) {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (j : ℕ) (hj : j ≤ c.groups) (ha : s.active = true)
    (ht : s.slot + j * ((if refresh then c.resetBatch else c.pilotBatch) + 1) < macroCalls c) :
    path p c answer { s with phase := .gradient refresh 0 0 0 (fun _ => 0) } ξ
      (j * ((if refresh then c.resetBatch else c.pilotBatch) + 1)) =
      { s with
        slot := s.slot + j * ((if refresh then c.resetBatch else c.pilotBatch) + 1)
        phase := .gradient refresh ⟨j, by omega⟩ 0 0
          (fun k => if k.val < j then
            (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
              ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
                answer (s.point, none)
                  (ξ (k.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2
            else 0) } := by
  let b := if refresh then c.resetBatch else c.pilotBatch
  induction j with
  | zero => simp [path, trajectory]
  | succ j ih =>
    have htime : s.slot + j * (b + 1) + (b + 1) < macroCalls c := by
      simpa only [Nat.succ_mul, Nat.add_assoc] using ht
    have hbefore : s.slot + j * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
        macroCalls c := lt_of_le_of_lt (Nat.le_add_right _ _) htime
    rw [Nat.succ_mul, path_add, ih (by omega) hbefore]
    rw [gradient_group p c { s with slot := s.slot + j * (b + 1) } refresh
      ⟨j, by omega⟩ _ answer _ ha htime]
    simp only [show j + 1 < c.groups + 1 by omega, dite_true]
    rw [GuardedHessianExecution.prefix_values_update]
    simp only [b, Nat.add_assoc]

lemma gradient_pass (p : Params) (c : Config) (s : State p c)
    (refresh : Bool) {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
      macroCalls c) :
    path p c answer { s with phase := .gradient refresh 0 0 0 (fun _ => 0) } ξ
      ((c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1)) =
      finishGradient p c refresh
        { s with slot := s.slot + (c.groups + 1) *
          ((if refresh then c.resetBatch else c.pilotBatch) + 1) }
        (fun j => (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
          ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
            answer (s.point, none)
              (ξ (j.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2) := by
  let b := if refresh then c.resetBatch else c.pilotBatch
  have htime : s.slot + c.groups * (b + 1) + (b + 1) < macroCalls c := by
    simpa only [Nat.succ_mul, Nat.add_assoc] using ht
  have hbefore : s.slot + c.groups * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
      macroCalls c := lt_of_le_of_lt (Nat.le_add_right _ _) htime
  rw [Nat.succ_mul, path_add, gradient_groups_prefix p c s refresh answer ξ _ le_rfl ha hbefore]
  rw [gradient_group p c { s with slot := s.slot + c.groups * (b + 1) } refresh
    ⟨c.groups, by omega⟩ _ answer _ ha htime]
  simp only [lt_self_iff_false, dite_false]
  rw [GuardedHessianExecution.prefix_values_update]
  simp only [Fin.is_lt, ite_true, b, Nat.add_assoc]

lemma transport_prefix (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) (ha : s.active = true)
    (hn : n ≤ c.transportBatch) (ht : s.slot + n < macroCalls c) :
    path p c answer { s with phase := .transport 0 0 } ξ n =
      { s with
        slot := s.slot + n
        phase := .transport n (∑ k ∈ Finset.range n,
          OracleTemplate.clip c.clipThreshold
            (answer (s.point + (ξ k).1 • s.move, some s.move) (ξ k).2)) } := by
  induction n with
  | zero => simp [path, trajectory]
  | succ n ih =>
    have hi : n < c.transportBatch := by omega
    have hclock : s.slot + n + 1 < macroCalls c := by omega
    rw [path, trajectory_succ_last]
    change update p c (path p c answer _ ξ n) (ξ n).1
      (answer (query p c (path p c answer _ ξ n) (ξ n).1) (ξ n).2) = _
    simp only [ih (by omega) (by omega)]
    simp only [update, rawUpdate, query, ha, ite_true, hi, hclock, Finset.sum_range_succ]
    rfl

lemma transport_pass (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.transportBatch + 1) < macroCalls c) :
    path p c answer { s with phase := .transport 0 0 } ξ (c.transportBatch + 1) =
      { s with
        point := s.point + s.move
        estimate := s.estimate + ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ •
          ∑ k ∈ Finset.range (c.transportBatch + 1),
            OracleTemplate.clip c.clipThreshold
              (answer (s.point + (ξ k).1 • s.move, some s.move) (ξ k).2)
        inner := s.inner + 1
        slot := s.slot + (c.transportBatch + 1)
        phase := if s.inner < c.epoch then .gradient false 0 0 0 (fun _ => 0) else .padding } := by
  have hclock : s.slot + c.transportBatch + 1 < macroCalls c := by omega
  rw [path, trajectory_succ_last]
  change update p c (path p c answer _ ξ c.transportBatch) (ξ c.transportBatch).1
    (answer (query p c (path p c answer _ ξ c.transportBatch) (ξ c.transportBatch).1)
      (ξ c.transportBatch).2) = _
  simp only [transport_prefix p c s answer ξ c.transportBatch ha le_rfl (by omega)]
  simp only [update, rawUpdate, query, ha, ite_true, lt_self_iff_false, ite_false,
    hclock, Finset.sum_range_succ]
  rfl

def Fresh (p : Params) (c : Config) (s : State p c) : Prop :=
  s.active = true → match s.phase with
    | .gradient _ j i sum values => j.val = 0 ∧ i = 0 ∧ sum = 0 ∧ values = fun _ => 0
    | .transport i sum => i = 0 ∧ sum = 0
    | .padding => True

lemma initial_fresh (p : Params) (c : Config) : Fresh p c (initial p c) := by
  simp [Fresh, initial]

lemma beginFineStep_fresh (p : Params) (c : Config) (s : State p c) :
    Fresh p c (beginFineStep p c s) := by
  unfold beginFineStep
  split_ifs <;> simp [Fresh]

lemma finishPilot_fresh (p : Params) (c : Config) (s : State p c) (v : Space p) :
    Fresh p c (finishPilot p c s v) := by
  unfold finishPilot
  split_ifs
  all_goals first | exact beginFineStep_fresh p c s | simp [Fresh]

lemma finishGradient_fresh (p : Params) (c : Config) (refresh : Bool)
    (s : State p c) (values : Fin (c.groups + 1) → Space p) :
    Fresh p c (finishGradient p c refresh s values) := by
  unfold finishGradient
  split_ifs
  · exact beginFineStep_fresh p c _
  · exact finishPilot_fresh p c _ _

lemma padding_prefix (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) (hp : s.active = false ∨ s.phase = .padding)
    (ht : s.slot + n < macroCalls c) :
    path p c answer s ξ n = { s with slot := s.slot + n } := by
  induction n with
  | zero => simp [path, trajectory]
  | succ n ih =>
    rw [path, trajectory_succ_last]
    change update p c (path p c answer s ξ n) (ξ n).1
      (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2) = _
    simp only [ih (by omega)]
    rcases hp with ha | hp
    · simp [update, rawUpdate, ha, ht, Nat.add_assoc]
    · simp [update, rawUpdate, hp, ht, Nat.add_assoc]

lemma padding_pass (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hp : s.active = false ∨ s.phase = .padding)
    (ht : s.slot < macroCalls c) :
    path p c answer s ξ (macroCalls c - s.slot) =
      { s with slot := 0, inner := 0, phase := .gradient false 0 0 0 (fun _ => 0) } := by
  let n := macroCalls c - s.slot - 1
  have he : macroCalls c - s.slot = n + 1 := by omega
  have hclock : ¬s.slot + n + 1 < macroCalls c := by omega
  rw [he, path, trajectory_succ_last]
  change update p c (path p c answer s ξ n) (ξ n).1
    (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2) = _
  simp only [padding_prefix p c s answer ξ n hp (by omega)]
  rcases hp with ha | hp
  · simp [update, rawUpdate, ha, hclock]
  · simp [update, rawUpdate, hp, hclock]

lemma phaseCalls_strict_fit (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (ha : s.active = true) (hp : s.phase ≠ .padding) :
    s.slot + phaseCalls p c s < macroCalls c := by
  have hpos := work_pos p c s hc ha hp
  have hr := hf.2 hpos
  have hle := phaseCalls_le_work p c s ha hp
  have hpilot := pilotCalls_pos c
  omega

lemma phase_preserves_fresh (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (hfr : Fresh p c s) : Fresh p c (path p c answer s ξ (phaseCalls p c s)) := by
  by_cases ha : s.active = true
  · cases hp : s.phase with
    | padding =>
      simp only [phaseCalls, ha, ite_true, hp]
      rw [padding_pass p c s answer ξ (Or.inr hp) hf.1]
      simp [Fresh]
    | gradient refresh j i sum values =>
      have hh : j.val = 0 ∧ i = 0 ∧ sum = 0 ∧ values = fun _ => 0 := by
        simpa only [hp] using hfr ha
      have hj : j = 0 := Fin.ext hh.1
      subst j
      rcases hh with ⟨_, rfl, rfl, rfl⟩
      have ht := phaseCalls_strict_fit p c s hc hf ha (by simp [hp])
      simp only [phaseCalls, ha, ite_true, hp, Fin.val_zero, batchRemaining_initial] at ht ⊢
      have hout := gradient_pass p c s refresh answer ξ ha ht
      rw [← hp] at hout
      rw [hout]
      exact finishGradient_fresh p c refresh _ _
    | transport i sum =>
      have hh : i = 0 ∧ sum = 0 := by simpa only [hp] using hfr ha
      rcases hh with ⟨rfl, rfl⟩
      have ht := phaseCalls_strict_fit p c s hc hf ha (by simp [hp])
      simp only [phaseCalls, ha, ite_true, hp, Nat.sub_zero] at ht ⊢
      have hout := transport_pass p c s answer ξ ha ht
      rw [← hp] at hout
      rw [hout]
      unfold Fresh
      split_ifs <;> simp
  · have haf : s.active = false := Bool.eq_false_iff.mpr ha
    simp only [phaseCalls, haf, Bool.false_eq_true, ite_false]
    rw [padding_pass p c s answer ξ (Or.inl haf) hf.1]
    simp [Fresh, haf]

lemma finishGradient_rank (p : Params) (c : Config) (refresh : Bool)
    (s : State p c) (values : Fin (c.groups + 1) → Space p) :
    phaseRank p c (finishGradient p c refresh s values) ≤
      2 * (c.epoch + 1 - s.inner) + if refresh then 0 else if s.inner = 0 then 1 else 0 := by
  cases refresh with
  | true =>
    simpa [finishGradient] using (beginFineStep_rank_le p c
      { s with estimate := OracleTemplate.MultiplicativeRobustEstimator.medoid values })
  | false =>
    simpa [finishGradient] using (finishPilot_rank_le p c s
      (OracleTemplate.MultiplicativeRobustEstimator.medoid values))

lemma active_phase_rank_decreases (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (hfr : Fresh p c s) (ha : s.active = true) (hpad : s.phase ≠ .padding) :
    phaseRank p c (path p c answer s ξ (phaseCalls p c s)) + 1 ≤ phaseRank p c s := by
  have ht := phaseCalls_strict_fit p c s hc hf ha hpad
  cases hp : s.phase with
  | padding => exact (hpad hp).elim
  | gradient refresh j i sum values =>
    have hh : j.val = 0 ∧ i = 0 ∧ sum = 0 ∧ values = fun _ => 0 := by
      simpa only [hp] using hfr ha
    have hj : j = 0 := Fin.ext hh.1
    subst j
    rcases hh with ⟨_, rfl, rfl, rfl⟩
    simp only [phaseCalls, ha, ite_true, hp, Fin.val_zero, batchRemaining_initial] at ht ⊢
    have hout := gradient_pass p c s refresh answer ξ ha ht
    rw [← hp] at hout
    rw [hout]
    have hr := finishGradient_rank p c refresh
      { s with slot := s.slot + (c.groups + 1) *
        ((if refresh then c.resetBatch else c.pilotBatch) + 1) }
      (fun j => (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
        ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
          answer (s.point, none)
            (ξ (j.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2)
    have hright : phaseRank p c s = 2 * (c.epoch + 1 - s.inner) + 1 +
        (if refresh then 0 else if s.inner = 0 then 1 else 0) := by
      simp only [phaseRank, ha, hp, ite_true]
    dsimp only at hr
    rw [hright]
    omega
  | transport i sum =>
    have hh : i = 0 ∧ sum = 0 := by simpa only [hp] using hfr ha
    rcases hh with ⟨rfl, rfl⟩
    have hi : s.inner ≤ c.epoch := (by simpa only [hp] using hc.2 :
      s.inner ≤ c.epoch ∧ 0 ≤ c.transportBatch).1
    simp only [phaseCalls, ha, ite_true, hp, Nat.sub_zero] at ht ⊢
    have hout := transport_pass p c s answer ξ ha ht
    rw [← hp] at hout
    rw [hout]
    by_cases hnext : s.inner < c.epoch
    · simp only [phaseRank, ha, hp, ite_true, hnext, Bool.false_eq_true, ite_false,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false]
      omega
    · simp only [phaseRank, ha, hp, ite_true, hnext, ite_false]
      omega

lemma path_invariants (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) :
    CounterValid p c (path p c answer s ξ n) ∧ PhaseFits p c (path p c answer s ξ n) := by
  induction n generalizing s ξ with
  | zero => exact ⟨hc, hf⟩
  | succ n ih =>
    exact ih _ _ (update_counter_valid p c s hc (ξ 0).1 _)
      (update_phase_fits p c s hc hf (ξ 0).1 _)

lemma path_slot_from (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) (hs : s.slot < macroCalls c) :
    (path p c answer s ξ n).slot = (s.slot + n) % macroCalls c := by
  induction n with
  | zero => simp [path, trajectory, Nat.mod_eq_of_lt hs]
  | succ n ih =>
    have hslot : (path p c answer s ξ n).slot < macroCalls c := by
      rw [ih]
      exact Nat.mod_lt _ (macroCalls_pos c)
    simp only [path, trajectory_succ_last]
    change (update p c (path p c answer s ξ n) (ξ n).1
      (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2)).slot = _
    rw [update_slot p c _ hslot, ih]
    simp only [Nat.mod_add_mod, Nat.add_assoc]

lemma phaseCalls_within_horizon (p : Params) (c : Config) (s : State p c)
    (elapsed : ℕ) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (ht : elapsed < trialCalls c) (hslot : s.slot = elapsed % macroCalls c) :
    elapsed + phaseCalls p c s ≤ trialCalls c := by
  have hfit := phaseCalls_fit p c s hc hf
  have hM := macroCalls_pos c
  have hdiv : elapsed / macroCalls c < c.macros + 1 := by
    apply (Nat.div_lt_iff_lt_mul hM).2
    simpa only [trialCalls] using ht
  have hmul := Nat.mul_le_mul_right (macroCalls c)
    (show elapsed / macroCalls c + 1 ≤ c.macros + 1 by omega)
  have hrepr := Nat.mod_add_div elapsed (macroCalls c)
  rw [← hslot, Nat.mul_comm] at hrepr
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  simp only [trialCalls, Nat.add_mul, Nat.one_mul]
  omega

def blockCap (c : Config) : ℕ := (c.macros + 1) * (2 * (c.epoch + 1) + 3)

def horizonRank (p : Params) (c : Config) (s : State p c) (elapsed : ℕ) : ℕ :=
  if elapsed < trialCalls c then
    (c.macros - elapsed / macroCalls c) * (2 * (c.epoch + 1) + 3) + phaseRank p c s + 1
  else 0

lemma initial_horizon_rank (p : Params) (c : Config) :
    horizonRank p c (initial p c) 0 = blockCap c := by
  have ht : 0 < trialCalls c := Nat.mul_pos (by omega) (macroCalls_pos c)
  simp only [horizonRank, ht, ite_true, Nat.zero_div, Nat.sub_zero, initial_phase_rank, blockCap]
  ring

lemma horizonRank_pos (p : Params) (c : Config) (s : State p c) (elapsed : ℕ)
    (ht : elapsed < trialCalls c) : 0 < horizonRank p c s elapsed := by
  simp [horizonRank, ht]

lemma active_phase_div (p : Params) (c : Config) (s : State p c) (elapsed : ℕ)
    (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (ha : s.active = true) (hp : s.phase ≠ .padding)
    (hslot : s.slot = elapsed % macroCalls c) :
    (elapsed + phaseCalls p c s) / macroCalls c = elapsed / macroCalls c := by
  have hfit := phaseCalls_strict_fit p c s hc hf ha hp
  have hrepr := Nat.mod_add_div elapsed (macroCalls c)
  rw [← hslot, Nat.mul_comm] at hrepr
  apply Nat.div_eq_of_lt_le
  · omega
  · simp only [Nat.add_mul, Nat.one_mul]
    omega

lemma padding_phase_div (p : Params) (c : Config) (s : State p c) (elapsed : ℕ)
    (hf : PhaseFits p c s) (hp : s.active = false ∨ s.phase = .padding)
    (hslot : s.slot = elapsed % macroCalls c) :
    (elapsed + phaseCalls p c s) / macroCalls c = elapsed / macroCalls c + 1 := by
  have hs := hf.1
  have hM := macroCalls_pos c
  have hrepr := Nat.mod_add_div elapsed (macroCalls c)
  rw [← hslot, Nat.mul_comm] at hrepr
  have he : phaseCalls p c s = macroCalls c - s.slot := by
    rcases hp with ha | hp
    · simp [phaseCalls, ha]
    · simp [phaseCalls, hp]
  rw [he]
  apply Nat.div_eq_of_lt_le
  · simp only [Nat.add_mul, Nat.one_mul]
    omega
  · simp only [Nat.add_mul, Nat.one_mul]
    omega

lemma horizonRank_decreases (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (elapsed : ℕ)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) (hfr : Fresh p c s)
    (ht : elapsed < trialCalls c) (hslot : s.slot = elapsed % macroCalls c) :
    horizonRank p c (path p c answer s ξ (phaseCalls p c s)) (elapsed + phaseCalls p c s) + 1 ≤
      horizonRank p c s elapsed := by
  by_cases hend : elapsed + phaseCalls p c s < trialCalls c
  · simp only [horizonRank, ht, hend, ite_true]
    by_cases hactive : s.active = true ∧ s.phase ≠ .padding
    · rw [active_phase_div p c s elapsed hc hf hactive.1 hactive.2 hslot]
      have hr := active_phase_rank_decreases p c s answer ξ hc hf hfr hactive.1 hactive.2
      omega
    · have hp : s.active = false ∨ s.phase = .padding := by
        by_cases ha : s.active = true
        · exact Or.inr (by simpa [ha] using hactive)
        · exact Or.inl (Bool.eq_false_iff.mpr ha)
      rw [padding_phase_div p c s elapsed hf hp hslot]
      have hcost : phaseCalls p c s = macroCalls c - s.slot := by
        rcases hp with ha | hp
        · simp [phaseCalls, ha]
        · simp [phaseCalls, hp]
      rw [hcost, padding_pass p c s answer ξ hp hf.1]
      have hr0 : phaseRank p c s = 0 := by
        rcases hp with ha | hp
        · simp [phaseRank, ha]
        · simp [phaseRank, hp]
      have hr1 : phaseRank p c
          { s with slot := 0, inner := 0, phase := .gradient false 0 0 0 (fun _ => 0) } ≤
          2 * (c.epoch + 1) + 2 := by
        cases s.active <;> simp [phaseRank]
      have hdiv : elapsed / macroCalls c + 1 < c.macros + 1 := by
        have hd := (Nat.div_lt_iff_lt_mul (macroCalls_pos c)).2
          (show elapsed + phaseCalls p c s < (c.macros + 1) * macroCalls c from hend)
        rwa [padding_phase_div p c s elapsed hf hp hslot] at hd
      have hsub : c.macros - elapsed / macroCalls c =
          c.macros - (elapsed / macroCalls c + 1) + 1 := by omega
      rw [hr0, hsub, Nat.add_mul, Nat.one_mul]
      omega
  · simp only [horizonRank, ht, hend, ite_true, ite_false]
    omega

abbrev TimedState (p : Params) (c : Config) := State p c × ℕ

def timedCost (p : Params) (c : Config) (s : TimedState p c) : ℕ :=
  if s.2 < trialCalls c then phaseCalls p c s.1 else 0

noncomputable def timedAdvance (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : TimedState p c) (z : ℝ × Ω) : TimedState p c :=
  (update p c s.1 z.1 (answer (query p c s.1 z.1) z.2), s.2 + 1)

def TimedValid (p : Params) (c : Config) (s : TimedState p c) : Prop :=
  CounterValid p c s.1 ∧ PhaseFits p c s.1 ∧ Fresh p c s.1 ∧
    s.2 ≤ trialCalls c ∧ s.1.slot = s.2 % macroCalls c

lemma timed_trajectory (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : TimedState p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    trajectory (timedAdvance p c answer) n s ξ = (path p c answer s.1 ξ n, s.2 + n) := by
  induction n generalizing s ξ with
  | zero => simp [trajectory, path]
  | succ n ih =>
    rw [trajectory, ih]
    simp only [timedAdvance, path, trajectory]
    congr 1
    omega

lemma initial_timed_valid (p : Params) (c : Config) :
    TimedValid p c (initial p c, 0) :=
  ⟨initial_counter_valid p c, initial_phase_fits p c, initial_fresh p c,
    Nat.zero_le _, rfl⟩

lemma timed_next_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : TimedState p c) (ξ : ℕ → ℝ × Ω) (hs : TimedValid p c s) :
    TimedValid p c (finiteRun (timedAdvance p c answer) (timedCost p c s) s (fun i => ξ i)) := by
  rw [finiteRun_eq_trajectory, timed_trajectory]
  by_cases ht : s.2 < trialCalls c
  · simp only [timedCost, ht, ite_true]
    have hi := path_invariants p c answer s.1 ξ (phaseCalls p c s.1) hs.1 hs.2.1
    refine ⟨hi.1, hi.2, phase_preserves_fresh p c s.1 answer ξ hs.1 hs.2.1 hs.2.2.1,
      phaseCalls_within_horizon p c s.1 s.2 hs.1 hs.2.1 ht hs.2.2.2.2, ?_⟩
    rw [path_slot_from p c answer s.1 ξ _ hs.2.1.1, hs.2.2.2.2, Nat.mod_add_mod]
  · simpa only [timedCost, ht, ite_false, path, trajectory, Nat.add_zero] using hs

lemma timed_rank_decreases (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : TimedState p c) (ξ : ℕ → ℝ × Ω) (hs : TimedValid p c s) :
    let t := finiteRun (timedAdvance p c answer) (timedCost p c s) s (fun i => ξ i)
    horizonRank p c t.1 t.2 ≤ horizonRank p c s.1 s.2 - 1 := by
  dsimp only
  rw [finiteRun_eq_trajectory, timed_trajectory]
  by_cases ht : s.2 < trialCalls c
  · simp only [timedCost, ht, ite_true]
    have hh := horizonRank_decreases p c s.1 answer ξ s.2 hs.1 hs.2.1 hs.2.2.1 ht hs.2.2.2.2
    omega
  · simp [timedCost, horizonRank, ht]

lemma timed_trace_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : TimedState p c) (ξ : ℕ → ℝ × Ω) (k : ℕ) (hs : TimedValid p c s) :
    TimedValid p c (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer)) s ξ k).1 := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [blockTrace_succ]
    exact timed_next_valid p c answer _ _ ih

lemma timed_trace_rank (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : TimedState p c) (ξ : ℕ → ℝ × Ω) (k : ℕ) (hs : TimedValid p c s) :
    let t := (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer)) s ξ k).1
    horizonRank p c t.1 t.2 ≤ horizonRank p c s.1 s.2 - k := by
  dsimp only
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hv := timed_trace_valid p c answer s ξ k hs
    have hd := timed_rank_decreases p c answer
      (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer)) s ξ k).1
      (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer)) s ξ k).2 hv
    dsimp only at hd
    rw [blockTrace_succ]
    exact hd.trans (by omega)

lemma timed_trace_horizon (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) :
    (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer))
      (initial p c, 0) ξ (blockCap c)).1.2 = trialCalls c := by
  have hv := timed_trace_valid p c answer (initial p c, 0) ξ (blockCap c) (initial_timed_valid p c)
  have hr := timed_trace_rank p c answer (initial p c, 0) ξ (blockCap c) (initial_timed_valid p c)
  dsimp only at hr
  rw [initial_horizon_rank, Nat.sub_self] at hr
  by_contra hne
  have ht : (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer))
      (initial p c, 0) ξ (blockCap c)).1.2 < trialCalls c := lt_of_le_of_ne hv.2.2.2.1 hne
  have hp := horizonRank_pos p c
    (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer))
      (initial p c, 0) ξ (blockCap c)).1.1 _ ht
  omega

lemma timed_trace_output (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) :
    (blockTrace (timedCost p c) (finiteRun (timedAdvance p c answer))
      (initial p c, 0) ξ (blockCap c)).1.1 = path p c answer (initial p c) ξ (trialCalls c) := by
  have ht := timed_trace_horizon p c answer ξ
  rw [blockTrace_eq_trajectory, timed_trajectory] at ht ⊢
  simpa only [Nat.zero_add] using congrArg (path p c answer (initial p c) ξ) ht

end LongTails.Proofs.HystereticHessianBlocks
