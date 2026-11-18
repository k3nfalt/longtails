import LongTails.Setups.DistributedJacobianStrongGrowth
import LongTails.Proofs.DistributedExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthOracle

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth

lemma computation_submit_idle (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (s : ComputationState p) (time : Time) (x : Point p)
    (hs : s.pending = none) :
    (computation p g S).submit i s time x =
      { s with pending := some (time + p.computeTime, x) } := by
  simp [computation, hs]

lemma computation_answer_wait (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (s : ComputationState p) (time finish : Time) (x : Point p)
    (hs : s.pending = some (finish, x)) (ht : time < finish) :
    (computation p g S).answer i s time = none := by
  simp [computation, hs, not_le.mpr ht]

lemma computation_answer_complete (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (s : ComputationState p) (time finish : Time) (x : Point p)
    (hs : s.pending = some (finish, x)) (ht : finish ≤ time) :
    (computation p g S).answer i s time =
      some (g i x (s.samples (p.n * s.used + i.val)), { s with pending := none, used := s.used + 1 }) := by
  simp [computation, hs, ht]

lemma communication_submit_free (p : Params) (S : Sampling p) (s : CommunicationState p)
    (time : Time) (source target : Fin p.n) (bits : List Bool)
    (hadj : adjacent p source target) (hfree : s.messages source target = none) :
    (communication p S).submit s time source (target, bits) =
      { messages := Function.update s.messages source
          (Function.update (s.messages source) target
            (some (time + p.latency + p.timePerBit * bits.length, bits))) } := by
  classical
  simp [communication, hadj, hfree]

lemma child_adjacent (p : Params) (hp : valid p) (child parent : Fin p.n)
    (hc : child ≠ p.root) (he : p.parent child = parent) : adjacent p child parent := by
  have hd := hp.2.2.2.1 child hc
  refine ⟨?_, Or.inl he⟩
  intro hh
  rw [he, hh] at hd
  omega

lemma adjacent_symm (p : Params) (source target : Fin p.n) (h : adjacent p source target) :
    adjacent p target source := by
  exact ⟨Ne.symm h.1, h.2.symm⟩

lemma communication_ready (p : Params) (S : Sampling p)
    (s : CommunicationState p) (time : Time) :
    ((communication p S).answer s time).isSome ↔
      ∃ source target finish bits,
        s.messages source target = some (finish, bits) ∧ finish ≤ time := by
  classical
  let messages := (List.finRange p.n).flatMap fun source =>
    (List.finRange p.n).filterMap fun target =>
      (s.messages source target).map fun (finish, bits) => (finish, source, target, bits)
  have hm : (∃ item ∈ messages, item.1 ≤ time) ↔
      ∃ source target finish bits, s.messages source target = some (finish, bits) ∧ finish ≤ time := by
    simp only [messages, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff]
    constructor
    · rintro ⟨item, ⟨source, _, target, _, ⟨finish, bits⟩, he, rfl⟩, ht⟩
      exact ⟨source, target, finish, bits, he, ht⟩
    · rintro ⟨source, target, finish, bits, he, ht⟩
      exact ⟨(finish, source, target, bits),
        ⟨source, by simp, target, by simp, (finish, bits), he, rfl⟩, ht⟩
  have ha := (DistributedExecution.argmin_ready Prod.fst messages time).trans hm
  cases hmin : messages.argmin Prod.fst with
  | none =>
      have hnone : ¬ ∃ source target finish bits,
          s.messages source target = some (finish, bits) ∧ finish ≤ time := by
        simpa [hmin] using ha.symm
      dsimp only [messages] at hmin
      simp [communication, hmin]
      intro source target finish bits he
      exact lt_of_not_ge (fun ht => hnone ⟨source, target, finish, bits, he, ht⟩)
  | some item =>
      rcases item with ⟨finish, source, target, bits⟩
      have hsome : finish ≤ time ↔ ∃ source target finish bits,
          s.messages source target = some (finish, bits) ∧ finish ≤ time := by
        simpa [hmin] using ha
      dsimp only [messages] at hmin
      rw [← hsome]
      by_cases ht : finish ≤ time <;>
        simp [communication, hmin, ht]

lemma computation_ready (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (s : ComputationState p) (time : Time) :
    ((computation p g S).answer i s time).isSome ↔
      ∃ finish x, s.pending = some (finish, x) ∧ finish ≤ time := by
  cases hs : s.pending with
  | none => simp [computation, hs]
  | some pending =>
      obtain ⟨finish, x⟩ := pending
      by_cases ht : finish ≤ time <;> simp [computation, hs, ht]

lemma computation_thresholds (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (s : ComputationState p) :
    ∃ times : Finset Time, ∀ time, ((computation p g S).answer i s time).isSome ↔
      ∃ finish ∈ times, finish ≤ time := by
  classical
  cases hs : s.pending with
  | none => exact ⟨∅, fun time => by simp [computation_ready, hs]⟩
  | some pending =>
      obtain ⟨finish, x⟩ := pending
      exact ⟨{finish}, fun time => by simp [computation_ready, hs]⟩

lemma communication_thresholds (p : Params) (S : Sampling p)
    (s : CommunicationState p) :
    ∃ times : Finset Time, ∀ time,
      ((communication p S).answer s time).isSome ↔
        ∃ finish ∈ times, finish ≤ time := by
  classical
  let times := Finset.univ.biUnion fun source => Finset.univ.biUnion fun target =>
    ((s.messages source target).map Prod.fst).toFinset
  have hp (source target : Fin p.n) (time : Time) :
      (∃ finish ∈ ((s.messages source target).map Prod.fst).toFinset, finish ≤ time) ↔
        ∃ finish bits, s.messages source target = some (finish, bits) ∧ finish ≤ time := by
    cases he : s.messages source target with
    | none => simp only [Option.map_none, Option.toFinset_none, Finset.notMem_empty, false_and, exists_false, reduceCtorEq]
    | some value =>
        rcases value with ⟨finish, bits⟩
        simp only [Option.map_some, Option.toFinset_some, Finset.mem_singleton, Option.some.injEq, Prod.mk.injEq]
        simp
  refine ⟨times, ?_⟩
  intro time
  rw [communication_ready]
  simp only [times, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨source, target, finish, bits, he, ht⟩
    obtain ⟨finish', hf, ht'⟩ := (hp source target time).mpr ⟨finish, bits, he, ht⟩
    exact ⟨finish', ⟨source, target, hf⟩, ht'⟩
  · rintro ⟨finish, ⟨source, target, hf⟩, ht⟩
    obtain ⟨finish', bits, he, ht'⟩ := (hp source target time).mp ⟨finish, hf, ht⟩
    exact ⟨source, target, finish', bits, he, ht'⟩

lemma event_thresholds {Result : Type} (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (A : Algorithm (Point p) (Point p) (CommReply p) Result p.n)
    (c : ExecutionState (system p g S) A) :
    ∃ times : Finset Time, ∀ time,
      (event (system p g S) A c time).isSome ↔ ∃ finish ∈ times, finish ≤ time := by
  classical
  choose times htimes using fun v => computation_thresholds p g S v (c.oracle.computation v)
  obtain ⟨comm, hcomm⟩ := communication_thresholds p S c.oracle.communication
  refine ⟨(Finset.univ.biUnion times) ∪ comm ∪ (Finset.univ.image c.wakeTime), ?_⟩
  intro time
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready]
  change ((∃ v, ((computation p g S).answer v (c.oracle.computation v) time).isSome) ∨
    ((communication p S).answer c.oracle.communication time).isSome) ∨
    (∃ v, c.wakeTime v ≤ time) ↔ _
  simp only [htimes, hcomm, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  aesop

lemma nextTime_exists {Result : Type} (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (A : Algorithm (Point p) (Point p) (CommReply p) Result p.n)
    (c : ExecutionState (system p g S) A) (hc : c.time ≤ c.deadline) :
    ∃ t, IsLeast {t | c.time ≤ t ∧ t ≤ c.deadline ∧
      (t = c.deadline ∨ (event (system p g S) A c t).isSome)} t := by
  obtain ⟨times, htimes⟩ := event_thresholds p g S A c
  exact DistributedExecution.nextTime_exists_of_thresholds
    (event (system p g S) A c) times c.time c.deadline hc htimes

lemma communication_received_data (p : Params) (S : Sampling p)
    (s next : CommunicationState p) (time : Time) (source target : Fin p.n) (bits : List Bool)
    (h : (communication p S).answer s time = some ((target, ⟨source, bits⟩), next)) :
    ∃ finish, s.messages source target = some (finish, bits) ∧ finish ≤ time ∧
      next = { s with messages := (Function.update s.messages source
        (Function.update (s.messages source) target none)) } := by
  classical
  let messages := (List.finRange p.n).flatMap fun sender =>
    (List.finRange p.n).filterMap fun receiver =>
      (s.messages sender receiver).map fun (finish, payload) => (finish, sender, receiver, payload)
  cases hm : messages.argmin Prod.fst with
  | none =>
      dsimp only [messages] at hm
      simp [communication, hm] at h
  | some value =>
      rcases value with ⟨finish, sender, receiver, payload⟩
      have hmem := List.argmin_mem hm
      have hstored : s.messages sender receiver = some (finish, payload) := by
        simpa [messages, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff,
          Prod.exists] using hmem
      dsimp only [messages] at hm
      by_cases ht : finish ≤ time
      · have he : ((receiver, (⟨sender, payload⟩ : CommReply p)),
            { s with messages := (Function.update s.messages sender
              (Function.update (s.messages sender) receiver none)) }) =
            ((target, (⟨source, bits⟩ : CommReply p)), next) := by
          simpa [communication, hm, ht] using h
        have htarget : receiver = target := congrArg (fun z => z.1.1) he
        have hr := congrArg (fun z => z.1.2) he
        have hsource : sender = source := congrArg CommReply.source hr
        have hbits : payload = bits := congrArg CommReply.bits hr
        subst receiver
        subst sender
        subst payload
        exact ⟨finish, hstored, ht, by simpa using (congrArg Prod.snd he).symm⟩
      · simp [communication, hm, ht] at h

lemma computation_received_data (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (s next : ComputationState p) (time : Time) (value : Point p)
    (h : (computation p g S).answer i s time = some (value, next)) :
    ∃ finish x, s.pending = some (finish, x) ∧ finish ≤ time ∧
      value = g i x (s.samples (p.n * s.used + i.val)) ∧
      next = { s with pending := none, used := s.used + 1 } := by
  cases hs : s.pending with
  | none => simp [computation, hs] at h
  | some pending =>
      obtain ⟨finish, x⟩ := pending
      by_cases ht : finish ≤ time
      · have he : (g i x (s.samples (p.n * s.used + i.val)),
            { s with pending := none, used := s.used + 1 }) = (value, next) := by
          simpa [computation, hs, ht] using h
        exact ⟨finish, x, rfl, ht, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
      · simp [computation, hs, ht] at h

end LongTails.Proofs.DistributedJacobianStrongGrowthOracle
