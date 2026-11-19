import LongTails.Proofs.MultirateProgress

open MeasureTheory

namespace LongTails.Proofs.MultirateInvariants

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateAllocation
open MultirateReservations MultirateMachine MultirateEvents MultirateInteraction MultirateProgress

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
    {s : Samples p} {D u : Time} {x y : Config p} {n : ℕ} {out : Point p}

lemma root_tick (hr : Responsive x) {i : Fin p.n} {v : Cell p} (prog : Program p)
    (hs : ¬ dispatching v) : Responsive (tick x 0 x.now (revised x i v) prog) := by
  constructor
  · intro _; simp [tick]
  · intro j hj
    by_cases he : j = i
    · subst j; simp only [tick,revised,Function.update_self] at hj; exact (hs hj).elim
    · simpa only [tick, Function.update_of_ne (Fin.succ_ne_zero j)] using hr.2 j
        (by simpa only [tick,revised,Function.update_of_ne he] using hj)

lemma leaf_tick (hr : Responsive x) {i : Fin p.n} {v : Cell p} (hs : buffered v → buffered (x.table i)) :
    Responsive (tick x i.succ x.now (revised x i v) x.program) := by
  constructor
  · intro h
    change Function.update x.wakes i.succ x.now 0 ≤ x.now
    rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    apply hr.1
    change rootReady (Function.update x.table i v) x.program at h
    cases hp : x.program with
    | done => rw [hp] at h; exact h
    | post => trivial
    | collect j next =>
      rw [hp] at h
      by_cases he : j = i
      · subst j; exact hs (by simpa only [rootReady,Function.update_self] using h)
      · simpa only [rootReady,Function.update_of_ne he] using h
  · intro j hj
    by_cases he : j = i
    · subst j; simp [tick]
    · have hn := fun h : j.succ = i.succ => he (Fin.succ_inj.mp h)
      simpa only [tick,Function.update_of_ne hn] using hr.2 j (by simpa only [tick,revised,Function.update_of_ne he] using hj)

lemma sleep_root {v : Fin (p.n+1)} (hs : (algorithm p D).query v (workersOf g s x.table x.program v) 0 =
      (.advance 1,workersOf g s x.table x.program v)) :
    (v = 0 → ¬rootReady x.table x.program) ∧ ∀ i, v = i.succ → ¬dispatching (x.table i) := by
  constructor
  · rintro rfl
    change rootQuery p ⟨x.program,inbox g s x.table,.idle,false⟩ = _ at hs
    cases hp : x.program with
    | done => exact id
    | post =>
      have heq := congrArg Prod.fst hs
      simp [rootQuery,hp] at heq
    | collect i next =>
      cases he : x.table i with
      | buffered job =>
        have hm : inbox g s x.table i = some (jobReply g s i job) := by simp [inbox,he,mailbox]
        have hz : (0 : ClockReading) ≠ 1 := by decide
        have heq := congrArg Prod.fst hs
        simp only [rootQuery,hp,hm] at heq
        exact fun _ => hz (Action.advance.inj heq)
      | free | down | work | up | dispatch => simp [rootReady, he, buffered]
  · rintro i rfl
    cases he : x.table i with
    | dispatch job j t =>
      change workerQuery p i ⟨.done p.x0,fun _ => none,phaseOf g s i (x.table i),false⟩ = _ at hs
      rw [he] at hs
      simp only [phaseOf,workerQuery] at hs
      split at hs <;> cases hs
    | free | down | work | up | buffered => exact id

lemma responsive_next {v e os} (h : Move g P s D u x v e os y) (hr : Responsive x) : Responsive y := by
  cases h with
  | sleep v _ hs =>
    obtain ⟨h₀,hᵢ⟩ := sleep_root hs
    constructor
    · intro hr'
      have hn : 0 ≠ v := fun he => h₀ he.symm hr'
      simpa only [tick,Function.update_of_ne hn] using hr.1 hr'
    · intro j hj
      have hn : j.succ ≠ v := fun he => hᵢ j he.symm hj
      simpa only [tick,Function.update_of_ne hn] using hr.2 j hj
  | post | take | up => exact root_tick hr _ id
  | evaluate | reply | computed | down => exact leaf_tick hr False.elim

lemma safe_revise {v : Fin (p.n+1)} {w : Time} {i : Fin p.n} {cell : Cell p} {prog : Program p}
    (h : ∀ i, Safe x i) (hf : Feasible p i cell) (ht : ∀ t ∈ readyTime cell, x.now ≤ t) :
    ∀ j, Safe (tick x v w (revised x i cell) prog) j := by
  intro j
  by_cases he : j = i
  · subst j; simpa only [Safe,tick,revised,Function.update_self] using And.intro hf ht
  · simpa only [Safe,tick,revised,Function.update_of_ne he] using h j

lemma safe_next {v e os} (hm : Move g P s D u x v e os y) (h : Valid g s out D x n u) :
    ∀ i, Safe y i := by
  cases hm with
  | sleep => exact h.safe
  | post i bits next e hp hf hw hb =>
    have hn : 0 < n := by cases hcert : n with
      | zero => have hc := h.cert; rw [hcert,hp] at hc; cases hc
      | succ => omega
    apply safe_revise h.safe
    · exact add_le_add_left (h.current hn) _
    · intro t ht; cases ht; exact le_add_of_nonneg_right zero_le
  | take | up =>
    apply safe_revise h.safe
    · trivial
    · intro t ht; cases ht
  | down i job t he ht =>
    have hs := h.safe i
    simp only [Safe,he] at hs
    apply safe_revise h.safe
    · exact ⟨Nat.zero_le _,by simpa [Feasible] using hs.1⟩
    · exact hs.2
  | computed i job j t he ht =>
    have hs := h.safe i
    simp only [Safe,he] at hs
    exact safe_revise h.safe ⟨hs.1.1,hs.1.2⟩ hs.2
  | evaluate i job j t he hw hj =>
    have hs := h.safe i
    simp only [Safe,he] at hs
    have hnow := hs.2 t rfl
    apply safe_revise h.safe
    · refine ⟨hj,?_⟩
      have hh := add_le_add_left (hnow.trans hs.1.2) (p.h i)
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc,add_comm,add_left_comm] using hh
    · intro a ha; cases ha; exact le_add_of_nonneg_right zero_le
  | reply i job t he hw =>
    have hs := h.safe i
    simp only [Safe,he] at hs
    apply safe_revise h.safe
    · change x.now + packetDelay p ≤ job.posted + span p i
      simpa [span,add_assoc,add_left_comm,add_comm] using add_le_add_right ((hs.2 t rfl).trans hs.1.2) (packetDelay p)
    · intro a ha; cases ha; exact le_add_of_nonneg_right zero_le

end LongTails.Proofs.MultirateInvariants
